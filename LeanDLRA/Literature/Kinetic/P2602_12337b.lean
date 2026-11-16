import LeanDLRA.Integrators.BUG
import LeanDLRA.Kinetic.Stencils
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.Orthonormal

/-!
# The asymptotic-preserving property of IMEX-S-BUG (arXiv 2602.12337, Sec. 4.2)

Li, Jiang, Zhang, Xiong, *Temporal-Stability-Enhanced and Energy-Stable Dynamical Low-Rank
Approximation for Multiscale Linear Kinetic Transport Equations*.  This module writes out the
one-dimensional fully discrete scheme of Sec. 3.2 and 4.1 on finite grids (`Disc`, with `𝒜`, `ℋ`,
`𝒥`, `ℬ`, `R`; the Schur complement update `Disc.IsMacroStep`; the K-, L- and S-step; one step
`IsSchurIMEXSBUGStep`) and proves the formal AP property of Sec. 4.2 and a true limit
`ε → 0⁺`.  The formal part: the oblique projector fixes `Range X` (`oblique_fixes`), the limit
equations (4.1a-c) (`Disc.IsFormalLimit`) put `-(σˢ)⁻¹ 𝒟^{x,+} ρ¹` in `Range X¹` and `M Qˣ 1` in
`Range V¹` (`mem_rangeX`, `mem_rangeV`), this gives the flux (4.3) (`flux_eq_of_mem_range`), and the
macro equation becomes the implicit diffusion scheme (`formal_ap`, `Disc.IsDiffusionStep`), which is
well posed (`existsUnique_diffusion`) and is the conservative three-point scheme on the periodic
grid (`periodic_diffusion`).  The limit: the steps reduce to (4.1a-c) (`tendsto_steps`), the density
converges to the diffusion step (`tendsto_rho`) and to the diffusion iterates (`tendsto_iterates`,
`exists_ap_trajectory`), and the low-rank flux and macro equation converge (`tendsto_flux`,
`ap_step`, `ap_step_fixed`, `tendsto_flux_iterates`).  `exists_step`, `exists_trajectory`,
`exists_formal_limit` and `nondegenerate_instance` show that the hypotheses can hold.

## Differences from the paper

* **The range claims are false as stated.**  The paper reads off (4.1a), (4.1b) that
  `-(σˢ)⁻¹ 𝒟^{x,+} ρ^{n+1} ∈ Range X^{n+1}` and `M Qˣ 1 ∈ Range V^{n+1}`.  This needs
  `(Vⁿ)ᵀ M Qˣ 1 ≠ 0` and `(Xⁿ)ᵀ 𝒟^{x,+} ρ^{n+1} ≠ 0`: otherwise `K^{n+1}` or `L^{n+1}` vanishes in
  the limit and does not determine the new basis.  `ap_fails_of_degenerate_right` and
  `ap_fails_of_degenerate_left` are genuine runs of the scheme for all `ε > 0`, which satisfy the
  constraint `1ᵀ M V = 0`, where the inclusion and the flux limit (4.3) fail.  With these two
  hypotheses everything holds.  Once `M Qˣ 1` is in the right basis the first one propagates
  (`tendsto_flux_iterates`).  The enriched bases of the augmented scheme need neither of them.
* **The density needs no range condition.**  `ρ^{n+1}` comes from the Schur complement with the
  full-rank operator, so `tendsto_rho` and `tendsto_iterates` hold for every bounded micro state and
  without nondegeneracy.  The range conditions decide only whether the macro equation holds for the
  low-rank `G^{n+1}`.  For `ε > 0` it holds with the full-rank micro update (`isMacroStep_iff`), and
  it holds for the low-rank `G^{n+1}` only in the limit (`ap_step`).
* The paper's limit is formal: it does not say how the `O(1/ε)` terms and the bases behave.  Here
  `ε → 0⁺` is a true limit, for fixed `Δt` and grids and for data at level `n` that may depend on
  `ε`, as they do along a trajectory.  The bases `X¹(ε)`, `V¹(ε)` need not converge, so that the
  projector argument is replaced by a Galerkin bound (`tendsto_flux_of_capture`).
* The grid is one-dimensional, as in Sec. 4.2.  `𝒟^{x,±}` are arbitrary matrices with
  `𝒟^{x,-} = -(𝒟^{x,+})ᵀ`, which is the summation by parts behind
  `|D_Ω| ⟨ρ, ℋ(G)⟩ = -⟨𝒥(ρ), G⟩_w`; the paper does not print a stencil, and `periodic` is the
  first-order periodic one.  The invertibility of `Xᵀ σˢ X`, assumed in Sec. 4.2, is derived.
* The printed S-step has `ℬ(X S Vᵀ)` with an unsuperscripted `S`; it is read as `S̃ⁿ`, as in the
  explicit advection of the K- and L-step.  Of the QR steps only `Xᵀ X = 1`, `K = X R` are used.
* Not formalized: the convergence of the three-point scheme to `∂ₓ((σˢ)⁻¹ ∂ₓ ρ)` as `Δx → 0`,
  rates in `ε`, and the conservative truncation of the augmented scheme, of which only the flux
  with the enriched bases is covered.  The sibling slice treats the other sections.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2602_12337

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-- The data of the one-dimensional `S_N` discretisation of arXiv 2602.12337, Sec. 3.2: the
difference matrices `𝒟^{x,+}`, `𝒟^{x,-}` on the grid `x`, the quadrature weights `w` and nodes
`Ω` (the `x`-components `Ωˣ` of the directions) on the angular grid `a`, the measure `|D_Ω|`, the
scattering and absorption coefficients `σˢ`, `σᵃ` on the grid, and the time step `Δt`. -/
structure Disc (x a : Type*) where
  /-- The difference matrix `𝒟^{x,+}`. -/
  Dp : Matrix x x ℝ
  /-- The difference matrix `𝒟^{x,-}`. -/
  Dm : Matrix x x ℝ
  /-- The quadrature weights `wₘ`. -/
  w : a → ℝ
  /-- The quadrature nodes `Ωˣₘ`. -/
  Ω : a → ℝ
  /-- The measure `|D_Ω|` of the angular domain. -/
  vol : ℝ
  /-- The scattering coefficient `σˢ`. -/
  σs : x → ℝ
  /-- The absorption coefficient `σᵃ`. -/
  σa : x → ℝ
  /-- The time step `Δt`. -/
  dt : ℝ

variable {x a r r' : Type*} [Fintype x] [Fintype a] [Fintype r] [Fintype r']
  [DecidableEq x] [DecidableEq a] [DecidableEq r] [DecidableEq r']

/-- The standing assumptions of arXiv 2602.12337, Sec. 2.1 and 3.2: positive weights with
`∑ wₘ = |D_Ω|`, `σˢ > 0`, `σᵃ ≥ 0`, `Δt > 0`, and the summation by parts `𝒟^{x,-} = -(𝒟^{x,+})ᵀ`
behind `|D_Ω| ⟨ρ, ℋ(G)⟩ = -⟨𝒥(ρ), G⟩_w`.  `periodic_admissible` proves them for the
periodic stencil. -/
structure Disc.Admissible (D : Disc x a) : Prop where
  w_pos : ∀ i, 0 < D.w i
  vol_eq : ∑ i, D.w i = D.vol
  σs_pos : ∀ i, 0 < D.σs i
  σa_nonneg : ∀ i, 0 ≤ D.σa i
  dt_pos : 0 < D.dt
  sbp : D.Dm = -D.Dpᵀ

/-- The measure `|D_Ω|` of an admissible discretisation is positive. -/
theorem Disc.Admissible.vol_pos [Nonempty a] {D : Disc x a} (h : D.Admissible) : 0 < D.vol :=
  h.vol_eq ▸ Finset.sum_pos (fun i _ => h.w_pos i) Finset.univ_nonempty

/-- The weights of an admissible discretisation divided by `|D_Ω|`, with the nodes `Ωˣ`, are a core
velocity quadrature (positive weights of total mass one). -/
noncomputable def Disc.Admissible.toQuadrature [Nonempty a] {D : Disc x a} (h : D.Admissible) :
    Kinetic.Quadrature a where
  μ := D.Ω
  w := fun i => D.w i / D.vol
  w_pos := fun i => div_pos (h.w_pos i) h.vol_pos
  sum_w := by rw [← Finset.sum_div, h.vol_eq, div_self h.vol_pos.ne']

namespace Disc

variable (D : Disc x a)

/-- `M = diag(√wₘ)`. -/
noncomputable def M : Matrix a a ℝ := Matrix.diagonal fun i => √(D.w i)

/-- `M⁻¹ = diag(1/√wₘ)`. -/
noncomputable def Minv : Matrix a a ℝ := Matrix.diagonal fun i => (√(D.w i))⁻¹

/-- `Qˣ = diag(Ωˣₘ)`. -/
def Q : Matrix a a ℝ := Matrix.diagonal D.Ω

/-- `Q^{x,+} = (Qˣ + |Qˣ|) / 2`. -/
noncomputable def Qp : Matrix a a ℝ := Matrix.diagonal fun i => (D.Ω i + |D.Ω i|) / 2

/-- `Q^{x,-} = (Qˣ - |Qˣ|) / 2`. -/
noncomputable def Qm : Matrix a a ℝ := Matrix.diagonal fun i => (D.Ω i - |D.Ω i|) / 2

/-- `σˢ` as a diagonal matrix on the grid. -/
def sigS : Matrix x x ℝ := Matrix.diagonal D.σs

/-- `σᵃ` as a diagonal matrix on the grid. -/
def sigA : Matrix x x ℝ := Matrix.diagonal D.σa

/-- `(σˢ)⁻¹` as a diagonal matrix on the grid. -/
noncomputable def sigSInv : Matrix x x ℝ := Matrix.diagonal fun i => (D.σs i)⁻¹

/-- `I - (1/|D_Ω|) w 1ᵀ`, which removes the angular average from the rows of a matrix. -/
noncomputable def avg : Matrix a a ℝ := 1 - (1 / D.vol) • Matrix.vecMulVec D.w fun _ => 1

/-- The upwind advection `𝒜(G) = 𝒟^{x,-} G Q^{x,+} + 𝒟^{x,+} G Q^{x,-}`. -/
noncomputable def A (G : Matrix x a ℝ) : Matrix x a ℝ := D.Dm * G * D.Qp + D.Dp * G * D.Qm

/-- The flux `ℋ(G) = (1/|D_Ω|) 𝒟^{x,-} G Qˣ w`. -/
noncomputable def H (G : Matrix x a ℝ) : x → ℝ :=
  (1 / D.vol) • (D.Dm *ᵥ (G *ᵥ (D.Q *ᵥ D.w)))

/-- The coupling `𝒥(ρ) = 𝒟^{x,+} ρ 1ᵀ Qˣ`; the row vector `1ᵀ Qˣ` is `Ω`. -/
def J (ρ : x → ℝ) : Matrix x a ℝ := Matrix.vecMulVec (D.Dp *ᵥ ρ) D.Ω

/-- The operator of the low-rank steps, `ℬ(Y) = 𝒜(Y M⁻¹) (I - (1/|D_Ω|) w 1ᵀ) M`. -/
noncomputable def B (Y : Matrix x a ℝ) : Matrix x a ℝ := D.A (Y * D.Minv) * D.avg * D.M

/-- `R = (1/Δt + σˢ/ε² + σᵃ)⁻¹`. -/
noncomputable def R (ε : ℝ) : Matrix x x ℝ :=
  Matrix.diagonal fun i => (1 / D.dt + D.σs i / ε ^ 2 + D.σa i)⁻¹

/-- The second angular moment `⟨Ω ⊗ Ω⟩_Ω = (1/|D_Ω|) ∑ wₘ (Ωˣₘ)²` of the quadrature. -/
noncomputable def moment : ℝ := (1 / D.vol) * ∑ i, D.w i * D.Ω i ^ 2

/-- The limit direction `M Qˣ 1` of the angular basis. -/
noncomputable def u : a → ℝ := D.M *ᵥ (D.Q *ᵥ fun _ => 1)

/-- The matrix `G = X S Vᵀ M⁻¹` with `G M = X S Vᵀ`, the energy-consistent factorisation. -/
noncomputable def lift (X : Matrix x r ℝ) (S : Matrix r r' ℝ) (V : Matrix a r' ℝ) :
    Matrix x a ℝ :=
  X * S * Vᵀ * D.Minv

/-- The Schur complement update (3.4a) of `ρ^{n+1}`, discretised as printed in Sec. 4.1:
`(1/Δt + σᵃ) ρ¹ - (1/ε²) ℋ(R 𝒥(ρ¹))
  = ρ⁰/Δt + Φ - ℋ(R (G⁰/Δt - (1/ε) 𝒜(G⁰) (I - (1/|D_Ω|) w 1ᵀ)))`.
`isMacroStep_iff` shows that it is the macro equation with the full-rank micro update. -/
def IsMacroStep (ε : ℝ) (Φ ρ₀ : x → ℝ) (G₀ : Matrix x a ℝ) (ρ₁ : x → ℝ) : Prop :=
  (1 / D.dt) • ρ₁ + D.sigA *ᵥ ρ₁ - (1 / ε ^ 2) • D.H (D.R ε * D.J ρ₁) =
    (1 / D.dt) • ρ₀ + Φ - D.H (D.R ε * ((1 / D.dt) • G₀ - (1 / ε) • (D.A G₀ * D.avg)))

/-- The K-step of Sec. 4.1 with `Kⁿ = Xⁿ Sⁿ`: the advection is explicit, the coupling with
`ρ^{n+1}` and the collision are implicit. -/
def IsKStep (ε : ℝ) (ρ₁ : x → ℝ) (X₀ : Matrix x r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix a r ℝ)
    (K₁ : Matrix x r ℝ) : Prop :=
  (1 / D.dt) • (K₁ - X₀ * S₀) =
    -(1 / ε) • (D.B (X₀ * S₀ * V₀ᵀ) * V₀) - (1 / ε ^ 2) • (D.J ρ₁ * D.M * V₀)
      - (1 / ε ^ 2) • (D.sigS * K₁) - D.sigA * K₁

/-- The L-step of Sec. 4.1 with `Lⁿ = Vⁿ (Sⁿ)ᵀ`. -/
def IsLStep (ε : ℝ) (ρ₁ : x → ℝ) (X₀ : Matrix x r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix a r ℝ)
    (L₁ : Matrix a r ℝ) : Prop :=
  (1 / D.dt) • (L₁ - V₀ * S₀ᵀ) =
    -(1 / ε) • ((D.B (X₀ * (V₀ * S₀ᵀ)ᵀ))ᵀ * X₀) - (1 / ε ^ 2) • (D.M * (D.J ρ₁)ᵀ * X₀)
      - (1 / ε ^ 2) • (L₁ * (X₀ᵀ * D.sigS * X₀)) - L₁ * (X₀ᵀ * D.sigA * X₀)

/-- The S-step of Sec. 4.1, started from `S̃ⁿ = (X^{n+1})ᵀ Xⁿ Sⁿ (Vⁿ)ᵀ V^{n+1}`, with the
advection evaluated at `S̃ⁿ` (the IMEX reading of the unsuperscripted `S` of the printed
formula). -/
def IsSStep (ε : ℝ) (ρ₁ : x → ℝ) (X₀ : Matrix x r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix a r ℝ)
    (X₁ : Matrix x r' ℝ) (V₁ : Matrix a r' ℝ) (S₁ : Matrix r' r' ℝ) : Prop :=
  (1 / D.dt) • (S₁ - X₁ᵀ * X₀ * S₀ * V₀ᵀ * V₁) =
    -(1 / ε) • (X₁ᵀ * D.B (X₁ * (X₁ᵀ * X₀ * S₀ * V₀ᵀ * V₁) * V₁ᵀ) * V₁)
      - (1 / ε ^ 2) • (X₁ᵀ * D.J ρ₁ * D.M * V₁)
      - (1 / ε ^ 2) • (X₁ᵀ * D.sigS * X₁ * S₁) - X₁ᵀ * D.sigA * X₁ * S₁

/-- The scaling `ε²/Δt + σˢ + ε² σᵃ` of the implicit part of the steps: `R = ε² (scale ε)⁻¹`. -/
noncomputable def scale (ε : ℝ) (i : x) : ℝ := ε ^ 2 / D.dt + D.σs i + ε ^ 2 * D.σa i

/-- The operator `1/Δt + σᵃ - ⟨Ω ⊗ Ω⟩_Ω 𝒟^{x,-} q 𝒟^{x,+}`.  With `q = ε⁻² R` it is the Schur
complement, with `q = (σˢ)⁻¹` the implicit diffusion operator. -/
noncomputable def Top (q : x → ℝ) : Matrix x x ℝ :=
  (1 / D.dt) • 1 + D.sigA - D.moment • (D.Dm * Matrix.diagonal q * D.Dp)

/-- The implicit diffusion scheme, the limit macro update of Sec. 4.2:
`(ρ¹ - ρ⁰)/Δt - 𝒟^{x,-}(⟨Ω ⊗ Ω⟩_Ω (σˢ)⁻¹ 𝒟^{x,+} ρ¹) + σᵃ ρ¹ = Φ`. -/
def IsDiffusionStep (Φ ρ₀ ρ₁ : x → ℝ) : Prop :=
  (1 / D.dt) • (ρ₁ - ρ₀) - D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρ₁))) + D.sigA *ᵥ ρ₁ = Φ

/-- The limit equations (4.1a-c) of the K-, L- and S-step. -/
structure IsFormalLimit (ρ₁ : x → ℝ) (X₀ : Matrix x r ℝ) (V₀ : Matrix a r ℝ) (K₁ : Matrix x r ℝ)
    (L₁ : Matrix a r ℝ) (X₁ : Matrix x r' ℝ) (V₁ : Matrix a r' ℝ) (S₁ : Matrix r' r' ℝ) :
    Prop where
  /-- (4.1a) -/
  kstep : K₁ = -(D.sigSInv * (D.J ρ₁ * D.M * V₀))
  /-- (4.1b) -/
  lstep : L₁ * (X₀ᵀ * D.sigS * X₀) = -(D.M * (D.J ρ₁)ᵀ * X₀)
  /-- (4.1c) -/
  sstep : X₁ᵀ * D.sigS * X₁ * S₁ = -(X₁ᵀ * D.J ρ₁ * D.M * V₁)

end Disc

/-- One step of the IMEX-S-BUG scheme of Sec. 4.1, in the order of the paper: `ρ¹` from the Schur
complement with `G⁰ M = X⁰ S⁰ (V⁰)ᵀ`, then `K¹` and `L¹`, then `X¹`, `V¹` with orthonormal columns
and `K¹ = X¹ R_K`, `L¹ = V¹ R_L` (all that is used of the QR factorisations), then `S¹`.  The
sibling file states the same scheme as `Grid.IsIMEXSBUGStep` on other data (`d` space dimensions
with periodic shifts, a separate macro absorption, and the zero-density constraint of Sec. 4.3 as a
further field); the two predicates are not equal as stated and are not compared formally. -/
structure IsSchurIMEXSBUGStep (D : Disc x a) (ε : ℝ) (Φ ρ₀ : x → ℝ) (X₀ : Matrix x r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix a r ℝ) (ρ₁ : x → ℝ) (K₁ : Matrix x r ℝ) (L₁ : Matrix a r ℝ)
    (X₁ : Matrix x r' ℝ) (S₁ : Matrix r' r' ℝ) (V₁ : Matrix a r' ℝ) : Prop where
  schur : D.IsMacroStep ε Φ ρ₀ (D.lift X₀ S₀ V₀) ρ₁
  kstep : D.IsKStep ε ρ₁ X₀ S₀ V₀ K₁
  lstep : D.IsLStep ε ρ₁ X₀ S₀ V₀ L₁
  orthX : X₁ᵀ * X₁ = 1
  orthV : V₁ᵀ * V₁ = 1
  rangeK : ∃ Rk : Matrix r' r ℝ, K₁ = X₁ * Rk
  rangeL : ∃ Rl : Matrix r' r ℝ, L₁ = V₁ * Rl
  sstep : D.IsSStep ε ρ₁ X₀ S₀ V₀ X₁ V₁ S₁

/-! ## Algebra of the operators -/

section Algebra

variable {D : Disc x a}

private theorem vecMulVec_mulVec' {m n : Type*} [Fintype n] (p : m → ℝ) (q t : n → ℝ) :
    Matrix.vecMulVec p q *ᵥ t = (q ⬝ᵥ t) • p := by
  ext i
  simp [Matrix.vecMulVec_mulVec, mul_comm]

/-- `𝒥(ρ) M = 𝒟^{x,+} ρ (M Qˣ 1)ᵀ`. -/
private theorem J_mul_M (ρ : x → ℝ) : D.J ρ * D.M = Matrix.vecMulVec (D.Dp *ᵥ ρ) D.u := by
  ext i j
  simp only [Disc.J, Disc.M, Disc.u, Disc.Q, Matrix.mul_diagonal, Matrix.vecMulVec_apply,
    Matrix.mulVec_diagonal, mul_one]
  ring

private theorem J_M_V (ρ : x → ℝ) {n : Type*} [Fintype n] (V : Matrix a n ℝ) :
    D.J ρ * D.M * V = Matrix.vecMulVec (D.Dp *ᵥ ρ) (Vᵀ *ᵥ D.u) := by
  rw [J_mul_M, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

/-- `M 𝒥(ρ)ᵀ Xⁿ = (M Qˣ 1) ((Xⁿ)ᵀ 𝒟^{x,+} ρ)ᵀ`. -/
private theorem M_Jt_X (ρ : x → ℝ) {n : Type*} [Fintype n] (X : Matrix x n ℝ) :
    D.M * (D.J ρ)ᵀ * X = Matrix.vecMulVec D.u (Xᵀ *ᵥ (D.Dp *ᵥ ρ)) := by
  have h : D.M * (D.J ρ)ᵀ = (D.J ρ * D.M)ᵀ := by
    rw [Matrix.transpose_mul, Disc.M, Matrix.diagonal_transpose]
  rw [h, J_mul_M, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]

private theorem u_apply (hw : ∀ i, 0 < D.w i) (i : a) : D.u i = √(D.w i) * D.Ω i := by
  have _ := hw
  simp [Disc.u, Disc.M, Disc.Q, Matrix.mulVec_diagonal]

/-- `|M Qˣ 1|² = ∑ wₘ (Ωˣₘ)²`. -/
private theorem u_dot_u (hw : ∀ i, 0 < D.w i) : D.u ⬝ᵥ D.u = ∑ i, D.w i * D.Ω i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : √(D.w i) * √(D.w i) = D.w i := Real.mul_self_sqrt (hw i).le
  simp only [u_apply hw]
  calc √(D.w i) * D.Ω i * (√(D.w i) * D.Ω i) = (√(D.w i) * √(D.w i)) * D.Ω i ^ 2 := by ring
    _ = _ := by rw [hs]

/-- `M⁻¹ Qˣ w = M Qˣ 1`. -/
private theorem Minv_Q_w (hw : ∀ i, 0 < D.w i) : D.Minv *ᵥ (D.Q *ᵥ D.w) = D.u := by
  ext i
  have hs : √(D.w i) * √(D.w i) = D.w i := Real.mul_self_sqrt (hw i).le
  have hp : √(D.w i) ≠ 0 := (Real.sqrt_pos.2 (hw i)).ne'
  rw [u_apply hw]
  simp only [Disc.Minv, Disc.Q, Matrix.mulVec_diagonal]
  field_simp
  rw [Real.sq_sqrt (hw i).le]
  ring

/-- `G Qˣ w = X S Vᵀ (M Qˣ 1)` for `G = X S Vᵀ M⁻¹`. -/
private theorem lift_mulVec (hw : ∀ i, 0 < D.w i) (X : Matrix x r ℝ) (S : Matrix r r' ℝ)
    (V : Matrix a r' ℝ) :
    D.lift X S V *ᵥ (D.Q *ᵥ D.w) = X *ᵥ (S *ᵥ (Vᵀ *ᵥ D.u)) := by
  simp only [Disc.lift, ← Matrix.mulVec_mulVec]
  rw [Minv_Q_w hw]

private theorem H_add (G G' : Matrix x a ℝ) : D.H (G + G') = D.H G + D.H G' := by
  simp only [Disc.H, Matrix.add_mulVec, Matrix.mulVec_add, smul_add]

private theorem H_sub (G G' : Matrix x a ℝ) : D.H (G - G') = D.H G - D.H G' := by
  simp only [Disc.H, Matrix.sub_mulVec, Matrix.mulVec_sub, smul_sub]

private theorem H_smul (c : ℝ) (G : Matrix x a ℝ) : D.H (c • G) = c • D.H G := by
  simp only [Disc.H, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm c]

private theorem H_diagonal_J (q ρ : x → ℝ) :
    D.H (Matrix.diagonal q * D.J ρ) =
      D.moment • (D.Dm *ᵥ (Matrix.diagonal q *ᵥ (D.Dp *ᵥ ρ))) := by
  have h : D.Ω ⬝ᵥ (D.Q *ᵥ D.w) = ∑ i, D.w i * D.Ω i ^ 2 := by
    simp only [Disc.Q, Matrix.mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Disc.H, Disc.J, Disc.moment, Matrix.mul_vecMulVec, vecMulVec_mulVec', h,
    Matrix.mulVec_smul, smul_smul]

/-- `R = ε² q(ε)` with `q(ε) = (ε²/Δt + σˢ + ε² σᵃ)⁻¹`. -/
private theorem R_eq {ε : ℝ} (hε : ε ≠ 0) :
    D.R ε = (ε ^ 2) • Matrix.diagonal fun i => (D.scale ε i)⁻¹ := by
  ext i j
  by_cases hij : i = j
  · subst hij
    have h : 1 / D.dt + D.σs i / ε ^ 2 + D.σa i =
        (ε ^ 2 / D.dt + D.σs i + ε ^ 2 * D.σa i) / ε ^ 2 := by
      field_simp
    simp only [Disc.R, Disc.scale, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, h,
      inv_div]
    rw [div_eq_mul_inv]
  · simp [Disc.R, Matrix.diagonal_apply_ne, hij]

/-- **Eq. (3.4a), (3.4b)** (arXiv 2602.12337, Sec. 3.1).  The Schur complement update is the macro
equation `(ρ¹ - ρ⁰)/Δt + ℋ(G¹) = -σᵃ ρ¹ + Φ` with the full-rank micro update
`G¹ = R (G⁰/Δt - (1/ε) 𝒜(G⁰) (I - (1/|D_Ω|) w 1ᵀ) - (1/ε²) 𝒥(ρ¹))`. -/
theorem isMacroStep_iff (ε : ℝ) (Φ ρ₀ ρ₁ : x → ℝ) (G₀ : Matrix x a ℝ) :
    D.IsMacroStep ε Φ ρ₀ G₀ ρ₁ ↔
      (1 / D.dt) • (ρ₁ - ρ₀) +
          D.H (D.R ε * ((1 / D.dt) • G₀ - (1 / ε) • (D.A G₀ * D.avg) - (1 / ε ^ 2) • D.J ρ₁)) =
        -(D.sigA *ᵥ ρ₁) + Φ := by
  have h1 : D.H (D.R ε * ((1 / D.dt) • G₀ - (1 / ε) • (D.A G₀ * D.avg) - (1 / ε ^ 2) • D.J ρ₁)) =
      D.H (D.R ε * ((1 / D.dt) • G₀ - (1 / ε) • (D.A G₀ * D.avg))) -
        (1 / ε ^ 2) • D.H (D.R ε * D.J ρ₁) := by
    rw [Matrix.mul_sub _ _ (_ • D.J ρ₁), H_sub, Matrix.mul_smul, H_smul]
  rw [Disc.IsMacroStep, h1]
  constructor <;> intro h
  · linear_combination (norm := module) h
  · linear_combination (norm := module) h

private theorem gram_injective {d : x → ℝ} (hd : ∀ i, 0 < d i) {X : Matrix x r ℝ}
    (hX : Xᵀ * X = 1) {t : r → ℝ} (h : (Xᵀ * Matrix.diagonal d * X) *ᵥ t = 0) : t = 0 := by
  have h1 : (X *ᵥ t) ⬝ᵥ (Matrix.diagonal d *ᵥ (X *ᵥ t)) = 0 := by
    have h2 : t ⬝ᵥ ((Xᵀ * Matrix.diagonal d * X) *ᵥ t) = 0 := by rw [h]; simp
    simpa only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] using h2
  have h3 : ∑ i, d i * ((X *ᵥ t) i) ^ 2 = 0 := by
    rw [← h1]
    simp only [Matrix.mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : X *ᵥ t = 0 := by
    ext i
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => mul_nonneg (hd i).le (sq_nonneg _)).1 h3 i (mem_univ i)
    simpa [(hd i).ne'] using h5
  calc t = (Xᵀ * X) *ᵥ t := by rw [hX, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]

private theorem gram_isUnit {d : x → ℝ} (hd : ∀ i, 0 < d i) {X : Matrix x r ℝ}
    (hX : Xᵀ * X = 1) : IsUnit (Xᵀ * Matrix.diagonal d * X).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨t, ht, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  exact ht (gram_injective hd hX h0)

private theorem dot_mulVec_self {X : Matrix x r ℝ} (hX : Xᵀ * X = 1) (t : r → ℝ) :
    (X *ᵥ t) ⬝ᵥ (X *ᵥ t) = t ⬝ᵥ t := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← dotProduct_comm, Matrix.mulVec_mulVec,
    hX, Matrix.one_mulVec]

private theorem sigS_sigSInv (hσ : ∀ i, 0 < D.σs i) (y : x → ℝ) :
    D.sigS *ᵥ (D.sigSInv *ᵥ y) = y := by
  ext i
  simp [Disc.sigS, Disc.sigSInv, Matrix.mulVec_diagonal, (hσ i).ne']

/-- **Sec. 4.2, the oblique projector** (arXiv 2602.12337).  For `Xᵀ X = 1` and `σˢ > 0` the matrix
`Xᵀ σˢ X` is invertible (the paper assumes this; here it is derived) and
`X (Xᵀ σˢ X)⁻¹ Xᵀ σˢ` fixes every vector of `Range X`.  It is the library's `obliqueProj` with
selection `σˢ X`. -/
theorem oblique_fixes (hσ : ∀ i, 0 < D.σs i) {X : Matrix x r ℝ} (hX : Xᵀ * X = 1) {y : x → ℝ}
    (hy : ∃ z, X *ᵥ z = y) :
    IsUnit (Xᵀ * D.sigS * X).det ∧ (X * (Xᵀ * D.sigS * X)⁻¹ * Xᵀ * D.sigS) *ᵥ y = y := by
  obtain ⟨z, rfl⟩ := hy
  have hu : IsUnit (Xᵀ * D.sigS * X).det := gram_isUnit hσ hX
  have ht : (D.sigS * X)ᵀ = Xᵀ * D.sigS := by
    rw [Matrix.transpose_mul, Disc.sigS, Matrix.diagonal_transpose]
  have h : X * (Xᵀ * D.sigS * X)⁻¹ * Xᵀ * D.sigS = obliqueProj X (D.sigS * X) := by
    rw [obliqueProj, ht, Matrix.mul_assoc _ Xᵀ]
  have h' : ((D.sigS * X)ᵀ * X).det = (Xᵀ * D.sigS * X).det := by rw [ht]
  refine ⟨hu, ?_⟩
  rw [h, Matrix.mulVec_mulVec, obliqueProj_mul_self_left (by rw [h']; exact hu)]

/-- **Sec. 4.2, Range of the left basis** (arXiv 2602.12337).  By (4.1a) and `K¹ = X¹ R_K`,
`-(σˢ)⁻¹ 𝒟^{x,+} ρ¹ ∈ Range X¹`, provided `(V⁰)ᵀ M Qˣ 1 ≠ 0`.  The paper states the inclusion
without this hypothesis; `ap_fails_of_degenerate_right` shows that it is needed. -/
theorem mem_rangeX {ρ₁ : x → ℝ} {V₀ : Matrix a r ℝ} {K₁ : Matrix x r ℝ} {X₁ : Matrix x r' ℝ}
    {Rk : Matrix r' r ℝ} (hK : K₁ = -(D.sigSInv * (D.J ρ₁ * D.M * V₀))) (hR : K₁ = X₁ * Rk)
    (hc : V₀ᵀ *ᵥ D.u ≠ 0) : ∃ z, X₁ *ᵥ z = -(D.sigSInv *ᵥ (D.Dp *ᵥ ρ₁)) := by
  set c := V₀ᵀ *ᵥ D.u with hcdef
  have hcc : c ⬝ᵥ c ≠ 0 := by simpa using hc
  refine ⟨(1 / (c ⬝ᵥ c)) • (Rk *ᵥ c), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hR, hK, J_M_V, ← hcdef, Matrix.mul_vecMulVec,
    Matrix.neg_mulVec, vecMulVec_mulVec', smul_neg, smul_smul, one_div_mul_cancel hcc, one_smul]

/-- **Sec. 4.2, Range of the right basis** (arXiv 2602.12337).  By (4.1b) and `L¹ = V¹ R_L`,
`M Qˣ 1 ∈ Range V¹`, provided `(X⁰)ᵀ 𝒟^{x,+} ρ¹ ≠ 0`.  The paper states the inclusion without this
hypothesis; `ap_fails_of_degenerate_left` shows that it is needed. -/
theorem mem_rangeV {ρ₁ : x → ℝ} {X₀ : Matrix x r ℝ} {L₁ : Matrix a r ℝ} {V₁ : Matrix a r' ℝ}
    {Rl : Matrix r' r ℝ} (hL : L₁ * (X₀ᵀ * D.sigS * X₀) = -(D.M * (D.J ρ₁)ᵀ * X₀))
    (hR : L₁ = V₁ * Rl) (hq : X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁) ≠ 0) : ∃ z, V₁ *ᵥ z = D.u := by
  set q := X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁) with hqdef
  have hqq : q ⬝ᵥ q ≠ 0 := by simpa using hq
  refine ⟨(-1 / (q ⬝ᵥ q)) • (Rl *ᵥ ((X₀ᵀ * D.sigS * X₀) *ᵥ q)), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hR, Matrix.mulVec_mulVec, hL, M_Jt_X, ← hqdef,
    Matrix.neg_mulVec, vecMulVec_mulVec', smul_neg, smul_smul]
  have : -1 / (q ⬝ᵥ q) * (q ⬝ᵥ q) = -1 := by field_simp
  rw [this]
  simp

/-- **Sec. 4.2, Eq. (4.2)-(4.5)** (arXiv 2602.12337).  If `S¹` solves the limit S-step (4.1c) and
the two limit directions lie in the new bases, `-(σˢ)⁻¹ 𝒟^{x,+} ρ¹ ∈ Range X¹` and
`M Qˣ 1 ∈ Range V¹`, then `G¹ = X¹ S¹ (V¹)ᵀ M⁻¹` has the flux (4.3)
`ℋ(G¹) = -𝒟^{x,-}(⟨Ω ⊗ Ω⟩_Ω (σˢ)⁻¹ 𝒟^{x,+} ρ¹)`.  This holds for any orthonormal bases with these
ranges, so also for the enriched bases `qr([-(σˢ)⁻¹ 𝒟^{x,+} ρ¹, K¹, X⁰])`, `qr([M Qˣ 1, L¹, V⁰])`
of the augmented scheme, which need no nondegeneracy, and after any truncation that keeps these
two directions. -/
theorem flux_eq_of_mem_range (hw : ∀ i, 0 < D.w i) (hσ : ∀ i, 0 < D.σs i) {ρ₁ : x → ℝ}
    {X₁ : Matrix x r' ℝ} {V₁ : Matrix a r' ℝ} {S₁ : Matrix r' r' ℝ} (hX : X₁ᵀ * X₁ = 1)
    (hV : V₁ᵀ * V₁ = 1) (hS : X₁ᵀ * D.sigS * X₁ * S₁ = -(X₁ᵀ * D.J ρ₁ * D.M * V₁))
    (hz : ∃ z, X₁ *ᵥ z = -(D.sigSInv *ᵥ (D.Dp *ᵥ ρ₁))) (hv : ∃ v, V₁ *ᵥ v = D.u) :
    D.H (D.lift X₁ S₁ V₁) = -(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρ₁)))) := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨v, hv⟩ := hv
  set g := D.Dp *ᵥ ρ₁ with hg
  set p := V₁ᵀ *ᵥ D.u with hp
  have hpv : p = v := by
    rw [hp, ← hv, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  have hVp : V₁ *ᵥ p = D.u := by rw [hpv, hv]
  have hpp : D.u ⬝ᵥ D.u = p ⬝ᵥ p := by
    rw [← hVp, dot_mulVec_self hV]
  have hzg : D.sigS *ᵥ (X₁ *ᵥ z) = -g := by
    rw [hz, Matrix.mulVec_neg, sigS_sigSInv hσ]
  have hmain : (X₁ᵀ * D.sigS * X₁) *ᵥ (S₁ *ᵥ p - (p ⬝ᵥ p) • z) = 0 := by
    have h1 : (X₁ᵀ * D.sigS * X₁) *ᵥ (S₁ *ᵥ p) = -((p ⬝ᵥ p) • (X₁ᵀ *ᵥ g)) := by
      rw [Matrix.mulVec_mulVec, hS, Matrix.neg_mulVec]
      have h2 : X₁ᵀ * D.J ρ₁ * D.M * V₁ = X₁ᵀ * (D.J ρ₁ * D.M * V₁) := by
        simp only [Matrix.mul_assoc]
      rw [h2, J_M_V, ← Matrix.mulVec_mulVec, vecMulVec_mulVec', Matrix.mulVec_smul]
    have h3 : (X₁ᵀ * D.sigS * X₁) *ᵥ z = -(X₁ᵀ *ᵥ g) := by
      simp only [← Matrix.mulVec_mulVec, hzg, Matrix.mulVec_neg]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h1, h3]
    simp
  have hSp : S₁ *ᵥ p = (p ⬝ᵥ p) • z := sub_eq_zero.1 (gram_injective hσ hX hmain)
  have hpp' := u_dot_u (D := D) hw
  rw [Disc.H, lift_mulVec hw, ← hp, hSp, Matrix.mulVec_smul, hz, Disc.moment, ← hpp', hpp]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_neg, smul_neg, smul_smul]

/-- **Sec. 4.2, the limit macro update** (arXiv 2602.12337).  Under (4.1a-c), with
`K¹ = X¹ R_K`, `L¹ = V¹ R_L` and the nondegeneracy `(V⁰)ᵀ M Qˣ 1 ≠ 0`, `(X⁰)ᵀ 𝒟^{x,+} ρ¹ ≠ 0`, the
low-rank `G¹` has the flux (4.3), and the macro equation
`(ρ¹ - ρ⁰)/Δt + ℋ(G¹) + σᵃ ρ¹ = Φ` is the implicit diffusion scheme `IsDiffusionStep`. -/
theorem formal_ap (hw : ∀ i, 0 < D.w i) (hσ : ∀ i, 0 < D.σs i) {ρ₀ ρ₁ Φ : x → ℝ}
    {X₀ : Matrix x r ℝ} {V₀ : Matrix a r ℝ} {K₁ : Matrix x r ℝ} {L₁ : Matrix a r ℝ}
    {X₁ : Matrix x r' ℝ} {V₁ : Matrix a r' ℝ} {S₁ : Matrix r' r' ℝ} {Rk Rl : Matrix r' r ℝ}
    (hlim : D.IsFormalLimit ρ₁ X₀ V₀ K₁ L₁ X₁ V₁ S₁) (hX : X₁ᵀ * X₁ = 1) (hV : V₁ᵀ * V₁ = 1)
    (hRk : K₁ = X₁ * Rk) (hRl : L₁ = V₁ * Rl) (hc : V₀ᵀ *ᵥ D.u ≠ 0)
    (hq : X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁) ≠ 0) :
    D.H (D.lift X₁ S₁ V₁) = -(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρ₁)))) ∧
      ((1 / D.dt) • (ρ₁ - ρ₀) + D.H (D.lift X₁ S₁ V₁) + D.sigA *ᵥ ρ₁ = Φ ↔
        D.IsDiffusionStep Φ ρ₀ ρ₁) := by
  have hH := flux_eq_of_mem_range hw hσ hX hV hlim.sstep (mem_rangeX hlim.kstep hRk hc)
    (mem_rangeV hlim.lstep hRl hq)
  refine ⟨hH, ?_⟩
  rw [hH, Disc.IsDiffusionStep]
  simp only [sub_eq_add_neg]

end Algebra

/-! ## The limit `ε → 0` -/

section Asymptotics

variable {ι : Type*} {F : Filter ι} {D : Disc x a}

/-- The family of matrices `f` is entrywise bounded along the filter `F`. -/
def EntryBdd {m n : Type*} (F : Filter ι) (f : ι → Matrix m n ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ e in F, ∀ i j, |f e i j| ≤ C

private theorem EntryBdd.congr' {m n : Type*} {f g : ι → Matrix m n ℝ} (hf : EntryBdd F f)
    (h : f =ᶠ[F] g) : EntryBdd F g := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  filter_upwards [hC, h] with e he hfg
  rw [← hfg]
  exact he

private theorem EntryBdd.of_tendsto {m n : Type*} [Fintype m] [Fintype n] {f : ι → Matrix m n ℝ}
    {A : Matrix m n ℝ} (h : Tendsto f F (𝓝 A)) : EntryBdd F f := by
  refine ⟨∑ i, ∑ j, (|A i j| + 1), ?_⟩
  have h1 : ∀ᶠ e in F, ∀ i j, |f e i j| < |A i j| + 1 := eventually_all.2 fun i =>
    eventually_all.2 fun j =>
      ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j).abs).eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [h1] with e he i j
  calc |f e i j| ≤ |A i j| + 1 := (he i j).le
    _ ≤ ∑ j, (|A i j| + 1) := Finset.single_le_sum (f := fun j => |A i j| + 1)
        (fun _ _ => by positivity) (mem_univ j)
    _ ≤ ∑ i, ∑ j, (|A i j| + 1) := Finset.single_le_sum (f := fun i => ∑ j, (|A i j| + 1))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (mem_univ i)

private theorem EntryBdd.const {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    EntryBdd F fun _ => A :=
  EntryBdd.of_tendsto tendsto_const_nhds

private theorem EntryBdd.mul {l m n : Type*} [Fintype m] {f : ι → Matrix l m ℝ}
    {g : ι → Matrix m n ℝ} (hf : EntryBdd F f) (hg : EntryBdd F g) :
    EntryBdd F fun e => f e * g e := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨Fintype.card m * (C₁ * C₂), ?_⟩
  filter_upwards [h₁, h₂] with e h₁ h₂ i j
  rw [Matrix.mul_apply]
  calc |∑ k, f e i k * g e k j| ≤ ∑ k, |f e i k * g e k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : m, C₁ * C₂ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (h₁ i k) (h₂ k j) (abs_nonneg _) ((abs_nonneg _).trans (h₁ i k))
    _ = _ := by simp

private theorem EntryBdd.add {m n : Type*} {f g : ι → Matrix m n ℝ} (hf : EntryBdd F f)
    (hg : EntryBdd F g) : EntryBdd F fun e => f e + g e := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with e h₁ h₂ i j
  exact (abs_add_le _ _).trans (add_le_add (h₁ i j) (h₂ i j))

private theorem EntryBdd.neg {m n : Type*} {f : ι → Matrix m n ℝ} (hf : EntryBdd F f) :
    EntryBdd F fun e => -f e := by
  obtain ⟨C, h⟩ := hf
  exact ⟨C, h.mono fun _ he i j => by simpa using he i j⟩

private theorem EntryBdd.sub {m n : Type*} {f g : ι → Matrix m n ℝ} (hf : EntryBdd F f)
    (hg : EntryBdd F g) : EntryBdd F fun e => f e - g e := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem EntryBdd.transpose {m n : Type*} {f : ι → Matrix m n ℝ} (hf : EntryBdd F f) :
    EntryBdd F fun e => (f e)ᵀ := by
  obtain ⟨C, h⟩ := hf
  exact ⟨C, h.mono fun _ he i j => he j i⟩

private theorem EntryBdd.smul {m n : Type*} {f : ι → Matrix m n ℝ} (hf : EntryBdd F f) {s : ι → ℝ}
    (hs : ∃ C : ℝ, ∀ᶠ e in F, |s e| ≤ C) : EntryBdd F fun e => s e • f e := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hs
  refine ⟨C₂ * C₁, ?_⟩
  filter_upwards [h₁, h₂] with e h₁ h₂ i j
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul h₂ (h₁ i j) (abs_nonneg _) ((abs_nonneg _).trans h₂)

private theorem EntryBdd.tendsto_smul {m n : Type*} {f : ι → Matrix m n ℝ} (hf : EntryBdd F f)
    {s : ι → ℝ} (hs : Tendsto s F (𝓝 0)) : Tendsto (fun e => s e • f e) F (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h0 : Tendsto (fun e => |s e| * C) F (𝓝 0) := by simpa using hs.abs.mul_const C
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [hC] with e he
  simpa [abs_mul] using mul_le_mul_of_nonneg_left (he i j) (abs_nonneg (s e))

private theorem abs_entry_le_one {X : Matrix x r ℝ} (h : Xᵀ * X = 1) (i : x) (j : r) :
    |X i j| ≤ 1 := by
  have h1 : ∑ k, X k j * X k j = 1 := by
    have := congrFun (congrFun h j) j
    simpa [Matrix.mul_apply] using this
  have h2 : X i j * X i j ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun k => X k j * X k j) (fun k _ => mul_self_nonneg _)
      (mem_univ i)
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

private theorem EntryBdd.of_orth {X : ι → Matrix x r ℝ} (h : ∀ᶠ e in F, (X e)ᵀ * X e = 1) :
    EntryBdd F X :=
  ⟨1, h.mono fun _ he i j => abs_entry_le_one he i j⟩

private theorem tendsto_mul_bdd {l m n : Type*} [Fintype m] {E : ι → Matrix l m ℝ}
    {f : ι → Matrix m n ℝ} (hE : Tendsto E F (𝓝 0)) (hf : EntryBdd F f) :
    Tendsto (fun e => E e * f e) F (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h0 : Tendsto (fun e => ∑ k, |E e i k| * C) F (𝓝 0) := by
    have h1 : ∀ k, Tendsto (fun e => |E e i k| * C) F (𝓝 0) := fun k => by
      simpa using ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hE i) k).abs).mul_const C
    simpa using tendsto_finsetSum univ fun k _ => h1 k
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [hC] with e he
  rw [Real.norm_eq_abs, Matrix.mul_apply]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (he k j) (abs_nonneg _))

private theorem tendsto_bdd_mul {l m n : Type*} [Fintype m] {E : ι → Matrix m n ℝ}
    {f : ι → Matrix l m ℝ} (hf : EntryBdd F f) (hE : Tendsto E F (𝓝 0)) :
    Tendsto (fun e => f e * E e) F (𝓝 0) := by
  have h1 : Tendsto (fun e => (E e)ᵀ) F (𝓝 0) := by
    have h0 := ((Continuous.matrix_transpose continuous_id).tendsto (0 : Matrix m n ℝ)).comp hE
    simpa [Function.comp_def] using h0
  have h2 := tendsto_mul_bdd h1 hf.transpose
  have h3 := ((Continuous.matrix_transpose continuous_id).tendsto (0 : Matrix n l ℝ)).comp h2
  simpa [Function.comp_def, Matrix.transpose_mul] using h3

private theorem tendsto_mulVec {m n : Type*} [Fintype n] {A : ι → Matrix m n ℝ}
    {b : ι → n → ℝ} {A₀ : Matrix m n ℝ} {b₀ : n → ℝ} (hA : Tendsto A F (𝓝 A₀))
    (hb : Tendsto b F (𝓝 b₀)) : Tendsto (fun e => A e *ᵥ b e) F (𝓝 (A₀ *ᵥ b₀)) :=
  ((continuous_fst.matrix_mulVec continuous_snd).tendsto (A₀, b₀)).comp (hA.prodMk_nhds hb)

private theorem tendsto_mat_mul {l m n : Type*} [Fintype m] {A : ι → Matrix l m ℝ}
    {B : ι → Matrix m n ℝ} {A₀ : Matrix l m ℝ} {B₀ : Matrix m n ℝ} (hA : Tendsto A F (𝓝 A₀))
    (hB : Tendsto B F (𝓝 B₀)) : Tendsto (fun e => A e * B e) F (𝓝 (A₀ * B₀)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (A₀, B₀)).comp (hA.prodMk_nhds hB)

private theorem tendsto_dot {m : Type*} [Fintype m] {f g : ι → m → ℝ} {f₀ g₀ : m → ℝ}
    (hf : Tendsto f F (𝓝 f₀)) (hg : Tendsto g F (𝓝 g₀)) :
    Tendsto (fun e => f e ⬝ᵥ g e) F (𝓝 (f₀ ⬝ᵥ g₀)) :=
  tendsto_finsetSum _ fun i _ => (tendsto_pi_nhds.1 hf i).mul (tendsto_pi_nhds.1 hg i)

/-- The energy estimate behind the Galerkin steps: if `y = X t` solves the Galerkin equation
`Xᵀ d (y - τ) = 0`, it is the best approximation of `τ` in `Range X` in the norm with weight `d`. -/
private theorem galerkin_energy {d : x → ℝ} (hd : ∀ i, 0 < d i) (X : Matrix x r ℝ) (t z : r → ℝ)
    (τ : x → ℝ) (h : Xᵀ *ᵥ (fun i => d i * ((X *ᵥ t) i - τ i)) = 0) :
    ∑ i, d i * ((X *ᵥ t) i - (X *ᵥ z) i) ^ 2 ≤ ∑ i, d i * (τ i - (X *ᵥ z) i) ^ 2 := by
  have h0 : (X *ᵥ (t - z)) ⬝ᵥ (fun i => d i * ((X *ᵥ t) i - τ i)) = 0 := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, h, dotProduct_zero]
  have h1 : ∑ i, d i * ((X *ᵥ t) i - (X *ᵥ z) i) * ((X *ᵥ t) i - τ i) = 0 := by
    rw [← h0, Matrix.mulVec_sub]
    simp only [dotProduct, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, d i * (τ i - (X *ᵥ z) i) ^ 2 =
      ∑ i, d i * ((X *ᵥ t) i - (X *ᵥ z) i) ^ 2 + ∑ i, d i * ((X *ᵥ t) i - τ i) ^ 2 -
        2 * ∑ i, d i * ((X *ᵥ t) i - (X *ᵥ z) i) * ((X *ᵥ t) i - τ i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : 0 ≤ ∑ i, d i * ((X *ᵥ t) i - τ i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)
  rw [h2, h1]
  linarith

/-- Galerkin solutions converge if their targets and some elements of the ranges do, with no
convergence of the bases. -/
private theorem tendsto_of_galerkin {d : ι → x → ℝ} {d₀ : x → ℝ} (hd₀ : ∀ i, 0 < d₀ i)
    (hd : Tendsto d F (𝓝 d₀)) {X : ι → Matrix x r ℝ} {t z : ι → r → ℝ} {τ : ι → x → ℝ}
    {ξ : x → ℝ} (h : ∀ᶠ e in F, (X e)ᵀ *ᵥ (fun i => d e i * ((X e *ᵥ t e) i - τ e i)) = 0)
    (hτ : Tendsto τ F (𝓝 ξ)) (hz : Tendsto (fun e => X e *ᵥ z e) F (𝓝 ξ)) :
    Tendsto (fun e => X e *ᵥ t e) F (𝓝 ξ) := by
  have hlo : ∀ᶠ e in F, ∀ i, d₀ i / 2 < d e i := eventually_all.2 fun i =>
    (tendsto_pi_nhds.1 hd i).eventually (lt_mem_nhds (by linarith [hd₀ i]))
  have hhi : ∀ᶠ e in F, ∀ i, d e i < 2 * d₀ i := eventually_all.2 fun i =>
    (tendsto_pi_nhds.1 hd i).eventually (gt_mem_nhds (by linarith [hd₀ i]))
  have hf : Tendsto (fun e => ∑ i, 2 * d₀ i * (τ e i - (X e *ᵥ z e) i) ^ 2) F (𝓝 0) := by
    have h1 : ∀ i, Tendsto (fun e => 2 * d₀ i * (τ e i - (X e *ᵥ z e) i) ^ 2) F (𝓝 0) := fun i => by
      have h2 := ((tendsto_pi_nhds.1 hτ i).sub (tendsto_pi_nhds.1 hz i)).pow 2
      simpa using h2.const_mul (2 * d₀ i)
    simpa using tendsto_finsetSum univ fun i _ => h1 i
  have hkey : ∀ᶠ e in F, ∀ i, d₀ i / 2 * ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2 ≤
      ∑ i, 2 * d₀ i * (τ e i - (X e *ᵥ z e) i) ^ 2 := by
    filter_upwards [h, hlo, hhi] with e he hl hh i
    have hd' : ∀ i, 0 < d e i := fun i => lt_trans (by linarith [hd₀ i]) (hl i)
    calc d₀ i / 2 * ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2
        ≤ d e i * ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2 :=
          mul_le_mul_of_nonneg_right (hl i).le (sq_nonneg _)
      _ ≤ ∑ i, d e i * ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2 :=
          Finset.single_le_sum (f := fun i => d e i * ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2)
            (fun j _ => mul_nonneg (hd' j).le (sq_nonneg _)) (mem_univ i)
      _ ≤ ∑ i, d e i * (τ e i - (X e *ᵥ z e) i) ^ 2 :=
          galerkin_energy hd' (X e) (t e) (z e) (τ e) he
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hh j).le (sq_nonneg _)
  refine tendsto_pi_nhds.2 fun i => ?_
  have h2 : Tendsto (fun e => ((X e *ᵥ t e) i - (X e *ᵥ z e) i) ^ 2) F (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_
      (by simpa using hf.const_mul (2 / d₀ i))
    filter_upwards [hkey] with e he
    have h3 := he i
    have h4 := hd₀ i
    rw [div_mul_eq_mul_div, le_div_iff₀ h4]
    nlinarith
  have h3 : Tendsto (fun e => (X e *ᵥ t e) i - (X e *ᵥ z e) i) F (𝓝 0) := by
    have h4 := h2.sqrt
    simp only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h4
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h4
  simpa using h3.add (tendsto_pi_nhds.1 hz i)

private theorem exists_pos_le (d₀ : x → ℝ) (hd₀ : ∀ i, 0 < d₀ i) : ∃ m > 0, ∀ i, m ≤ d₀ i := by
  rcases isEmpty_or_nonempty x with hx | hx
  · exact ⟨1, one_pos, fun i => (hx.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min d₀
    exact ⟨d₀ i₀, hd₀ i₀, hi₀⟩

/-- Galerkin solutions are bounded if the right-hand sides are. -/
private theorem EntryBdd.of_galerkin {n : Type*} [Fintype n] {d : ι → x → ℝ} {d₀ : x → ℝ}
    (hd₀ : ∀ i, 0 < d₀ i) (hd : Tendsto d F (𝓝 d₀)) {X : ι → Matrix x r ℝ}
    (hX : ∀ᶠ e in F, (X e)ᵀ * X e = 1) {S : ι → Matrix r n ℝ} {B : ι → Matrix x n ℝ}
    (hB : EntryBdd F B)
    (h : ∀ᶠ e in F, ((X e)ᵀ * Matrix.diagonal (d e) * X e) * S e = (X e)ᵀ * B e) :
    EntryBdd F S := by
  obtain ⟨m, hm, hm'⟩ := exists_pos_le d₀ hd₀
  obtain ⟨C, hC⟩ := hB
  have hlo : ∀ᶠ e in F, ∀ i, m / 2 < d e i := eventually_all.2 fun i =>
    (tendsto_pi_nhds.1 hd i).eventually (lt_mem_nhds (by linarith [hm' i]))
  have hm2 : 0 < m / 2 := by linarith
  refine ⟨(Fintype.card x : ℝ) * C ^ 2 / (m / 2) ^ 2 + 1, ?_⟩
  filter_upwards [hX, hC, hlo, h] with e hXe hCe hl he k j
  have hd' : ∀ i, 0 < d e i := fun i => hm2.trans (hl i)
  set t : r → ℝ := fun k => S e k j with ht
  set b : x → ℝ := fun i => B e i j with hb
  have hcol : ((X e)ᵀ * Matrix.diagonal (d e) * X e) *ᵥ t = (X e)ᵀ *ᵥ b := by
    funext k
    exact congrFun (congrFun he k) j
  have hgal : (X e)ᵀ *ᵥ (fun i => d e i * ((X e *ᵥ t) i - b i / d e i)) = 0 := by
    have h1 : (fun i => d e i * ((X e *ᵥ t) i - b i / d e i)) =
        Matrix.diagonal (d e) *ᵥ (X e *ᵥ t) - b := by
      ext i
      have := (hd' i).ne'
      simp only [Pi.sub_apply, Matrix.mulVec_diagonal]
      field_simp
    rw [h1, Matrix.mulVec_sub, sub_eq_zero, ← hcol]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 := galerkin_energy hd' (X e) t 0 _ hgal
  simp only [Matrix.mulVec_zero, Pi.zero_apply, sub_zero] at h2
  have h3 : (m / 2) * (t ⬝ᵥ t) ≤ ∑ i, d e i * (X e *ᵥ t) i ^ 2 := by
    rw [← dot_mulVec_self hXe, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_right (hl i).le (mul_self_nonneg ((X e *ᵥ t) i))
    nlinarith
  have h4 : ∑ i, d e i * (b i / d e i) ^ 2 ≤ (Fintype.card x : ℝ) * (C ^ 2 / (m / 2)) := by
    have h5 : ∀ i ∈ (univ : Finset x), d e i * (b i / d e i) ^ 2 ≤ C ^ 2 / (m / 2) := fun i _ => by
      have h6 : d e i * (b i / d e i) ^ 2 = b i ^ 2 / d e i := by
        have := (hd' i).ne'
        field_simp
      rw [h6]
      have h7 : b i ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs (b i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hCe i j) 2
      exact div_le_div₀ (sq_nonneg _) h7 hm2 (hl i).le
    simpa using Finset.sum_le_sum h5
  have h5 : t k ^ 2 ≤ t ⬝ᵥ t := by
    simpa [dotProduct, sq] using Finset.single_le_sum (f := fun k => t k * t k)
      (fun k _ => mul_self_nonneg _) (mem_univ k)
  have h6 : t k ^ 2 ≤ (Fintype.card x : ℝ) * C ^ 2 / (m / 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h7 : (m / 2) * t k ^ 2 ≤ (Fintype.card x : ℝ) * (C ^ 2 / (m / 2)) := by
      have := mul_le_mul_of_nonneg_left h5 hm2.le
      linarith
    have h8 := mul_le_mul_of_nonneg_left h7 hm2.le
    have h9 : m / 2 * ((Fintype.card x : ℝ) * (C ^ 2 / (m / 2))) =
        (Fintype.card x : ℝ) * C ^ 2 := by
      field_simp
    nlinarith
  have h10 : |t k| ≤ (Fintype.card x : ℝ) * C ^ 2 / (m / 2) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|t k| - 1), sq_abs (t k)]
  exact h10

private theorem Top_mulVec (q ρ : x → ℝ) :
    D.Top q *ᵥ ρ = (1 / D.dt) • ρ + D.sigA *ᵥ ρ -
      D.moment • (D.Dm *ᵥ (Matrix.diagonal q *ᵥ (D.Dp *ᵥ ρ))) := by
  simp only [Disc.Top, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem moment_nonneg (hD : D.Admissible) : 0 ≤ D.moment := by
  have h1 : 0 ≤ D.vol := by
    rw [← hD.vol_eq]
    exact Finset.sum_nonneg fun i _ => (hD.w_pos i).le
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hD.w_pos i).le (sq_nonneg _))

private theorem dot_diagonal_nonneg {q : x → ℝ} (hq : ∀ i, 0 ≤ q i) (y : x → ℝ) :
    0 ≤ y ⬝ᵥ (Matrix.diagonal q *ᵥ y) := by
  simp only [Matrix.mulVec_diagonal, dotProduct]
  exact Finset.sum_nonneg fun i _ => by nlinarith [hq i, mul_nonneg (hq i) (mul_self_nonneg (y i))]

private theorem Top_det_ne (hD : D.Admissible) {q : x → ℝ} (hq : ∀ i, 0 ≤ q i) :
    (D.Top q).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  rw [Top_mulVec] at h0
  have h1 : v ⬝ᵥ ((1 / D.dt) • v + D.sigA *ᵥ v -
      D.moment • (D.Dm *ᵥ (Matrix.diagonal q *ᵥ (D.Dp *ᵥ v)))) = 0 := by
    rw [h0, dotProduct_zero]
  have h3 : v ⬝ᵥ (D.Dm *ᵥ (Matrix.diagonal q *ᵥ (D.Dp *ᵥ v))) =
      -((D.Dp *ᵥ v) ⬝ᵥ (Matrix.diagonal q *ᵥ (D.Dp *ᵥ v))) := by
    rw [hD.sbp, Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  rw [dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, h3, smul_eq_mul,
    smul_eq_mul] at h1
  have h2 : 0 ≤ v ⬝ᵥ (D.sigA *ᵥ v) := dot_diagonal_nonneg hD.σa_nonneg v
  have h4 := mul_nonneg (moment_nonneg hD) (dot_diagonal_nonneg hq (D.Dp *ᵥ v))
  have h5 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h6 : 0 < 1 / D.dt := one_div_pos.2 hD.dt_pos
  have h7 : (1 / D.dt) * (v ⬝ᵥ v) = 0 := by nlinarith
  have h8 : v ⬝ᵥ v = 0 := by
    rcases mul_eq_zero.1 h7 with h | h
    · exact absurd h h6.ne'
    · exact h
  exact dotProduct_self_eq_zero.1 h8

/-- `IsDiffusionStep` as the linear system with the implicit diffusion operator. -/
private theorem isDiffusionStep_iff {Φ ρ₀ ρ₁ : x → ℝ} :
    D.IsDiffusionStep Φ ρ₀ ρ₁ ↔
      D.Top (fun i => (D.σs i)⁻¹) *ᵥ ρ₁ = (1 / D.dt) • ρ₀ + Φ := by
  rw [Top_mulVec, Disc.IsDiffusionStep]
  change _ - D.moment • (D.Dm *ᵥ (Matrix.diagonal (fun i => (D.σs i)⁻¹) *ᵥ _)) + _ = _ ↔ _
  constructor <;> intro h
  · linear_combination (norm := module) h
  · linear_combination (norm := module) h

private theorem existsUnique_of_det {T : Matrix x x ℝ} (h : T.det ≠ 0) (b : x → ℝ) :
    ∃! y, T *ᵥ y = b := by
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 h
  refine ⟨T⁻¹ *ᵥ b, ?_, fun y (hy : T *ᵥ y = b) => ?_⟩
  · change T *ᵥ (T⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · rw [← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- **Sec. 4.2, the limit scheme is well posed** (arXiv 2602.12337).  The implicit diffusion step
has exactly one solution.  This uses the summation by parts and is not discussed in the paper. -/
theorem existsUnique_diffusion (hD : D.Admissible) (Φ ρ₀ : x → ℝ) :
    ∃! ρ₁, D.IsDiffusionStep Φ ρ₀ ρ₁ := by
  simp only [isDiffusionStep_iff]
  exact existsUnique_of_det (Top_det_ne hD fun i => (inv_pos.2 (hD.σs_pos i)).le) _

private theorem tendsto_solve {T : ι → Matrix x x ℝ} {T₀ : Matrix x x ℝ} {b : ι → x → ℝ}
    {b₀ ρ₀ : x → ℝ} {ρ : ι → x → ℝ} (hT : Tendsto T F (𝓝 T₀)) (hb : Tendsto b F (𝓝 b₀))
    (hdet : T₀.det ≠ 0) (h : ∀ᶠ e in F, T e *ᵥ ρ e = b e) (h₀ : T₀ *ᵥ ρ₀ = b₀) :
    Tendsto ρ F (𝓝 ρ₀) := by
  have hd : Tendsto (fun e => (T e).det) F (𝓝 T₀.det) :=
    ((continuous_id.matrix_det).tendsto T₀).comp hT
  have ha : Tendsto (fun e => (T e).adjugate) F (𝓝 T₀.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto T₀).comp hT
  have hne : ∀ᶠ e in F, (T e).det ≠ 0 := hd.eventually_ne hdet
  have h1 : Tendsto (fun e => (T e).det⁻¹ • ((T e).adjugate *ᵥ b e)) F
      (𝓝 (T₀.det⁻¹ • (T₀.adjugate *ᵥ b₀))) := (hd.inv₀ hdet).smul (tendsto_mulVec ha hb)
  have key : ∀ (A : Matrix x x ℝ) (v : x → ℝ), A.det ≠ 0 →
      A.det⁻¹ • (A.adjugate *ᵥ (A *ᵥ v)) = v := by
    intro A v hA
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
      inv_mul_cancel₀ hA, one_smul]
  rw [← h₀, key _ _ hdet] at h1
  refine h1.congr' ?_
  filter_upwards [h, hne] with e he hn
  rw [← he, key _ _ hn]

end Asymptotics

/-! ## One step of the scheme as `ε → 0` -/

section Limit

local notation "𝓕" => 𝓝[>] (0 : ℝ)

variable {ι : Type*} {D : Disc x a}

private theorem tendsto_scale : Tendsto D.scale 𝓕 (𝓝 D.σs) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_nhdsWithin_of_tendsto_nhds ?_
  have hc : Continuous fun ε : ℝ => D.scale ε i := by
    unfold Disc.scale
    fun_prop
  simpa [Disc.scale] using hc.tendsto 0

private theorem tendsto_scale_inv (hσ : ∀ i, 0 < D.σs i) :
    Tendsto (fun ε i => (D.scale ε i)⁻¹) 𝓕 (𝓝 fun i => (D.σs i)⁻¹) :=
  tendsto_pi_nhds.2 fun i => (tendsto_pi_nhds.1 tendsto_scale i).inv₀ (hσ i).ne'

private theorem tendsto_diagonal {q : ι → x → ℝ} {F : Filter ι} {q₀ : x → ℝ}
    (hq : Tendsto q F (𝓝 q₀)) :
    Tendsto (fun e => Matrix.diagonal (q e)) F (𝓝 (Matrix.diagonal q₀)) :=
  ((continuous_id.matrix_diagonal).tendsto q₀).comp hq

private theorem scale_pos (hD : D.Admissible) (ε : ℝ) (i : x) : 0 < D.scale ε i := by
  have h1 := hD.σs_pos i
  have h2 := hD.σa_nonneg i
  have h3 := hD.dt_pos
  unfold Disc.scale
  positivity

private theorem diag_scale (ε : ℝ) :
    Matrix.diagonal (D.scale ε) = (ε ^ 2 / D.dt) • 1 + D.sigS + (ε ^ 2) • D.sigA := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Disc.scale, Disc.sigS, Disc.sigA]
  · simp [Disc.sigS, Disc.sigA, h]

private theorem gram_scale (ε : ℝ) {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix x n ℝ}
    (hX : Xᵀ * X = 1) :
    Xᵀ * Matrix.diagonal (D.scale ε) * X =
      (ε ^ 2 / D.dt) • 1 + Xᵀ * D.sigS * X + (ε ^ 2) • (Xᵀ * D.sigA * X) := by
  rw [diag_scale, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, hX]

private theorem scaled_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {ε dt : ℝ} (hε : ε ≠ 0)
    {K K₀ b c s p : E} :
    (1 / dt) • (K - K₀) = -(1 / ε) • b - (1 / ε ^ 2) • c - (1 / ε ^ 2) • s - p ↔
      (ε ^ 2 / dt) • K + s + (ε ^ 2) • p = (ε ^ 2 / dt) • K₀ - ε • b - c := by
  constructor
  · intro h
    have h' : (ε ^ 2) • ((1 / dt) • (K - K₀)) =
        (ε ^ 2) • (-(1 / ε) • b - (1 / ε ^ 2) • c - (1 / ε ^ 2) • s - p) := by rw [h]
    have e1 : ε ^ 2 * (1 / dt) = ε ^ 2 / dt := by ring
    have e2 : ε ^ 2 * -(1 / ε) = -ε := by field_simp
    have e3 : ε ^ 2 * (1 / ε ^ 2) = 1 := by field_simp
    simp only [smul_sub, smul_smul, e1, e2, e3, one_smul] at h'
    linear_combination (norm := module) h'
  · intro h
    have h' : (1 / ε ^ 2) • ((ε ^ 2 / dt) • K + s + (ε ^ 2) • p) =
        (1 / ε ^ 2) • ((ε ^ 2 / dt) • K₀ - ε • b - c) := by rw [h]
    have e1 : 1 / ε ^ 2 * (ε ^ 2 / dt) = 1 / dt := by field_simp
    have e2 : 1 / ε ^ 2 * ε ^ 2 = 1 := by field_simp
    have e3 : 1 / ε ^ 2 * ε = 1 / ε := by field_simp
    simp only [smul_add, smul_sub, smul_smul, e1, e2, e3, one_smul] at h'
    linear_combination (norm := module) h'

variable {ρ₁ : x → ℝ} {ε : ℝ} {X₀ : Matrix x r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix a r ℝ}

private theorem kstep_scaled (hε : ε ≠ 0) {K₁ : Matrix x r ℝ} :
    D.IsKStep ε ρ₁ X₀ S₀ V₀ K₁ ↔ Matrix.diagonal (D.scale ε) * K₁ =
      (ε ^ 2 / D.dt) • (X₀ * S₀) - ε • (D.B (X₀ * S₀ * V₀ᵀ) * V₀) -
        Matrix.vecMulVec (D.Dp *ᵥ ρ₁) (V₀ᵀ *ᵥ D.u) := by
  rw [Disc.IsKStep, scaled_iff hε, J_M_V, diag_scale, Matrix.add_mul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]

private theorem lstep_scaled (hε : ε ≠ 0) (hX : X₀ᵀ * X₀ = 1) {L₁ : Matrix a r ℝ} :
    D.IsLStep ε ρ₁ X₀ S₀ V₀ L₁ ↔ L₁ * (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀) =
      (ε ^ 2 / D.dt) • (V₀ * S₀ᵀ) - ε • ((D.B (X₀ * (V₀ * S₀ᵀ)ᵀ))ᵀ * X₀) -
        Matrix.vecMulVec D.u (X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁)) := by
  rw [Disc.IsLStep, scaled_iff hε, M_Jt_X, gram_scale ε hX, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

private theorem sstep_scaled (hε : ε ≠ 0) {X₁ : Matrix x r' ℝ} {V₁ : Matrix a r' ℝ}
    {S₁ : Matrix r' r' ℝ} (hX : X₁ᵀ * X₁ = 1) :
    D.IsSStep ε ρ₁ X₀ S₀ V₀ X₁ V₁ S₁ ↔ (X₁ᵀ * Matrix.diagonal (D.scale ε) * X₁) * S₁ =
      X₁ᵀ * ((ε ^ 2 / D.dt) • (X₀ * S₀ * V₀ᵀ * V₁) -
        ε • (D.B (X₁ * (X₁ᵀ * X₀ * S₀ * V₀ᵀ * V₁) * V₁ᵀ) * V₁) -
        Matrix.vecMulVec (D.Dp *ᵥ ρ₁) (V₁ᵀ *ᵥ D.u)) := by
  have h3 : X₁ᵀ * (X₀ * S₀ * V₀ᵀ * V₁) = X₁ᵀ * X₀ * S₀ * V₀ᵀ * V₁ := by
    simp only [Matrix.mul_assoc]
  have h4 : X₁ᵀ * Matrix.vecMulVec (D.Dp *ᵥ ρ₁) (V₁ᵀ *ᵥ D.u) = X₁ᵀ * D.J ρ₁ * D.M * V₁ := by
    rw [← J_M_V]
    simp only [Matrix.mul_assoc]
  rw [Disc.IsSStep, scaled_iff hε, gram_scale ε hX, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_smul, h3, h4, ← Matrix.mul_assoc X₁ᵀ (D.B _) V₁]

private theorem H_R_J (hε : ε ≠ 0) (ρ : x → ℝ) :
    (1 / ε ^ 2) • D.H (D.R ε * D.J ρ) = D.moment • (D.Dm *ᵥ
      (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *ᵥ (D.Dp *ᵥ ρ))) := by
  rw [R_eq hε, Matrix.smul_mul, H_smul, smul_smul, one_div_mul_cancel (pow_ne_zero 2 hε),
    one_smul, H_diagonal_J]

private theorem macro_scaled (hε : ε ≠ 0) {Φ ρ₀ : x → ℝ} {G₀ : Matrix x a ℝ} :
    D.IsMacroStep ε Φ ρ₀ G₀ ρ₁ ↔ D.Top (fun i => (D.scale ε i)⁻¹) *ᵥ ρ₁ =
      (1 / D.dt) • ρ₀ + Φ - D.H (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *
        ((ε ^ 2 / D.dt) • G₀ - ε • (D.A G₀ * D.avg))) := by
  have h1 := H_R_J (D := D) hε ρ₁
  have h2 : D.R ε * ((1 / D.dt) • G₀ - (1 / ε) • (D.A G₀ * D.avg)) =
      Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *
        ((ε ^ 2 / D.dt) • G₀ - ε • (D.A G₀ * D.avg)) := by
    have e1 : ε ^ 2 * (1 / D.dt) = ε ^ 2 / D.dt := by ring
    have e2 : ε ^ 2 * (1 / ε) = ε := by field_simp
    rw [R_eq hε, Matrix.smul_mul, ← Matrix.mul_smul, smul_sub, smul_smul, smul_smul, e1, e2]
  rw [Disc.IsMacroStep, h1, h2, Top_mulVec]

private theorem continuous_H : Continuous D.H := by
  have h : Continuous fun G : Matrix x a ℝ => D.Dm *ᵥ (G *ᵥ (D.Q *ᵥ D.w)) :=
    continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
  exact (continuous_const_smul (1 / D.vol)).comp h

private theorem EntryBdd.A {G : ι → Matrix x a ℝ} {F : Filter ι} (hG : EntryBdd F G) :
    EntryBdd F fun e => D.A (G e) :=
  (((EntryBdd.const _).mul hG).mul (EntryBdd.const _)).add
    (((EntryBdd.const _).mul hG).mul (EntryBdd.const _))

private theorem EntryBdd.B {G : ι → Matrix x a ℝ} {F : Filter ι} (hG : EntryBdd F G) :
    EntryBdd F fun e => D.B (G e) :=
  ((EntryBdd.A (hG.mul (EntryBdd.const _))).mul (EntryBdd.const _)).mul (EntryBdd.const _)

private theorem tendsto_small {m n : Type*} (dt : ℝ) {N₁ N₂ : ℝ → Matrix m n ℝ}
    (h₁ : EntryBdd 𝓕 N₁) (h₂ : EntryBdd 𝓕 N₂) :
    Tendsto (fun ε => (ε ^ 2 / dt) • N₁ ε - ε • N₂ ε) 𝓕 (𝓝 0) := by
  have h3 : Tendsto (fun ε : ℝ => ε ^ 2 / dt) 𝓕 (𝓝 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have hc : Continuous fun ε : ℝ => ε ^ 2 / dt := by fun_prop
    simpa using hc.tendsto 0
  have h4 : Tendsto (fun ε : ℝ => ε) 𝓕 (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  simpa using (h₁.tendsto_smul h3).sub (h₂.tendsto_smul h4)

/-- **Sec. 4.2, the limit of the density** (arXiv 2602.12337).  Let `ρ¹(ε)` solve the Schur
complement update with data `ρ⁰(ε) → ρ⁰*`, `Φ(ε) → Φ*` and bounded `G⁰(ε)`.  Then `ρ¹(ε)` converges,
as `ε → 0⁺`, to the solution of the implicit diffusion step.  This is a true limit, where the paper
has a formal one, and it uses nothing about the low-rank structure of `G⁰(ε)`: the density update
of the scheme is asymptotic-preserving for every bounded micro state. -/
theorem tendsto_rho (hD : D.Admissible) {Φ ρ₀ ρ₁ : ℝ → x → ℝ} {G₀ : ℝ → Matrix x a ℝ}
    {Φs ρ₀s ρs : x → ℝ} (hΦ : Tendsto Φ 𝓕 (𝓝 Φs)) (hρ₀ : Tendsto ρ₀ 𝓕 (𝓝 ρ₀s))
    (hG : EntryBdd 𝓕 G₀) (hs : ∀ᶠ ε in 𝓕, D.IsMacroStep ε (Φ ε) (ρ₀ ε) (G₀ ε) (ρ₁ ε))
    (hd : D.IsDiffusionStep Φs ρ₀s ρs) : Tendsto ρ₁ 𝓕 (𝓝 ρs) := by
  have hq := tendsto_scale_inv hD.σs_pos
  have hdiag := tendsto_diagonal hq
  have hT : Tendsto (fun ε => D.Top fun i => (D.scale ε i)⁻¹) 𝓕
      (𝓝 (D.Top fun i => (D.σs i)⁻¹)) := by
    have hc : Continuous fun q : x → ℝ => D.Top q := by
      have h1 : Continuous fun q : x → ℝ => D.Dm * Matrix.diagonal q * D.Dp :=
        (continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const
      exact continuous_const.sub ((continuous_const_smul D.moment).comp h1)
    exact (hc.tendsto _).comp hq
  have hY := tendsto_small D.dt hG (hG.A (D := D) |>.mul (EntryBdd.const D.avg))
  have hH : Tendsto (fun ε => D.H (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *
      ((ε ^ 2 / D.dt) • G₀ ε - ε • (D.A (G₀ ε) * D.avg)))) 𝓕 (𝓝 0) := by
    have h1 := tendsto_mat_mul hdiag hY
    have h2 := (continuous_H (D := D)).tendsto _ |>.comp h1
    simpa [Disc.H, Function.comp_def] using h2
  have hb := ((hρ₀.const_smul (1 / D.dt)).add hΦ).sub hH
  rw [sub_zero] at hb
  refine tendsto_solve hT hb (Top_det_ne hD fun i => (inv_pos.2 (hD.σs_pos i)).le) ?_
    (isDiffusionStep_iff.1 hd)
  filter_upwards [hs, self_mem_nhdsWithin] with ε h (hε : 0 < ε)
  exact (macro_scaled hε.ne').1 h

private theorem tendsto_J {F : Filter ι} {ρ : ι → x → ℝ} {ρs : x → ℝ}
    (hρ : Tendsto ρ F (𝓝 ρs)) : Tendsto (fun e => D.J (ρ e)) F (𝓝 (D.J ρs)) := by
  have hc : Continuous fun ρ : x → ℝ => D.J ρ :=
    (continuous_const.matrix_mulVec continuous_id).matrix_vecMulVec continuous_const
  exact (hc.tendsto ρs).comp hρ

private theorem diag_inv_mulVec {d : x → ℝ} (hd : ∀ i, d i ≠ 0) (y : x → ℝ) :
    Matrix.diagonal (fun i => (d i)⁻¹) *ᵥ (Matrix.diagonal d *ᵥ y) = y := by
  ext i
  simp [Matrix.mulVec_diagonal, hd i]

private theorem proj_fix {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix a n ℝ}
    (hV : Vᵀ * V = 1) (w : n → ℝ) : V *ᵥ (Vᵀ *ᵥ (V *ᵥ w)) = V *ᵥ w := by
  rw [Matrix.mulVec_mulVec w Vᵀ V, hV, Matrix.one_mulVec]

private theorem inv_bdd {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (h : ∀ᶠ ε in 𝓕, δ ≤ f ε) :
    ∃ C : ℝ, ∀ᶠ ε in 𝓕, |(f ε)⁻¹| ≤ C :=
  ⟨δ⁻¹, h.mono fun ε hε => by
    rw [abs_of_nonneg (inv_nonneg.2 (hδ.le.trans hε))]
    exact inv_anti₀ hδ hε⟩

/-- If `Vᵀ V = 1` and `V s → u`, the projection satisfies `V Vᵀ u → u`. -/
private theorem tendsto_proj {n : Type*} [Fintype n] [DecidableEq n] {V : ℝ → Matrix a n ℝ}
    {s : ℝ → n → ℝ} {u : a → ℝ} (hV : ∀ᶠ ε in 𝓕, (V ε)ᵀ * V ε = 1)
    (hs : Tendsto (fun ε => V ε *ᵥ s ε) 𝓕 (𝓝 u)) :
    Tendsto (fun ε => V ε *ᵥ ((V ε)ᵀ *ᵥ u)) 𝓕 (𝓝 u) := by
  refine tendsto_of_galerkin (d := fun _ _ => 1) (d₀ := fun _ => 1) (fun _ => one_pos)
    tendsto_const_nhds (τ := fun _ => u) (z := s) ?_ tendsto_const_nhds hs
  filter_upwards [hV] with ε hε
  have h1 : (fun i => (1 : ℝ) * ((V ε *ᵥ ((V ε)ᵀ *ᵥ u)) i - u i)) =
      V ε *ᵥ ((V ε)ᵀ *ᵥ u) - u := by
    ext i
    simp
  rw [h1, Matrix.mulVec_sub, Matrix.mulVec_mulVec _ (V ε)ᵀ (V ε), hε, Matrix.one_mulVec, sub_self]

private theorem tendsto_proj_dot {n : Type*} [Fintype n] [DecidableEq n] {V : ℝ → Matrix a n ℝ}
    {u : a → ℝ} (hV : ∀ᶠ ε in 𝓕, (V ε)ᵀ * V ε = 1)
    (hs : Tendsto (fun ε => V ε *ᵥ ((V ε)ᵀ *ᵥ u)) 𝓕 (𝓝 u)) :
    Tendsto (fun ε => (V ε)ᵀ *ᵥ u ⬝ᵥ (V ε)ᵀ *ᵥ u) 𝓕 (𝓝 (u ⬝ᵥ u)) := by
  refine (tendsto_dot hs hs).congr' ?_
  filter_upwards [hV] with ε hε
  exact dot_mulVec_self hε _

variable {ρ₁ : ℝ → x → ℝ} {ρs : x → ℝ} {X₀ : ℝ → Matrix x r ℝ} {S₀ : ℝ → Matrix r r ℝ}
  {V₀ : ℝ → Matrix a r ℝ} {K₁ : ℝ → Matrix x r ℝ} {L₁ : ℝ → Matrix a r ℝ}
  {X₁ : ℝ → Matrix x r' ℝ} {V₁ : ℝ → Matrix a r' ℝ} {S₁ : ℝ → Matrix r' r' ℝ}

/-- **Sec. 4.2, the limit of the flux** (arXiv 2602.12337).  Let `S¹(ε)` solve the S-step with
orthonormal bases `X¹(ε)`, `V¹(ε)` and let `ρ¹(ε) → ρ*`.  If elements of `Range X¹(ε)` converge to
`-(σˢ)⁻¹ 𝒟^{x,+} ρ*` and elements of `Range V¹(ε)` converge to `M Qˣ 1`, then
`ℋ(G¹(ε)) → -𝒟^{x,-}(⟨Ω ⊗ Ω⟩_Ω (σˢ)⁻¹ 𝒟^{x,+} ρ*)`, the flux (4.3).  The bases need not converge;
this is where the oblique projector of the paper is replaced by the bound for Galerkin solutions.
The captures are exact for the enriched bases of the augmented scheme. -/
theorem tendsto_flux_of_capture (hD : D.Admissible) {z s : ℝ → r' → ℝ}
    (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs)) (hX₀ : EntryBdd 𝓕 X₀) (hV₀ : EntryBdd 𝓕 V₀) (hS₀ : EntryBdd 𝓕 S₀)
    (hX₁ : ∀ᶠ ε in 𝓕, (X₁ ε)ᵀ * X₁ ε = 1) (hV₁ : ∀ᶠ ε in 𝓕, (V₁ ε)ᵀ * V₁ ε = 1)
    (hs : ∀ᶠ ε in 𝓕, D.IsSStep ε (ρ₁ ε) (X₀ ε) (S₀ ε) (V₀ ε) (X₁ ε) (V₁ ε) (S₁ ε))
    (hz : Tendsto (fun ε => X₁ ε *ᵥ z ε) 𝓕 (𝓝 (-(D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))))
    (hv : Tendsto (fun ε => V₁ ε *ᵥ s ε) 𝓕 (𝓝 D.u)) :
    Tendsto (fun ε => D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε))) 𝓕
      (𝓝 (-(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))))) := by
  set v : ℝ → r' → ℝ := fun ε => (V₁ ε)ᵀ *ᵥ D.u with hvdef
  have hVb : EntryBdd 𝓕 V₁ := EntryBdd.of_orth hV₁
  have hXb : EntryBdd 𝓕 X₁ := EntryBdd.of_orth hX₁
  have hvv : Tendsto (fun ε => v ε ⬝ᵥ v ε) 𝓕 (𝓝 (D.u ⬝ᵥ D.u)) :=
    tendsto_proj_dot hV₁ (tendsto_proj hV₁ hv)
  set St : ℝ → Matrix r' r' ℝ := fun ε => (X₁ ε)ᵀ * X₀ ε * S₀ ε * (V₀ ε)ᵀ * V₁ ε with hStdef
  have hSt : EntryBdd 𝓕 St := (((hXb.transpose.mul hX₀).mul hS₀).mul hV₀.transpose).mul hVb
  set Es : ℝ → Matrix x r' ℝ := fun ε => (ε ^ 2 / D.dt) • (X₀ ε * S₀ ε * (V₀ ε)ᵀ * V₁ ε) -
    ε • (D.B (X₁ ε * St ε * (V₁ ε)ᵀ) * V₁ ε) with hEsdef
  have hEs : Tendsto Es 𝓕 (𝓝 0) := tendsto_small D.dt
    (((hX₀.mul hS₀).mul hV₀.transpose).mul hVb)
    ((EntryBdd.B ((hXb.mul hSt).mul hVb.transpose)).mul hVb)
  have hEv : Tendsto (fun ε => Es ε *ᵥ v ε) 𝓕 (𝓝 0) := by
    have h1 := tendsto_mulVec (tendsto_mul_bdd hEs hVb.transpose)
      (tendsto_const_nhds (x := D.u))
    rw [Matrix.zero_mulVec] at h1
    exact h1.congr fun ε => (Matrix.mulVec_mulVec _ _ _).symm
  have hg : Tendsto (fun ε => D.Dp *ᵥ ρ₁ ε) 𝓕 (𝓝 (D.Dp *ᵥ ρs)) :=
    tendsto_mulVec tendsto_const_nhds hρ
  set τ : ℝ → x → ℝ := fun ε => Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *ᵥ
    (Es ε *ᵥ v ε - (v ε ⬝ᵥ v ε) • (D.Dp *ᵥ ρ₁ ε)) with hτdef
  set ξ : x → ℝ := (D.u ⬝ᵥ D.u) • (-(D.sigSInv *ᵥ (D.Dp *ᵥ ρs))) with hξ
  have hτ : Tendsto τ 𝓕 (𝓝 ξ) := by
    have h1 := tendsto_mulVec (tendsto_diagonal (tendsto_scale_inv hD.σs_pos))
      (hEv.sub (hvv.smul hg))
    have h2 : Matrix.diagonal (fun i => (D.σs i)⁻¹) *ᵥ
        ((0 : x → ℝ) - (D.u ⬝ᵥ D.u) • (D.Dp *ᵥ ρs)) = ξ := by
      rw [zero_sub, Matrix.mulVec_neg, Matrix.mulVec_smul, hξ, ← smul_neg]
      rfl
    rwa [h2] at h1
  have hz' : Tendsto (fun ε => X₁ ε *ᵥ ((D.u ⬝ᵥ D.u) • z ε)) 𝓕 (𝓝 ξ) := by
    simpa only [Matrix.mulVec_smul] using hz.const_smul (D.u ⬝ᵥ D.u)
  have hgal : ∀ᶠ ε in 𝓕, (X₁ ε)ᵀ *ᵥ
      (fun i => D.scale ε i * ((X₁ ε *ᵥ (S₁ ε *ᵥ v ε)) i - τ ε i)) = 0 := by
    filter_upwards [hs, hX₁, self_mem_nhdsWithin] with ε h hX (hε : 0 < ε)
    have h1 := (sstep_scaled hε.ne' hX).1 h
    have h3 : (fun i => D.scale ε i * ((X₁ ε *ᵥ (S₁ ε *ᵥ v ε)) i - τ ε i)) =
        Matrix.diagonal (D.scale ε) *ᵥ (X₁ ε *ᵥ (S₁ ε *ᵥ v ε)) -
          (Es ε *ᵥ v ε - (v ε ⬝ᵥ v ε) • (D.Dp *ᵥ ρ₁ ε)) := by
      ext i
      have h4 := (scale_pos hD ε i).ne'
      simp only [hτdef, Matrix.mulVec_diagonal, Pi.sub_apply]
      field_simp
    have h5 : (X₁ ε)ᵀ *ᵥ (Matrix.diagonal (D.scale ε) *ᵥ (X₁ ε *ᵥ (S₁ ε *ᵥ v ε))) =
        (X₁ ε)ᵀ *ᵥ (Es ε *ᵥ v ε - (v ε ⬝ᵥ v ε) • (D.Dp *ᵥ ρ₁ ε)) := by
      have h6 : ((X₁ ε)ᵀ * Matrix.diagonal (D.scale ε) * X₁ ε * S₁ ε) *ᵥ v ε =
          ((X₁ ε)ᵀ * (Es ε - Matrix.vecMulVec (D.Dp *ᵥ ρ₁ ε) (v ε))) *ᵥ v ε :=
        congrArg (· *ᵥ v ε) h1
      simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, vecMulVec_mulVec'] at h6
      exact h6
    rw [h3, Matrix.mulVec_sub, h5, sub_self]
  have hy := tendsto_of_galerkin hD.σs_pos tendsto_scale hgal hτ hz'
  have hH : (fun ε => D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε))) =
      fun ε => (1 / D.vol) • (D.Dm *ᵥ (X₁ ε *ᵥ (S₁ ε *ᵥ v ε))) := by
    funext ε
    rw [Disc.H, lift_mulVec hD.w_pos]
  rw [hH]
  have h1 := (tendsto_mulVec tendsto_const_nhds hy (A := fun _ => D.Dm)).const_smul (1 / D.vol)
  have h2 : (1 / D.vol) • (D.Dm *ᵥ ξ) = -(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))) := by
    simp only [hξ, Matrix.mulVec_smul, Matrix.mulVec_neg, smul_neg, smul_smul, Disc.moment,
      u_dot_u hD.w_pos]
  rwa [h2] at h1

/-- The left capture: under `|(V⁰(ε))ᵀ M Qˣ 1|² ≥ δ > 0` elements of `Range X¹(ε)` converge to
`-(σˢ)⁻¹ 𝒟^{x,+} ρ*`. -/
private theorem capture_left (hD : D.Admissible) (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs))
    (hX₀ : EntryBdd 𝓕 X₀) (hV₀ : EntryBdd 𝓕 V₀) (hS₀ : EntryBdd 𝓕 S₀)
    (hX₁ : ∀ᶠ ε in 𝓕, (X₁ ε)ᵀ * X₁ ε = 1)
    (hk : ∀ᶠ ε in 𝓕, D.IsKStep ε (ρ₁ ε) (X₀ ε) (S₀ ε) (V₀ ε) (K₁ ε))
    (hR : ∀ᶠ ε in 𝓕, ∃ Rk : Matrix r' r ℝ, K₁ ε = X₁ ε * Rk)
    (hc : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (V₀ ε)ᵀ *ᵥ D.u ⬝ᵥ (V₀ ε)ᵀ *ᵥ D.u) :
    ∃ z : ℝ → r' → ℝ,
      Tendsto (fun ε => X₁ ε *ᵥ z ε) 𝓕 (𝓝 (-(D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))) := by
  obtain ⟨δ, hδ, hcδ⟩ := hc
  set c : ℝ → r → ℝ := fun ε => (V₀ ε)ᵀ *ᵥ D.u with hcdef
  set t : ℝ → r → ℝ := fun ε => (c ε ⬝ᵥ c ε)⁻¹ • c ε with htdef
  refine ⟨fun ε => (X₁ ε)ᵀ *ᵥ (K₁ ε *ᵥ t ε), ?_⟩
  set EK : ℝ → Matrix x r ℝ := fun ε => (ε ^ 2 / D.dt) • (X₀ ε * S₀ ε) -
    ε • (D.B (X₀ ε * S₀ ε * (V₀ ε)ᵀ) * V₀ ε) with hEKdef
  have hEK : Tendsto EK 𝓕 (𝓝 0) := tendsto_small D.dt (hX₀.mul hS₀)
    ((EntryBdd.B ((hX₀.mul hS₀).mul hV₀.transpose)).mul hV₀)
  have hEt : Tendsto (fun ε => EK ε *ᵥ t ε) 𝓕 (𝓝 0) := by
    have h1 := tendsto_mulVec (tendsto_mul_bdd hEK (hV₀.transpose.smul (inv_bdd hδ hcδ)))
      (tendsto_const_nhds (x := D.u))
    rw [Matrix.zero_mulVec] at h1
    refine h1.congr fun ε => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  have hg : Tendsto (fun ε => D.Dp *ᵥ ρ₁ ε) 𝓕 (𝓝 (D.Dp *ᵥ ρs)) :=
    tendsto_mulVec tendsto_const_nhds hρ
  have hlim := tendsto_mulVec (tendsto_diagonal (tendsto_scale_inv hD.σs_pos)) (hEt.sub hg)
  rw [zero_sub, Matrix.mulVec_neg] at hlim
  refine hlim.congr' ?_
  filter_upwards [hk, hR, hX₁, hcδ, self_mem_nhdsWithin] with ε hk ⟨Rk, hRk⟩ hX hδε (hε : 0 < ε)
  have h1 : X₁ ε *ᵥ ((X₁ ε)ᵀ *ᵥ (K₁ ε *ᵥ t ε)) = K₁ ε *ᵥ t ε := by
    rw [hRk, ← Matrix.mulVec_mulVec]
    exact proj_fix hX _
  have hne : c ε ⬝ᵥ c ε ≠ 0 := (hδ.trans_le hδε).ne'
  have h3 : c ε ⬝ᵥ t ε = 1 := by
    rw [htdef]
    simp only [dotProduct_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hne
  have h5 : Matrix.diagonal (D.scale ε) * K₁ ε =
      EK ε - Matrix.vecMulVec (D.Dp *ᵥ ρ₁ ε) (c ε) := (kstep_scaled hε.ne').1 hk
  have h4 : Matrix.diagonal (D.scale ε) *ᵥ (K₁ ε *ᵥ t ε) = EK ε *ᵥ t ε - D.Dp *ᵥ ρ₁ ε := by
    rw [Matrix.mulVec_mulVec, h5, Matrix.sub_mulVec, vecMulVec_mulVec', h3, one_smul]
  rw [h1, ← h4, diag_inv_mulVec fun i => (scale_pos hD ε i).ne']

/-- The right capture: under `|(X⁰(ε))ᵀ 𝒟^{x,+} ρ¹(ε)|² ≥ δ > 0` elements of `Range V¹(ε)` converge
to `M Qˣ 1`. -/
private theorem capture_right (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs))
    (hX₀ : ∀ᶠ ε in 𝓕, (X₀ ε)ᵀ * X₀ ε = 1) (hV₀ : EntryBdd 𝓕 V₀) (hS₀ : EntryBdd 𝓕 S₀)
    (hV₁ : ∀ᶠ ε in 𝓕, (V₁ ε)ᵀ * V₁ ε = 1)
    (hl : ∀ᶠ ε in 𝓕, D.IsLStep ε (ρ₁ ε) (X₀ ε) (S₀ ε) (V₀ ε) (L₁ ε))
    (hR : ∀ᶠ ε in 𝓕, ∃ Rl : Matrix r' r ℝ, L₁ ε = V₁ ε * Rl)
    (hq : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε) ⬝ᵥ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε)) :
    ∃ s : ℝ → r' → ℝ, Tendsto (fun ε => V₁ ε *ᵥ s ε) 𝓕 (𝓝 D.u) := by
  obtain ⟨δ, hδ, hqδ⟩ := hq
  have hXb : EntryBdd 𝓕 X₀ := EntryBdd.of_orth hX₀
  set q : ℝ → r → ℝ := fun ε => (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε) with hqdef
  set t : ℝ → r → ℝ := fun ε => (q ε ⬝ᵥ q ε)⁻¹ • q ε with htdef
  set Z : ℝ → Matrix r r ℝ := fun ε => (X₀ ε)ᵀ * Matrix.diagonal (D.scale ε) * X₀ ε with hZdef
  refine ⟨fun ε => -((V₁ ε)ᵀ *ᵥ ((L₁ ε * Z ε) *ᵥ t ε)), ?_⟩
  set EL : ℝ → Matrix a r ℝ := fun ε => (ε ^ 2 / D.dt) • (V₀ ε * (S₀ ε)ᵀ) -
    ε • ((D.B (X₀ ε * (V₀ ε * (S₀ ε)ᵀ)ᵀ))ᵀ * X₀ ε) with hELdef
  have hL₀ : EntryBdd 𝓕 fun ε => V₀ ε * (S₀ ε)ᵀ := hV₀.mul hS₀.transpose
  have hEL : Tendsto EL 𝓕 (𝓝 0) := tendsto_small D.dt hL₀
    ((EntryBdd.B (hXb.mul hL₀.transpose)).transpose.mul hXb)
  have hg : Tendsto (fun ε => D.Dp *ᵥ ρ₁ ε) 𝓕 (𝓝 (D.Dp *ᵥ ρs)) :=
    tendsto_mulVec tendsto_const_nhds hρ
  have hEt : Tendsto (fun ε => EL ε *ᵥ t ε) 𝓕 (𝓝 0) := by
    have h1 := tendsto_mulVec (tendsto_mul_bdd hEL (hXb.transpose.smul (inv_bdd hδ hqδ))) hg
    rw [Matrix.zero_mulVec] at h1
    refine h1.congr fun ε => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  have hlim := (tendsto_const_nhds (x := D.u)).sub hEt
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hl, hR, hV₁, hX₀, hqδ, self_mem_nhdsWithin] with ε hl ⟨Rl, hRl⟩ hV hX hδε
    (hε : 0 < ε)
  have h1 : V₁ ε *ᵥ ((V₁ ε)ᵀ *ᵥ ((L₁ ε * Z ε) *ᵥ t ε)) = (L₁ ε * Z ε) *ᵥ t ε := by
    rw [hRl, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    exact proj_fix hV _
  have hne : q ε ⬝ᵥ q ε ≠ 0 := (hδ.trans_le hδε).ne'
  have h3 : q ε ⬝ᵥ t ε = 1 := by
    rw [htdef]
    simp only [dotProduct_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hne
  have h5 : L₁ ε * Z ε = EL ε - Matrix.vecMulVec D.u (q ε) := (lstep_scaled hε.ne' hX).1 hl
  have h4 : (L₁ ε * Z ε) *ᵥ t ε = EL ε *ᵥ t ε - D.u := by
    rw [h5, Matrix.sub_mulVec, vecMulVec_mulVec', h3, one_smul]
  rw [Matrix.mulVec_neg, h1, h4, neg_sub]

/-- **Sec. 4.2, the AP property of IMEX-S-BUG** (arXiv 2602.12337).  Let one step of the scheme
(`IsSchurIMEXSBUGStep`) start from orthonormal `X⁰(ε)`, `V⁰(ε)` and bounded `S⁰(ε)`, with
`ρ¹(ε) → ρ*`.  Assume the nondegeneracy `|(V⁰)ᵀ M Qˣ 1|² ≥ δ`, `|(X⁰)ᵀ 𝒟^{x,+} ρ¹|² ≥ δ` with
`δ > 0` independent of `ε`.  Then, as `ε → 0⁺`, the low-rank flux converges to the flux (4.3):
`ℋ(G¹(ε)) → -𝒟^{x,-}(⟨Ω ⊗ Ω⟩_Ω (σˢ)⁻¹ 𝒟^{x,+} ρ*)`.  The paper passes to the limit formally and has
no nondegeneracy; `ap_fails_of_degenerate_right`, `ap_fails_of_degenerate_left` show that it is
needed.  The bases `X¹(ε)`, `V¹(ε)` need not converge. -/
theorem tendsto_flux (hD : D.Admissible) {Φ ρ₀ : ℝ → x → ℝ} (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs))
    (hX₀ : ∀ᶠ ε in 𝓕, (X₀ ε)ᵀ * X₀ ε = 1) (hV₀ : ∀ᶠ ε in 𝓕, (V₀ ε)ᵀ * V₀ ε = 1)
    (hS₀ : EntryBdd 𝓕 S₀)
    (hs : ∀ᶠ ε in 𝓕, IsSchurIMEXSBUGStep D ε (Φ ε) (ρ₀ ε) (X₀ ε) (S₀ ε) (V₀ ε) (ρ₁ ε) (K₁ ε)
      (L₁ ε) (X₁ ε) (S₁ ε) (V₁ ε))
    (hc : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (V₀ ε)ᵀ *ᵥ D.u ⬝ᵥ (V₀ ε)ᵀ *ᵥ D.u)
    (hq : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε) ⬝ᵥ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε)) :
    Tendsto (fun ε => D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε))) 𝓕
      (𝓝 (-(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))))) := by
  have hXb : EntryBdd 𝓕 X₀ := EntryBdd.of_orth hX₀
  have hVb : EntryBdd 𝓕 V₀ := EntryBdd.of_orth hV₀
  have hX₁ := hs.mono fun _ h => h.orthX
  have hV₁ := hs.mono fun _ h => h.orthV
  obtain ⟨z, hz⟩ := capture_left hD hρ hXb hVb hS₀ hX₁ (hs.mono fun _ h => h.kstep)
    (hs.mono fun _ h => h.rangeK) hc
  obtain ⟨s, hs'⟩ := capture_right hρ hX₀ hVb hS₀ hV₁ (hs.mono fun _ h => h.lstep)
    (hs.mono fun _ h => h.rangeL) hq
  exact tendsto_flux_of_capture hD hρ hXb hVb hS₀ hX₁ hV₁ (hs.mono fun _ h => h.sstep) hz hs'

/-- **Sec. 4.2, the AP property of one step** (arXiv 2602.12337).  Let one step of IMEX-S-BUG
(`IsSchurIMEXSBUGStep`) start from orthonormal `X⁰(ε)`, `V⁰(ε)`, bounded `S⁰(ε)`, `ρ⁰(ε) → ρ⁰*`,
`Φ(ε) → Φ*`, and
let `ρ*` be the implicit diffusion step from `ρ⁰*`.  Under the nondegeneracy of `tendsto_flux`, as
`ε → 0⁺`: `ρ¹(ε) → ρ*`, `ℋ(G¹(ε))` converges to the flux (4.3), and the macro equation holds for
the low-rank `G¹(ε)` in the limit, `(ρ¹ - ρ⁰)/Δt + ℋ(G¹) + σᵃ ρ¹ → Φ*`.  For `ε > 0` it holds only
with the full-rank `G¹`, since `ρ¹` comes from the Schur complement; the paper inserts (4.3) in
"the macroscopic equation" at `ε = 0`. -/
theorem ap_step (hD : D.Admissible) {Φ ρ₀ : ℝ → x → ℝ} {Φs ρ₀s : x → ℝ}
    (hΦ : Tendsto Φ 𝓕 (𝓝 Φs)) (hρ₀ : Tendsto ρ₀ 𝓕 (𝓝 ρ₀s)) (hd : D.IsDiffusionStep Φs ρ₀s ρs)
    (hX₀ : ∀ᶠ ε in 𝓕, (X₀ ε)ᵀ * X₀ ε = 1) (hV₀ : ∀ᶠ ε in 𝓕, (V₀ ε)ᵀ * V₀ ε = 1)
    (hS₀ : EntryBdd 𝓕 S₀)
    (hs : ∀ᶠ ε in 𝓕, IsSchurIMEXSBUGStep D ε (Φ ε) (ρ₀ ε) (X₀ ε) (S₀ ε) (V₀ ε) (ρ₁ ε) (K₁ ε)
      (L₁ ε) (X₁ ε) (S₁ ε) (V₁ ε))
    (hc : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (V₀ ε)ᵀ *ᵥ D.u ⬝ᵥ (V₀ ε)ᵀ *ᵥ D.u)
    (hq : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε) ⬝ᵥ (X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε)) :
    Tendsto ρ₁ 𝓕 (𝓝 ρs) ∧
      Tendsto (fun ε => D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε))) 𝓕
        (𝓝 (-(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))))) ∧
      Tendsto (fun ε => (1 / D.dt) • (ρ₁ ε - ρ₀ ε) + D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε)) +
        D.sigA *ᵥ ρ₁ ε) 𝓕 (𝓝 Φs) := by
  have hXb : EntryBdd 𝓕 X₀ := EntryBdd.of_orth hX₀
  have hVb : EntryBdd 𝓕 V₀ := EntryBdd.of_orth hV₀
  have hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs) := tendsto_rho hD hΦ hρ₀
    (((hXb.mul hS₀).mul hVb.transpose).mul (EntryBdd.const _)) (hs.mono fun _ h => h.schur) hd
  have hH := tendsto_flux hD hρ hX₀ hV₀ hS₀ hs hc hq
  refine ⟨hρ, hH, ?_⟩
  have h1 := (((hρ.sub hρ₀).const_smul (1 / D.dt)).add hH).add
    (tendsto_mulVec (tendsto_const_nhds (x := D.sigA)) hρ)
  have h2 : (1 / D.dt) • (ρs - ρ₀s) + -(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))) +
      D.sigA *ᵥ ρs = Φs := by
    have h3 := hd
    rw [Disc.IsDiffusionStep, sub_eq_add_neg _ (D.moment • _)] at h3
    exact h3
  rwa [h2] at h1

/-- **Sec. 4.2, the AP property for data independent of `ε`** (arXiv 2602.12337).  `ap_step` for
fixed `ρ⁰`, `Φ`, `X⁰`, `S⁰`, `V⁰`; the nondegeneracy reads `(V⁰)ᵀ M Qˣ 1 ≠ 0` and
`(X⁰)ᵀ 𝒟^{x,+} ρ* ≠ 0`. -/
theorem ap_step_fixed (hD : D.Admissible) {Φ ρ₀ : x → ℝ} {X₀ : Matrix x r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix a r ℝ} (hd : D.IsDiffusionStep Φ ρ₀ ρs) (hX₀ : X₀ᵀ * X₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hs : ∀ᶠ ε in 𝓕,
      IsSchurIMEXSBUGStep D ε Φ ρ₀ X₀ S₀ V₀ (ρ₁ ε) (K₁ ε) (L₁ ε) (X₁ ε) (S₁ ε) (V₁ ε))
    (hc : V₀ᵀ *ᵥ D.u ≠ 0) (hq : X₀ᵀ *ᵥ (D.Dp *ᵥ ρs) ≠ 0) :
    Tendsto ρ₁ 𝓕 (𝓝 ρs) ∧
      Tendsto (fun ε => D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε))) 𝓕
        (𝓝 (-(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρs)))))) ∧
      Tendsto (fun ε => (1 / D.dt) • (ρ₁ ε - ρ₀) + D.H (D.lift (X₁ ε) (S₁ ε) (V₁ ε)) +
        D.sigA *ᵥ ρ₁ ε) 𝓕 (𝓝 Φ) := by
  have hpos : ∀ {m : Type _} [Fintype m] {y : m → ℝ}, y ≠ 0 → 0 < y ⬝ᵥ y := fun {m} _ {y} hy =>
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Ne.symm fun h => hy (dotProduct_self_eq_zero.1 h))
  have hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs) := tendsto_rho hD tendsto_const_nhds tendsto_const_nhds
    (EntryBdd.const _) (hs.mono fun _ h => h.schur) hd
  have hq' : Tendsto (fun ε => X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε)) 𝓕 (𝓝 (X₀ᵀ *ᵥ (D.Dp *ᵥ ρs))) :=
    tendsto_mulVec tendsto_const_nhds (tendsto_mulVec tendsto_const_nhds hρ)
  have hq0 := hpos hq
  have hev := (tendsto_dot hq' hq').eventually (lt_mem_nhds (half_lt_self hq0))
  exact ap_step hD tendsto_const_nhds tendsto_const_nhds hd
    (Eventually.of_forall fun _ => hX₀) (Eventually.of_forall fun _ => hV₀) (EntryBdd.const _) hs
    ⟨_, hpos hc, Eventually.of_forall fun _ => le_rfl⟩ ⟨_, half_pos hq0, hev.mono fun _ h => h.le⟩

private theorem tendsto_Es (hX₀ : EntryBdd 𝓕 X₀) (hV₀ : EntryBdd 𝓕 V₀) (hS₀ : EntryBdd 𝓕 S₀)
    (hX₁ : EntryBdd 𝓕 X₁) (hV₁ : EntryBdd 𝓕 V₁) :
    Tendsto (fun ε => (ε ^ 2 / D.dt) • (X₀ ε * S₀ ε * (V₀ ε)ᵀ * V₁ ε) -
      ε • (D.B (X₁ ε * ((X₁ ε)ᵀ * X₀ ε * S₀ ε * (V₀ ε)ᵀ * V₁ ε) * (V₁ ε)ᵀ) * V₁ ε)) 𝓕 (𝓝 0) :=
  tendsto_small D.dt (((hX₀.mul hS₀).mul hV₀.transpose).mul hV₁)
    ((EntryBdd.B ((hX₁.mul (((hX₁.transpose.mul hX₀).mul hS₀).mul hV₀.transpose |>.mul hV₁)).mul
      hV₁.transpose)).mul hV₁)

private theorem bdd_J_M_V {n : Type*} [Fintype n] (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs))
    {V : ℝ → Matrix a n ℝ} (hV : EntryBdd 𝓕 V) :
    EntryBdd 𝓕 fun ε => Matrix.vecMulVec (D.Dp *ᵥ ρ₁ ε) ((V ε)ᵀ *ᵥ D.u) := by
  have h : EntryBdd 𝓕 fun ε => D.J (ρ₁ ε) * D.M * V ε :=
    ((EntryBdd.of_tendsto (tendsto_J hρ)).mul (EntryBdd.const _)).mul hV
  simpa only [J_M_V] using h

/-- The Galerkin bound for the S-step: `S¹(ε)` is bounded, uniformly in `ε`. -/
private theorem bdd_S₁ (hD : D.Admissible) (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs)) (hX₀ : EntryBdd 𝓕 X₀)
    (hV₀ : EntryBdd 𝓕 V₀) (hS₀ : EntryBdd 𝓕 S₀) (hX₁ : ∀ᶠ ε in 𝓕, (X₁ ε)ᵀ * X₁ ε = 1)
    (hV₁ : EntryBdd 𝓕 V₁)
    (hs : ∀ᶠ ε in 𝓕, D.IsSStep ε (ρ₁ ε) (X₀ ε) (S₀ ε) (V₀ ε) (X₁ ε) (V₁ ε) (S₁ ε)) :
    EntryBdd 𝓕 S₁ := by
  refine EntryBdd.of_galerkin hD.σs_pos tendsto_scale hX₁
    ((EntryBdd.of_tendsto (tendsto_Es (D := D) hX₀ hV₀ hS₀ (EntryBdd.of_orth hX₁) hV₁)).sub
      (bdd_J_M_V (D := D) hρ hV₁)) ?_
  filter_upwards [hs, hX₁, self_mem_nhdsWithin] with ε h hX (hε : 0 < ε)
  exact (sstep_scaled hε.ne' hX).1 h

/-- A step equation of the shape of the K-, L- and S-steps has `s + c → 0` for bounded `K`, `K₀`,
`b`, `p`. -/
private theorem tendsto_residual {m n : Type*} {K K₀ b c s p : ℝ → Matrix m n ℝ} (dt : ℝ)
    (hK : EntryBdd 𝓕 K) (hK₀ : EntryBdd 𝓕 K₀) (hb : EntryBdd 𝓕 b) (hp : EntryBdd 𝓕 p)
    (h : ∀ᶠ ε in 𝓕, (1 / dt) • (K ε - K₀ ε) =
      -(1 / ε) • b ε - (1 / ε ^ 2) • c ε - (1 / ε ^ 2) • s ε - p ε) :
    Tendsto (fun ε => s ε + c ε) 𝓕 (𝓝 0) := by
  have hε : ∀ᶠ ε : ℝ in 𝓕, |ε| ≤ 1 := by
    have h0 : Tendsto (fun ε : ℝ => |ε|) 𝓕 (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ε) 𝓕 (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using h1.abs
    exact h0.eventually (ge_mem_nhds one_pos)
  have h1 := tendsto_small dt (hK₀.sub hK) (hb.add (hp.smul (s := fun ε => ε) ⟨1, hε⟩))
  refine h1.congr' ?_
  filter_upwards [h, self_mem_nhdsWithin] with ε he (hε : 0 < ε)
  have h2 := (scaled_iff hε.ne').1 he
  simp only [smul_add, smul_smul]
  linear_combination (norm := module) -h2

/-- **Sec. 4.2, Eq. (4.1a-c)** (arXiv 2602.12337).  "In the limit `ε → 0`, the K-, L- and S-step
reduce to (4.1a-c)", as a theorem: for one step (`IsSchurIMEXSBUGStep`) from orthonormal `X⁰(ε)`,
`V⁰(ε)`, bounded `S⁰(ε)` and with `ρ¹(ε) → ρ*`, the residuals of (4.1a-c) tend to zero.  No
nondegeneracy is needed here.  Since `X¹(ε)`, `V¹(ε)` need not converge, (4.1c) can only hold in
this form. -/
theorem tendsto_steps (hD : D.Admissible) {Φ ρ₀ : ℝ → x → ℝ} (hρ : Tendsto ρ₁ 𝓕 (𝓝 ρs))
    (hX₀ : ∀ᶠ ε in 𝓕, (X₀ ε)ᵀ * X₀ ε = 1) (hV₀ : ∀ᶠ ε in 𝓕, (V₀ ε)ᵀ * V₀ ε = 1)
    (hS₀ : EntryBdd 𝓕 S₀)
    (hs : ∀ᶠ ε in 𝓕, IsSchurIMEXSBUGStep D ε (Φ ε) (ρ₀ ε) (X₀ ε) (S₀ ε) (V₀ ε) (ρ₁ ε) (K₁ ε)
      (L₁ ε) (X₁ ε) (S₁ ε) (V₁ ε)) :
    Tendsto (fun ε => K₁ ε + D.sigSInv * (D.J (ρ₁ ε) * D.M * V₀ ε)) 𝓕 (𝓝 0) ∧
      Tendsto (fun ε => L₁ ε * ((X₀ ε)ᵀ * D.sigS * X₀ ε) + D.M * (D.J (ρ₁ ε))ᵀ * X₀ ε) 𝓕 (𝓝 0) ∧
      Tendsto (fun ε => (X₁ ε)ᵀ * D.sigS * X₁ ε * S₁ ε + (X₁ ε)ᵀ * D.J (ρ₁ ε) * D.M * V₁ ε) 𝓕
        (𝓝 0) := by
  have hXb : EntryBdd 𝓕 X₀ := EntryBdd.of_orth hX₀
  have hVb : EntryBdd 𝓕 V₀ := EntryBdd.of_orth hV₀
  have hX₁ := hs.mono fun _ h => h.orthX
  have hV₁ := hs.mono fun _ h => h.orthV
  have hX₁b : EntryBdd 𝓕 X₁ := EntryBdd.of_orth hX₁
  have hV₁b : EntryBdd 𝓕 V₁ := EntryBdd.of_orth hV₁
  have hSb : EntryBdd 𝓕 S₁ := bdd_S₁ hD hρ hXb hVb hS₀ hX₁ hV₁b (hs.mono fun _ h => h.sstep)
  have hL₀ : EntryBdd 𝓕 fun ε => V₀ ε * (S₀ ε)ᵀ := hVb.mul hS₀.transpose
  have hEK := tendsto_small D.dt (hXb.mul hS₀)
    ((EntryBdd.B (D := D) ((hXb.mul hS₀).mul hVb.transpose)).mul hVb)
  have hEL := tendsto_small D.dt hL₀
    ((EntryBdd.B (D := D) (hXb.mul hL₀.transpose)).transpose.mul hXb)
  -- boundedness of `K¹`
  have hKb : EntryBdd 𝓕 K₁ := by
    refine EntryBdd.of_galerkin (X := fun _ => (1 : Matrix x x ℝ)) hD.σs_pos tendsto_scale
      (Eventually.of_forall fun _ => by simp)
      ((EntryBdd.of_tendsto hEK).sub (bdd_J_M_V (D := D) hρ hVb)) ?_
    filter_upwards [hs, self_mem_nhdsWithin] with ε h (hε : 0 < ε)
    simpa using (kstep_scaled hε.ne').1 h.kstep
  -- boundedness of `L¹`
  have hLb : EntryBdd 𝓕 L₁ := by
    have hN : EntryBdd 𝓕 fun ε => Matrix.vecMulVec D.u ((X₀ ε)ᵀ *ᵥ (D.Dp *ᵥ ρ₁ ε)) := by
      have h := ((EntryBdd.const D.M).mul
        (EntryBdd.of_tendsto (tendsto_J (D := D) hρ)).transpose).mul hXb
      simpa only [M_Jt_X] using h
    have hW := (EntryBdd.of_tendsto hEL).sub hN
    have hT : EntryBdd 𝓕 fun ε => (L₁ ε)ᵀ := by
      refine EntryBdd.of_galerkin hD.σs_pos tendsto_scale hX₀ (hXb.mul hW.transpose) ?_
      filter_upwards [hs, hX₀, self_mem_nhdsWithin] with ε h hX (hε : 0 < ε)
      have h2 := congrArg Matrix.transpose ((lstep_scaled hε.ne' hX).1 h.lstep)
      have hZ : ((X₀ ε)ᵀ * Matrix.diagonal (D.scale ε) * X₀ ε)ᵀ =
          (X₀ ε)ᵀ * Matrix.diagonal (D.scale ε) * X₀ ε := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [Matrix.transpose_mul, hZ] at h2
      rw [h2, ← Matrix.mul_assoc, hX, Matrix.one_mul]
    simpa using hT.transpose
  have hA : EntryBdd 𝓕 fun _ : ℝ => D.sigA := EntryBdd.const _
  have h1 : Tendsto (fun ε => D.sigS * K₁ ε + D.J (ρ₁ ε) * D.M * V₀ ε) 𝓕 (𝓝 0) :=
    tendsto_residual D.dt hKb (hXb.mul hS₀)
      ((EntryBdd.B (D := D) ((hXb.mul hS₀).mul hVb.transpose)).mul hVb) (hA.mul hKb)
      (hs.mono fun _ h => h.kstep)
  have h2 : Tendsto (fun ε => L₁ ε * ((X₀ ε)ᵀ * D.sigS * X₀ ε) + D.M * (D.J (ρ₁ ε))ᵀ * X₀ ε) 𝓕
      (𝓝 0) :=
    tendsto_residual D.dt hLb hL₀
      ((EntryBdd.B (D := D) (hXb.mul hL₀.transpose)).transpose.mul hXb)
      (hLb.mul ((hXb.transpose.mul hA).mul hXb)) (hs.mono fun _ h => h.lstep)
  have hSt : EntryBdd 𝓕 fun ε => (X₁ ε)ᵀ * X₀ ε * S₀ ε * (V₀ ε)ᵀ * V₁ ε :=
    (((hX₁b.transpose.mul hXb).mul hS₀).mul hVb.transpose).mul hV₁b
  have h3 : Tendsto
      (fun ε => (X₁ ε)ᵀ * D.sigS * X₁ ε * S₁ ε + (X₁ ε)ᵀ * D.J (ρ₁ ε) * D.M * V₁ ε) 𝓕 (𝓝 0) :=
    tendsto_residual D.dt hSb hSt
      ((hX₁b.transpose.mul (EntryBdd.B (D := D) ((hX₁b.mul hSt).mul hV₁b.transpose))).mul hV₁b)
      (((hX₁b.transpose.mul hA).mul hX₁b).mul hSb) (hs.mono fun _ h => h.sstep)
  refine ⟨?_, h2, h3⟩
  have h4 := tendsto_mat_mul (tendsto_const_nhds (x := D.sigSInv)) h1
  rw [Matrix.mul_zero] at h4
  refine h4.congr fun ε => ?_
  have h5 : D.sigSInv * D.sigS = 1 := by
    rw [Disc.sigSInv, Disc.sigS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hD.σs_pos i).ne'
  rw [Matrix.mul_add, ← Matrix.mul_assoc, h5, Matrix.one_mul]

variable {Φ : ℕ → x → ℝ} {ρ : ℕ → ℝ → x → ℝ} {X : ℕ → ℝ → Matrix x r ℝ}
  {S : ℕ → ℝ → Matrix r r ℝ} {V : ℕ → ℝ → Matrix a r ℝ} {K : ℕ → ℝ → Matrix x r ℝ}
  {L : ℕ → ℝ → Matrix a r ℝ} {ρd : ℕ → x → ℝ}

/-- **Sec. 4.2, the iterates of the density** (arXiv 2602.12337).  For every `n`, the density
`ρⁿ(ε)` of the IMEX-S-BUG scheme converges as `ε → 0⁺` to the `n`-th iterate `ρd n` of the implicit
diffusion scheme, and `Sⁿ(ε)` stays bounded.  The data at `n = 0` may depend on `ε`, with
orthonormal bases, bounded `S⁰(ε)` and `ρ⁰(ε) → ρd 0`.  There is no nondegeneracy hypothesis: the
paper has no such statement, and the density does not need the range conditions, because the Schur
complement uses the full-rank operator. -/
theorem tendsto_iterates (hD : D.Admissible) (hX : ∀ᶠ ε in 𝓕, (X 0 ε)ᵀ * X 0 ε = 1)
    (hV : ∀ᶠ ε in 𝓕, (V 0 ε)ᵀ * V 0 ε = 1) (hS : EntryBdd 𝓕 (S 0))
    (hρ : Tendsto (ρ 0) 𝓕 (𝓝 (ρd 0)))
    (hstep : ∀ n, ∀ᶠ ε in 𝓕, IsSchurIMEXSBUGStep D ε (Φ n) (ρ n ε) (X n ε) (S n ε) (V n ε)
      (ρ (n + 1) ε) (K n ε) (L n ε) (X (n + 1) ε) (S (n + 1) ε) (V (n + 1) ε))
    (hlim : ∀ n, D.IsDiffusionStep (Φ n) (ρd n) (ρd (n + 1))) (n : ℕ) :
    Tendsto (ρ n) 𝓕 (𝓝 (ρd n)) ∧ EntryBdd 𝓕 (S n) ∧
      (∀ᶠ ε in 𝓕, (X n ε)ᵀ * X n ε = 1) ∧ ∀ᶠ ε in 𝓕, (V n ε)ᵀ * V n ε = 1 := by
  induction n with
  | zero => exact ⟨hρ, hS, hX, hV⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hs := hstep n
    have hXb : EntryBdd 𝓕 (X n) := EntryBdd.of_orth h3
    have hVb : EntryBdd 𝓕 (V n) := EntryBdd.of_orth h4
    have hG : EntryBdd 𝓕 fun ε => D.lift (X n ε) (S n ε) (V n ε) :=
      ((hXb.mul h2).mul hVb.transpose).mul (EntryBdd.const _)
    have hρ' := tendsto_rho hD tendsto_const_nhds h1 hG (hs.mono fun _ h => h.schur) (hlim n)
    have hX' := hs.mono fun _ h => h.orthX
    have hV' := hs.mono fun _ h => h.orthV
    exact ⟨hρ', bdd_S₁ hD hρ' hXb hVb h2 hX' (EntryBdd.of_orth hV') (hs.mono fun _ h => h.sstep),
      hX', hV'⟩

/-- **Sec. 4.2, the AP property of the iterates** (arXiv 2602.12337).  In the setting of
`tendsto_iterates`, assume `|(V⁰)ᵀ M Qˣ 1|² ≥ δ` at the first step and
`|(Xⁿ)ᵀ 𝒟^{x,+} ρ^{n+1}|² ≥ δₙ` at every step.  Then for every `n` the low-rank flux converges to
the diffusion flux: `ℋ(G^{n+1}(ε)) → -𝒟^{x,-}(⟨Ω ⊗ Ω⟩_Ω (σˢ)⁻¹ 𝒟^{x,+} ρd_{n+1})`.  The condition
on `Vⁿ` for `n ≥ 1` is derived: `M Qˣ 1` is captured by `Vⁿ(ε)` in the limit. -/
theorem tendsto_flux_iterates (hD : D.Admissible) (hX : ∀ᶠ ε in 𝓕, (X 0 ε)ᵀ * X 0 ε = 1)
    (hV : ∀ᶠ ε in 𝓕, (V 0 ε)ᵀ * V 0 ε = 1) (hS : EntryBdd 𝓕 (S 0))
    (hρ : Tendsto (ρ 0) 𝓕 (𝓝 (ρd 0)))
    (hstep : ∀ n, ∀ᶠ ε in 𝓕, IsSchurIMEXSBUGStep D ε (Φ n) (ρ n ε) (X n ε) (S n ε) (V n ε)
      (ρ (n + 1) ε) (K n ε) (L n ε) (X (n + 1) ε) (S (n + 1) ε) (V (n + 1) ε))
    (hlim : ∀ n, D.IsDiffusionStep (Φ n) (ρd n) (ρd (n + 1)))
    (hc : ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (V 0 ε)ᵀ *ᵥ D.u ⬝ᵥ (V 0 ε)ᵀ *ᵥ D.u)
    (hq : ∀ n, ∃ δ > 0, ∀ᶠ ε in 𝓕,
      δ ≤ (X n ε)ᵀ *ᵥ (D.Dp *ᵥ ρ (n + 1) ε) ⬝ᵥ (X n ε)ᵀ *ᵥ (D.Dp *ᵥ ρ (n + 1) ε)) (n : ℕ) :
    Tendsto (fun ε => D.H (D.lift (X (n + 1) ε) (S (n + 1) ε) (V (n + 1) ε))) 𝓕
      (𝓝 (-(D.moment • (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρd (n + 1))))))) := by
  have hinv := tendsto_iterates hD hX hV hS hρ hstep hlim
  have hu : 0 < D.u ⬝ᵥ D.u := by
    obtain ⟨δ, hδ, h⟩ := hc
    obtain ⟨ε, hε⟩ := h.exists
    have h0 : D.u ≠ 0 := by
      intro h0
      rw [h0, Matrix.mulVec_zero, dotProduct_zero] at hε
      exact absurd hε (not_le.2 hδ)
    have h1 : 0 ≤ D.u ⬝ᵥ D.u := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact lt_of_le_of_ne h1 (Ne.symm fun h2 => h0 (dotProduct_self_eq_zero.1 h2))
  have hcn : ∀ n, ∃ δ > 0, ∀ᶠ ε in 𝓕, δ ≤ (V n ε)ᵀ *ᵥ D.u ⬝ᵥ (V n ε)ᵀ *ᵥ D.u := by
    intro n
    cases n with
    | zero => exact hc
    | succ n =>
      obtain ⟨h1, h2, h3, h4⟩ := hinv (n + 1)
      obtain ⟨h1', h2', h3', h4'⟩ := hinv n
      have hs := hstep n
      obtain ⟨s, hs'⟩ := capture_right h1 h3' (EntryBdd.of_orth h4') h2' h4
        (hs.mono fun _ h => h.lstep) (hs.mono fun _ h => h.rangeL) (hq n)
      refine ⟨D.u ⬝ᵥ D.u / 2, by positivity, ?_⟩
      exact (tendsto_proj_dot h4 (tendsto_proj h4 hs')).eventually
        (lt_mem_nhds (by linarith)) |>.mono fun _ h => h.le
  obtain ⟨h1, -, h3, h4⟩ := hinv (n + 1)
  obtain ⟨-, h2', h3', h4'⟩ := hinv n
  exact tendsto_flux hD h1 h3' h4' h2' (hstep n) (hcn n) (hq n)

/-- **Sec. 4.2, the limit equations are solvable** (arXiv 2602.12337).  For orthonormal `X⁰` and
rank `n` at most the grid sizes, (4.1a-c) have a solution with orthonormal `X¹`, `V¹` capturing
`K¹`, `L¹`, so that `formal_ap` is not vacuous. -/
theorem exists_formal_limit (hσ : ∀ i, 0 < D.σs i) {n : ℕ} (hnx : n ≤ Fintype.card x)
    (hna : n ≤ Fintype.card a) (ρ : x → ℝ) {X₀ : Matrix x (Fin n) ℝ} (V₀ : Matrix a (Fin n) ℝ)
    (hX₀ : X₀ᵀ * X₀ = 1) :
    ∃ (K₁ : Matrix x (Fin n) ℝ) (L₁ : Matrix a (Fin n) ℝ) (X₁ : Matrix x (Fin n) ℝ)
      (V₁ : Matrix a (Fin n) ℝ) (S₁ : Matrix (Fin n) (Fin n) ℝ) (Rk Rl : Matrix (Fin n) (Fin n) ℝ),
      D.IsFormalLimit ρ X₀ V₀ K₁ L₁ X₁ V₁ S₁ ∧ X₁ᵀ * X₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧ K₁ = X₁ * Rk ∧
        L₁ = V₁ * Rl := by
  have hZ : IsUnit (X₀ᵀ * D.sigS * X₀).det := gram_isUnit hσ hX₀
  set K₁ : Matrix x (Fin n) ℝ := -(D.sigSInv * (D.J ρ * D.M * V₀)) with hK
  set L₁ : Matrix a (Fin n) ℝ := -(D.M * (D.J ρ)ᵀ * X₀) * (X₀ᵀ * D.sigS * X₀)⁻¹ with hL
  obtain ⟨X₁, hX₁, hcX⟩ := exists_orthonormal_capture_of_le_card K₁ hnx
  obtain ⟨V₁, hV₁, hcV⟩ := exists_orthonormal_capture_of_le_card L₁ hna
  have hZ₁ : IsUnit (X₁ᵀ * D.sigS * X₁).det := gram_isUnit hσ hX₁
  refine ⟨K₁, L₁, X₁, V₁, (X₁ᵀ * D.sigS * X₁)⁻¹ * -(X₁ᵀ * D.J ρ * D.M * V₁), X₁ᵀ * K₁, V₁ᵀ * L₁,
    ⟨rfl, ?_, ?_⟩, hX₁, hV₁, ?_, ?_⟩
  · rw [hL, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZ₁, Matrix.one_mul]
  · rw [← Matrix.mul_assoc]
    exact hcX.symm
  · rw [← Matrix.mul_assoc]
    exact hcV.symm

/-- **Sec. 4.1, one step exists** (arXiv 2602.12337).  For `ε > 0`, orthonormal `X⁰`, and rank `n`
at most the grid sizes, all the linear systems of a step are solvable and the QR steps exist, also
for rank-deficient `K¹`, `L¹`. -/
theorem exists_step (hD : D.Admissible) {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hnx : n ≤ Fintype.card x) (hna : n ≤ Fintype.card a) (Φ ρ₀ : x → ℝ)
    {X₀ : Matrix x (Fin n) ℝ} (S₀ : Matrix (Fin n) (Fin n) ℝ) (V₀ : Matrix a (Fin n) ℝ)
    (hX₀ : X₀ᵀ * X₀ = 1) :
    ∃ (ρ₁ : x → ℝ) (K₁ : Matrix x (Fin n) ℝ) (L₁ : Matrix a (Fin n) ℝ) (X₁ : Matrix x (Fin n) ℝ)
      (S₁ : Matrix (Fin n) (Fin n) ℝ) (V₁ : Matrix a (Fin n) ℝ),
      IsSchurIMEXSBUGStep D ε Φ ρ₀ X₀ S₀ V₀ ρ₁ K₁ L₁ X₁ S₁ V₁ := by
  have hd : ∀ i, 0 < D.scale ε i := scale_pos hD ε
  obtain ⟨ρ₁, hρ, -⟩ := existsUnique_of_det
    (Top_det_ne (D := D) hD (q := fun i => (D.scale ε i)⁻¹) fun i => (inv_pos.2 (hd i)).le)
    ((1 / D.dt) • ρ₀ + Φ - D.H (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) *
      ((ε ^ 2 / D.dt) • D.lift X₀ S₀ V₀ - ε • (D.A (D.lift X₀ S₀ V₀) * D.avg))))
  -- the K-step
  set bK : Matrix x (Fin n) ℝ := (ε ^ 2 / D.dt) • (X₀ * S₀) - ε • (D.B (X₀ * S₀ * V₀ᵀ) * V₀) -
    Matrix.vecMulVec (D.Dp *ᵥ ρ₁) (V₀ᵀ *ᵥ D.u) with hbK
  have hK : Matrix.diagonal (D.scale ε) * (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) * bK) =
      bK := by
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => D.scale ε i * (D.scale ε i)⁻¹) = fun _ => (1 : ℝ) := by
      funext i
      exact mul_inv_cancel₀ (hd i).ne'
    rw [h1, Matrix.diagonal_one, Matrix.one_mul]
  -- the L-step
  set bL : Matrix a (Fin n) ℝ := (ε ^ 2 / D.dt) • (V₀ * S₀ᵀ) -
    ε • ((D.B (X₀ * (V₀ * S₀ᵀ)ᵀ))ᵀ * X₀) - Matrix.vecMulVec D.u (X₀ᵀ *ᵥ (D.Dp *ᵥ ρ₁)) with hbL
  have hZ := gram_isUnit hd hX₀
  have hL : bL * (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀)⁻¹ *
      (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀) = bL := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZ, Matrix.mul_one]
  -- the new bases
  obtain ⟨X₁, hX₁, hcX⟩ := exists_orthonormal_capture_of_le_card
    (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) * bK) hnx
  obtain ⟨V₁, hV₁, hcV⟩ := exists_orthonormal_capture_of_le_card
    (bL * (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀)⁻¹) hna
  -- the S-step
  have hZ₁ := gram_isUnit hd hX₁
  refine ⟨ρ₁, Matrix.diagonal (fun i => (D.scale ε i)⁻¹) * bK,
    bL * (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀)⁻¹, X₁,
    (X₁ᵀ * Matrix.diagonal (D.scale ε) * X₁)⁻¹ * (X₁ᵀ *
      ((ε ^ 2 / D.dt) • (X₀ * S₀ * V₀ᵀ * V₁) -
        ε • (D.B (X₁ * (X₁ᵀ * X₀ * S₀ * V₀ᵀ * V₁) * V₁ᵀ) * V₁) -
        Matrix.vecMulVec (D.Dp *ᵥ ρ₁) (V₁ᵀ *ᵥ D.u))), V₁,
    (macro_scaled hε.ne').2 hρ, (kstep_scaled hε.ne').2 hK, (lstep_scaled hε.ne' hX₀).2 hL, hX₁,
    hV₁, ⟨X₁ᵀ * (Matrix.diagonal (fun i => (D.scale ε i)⁻¹) * bK), ?_⟩,
    ⟨V₁ᵀ * (bL * (X₀ᵀ * Matrix.diagonal (D.scale ε) * X₀)⁻¹), ?_⟩, ?_⟩
  · rw [← Matrix.mul_assoc]
    exact hcX.symm
  · rw [← Matrix.mul_assoc]
    exact hcV.symm
  · rw [sstep_scaled hε.ne' hX₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZ₁, Matrix.one_mul]

/-- **Sec. 4.1, trajectories exist** (arXiv 2602.12337).  For `ε > 0` the scheme can be run for all
time steps from any orthonormal `X⁰`. -/
theorem exists_trajectory (hD : D.Admissible) {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hnx : n ≤ Fintype.card x) (hna : n ≤ Fintype.card a) (Φ : ℕ → x → ℝ) (ρ₀ : x → ℝ)
    {X₀ : Matrix x (Fin n) ℝ} (S₀ : Matrix (Fin n) (Fin n) ℝ) (V₀ : Matrix a (Fin n) ℝ)
    (hX₀ : X₀ᵀ * X₀ = 1) :
    ∃ (ρ : ℕ → x → ℝ) (X : ℕ → Matrix x (Fin n) ℝ) (S : ℕ → Matrix (Fin n) (Fin n) ℝ)
      (V : ℕ → Matrix a (Fin n) ℝ) (K : ℕ → Matrix x (Fin n) ℝ) (L : ℕ → Matrix a (Fin n) ℝ),
      ρ 0 = ρ₀ ∧ X 0 = X₀ ∧ S 0 = S₀ ∧ V 0 = V₀ ∧
        ∀ k, IsSchurIMEXSBUGStep D ε (Φ k) (ρ k) (X k) (S k) (V k) (ρ (k + 1)) (K k) (L k)
          (X (k + 1)) (S (k + 1)) (V (k + 1)) := by
  let T := (x → ℝ) × {X : Matrix x (Fin n) ℝ // Xᵀ * X = 1} × Matrix (Fin n) (Fin n) ℝ ×
    Matrix a (Fin n) ℝ
  have hnext : ∀ (k : ℕ) (st : T), ∃ (st' : T) (K : Matrix x (Fin n) ℝ) (L : Matrix a (Fin n) ℝ),
      IsSchurIMEXSBUGStep D ε (Φ k) st.1 st.2.1.1 st.2.2.1 st.2.2.2 st'.1 K L st'.2.1.1 st'.2.2.1
        st'.2.2.2 := by
    intro k st
    obtain ⟨ρ₁, K₁, L₁, X₁, S₁, V₁, h⟩ :=
      exists_step hD hε hnx hna (Φ k) st.1 st.2.2.1 st.2.2.2 st.2.1.2
    exact ⟨(ρ₁, ⟨X₁, h.orthX⟩, S₁, V₁), K₁, L₁, h⟩
  choose next K L hs using hnext
  let seq : ℕ → T := fun k => Nat.rec (ρ₀, ⟨X₀, hX₀⟩, S₀, V₀) (fun k st => next k st) k
  exact ⟨fun k => (seq k).1, fun k => (seq k).2.1.1, fun k => (seq k).2.2.1,
    fun k => (seq k).2.2.2, fun k => K k (seq k), fun k => L k (seq k), rfl, rfl, rfl, rfl,
    fun k => hs k (seq k)⟩

/-- **Sec. 4.2, the AP property of the density, with existence** (arXiv 2602.12337).  From data
`ρ⁰`, `X⁰`, `S⁰`, `V⁰` independent of `ε`, with orthonormal `X⁰`, `V⁰`, the scheme has trajectories
for all `ε > 0`, and on every such family, at every time step, `ρⁿ(ε)` converges as `ε → 0⁺` to the
iterates of the implicit diffusion scheme.  This shows that `tendsto_iterates` is not vacuous. -/
theorem exists_ap_trajectory (hD : D.Admissible) {n : ℕ} (hnx : n ≤ Fintype.card x)
    (hna : n ≤ Fintype.card a) (Φ : ℕ → x → ℝ) (ρ₀ : x → ℝ) {X₀ : Matrix x (Fin n) ℝ}
    (S₀ : Matrix (Fin n) (Fin n) ℝ) {V₀ : Matrix a (Fin n) ℝ} (hX₀ : X₀ᵀ * X₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (ρd : ℕ → x → ℝ) (ρ : ℕ → ℝ → x → ℝ) (X : ℕ → ℝ → Matrix x (Fin n) ℝ)
      (S : ℕ → ℝ → Matrix (Fin n) (Fin n) ℝ) (V : ℕ → ℝ → Matrix a (Fin n) ℝ)
      (K : ℕ → ℝ → Matrix x (Fin n) ℝ) (L : ℕ → ℝ → Matrix a (Fin n) ℝ),
      ρd 0 = ρ₀ ∧ (∀ k, D.IsDiffusionStep (Φ k) (ρd k) (ρd (k + 1))) ∧
      (∀ ε > 0, ρ 0 ε = ρ₀ ∧ X 0 ε = X₀ ∧ S 0 ε = S₀ ∧ V 0 ε = V₀) ∧
      (∀ ε > 0, ∀ k, IsSchurIMEXSBUGStep D ε (Φ k) (ρ k ε) (X k ε) (S k ε) (V k ε) (ρ (k + 1) ε)
        (K k ε) (L k ε) (X (k + 1) ε) (S (k + 1) ε) (V (k + 1) ε)) ∧
      ∀ k, Tendsto (ρ k) 𝓕 (𝓝 (ρd k)) := by
  obtain ⟨ρd, hρ0, hρd⟩ : ∃ ρd : ℕ → x → ℝ, ρd 0 = ρ₀ ∧
      ∀ k, D.IsDiffusionStep (Φ k) (ρd k) (ρd (k + 1)) := by
    choose f hf using fun (k : ℕ) (y : x → ℝ) => (existsUnique_diffusion hD (Φ k) y).exists
    exact ⟨fun k => Nat.rec ρ₀ (fun k y => f k y) k, rfl, fun k => hf k _⟩
  have htraj : ∀ ε : ℝ, ∃ (ρ : ℕ → x → ℝ) (X : ℕ → Matrix x (Fin n) ℝ)
      (S : ℕ → Matrix (Fin n) (Fin n) ℝ) (V : ℕ → Matrix a (Fin n) ℝ)
      (K : ℕ → Matrix x (Fin n) ℝ) (L : ℕ → Matrix a (Fin n) ℝ), 0 < ε →
        (ρ 0 = ρ₀ ∧ X 0 = X₀ ∧ S 0 = S₀ ∧ V 0 = V₀) ∧
          ∀ k, IsSchurIMEXSBUGStep D ε (Φ k) (ρ k) (X k) (S k) (V k) (ρ (k + 1)) (K k) (L k)
            (X (k + 1)) (S (k + 1)) (V (k + 1)) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨ρ, X, S, V, K, L, h1, h2, h3, h4, h5⟩ :=
        exists_trajectory hD hε hnx hna Φ ρ₀ S₀ V₀ hX₀
      exact ⟨ρ, X, S, V, K, L, fun _ => ⟨⟨h1, h2, h3, h4⟩, h5⟩⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
        fun h => absurd h hε⟩
  choose ρ X S V K L h using htraj
  have h0 : ∀ᶠ ε in 𝓕, 0 < ε := self_mem_nhdsWithin
  refine ⟨ρd, fun k ε => ρ ε k, fun k ε => X ε k, fun k ε => S ε k, fun k ε => V ε k,
    fun k ε => K ε k, fun k ε => L ε k, hρ0, hρd, fun ε hε => (h ε hε).1,
    fun ε hε => (h ε hε).2, fun k => ?_⟩
  have hρ : Tendsto (fun ε => ρ ε 0) 𝓕 (𝓝 (ρd 0)) := by
    rw [hρ0]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h0] with ε hε
    exact (h ε hε).1.1.symm
  have hS : EntryBdd 𝓕 fun ε => S ε 0 := by
    refine (EntryBdd.const S₀).congr' ?_
    filter_upwards [h0] with ε hε
    exact (h ε hε).1.2.2.1.symm
  exact (tendsto_iterates (ρ := fun k ε => ρ ε k) (X := fun k ε => X ε k) (S := fun k ε => S ε k)
    (V := fun k ε => V ε k) (K := fun k ε => K ε k) (L := fun k ε => L ε k) (Φ := Φ) hD
    (h0.mono fun ε hε => by rw [(h ε hε).1.2.1, hX₀])
    (h0.mono fun ε hε => by rw [(h ε hε).1.2.2.2, hV₀]) hS hρ
    (fun k => h0.mono fun ε hε => (h ε hε).2 k) hρd k).1

end Limit

/-! ## The periodic stencil and examples -/

section Periodic

/-- The periodic stencil `(𝒟^{x,+} ρ)ᵢ = (ρ_{i+1} - ρᵢ)/Δx` on `n + 1` cells. -/
noncomputable def periodicDp (n : ℕ) (h : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => ((if j = i + 1 then 1 else 0) - (if j = i then 1 else 0)) / h

/-- The periodic stencil `(𝒟^{x,-} g)ᵢ = (gᵢ - g_{i-1})/Δx` on `n + 1` cells. -/
noncomputable def periodicDm (n : ℕ) (h : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => ((if j = i then 1 else 0) - (if j = i - 1 then 1 else 0)) / h

/-- `periodicDp` is the core forward difference `Kinetic.fwdDiff` with the cells numbered by
`Fin (n + 1)` through `ZMod.finEquiv`. -/
theorem periodicDp_eq_submatrix (n : ℕ) (h : ℝ) :
    periodicDp n h =
      (Kinetic.fwdDiff (n + 1) h).submatrix (ZMod.finEquiv (n + 1)) (ZMod.finEquiv (n + 1)) := by
  rw [Kinetic.fwdDiff_submatrix_finEquiv]
  rfl

/-- `periodicDm` is the core backward difference `Kinetic.bwdDiff` with the cells numbered by
`Fin (n + 1)` through `ZMod.finEquiv`. -/
theorem periodicDm_eq_submatrix (n : ℕ) (h : ℝ) :
    periodicDm n h =
      (Kinetic.bwdDiff (n + 1) h).submatrix (ZMod.finEquiv (n + 1)) (ZMod.finEquiv (n + 1)) := by
  rw [Kinetic.bwdDiff_submatrix_finEquiv]
  rfl

/-- The stencil of `periodicDp` (arXiv 2602.12337, Sec. 3.2; the paper does not print it). -/
theorem periodicDp_mulVec (n : ℕ) (h : ℝ) (ρ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (periodicDp n h *ᵥ ρ) i = (ρ (i + 1) - ρ i) / h := by
  rw [periodicDp_eq_submatrix, Kinetic.fwdDiff_submatrix_finEquiv_mulVec]

/-- The stencil of `periodicDm` (arXiv 2602.12337, Sec. 3.2; the paper does not print it). -/
theorem periodicDm_mulVec (n : ℕ) (h : ℝ) (g : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (periodicDm n h *ᵥ g) i = (g i - g (i - 1)) / h := by
  rw [periodicDm_eq_submatrix, Kinetic.bwdDiff_submatrix_finEquiv_mulVec]

/-- Summation by parts for the periodic stencil (arXiv 2602.12337, Sec. 3.3, the identity behind
`|D_Ω| ⟨ρ, ℋ(G)⟩ = -⟨𝒥(ρ), G⟩_w`). -/
theorem periodicDm_eq (n : ℕ) (h : ℝ) : periodicDm n h = -(periodicDp n h)ᵀ := by
  ext i j
  have h1 : (j = i - 1) ↔ (i = j + 1) := by
    constructor <;> (intro h2; rw [h2]; simp)
  have h2 : (j = i) ↔ (i = j) := eq_comm
  simp only [periodicDm, periodicDp, Matrix.of_apply, Matrix.neg_apply, Matrix.transpose_apply, h1,
    h2]
  ring

/-- The one-dimensional periodic `S_N` discretisation of Sec. 3.2. -/
noncomputable def periodic (n : ℕ) (h : ℝ) (w Ω : a → ℝ) (vol : ℝ) (σs σa : Fin (n + 1) → ℝ)
    (dt : ℝ) : Disc (Fin (n + 1)) a :=
  ⟨periodicDp n h, periodicDm n h, w, Ω, vol, σs, σa, dt⟩

/-- The standing assumptions of arXiv 2602.12337, Sec. 2.1 and 3.2, hold for the periodic
stencil. -/
theorem periodic_admissible {n : ℕ} {h : ℝ} {w Ω : a → ℝ} {σs σa : Fin (n + 1) → ℝ} {dt : ℝ}
    (hw : ∀ i, 0 < w i) (hs : ∀ i, 0 < σs i) (ha : ∀ i, 0 ≤ σa i) (hdt : 0 < dt) :
    (periodic n h w Ω (∑ i, w i) σs σa dt).Admissible :=
  ⟨hw, rfl, hs, ha, hdt, periodicDm_eq n h⟩

/-- **Sec. 4.2, the limit scheme on the periodic grid** (arXiv 2602.12337).  The diffusion operator
of `IsDiffusionStep` is the conservative three-point stencil of `∂ₓ((σˢ)⁻¹ ∂ₓ ρ)`. -/
theorem periodic_diffusion {n : ℕ} {h : ℝ} {w Ω : a → ℝ} {vol : ℝ} {σs σa : Fin (n + 1) → ℝ}
    {dt : ℝ} (ρ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    let D := periodic n h w Ω vol σs σa dt
    (D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρ))) i =
      ((σs i)⁻¹ * (ρ (i + 1) - ρ i) / h - (σs (i - 1))⁻¹ * (ρ i - ρ (i - 1)) / h) / h := by
  intro D
  have h1 : D.Dm *ᵥ (D.sigSInv *ᵥ (D.Dp *ᵥ ρ)) =
      periodicDm n h *ᵥ (Matrix.diagonal (fun i => (σs i)⁻¹) *ᵥ (periodicDp n h *ᵥ ρ)) := rfl
  rw [h1, periodicDm_mulVec]
  simp only [Matrix.mulVec_diagonal, periodicDp_mulVec, mul_div_assoc]
  simp

/-- The quadrature of the periodic discretisation on two cells with two unit weights: the core
quadrature has the weights `1 / 2`, and the periodic stencil is the core one on `Fin 2`, whose
entry `(0, 1)` is `1 / h = 1`. -/
example :
    ((periodic_admissible (n := 1) (h := 1) (w := fun _ : Fin 2 => (1 : ℝ)) (Ω := fun _ => 0)
      (σs := fun _ => 1) (σa := fun _ => 0) (dt := 1) (fun _ => one_pos) (fun _ => one_pos)
      (fun _ => le_rfl) one_pos).toQuadrature).w 0 = 1 / 2 ∧
    (Kinetic.fwdDiff 2 1).submatrix (ZMod.finEquiv 2) (ZMod.finEquiv 2) 0 1 = 1 := by
  refine ⟨?_, ?_⟩
  · simp only [Disc.Admissible.toQuadrature, periodic, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  · rw [← periodicDp_eq_submatrix, periodicDp, Matrix.of_apply]
    norm_num [show (1 : Fin 2) = 0 + 1 from rfl, show ¬((1 : Fin 2) = 0) by decide]

end Periodic

section Examples

local notation "𝓕" => 𝓝[>] (0 : ℝ)

/-- A sample discretisation: four periodic cells of width `1` and four directions with `w = 1`,
`Ωˣ = (1, -1, 1, -1)`, `|D_Ω| = 4`, `σˢ = 1`, `σᵃ = 0`, `Δt = 1`. -/
noncomputable def sample : Disc (Fin 4) (Fin 4) :=
  periodic 3 1 (fun _ => 1) ![1, -1, 1, -1] 4 (fun _ => 1) (fun _ => 0) 1

/-- The alternating vector, on the grid and on the directions. -/
def alt : Fin 4 → ℝ := ![1, -1, 1, -1]

/-- The constant vector. -/
def ones : Fin 4 → ℝ := ![1, 1, 1, 1]

/-- A vector orthogonal to `alt` and `ones`. -/
def half : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- A vector as a matrix with one column. -/
def col (y : Fin 4 → ℝ) : Matrix (Fin 4) Unit ℝ := Matrix.of fun i _ => y i

/-- The density of the sample step. -/
noncomputable def lam (ε : ℝ) : ℝ := (1 + ε ^ 2) / (5 + ε ^ 2)

/-- The sample discretisation satisfies the standing assumptions of arXiv 2602.12337. -/
theorem sample_admissible : sample.Admissible := by
  have h := periodic_admissible (a := Fin 4) (n := 3) (h := 1) (w := fun _ => 1)
    (Ω := ![1, -1, 1, -1]) (σs := fun _ => 1) (σa := fun _ => 0) (dt := 1)
    (fun _ => one_pos) (fun _ => one_pos) (fun _ => le_rfl) one_pos
  have h4 : ∑ _i : Fin 4, (1 : ℝ) = 4 := by simp
  rw [h4] at h
  exact h

private theorem sample_dt : sample.dt = 1 := rfl

private theorem sample_sigS : sample.sigS = 1 := by
  simp [Disc.sigS, sample, periodic]

private theorem sample_sigA : sample.sigA = 0 := by
  simp [Disc.sigA, sample, periodic]

private theorem sample_sigSInv : sample.sigSInv = 1 := by
  simp [Disc.sigSInv, sample, periodic]

private theorem sample_M : sample.M = 1 := by
  simp [Disc.M, sample, periodic]

private theorem sample_Minv : sample.Minv = 1 := by
  simp [Disc.Minv, sample, periodic]

private theorem sample_u : sample.u = alt := by
  ext i
  fin_cases i <;> simp [Disc.u, Disc.M, Disc.Q, sample, periodic, alt, Matrix.mulVec_diagonal]

private theorem sample_scale (ε : ℝ) (i : Fin 4) : sample.scale ε i = 1 + ε ^ 2 := by
  simp [Disc.scale, sample, periodic]
  ring

private theorem sample_moment : sample.moment = 1 := by
  simp [Disc.moment, sample, periodic, Fin.sum_univ_four]
  norm_num

private theorem sample_Dp (t : ℝ) : sample.Dp *ᵥ (t • alt) = (-2 * t) • alt := by
  ext i
  have h : sample.Dp = periodicDp 3 1 := rfl
  rw [h, periodicDp_mulVec]
  fin_cases i <;> simp [alt] <;> ring

private theorem sample_Dm (t : ℝ) : sample.Dm *ᵥ (t • alt) = (2 * t) • alt := by
  ext i
  have h : sample.Dm = periodicDm 3 1 := rfl
  rw [h, periodicDm_mulVec]
  fin_cases i <;> simp [alt] <;> ring

private theorem sample_B_zero : sample.B 0 = 0 := by
  simp [Disc.B, Disc.A]

private theorem col_orth {y : Fin 4 → ℝ} (h : y ⬝ᵥ y = 1) : (col y)ᵀ * col y = 1 := by
  ext ⟨⟩ ⟨⟩
  simpa [Matrix.mul_apply, col, dotProduct] using h

private theorem col_t_mulVec (y z : Fin 4 → ℝ) : (col y)ᵀ *ᵥ z = fun _ => y ⬝ᵥ z := by
  ext ⟨⟩
  simp [Matrix.mulVec, col, dotProduct]

private theorem lift_zero (X V : Matrix (Fin 4) Unit ℝ) :
    sample.lift X (0 : Matrix Unit Unit ℝ) V = 0 := by
  simp [Disc.lift]

private theorem H_zero : sample.H 0 = 0 := by
  simp [Disc.H]

private theorem sample_macro {ε : ℝ} (hε : 0 < ε) (X V : Matrix (Fin 4) Unit ℝ) :
    sample.IsMacroStep ε 0 alt (sample.lift X 0 V) (lam ε • alt) := by
  have h1 := H_R_J (D := sample) hε.ne' (lam ε • alt)
  have h2 : Matrix.diagonal (fun i => (sample.scale ε i)⁻¹) *ᵥ ((-2 * lam ε) • alt) =
      ((-2 * lam ε) / (1 + ε ^ 2)) • alt := by
    ext i
    simp only [Matrix.mulVec_diagonal, sample_scale, Pi.smul_apply, smul_eq_mul]
    ring
  have hA : sample.A 0 = 0 := by simp [Disc.A]
  have hl : 5 + ε ^ 2 ≠ 0 := by positivity
  have he : 1 + ε ^ 2 ≠ 0 := by positivity
  rw [Disc.IsMacroStep, h1, lift_zero, hA, sample_Dp, h2, sample_Dm, sample_moment, sample_dt,
    sample_sigA]
  simp only [smul_zero, Matrix.zero_mul, sub_zero, Matrix.mul_zero, H_zero, Matrix.zero_mulVec,
    add_zero, one_div, inv_one, one_smul]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lam]
  field_simp
  ring

private theorem sample_step {ε : ℝ} (hε : 0 < ε) {x₀ v₀ x₁ v₁ : Fin 4 → ℝ}
    (hx₀ : x₀ ⬝ᵥ x₀ = 1) (hx₁ : x₁ ⬝ᵥ x₁ = 1) (hv₁ : v₁ ⬝ᵥ v₁ = 1) {rk rl : ℝ}
    (hrk : (2 * lam ε * (v₀ ⬝ᵥ alt) / (1 + ε ^ 2)) • alt = rk • x₁)
    (hrl : (2 * lam ε * (x₀ ⬝ᵥ alt) / (1 + ε ^ 2)) • alt = rl • v₁) :
    IsSchurIMEXSBUGStep sample ε 0 alt (col x₀) 0 (col v₀) (lam ε • alt)
      (col ((2 * lam ε * (v₀ ⬝ᵥ alt) / (1 + ε ^ 2)) • alt))
      (col ((2 * lam ε * (x₀ ⬝ᵥ alt) / (1 + ε ^ 2)) • alt)) (col x₁)
      (Matrix.of fun _ _ => 2 * lam ε * (x₁ ⬝ᵥ alt) * (alt ⬝ᵥ v₁) / (1 + ε ^ 2)) (col v₁) := by
  have he : 1 + ε ^ 2 ≠ 0 := by positivity
  have hε' : ε ≠ 0 := hε.ne'
  refine ⟨sample_macro hε _ _, ?_, ?_, col_orth hx₁, col_orth hv₁,
    ⟨Matrix.of fun _ _ => rk, ?_⟩, ⟨Matrix.of fun _ _ => rl, ?_⟩, ?_⟩
  · rw [Disc.IsKStep, J_M_V, sample_Dp, sample_u, col_t_mulVec]
    simp only [Matrix.mul_zero, Matrix.zero_mul, sample_B_zero, smul_zero, sample_sigS, sample_sigA,
      sample_dt, Matrix.one_mul, sub_zero]
    ext i ⟨⟩
    simp only [col, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
    field_simp
    ring
  · have h1 : (col x₀)ᵀ * sample.sigS * col x₀ = 1 := by
      rw [sample_sigS, Matrix.mul_one, col_orth hx₀]
    have h2 : (col x₀)ᵀ *ᵥ ((-2 * lam ε) • alt) = fun _ => -2 * lam ε * (x₀ ⬝ᵥ alt) := by
      rw [col_t_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Disc.IsLStep, M_Jt_X, sample_Dp, h2, h1, sample_u, sample_sigA]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, sample_B_zero, smul_zero,
      sample_dt, Matrix.mul_one, sub_zero]
    ext i ⟨⟩
    simp only [col, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
    field_simp
    ring
  · ext i ⟨⟩
    have h1 := congrFun hrk i
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    simp only [col, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_unique]
    linarith
  · ext i ⟨⟩
    have h1 := congrFun hrl i
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    simp only [col, Matrix.mul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_unique]
    linarith
  · have h1 : (col x₁)ᵀ * sample.sigS * col x₁ = 1 := by
      rw [sample_sigS, Matrix.mul_one, col_orth hx₁]
    have h2 : (col x₁)ᵀ * sample.J (lam ε • alt) * sample.M * col v₁ =
        (col x₁)ᵀ * Matrix.vecMulVec ((-2 * lam ε) • alt) (fun _ => v₁ ⬝ᵥ alt) := by
      have h3 : (fun _ : Unit => v₁ ⬝ᵥ alt) = (col v₁)ᵀ *ᵥ sample.u := by
        rw [sample_u, col_t_mulVec]
      rw [h3, ← sample_Dp, ← J_M_V]
      simp only [Matrix.mul_assoc]
    rw [Disc.IsSStep, h2, h1, sample_sigA]
    simp only [Matrix.mul_zero, Matrix.zero_mul, sample_B_zero, smul_zero, sample_dt,
      Matrix.one_mul, sub_zero]
    ext ⟨⟩ ⟨⟩
    have h4 : ∑ j, x₁ j * (alt j * v₁ ⬝ᵥ alt) = (x₁ ⬝ᵥ alt) * (v₁ ⬝ᵥ alt) := by
      change _ = (∑ j, x₁ j * alt j) * _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, one_mul, one_div, col, neg_mul, neg_smul, Matrix.neg_vecMulVec,
      Matrix.smul_vecMulVec, Matrix.mul_neg, Matrix.mul_smul, smul_neg, sub_neg_eq_add, zero_add,
      Matrix.smul_of, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, Pi.smul_apply]
    rw [h4, dotProduct_comm alt v₁]
    field_simp
    ring

private theorem dot_half_smul (y z : Fin 4 → ℝ) : ((1 / 2 : ℝ) • y) ⬝ᵥ z = (1 / 2) * (y ⬝ᵥ z) := by
  rw [smul_dotProduct, smul_eq_mul]

private theorem alt_alt : alt ⬝ᵥ alt = 4 := by
  simp [alt, dotProduct, Fin.sum_univ_four]
  norm_num

private theorem ones_ones : ones ⬝ᵥ ones = 4 := by
  simp [ones, dotProduct, Fin.sum_univ_four]
  norm_num

private theorem half_half : half ⬝ᵥ half = 4 := by
  simp [half, dotProduct, Fin.sum_univ_four]
  norm_num

private theorem ones_alt : ones ⬝ᵥ alt = 0 := by
  simp [ones, alt, dotProduct, Fin.sum_univ_four]

private theorem half_alt : half ⬝ᵥ alt = 0 := by
  simp [half, alt, dotProduct, Fin.sum_univ_four]

private theorem alt_ones : alt ⬝ᵥ ones = 0 := by
  rw [dotProduct_comm, ones_alt]

private theorem half_ones : half ⬝ᵥ ones = 0 := by
  simp [half, ones, dotProduct, Fin.sum_univ_four]

/-- A column orthogonal to `ones` satisfies the zero-density constraint `1ᵀ M V = 0` of Sec. 4.3. -/
private theorem constraint {y : Fin 4 → ℝ} (h : y ⬝ᵥ ones = 0) :
    (col ((1 / 2 : ℝ) • y))ᵀ *ᵥ (sample.M *ᵥ fun _ => 1) = 0 := by
  have h1 : (fun _ : Fin 4 => (1 : ℝ)) = ones := by
    ext i
    fin_cases i <;> rfl
  rw [sample_M, Matrix.one_mulVec, h1, col_t_mulVec, dot_half_smul, h, mul_zero]
  rfl

private theorem unit_of {y : Fin 4 → ℝ} (h : y ⬝ᵥ y = 4) :
    ((1 / 2 : ℝ) • y) ⬝ᵥ ((1 / 2 : ℝ) • y) = 1 := by
  rw [dot_half_smul, dotProduct_smul, smul_eq_mul, h]
  norm_num

private theorem tendsto_lam : Tendsto (fun ε => lam ε • alt) 𝓕 (𝓝 ((1 / 5 : ℝ) • alt)) := by
  have hc : Continuous lam := Continuous.div (by fun_prop) (by fun_prop) fun ε => by positivity
  have h1 : Tendsto lam 𝓕 (𝓝 (1 / 5)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    simpa [lam] using hc.tendsto 0
  exact h1.smul_const alt

private theorem lam_ge (ε : ℝ) : 1 / 5 ≤ lam ε := by
  rw [lam, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ε]

private theorem sample_diffusion : sample.IsDiffusionStep 0 alt ((1 / 5 : ℝ) • alt) := by
  rw [Disc.IsDiffusionStep, sample_Dp, sample_sigSInv, Matrix.one_mulVec, sample_Dm, sample_moment,
    sample_sigA, sample_dt]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.zero_mulVec,
    Pi.zero_apply]
  ring

private theorem sample_flux :
    -(sample.moment • (sample.Dm *ᵥ (sample.sigSInv *ᵥ (sample.Dp *ᵥ ((1 / 5 : ℝ) • alt))))) =
      (4 / 5 : ℝ) • alt := by
  rw [sample_Dp, sample_sigSInv, Matrix.one_mulVec, sample_Dm, sample_moment]
  ext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem flux_ne : (4 / 5 : ℝ) • alt ≠ 0 := by
  intro h
  have h1 := congrFun h 0
  simp [alt] at h1

/-- The density step does not see the bases, the flux of a vanishing `S¹` does not converge to the
diffusion flux. -/
private theorem not_tendsto_zero {X V : Matrix (Fin 4) Unit ℝ} :
    ¬ Tendsto (fun _ : ℝ => sample.H (sample.lift X (0 : Matrix Unit Unit ℝ) V)) 𝓕
      (𝓝 (-(sample.moment •
        (sample.Dm *ᵥ (sample.sigSInv *ᵥ (sample.Dp *ᵥ ((1 / 5 : ℝ) • alt))))))) := by
  intro h
  rw [lift_zero, H_zero, sample_flux] at h
  exact flux_ne (tendsto_nhds_unique h tendsto_const_nhds)

private theorem not_mem_range_of_ones {z : Unit → ℝ} (h : ∀ i, (col ((1 / 2 : ℝ) • ones) *ᵥ z) i =
    -(sample.sigSInv *ᵥ (sample.Dp *ᵥ ((1 / 5 : ℝ) • alt))) i) : False := by
  have h1 := h 0
  have h2 := h 1
  simp only [sample_Dp, sample_sigSInv, Matrix.one_mulVec] at h1 h2
  simp [col, Matrix.mulVec, dotProduct, ones, alt] at h1 h2
  linarith

private theorem not_mem_range_of_half {z : Unit → ℝ} (h : col ((1 / 2 : ℝ) • half) *ᵥ z = alt) :
    False := by
  have h1 := congrFun h 0
  have h2 := congrFun h 1
  simp [col, Matrix.mulVec, dotProduct, half, alt] at h1 h2
  linarith

private theorem hq_alt :
    ∃ δ > 0, ∀ ε > 0, δ ≤ (col ((1 / 2 : ℝ) • alt))ᵀ *ᵥ (sample.Dp *ᵥ (lam ε • alt)) ⬝ᵥ
      (col ((1 / 2 : ℝ) • alt))ᵀ *ᵥ (sample.Dp *ᵥ (lam ε • alt)) := by
  refine ⟨16 / 25, by norm_num, fun ε _ => ?_⟩
  have h1 : (col ((1 / 2 : ℝ) • alt))ᵀ *ᵥ (sample.Dp *ᵥ (lam ε • alt)) = fun _ => -4 * lam ε := by
    rw [sample_Dp, col_t_mulVec, dotProduct_smul, smul_eq_mul, dot_half_smul, alt_alt]
    funext _
    ring
  have h2 := lam_ge ε
  rw [h1]
  simp only [dotProduct, Fintype.sum_unique]
  nlinarith

private theorem step_formula_zero {t : ℝ} (ht : t = 0) {ε p : ℝ} :
    (Matrix.of fun (_ _ : Unit) => 2 * lam ε * t * p / (1 + ε ^ 2)) = 0 := by
  subst ht
  ext
  simp

/-- **Sec. 4.2, the range of the left basis fails without nondegeneracy** (arXiv 2602.12337): the
claim `-(σˢ)⁻¹ 𝒟^{x,+} ρ^{n+1} ∈ Range X^{n+1}` is false in general.  On the sample discretisation
take `Sⁿ = 0` and `Vⁿ ⊥ M Qˣ 1`.  This is an admissible state: `Gⁿ = 0`, and `Vⁿ` also satisfies
the constraint `1ᵀ M V = 0`.  For every `ε > 0` the scheme has `K¹ = 0`, so that `X¹` is not
determined by the QR step; take `X¹` orthogonal to `𝒟^{x,+} ρ¹`.  The nondegeneracy of
`tendsto_flux` on `X⁰` holds, the density still converges to the diffusion step, but
`-(σˢ)⁻¹ 𝒟^{x,+} ρ*` is not in `Range X¹`, and the low-rank flux does not converge to the diffusion
flux. -/
theorem ap_fails_of_degenerate_right :
    ∃ (X₀ V₀ X₁ V₁ : Matrix (Fin 4) Unit ℝ) (ρ₁ : ℝ → Fin 4 → ℝ)
      (K₁ L₁ : ℝ → Matrix (Fin 4) Unit ℝ) (S₁ : ℝ → Matrix Unit Unit ℝ) (ρs : Fin 4 → ℝ),
      X₀ᵀ * X₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧
      (∀ ε > 0, IsSchurIMEXSBUGStep sample ε 0 alt X₀ 0 V₀ (ρ₁ ε) (K₁ ε) (L₁ ε) X₁ (S₁ ε) V₁) ∧
      V₀ᵀ *ᵥ (sample.M *ᵥ fun _ => 1) = 0 ∧ V₁ᵀ *ᵥ (sample.M *ᵥ fun _ => 1) = 0 ∧
      sample.IsDiffusionStep 0 alt ρs ∧ Tendsto ρ₁ 𝓕 (𝓝 ρs) ∧
      V₀ᵀ *ᵥ sample.u = 0 ∧
      (∃ δ > 0, ∀ ε > 0, δ ≤ X₀ᵀ *ᵥ (sample.Dp *ᵥ ρ₁ ε) ⬝ᵥ X₀ᵀ *ᵥ (sample.Dp *ᵥ ρ₁ ε)) ∧
      (∀ ε, K₁ ε = 0) ∧
      (¬ ∃ z, X₁ *ᵥ z = -(sample.sigSInv *ᵥ (sample.Dp *ᵥ ρs))) ∧
      ¬ Tendsto (fun ε => sample.H (sample.lift X₁ (S₁ ε) V₁)) 𝓕
        (𝓝 (-(sample.moment • (sample.Dm *ᵥ (sample.sigSInv *ᵥ (sample.Dp *ᵥ ρs)))))) := by
  have hv₀ : ((1 / 2 : ℝ) • half) ⬝ᵥ alt = 0 := by rw [dot_half_smul, half_alt, mul_zero]
  have hx₁ : ((1 / 2 : ℝ) • ones) ⬝ᵥ alt = 0 := by rw [dot_half_smul, ones_alt, mul_zero]
  have hx₀ : ((1 / 2 : ℝ) • alt) ⬝ᵥ alt = 2 := by rw [dot_half_smul, alt_alt]; norm_num
  have hk : ∀ ε : ℝ, col ((2 * lam ε * (((1 / 2 : ℝ) • half) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt) = 0 := by
    intro ε
    rw [hv₀]
    ext i j
    simp [col]
  refine ⟨col ((1 / 2 : ℝ) • alt), col ((1 / 2 : ℝ) • half), col ((1 / 2 : ℝ) • ones),
    col ((1 / 2 : ℝ) • alt), fun ε => lam ε • alt, fun _ => 0,
    fun ε => col ((2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt), fun _ => 0,
    (1 / 5 : ℝ) • alt, col_orth (unit_of alt_alt), col_orth (unit_of half_half), ?_,
    constraint half_ones, constraint alt_ones, sample_diffusion, tendsto_lam, ?_, hq_alt,
    fun _ => rfl, ?_, not_tendsto_zero⟩
  · intro ε hε
    have h := sample_step hε (x₀ := (1 / 2 : ℝ) • alt) (v₀ := (1 / 2 : ℝ) • half)
      (x₁ := (1 / 2 : ℝ) • ones) (v₁ := (1 / 2 : ℝ) • alt) (unit_of alt_alt) (unit_of ones_ones)
      (unit_of alt_alt) (rk := 0) (rl := 8 * lam ε / (1 + ε ^ 2))
      (by rw [hv₀]; simp) (by
        rw [hx₀, smul_smul]
        congr 1
        ring)
    rw [hk ε, step_formula_zero hx₁] at h
    exact h
  · rw [sample_u, col_t_mulVec, hv₀]
    rfl
  · rintro ⟨z, hz⟩
    exact not_mem_range_of_ones (z := z) fun i => congrFun hz i

/-- **Sec. 4.2, the range of the right basis fails without nondegeneracy** (arXiv 2602.12337): the
claim `M Qˣ 1 ∈ Range V^{n+1}` is false in general.  Take `Sⁿ = 0` and `Xⁿ ⊥ 𝒟^{x,+} ρ¹` on the
sample discretisation.  For every `ε > 0` the scheme has `L¹ = 0`, so that `V¹` is not determined by
the QR step; take `V¹ ⊥ M Qˣ 1` with `1ᵀ M V¹ = 0`.  The nondegeneracy on `V⁰` holds, the density
converges to the diffusion step, but `M Qˣ 1 ∉ Range V¹` and the low-rank flux does not converge to
the diffusion flux. -/
theorem ap_fails_of_degenerate_left :
    ∃ (X₀ V₀ X₁ V₁ : Matrix (Fin 4) Unit ℝ) (ρ₁ : ℝ → Fin 4 → ℝ)
      (K₁ L₁ : ℝ → Matrix (Fin 4) Unit ℝ) (S₁ : ℝ → Matrix Unit Unit ℝ) (ρs : Fin 4 → ℝ),
      X₀ᵀ * X₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧
      (∀ ε > 0, IsSchurIMEXSBUGStep sample ε 0 alt X₀ 0 V₀ (ρ₁ ε) (K₁ ε) (L₁ ε) X₁ (S₁ ε) V₁) ∧
      V₀ᵀ *ᵥ (sample.M *ᵥ fun _ => 1) = 0 ∧ V₁ᵀ *ᵥ (sample.M *ᵥ fun _ => 1) = 0 ∧
      sample.IsDiffusionStep 0 alt ρs ∧ Tendsto ρ₁ 𝓕 (𝓝 ρs) ∧
      V₀ᵀ *ᵥ sample.u ≠ 0 ∧
      (∀ ε, X₀ᵀ *ᵥ (sample.Dp *ᵥ ρ₁ ε) = 0) ∧
      (∀ ε, L₁ ε = 0) ∧
      (¬ ∃ z, V₁ *ᵥ z = sample.u) ∧
      ¬ Tendsto (fun ε => sample.H (sample.lift X₁ (S₁ ε) V₁)) 𝓕
        (𝓝 (-(sample.moment • (sample.Dm *ᵥ (sample.sigSInv *ᵥ (sample.Dp *ᵥ ρs)))))) := by
  have hx₀ : ((1 / 2 : ℝ) • ones) ⬝ᵥ alt = 0 := by rw [dot_half_smul, ones_alt, mul_zero]
  have hv₀ : ((1 / 2 : ℝ) • alt) ⬝ᵥ alt = 2 := by rw [dot_half_smul, alt_alt]; norm_num
  have hv₁ : alt ⬝ᵥ ((1 / 2 : ℝ) • half) = 0 := by
    rw [dotProduct_comm, dot_half_smul, half_alt, mul_zero]
  have hl : ∀ ε : ℝ, col ((2 * lam ε * (((1 / 2 : ℝ) • ones) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt) = 0 := by
    intro ε
    rw [hx₀]
    ext i j
    simp [col]
  have hS : ∀ ε : ℝ, (Matrix.of fun (_ _ : Unit) => 2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) *
      (alt ⬝ᵥ ((1 / 2 : ℝ) • half)) / (1 + ε ^ 2)) = 0 := by
    intro ε
    rw [hv₁]
    ext
    simp
  refine ⟨col ((1 / 2 : ℝ) • ones), col ((1 / 2 : ℝ) • alt), col ((1 / 2 : ℝ) • alt),
    col ((1 / 2 : ℝ) • half), fun ε => lam ε • alt,
    fun ε => col ((2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt), fun _ => 0,
    fun _ => 0, (1 / 5 : ℝ) • alt, col_orth (unit_of ones_ones), col_orth (unit_of alt_alt), ?_,
    constraint alt_ones, constraint half_ones, sample_diffusion, tendsto_lam, ?_, ?_, fun _ => rfl,
    ?_, not_tendsto_zero⟩
  · intro ε hε
    have h := sample_step hε (x₀ := (1 / 2 : ℝ) • ones) (v₀ := (1 / 2 : ℝ) • alt)
      (x₁ := (1 / 2 : ℝ) • alt) (v₁ := (1 / 2 : ℝ) • half) (unit_of ones_ones) (unit_of alt_alt)
      (unit_of half_half) (rk := 8 * lam ε / (1 + ε ^ 2)) (rl := 0)
      (by
        rw [hv₀, smul_smul]
        congr 1
        ring) (by rw [hx₀]; simp)
    rw [hl ε, hS ε] at h
    exact h
  · rw [sample_u, col_t_mulVec, hv₀]
    intro h
    have h1 := congrFun h ()
    norm_num at h1
  · intro ε
    rw [sample_Dp, col_t_mulVec, dotProduct_smul, hx₀, smul_zero]
    rfl
  · rintro ⟨z, hz⟩
    rw [sample_u] at hz
    exact not_mem_range_of_half hz

/-- **Sec. 4.2, non-vacuity** (arXiv 2602.12337).  On the sample discretisation all hypotheses of
`tendsto_flux` hold for a family of steps with `D^{x,+} ρ* ≠ 0`, so that the flux limit is
nontrivial. -/
theorem nondegenerate_instance :
    ∃ (X₀ V₀ X₁ V₁ : Matrix (Fin 4) Unit ℝ) (ρ₁ : ℝ → Fin 4 → ℝ)
      (K₁ L₁ : ℝ → Matrix (Fin 4) Unit ℝ) (S₁ : ℝ → Matrix Unit Unit ℝ) (ρs : Fin 4 → ℝ),
      X₀ᵀ * X₀ = 1 ∧ V₀ᵀ * V₀ = 1 ∧
      (∀ ε > 0, IsSchurIMEXSBUGStep sample ε 0 alt X₀ 0 V₀ (ρ₁ ε) (K₁ ε) (L₁ ε) X₁ (S₁ ε) V₁) ∧
      sample.IsDiffusionStep 0 alt ρs ∧ Tendsto ρ₁ 𝓕 (𝓝 ρs) ∧
      V₀ᵀ *ᵥ sample.u ≠ 0 ∧
      (∃ δ > 0, ∀ ε > 0, δ ≤ X₀ᵀ *ᵥ (sample.Dp *ᵥ ρ₁ ε) ⬝ᵥ X₀ᵀ *ᵥ (sample.Dp *ᵥ ρ₁ ε)) ∧
      -(sample.moment • (sample.Dm *ᵥ (sample.sigSInv *ᵥ (sample.Dp *ᵥ ρs)))) ≠ 0 := by
  have hv₀ : ((1 / 2 : ℝ) • alt) ⬝ᵥ alt = 2 := by rw [dot_half_smul, alt_alt]; norm_num
  refine ⟨col ((1 / 2 : ℝ) • alt), col ((1 / 2 : ℝ) • alt), col ((1 / 2 : ℝ) • alt),
    col ((1 / 2 : ℝ) • alt), fun ε => lam ε • alt,
    fun ε => col ((2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt),
    fun ε => col ((2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) / (1 + ε ^ 2)) • alt),
    fun ε => Matrix.of fun _ _ => 2 * lam ε * (((1 / 2 : ℝ) • alt) ⬝ᵥ alt) *
      (alt ⬝ᵥ ((1 / 2 : ℝ) • alt)) / (1 + ε ^ 2), (1 / 5 : ℝ) • alt,
    col_orth (unit_of alt_alt), col_orth (unit_of alt_alt), fun ε hε => ?_,
    sample_diffusion, tendsto_lam, ?_, hq_alt, ?_⟩
  · refine sample_step hε (unit_of alt_alt) (unit_of alt_alt) (unit_of alt_alt)
      (rk := 8 * lam ε / (1 + ε ^ 2)) (rl := 8 * lam ε / (1 + ε ^ 2)) ?_ ?_ <;>
    · rw [hv₀, smul_smul]
      congr 1
      ring
  · rw [sample_u, col_t_mulVec, hv₀]
    intro h
    have h1 := congrFun h ()
    norm_num at h1
  · rw [sample_flux]
    exact flux_ne

end Examples

end LeanDLRA.Literature.P2602_12337
