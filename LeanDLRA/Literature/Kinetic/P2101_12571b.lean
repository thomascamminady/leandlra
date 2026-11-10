import LeanDLRA.Integrators.BUG
import LeanDLRA.Kinetic.Defs
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal

/-!
# Results of arXiv 2101.12571, Sec. 6.2: the unconventional conservative integrator

This module formalizes the integrator of Sec. 6.2 of Einkemmer-Joseph, *A mass, momentum, and energy
conservative dynamical low-rank scheme for the Vlasov equation*, in the fully discrete setting in
which it is run.  `Grid` holds arbitrary positive quadrature weights in `x` and `v` and the weight
`f₀ᵥ`, `D` is an arbitrary right-hand side (any space discretization), and `Grid.IsStep` is one
step: the K- and L-updates, QR, and the S-update with `M` and `N`, each written with the paper's
formula (`Grid.kNext`, `Grid.lNext`, `Grid.sNext`).  Nothing is assumed about `S`.

## Main results

* `Grid.exists_step`: the step exists for every state and every `S`, also singular.  This is the
  claim that `S` need not be inverted; `Grid.lNext_orth` gives `Lⁿ⁺¹ ⊥ Uₐ`.
* `Grid.IsStep.range_kNext`, `Grid.IsStep.range_lNext`: the spaces are determined by `Kⁿ⁺¹`, `Lⁿ⁺¹`.
  `Grid.IsStep.spaces_eq_consEuler`: they are the spaces of the conservative Euler scheme (14)-(16).
* `Grid.fStart_eq`: the paper's `∑ Xᵢ Sᵢⱼ Vⱼ ≈ ∑ Xₖ' Mₖᵢ Sᵢⱼ Nᵀⱼₗ Vₗ'` is `f̃ = P₁ fⁿ Q₁`.
  `Grid.IsStep.start_error_le`: `‖f̃ - fⁿ‖ ≤ 2 |τ| ‖D[fⁿ]‖`, uniformly in `S`.  Its key step is
  `norm_mul_transpose_le_of_mul_eq`, which handles `Sₚᵀ Sₚ` without inverting it.
* `Grid.IsStep.continuity`: the discrete continuity equation with its exact defect
  `τ P₁ (ρ_ζ[D[f̃]] - ρ_ζ[D[fⁿ]])`.  `Grid.IsStep.charge_sub`: the exact change of a global
  invariant.  `Grid.IsStep.continuity_of_nested`, `Grid.IsStep.charge_eq_of_mem`: no loss if the
  projection is exact, or if `c ∈ X̄ⁿ⁺¹`.
* `Grid.IsStep.charge_defect_le`, `Grid.charge_drift_le`: the conservation error is `O(τ²)` per step
  and `O(τ)` over a fixed time, uniformly in `S` (Sec. 7.3 reports this numerically).
* `vp_mass_momentum_change`, with `vp_instance`, `vp_mass_conservative`, `vp_momentum_conservative`:
  for a discrete Vlasov-Poisson operator that conserves mass and momentum exactly and a nonnegative
  `fⁿ`, the exact change of both per step, for all `τ`.  This proves the claim that conservation is
  lost, and it shows that `O(τ²)` is sharp.  `rob_mass_change`: the same with a dynamic `W`.
* `rob_local_error`, `rob_competitor`, `rob_no_uniform_bound`: see "The robustness claim" below.

The remedy of later work (augmented bases) is `consBug_euler_inner_eq` in
`Stability/Conservation.lean`; `bug_moment_defect` in `OpenProblems/Conservation/Part3a.lean` is the
abstract `O(h²)` defect for exact substeps and the classical L-step, which is a different
integrator.

## Differences from the paper

* The paper's integrator is stated for functions of `x` and `v`.  Here it is fully discrete: the
  paper says that its calculations carry over when the quadrature allows exact integration by parts,
  and `D` and the weights are arbitrary, but the PDE itself is not treated.  The estimates need `D`
  Lipschitz on the discrete space, which fails for the PDE.
* QR is recorded by `K = X' R`, `L = W' R`, with orthonormal factors.  `R` need not be triangular,
  so universal statements are slightly stronger than the paper's.  In the rank-deficient case the
  completion must be chosen with `W' ⊥ U`; `IsState` requires it, and `exists_step` shows it is
  possible.  In the full-rank case it is automatic, as `W' = Lⁿ⁺¹ R⁻¹` and `Grid.lNext_orth`.
* The paper's formula for `Lⁿ⁺¹` prints `(Xₖⁿ Vₗⁿ, D[fⁿ])` under a sum over `i`, `l`.  It is read
  as `(Xᵢⁿ Vₗⁿ, D[fⁿ])ₓᵥ`, as in (11).  Eq. (15) prints `(S⁻¹)ᵢₖ`; `Grid.ceX` uses `(S⁻¹)ₖᵢ`,
  which is what the Euler step of (13) requires (the two agree only for symmetric `S`).
* The paper blames both `M` and `N` for the loss.  `Grid.IsStep.density_fStart` shows that the
  moments of the start see only `M`, since `Nᵀ` fixes the `Uₐ`.  `N` acts through the flux at `f̃`.
* `vp_mass_momentum_change` uses `m = r = 2`, a two-point velocity grid and the velocity derivative
  `vpDv` built for exact integration by parts.  Momentum is unchanged at the one value
  `τ² = 513/126250`, and is lost for every other `τ ≠ 0`.
* The energy is not treated: it needs the electric energy of Sec. 6.1.

## The robustness claim of Sec. 6.2 (an interpretation)

Sec. 6.2 says: "This gives us a robust dynamical low-rank integrator as the matrix `S` needs not
be inverted".  The paper does not define "robust"; it motivates the word by the ill-conditioned
inversion of `S` and refers to [17] (Kieri-Lubich-Walach).  The second half is true
(`Grid.exists_step`), and in the sense "no inverse of `S`" the claim holds.  In the sense of [17]
and of Ceruti-Lubich [3], where robust means error bounds independent of small singular values,
the claim fails; this reading is ours, not a statement printed in the paper.  `rob_local_error`:
for free streaming and
`S = diag(3, ε)` with `0 < ε ≤ (12/25) τ`, every step misses the Euler step by at least
`(9/25) τ / √2`.  `rob_no_uniform_bound`: no bound `C τ²` holds uniformly in `ε`.
`rob_competitor`: the format is not to blame, since an admissible state with the same `X` and `U`
is within `τ ε` of the Euler step.  The cause is that `Lⁿ⁺¹` drops the part of `D[fⁿ]` along the
current `Wₚ`, so QR overshoots when `S` is small.  The result concerns one step: it does not
contradict the numerics of Sec. 7, and it is not a statement about convergence.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2101_12571

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-- A tensor phase-space grid. -/
structure Grid (Mx Mv : Type*) where
  /-- Quadrature weights of `∫ dx`. -/
  wx : Mx → ℝ
  /-- Quadrature weights of `∫ dv`. -/
  wv : Mv → ℝ
  /-- The weight function `f₀ᵥ` on the velocity grid. -/
  f0 : Mv → ℝ
  wx_pos : ∀ x, 0 < wx x
  wv_pos : ∀ v, 0 < wv v
  f0_pos : ∀ v, 0 < f0 v

variable {Mx Mv a p r s : Type*} [Fintype Mx] [Fintype Mv] [Fintype a] [Fintype p] [Fintype r]
  [Fintype s] [DecidableEq Mx] [DecidableEq Mv] [DecidableEq a] [DecidableEq p] [DecidableEq r]
  [DecidableEq s]

namespace Grid

variable (q : Grid Mx Mv)

/-- The Gram matrix of `(·,·)ₓ = ⟨·,·⟩ₓ` (`f₀ₓ = 1`). -/
def Hx : Matrix Mx Mx ℝ := diagonal q.wx

/-- The Gram matrix of the unweighted `(·,·)ᵥ`. -/
def Hu : Matrix Mv Mv ℝ := diagonal q.wv

/-- The Gram matrix of the weighted `⟨·,·⟩ᵥ = ∫ f₀ᵥ · · dv`. -/
def Hv : Matrix Mv Mv ℝ := diagonal fun v => q.wv v * q.f0 v

/-- Multiplication by `f₀ᵥ`. -/
def F : Matrix Mv Mv ℝ := diagonal q.f0

/-- Multiplication by `1 / f₀ᵥ`. -/
noncomputable def Fi : Matrix Mv Mv ℝ := diagonal fun v => (q.f0 v)⁻¹

/-- Eq. (8): `f = f₀ᵥ ∑ᵢⱼ Xᵢ Sᵢⱼ Vⱼ`. -/
def dist (X : Matrix Mx r ℝ) (S : Matrix r s ℝ) (V : Matrix Mv s ℝ) : Matrix Mx Mv ℝ :=
  X * S * Vᵀ * q.F

/-- `(Vₖ, A)ᵥ`, a function of `x` for every `k`. -/
def pairV (A : Matrix Mx Mv ℝ) (V : Matrix Mv s ℝ) : Matrix Mx s ℝ := A * q.Hu * V

/-- `(Xᵢ, A)ₓ`, a function of `v` for every `i`. -/
def pairX (X : Matrix Mx r ℝ) (A : Matrix Mx Mv ℝ) : Matrix Mv r ℝ := Aᵀ * q.Hx * X

/-- `(Xᵢ Vⱼ, A)ₓᵥ`. -/
def pairXV (X : Matrix Mx r ℝ) (V : Matrix Mv s ℝ) (A : Matrix Mx Mv ℝ) : Matrix r s ℝ :=
  Xᵀ * q.Hx * A * q.Hu * V

/-- The density `∫ ζ f dv` of a velocity function `ζ` (`ζ = 1`: `ρ`, `ζ = v`: `j`). -/
def density (ζ : Mv → ℝ) (f : Matrix Mx Mv ℝ) (x : Mx) : ℝ := ∑ v, q.wv v * ζ v * f x v

/-- `(a, b)ₓ`. -/
def ipx (u w : Mx → ℝ) : ℝ := ∑ x, q.wx x * u x * w x

/-- The global invariant `∫∫ c(x) ζ(v) f d(x,v)`.  For `c = 1` and `ζ = 1, v` this is the mass and
the momentum. -/
def charge (c : Mx → ℝ) (ζ : Mv → ℝ) (f : Matrix Mx Mv ℝ) : ℝ := q.ipx c (q.density ζ f)

/-- `P₁ = X' X'ᵀ Hx`, the orthogonal projector of `⟨·,·⟩ₓ` onto `span X'`. -/
def projX (X' : Matrix Mx r ℝ) : Matrix Mx Mx ℝ := X' * X'ᵀ * q.Hx

end Grid

/-- The block `Sᵢ_q` of `S` with the columns of the dynamic velocity functions. -/
def colsP (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) : Matrix (a ⊕ p) p ℝ := S.submatrix id Sum.inr

namespace Grid

variable (q : Grid Mx Mv)

/-- Sec. 6.2: `Kₖⁿ⁺¹ = Kₖⁿ + τ (Vₖⁿ, A)ᵥ` with `Kₖ = ∑ᵢ Xᵢ Sᵢₖ`, `A = D[fⁿ]`. -/
def kNext (τ : ℝ) (X : Matrix Mx r ℝ) (S : Matrix r s ℝ) (V : Matrix Mv s ℝ)
    (A : Matrix Mx Mv ℝ) : Matrix Mx s ℝ :=
  X * S + τ • q.pairV A V

/-- Sec. 6.2: `L_qⁿ⁺¹ = L_qⁿ + (τ/f₀ᵥ) ∑ᵢ Sᵢ_q (Xᵢ, A)ₓ - τ ∑ᵢₗ Sᵢ_q (Xᵢ Vₗ, A)ₓᵥ Vₗ` with
`L_q = ∑ᵢₚ Sᵢ_q Sᵢₚ Wₚ`, `A = D[fⁿ]`. -/
noncomputable def lNext (τ : ℝ) (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ)
    (V : Matrix Mv (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) (A : Matrix Mx Mv ℝ) : Matrix Mv p ℝ :=
  W * ((colsP S)ᵀ * colsP S) +
    τ • (q.Fi * q.pairX X A * colsP S - V * (q.pairXV X V A)ᵀ * colsP S)

/-- Sec. 6.2: the start `M Sⁿ Nᵀ` of the S-step, with `Mₖᵢ = ⟨Xₖⁿ⁺¹, Xᵢⁿ⟩ₓ` and
`Nᵀⱼₗ = ⟨Vⱼⁿ, Vₗⁿ⁺¹⟩ᵥ`. -/
def sStart (X' X : Matrix Mx r ℝ) (S : Matrix r s ℝ) (V V' : Matrix Mv s ℝ) : Matrix r s ℝ :=
  (X'ᵀ * q.Hx * X) * S * (Vᵀ * q.Hv * V')

end Grid

variable (q : Grid Mx Mv)

/-- The velocity basis `V = [U, W]`, fixed functions first. -/
abbrev vb (U : Matrix Mv a ℝ) (W : Matrix Mv p ℝ) : Matrix Mv (a ⊕ p) ℝ := fromCols U W

namespace Grid

/-- The admissible factors of Sec. 4: `⟨Xᵢ, Xⱼ⟩ₓ = δᵢⱼ`, `⟨Uₐ, U_b⟩ᵥ = δₐ_b`, `⟨Wₚ, W_q⟩ᵥ = δₚ_q`,
`⟨Uₐ, Wₚ⟩ᵥ = 0`.  `S` is arbitrary: unlike in Sec. 4 it need not be invertible. -/
structure IsState (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) : Prop where
  orthX : Xᵀ * q.Hx * X = 1
  orthU : Uᵀ * q.Hv * U = 1
  orthW : Wᵀ * q.Hv * W = 1
  orthUW : Uᵀ * q.Hv * W = 0

/-- `Sⁿ⁺¹ = M Sⁿ Nᵀ + τ (Xⁿ⁺¹ Vⁿ⁺¹, D[f(Xⁿ⁺¹, M Sⁿ Nᵀ, Vⁿ⁺¹)])ₓᵥ`. -/
def sNext (D : Matrix Mx Mv ℝ → Matrix Mx Mv ℝ) (τ : ℝ) (X' X : Matrix Mx r ℝ) (S : Matrix r r ℝ)
    (V V' : Matrix Mv r ℝ) : Matrix r r ℝ :=
  q.sStart X' X S V V' + τ • q.pairXV X' V' (D (q.dist X' (q.sStart X' X S V V') V'))

/-- One step of the integrator of Sec. 6.2 from `(X, S, [U, W])` to `(X', S', [U, W'])`.
The K- and L-updates are followed by QR decompositions, recorded by their two defining properties
(orthonormal factor, `Kⁿ⁺¹ = X' R¹`, `Lⁿ⁺¹ = W' R²`); `R¹` and `R²` are discarded. -/
structure IsStep (D : Matrix Mx Mv ℝ → Matrix Mx Mv ℝ) (τ : ℝ) (U : Matrix Mv a ℝ)
    (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (W : Matrix Mv p ℝ)
    (X' : Matrix Mx (a ⊕ p) ℝ) (S' : Matrix (a ⊕ p) (a ⊕ p) ℝ) (W' : Matrix Mv p ℝ) : Prop where
  state : q.IsState U X' W'
  qrK : ∃ R : Matrix (a ⊕ p) (a ⊕ p) ℝ,
    q.kNext τ X S (vb U W) (D (q.dist X S (vb U W))) = X' * R
  qrL : ∃ R : Matrix p p ℝ, q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W))) = W' * R
  sStep : S' = q.sNext D τ X' X S (vb U W) (vb U W')

variable {q}

lemma Hv_transpose : q.Hvᵀ = q.Hv := by simp [Hv]
lemma Hx_transpose : q.Hxᵀ = q.Hx := by simp [Hx]
lemma F_mul_Hu : q.F * q.Hu = q.Hv := by
  simp [F, Hu, Hv, diagonal_mul_diagonal, mul_comm]
lemma Fi_mul_Hv : q.Fi * q.Hv = q.Hu := by
  simp only [Fi, Hu, Hv, diagonal_mul_diagonal]
  congr 1; ext v
  have := (q.f0_pos v).ne'
  field_simp
lemma Fi_mul_F : q.Fi * q.F = 1 := by
  simp only [Fi, F, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext v
  exact inv_mul_cancel₀ (q.f0_pos v).ne'
lemma F_mul_Fi : q.F * q.Fi = 1 := by
  simp only [Fi, F, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext v
  exact mul_inv_cancel₀ (q.f0_pos v).ne'

/-- The unit block `(δₐ_b)` selecting the fixed functions out of `V = [U, W]`. -/
def ea (a p : Type*) [DecidableEq a] : Matrix (a ⊕ p) a ℝ := fromRows 1 0

lemma vb_mul_ea (U : Matrix Mv a ℝ) (W : Matrix Mv p ℝ) :
    vb U W * ea a p = U := by
  rw [vb, ea, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

variable {U : Matrix Mv a ℝ} {X X' : Matrix Mx (a ⊕ p) ℝ} {W W' : Matrix Mv p ℝ}

lemma IsState.orthWU (h : q.IsState U X W) : Wᵀ * q.Hv * U = 0 := by
  have := congrArg transpose h.orthUW
  simpa [transpose_mul, Hv_transpose, Matrix.mul_assoc] using this

lemma IsState.vb_transpose_U (h : q.IsState U X W) :
    (vb U W)ᵀ * q.Hv * U = ea a p := by
  rw [vb, transpose_fromCols, fromRows_mul, fromRows_mul, h.orthU, h.orthWU, ea]

lemma IsState.U_transpose_vb (h : q.IsState U X W) :
    Uᵀ * q.Hv * vb U W = (ea a p)ᵀ := by
  have := congrArg transpose h.vb_transpose_U
  simpa [transpose_mul, Hv_transpose, Matrix.mul_assoc] using this

lemma IsState.orthV (h : q.IsState U X W) : (vb U W)ᵀ * q.Hv * vb U W = 1 := by
  rw [vb, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, h.orthU, h.orthUW, h.orthWU,
    h.orthW, fromBlocks_one]

/-! ### Reduction to the reduced distribution -/

section Algebra

variable {D : Matrix Mx Mv ℝ → Matrix Mx Mv ℝ} {τ : ℝ} {S S' : Matrix (a ⊕ p) (a ⊕ p) ℝ}

lemma pairV_eq (A : Matrix Mx Mv ℝ) (V : Matrix Mv s ℝ) :
    q.pairV A V = A * q.Fi * q.Hv * V := by
  rw [pairV, Matrix.mul_assoc A q.Fi, Fi_mul_Hv]

lemma pairXV_eq (X : Matrix Mx r ℝ) (V : Matrix Mv s ℝ) (A : Matrix Mx Mv ℝ) :
    q.pairXV X V A = Xᵀ * q.Hx * (A * q.Fi) * q.Hv * V := by
  rw [pairXV, Matrix.mul_assoc _ (A * q.Fi), Matrix.mul_assoc A q.Fi, Fi_mul_Hv,
    ← Matrix.mul_assoc]

lemma fi_pairX_eq (X : Matrix Mx r ℝ) (A : Matrix Mx Mv ℝ) :
    q.Fi * q.pairX X A = (A * q.Fi)ᵀ * q.Hx * X := by
  have : q.Fiᵀ = q.Fi := by simp [Fi]
  rw [pairX, transpose_mul, this]
  simp only [Matrix.mul_assoc]

/-- The L-update in the form `Lⁿ⁺¹ = W T + τ (1 - V Vᵀ Hᵥ) Γᵀ Hₓ X Sₚ`, `Γ = A / f₀ᵥ`. -/
lemma lNext_eq (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ)
    (V : Matrix Mv (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) (A : Matrix Mx Mv ℝ) :
    q.lNext τ X S V W A = W * ((colsP S)ᵀ * colsP S) +
      τ • ((1 - V * Vᵀ * q.Hv) * ((A * q.Fi)ᵀ * q.Hx * X) * colsP S) := by
  have h : (q.pairXV X V A)ᵀ = Vᵀ * q.Hv * ((A * q.Fi)ᵀ * q.Hx * X) := by
    rw [pairXV_eq]
    simp only [transpose_mul, Hv_transpose, Hx_transpose, transpose_transpose, Matrix.mul_assoc]
  rw [lNext, fi_pairX_eq, h, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

/-- **`Lⁿ⁺¹ ⊥ Uₐ`** (arXiv 2101.12571, Sec. 6.1, end, for eq. (16), and Sec. 6.2).  The L-update
is `⟨·,·⟩ᵥ`-orthogonal to the fixed functions, for every `S`. -/
theorem lNext_orth (h : q.IsState U X W) (A : Matrix Mx Mv ℝ) :
    Uᵀ * q.Hv * q.lNext τ X S (vb U W) W A = 0 := by
  rw [lNext_eq, Matrix.mul_add, Matrix.mul_smul]
  have h1 : Uᵀ * q.Hv * (W * ((colsP S)ᵀ * colsP S)) = 0 := by
    rw [← Matrix.mul_assoc, h.orthUW, Matrix.zero_mul]
  have h2 : Uᵀ * q.Hv * (1 - vb U W * (vb U W)ᵀ * q.Hv) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      h.U_transpose_vb, ← transpose_mul, vb_mul_ea, sub_self]
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
  simp

/-- `fⁿ` of a state. -/
def fNow (q : Grid Mx Mv) (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) : Matrix Mx Mv ℝ :=
  q.dist X S (vb U W)

/-- `f(Xⁿ⁺¹, M Sⁿ Nᵀ, Vⁿ⁺¹)`, the projected start of the S-step. -/
def fStart (q : Grid Mx Mv) (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) (X' : Matrix Mx (a ⊕ p) ℝ)
    (W' : Matrix Mv p ℝ) : Matrix Mx Mv ℝ :=
  q.dist X' (q.sStart X' X S (vb U W) (vb U W')) (vb U W')

/-- `Q₁`, acting from the right on `f`: the orthogonal projection of `f / f₀ᵥ` onto `span V'` in
the `v`-variable. -/
def projV (q : Grid Mx Mv) (V' : Matrix Mv s ℝ) : Matrix Mv Mv ℝ := q.Hu * V' * V'ᵀ * q.F

/-- **The projected start** (arXiv 2101.12571, Sec. 6.2).  The paper's
`∑ Xᵢ Sᵢⱼ Vⱼ ≈ ∑ Xₖ' Mₖᵢ Sᵢⱼ Nᵀⱼₗ Vₗ'`, as an exact identity: the start of the S-step is
`f̃ = P₁ fⁿ Q₁`. -/
theorem fStart_eq (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ)
    (W : Matrix Mv p ℝ) (X' : Matrix Mx (a ⊕ p) ℝ) (W' : Matrix Mv p ℝ) :
    q.fStart U X S W X' W' = q.projX X' * q.fNow U X S W * q.projV (vb U W') := by
  have hF : q.F * q.Hu = q.Hv := F_mul_Hu
  simp only [fStart, fNow, dist, sStart, projX, projV, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc (q.F) (q.Hu), hF]

lemma density_eq (ζ : Mv → ℝ) (f : Matrix Mx Mv ℝ) :
    q.density ζ f = f *ᵥ (q.Hu *ᵥ ζ) := by
  ext x
  simp only [density, Hu, mulVec, dotProduct, diagonal_apply, ite_mul, zero_mul]
  simp [mul_comm, mul_left_comm]

lemma density_U (U : Matrix Mv a ℝ) (b : a → ℝ) (f : Matrix Mx Mv ℝ) :
    q.density (U *ᵥ b) f = (f * q.Hu * U) *ᵥ b := by
  rw [density_eq, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

lemma density_add (ζ : Mv → ℝ) (f h : Matrix Mx Mv ℝ) :
    q.density ζ (f + h) = q.density ζ f + q.density ζ h := by
  rw [density_eq, density_eq, density_eq, add_mulVec]

lemma density_sub (ζ : Mv → ℝ) (f h : Matrix Mx Mv ℝ) :
    q.density ζ (f - h) = q.density ζ f - q.density ζ h := by
  rw [density_eq, density_eq, density_eq, sub_mulVec]

lemma density_smul (ζ : Mv → ℝ) (t : ℝ) (f : Matrix Mx Mv ℝ) :
    q.density ζ (t • f) = t • q.density ζ f := by
  rw [density_eq, density_eq, smul_mulVec]

lemma dist_density (hs : q.IsState U X W) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (b : a → ℝ) :
    q.density (U *ᵥ b) (q.dist X S (vb U W)) = (X * S * ea a p) *ᵥ b := by
  rw [density_U, dist]
  have : X * S * (vb U W)ᵀ * q.F * q.Hu * U = X * S * ((vb U W)ᵀ * q.Hv * U) := by
    rw [← F_mul_Hu]
    simp only [Matrix.mul_assoc]
  rw [this, hs.vb_transpose_U]

lemma projX_mul_self {X' : Matrix Mx r ℝ} (h : X'ᵀ * q.Hx * X' = 1) {K : Matrix Mx s ℝ}
    {R : Matrix r s ℝ} (hK : K = X' * R) : q.projX X' * K = K := by
  rw [hK, projX]
  calc X' * X'ᵀ * q.Hx * (X' * R) = X' * (X'ᵀ * q.Hx * X') * R := by
        simp only [Matrix.mul_assoc]
    _ = X' * R := by rw [h, Matrix.mul_one]

/-- The first block of the S-update: `X' S' e = P₁ (X S e + τ Ã Hᵤ U)`. -/
lemma IsStep.mul_ea (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W') :
    X' * S' * ea a p = q.projX X' * (X * S * ea a p) +
      τ • (q.projX X' * (D (q.fStart U X S W X' W') * q.Hu * U)) := by
  have hV' : (X'ᵀ * q.Hx * X) * S * ((vb U W)ᵀ * q.Hv * vb U W') * ea a p
      = (X'ᵀ * q.Hx * X) * S * ea a p := by
    rw [Matrix.mul_assoc _ _ (ea a p), Matrix.mul_assoc _ _ (ea a p), vb_mul_ea, hs.vb_transpose_U]
  rw [h.sStep, sNext, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  · rw [sStart, Matrix.mul_assoc X', hV', projX]
    simp only [Matrix.mul_assoc]
  · congr 1
    simp only [pairXV, projX, Matrix.mul_assoc]
    rw [vb_mul_ea]
    rfl

/-- `K¹ e = X S e + τ A Hᵤ U` is captured by `P₁`. -/
lemma IsStep.proj_kNext (h : q.IsStep D τ U X S W X' S' W') :
    q.projX X' * (X * S * ea a p) + τ • (q.projX X' * (D (q.fNow U X S W) * q.Hu * U)) =
      X * S * ea a p + τ • (D (q.fNow U X S W) * q.Hu * U) := by
  obtain ⟨R, hR⟩ := h.qrK
  have hcap := projX_mul_self h.state.orthX hR
  have := congrArg (· * ea a p) hcap
  simp only [kNext, pairV] at this
  simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    vb_mul_ea] at this
  simp only [Matrix.mul_assoc, fNow]
  exact this

/-- The matrix form of the continuity equation with defect. -/
lemma IsStep.moment_mat (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W') :
    X' * S' * ea a p = X * S * ea a p + τ • (D (q.fNow U X S W) * q.Hu * U) +
      τ • (q.projX X' * ((D (q.fStart U X S W X' W') - D (q.fNow U X S W)) * q.Hu * U)) := by
  rw [h.mul_ea hs, ← h.proj_kNext, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, smul_sub]
  abel

/-- **The discrete continuity equation of the integrator of Sec. 6.2, with its exact defect**
(arXiv 2101.12571, Sec. 6.2).  For every velocity function `ζ = ∑ₐ bₐ Uₐ` in the span of the fixed
functions (mass: `ζ = 1`, momentum: `ζ = v`) and `ρ_ζ[f] = ∫ ζ f dv`,
`ρ_ζ[fⁿ⁺¹] = ρ_ζ[fⁿ] + τ ρ_ζ[D[fⁿ]] + τ P₁ (ρ_ζ[D[f̃]] - ρ_ζ[D[fⁿ]])`,
where `f̃ = f(Xⁿ⁺¹, M Sⁿ Nᵀ, Vⁿ⁺¹)` and `P₁` is the `⟨·,·⟩ₓ`-orthogonal projector onto `X̄ⁿ⁺¹`.
The first two terms on the right are the discrete continuity equation of the conservative Euler
scheme of Sec. 6.1, so the last term is exactly what the paper means by "conservation can be lost";
`S` is arbitrary.  The paper states no formula. -/
theorem IsStep.continuity (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (b : a → ℝ) :
    q.density (U *ᵥ b) (q.fNow U X' S' W') =
      q.density (U *ᵥ b) (q.fNow U X S W) + τ • q.density (U *ᵥ b) (D (q.fNow U X S W)) +
        τ • (q.projX X' *ᵥ (q.density (U *ᵥ b) (D (q.fStart U X S W X' W')) -
          q.density (U *ᵥ b) (D (q.fNow U X S W)))) := by
  have e1 := dist_density h.state S' b
  have e2 := dist_density hs S b
  simp only [fNow]
  rw [e1, e2, ← density_sub]
  simp only [density_U]
  have := congrArg (· *ᵥ b) (h.moment_mat hs)
  simp only [add_mulVec, smul_mulVec, fNow] at this
  rw [this, mulVec_mulVec]

lemma ipx_eq (u w : Mx → ℝ) : q.ipx u w = u ⬝ᵥ (q.Hx *ᵥ w) := by
  simp only [ipx, dotProduct, Hx, mulVec_diagonal]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma ipx_comm (u w : Mx → ℝ) : q.ipx u w = q.ipx w u :=
  Finset.sum_congr rfl fun x _ => by ring

lemma ipx_add_right (u w z : Mx → ℝ) : q.ipx u (w + z) = q.ipx u w + q.ipx u z := by
  simp only [ipx, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma ipx_sub_right (u w z : Mx → ℝ) : q.ipx u (w - z) = q.ipx u w - q.ipx u z := by
  simp only [ipx, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma ipx_sub_left (u w z : Mx → ℝ) : q.ipx (u - w) z = q.ipx u z - q.ipx w z := by
  simp only [ipx, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma ipx_smul_right (t : ℝ) (u w : Mx → ℝ) : q.ipx u (t • w) = t * q.ipx u w := by
  simp only [ipx, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `P₁` is `(·,·)ₓ`-symmetric. -/
lemma ipx_projX (X' : Matrix Mx r ℝ) (u w : Mx → ℝ) :
    q.ipx u (q.projX X' *ᵥ w) = q.ipx (q.projX X' *ᵥ u) w := by
  have hs : q.Hx * q.projX X' = (q.projX X')ᵀ * q.Hx := by
    simp only [projX, transpose_mul, transpose_transpose, Hx_transpose, Matrix.mul_assoc]
  rw [ipx_eq, ipx_eq, mulVec_mulVec, hs, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **Exact change of a global invariant per step** (arXiv 2101.12571, Sec. 6.2).  For `c` a
function of `x` and `ζ = ∑ₐ bₐ Uₐ`, if the right-hand side satisfies `∫∫ c ζ D[f] = 0` for all `f`
(for `c = 1`, `ζ = 1, v`: mass and momentum of the Vlasov equation), then
`I[fⁿ⁺¹] - I[fⁿ] = -τ ((1 - P₁) c, ρ_ζ[D[f̃]] - ρ_ζ[D[fⁿ]])ₓ`.
The invariant is lost through the part of `c` outside `X̄ⁿ⁺¹`, tested against the change of the
flux caused by the projected start. -/
theorem IsStep.charge_sub (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (b : a → ℝ) {c : Mx → ℝ} (hD : ∀ f, q.charge c (U *ᵥ b) (D f) = 0) :
    q.charge c (U *ᵥ b) (q.fNow U X' S' W') - q.charge c (U *ᵥ b) (q.fNow U X S W) =
      -τ * q.ipx (c - q.projX X' *ᵥ c) (q.density (U *ᵥ b) (D (q.fStart U X S W X' W')) -
        q.density (U *ᵥ b) (D (q.fNow U X S W))) := by
  have h1 := hD (q.fNow U X S W)
  have h2 := hD (q.fStart U X S W X' W')
  simp only [charge] at h1 h2 ⊢
  rw [h.continuity hs, ipx_add_right, ipx_add_right, ipx_smul_right, ipx_smul_right, h1,
    ipx_projX, ipx_sub_left, ipx_sub_right, ipx_sub_right, h1, h2]
  ring

/-- **No loss if `c ∈ X̄ⁿ⁺¹`** (arXiv 2101.12571, Sec. 6.2).  If `c ∈ X̄ⁿ⁺¹`, the invariant
`∫∫ c ζ f` is conserved exactly by the step: for the mass and momentum (`c = 1`), the loss is
entirely caused by `1 ∉ X̄ⁿ⁺¹`.  The paper does not say this. -/
theorem IsStep.charge_eq_of_mem (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (b : a → ℝ) {c : Mx → ℝ} (hD : ∀ f, q.charge c (U *ᵥ b) (D f) = 0)
    (hc : ∃ y, c = X' *ᵥ y) :
    q.charge c (U *ᵥ b) (q.fNow U X' S' W') = q.charge c (U *ᵥ b) (q.fNow U X S W) := by
  obtain ⟨y, rfl⟩ := hc
  have hP : q.projX X' *ᵥ (X' *ᵥ y) = X' *ᵥ y := by
    rw [mulVec_mulVec, projX_mul_self h.state.orthX (R := 1) (by simp)]
  have := h.charge_sub hs b hD
  rw [hP, sub_self] at this
  have h0 : q.ipx 0 (q.density (U *ᵥ b) (D (q.fStart U X S W (X') W')) -
      q.density (U *ᵥ b) (D (q.fNow U X S W))) = 0 := by simp [ipx]
  rw [h0, mul_zero] at this
  exact sub_eq_zero.mp this

/-- **Exact projection** (arXiv 2101.12571, Sec. 6.2).  If the old spaces lie in the new ones
(`P₁ Xⁿ = Xⁿ`, `Vⁿ⁺¹` captures `Vⁿ`), the projected start is exact: `f̃ = fⁿ`. -/
theorem fStart_eq_of_nested (hX : q.projX X' * X = X)
    (hV : vb U W' * (vb U W')ᵀ * q.Hv * vb U W = vb U W) :
    q.fStart U X S W X' W' = q.fNow U X S W := by
  have h1 : (vb U W)ᵀ * q.Hv * vb U W' * (vb U W')ᵀ = (vb U W)ᵀ := by
    have := congrArg transpose hV
    rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, Hv_transpose] at this
    simpa only [Matrix.mul_assoc] using this
  have h2 : X' * (X'ᵀ * q.Hx * X) = X := by
    calc X' * (X'ᵀ * q.Hx * X) = q.projX X' * X := by simp only [projX, Matrix.mul_assoc]
      _ = X := hX
  calc q.fStart U X S W X' W'
      = (X' * (X'ᵀ * q.Hx * X)) * S * ((vb U W)ᵀ * q.Hv * vb U W' * (vb U W')ᵀ) * q.F := by
        simp only [fStart, dist, sStart, Matrix.mul_assoc]
    _ = q.fNow U X S W := by rw [h1, h2]; rfl

/-- **The reason given in Sec. 6.2: if the projection is exact, nothing is lost.**  If the old
spaces lie in the new ones, the integrator satisfies the discrete continuity equation of Sec. 6.1
exactly (arXiv 2101.12571, Sec. 6.1 and 6.2). -/
theorem IsStep.continuity_of_nested (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (hX : q.projX X' * X = X) (hV : vb U W' * (vb U W')ᵀ * q.Hv * vb U W = vb U W) (b : a → ℝ) :
    q.density (U *ᵥ b) (q.fNow U X' S' W') =
      q.density (U *ᵥ b) (q.fNow U X S W) + τ • q.density (U *ᵥ b) (D (q.fNow U X S W)) := by
  rw [h.continuity hs, fStart_eq_of_nested hX hV, sub_self, mulVec_zero, smul_zero, add_zero]

end Algebra

end Grid

/-! ### Two estimates for Frobenius projections -/

section Core

open scoped LeanDLRA.Frobenius

variable {m n k l c d e : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [Fintype c]
  [Fintype d] [Fintype e] [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]
  [DecidableEq c] [DecidableEq d] [DecidableEq e]

/-- Frobenius lemma for the K-update of arXiv 2101.12571, Sec. 6.2: if `X'` captures `C + τ G V`,
then it captures `C Vᵀ` up to `|τ| ‖G‖`. -/
theorem core_left {X' : Matrix m k ℝ} (hX' : X'ᵀ * X' = 1) {V : Matrix n l ℝ} (hV : Vᵀ * V = 1)
    (C : Matrix m l ℝ) (G : Matrix m n ℝ) {τ : ℝ} {R : Matrix k l ℝ}
    (hK : C + τ • (G * V) = X' * R) :
    ‖C * Vᵀ - leftProj X' (C * Vᵀ)‖ ≤ |τ| * ‖G‖ := by
  have hP : X' * X'ᵀ * (C + τ • (G * V)) = C + τ • (G * V) :=
    mul_transpose_mul_eq_of_eq_mul hX' hK
  have hid : C * Vᵀ - leftProj X' (C * Vᵀ) =
      -τ • (G * V * Vᵀ - leftProj X' (G * V * Vᵀ)) := by
    rw [Matrix.mul_add, Matrix.mul_smul] at hP
    simp only [leftProj_apply]
    have h1 : X' * X'ᵀ * (C * Vᵀ) = (X' * X'ᵀ * C) * Vᵀ := by simp only [Matrix.mul_assoc]
    have h2 : X' * X'ᵀ * (G * V * Vᵀ) = (X' * X'ᵀ * (G * V)) * Vᵀ := by
      simp only [Matrix.mul_assoc]
    rw [h1, h2]
    have h3 : X' * X'ᵀ * C = C + τ • (G * V) - τ • (X' * X'ᵀ * (G * V)) := by
      rw [← hP]; abel
    rw [h3]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, smul_sub, neg_smul]
    abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine ((isOrthProj_leftProj hX').norm_sub_le _).trans ?_
  have := (isOrthProj_rightProj (m := m) hV).norm_le G
  rwa [rightProj_apply] at this

/-- **The robust key estimate of the L-update** (for arXiv 2101.12571, Sec. 6.2).  With
`E = 1 - V' V'ᵀ`, if `E W Sₚᵀ Sₚ = C' Sₚ` then `‖E W Sₚᵀ‖ ≤ ‖C'‖`: no inverse of `Sₚ`.  The
matrices `E W Sₚᵀ` and `E W Sₚᵀ - C'` are orthogonal since `(E W Sₚᵀ - C') Sₚ = 0`. -/
theorem norm_mul_transpose_le_of_mul_eq {M : Matrix n c ℝ} {Sp : Matrix e c ℝ}
    {C' : Matrix n e ℝ} (h : M * (Spᵀ * Sp) = C' * Sp) :
    ‖M * Spᵀ‖ ≤ ‖C'‖ := by
  set A := M * Spᵀ with hA
  have hz : (A - C') * Sp = 0 := by
    rw [Matrix.sub_mul, hA, Matrix.mul_assoc, h, sub_self]
  have horth : ⟪A, A - C'⟫ = 0 := by
    rw [hA, Frobenius.inner_mul_right, transpose_transpose, ← hA, hz]
    simp
  have hsq : ‖C'‖ ^ 2 = ‖A‖ ^ 2 + ‖A - C'‖ ^ 2 := by
    have e1 : C' = A - (A - C') := by abel
    conv_lhs => rw [e1]
    rw [norm_sub_sq_real, horth]
    ring
  have : ‖A‖ ^ 2 ≤ ‖C'‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖A - C'‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

/-- **The L-update captures `fⁿ` up to `O(τ)`, for every `S`** (arXiv 2101.12571, Sec. 6.2).
This is the Frobenius form of the estimate: `Lⁿ⁺¹ = W Sₚᵀ Sₚ + τ (1 - V Vᵀ) Gᵀ X Sₚ = W' R` implies
`‖Y - Y V' V'ᵀ‖ ≤ |τ| ‖G‖` for `Y = X S Vᵀ`, without any assumption on `S`. -/
theorem core_right {a p : Type*} [Fintype a] [Fintype p] [DecidableEq a] [DecidableEq p]
    {X : Matrix m (a ⊕ p) ℝ} (hX : Xᵀ * X = 1) {U : Matrix n a ℝ} {W W' : Matrix n p ℝ}
    (hV : (fromCols U W)ᵀ * fromCols U W = 1) (hV' : (fromCols U W')ᵀ * fromCols U W' = 1)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (G : Matrix m n ℝ) {τ : ℝ} {R : Matrix p p ℝ}
    (hL : W * ((colsP S)ᵀ * colsP S) +
      τ • ((1 - fromCols U W * (fromCols U W)ᵀ) * (Gᵀ * X) * colsP S) = W' * R) :
    ‖X * S * (fromCols U W)ᵀ - rightProj (fromCols U W') (X * S * (fromCols U W)ᵀ)‖ ≤
      |τ| * ‖G‖ := by
  set V' := fromCols U W' with hV'def
  set V := fromCols U W with hVdef
  set E : Matrix n n ℝ := 1 - V' * V'ᵀ with hE
  have hEsymm : Eᵀ = E := by
    simp [hE, transpose_sub, transpose_mul]
  have hEV' : E * V' = 0 := by
    rw [hE, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV', Matrix.mul_one, sub_self]
  have hEU : E * U = 0 ∧ E * W' = 0 := by
    have := hEV'
    rw [hV'def, mul_fromCols] at this
    have h0 : (0 : Matrix n (a ⊕ p) ℝ) = fromCols 0 0 := by
      ext i j; cases j <;> rfl
    rw [h0] at this
    exact Matrix.fromCols_inj.eq_iff.mp this
  have hUE : Uᵀ * E = 0 := by
    have := congrArg transpose hEU.1
    simpa [transpose_mul, hEsymm] using this
  have hS : S = fromCols S.toCols₁ (colsP S) := (fromCols_toCols S).symm
  -- the defect is `X Sₚ Wᵀ E`
  have hdef : X * S * Vᵀ - rightProj V' (X * S * Vᵀ) = X * (E * W * (colsP S)ᵀ)ᵀ := by
    have h1 : X * S * Vᵀ - rightProj V' (X * S * Vᵀ) = X * S * (Vᵀ * E) := by
      rw [rightProj_apply, hE]
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    have h2 : S * (Vᵀ * E) = colsP S * (E * W)ᵀ := by
      rw [hVdef, transpose_fromCols, fromRows_mul]
      conv_lhs => rw [hS]
      rw [fromCols_mul_fromRows, hUE, Matrix.mul_zero, zero_add, transpose_mul, hEsymm]
    rw [h1, Matrix.mul_assoc, h2, transpose_mul (E * W) (colsP S)ᵀ, transpose_transpose]
  have hkey : (E * W) * ((colsP S)ᵀ * colsP S) =
      (-τ • (E * ((1 - V * Vᵀ) * (Gᵀ * X)))) * colsP S := by
    have := congrArg (E * ·) hL
    simp only [Matrix.mul_add, Matrix.mul_smul] at this
    rw [← Matrix.mul_assoc E W', hEU.2, Matrix.zero_mul] at this
    rw [neg_smul, Matrix.neg_mul, Matrix.smul_mul, eq_neg_iff_add_eq_zero, Matrix.mul_assoc E W]
    rw [Matrix.mul_assoc E (_ * _)]
    exact this
  rw [hdef, Frobenius.norm_mul_of_orthonormal hX, Frobenius.norm_transpose]
  refine (norm_mul_transpose_le_of_mul_eq hkey).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : ‖E * ((1 - V * Vᵀ) * (Gᵀ * X))‖ ≤ ‖(1 - V * Vᵀ) * (Gᵀ * X)‖ := by
    have := (isOrthProj_leftProj hV').norm_sub_le ((1 - V * Vᵀ) * (Gᵀ * X))
    simpa [leftProj_apply, hE, Matrix.sub_mul, Matrix.one_mul] using this
  have h2 : ‖(1 - V * Vᵀ) * (Gᵀ * X)‖ ≤ ‖Gᵀ * X‖ := by
    have := (isOrthProj_leftProj hV).norm_sub_le (Gᵀ * X)
    simpa [leftProj_apply, Matrix.sub_mul, Matrix.one_mul] using this
  have h3 : ‖Gᵀ * X‖ ≤ ‖G‖ := by
    have := norm_mul_le_of_orthonormal hX Gᵀ
    rwa [Frobenius.norm_transpose] at this
  exact h1.trans (h2.trans h3)

end Core

/-! ### The weighted norm -/

namespace Grid

/-- The norm of `L²(Ω, f₀)` of the reduced function `f / f₀ᵥ`:
`‖f‖² = ∫∫ f² / f₀ᵥ = ∫∫ f₀ᵥ (f / f₀ᵥ)²`. -/
noncomputable def fnorm (q : Grid Mx Mv) (f : Matrix Mx Mv ℝ) : ℝ :=
  √(∑ x, ∑ v, q.wx x * q.wv v * f x v ^ 2 / q.f0 v)

/-- The norm of `L²(Ωₓ)`. -/
noncomputable def xnorm (q : Grid Mx Mv) (u : Mx → ℝ) : ℝ := √(∑ x, q.wx x * u x ^ 2)

/-- The norm of `L²(Ωᵥ, f₀ᵥ)`. -/
noncomputable def vnorm (q : Grid Mx Mv) (ζ : Mv → ℝ) : ℝ := √(∑ v, q.wv v * q.f0 v * ζ v ^ 2)

variable (q : Grid Mx Mv)

/-- `√wₓ` as a diagonal matrix. -/
noncomputable def Sx : Matrix Mx Mx ℝ := diagonal fun x => √(q.wx x)

/-- `√(wᵥ f₀ᵥ)` as a diagonal matrix. -/
noncomputable def Sv : Matrix Mv Mv ℝ := diagonal fun v => √(q.wv v * q.f0 v)

/-- `√(wᵥ / f₀ᵥ)` as a diagonal matrix. -/
noncomputable def Rv : Matrix Mv Mv ℝ := diagonal fun v => √(q.wv v / q.f0 v)

/-- The isometry of the weighted space onto Frobenius matrices. -/
noncomputable def iota (f : Matrix Mx Mv ℝ) : Matrix Mx Mv ℝ := q.Sx * f * q.Rv

variable {q}

lemma Sx_transpose : q.Sxᵀ = q.Sx := by simp [Sx]
lemma Sv_transpose : q.Svᵀ = q.Sv := by simp [Sv]
lemma Rv_transpose : q.Rvᵀ = q.Rv := by simp [Rv]

lemma Sx_mul_Sx : q.Sx * q.Sx = q.Hx := by
  simp only [Sx, Hx, diagonal_mul_diagonal]
  congr 1; ext x
  exact Real.mul_self_sqrt (q.wx_pos x).le

lemma Sv_mul_Sv : q.Sv * q.Sv = q.Hv := by
  simp only [Sv, Hv, diagonal_mul_diagonal]
  congr 1; ext v
  exact Real.mul_self_sqrt (mul_pos (q.wv_pos v) (q.f0_pos v)).le

lemma F_mul_Rv : q.F * q.Rv = q.Sv := by
  simp only [F, Rv, Sv, diagonal_mul_diagonal]
  congr 1; ext v
  have h1 := q.f0_pos v
  have h2 := q.wv_pos v
  rw [← Real.sqrt_sq h1.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1.le]
  congr 1
  field_simp

lemma Rv_mul_Sv : q.Rv * q.Sv = q.Hu := by
  simp only [Hu, Rv, Sv, diagonal_mul_diagonal]
  congr 1; ext v
  have h1 := q.f0_pos v
  have h2 := q.wv_pos v
  rw [← Real.sqrt_mul (by positivity)]
  have : q.wv v / q.f0 v * (q.wv v * q.f0 v) = q.wv v ^ 2 := by field_simp
  rw [this, Real.sqrt_sq h2.le]

lemma Rv_mul_F : q.Rv * q.F = q.Sv := by
  rw [← F_mul_Rv]
  simp only [F, Rv, diagonal_mul_diagonal, mul_comm]

lemma Sv_mul_Fi : q.Sv * q.Fi = q.Rv := by
  rw [← Rv_mul_F, Matrix.mul_assoc, F_mul_Fi, Matrix.mul_one]

section Weighted

open scoped LeanDLRA.Frobenius

variable {U : Matrix Mv a ℝ} {X X' : Matrix Mx (a ⊕ p) ℝ} {W W' : Matrix Mv p ℝ}
  {D : Matrix Mx Mv ℝ → Matrix Mx Mv ℝ} {τ : ℝ} {S S' : Matrix (a ⊕ p) (a ⊕ p) ℝ}

lemma iota_sub (f h : Matrix Mx Mv ℝ) : q.iota (f - h) = q.iota f - q.iota h := by
  simp only [iota, Matrix.mul_sub, Matrix.sub_mul]

lemma iota_apply (f : Matrix Mx Mv ℝ) (x : Mx) (v : Mv) :
    q.iota f x v = √(q.wx x) * f x v * √(q.wv v / q.f0 v) := by
  simp only [iota, Sx, Rv, mul_diagonal, diagonal_mul]

lemma fnorm_eq (f : Matrix Mx Mv ℝ) : q.fnorm f = ‖q.iota f‖ := by
  rw [Frobenius.norm_def, fnorm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ => ?_
  rw [iota_apply, mul_pow, mul_pow, Real.sq_sqrt (q.wx_pos x).le,
    Real.sq_sqrt (div_pos (q.wv_pos v) (q.f0_pos v)).le]
  ring

lemma fnorm_nonneg (f : Matrix Mx Mv ℝ) : 0 ≤ q.fnorm f := Real.sqrt_nonneg _

lemma iota_dist (X : Matrix Mx r ℝ) (S : Matrix r s ℝ) (V : Matrix Mv s ℝ) :
    q.iota (q.dist X S V) = (q.Sx * X) * S * (q.Sv * V)ᵀ := by
  rw [iota, dist, transpose_mul, Sv_transpose]
  calc q.Sx * (X * S * Vᵀ * q.F) * q.Rv = q.Sx * X * S * Vᵀ * (q.F * q.Rv) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [F_mul_Rv]; simp only [Matrix.mul_assoc]

lemma tx_mul (A : Matrix Mx r ℝ) (B : Matrix Mx s ℝ) :
    (q.Sx * A)ᵀ * (q.Sx * B) = Aᵀ * q.Hx * B := by
  rw [transpose_mul, Sx_transpose, ← Sx_mul_Sx]
  simp only [Matrix.mul_assoc]

lemma tv_mul (A : Matrix Mv r ℝ) (B : Matrix Mv s ℝ) :
    (q.Sv * A)ᵀ * (q.Sv * B) = Aᵀ * q.Hv * B := by
  rw [transpose_mul, Sv_transpose, ← Sv_mul_Sv]
  simp only [Matrix.mul_assoc]

lemma Sx_kNext (τ : ℝ) (X : Matrix Mx r ℝ) (S : Matrix r s ℝ) (V : Matrix Mv s ℝ)
    (A : Matrix Mx Mv ℝ) :
    q.Sx * q.kNext τ X S V A = (q.Sx * X) * S + τ • (q.iota A * (q.Sv * V)) := by
  have : q.iota A * (q.Sv * V) = q.Sx * (A * q.Hu * V) := by
    rw [iota, ← Rv_mul_Sv]
    simp only [Matrix.mul_assoc]
  rw [kNext, Matrix.mul_add, Matrix.mul_smul, pairV, this, Matrix.mul_assoc q.Sx X S]

lemma Sv_lNext (τ : ℝ) (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ)
    (V : Matrix Mv (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) (A : Matrix Mx Mv ℝ) :
    q.Sv * q.lNext τ X S V W A = (q.Sv * W) * ((colsP S)ᵀ * colsP S) +
      τ • ((1 - (q.Sv * V) * (q.Sv * V)ᵀ) * ((q.iota A)ᵀ * (q.Sx * X)) * colsP S) := by
  have h1 : q.Sv * (1 - V * Vᵀ * q.Hv) = (1 - (q.Sv * V) * (q.Sv * V)ᵀ) * q.Sv := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, transpose_mul,
      Sv_transpose, ← Sv_mul_Sv]
    simp only [Matrix.mul_assoc]
  have h2 : q.Sv * ((A * q.Fi)ᵀ * q.Hx * X) = (q.iota A)ᵀ * (q.Sx * X) := by
    have hFi : q.Fiᵀ = q.Fi := by simp [Fi]
    rw [iota, transpose_mul, transpose_mul, transpose_mul, hFi, Sx_transpose, Rv_transpose,
      ← Sv_mul_Fi, ← Sx_mul_Sx]
    simp only [Matrix.mul_assoc]
  rw [lNext_eq, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc q.Sv W]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc _ q.Sv, h2]

lemma IsState.tx (h : q.IsState U X W) : (q.Sx * X)ᵀ * (q.Sx * X) = 1 := by
  rw [tx_mul, h.orthX]

lemma IsState.tV (h : q.IsState U X W) :
    (fromCols (q.Sv * U) (q.Sv * W))ᵀ * fromCols (q.Sv * U) (q.Sv * W) = 1 := by
  rw [← mul_fromCols, tv_mul]
  exact h.orthV

lemma iota_fStart (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ) (S : Matrix (a ⊕ p) (a ⊕ p) ℝ)
    (W : Matrix Mv p ℝ) (X' : Matrix Mx (a ⊕ p) ℝ) (W' : Matrix Mv p ℝ) :
    q.iota (q.fStart U X S W X' W') =
      leftProj (q.Sx * X') (rightProj (q.Sv * vb U W') (q.iota (q.fNow U X S W))) := by
  rw [fStart, fNow, iota_dist, iota_dist, sStart, ← tx_mul, ← tv_mul, rightProj_apply,
    leftProj_apply]
  simp only [Matrix.mul_assoc]

/-- **The projected start of the S-step is `O(τ)` from `fⁿ`, for every `S`** (arXiv 2101.12571,
Sec. 6.2).  This makes the paper's `∑ Xᵢ Sᵢⱼ Vⱼ ≈ ∑ Xₖ' Mₖᵢ Sᵢⱼ Nᵀⱼₗ Vₗ'` precise:
`‖f̃ - fⁿ‖ ≤ 2 |τ| ‖D[fⁿ]‖` in `L²(Ω, f₀)` (for the reduced functions), with a constant independent
of the singular values of `S`, and `S` may be singular. -/
theorem IsStep.start_error_le (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W') :
    q.fnorm (q.fStart U X S W X' W' - q.fNow U X S W) ≤
      2 * |τ| * q.fnorm (D (q.fNow U X S W)) := by
  rw [fnorm_eq, fnorm_eq, iota_sub, iota_fStart]
  set Y := q.iota (q.fNow U X S W) with hY
  set G := q.iota (D (q.fNow U X S W)) with hG
  have hX' := h.state.tx
  have hV' := h.state.tV
  rw [← mul_fromCols] at hV'
  have hYeq : Y = (q.Sx * X * S) * (q.Sv * vb U W)ᵀ := iota_dist _ _ _
  have hleft : ‖Y - leftProj (q.Sx * X') Y‖ ≤ |τ| * ‖G‖ := by
    obtain ⟨R, hR⟩ := h.qrK
    have hK : q.Sx * X * S + τ • (G * (q.Sv * vb U W)) = (q.Sx * X') * R := by
      calc q.Sx * X * S + τ • (G * (q.Sv * vb U W))
          = q.Sx * q.kNext τ X S (vb U W) (D (q.dist X S (vb U W))) := (Sx_kNext _ _ _ _ _).symm
        _ = q.Sx * (X' * R) := by rw [hR]
        _ = _ := (Matrix.mul_assoc _ _ _).symm
    rw [hYeq]
    have hV := hs.tV
    rw [← mul_fromCols] at hV
    exact core_left hX' hV _ _ hK
  have hright : ‖Y - rightProj (q.Sv * vb U W') Y‖ ≤ |τ| * ‖G‖ := by
    obtain ⟨R, hR⟩ := h.qrL
    have hL : (q.Sv * W) * ((colsP S)ᵀ * colsP S) + τ • ((1 - (q.Sv * vb U W) * (q.Sv * vb U W)ᵀ) *
        (Gᵀ * (q.Sx * X)) * colsP S) = (q.Sv * W') * R := by
      calc (q.Sv * W) * ((colsP S)ᵀ * colsP S) + τ • ((1 - (q.Sv * vb U W) * (q.Sv * vb U W)ᵀ) *
            (Gᵀ * (q.Sx * X)) * colsP S)
          = q.Sv * q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W))) :=
            (Sv_lNext _ _ _ _ _ _).symm
        _ = q.Sv * (W' * R) := by rw [hR]
        _ = _ := (Matrix.mul_assoc _ _ _).symm
    have e : q.Sv * vb U W = fromCols (q.Sv * U) (q.Sv * W) := mul_fromCols _ _ _
    have e' : q.Sv * vb U W' = fromCols (q.Sv * U) (q.Sv * W') := mul_fromCols _ _ _
    have hYeq' : Y = q.Sx * X * S * (fromCols (q.Sv * U) (q.Sv * W))ᵀ := by rw [hYeq, e]
    rw [e] at hL
    rw [hYeq', e']
    exact core_right hs.tx hs.tV h.state.tV S G hL
  have hP := isOrthProj_leftProj (n := Mv) hX'
  have hsplit : leftProj (q.Sx * X') (rightProj (q.Sv * vb U W') Y) - Y =
      -(Y - leftProj (q.Sx * X') Y) -
        leftProj (q.Sx * X') (Y - rightProj (q.Sv * vb U W') Y) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc _ ≤ ‖Y - leftProj (q.Sx * X') Y‖ +
        ‖leftProj (q.Sx * X') (Y - rightProj (q.Sv * vb U W') Y)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ |τ| * ‖G‖ + |τ| * ‖G‖ := add_le_add hleft ((hP.norm_le _).trans hright)
    _ = _ := by ring

/-- The Cauchy-Schwarz inequality `|∫∫ u ζ A| ≤ ‖u‖ ‖ζ‖ ‖A‖`. -/
lemma abs_ipx_density_le (u : Mx → ℝ) (ζ : Mv → ℝ) (A : Matrix Mx Mv ℝ) :
    |q.ipx u (q.density ζ A)| ≤ q.xnorm u * q.vnorm ζ * q.fnorm A := by
  set T : Matrix Mx Mv ℝ := Matrix.of fun x v => √(q.wx x) * u x * (√(q.wv v * q.f0 v) * ζ v)
    with hT
  have h1 : q.ipx u (q.density ζ A) = ⟪T, q.iota A⟫ := by
    rw [Frobenius.inner_def, ipx]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [density, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hw := q.wv_pos v
    have hf := q.f0_pos v
    have hx := q.wx_pos x
    have e : √(q.wv v * q.f0 v) * √(q.wv v / q.f0 v) = q.wv v := by
      rw [← Real.sqrt_mul (by positivity)]
      have : q.wv v * q.f0 v * (q.wv v / q.f0 v) = q.wv v ^ 2 := by field_simp
      rw [this, Real.sqrt_sq hw.le]
    rw [iota_apply, hT, Matrix.of_apply]
    calc q.wx x * u x * (q.wv v * ζ v * A x v)
        = (√(q.wx x) * √(q.wx x)) * u x * ((√(q.wv v * q.f0 v) * √(q.wv v / q.f0 v)) *
            ζ v * A x v) := by rw [Real.mul_self_sqrt hx.le, e]
      _ = _ := by ring
  have h2 : ‖T‖ = q.xnorm u * q.vnorm ζ := by
    rw [Frobenius.norm_def, xnorm, vnorm, ← Real.sqrt_mul
      (Finset.sum_nonneg fun x _ => mul_nonneg (q.wx_pos x).le (sq_nonneg _)), Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hT, Matrix.of_apply, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (q.wx_pos x).le, Real.sq_sqrt (mul_pos (q.wv_pos v) (q.f0_pos v)).le]
  rw [h1, fnorm_eq, ← h2]
  exact abs_real_inner_le_norm _ _

lemma xnorm_sq (u : Mx → ℝ) : q.xnorm u ^ 2 = q.ipx u u := by
  rw [xnorm, Real.sq_sqrt (Finset.sum_nonneg fun x _ => mul_nonneg (q.wx_pos x).le (sq_nonneg _)),
    ipx]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma ipx_sub_left' (u w z : Mx → ℝ) : q.ipx u (w - z) = q.ipx u w - q.ipx u z :=
  ipx_sub_right u w z

/-- `1 - P₁` does not increase the norm. -/
lemma xnorm_sub_projX_le (hX' : X'ᵀ * q.Hx * X' = 1) (c : Mx → ℝ) :
    q.xnorm (c - q.projX X' *ᵥ c) ≤ q.xnorm c := by
  have hPP : q.projX X' *ᵥ (q.projX X' *ᵥ c) = q.projX X' *ᵥ c := by
    rw [mulVec_mulVec, projX_mul_self hX' (K := q.projX X') (R := X'ᵀ * q.Hx)
      (by simp only [projX, Matrix.mul_assoc])]
  have hsq : q.xnorm (c - q.projX X' *ᵥ c) ^ 2 + q.xnorm (q.projX X' *ᵥ c) ^ 2 = q.xnorm c ^ 2 := by
    simp only [xnorm_sq]
    rw [ipx_sub_left, ipx_sub_right, ipx_sub_right, ipx_comm (q.projX X' *ᵥ c) c,
      ipx_comm (q.projX X' *ᵥ c) (q.projX X' *ᵥ c)]
    have : q.ipx (q.projX X' *ᵥ c) (q.projX X' *ᵥ c) = q.ipx c (q.projX X' *ᵥ c) := by
      rw [← ipx_projX, hPP]
    rw [this]
    ring
  have hle : q.xnorm (c - q.projX X' *ᵥ c) ^ 2 ≤ q.xnorm c ^ 2 := by
    nlinarith [sq_nonneg (q.xnorm (q.projX X' *ᵥ c))]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hle

/-- **Conservation is lost only at second order per step, uniformly in `S`** (arXiv 2101.12571,
Sec. 6.2 and Sec. 7.3).  Sec. 7.3 reports that the conservation error is "dominated by the time
integration error"; here this is a theorem.  If `D` conserves `∫∫ c ζ f` and satisfies the
Lipschitz bound `‖D[f̃] - D[fⁿ]‖ ≤ L ‖f̃ - fⁿ‖` in `L²(Ω, f₀)` between the two states it is
evaluated at, then `|I[fⁿ⁺¹] - I[fⁿ]| ≤ 2 L τ² ‖c‖ ‖ζ‖ ‖D[fⁿ]‖`, without any assumption on `S`.
Such a bound needs a space discretization, which is the setting here. -/
theorem IsStep.charge_defect_le (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (b : a → ℝ) {c : Mx → ℝ} (hD : ∀ f, q.charge c (U *ᵥ b) (D f) = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : q.fnorm (D (q.fStart U X S W X' W') - D (q.fNow U X S W)) ≤
      L * q.fnorm (q.fStart U X S W X' W' - q.fNow U X S W)) :
    |q.charge c (U *ᵥ b) (q.fNow U X' S' W') - q.charge c (U *ᵥ b) (q.fNow U X S W)| ≤
      2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * q.fnorm (D (q.fNow U X S W)) := by
  rw [h.charge_sub hs b hD, abs_mul, abs_neg, ← density_sub]
  have h1 := abs_ipx_density_le (q := q) (c - q.projX X' *ᵥ c) (U *ᵥ b)
    (D (q.fStart U X S W X' W') - D (q.fNow U X S W))
  have h2 := xnorm_sub_projX_le h.state.orthX c
  have h4 := h.start_error_le hs
  have hx : 0 ≤ q.xnorm c := Real.sqrt_nonneg _
  have hv : 0 ≤ q.vnorm (U *ᵥ b) := Real.sqrt_nonneg _
  have hd : 0 ≤ q.fnorm (D (q.fNow U X S W)) := fnorm_nonneg _
  calc |τ| * |q.ipx (c - q.projX X' *ᵥ c) (q.density (U *ᵥ b)
        (D (q.fStart U X S W X' W') - D (q.fNow U X S W)))|
      ≤ |τ| * (q.xnorm c * q.vnorm (U *ᵥ b) * (L * (2 * |τ| * q.fnorm (D (q.fNow U X S W))))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg _)
        have h5 : q.fnorm (D (q.fStart U X S W X' W') - D (q.fNow U X S W)) ≤
            L * (2 * |τ| * q.fnorm (D (q.fNow U X S W))) :=
          hL.trans (mul_le_mul_of_nonneg_left h4 hL0)
        have h6 := fnorm_nonneg (q := q) (D (q.fStart U X S W X' W') - D (q.fNow U X S W))
        exact mul_le_mul (mul_le_mul_of_nonneg_right h2 hv) h5 h6 (mul_nonneg hx hv)
    _ = 2 * L * |τ| ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * q.fnorm (D (q.fNow U X S W)) := by ring
    _ = _ := by rw [sq_abs]

/-- **Global drift of an invariant** (arXiv 2101.12571, Sec. 7.3, as an estimate).  Along `n` steps
of the integrator of Sec. 6.2, `|I[fₙ] - I[f₀]| ≤ n · 2 L τ² ‖c‖ ‖ζ‖ B`, so the drift over a fixed
time `T = n τ` is `O(τ)`: "reducing the time step size reduces the error in the conserved
quantities".  No assumption on `Sₙ`. -/
theorem charge_drift_le {Xs : ℕ → Matrix Mx (a ⊕ p) ℝ} {Ss : ℕ → Matrix (a ⊕ p) (a ⊕ p) ℝ}
    {Ws : ℕ → Matrix Mv p ℝ} (h0 : q.IsState U (Xs 0) (Ws 0))
    (hstep : ∀ n, q.IsStep D τ U (Xs n) (Ss n) (Ws n) (Xs (n + 1)) (Ss (n + 1)) (Ws (n + 1)))
    (b : a → ℝ) {c : Mx → ℝ} (hD : ∀ f, q.charge c (U *ᵥ b) (D f) = 0) {L B : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ n, q.fnorm (D (q.fStart U (Xs n) (Ss n) (Ws n) (Xs (n + 1)) (Ws (n + 1))) -
        D (q.fNow U (Xs n) (Ss n) (Ws n))) ≤
      L * q.fnorm (q.fStart U (Xs n) (Ss n) (Ws n) (Xs (n + 1)) (Ws (n + 1)) -
        q.fNow U (Xs n) (Ss n) (Ws n)))
    (hB : ∀ n, q.fnorm (D (q.fNow U (Xs n) (Ss n) (Ws n))) ≤ B) (n : ℕ) :
    |q.charge c (U *ᵥ b) (q.fNow U (Xs n) (Ss n) (Ws n)) -
        q.charge c (U *ᵥ b) (q.fNow U (Xs 0) (Ss 0) (Ws 0))| ≤
      n * (2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * B) := by
  have hstate : ∀ n, q.IsState U (Xs n) (Ws n) := by
    intro n
    cases n with
    | zero => exact h0
    | succ n => exact (hstep n).state
  have hx : 0 ≤ q.xnorm c := Real.sqrt_nonneg _
  have hv : 0 ≤ q.vnorm (U *ᵥ b) := Real.sqrt_nonneg _
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := (hstep n).charge_defect_le (hstate n) b hD hL0 (hL n)
    have h2 : 2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) *
        q.fnorm (D (q.fNow U (Xs n) (Ss n) (Ws n))) ≤
        2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * B :=
      mul_le_mul_of_nonneg_left (hB n) (by positivity)
    calc _ ≤ |q.charge c (U *ᵥ b) (q.fNow U (Xs (n + 1)) (Ss (n + 1)) (Ws (n + 1))) -
            q.charge c (U *ᵥ b) (q.fNow U (Xs n) (Ss n) (Ws n))| +
          |q.charge c (U *ᵥ b) (q.fNow U (Xs n) (Ss n) (Ws n)) -
            q.charge c (U *ᵥ b) (q.fNow U (Xs 0) (Ss 0) (Ws 0))| := abs_sub_le _ _ _
      _ ≤ (2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * B) +
          n * (2 * L * τ ^ 2 * q.xnorm c * q.vnorm (U *ᵥ b) * B) := add_le_add (h1.trans h2) ih
      _ = _ := by push_cast; ring

/-! ### Well-posedness without `S⁻¹` and comparison with the conservative Euler scheme -/

/-- `1 / √wₓ` as a diagonal matrix. -/
noncomputable def Sxi (q : Grid Mx Mv) : Matrix Mx Mx ℝ := diagonal fun x => (√(q.wx x))⁻¹

/-- `1 / √(wᵥ f₀ᵥ)` as a diagonal matrix. -/
noncomputable def Svi (q : Grid Mx Mv) : Matrix Mv Mv ℝ :=
  diagonal fun v => (√(q.wv v * q.f0 v))⁻¹

lemma Sxi_mul_Sx : q.Sxi * q.Sx = 1 := by
  simp only [Sxi, Sx, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext x
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (q.wx_pos x)).ne'

lemma Sx_mul_Sxi : q.Sx * q.Sxi = 1 := by
  simp only [Sxi, Sx, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext x
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (q.wx_pos x)).ne'

lemma Svi_mul_Sv : q.Svi * q.Sv = 1 := by
  simp only [Svi, Sv, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext v
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (mul_pos (q.wv_pos v) (q.f0_pos v))).ne'

lemma Sv_mul_Svi : q.Sv * q.Svi = 1 := by
  simp only [Svi, Sv, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1; ext v
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (mul_pos (q.wv_pos v) (q.f0_pos v))).ne'

/-- Reindexing the columns of a capturing basis. -/
lemma orth_capture_reindex {m c d : Type*} [Fintype m] [Fintype c] [Fintype d] [DecidableEq c]
    [DecidableEq d] (e : d ≃ c) {Q : Matrix m c ℝ} (hQ : Qᵀ * Q = 1) :
    (Q.submatrix id e)ᵀ * Q.submatrix id e = 1 ∧
      Q.submatrix id e * (Q.submatrix id e)ᵀ = Q * Qᵀ := by
  constructor
  · rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hQ,
      submatrix_one_equiv]
  · rw [transpose_submatrix, submatrix_mul_equiv]
    rfl

/-- The QR step of the spatial basis in the weighted setting, also for rank-deficient `K`. -/
lemma exists_xBasis (q : Grid Mx Mv) (K : Matrix Mx (a ⊕ p) ℝ)
    (hx : Fintype.card (a ⊕ p) ≤ Fintype.card Mx) :
    ∃ (X' : Matrix Mx (a ⊕ p) ℝ) (R : Matrix (a ⊕ p) (a ⊕ p) ℝ),
      X'ᵀ * q.Hx * X' = 1 ∧ K = X' * R := by
  obtain ⟨Q, hQ, hcap⟩ := exists_orthonormal_capture (q.Sx * K) (r := Fintype.card (a ⊕ p))
    (rank_le_card_width _) hx
  obtain ⟨h1, h2⟩ := orth_capture_reindex (Fintype.equivFin (a ⊕ p)) hQ
  set Q' := Q.submatrix id (Fintype.equivFin (a ⊕ p)) with hQ'
  refine ⟨q.Sxi * Q', Q'ᵀ * (q.Sx * K), ?_, ?_⟩
  · rw [← tx_mul, ← Matrix.mul_assoc q.Sx q.Sxi, Sx_mul_Sxi, Matrix.one_mul, h1]
  · calc K = q.Sxi * (q.Sx * K) := by rw [← Matrix.mul_assoc, Sxi_mul_Sx, Matrix.one_mul]
      _ = q.Sxi * (Q * Qᵀ * (q.Sx * K)) := by rw [hcap]
      _ = q.Sxi * (Q' * Q'ᵀ * (q.Sx * K)) := by rw [h2]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- The QR step of the dynamic velocity functions in the weighted setting: an `L` orthogonal to
the `Uₐ` factors as `L = W' R` with `W'` orthonormal and orthogonal to the `Uₐ`.  For a
rank-deficient `L`, this says that the factorization can be completed inside `span(Uₐ)^⊥`. -/
lemma exists_wBasis (q : Grid Mx Mv) {U : Matrix Mv a ℝ} (hU : Uᵀ * q.Hv * U = 1)
    {L : Matrix Mv p ℝ} (hL : Uᵀ * q.Hv * L = 0)
    (hv : Fintype.card (a ⊕ p) ≤ Fintype.card Mv) :
    ∃ (W' : Matrix Mv p ℝ) (R : Matrix p p ℝ),
      W'ᵀ * q.Hv * W' = 1 ∧ Uᵀ * q.Hv * W' = 0 ∧ L = W' * R := by
  have hU' : (q.Sv * U)ᵀ * (q.Sv * U) = 1 := by rw [tv_mul, hU]
  have hZ : (1 - (q.Sv * U) * (q.Sv * U)ᵀ) * (q.Sv * L) = q.Sv * L := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, tv_mul, hL, Matrix.mul_zero, sub_zero]
  obtain ⟨Y, hY, hYU, hcap⟩ := exists_orthonormal_capture_compl (s := Fintype.card p) (q.Sv * U) hU'
    (q.Sv * L) (rank_le_card_width _) (by simpa using hv)
  rw [hZ] at hcap
  obtain ⟨h1, h2⟩ := orth_capture_reindex (Fintype.equivFin p) hY
  set Y' := Y.submatrix id (Fintype.equivFin p) with hY'
  have hS : q.Sv * (q.Svi * Y') = Y' := by
    rw [← Matrix.mul_assoc, Sv_mul_Svi, Matrix.one_mul]
  refine ⟨q.Svi * Y', Y'ᵀ * (q.Sv * L), ?_, ?_, ?_⟩
  · rw [← tv_mul, hS, h1]
  · rw [← tv_mul, hS]
    have : (q.Sv * U)ᵀ * Y = 0 := by
      have := congrArg transpose hYU
      simpa [transpose_mul] using this
    ext i j
    have h := congrFun (congrFun this i) (Fintype.equivFin p j)
    simpa [Matrix.mul_apply, hY'] using h
  · calc L = q.Svi * (q.Sv * L) := by rw [← Matrix.mul_assoc, Svi_mul_Sv, Matrix.one_mul]
      _ = q.Svi * (Y * Yᵀ * (q.Sv * L)) := by rw [hcap]
      _ = q.Svi * (Y' * Y'ᵀ * (q.Sv * L)) := by rw [h2]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- **The integrator of Sec. 6.2 is well defined without any inverse of `S`** (arXiv 2101.12571,
Sec. 6.2: "the matrix `S` needs not be inverted").  For every admissible state, every `S`
(in particular a singular one, even `S = 0`), every `τ` and every right-hand side there is a step.
The two grids must carry at least `r` points.  This also shows that the hypotheses of `IsStep` can
be met: the rank-deficient QR can be completed so that `Wⁿ⁺¹ ⊥ Uₐ` still holds. -/
theorem exists_step (hs : q.IsState U X W) (D : Matrix Mx Mv ℝ → Matrix Mx Mv ℝ) (τ : ℝ)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (hx : Fintype.card (a ⊕ p) ≤ Fintype.card Mx)
    (hv : Fintype.card (a ⊕ p) ≤ Fintype.card Mv) :
    ∃ X' S' W', q.IsStep D τ U X S W X' S' W' := by
  obtain ⟨X', R₁, hX', hK⟩ := exists_xBasis q (q.kNext τ X S (vb U W) (D (q.dist X S (vb U W)))) hx
  obtain ⟨W', R₂, hW', hUW', hL⟩ := exists_wBasis q hs.orthU
    (lNext_orth (τ := τ) (S := S) hs (D (q.dist X S (vb U W)))) hv
  exact ⟨X', _, W', ⟨⟨hX', hs.orthU, hW', hUW'⟩, ⟨R₁, hK⟩, ⟨R₂, hL⟩, rfl⟩⟩

lemma range_mul_unit {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ)
    {B : Matrix n n ℝ} (hB : IsUnit B) :
    LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin := by
  rw [mulVecLin_mul, LinearMap.range_comp_of_range_eq_top]
  rw [LinearMap.range_eq_top]
  exact mulVec_surjective_iff_isUnit.mpr hB

lemma isUnit_inv {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : IsUnit A) :
    IsUnit A⁻¹ :=
  (isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det A ((isUnit_iff_isUnit_det A).mp hA))

/-- Eq. (14) of the conservative Euler scheme. -/
def ceS (q : Grid Mx Mv) (τ : ℝ) (X : Matrix Mx r ℝ) (S : Matrix r r ℝ) (V : Matrix Mv r ℝ)
    (A : Matrix Mx Mv ℝ) : Matrix r r ℝ :=
  S + τ • q.pairXV X V A

/-- Eq. (15) of the conservative Euler scheme, in the form forced by its derivation
`∑ᵢ Xᵢⁿ⁺¹ Sᵢₖⁿ⁺¹ = Kₖⁿ⁺¹`, i.e. with the index pair `(S⁻¹)ₖᵢ`; (15) prints `(S⁻¹)ᵢₖ`. -/
noncomputable def ceX (q : Grid Mx Mv) (τ : ℝ) (X : Matrix Mx r ℝ) (S : Matrix r r ℝ)
    (V : Matrix Mv r ℝ) (A : Matrix Mx Mv ℝ) : Matrix Mx r ℝ :=
  q.kNext τ X S V A * (q.ceS τ X S V A)⁻¹

/-- Eq. (16) of the conservative Euler scheme, with `T = Sₚᵀ Sₚ` inverted as the matrix of (11). -/
noncomputable def ceW (q : Grid Mx Mv) (τ : ℝ) (X : Matrix Mx (a ⊕ p) ℝ)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (V : Matrix Mv (a ⊕ p) ℝ) (W : Matrix Mv p ℝ)
    (A : Matrix Mx Mv ℝ) : Matrix Mv p ℝ :=
  W + τ • ((q.Fi * q.pairX X A * colsP S - V * (q.pairXV X V A)ᵀ * colsP S) *
    ((colsP S)ᵀ * colsP S)⁻¹)

/-- **`Kⁿ⁺¹` determines `X̄ⁿ⁺¹`** (arXiv 2101.12571, Sec. 6.2, which says that the approximation
spaces are uniquely defined by `Lⁿ⁺¹` and `Kⁿ⁺¹`), in the full-rank case. -/
theorem IsStep.range_kNext (h : q.IsStep D τ U X S W X' S' W')
    (hK : Function.Injective
      (q.kNext τ X S (vb U W) (D (q.dist X S (vb U W)))).mulVec) :
    LinearMap.range (q.kNext τ X S (vb U W) (D (q.dist X S (vb U W)))).mulVecLin =
      LinearMap.range X'.mulVecLin := by
  obtain ⟨R, hR⟩ := h.qrK
  rw [hR] at hK ⊢
  refine range_mul_unit _ (mulVec_injective_iff_isUnit.mp fun y z hyz => hK ?_)
  simp only [← mulVec_mulVec, hyz]

/-- **`Lⁿ⁺¹` determines `W̄ⁿ⁺¹`** (arXiv 2101.12571, Sec. 6.2), in the full-rank case. -/
theorem IsStep.range_lNext (h : q.IsStep D τ U X S W X' S' W')
    (hL : Function.Injective
      (q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W)))).mulVec) :
    LinearMap.range (q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W)))).mulVecLin =
      LinearMap.range W'.mulVecLin := by
  obtain ⟨R, hR⟩ := h.qrL
  rw [hR] at hL ⊢
  refine range_mul_unit _ (mulVec_injective_iff_isUnit.mp fun y z hyz => hL ?_)
  simp only [← mulVec_mulVec, hyz]

/-- **`S⁻¹` is only needed for the factors, not for the spaces** (arXiv 2101.12571, Sec. 6.2:
"Inverting `S` is only required in equations (10) and (11)").  Where the conservative Euler scheme
(14)-(16) is defined and the K- and L-updates have full rank, the integrator of Sec. 6.2 produces
the same `X̄ⁿ⁺¹` and the same `W̄ⁿ⁺¹` as the conservative Euler scheme. -/
theorem IsStep.spaces_eq_consEuler (h : q.IsStep D τ U X S W X' S' W')
    (hK : Function.Injective
      (q.kNext τ X S (vb U W) (D (q.dist X S (vb U W)))).mulVec)
    (hL : Function.Injective
      (q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W)))).mulVec)
    (hS : IsUnit (q.ceS τ X S (vb U W) (D (q.dist X S (vb U W)))))
    (hT : IsUnit ((colsP S)ᵀ * colsP S)) :
    LinearMap.range (q.ceX τ X S (vb U W) (D (q.dist X S (vb U W)))).mulVecLin =
        LinearMap.range X'.mulVecLin ∧
      LinearMap.range (q.ceW τ X S (vb U W) W (D (q.dist X S (vb U W)))).mulVecLin =
        LinearMap.range W'.mulVecLin := by
  constructor
  · rw [ceX, range_mul_unit _ (isUnit_inv hS), h.range_kNext hK]
  · have e : q.ceW τ X S (vb U W) W (D (q.dist X S (vb U W))) =
        q.lNext τ X S (vb U W) W (D (q.dist X S (vb U W))) * ((colsP S)ᵀ * colsP S)⁻¹ := by
      rw [ceW, lNext, Matrix.add_mul, Matrix.mul_assoc W, Matrix.mul_nonsing_inv _
        ((isUnit_iff_isUnit_det _).mp hT), Matrix.mul_one, Matrix.smul_mul]
    rw [e, range_mul_unit _ (isUnit_inv hT), h.range_lNext hL]

/-- **The moment of the projected start** (arXiv 2101.12571, Sec. 6.2): `ρ_ζ[f̃] = P₁ ρ_ζ[fⁿ]`.
The moments are only touched by
the spatial projection `M`, because `Nᵀ` fixes the `Uₐ` (Sec. 6.2). -/
theorem IsStep.density_fStart (hs : q.IsState U X W) (h : q.IsStep D τ U X S W X' S' W')
    (b : a → ℝ) :
    q.density (U *ᵥ b) (q.fStart U X S W X' W') =
      q.projX X' *ᵥ q.density (U *ᵥ b) (q.fNow U X S W) := by
  have hV' : (X'ᵀ * q.Hx * X) * S * ((vb U W)ᵀ * q.Hv * vb U W') * ea a p
      = (X'ᵀ * q.Hx * X) * S * ea a p := by
    rw [Matrix.mul_assoc _ _ (ea a p), Matrix.mul_assoc _ _ (ea a p), vb_mul_ea, hs.vb_transpose_U]
  rw [fStart, dist_density h.state, fNow, dist_density hs, sStart, Matrix.mul_assoc X', hV',
    mulVec_mulVec, projX]
  simp only [Matrix.mul_assoc]

/-- The moment of the projected start (arXiv 2101.12571, Sec. 6.2) against an arbitrary velocity
function:
`ρ_ζ[f̃] = P₁ ρ_{Π ζ}[fⁿ]`, where `Π` is the `⟨·,·⟩ᵥ`-orthogonal projection onto `V̄ⁿ⁺¹`. -/
theorem density_fStart_general (U : Matrix Mv a ℝ) (X : Matrix Mx (a ⊕ p) ℝ)
    (S : Matrix (a ⊕ p) (a ⊕ p) ℝ) (W : Matrix Mv p ℝ) (X' : Matrix Mx (a ⊕ p) ℝ)
    (W' : Matrix Mv p ℝ) (ζ : Mv → ℝ) :
    q.density ζ (q.fStart U X S W X' W') =
      q.projX X' *ᵥ q.density (vb U W' *ᵥ ((vb U W')ᵀ *ᵥ (q.Hv *ᵥ ζ))) (q.fNow U X S W) := by
  have e : ∀ (A : Matrix Mx Mv ℝ) (y : Mv → ℝ), (A * q.F) *ᵥ (q.Hu *ᵥ y) = A *ᵥ (q.Hv *ᵥ y) := by
    intro A y
    rw [← mulVec_mulVec, mulVec_mulVec _ q.F q.Hu, F_mul_Hu]
  rw [density_eq, density_eq, fStart, fNow, dist, dist, e, e, sStart, projX]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/-- Evaluation of `P₁`: if `z ∈ span K = X̄ⁿ⁺¹` and `y - z ⊥ K`, then `P₁ y = z`.  Here `K` has a
left inverse `C`, so that `K` spans `span X'` exactly. -/
lemma projX_mulVec_eq {X' : Matrix Mx r ℝ} {K : Matrix Mx s ℝ} {R : Matrix r s ℝ}
    {C : Matrix s Mx ℝ} (hcard : Fintype.card r = Fintype.card s) (hX : X'ᵀ * q.Hx * X' = 1)
    (hK : K = X' * R) (hC : C * K = 1) {y z : Mx → ℝ} (w : s → ℝ) (hz : z = K *ᵥ w)
    (horth : Kᵀ *ᵥ (q.Hx *ᵥ (y - z)) = 0) : q.projX X' *ᵥ y = z := by
  have hR : (C * X') * R = 1 := by rw [Matrix.mul_assoc, ← hK, hC]
  have hR' : R * (C * X') = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (A := C * X') (B := R) (eq := hcard.symm)).mp hR
  have hX' : X' = K * (C * X') := by rw [hK, Matrix.mul_assoc, hR', Matrix.mul_one]
  have h0 : X'ᵀ *ᵥ (q.Hx *ᵥ (y - z)) = 0 := by
    have e : X'ᵀ = (C * X')ᵀ * Kᵀ := by
      conv_lhs => rw [hX', transpose_mul]
    rw [e, ← mulVec_mulVec, horth, mulVec_zero]
  have h1 : q.projX X' *ᵥ (y - z) = 0 := by
    rw [projX, ← mulVec_mulVec, ← mulVec_mulVec, h0, mulVec_zero]
  have h2 : q.projX X' *ᵥ z = z := by
    rw [hz, mulVec_mulVec, projX_mul_self hX hK]
  rw [mulVec_sub, sub_eq_zero] at h1
  rw [h1, h2]

end Weighted

end Grid

/-! ### A discrete Vlasov-Poisson instance: mass and momentum are lost -/

/-- The discrete right-hand side `D[f] = -v ∂ₓ f + E[f] ∂ᵥ f` of the Vlasov equation, for discrete
derivatives `dx`, `dv`. -/
def vlasovRHS {Mx Mv : Type*} [Fintype Mx] [Fintype Mv] (vel : Mv → ℝ) (dx : Matrix Mx Mx ℝ)
    (dv : Matrix Mv Mv ℝ) (E : Matrix Mx Mv ℝ → Mx → ℝ) (f : Matrix Mx Mv ℝ) : Matrix Mx Mv ℝ :=
  Matrix.of fun x v => -(vel v * (dx * f) x v) + E f x * (f * dvᵀ) x v

section VP

/-- Four periodic points in `x`, two velocities, `f₀ᵥ = 1`. -/
noncomputable def vpGrid : Grid (Fin 4) (Fin 2) where
  wx _ := 1 / 4
  wv _ := 1 / 2
  f0 _ := 1
  wx_pos _ := by norm_num
  wv_pos _ := by norm_num
  f0_pos _ := by norm_num

/-- The velocities `v = ∓2`. -/
def vpVel : Fin 2 → ℝ := ![-2, 2]

/-- Centered differences on the periodic grid of mesh size one. -/
noncomputable def vpDx : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1 / 2, 0, -1 / 2; -1 / 2, 0, 1 / 2, 0; 0, -1 / 2, 0, 1 / 2; 1 / 2, 0, -1 / 2, 0]

/-- `vpDx` is the centered difference `(y(x + 1) - y(x - 1)) / 2` (periodic), one of the space
discretizations named in arXiv 2101.12571, Sec. 6.1. -/
theorem vpDx_mulVec (y : Fin 4 → ℝ) (x : Fin 4) :
    (vpDx *ᵥ y) x = (y (x + 1) - y (x - 1)) / 2 := by
  fin_cases x
  · change (vpDx *ᵥ y) 0 = (y 1 - y 3) / 2
    simp [vpDx, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · change (vpDx *ᵥ y) 1 = (y 2 - y 0) / 2
    simp [vpDx, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · change (vpDx *ᵥ y) 2 = (y 3 - y 1) / 2
    simp [vpDx, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · change (vpDx *ᵥ y) 3 = (y 0 - y 2) / 2
    simp [vpDx, mulVec, dotProduct, Fin.sum_univ_four]; ring

/-- The velocity derivative with exact discrete integration by parts against `1` and `v`:
`∫ ∂ᵥ f dv = 0` and `∫ v ∂ᵥ f dv = -∫ f dv`. -/
noncomputable def vpDv : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 4, 1 / 4; -1 / 4, -1 / 4]

/-- The self-consistent field `E = ∂ₓ ρ`.  On this grid `∂ₓ` is its own negative pseudo-inverse,
so `E` is the least-squares solution of the discrete Poisson equation `∂ₓ E = 1 - ρ`. -/
noncomputable def vpE (f : Matrix (Fin 4) (Fin 2) ℝ) : Fin 4 → ℝ :=
  vpDx *ᵥ vpGrid.density 1 f

/-- The discrete Vlasov-Poisson right-hand side. -/
noncomputable def vpD : Matrix (Fin 4) (Fin 2) ℝ → Matrix (Fin 4) (Fin 2) ℝ :=
  vlasovRHS vpVel vpDx vpDv vpE

/-- The fixed functions: `U₁ = 1 / ‖1‖` and `U₂ = v / ‖v‖`. -/
def vpU : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 1]

/-- The second fixed function. -/
def vpU₂ : Fin 2 → ℝ := ![-1, 1]

lemma vpU_one : vpU *ᵥ ![1, 0] = 1 := by
  ext v; fin_cases v <;> simp [vpU, mulVec, dotProduct, Fin.sum_univ_two]

lemma vpU_two : vpU *ᵥ ![0, 1] = vpU₂ := by
  ext v; fin_cases v <;> simp [vpU, vpU₂, mulVec, dotProduct, Fin.sum_univ_two]

lemma vpU_vel : vpU *ᵥ ![0, 2] = vpVel := by
  ext v; fin_cases v <;> simp [vpU, vpVel, mulVec, dotProduct, Fin.sum_univ_two]

lemma vpD_density_one (f : Matrix (Fin 4) (Fin 2) ℝ) :
    vpGrid.density 1 (vpD f) = -(2 : ℝ) • (vpDx *ᵥ vpGrid.density vpU₂ f) := by
  ext x
  fin_cases x <;>
    simp [Grid.density, vpD, vlasovRHS, vpGrid, vpVel, vpDv, vpDx, vpU₂, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two, Fin.sum_univ_four] <;> ring

lemma vpD_density_two (f : Matrix (Fin 4) (Fin 2) ℝ) :
    vpGrid.density vpU₂ (vpD f) =
      -(2 : ℝ) • (vpDx *ᵥ vpGrid.density 1 f) - (1 / 2 : ℝ) • (vpE f * vpGrid.density 1 f) := by
  ext x
  have h : vpE f x = (vpDx *ᵥ vpGrid.density 1 f) x := rfl
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, h]
  fin_cases x <;>
    simp [Grid.density, vpD, vlasovRHS, vpE, vpGrid, vpVel, vpDv, vpDx, vpU₂, Matrix.mul_apply,
      mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_four] <;> ring

lemma vp_density_vel (f : Matrix (Fin 4) (Fin 2) ℝ) :
    vpGrid.density vpVel f = (2 : ℝ) • vpGrid.density vpU₂ f := by
  ext x
  simp [Grid.density, vpGrid, vpVel, vpU₂, Fin.sum_univ_two]
  ring

lemma vpDx0 (r : Fin 4 → ℝ) : (vpDx *ᵥ r) 0 = (r 1 - r 3) / 2 := vpDx_mulVec r 0
lemma vpDx1 (r : Fin 4 → ℝ) : (vpDx *ᵥ r) 1 = (r 2 - r 0) / 2 := vpDx_mulVec r 1
lemma vpDx2 (r : Fin 4 → ℝ) : (vpDx *ᵥ r) 2 = (r 3 - r 1) / 2 := vpDx_mulVec r 2
lemma vpDx3 (r : Fin 4 → ℝ) : (vpDx *ᵥ r) 3 = (r 0 - r 2) / 2 := vpDx_mulVec r 3

lemma vp_ipx (u w : Fin 4 → ℝ) :
    vpGrid.ipx u w = (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3) / 4 := by
  simp only [Grid.ipx, Fin.sum_univ_four, vpGrid]
  ring

/-- The discrete Vlasov-Poisson operator conserves the mass exactly (arXiv 2101.12571, Sec. 2 and
Sec. 6.1: exact discrete integration by parts). -/
theorem vp_mass_conservative (f : Matrix (Fin 4) (Fin 2) ℝ) : vpGrid.charge 1 1 (vpD f) = 0 := by
  rw [Grid.charge, vpD_density_one, vp_ipx]
  generalize vpGrid.density vpU₂ f = r
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1, vpDx2, vpDx3]
  ring

/-- The discrete Vlasov-Poisson operator conserves the momentum exactly (arXiv 2101.12571, Sec. 2):
`∫ E ρ dx = ∫ ρ ∂ₓ ρ dx = 0`. -/
theorem vp_momentum_conservative (f : Matrix (Fin 4) (Fin 2) ℝ) :
    vpGrid.charge 1 vpVel (vpD f) = 0 := by
  rw [Grid.charge, vp_density_vel, vpD_density_two, vp_ipx]
  simp only [vpE]
  generalize vpGrid.density 1 f = r
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1,
    vpDx2, vpDx3]
  ring

/-- The density of the example. -/
noncomputable def vpRho : Fin 4 → ℝ := ![7 / 5, 1, 3 / 5, 1]

/-- The coefficient of `U₂`; the current is `2 κ`. -/
noncomputable def vpKap : Fin 4 → ℝ := ![7 / 5, 7 / 25, -3 / 5, 7 / 25]

/-- `Kⁿ = Xⁿ Sⁿ` of the example; the distribution is `f(x, ±2) = ρ ± κ`. -/
noncomputable def vpK : Matrix (Fin 4) (Fin 2 ⊕ Empty) ℝ :=
  Matrix.of fun x j => Sum.elim (fun i : Fin 2 => ![vpRho x, vpKap x] i) (fun e => e.elim) j

/-- The columns of `Kⁿ⁺¹` of the example. -/
noncomputable def vpk (τ : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![7 / 5, 7 / 5; 2 * τ + 1, τ + 7 / 25; 3 / 5, -3 / 5; 1 - 2 * τ, 7 / 25 - τ]

/-- A left inverse of `vpk τ`, independent of `τ`. -/
noncomputable def vpC : Matrix (Fin 2) (Fin 4) ℝ := !![5 / 14, 0, 5 / 6, 0; 5 / 14, 0, -5 / 6, 0]

lemma vpC_mul (τ : ℝ) : vpC * vpk τ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vpC, vpk, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma mul_ea_apply {m : Type*} (A : Matrix m (a ⊕ p) ℝ) (x : m) (i : a) :
    (A * Grid.ea a p) x i = A x (Sum.inl i) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Grid.ea, Matrix.one_apply]

variable {τ : ℝ} {X X' : Matrix (Fin 4) (Fin 2 ⊕ Empty) ℝ} {R : Matrix (Fin 2 ⊕ Empty) (Fin 2) ℝ}
  {S S' : Matrix (Fin 2 ⊕ Empty) (Fin 2 ⊕ Empty) ℝ} {W W' : Matrix (Fin 2) Empty ℝ}

lemma vp_proj (hX : X'ᵀ * vpGrid.Hx * X' = 1) (hK : vpk τ = X' * R) {y z : Fin 4 → ℝ}
    (w : Fin 2 → ℝ) (hz : z = vpk τ *ᵥ w)
    (horth : (vpk τ)ᵀ *ᵥ (vpGrid.Hx *ᵥ (y - z)) = 0) : vpGrid.projX X' *ᵥ y = z :=
  Grid.projX_mulVec_eq (by simp) hX hK (vpC_mul τ) w hz horth

lemma vp_proj_rho (hX : X'ᵀ * vpGrid.Hx * X' = 1) (hK : vpk τ = X' * R) :
    vpGrid.projX X' *ᵥ vpRho = ![189 / (5 * (50 * τ ^ 2 + 27)),
      27 * (2 * τ + 1) / (50 * τ ^ 2 + 27), 81 / (5 * (50 * τ ^ 2 + 27)),
      -27 * (2 * τ - 1) / (50 * τ ^ 2 + 27)] := by
  have hZ : (50 * τ ^ 2 + 27 : ℝ) ≠ 0 := by positivity
  refine vp_proj hX hK ![27 / (50 * τ ^ 2 + 27), 0] ?_ ?_
  · ext i
    fin_cases i <;> simp [vpk, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  · ext i
    fin_cases i <;>
      simp [vpk, vpRho, vpGrid, Grid.Hx, mulVec, dotProduct, Fin.sum_univ_four] <;>
        field_simp <;> ring

lemma vp_proj_kap (hX : X'ᵀ * vpGrid.Hx * X' = 1) (hK : vpk τ = X' * R) :
    vpGrid.projX X' *ᵥ vpKap = ![7 * (25 * τ ^ 2 + 27) / (5 * (50 * τ ^ 2 + 27)),
      -(275 * τ ^ 2 - 675 * τ - 189) / (25 * (50 * τ ^ 2 + 27)),
      -9 * (25 * τ ^ 2 + 9) / (5 * (50 * τ ^ 2 + 27)),
      -(275 * τ ^ 2 + 675 * τ - 189) / (25 * (50 * τ ^ 2 + 27))] := by
  have hZ : (50 * τ ^ 2 + 27 : ℝ) ≠ 0 := by positivity
  refine vp_proj hX hK ![-25 * τ ^ 2 / (50 * τ ^ 2 + 27), 1] ?_ ?_
  · ext i
    fin_cases i <;> simp [vpk, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  · ext i
    fin_cases i <;>
      simp [vpk, vpKap, vpGrid, Grid.Hx, mulVec, dotProduct, Fin.sum_univ_four] <;>
        field_simp <;> ring

lemma vp_proj_one (hX : X'ᵀ * vpGrid.Hx * X' = 1) (hK : vpk τ = X' * R) :
    vpGrid.projX X' *ᵥ 1 = ![-35 * (400 * τ ^ 2 - 657) / (873 * (50 * τ ^ 2 + 27)),
      (4400 * τ ^ 2 + 43650 * τ + 24201) / (873 * (50 * τ ^ 2 + 27)),
      5 * (400 * τ ^ 2 + 507) / (97 * (50 * τ ^ 2 + 27)),
      (4400 * τ ^ 2 - 43650 * τ + 24201) / (873 * (50 * τ ^ 2 + 27))] := by
  have hZ : (50 * τ ^ 2 + 27 : ℝ) ≠ 0 := by positivity
  refine vp_proj hX hK ![25 * (400 * τ ^ 2 + 1089) / (873 * (50 * τ ^ 2 + 27)), -400 / 873] ?_ ?_
  · ext i
    fin_cases i <;> simp [vpk, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  · ext i
    fin_cases i <;>
      simp [vpk, vpGrid, Grid.Hx, mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp <;> ring

lemma vp_fNow_density (hs : vpGrid.IsState vpU X W) (hK : X * S = vpK) :
    vpGrid.density 1 (vpGrid.fNow vpU X S W) = vpRho ∧
      vpGrid.density vpU₂ (vpGrid.fNow vpU X S W) = vpKap := by
  constructor
  · rw [← vpU_one, Grid.fNow, Grid.dist_density hs, hK]
    ext x
    simp [mulVec, dotProduct, Fin.sum_univ_two, mul_ea_apply, vpK]
  · rw [← vpU_two, Grid.fNow, Grid.dist_density hs, hK]
    ext x
    simp [mulVec, dotProduct, Fin.sum_univ_two, mul_ea_apply, vpK]

lemma vp_kNext (hs : vpGrid.IsState vpU X W) (hK : X * S = vpK) :
    vpGrid.kNext τ X S (vb vpU W) (vpD (vpGrid.dist X S (vb vpU W))) * Grid.ea (Fin 2) Empty =
      vpk τ := by
  obtain ⟨hρ, hκ⟩ := vp_fNow_density hs hK
  set A := vpD (vpGrid.dist X S (vb vpU W)) with hA
  have hmat : vpGrid.kNext τ X S (vb vpU W) A * Grid.ea (Fin 2) Empty =
      vpK * Grid.ea (Fin 2) Empty + τ • (A * vpGrid.Hu * vpU) := by
    rw [Grid.kNext, Grid.pairV, hK, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc _ (vb vpU W),
      Grid.vb_mul_ea]
  have e0 : ∀ x, (A * vpGrid.Hu * vpU) x 0 = (-(2 : ℝ) • (vpDx *ᵥ vpKap)) x := by
    intro x
    have h1 := Grid.density_U (q := vpGrid) vpU ![1, 0] A
    rw [vpU_one, hA, vpD_density_one, ← hA] at h1
    rw [show vpGrid.density vpU₂ (vpGrid.dist X S (vb vpU W)) = vpKap from hκ] at h1
    rw [h1]
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : ∀ x, (A * vpGrid.Hu * vpU) x 1 = (-(2 : ℝ) • (vpDx *ᵥ vpRho) -
      (1 / 2 : ℝ) • ((vpDx *ᵥ vpRho) * vpRho)) x := by
    intro x
    have h1 := Grid.density_U (q := vpGrid) vpU ![0, 1] A
    rw [vpU_two, hA, vpD_density_two, ← hA] at h1
    simp only [vpE] at h1
    rw [show vpGrid.density 1 (vpGrid.dist X S (vb vpU W)) = vpRho from hρ] at h1
    rw [h1]
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [hmat]
  ext x i
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_ea_apply]
  fin_cases i
  · simp only [Fin.zero_eta, e0, vpK, Pi.smul_apply, smul_eq_mul]
    fin_cases x <;> simp [vpDx0, vpDx1, vpDx2, vpDx3, vpk, vpRho, vpKap] <;> ring
  · simp only [Fin.mk_one, e1, vpK, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    fin_cases x <;> simp [vpDx0, vpDx1, vpDx2, vpDx3, vpk, vpRho, vpKap] <;> ring

/-- **Mass and momentum are not conserved by the integrator of Sec. 6.2** (arXiv 2101.12571,
Sec. 6.2: "mass and momentum conservation up to machine precision is lost"), for the actual
Vlasov-Poisson right-hand side.  On four periodic points and two velocities `±2`, with centered
differences and the self-consistent field, `vpD` conserves mass and momentum exactly
(`vp_mass_conservative`, `vp_momentum_conservative`).  With `m = r = 2`, `U₁ ∝ 1`, `U₂ ∝ v` and the
nonnegative `fⁿ` of `vp_instance`, every step of the integrator, for every QR factorization and
every `τ`, changes mass and momentum by exactly the amounts below.  The mass changes for every
`τ ≠ 0`.  Both defects are exactly of order `τ²`, so `Grid.IsStep.charge_defect_le` is sharp in `τ`.
The example has no dynamic `W`: the loss comes from the spatial projection `M` alone. -/
theorem vp_mass_momentum_change (hs : vpGrid.IsState vpU X W) (hK : X * S = vpK)
    (h : vpGrid.IsStep vpD τ vpU X S W X' S' W') :
    vpGrid.charge 1 1 (vpGrid.fNow vpU X' S' W') - vpGrid.charge 1 1 (vpGrid.fNow vpU X S W) =
        -(10 * τ ^ 2 / (97 * (50 * τ ^ 2 + 27))) ∧
      vpGrid.charge 1 vpVel (vpGrid.fNow vpU X' S' W') -
          vpGrid.charge 1 vpVel (vpGrid.fNow vpU X S W) =
        -(2 * τ ^ 2 * (126250 * τ ^ 2 - 513) / (485 * (50 * τ ^ 2 + 27) ^ 2)) := by
  obtain ⟨hρ, hκ⟩ := vp_fNow_density hs hK
  obtain ⟨R, hR⟩ := h.qrK
  have hk : vpk τ = X' * (R * Grid.ea (Fin 2) Empty) := by
    rw [← vp_kNext hs hK, hR, Matrix.mul_assoc]
  have hX := h.state.orthX
  have p1 := vp_proj_one hX hk
  have pρ := vp_proj_rho hX hk
  have pκ := vp_proj_kap hX hk
  have hρt : vpGrid.density 1 (vpGrid.fStart vpU X S W X' W') = vpGrid.projX X' *ᵥ vpRho := by
    have := h.density_fStart hs ![1, 0]
    rwa [vpU_one, hρ] at this
  have hκt : vpGrid.density vpU₂ (vpGrid.fStart vpU X S W X' W') = vpGrid.projX X' *ᵥ vpKap := by
    have := h.density_fStart hs ![0, 1]
    rwa [vpU_two, hκ] at this
  have hZ : (50 * τ ^ 2 + 27 : ℝ) ≠ 0 := by positivity
  constructor
  · have := h.charge_sub hs ![1, 0] (c := 1) (by rw [vpU_one]; exact vp_mass_conservative)
    rw [vpU_one] at this
    rw [this, vpD_density_one, vpD_density_one, hκt, hκ, pκ, p1, vp_ipx]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1, vpDx2, vpDx3]
    simp [vpKap]
    field_simp
    ring
  · have := h.charge_sub hs ![0, 2] (c := 1) (by rw [vpU_vel]; exact vp_momentum_conservative)
    rw [vpU_vel] at this
    rw [this, vp_density_vel, vp_density_vel, vpD_density_two, vpD_density_two, vp_ipx]
    simp only [vpE]
    rw [hρt, hρ, pρ, p1]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1,
      vpDx2, vpDx3]
    simp [vpRho]
    field_simp
    ring

/-- The explicit form of `fⁿ` in the example: `f(x, ±2) = ρ ± κ`. -/
lemma vp_fNow_apply (hK : X * S = vpK) (x : Fin 4) (v : Fin 2) :
    vpGrid.fNow vpU X S W x v = vpRho x + vpU₂ v * vpKap x := by
  have e : vpGrid.F = 1 := by
    simp only [Grid.F, vpGrid]
    exact diagonal_one
  rw [Grid.fNow, Grid.dist, hK, e, Matrix.mul_one]
  fin_cases v <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, vb, vpK, vpU, vpU₂]

/-- **The example of `vp_mass_momentum_change` exists** and is physical: the state exists, `fⁿ` is
nonnegative (it describes two beams), the field `E` solves the discrete Poisson equation
`∂ₓ E = 1 - ρ` exactly at `fⁿ`, and a step exists for every `τ`. -/
theorem vp_instance : ∃ (X : Matrix (Fin 4) (Fin 2 ⊕ Empty) ℝ)
    (S : Matrix (Fin 2 ⊕ Empty) (Fin 2 ⊕ Empty) ℝ) (W : Matrix (Fin 2) Empty ℝ),
    vpGrid.IsState vpU X W ∧ X * S = vpK ∧ (∀ x v, 0 ≤ vpGrid.fNow vpU X S W x v) ∧
      vpDx *ᵥ vpE (vpGrid.fNow vpU X S W) = 1 - vpGrid.density 1 (vpGrid.fNow vpU X S W) ∧
      ∀ τ : ℝ, ∃ X' S' W', vpGrid.IsStep vpD τ vpU X S W X' S' W' := by
  obtain ⟨X, R, hX, hK⟩ := Grid.exists_xBasis vpGrid vpK (by simp)
  have hU : vpUᵀ * vpGrid.Hv * vpU = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vpU, vpGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;>
      norm_num
  have hs : vpGrid.IsState vpU X 0 := ⟨hX, hU, by ext e; exact e.elim, by ext _ e; exact e.elim⟩
  refine ⟨X, R, 0, hs, hK.symm, ?_, ?_, fun τ => Grid.exists_step hs vpD τ R (by simp) (by simp)⟩
  · intro x v
    rw [vp_fNow_apply hK.symm]
    fin_cases x <;> fin_cases v <;> norm_num [vpRho, vpKap, vpU₂]
  · have hρ := (vp_fNow_density hs hK.symm).1
    rw [vpE, hρ]
    ext x
    fin_cases x <;>
      simp [vpRho, vpDx, mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

end VP

/-! ### Small singular values: no robust local error bound -/

section Robust

/-- Four periodic points in `x`, three velocities, a discrete Maxwellian `f₀ᵥ` of mass one. -/
noncomputable def robGrid : Grid (Fin 4) (Fin 3) where
  wx _ := 1 / 2
  wv _ := 1
  f0 := ![9 / 50, 16 / 25, 9 / 50]
  wx_pos _ := by norm_num
  wv_pos _ := by norm_num
  f0_pos v := by fin_cases v <;> norm_num

/-- The velocities `v = -1, 0, 1`. -/
def robVel : Fin 3 → ℝ := ![-1, 0, 1]

/-- Free streaming: the right-hand side of the Vlasov equation with zero field. -/
noncomputable def robD : Matrix (Fin 4) (Fin 3) ℝ → Matrix (Fin 4) (Fin 3) ℝ :=
  vlasovRHS robVel vpDx 0 fun _ _ => 0

/-- The fixed function `U₁ = 1` (mass conservation, `m = 1`). -/
def robU : Matrix (Fin 3) Unit ℝ := Matrix.of fun _ _ => 1

/-- The dynamic velocity function `W = (3 v̂ + 4 ĥ) / 5` (`v̂ = v / ‖v‖`, `ĥ ∝ v² - c`). -/
noncomputable def robW : Matrix (Fin 3) Unit ℝ := Matrix.of fun v _ => ![1 / 15, -3 / 5, 31 / 15] v

/-- The spatial basis `X₁ = (2 + cos) / 3`, `X₂ = sin`. -/
noncomputable def robX : Matrix (Fin 4) (Unit ⊕ Unit) ℝ :=
  Matrix.of fun x j => Sum.elim (fun _ => ![1, 2 / 3, 1 / 3, 2 / 3] x) (fun _ => ![0, 1, 0, -1] x) j

/-- `S = diag(3, ε)`: the small singular value is `ε`. -/
noncomputable def robS (ε : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ :=
  diagonal (Sum.elim (fun _ => 3) (fun _ => ε))

/-- `fⁿ` of the example. -/
noncomputable def robF (ε : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of fun x v => robGrid.f0 v *
    (2 + ![1, 0, -1, 0] x + ε * ![0, 1, 0, -1] x * ![1 / 15, -3 / 5, 31 / 15] v)

lemma rob_state : robGrid.IsState robU robX robW := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [robX, robGrid, Grid.Hx, Matrix.mul_apply, Fin.sum_univ_four] <;>
      norm_num
  · ext i j
    simp [robU, robGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  · ext i j
    simp [robW, robGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  · ext i j
    simp [robU, robW, robGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num

lemma rob_dist (ε : ℝ) : robGrid.dist robX (robS ε) (vb robU robW) = robF ε := by
  ext x v
  fin_cases x <;> fin_cases v <;>
    simp [Grid.dist, Grid.F, robGrid, robX, robS, robU, robW, robF, vb, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.diagonal_apply] <;> ring

/-- `D[fⁿ]` of the example. -/
noncomputable def robA (ε : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  Matrix.of fun x v => robGrid.f0 v * robVel v *
    (![0, 1, 0, -1] x - ε * ![1, 0, -1, 0] x * ![1 / 15, -3 / 5, 31 / 15] v)

lemma rob_D (ε : ℝ) : robD (robF ε) = robA ε := by
  ext x v
  fin_cases x <;> fin_cases v <;>
    simp [robD, vlasovRHS, vpDx, robF, robA, robGrid, robVel, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

/-- `Lⁿ⁺¹ = ε (ε W - (12/25) τ h)`, with `h ⊥ U, W`.  The part of `D[fⁿ]` along `W` is missing. -/
noncomputable def robL (τ ε : ℝ) : Matrix (Fin 3) Unit ℝ :=
  Matrix.of fun v _ => ε * (ε * ![1 / 15, -3 / 5, 31 / 15] v -
    12 / 25 * τ * ![32 / 15, -9 / 20, -8 / 15] v)

lemma rob_lNext (τ ε : ℝ) :
    robGrid.lNext τ robX (robS ε) (vb robU robW) robW (robA ε) = robL τ ε := by
  ext v u
  fin_cases v <;>
    simp [Grid.lNext, Grid.pairX, Grid.pairXV, Grid.Hx, Grid.Hu, Grid.Fi, robGrid, robX, robS,
      robU, robW, robA, robL, robVel, colsP, vb, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_four, Fin.sum_univ_three, Matrix.diagonal_apply] <;> ring

lemma density_dist_eq_zero {q : Grid Mx Mv} {y : Mv → ℝ} (X' : Matrix Mx r ℝ) (S' : Matrix r s ℝ)
    (V' : Matrix Mv s ℝ) (hy : V'ᵀ *ᵥ (q.Hv *ᵥ y) = 0) : q.density y (q.dist X' S' V') = 0 := by
  have e : q.F *ᵥ (q.Hu *ᵥ y) = q.Hv *ᵥ y := by
    rw [mulVec_mulVec, Grid.F_mul_Hu]
  rw [Grid.density_eq, Grid.dist, ← mulVec_mulVec, e, ← mulVec_mulVec, hy, mulVec_zero]

/-- The test function of the lower bound: orthogonal to `U` and to `Lⁿ⁺¹`. -/
noncomputable def robY (τ ε : ℝ) : Fin 3 → ℝ :=
  ![12 / 25 * τ * (1 / 15) + ε * (32 / 15), 12 / 25 * τ * (-3 / 5) + ε * (-9 / 20),
    12 / 25 * τ * (31 / 15) + ε * (-8 / 15)]

/-- **Small singular values spoil the local error of the integrator of Sec. 6.2** (arXiv
2101.12571, Sec. 6.2: "This gives us a robust dynamical low-rank integrator as the matrix `S` needs
not be inverted").  `S` need indeed not be inverted (`exists_step`), but the *errors* are not robust
in the sense of Kieri-Lubich-Walach and Ceruti-Lubich, the references the paper relies on (the
paper does not define "robust"; this reading is ours).  For
free streaming on a fixed grid, `U₁ = 1`, `r = 2`, `S = diag(3, ε)` with `0 < ε ≤ (12/25) τ`, every
step of the integrator, for every QR factorization, misses the explicit Euler step by at least
`(9/25) τ / √2`: the local error is `O(τ)`, not `O(τ²)`.  The cause is the L-update: the part of
`D[fⁿ]` along `W` is removed from `Lⁿ⁺¹`, and QR then rotates `W` too far when `ε ≲ τ`.
This concerns one step; it does not say that the method fails to converge. -/
theorem rob_local_error {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hετ : ε ≤ 12 / 25 * τ)
    {X' : Matrix (Fin 4) (Unit ⊕ Unit) ℝ} {S' : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ}
    {W' : Matrix (Fin 3) Unit ℝ}
    (h : robGrid.IsStep robD τ robU robX (robS ε) robW X' S' W') :
    9 / 25 * τ / √2 ≤ robGrid.fnorm (robGrid.fNow robU X' S' W' - (robF ε + τ • robA ε)) := by
  obtain ⟨R, hR⟩ := h.qrL
  rw [rob_dist, rob_D, rob_lNext] at hR
  set r₀ := R () () with hr₀
  have hent : ∀ v, robL τ ε v () = W' v () * r₀ := by
    intro v
    rw [hR]
    simp [Matrix.mul_apply, hr₀]
  have hr : r₀ ≠ 0 := by
    intro h0
    have e0 := hent 0
    have e1 := hent 1
    simp only [h0, mul_zero, robL, Matrix.of_apply] at e0 e1
    have e0' := (mul_eq_zero.mp e0).resolve_left hε.ne'
    have e1' := (mul_eq_zero.mp e1).resolve_left hε.ne'
    simp at e0' e1'
    nlinarith
  have hy0 : ∑ v, robGrid.wv v * robGrid.f0 v * robY τ ε v = 0 := by
    simp [Fin.sum_univ_three, robGrid, robY]
    ring
  have hyL : ∑ v, robGrid.wv v * robGrid.f0 v * robY τ ε v * robL τ ε v () = 0 := by
    simp [Fin.sum_univ_three, robGrid, robY, robL]
    ring
  have hyW : ∑ v, robGrid.wv v * robGrid.f0 v * robY τ ε v * W' v () = 0 := by
    have : ∑ v, robGrid.wv v * robGrid.f0 v * robY τ ε v * W' v () =
        (∑ v, robGrid.wv v * robGrid.f0 v * robY τ ε v * robL τ ε v ()) / r₀ := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hent v]
      field_simp
    rw [this, hyL, zero_div]
  have hV : (vb robU W')ᵀ *ᵥ (robGrid.Hv *ᵥ robY τ ε) = 0 := by
    ext j
    rcases j with j | j
    · simp only [vb, Pi.zero_apply, mulVec, dotProduct, transpose_apply, fromCols_apply_inl, robU,
        Matrix.of_apply, one_mul, Grid.Hv, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      exact hy0
    · simp only [vb, Pi.zero_apply, mulVec, dotProduct, transpose_apply, fromCols_apply_inr,
        Grid.Hv, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← hyW]
      exact Finset.sum_congr rfl fun v _ => by ring
  set A := robGrid.fNow robU X' S' W' - (robF ε + τ • robA ε) with hA
  have h1 := Grid.abs_ipx_density_le (q := robGrid) ![0, 1, 0, -1] (robY τ ε) A
  have h2 : robGrid.ipx ![0, 1, 0, -1] (robGrid.density (robY τ ε) A) = -(108 / 625 * τ ^ 2) := by
    rw [hA, Grid.density_sub, show robGrid.density (robY τ ε) (robGrid.fNow robU X' S' W') = 0 from
      density_dist_eq_zero _ _ _ hV]
    simp [Grid.ipx, Grid.density, Fin.sum_univ_three, Fin.sum_univ_four, robGrid, robY, robF, robA,
      robVel]
    ring
  have h3 : robGrid.xnorm ![0, 1, 0, -1] = 1 := by
    simp [Grid.xnorm, Fin.sum_univ_four, robGrid]
    norm_num
  have h4 : robGrid.vnorm (robY τ ε) = √(144 / 625 * τ ^ 2 + ε ^ 2) := by
    rw [Grid.vnorm]
    congr 1
    simp [Fin.sum_univ_three, robGrid, robY]
    ring
  have h5 : √(144 / 625 * τ ^ 2 + ε ^ 2) ≤ √2 * (12 / 25 * τ) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  have hE : 0 ≤ robGrid.fnorm A := Grid.fnorm_nonneg _
  rw [h2, h3, h4, abs_neg, abs_of_nonneg (by positivity), one_mul] at h1
  have hs2 : 0 < √2 := by positivity
  rw [div_le_iff₀ hs2]
  have h6 : 108 / 625 * τ ^ 2 ≤ √2 * (12 / 25 * τ) * robGrid.fnorm A :=
    h1.trans (mul_le_mul_of_nonneg_right h5 hE)
  have h7 : 12 / 25 * τ * (9 / 25 * τ) ≤ 12 / 25 * τ * (robGrid.fnorm A * √2) := by nlinarith
  exact le_of_mul_le_mul_left h7 (by positivity)

/-- **The format is not to blame** (arXiv 2101.12571, Sec. 6.2).  The Euler step of
`rob_local_error` is approximated up to `τ ε` by an admissible state of the same rank `2`, with
the same fixed function and the same `X`, and the only change being a new `W`.
So the error of `rob_local_error` is not caused by the low-rank format. -/
theorem rob_competitor {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ (W₁ : Matrix (Fin 3) Unit ℝ) (S₁ : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ),
      robGrid.IsState robU robX W₁ ∧
        robGrid.fnorm (robGrid.fNow robU robX S₁ W₁ - (robF ε + τ • robA ε)) ≤ τ * ε := by
  set N := √(ε ^ 2 + 18 / 25 * ε * τ + 9 / 25 * τ ^ 2) with hN
  have hN2 : N ^ 2 = ε ^ 2 + 18 / 25 * ε * τ + 9 / 25 * τ ^ 2 := Real.sq_sqrt (by positivity)
  have hN0 : 0 < N := Real.sqrt_pos.mpr (by positivity)
  set W₁ : Matrix (Fin 3) Unit ℝ :=
    Matrix.of fun v _ => (ε * ![1 / 15, -3 / 5, 31 / 15] v + τ * robVel v) / N with hW₁
  refine ⟨W₁, diagonal (Sum.elim (fun _ => 3) (fun _ => N)), ⟨rob_state.orthX, rob_state.orthU,
    ?_, ?_⟩, ?_⟩
  · ext i j
    simp [hW₁, robGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_three, robVel]
    field_simp
    rw [hN2]
    ring
  · ext i j
    simp [hW₁, robU, robGrid, Grid.Hv, Matrix.mul_apply, Fin.sum_univ_three, robVel]
    field_simp
    ring
  · have hent : ∀ x v, (robGrid.fNow robU robX (diagonal (Sum.elim (fun _ => 3) fun _ => N)) W₁ -
        (robF ε + τ • robA ε)) x v = robGrid.f0 v * (τ * ε) * ![1, 0, -1, 0] x * robVel v *
          ![1 / 15, -3 / 5, 31 / 15] v := by
      intro x v
      fin_cases x <;> fin_cases v <;>
        simp [Grid.fNow, Grid.dist, Grid.F, robGrid, robX, robU, robF, robA, robVel, vb, hW₁,
          Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply] <;> field_simp <;> ring
    rw [Grid.fnorm]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    simp only [hent]
    simp [Fin.sum_univ_three, Fin.sum_univ_four, robGrid, robVel]
    nlinarith [sq_nonneg (τ * ε)]

/-- **No uniform second-order local error bound** (arXiv 2101.12571, Sec. 6.2).  There is no
constant `C` such that the local error of the integrator of Sec. 6.2 is at most `C τ²` for all small
singular values `ε ≲ τ` of `S`.  Here `D`, `U`, `X`, the bound `‖S‖ ≤ 3` and the Lipschitz constant
of `D` are all fixed.  Compare `bug_local_error_le` for the unconventional integrator without
fixed functions. -/
theorem rob_no_uniform_bound : ¬ ∃ C : ℝ, ∀ τ ε : ℝ, 0 < τ → 0 < ε → ε ≤ 12 / 25 * τ →
    ∀ X' S' W', robGrid.IsStep robD τ robU robX (robS ε) robW X' S' W' →
      robGrid.fnorm (robGrid.fNow robU X' S' W' - (robF ε + τ • robD (robF ε))) ≤ C * τ ^ 2 := by
  rintro ⟨C, hC⟩
  set t : ℝ := 1 / (8 * (|C| + 1)) with ht
  have hC1 : 0 < |C| + 1 := by positivity
  have ht0 : 0 < t := by positivity
  have hε : 0 < 12 / 25 * t := by positivity
  obtain ⟨X', S', W', h⟩ := Grid.exists_step rob_state robD t (robS (12 / 25 * t))
    (by simp) (by simp)
  have h1 := rob_local_error ht0 hε le_rfl h
  have h2 := hC t _ ht0 hε le_rfl X' S' W' h
  rw [rob_D] at h2
  have hCt : C * t ≤ 1 / 8 := by
    have : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le
    have h3 : |C| * t ≤ 1 / 8 := by
      rw [ht]
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hs : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hs0 : 0 < √2 := by positivity
  have h4 : 9 / 25 * t / √2 ≤ C * t ^ 2 := h1.trans h2
  rw [div_le_iff₀ hs0] at h4
  have h5 : C * t ^ 2 * √2 ≤ t * (1 / 8) * (3 / 2) := by
    have : C * t ^ 2 = t * (C * t) := by ring
    rw [this]
    have h6 : t * (C * t) ≤ t * (1 / 8) := mul_le_mul_of_nonneg_left hCt ht0.le
    calc t * (C * t) * √2 ≤ t * (1 / 8) * √2 := mul_le_mul_of_nonneg_right h6 hs0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  nlinarith

/-! ### Mass is also lost with a dynamic `W` -/

lemma rob_density_one (f : Matrix (Fin 4) (Fin 3) ℝ) :
    robGrid.density 1 (robD f) = -(1 : ℝ) • (vpDx *ᵥ robGrid.density robVel f) := by
  ext x
  fin_cases x <;>
    simp [Grid.density, robD, vlasovRHS, robGrid, robVel, vpDx, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

lemma rob_ipx (u w : Fin 4 → ℝ) :
    robGrid.ipx u w = (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3) / 2 := by
  simp only [Grid.ipx, Fin.sum_univ_four, robGrid]
  ring

/-- Free streaming conserves the mass exactly on the grid (arXiv 2101.12571, Sec. 6.1). -/
theorem rob_mass_conservative (f : Matrix (Fin 4) (Fin 3) ℝ) :
    robGrid.charge 1 1 (robD f) = 0 := by
  rw [Grid.charge, rob_density_one, rob_ipx]
  generalize robGrid.density robVel f = r
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1, vpDx2, vpDx3]
  ring

/-- `Kⁿ⁺¹` of the example with `τ = 1`, `ε = 16/25`. -/
noncomputable def robK : Matrix (Fin 4) (Unit ⊕ Unit) ℝ :=
  Matrix.of fun x j => Sum.elim (fun _ => ![1731 / 625, 2, 769 / 625, 2] x)
    (fun _ => ![-1536 / 3125, 1, 1536 / 3125, -1] x) j

lemma rob_kNext :
    robGrid.kNext 1 robX (robS (16 / 25)) (vb robU robW) (robA (16 / 25)) = robK := by
  ext x j
  rcases j with j | j <;> fin_cases x <;>
    simp [Grid.kNext, Grid.pairV, Grid.Hu, robGrid, robX, robS, robU, robW, robA, robK, robVel, vb,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
    norm_num

/-- A left inverse of `robK`. -/
noncomputable def robC : Matrix (Unit ⊕ Unit) (Fin 4) ℝ :=
  Matrix.of fun j x => Sum.elim (fun _ => ![0, 1 / 4, 0, 1 / 4] x)
    (fun _ => ![0, 1 / 2, 0, -1 / 2] x) j

lemma robC_mul : robC * robK = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [robC, robK, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

variable {X' : Matrix (Fin 4) (Unit ⊕ Unit) ℝ} {S' : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ}
  {W' : Matrix (Fin 3) Unit ℝ} {R : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ}

lemma rob_proj (hX : X'ᵀ * robGrid.Hx * X' = 1) (hK : robK = X' * R) {y z : Fin 4 → ℝ}
    (w : Unit ⊕ Unit → ℝ) (hz : z = robK *ᵥ w)
    (horth : robKᵀ *ᵥ (robGrid.Hx *ᵥ (y - z)) = 0) : robGrid.projX X' *ᵥ y = z :=
  Grid.projX_mulVec_eq rfl hX hK robC_mul w hz horth

lemma rob_proj_one (hX : X'ᵀ * robGrid.Hx * X' = 1) (hK : robK = X' * R) :
    robGrid.projX X' *ᵥ 1 = ![42353956 / 34261131, 111775688 / 102783393, 66936868 / 102783393,
      82223048 / 102783393] := by
  refine rob_proj hX hK (Sum.elim (fun _ => 48499684 / 102783393)
    (fun _ => 4925440 / 34261131)) ?_ ?_
  · ext x
    fin_cases x <;> simp [robK, mulVec, dotProduct, Fintype.sum_sum_type] <;> norm_num
  · ext j
    rcases j with j | j <;>
      simp [robK, robGrid, Grid.Hx, mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

lemma rob_proj_sin (hX : X'ᵀ * robGrid.Hx * X' = 1) (hK : robK = X' * R) :
    robGrid.projX X' *ᵥ ![0, 1, 0, -1] = ![-3445760 / 11420377, 30432395 / 34261131,
      15262720 / 34261131, -25506955 / 34261131] := by
  refine rob_proj hX hK (Sum.elim (fun _ => 1231360 / 34261131)
    (fun _ => 9323225 / 11420377)) ?_ ?_
  · ext x
    fin_cases x <;> simp [robK, mulVec, dotProduct, Fintype.sum_sum_type] <;> norm_num
  · ext j
    rcases j with j | j <;>
      simp [robK, robGrid, Grid.Hx, mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

/-- `fⁿ` of the example is positive for `0 ≤ ε ≤ 16/25` (arXiv 2101.12571, Sec. 7: positive
initial data). -/
theorem robF_pos {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 16 / 25) (x : Fin 4) (v : Fin 3) :
    0 < robF ε x v := by
  refine mul_pos (robGrid.f0_pos v) ?_
  fin_cases x <;> fin_cases v <;> norm_num <;> linarith

/-- **Mass is lost also when `W` really moves** (arXiv 2101.12571, Sec. 6.2).  For free streaming,
which conserves mass exactly on the grid (`rob_mass_conservative`), and the configuration
`m = 1`, `r = 2` with `U₁ = 1`, one dynamic `W`, the positive `fⁿ` of `robF` with
`S = diag(3, 16/25)`, and `τ = 1`, every step changes the mass by exactly `-215488/11420377`. -/
theorem rob_mass_change (h : robGrid.IsStep robD 1 robU robX (robS (16 / 25)) robW X' S' W') :
    robGrid.charge 1 1 (robGrid.fNow robU X' S' W') -
        robGrid.charge 1 1 (robGrid.fNow robU robX (robS (16 / 25)) robW) =
      -(215488 / 11420377) := by
  obtain ⟨R, hR⟩ := h.qrK
  rw [rob_dist, rob_D, rob_kNext] at hR
  have hX := h.state.orthX
  have p1 := rob_proj_one hX hR
  have ps := rob_proj_sin hX hR
  obtain ⟨R₂, hR₂⟩ := h.qrL
  rw [rob_dist, rob_D, rob_lNext] at hR₂
  set r₀ := R₂ () () with hr₀
  have hent : ∀ v, robL 1 (16 / 25) v () = W' v () * r₀ := by
    intro v
    rw [hR₂]
    simp [Matrix.mul_apply, hr₀]
  have e0 : W' 0 () * r₀ = -5888 / 9375 := by
    rw [← hent 0]; simp [robL]; norm_num
  have e1 : W' 1 () * r₀ = -336 / 3125 := by
    rw [← hent 1]; simp [robL]; norm_num
  have e2 : W' 2 () * r₀ = 9472 / 9375 := by
    rw [← hent 2]; simp [robL]; norm_num
  have hW : 9 / 50 * W' 0 () ^ 2 + 16 / 25 * W' 1 () ^ 2 + 9 / 50 * W' 2 () ^ 2 = 1 := by
    have := congrFun (congrFun h.state.orthW ()) ()
    simp [Matrix.mul_apply, Grid.Hv, robGrid, Fin.sum_univ_three] at this
    linarith
  have hUW : 9 / 50 * W' 0 () + 16 / 25 * W' 1 () + 9 / 50 * W' 2 () = 0 := by
    have := congrFun (congrFun h.state.orthUW ()) ()
    simp [Matrix.mul_apply, Grid.Hv, robGrid, robU, Fin.sum_univ_three] at this
    linarith
  have hr2 : r₀ ^ 2 = 4096 / 15625 := by
    have e : r₀ ^ 2 = 9 / 50 * (W' 0 () * r₀) ^ 2 + 16 / 25 * (W' 1 () * r₀) ^ 2 +
        9 / 50 * (W' 2 () * r₀) ^ 2 := by linear_combination (-r₀ ^ 2) * hW
    rw [e, e0, e1, e2]
    norm_num
  have hr0 : r₀ ^ 2 ≠ 0 := by rw [hr2]; norm_num
  set ν : ℝ := 9 / 50 * (W' 2 () - W' 0 ()) with hν
  set κ : ℝ := 9 / 50 * (W' 0 () * (1 / 15)) + 16 / 25 * (W' 1 () * (-3 / 5)) +
    9 / 50 * (W' 2 () * (31 / 15)) with hκ
  have hνr : ν * r₀ = 4608 / 15625 := by
    rw [hν]; linear_combination (9 / 50) * e2 - (9 / 50) * e0
  have hκr : κ * r₀ = 256 / 625 := by
    rw [hκ]
    linear_combination (9 / 50 * (1 / 15)) * e0 + (16 / 25 * (-3 / 5)) * e1 +
      (9 / 50 * (31 / 15)) * e2
  have hνκ : ν * κ = 288 / 625 := by
    have : (ν * κ - 288 / 625) * r₀ ^ 2 = 0 := by
      have h1 : ν * κ * r₀ ^ 2 = (ν * r₀) * (κ * r₀) := by ring
      rw [sub_mul, h1, hνr, hκr, hr2]
      norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hr0)
  have hy : vb robU W' *ᵥ ((vb robU W')ᵀ *ᵥ (robGrid.Hv *ᵥ robVel)) = fun v => ν * W' v () := by
    ext v
    rw [hν]
    simp [mulVec, dotProduct, vb, Grid.Hv, robGrid, robU, robVel, Fin.sum_univ_three,
      Fintype.sum_sum_type, diagonal_apply]
    ring
  have hdens : robGrid.density (fun v => ν * W' v ()) (robF (16 / 25)) =
      (ν * κ * (16 / 25)) • ![0, 1, 0, -1] := by
    have hκ' := hκ
    ext x
    fin_cases x
    · simp [Grid.density, robF, robGrid, Fin.sum_univ_three]
      linear_combination (3 * ν) * hUW
    · simp [Grid.density, robF, robGrid, Fin.sum_univ_three]
      linear_combination (2 * ν) * hUW - (16 / 25 * ν) * hκ'
    · simp [Grid.density, robF, robGrid, Fin.sum_univ_three]
      linear_combination ν * hUW
    · simp [Grid.density, robF, robGrid, Fin.sum_univ_three]
      linear_combination (2 * ν) * hUW + (16 / 25 * ν) * hκ'
  have hvel0 : robGrid.density robVel (robF (16 / 25)) = (144 / 625 : ℝ) • ![0, 1, 0, -1] := by
    ext x
    fin_cases x <;> simp [Grid.density, robF, robGrid, robVel, Fin.sum_univ_three] <;> norm_num
  have hvelt : robGrid.density robVel (robGrid.fStart robU robX (robS (16 / 25)) robW X' W') =
      (4608 / 15625 : ℝ) • (robGrid.projX X' *ᵥ ![0, 1, 0, -1]) := by
    have := Grid.density_fStart_general (q := robGrid) robU robX (robS (16 / 25)) robW X' W'
      robVel
    rw [hy, Grid.fNow, rob_dist, hdens, hνκ, mulVec_smul] at this
    rw [this]
    norm_num
  have hone : robU *ᵥ (fun _ => 1) = 1 := by
    ext v
    simp [robU, mulVec, dotProduct]
  have hch := h.charge_sub rob_state (fun _ => 1) (c := 1)
    (by rw [hone]; exact rob_mass_conservative)
  rw [hone] at hch
  rw [hch, rob_density_one, rob_density_one, Grid.fNow, rob_dist, hvelt, hvel0, ps, p1, rob_ipx]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, vpDx0, vpDx1, vpDx2, vpDx3]
  simp
  norm_num

end Robust

/-! ### The moments and the Vlasov right-hand side in the core vocabulary

The moment `∫ ζ f dv` of the grid is the core quadrature moment for the velocity weights `q.wv`,
and the discrete Vlasov right-hand side with a frozen field value is an instance of the core
operator `Kinetic.streaming`. The local definitions stay: they are the core notions at the
fields of the structure `Grid`. -/

section KineticCore

open scoped LeanDLRA.Frobenius

/-- The moment `∫ ζ f dv` of the grid is the core quadrature moment for the velocity weights
`q.wv`. -/
theorem Grid.density_eq_quadMoment {Mx Mv : Type*} [Fintype Mv] (q : Grid Mx Mv) (ζ : Mv → ℝ)
    (f : Matrix Mx Mv ℝ) : q.density ζ f = Kinetic.quadMoment q.wv ζ f :=
  rfl

/-- For `ζ = 1` the moment of the grid is the core density. -/
theorem Grid.density_one_eq_density {Mx Mv : Type*} [Fintype Mv] (q : Grid Mx Mv)
    (f : Matrix Mx Mv ℝ) : q.density 1 f = Kinetic.density q.wv f :=
  rfl

/-- **The Vlasov right-hand side through the core**: at a given `f`, with the field value `E[f]`,
`D[f] = -v ∂ₓ f + E[f] ∂ᵥ f` is the core streaming operator `Y ↦ ∑ₖ Dₖ Y Mₖ` applied to `f`, with
the two terms `(-dx, diag v)` and `(diag E[f], dvᵀ)`. The field depends on `f`, so this is a
statement about the value at `f`, not about linearity of `f ↦ D[f]`. -/
theorem vlasovRHS_eq_streaming {Mx Mv : Type*} [Fintype Mx] [Fintype Mv] [DecidableEq Mx]
    [DecidableEq Mv] (vel : Mv → ℝ) (dx : Matrix Mx Mx ℝ) (dv : Matrix Mv Mv ℝ)
    (E : Matrix Mx Mv ℝ → Mx → ℝ) (f : Matrix Mx Mv ℝ) :
    vlasovRHS vel dx dv E f
      = Kinetic.streaming ![-dx, diagonal (E f)] ![diagonal vel, dvᵀ] f := by
  rw [Kinetic.streaming_apply, Fin.sum_univ_two]
  ext x v
  change -(vel v * (dx * f) x v) + E f x * (f * dvᵀ) x v
    = (-dx * f * diagonal vel + diagonal (E f) * f * dvᵀ) x v
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.neg_mul, Matrix.neg_apply,
    Matrix.mul_assoc (diagonal (E f)), Matrix.diagonal_mul]
  ring

/-- The moment bridges at nonzero data: on `vpGrid` (velocity weights `1/2`) the profile `(0, 1)`
has the core moment `1` against the velocities `v = ∓2` and the core density `1/2`. -/
example :
    Kinetic.quadMoment vpGrid.wv vpVel (Matrix.of fun _ : Fin 4 => ![0, 1]) 0 = 1 ∧
      Kinetic.density vpGrid.wv (Matrix.of fun _ : Fin 4 => ![0, 1]) 0 = 1 / 2 := by
  rw [← Grid.density_eq_quadMoment, ← Grid.density_one_eq_density]
  norm_num [Grid.density, vpGrid, vpVel, Fin.sum_univ_two, Matrix.of_apply]

/-- The streaming bridge at nonzero data: the discrete Vlasov-Poisson right-hand side `vpD` at
`f` is the core streaming operator with the centred difference `vpDx`, the velocities `∓2`, the
field value `vpE f` and the velocity derivative `vpDv`. -/
example (f : Matrix (Fin 4) (Fin 2) ℝ) :
    vpD f = Kinetic.streaming ![-vpDx, diagonal (vpE f)] ![diagonal vpVel, vpDvᵀ] f :=
  vlasovRHS_eq_streaming vpVel vpDx vpDv vpE f

end KineticCore

end LeanDLRA.Literature.P2101_12571
