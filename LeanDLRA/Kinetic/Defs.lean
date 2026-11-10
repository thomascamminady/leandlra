import LeanDLRA.LinearAlgebra.Frobenius.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Kinetic equations: definitions

The vocabulary of the kinetic layer. A kinetic density `f(x, v)` on a phase-space grid is stored
as a matrix `f : Matrix X V ℝ` (rows = space nodes, columns = velocity nodes); on a continuous
phase space it is a function `f : 𝒳 → 𝒱 → ℝ`. Dynamical low-rank approximation writes it as
`f = X S Vᵀ` (`lowRankAnsatz`).

## Main definitions

* `Kinetic.PhaseGrid X V`: positive quadrature weights `wx`, `wv` on the space and velocity
  nodes.
* `Kinetic.quadMoment w ζ f`, `Kinetic.density w f`: the discrete velocity moments
  `x ↦ ∑ᵥ w v * ζ v * f x v` and the density (`ζ = 1`); `Kinetic.velocityMoment ν ζ f`: the
  continuous moment `x ↦ ∫ ζ(v) f(x, v) dν(v)`.
* `Kinetic.streaming D M`: the streaming (transport) operator `Y ↦ ∑ₖ D k * Y * M k`.
* `Kinetic.lowRankAnsatz w X S V`: the ansatz `w(v) ∑ᵢⱼ Xᵢ(x) Sᵢⱼ Vⱼ(v)`;
  `Kinetic.IsOrthonormalWrt ν V`: orthonormality of a velocity basis in `L²(ν)`.
* `Kinetic.fwdDiff`, `Kinetic.bwdDiff`, `Kinetic.centralDiff`, `Kinetic.secondDiff`: periodic
  difference matrices on `ZMod N`, with their action `*ᵥ` on grid functions.
* `Kinetic.maxwellian R ρ T u v`: the Maxwellian on `ℝ^ι`.

`LeanDLRA.Novel.EpsRank.Quadrature` (velocity nodes and positive weights of total mass one) is
defined here as well and keeps the name of the file in which it was first stated.

## Main results

* `Kinetic.quadMoment_eq_mulVec`, `Kinetic.density_eq_mulVec`: a quadrature moment is the
  matrix–vector product `f *ᵥ (w * ζ)`, the density is `f *ᵥ w`.
* `Kinetic.velocityMoment_sum_smul_dirac`: for the discrete measure `∑ᵥ w v • δᵥ` the continuous
  moment is the quadrature moment.
* `Kinetic.lowRankAnsatz_one_eq_mul`: without weight the ansatz is the matrix product `Xᵀ S V`.
* `Kinetic.centralDiff_eq`, `Kinetic.secondDiff_eq`: `D⁰ = (D⁺ + D⁻) / 2` and
  `D² = (D⁺ - D⁻) / h`.
-/

/-! ### Velocity quadratures -/

namespace LeanDLRA.Novel.EpsRank

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

/-- A velocity quadrature: nodes `μ_v` and positive weights `w_v` of total mass one, so that
`⟨g⟩ = ∑_v w_v g_v` is the normalised velocity average. -/
structure Quadrature (V : Type*) [Fintype V] where
  /-- the nodes -/
  μ : V → ℝ
  /-- the weights -/
  w : V → ℝ
  w_pos : ∀ v, 0 < w v
  sum_w : ∑ v, w v = 1

end LeanDLRA.Novel.EpsRank

/-! ### Phase-space grids -/

namespace LeanDLRA.Kinetic

open MeasureTheory
open scoped Matrix

/-- A **phase-space grid**: quadrature weights `wx` on the spatial nodes `X` and `wv` on the
velocity nodes `V`, both positive, so that `∫ u dx ≈ ∑ₓ wx x * u x` and
`∫ g dv ≈ ∑ᵥ wv v * g v`. The weighted inner product of two phase-space matrices is
`Frobenius.weightedInner wx wv`. Unlike `Novel.EpsRank.Quadrature` the velocity weights need not
sum to one and no velocity nodes are stored. -/
structure PhaseGrid (X V : Type*) where
  /-- The spatial quadrature weights. -/
  wx : X → ℝ
  /-- The velocity quadrature weights. -/
  wv : V → ℝ
  /-- The spatial weights are positive. -/
  wx_pos : ∀ x, 0 < wx x
  /-- The velocity weights are positive. -/
  wv_pos : ∀ v, 0 < wv v

/-- A grid with two cells of width `1/2` and three velocities of weight `1/3`. -/
example : Nonempty (PhaseGrid (Fin 2) (Fin 3)) :=
  ⟨⟨fun _ => 1 / 2, fun _ => 1 / 3, fun _ => by norm_num, fun _ => by norm_num⟩⟩

/-! ### Velocity moments -/

section QuadMoment

variable {X V : Type*} [Fintype V]

/-- The **quadrature moment** of a phase-space function `f : X × V → ℝ` (stored as a matrix,
rows = space, columns = velocity) for the velocity weights `w` and the velocity function `ζ`:
`quadMoment w ζ f x = ∑ᵥ w v * ζ v * f x v`, the discrete form of `∫ ζ(v) f(x, v) dv`.
For `ζ = 1` it is the density, for `ζ = vₐ` the current (momentum) and for `ζ = |v|²/2` the
kinetic energy density. -/
def quadMoment (w ζ : V → ℝ) (f : Matrix X V ℝ) : X → ℝ := fun x => ∑ v, w v * ζ v * f x v

/-- The **density** `ρ(x) = ∑ᵥ w v * f x v` of a phase-space matrix `f`: the quadrature moment
with `ζ = 1`. -/
def density (w : V → ℝ) (f : Matrix X V ℝ) : X → ℝ := quadMoment w 1 f

theorem quadMoment_apply (w ζ : V → ℝ) (f : Matrix X V ℝ) (x : X) :
    quadMoment w ζ f x = ∑ v, w v * ζ v * f x v := rfl

theorem density_apply (w : V → ℝ) (f : Matrix X V ℝ) (x : X) :
    density w f x = ∑ v, w v * f x v := by
  simp [density, quadMoment]

/-- A quadrature moment is a matrix–vector product: `quadMoment w ζ f = f *ᵥ (w * ζ)`. -/
theorem quadMoment_eq_mulVec (w ζ : V → ℝ) (f : Matrix X V ℝ) :
    quadMoment w ζ f = f *ᵥ (w * ζ) := by
  ext x
  simp only [quadMoment, Matrix.mulVec, dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- The density is the matrix–vector product of `f` with the weights. -/
theorem density_eq_mulVec (w : V → ℝ) (f : Matrix X V ℝ) : density w f = f *ᵥ w := by
  rw [density, quadMoment_eq_mulVec, mul_one]

/-- Two velocities of weight `1/2` and the values `1, 3` in one cell: the density is `2`. -/
example : density ![(1 : ℝ) / 2, 1 / 2] (!![1, 3] : Matrix (Fin 1) (Fin 2) ℝ) 0 = 2 := by
  rw [density_apply, Fin.sum_univ_two]
  norm_num

end QuadMoment

section VelocityMoment

variable {𝒳 𝒱 : Type*} [MeasurableSpace 𝒱]

/-- The **velocity moment** `x ↦ ∫ ζ(v) f(x, v) dν(v)` of a phase-space function `f` for a
measure `ν` on the velocity space: the continuous counterpart of `quadMoment` (a finite sum of
weighted Dirac masses gives back the quadrature form, `velocityMoment_sum_smul_dirac`). -/
noncomputable def velocityMoment (ν : Measure 𝒱) (ζ : 𝒱 → ℝ) (f : 𝒳 → 𝒱 → ℝ) : 𝒳 → ℝ :=
  fun x => ∫ v, ζ v * f x v ∂ν

theorem velocityMoment_apply (ν : Measure 𝒱) (ζ : 𝒱 → ℝ) (f : 𝒳 → 𝒱 → ℝ) (x : 𝒳) :
    velocityMoment ν ζ f x = ∫ v, ζ v * f x v ∂ν := rfl

/-- Against the Dirac mass at `v = 2`, the first moment of `f(x, v) = v` is `2 * 2 = 4`. -/
example : velocityMoment (Measure.dirac (2 : ℝ)) id (fun (_ : Unit) v => v) () = 4 := by
  rw [velocityMoment_apply, integral_dirac]
  norm_num

/-- **The quadrature moment is a velocity moment.** For the discrete measure `∑ᵥ w v • δᵥ` on a
finite set of velocities, the velocity moment of `f` is the quadrature moment of the matrix
`Matrix.of f` with the weights `w`. -/
theorem velocityMoment_sum_smul_dirac {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (w : V → NNReal) (ζ : V → ℝ) (f : 𝒳 → V → ℝ) :
    velocityMoment (∑ v, w v • Measure.dirac v) ζ f =
      quadMoment (fun v => (w v : ℝ)) ζ (Matrix.of f) := by
  ext x
  rw [velocityMoment_apply, quadMoment_apply,
    integral_finsetSum_measure fun v _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul, Matrix.of_apply]
  ring

end VelocityMoment

/-! ### The streaming operator -/

section Streaming

open scoped LeanDLRA.Frobenius

variable {X V κ : Type*} [Fintype X] [Fintype V] [Fintype κ]

/-- The **streaming operator** `Y ↦ ∑ₖ D k * Y * M k` on phase-space matrices `Y` (rows = space,
columns = velocity): the space-discretized transport term `v · ∇ₓ f` in which every term is a
spatial difference matrix `D k` acting from the left and a velocity matrix `M k` (typically the
diagonal of the `k`-th velocity component) acting from the right. One-dimensional transport
`D Y diag(μ)` is a single term, upwind splittings `D⁻ Y A⁺ + D⁺ Y A⁻` have two. -/
noncomputable def streaming (D : κ → Matrix X X ℝ) (M : κ → Matrix V V ℝ) :
    Matrix X V ℝ →L[ℝ] Matrix X V ℝ :=
  ∑ k, Frobenius.sandwichCLM (D k) (M k)

theorem streaming_apply (D : κ → Matrix X X ℝ) (M : κ → Matrix V V ℝ) (Y : Matrix X V ℝ) :
    streaming D M Y = ∑ k, D k * Y * M k := by
  simp [streaming]

/-- One term: the swap matrix from the left and `diag(1, -1)` from the right. -/
example : streaming (fun _ : Unit => !![(0 : ℝ), 1; 1, 0]) (fun _ => !![(1 : ℝ), 0; 0, -1])
    !![1, 0; 0, 0] = !![0, 0; 1, 0] := by
  rw [streaming_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Streaming

/-! ### Low-rank ansatz and orthonormal velocity bases -/

section LowRank

variable {𝒳 𝒱 ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The **low-rank ansatz** `f(x, v) = w(v) ∑ᵢ ∑ⱼ Xᵢ(x) Sᵢⱼ Vⱼ(v)` with spatial basis functions
`X i`, coefficient matrix `S`, velocity basis functions `V j` and a velocity weight `w` (a
background Maxwellian `f₀`, or `1` for the plain ansatz `f = ∑ Xᵢ Sᵢⱼ Vⱼ`). -/
def lowRankAnsatz (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ) (S : Matrix ι κ ℝ) (V : κ → 𝒱 → ℝ) :
    𝒳 → 𝒱 → ℝ :=
  fun x v => w v * ∑ i, ∑ j, X i x * S i j * V j v

theorem lowRankAnsatz_apply (w : 𝒱 → ℝ) (X : ι → 𝒳 → ℝ) (S : Matrix ι κ ℝ)
    (V : κ → 𝒱 → ℝ) (x : 𝒳) (v : 𝒱) :
    lowRankAnsatz w X S V x v = w v * ∑ i, ∑ j, X i x * S i j * V j v := rfl

/-- With `w = 1` and `S = 1` the ansatz is `∑ⱼ Xⱼ(x) Vⱼ(v)`. -/
theorem lowRankAnsatz_one_one [DecidableEq ι] (X : ι → 𝒳 → ℝ) (V : ι → 𝒱 → ℝ) (x : 𝒳)
    (v : 𝒱) : lowRankAnsatz 1 X 1 V x v = ∑ j, X j x * V j v := by
  simp [lowRankAnsatz, Matrix.one_apply]

/-- **The ansatz is the factorization `Xᵀ S V`.** Without weight, and with the basis functions
stored as the rows of the matrices `X` and `V`, the low-rank ansatz is the matrix product
`Xᵀ * S * V` entry by entry, i.e. the factored form `U S Vᵀ` of a low-rank matrix with
`U = Xᵀ` and the transposed velocity basis. -/
theorem lowRankAnsatz_one_eq_mul (X : Matrix ι 𝒳 ℝ) (S : Matrix ι κ ℝ) (V : Matrix κ 𝒱 ℝ)
    (x : 𝒳) (v : 𝒱) : lowRankAnsatz 1 X S V x v = (X.transpose * S * V) x v := by
  simp only [lowRankAnsatz, Pi.one_apply, one_mul, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/-- A rank-one example: `f(x, v) = x v` at `(2, 3)`. -/
example : lowRankAnsatz (fun _ => 1) (fun (_ : Fin 1) (x : ℝ) => x) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ v => v) 2 3 = 6 := by
  rw [lowRankAnsatz_apply]
  norm_num

end LowRank

section Orthonormal

variable {𝒱 ι : Type*} [MeasurableSpace 𝒱] [DecidableEq ι]

/-- The functions `V i` form an **orthonormal family in `L²(ν)`**: each is square integrable and
`∫ V i V j dν = δᵢⱼ`. With `ν` the Lebesgue measure on `[-1, 1]` this is the orthonormality of a
Legendre-type velocity basis, with `ν = w • λ` that of a weighted basis. -/
structure IsOrthonormalWrt (ν : Measure 𝒱) (V : ι → 𝒱 → ℝ) : Prop where
  /-- Every `V i` is in `L²(ν)`. -/
  memLp : ∀ i, MemLp (V i) 2 ν
  /-- The Gram matrix is the identity. -/
  inner_eq : ∀ i j, ∫ v, V i v * V j v ∂ν = if i = j then 1 else 0

/-- The constant function `1` is orthonormal for a probability measure (here a Dirac mass). -/
example : IsOrthonormalWrt (Measure.dirac (0 : ℝ)) (fun (_ : Fin 1) (_ : ℝ) => (1 : ℝ)) where
  memLp _ := memLp_const 1
  inner_eq i j := by simp [Subsingleton.elim i j]

end Orthonormal

/-! ### Periodic difference matrices -/

section Stencils

/-- The periodic **forward difference** `(D⁺ φ)ᵢ = (φᵢ₊₁ - φᵢ) / h` on `N` cells, as a matrix on
`ZMod N` (indices are taken modulo `N`). -/
noncomputable def fwdDiff (N : ℕ) (h : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun i j => ((if j = i + 1 then 1 else 0) - (if j = i then 1 else 0)) / h

/-- The periodic **backward difference** `(D⁻ φ)ᵢ = (φᵢ - φᵢ₋₁) / h` on `N` cells. -/
noncomputable def bwdDiff (N : ℕ) (h : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun i j => ((if j = i then 1 else 0) - (if j = i - 1 then 1 else 0)) / h

/-- The periodic **central difference** `(D⁰ φ)ᵢ = (φᵢ₊₁ - φᵢ₋₁) / (2 h)` on `N` cells. -/
noncomputable def centralDiff (N : ℕ) (h : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun i j => ((if j = i + 1 then 1 else 0) - (if j = i - 1 then 1 else 0)) / (2 * h)

/-- The periodic **second difference** `(D² φ)ᵢ = (φᵢ₊₁ - 2 φᵢ + φᵢ₋₁) / h²` on `N` cells. Schemes
with numerical viscosity use `(h / 2) • secondDiff N h`, i.e. the denominator `2 h`. -/
noncomputable def secondDiff (N : ℕ) (h : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun i j =>
    ((if j = i + 1 then 1 else 0) - 2 * (if j = i then 1 else 0) + (if j = i - 1 then 1 else 0)) /
      h ^ 2

/-- The central difference is the mean of the forward and the backward difference. -/
theorem centralDiff_eq (N : ℕ) (h : ℝ) :
    centralDiff N h = (1 / 2 : ℝ) • (fwdDiff N h + bwdDiff N h) := by
  ext i j
  simp only [centralDiff, fwdDiff, bwdDiff, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

/-- The second difference is the difference quotient of the forward and the backward
difference. -/
theorem secondDiff_eq (N : ℕ) (h : ℝ) :
    secondDiff N h = (1 / h) • (fwdDiff N h - bwdDiff N h) := by
  ext i j
  simp only [secondDiff, fwdDiff, bwdDiff, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

variable {N : ℕ} [NeZero N] {h : ℝ}

theorem fwdDiff_mulVec (φ : ZMod N → ℝ) : fwdDiff N h *ᵥ φ = fun i => (φ (i + 1) - φ i) / h := by
  ext i
  simp [fwdDiff, Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

theorem bwdDiff_mulVec (φ : ZMod N → ℝ) : bwdDiff N h *ᵥ φ = fun i => (φ i - φ (i - 1)) / h := by
  ext i
  simp [bwdDiff, Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

theorem centralDiff_mulVec (φ : ZMod N → ℝ) :
    centralDiff N h *ᵥ φ = fun i => (φ (i + 1) - φ (i - 1)) / (2 * h) := by
  ext i
  simp [centralDiff, Matrix.mulVec, dotProduct, sub_div, sub_mul, ite_mul, div_mul_eq_mul_div,
    ← Finset.sum_div]

theorem secondDiff_mulVec (φ : ZMod N → ℝ) :
    secondDiff N h *ᵥ φ = fun i => (φ (i + 1) - 2 * φ i + φ (i - 1)) / h ^ 2 := by
  ext i
  simp [secondDiff, Matrix.mulVec, dotProduct, add_div, sub_div, add_mul, sub_mul, ite_mul,
    div_mul_eq_mul_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]

/-- On three cells with `h = 1/2` the forward difference matrix has the wrap-around entry
`D⁺(2, 0) = 1 / h = 2` (the right neighbour of cell `2` is cell `0`). -/
example : fwdDiff 3 (1 / 2) 2 0 = 2 := by
  rw [fwdDiff, Matrix.of_apply, ite_eq_left (by decide), ite_eq_right (by decide)]
  norm_num

end Stencils

/-! ### Maxwellians -/

section Maxwellian

variable {ι : Type*} [Fintype ι]

/-- The **Maxwellian** with gas constant `R`, density `ρ`, temperature `T` and mean velocity `u`
on the velocity space `ℝ^ι`:
`M(v) = ρ / (2π R T)^{|ι|/2} * exp (-|v - u|² / (2 R T))`. For `R = T = 1` it is
`ρ (2π)^{-|ι|/2} exp (-|v - u|² / 2)`. -/
noncomputable def maxwellian (R ρ T : ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  ρ / (2 * Real.pi * R * T) ^ ((Fintype.card ι : ℝ) / 2) * Real.exp (-‖v - u‖ ^ 2 / (2 * R * T))

theorem maxwellian_pos {R ρ T : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hT : 0 < T)
    (u v : EuclideanSpace ℝ ι) : 0 < maxwellian R ρ T u v := by
  unfold maxwellian; positivity

/-- In one dimension, with `R = 1` and `T = 1 / (2π)`, the Maxwellian of density `1` at its mean
velocity is `1`. -/
example : maxwellian (ι := Fin 1) 1 1 (1 / (2 * Real.pi)) 0 0 = 1 := by
  have h : 2 * Real.pi * 1 * (1 / (2 * Real.pi)) = 1 := by field_simp
  rw [maxwellian, h]
  simp

end Maxwellian

end LeanDLRA.Kinetic
