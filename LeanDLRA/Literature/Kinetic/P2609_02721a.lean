import LeanDLRA.Classical.SVD
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Energy

/-!
# Stable rank-adaptive step-and-truncate finite volumes for Vlasov (arXiv 2609.02721)

Uschmajew and Zeiser, *A stable rank-adaptive step-and-truncate finite volume method for Vlasov
transport on domains with piecewise linear boundaries*.  This module proves the theorems of the
paper for the actual scheme, not for an abstract model: `FVMesh.lemmaA1_stable` and
`FVMesh.tauCFL_pos` (Lemma A.1, `L²` stability of the forward Euler finite volume scheme (A.1) on a
finite polyhedral mesh, by the convex combination argument, with `τ_CFL` as in (A.2) valued in `(0,
∞]`); `integral_sq_tensorFn` (`‖u_h‖_{L²} = ‖U‖_F`), `tensorL_apply`, `tensorInflow_apply` (the
matrices `C_s, D, B_{μ,s}, M_b, G` of (2.10), defined entrywise as in the paper, give exactly the
finite volume cell balance on the product mesh), `tensorL_eq_kron` and `kron_isLipschitzField`
(Kronecker-structured affine, globally Lipschitz field); `VlasovFV.lemma41_stable` (Lemma 4.1),
`VlasovFV.theorem42_stable` (Theorem 4.2), `VlasovFV.theorem43_error` (Theorem 4.3) and
`VlasovFV.tolerance_scaling` (the first-order corollary), for Algorithm 2 (`IsSATStep`) with
truncated SVDs (`IsTruncSVD`), which are shown to exist (`exists_isSATStep`, `exists_satSequence`).
Differences from the paper.  Mathlib has no polytopes and no surface measures, so a mesh
(`PolyMesh`) consists of disjoint measurable cells of given volume and of combinatorial faces with
given areas and normals, and integrals over a face `e × K₂` are written as `|e|` times the cell
mean over `K₂`, which is their value since the normal is constant on `e` and the transport speed
does not depend on the point of `e`.  The one geometric fact used, the closure relation `∑_{e ⊂ ∂K}
|e| n_{K,e} = 0` of a polytope, is a field of `PolyMesh` (it is the divergence theorem for constant
fields); from it the discrete divergence-free identity (A.4), which is a hypothesis of Lemma A.1 on
a general mesh, is *derived* for the product mesh (`tensorCoeff_admissible`), as are the bounds
`|a_e| ≤ b_e`, so the hypotheses of the main theorems are the regularity assumptions
`VlasovFV.IsRegular` only.  The scheme is the one of (2.10): global Lax–Friedrichs on interior
faces and upwind on boundary faces; Lemma A.1 itself covers all fluxes with `|a_e| ≤ b_e`, so also
the upwind and local Lax–Friedrichs fluxes.  Truncated SVDs are specified by their singular-triplet
equations and the tolerance, so the theorems hold for every singular value selection, and
`‖𝒯_ε(A)‖_F ≤ ‖A‖_F` is derived; `ortho` is any orthonormal basis of a space containing the two
spans.  In Theorem 4.3 the inflow term is an arbitrary `U`-independent matrix `B t`, which includes
`tensorInflow`; the first order accuracy of full forward Euler in `tolerance_scaling` is a
hypothesis, as in the paper.  `exists_regularVlasov` exhibits an instance of all hypotheses. No
claim of the paper was found to be false.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix ENNReal LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2609_02721

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### Finite volumes on a polyhedral mesh (Appendix A) -/

/-- The combinatorics and the measures of a polyhedral mesh: cells `K : C` with volume `|K|`,
interior faces `e : F` with area `|e|` between the cells `side₁ e` and `side₂ e` (the face normal
points from `side₁ e` to `side₂ e`), and boundary faces `β : B` of area `|β|` on the boundary of the
cell `bCell β`.  Every boundary face carries the ghost cell of the paper implicitly. -/
structure FVMesh (C F B : Type*) where
  /-- The cell volume `|K|`. -/
  vol : C → ℝ
  vol_pos : ∀ K, 0 < vol K
  /-- The area `|e|` of an interior face. -/
  area : F → ℝ
  area_pos : ∀ e, 0 < area e
  /-- The cell the normal of an interior face points out of. -/
  side₁ : F → C
  /-- The cell the normal of an interior face points into. -/
  side₂ : F → C
  /-- The area `|β|` of a boundary face. -/
  bArea : B → ℝ
  bArea_pos : ∀ β, 0 < bArea β
  /-- The cell of a boundary face. -/
  bCell : B → C

/-- The face coefficients of (A.1) at one time.  For an interior face `a e = a_{side₁ e, e}` is the
mean `|e|⁻¹ ∫_e n · a` of the normal velocity, with the normal out of `side₁ e` (so that
`a_{side₂ e, e} = -a e`), and `b e = |e|⁻¹ ∫_e α_e` is the mean dissipation.  `aB`, `bB` are the
same means on boundary faces, with the outward normal. -/
structure FaceCoeff (F B : Type*) where
  /-- The mean normal velocity on an interior face. -/
  a : F → ℝ
  /-- The mean dissipation on an interior face. -/
  b : F → ℝ
  /-- The mean outward normal velocity on a boundary face. -/
  aB : B → ℝ
  /-- The mean dissipation on a boundary face. -/
  bB : B → ℝ

variable {C F B : Type*} [Fintype C] [Fintype F] [Fintype B] [DecidableEq C]

/-- The hypotheses of Lemma A.1 on the coefficients: `|a| ≤ b` on all faces (true for upwind and
Lax–Friedrichs fluxes) and the discrete divergence-free identity (A.4)
`∑_{e ⊂ ∂K} |e| a_{K,e} = 0`. -/
structure FaceCoeff.Admissible (M : FVMesh C F B) (c : FaceCoeff F B) : Prop where
  abs_le : ∀ e, |c.a e| ≤ c.b e
  abs_le_bdry : ∀ β, |c.aB β| ≤ c.bB β
  div_free : ∀ K, ∑ e with M.side₁ e = K, M.area e * c.a e
    - ∑ e with M.side₂ e = K, M.area e * c.a e + ∑ β with M.bCell β = K, M.bArea β * c.aB β = 0

namespace FVMesh

variable (M : FVMesh C F B) (c : FaceCoeff F B)

/-- The numerical flux `|e| (a {u}_e + b/2 [u]_e)` through an interior face, from `side₁ e` to
`side₂ e`. -/
def faceFlux (u : C → ℝ) (e : F) : ℝ :=
  M.area e * (c.a e * ((u (M.side₁ e) + u (M.side₂ e)) / 2)
    + c.b e / 2 * (u (M.side₁ e) - u (M.side₂ e)))

/-- The numerical flux through a boundary face, with ghost value `0` (homogeneous inflow). -/
def bdryFlux (u : C → ℝ) (β : B) : ℝ :=
  M.bArea β * (c.aB β * (u (M.bCell β) / 2) + c.bB β / 2 * u (M.bCell β))

/-- The discrete divergence `|K|⁻¹ ∑_{e ⊂ ∂K} |e| (a_{K,e} {u}_e + b_{K,e}/2 [u]_e)`. -/
def div (u : C → ℝ) (K : C) : ℝ :=
  (∑ e with M.side₁ e = K, M.faceFlux c u e - ∑ e with M.side₂ e = K, M.faceFlux c u e
    + ∑ β with M.bCell β = K, M.bdryFlux c u β) / M.vol K

/-- The forward Euler finite volume step (A.1), homogeneous inflow. -/
def euler (τ : ℝ) (u : C → ℝ) (K : C) : ℝ := u K - τ * M.div c u K

/-- The squared `L²` norm `∑_K |K| u_K²` of a piecewise constant function. -/
def energy (u : C → ℝ) : ℝ := ∑ K, M.vol K * u K ^ 2

/-- The local CFL rate `(2|K|)⁻¹ ∑_{e ⊂ ∂K} ∫_e α_e`, the term in the supremum of (A.2). -/
def cflRate (K : C) : ℝ :=
  (∑ e with M.side₁ e = K, M.area e * c.b e + ∑ e with M.side₂ e = K, M.area e * c.b e
    + ∑ β with M.bCell β = K, M.bArea β * c.bB β) / (2 * M.vol K)

/-- The CFL time step (A.2): `τ_CFL = (sup_{K, t ∈ [0,T]} (2|K|)⁻¹ ∑_{e ⊂ ∂K} ∫_e α_e)⁻¹`, as an
extended number, so that it is `∞` if the supremum is `0`, as in the paper. -/
def tauCFL (c : ℝ → FaceCoeff F B) (T : ℝ) : ℝ≥0∞ :=
  (⨆ t ∈ Icc (0 : ℝ) T, ⨆ K, ENNReal.ofReal (M.cflRate (c t) K))⁻¹

end FVMesh

/-- Convexity of the square in the form used in Step 7 of the proof of Lemma A.1, with sub-unit
total weight, proved with the tangent line `2 m y ≤ m² + y²`. -/
lemma weighted_sq_le {ι₁ ι₂ : Type*} (S : Finset ι₁) (T : Finset ι₂) {w p m x : ℝ}
    (q y : ι₁ → ℝ) (q' y' : ι₂ → ℝ) (hp : 0 ≤ p) (hq : ∀ i ∈ S, 0 ≤ q i) (hq' : ∀ i ∈ T, 0 ≤ q' i)
    (hsum : p + ∑ i ∈ S, q i + ∑ i ∈ T, q' i ≤ w)
    (hm : w * m = p * x + ∑ i ∈ S, q i * y i + ∑ i ∈ T, q' i * y' i) :
    w * m ^ 2 ≤ p * x ^ 2 + ∑ i ∈ S, q i * y i ^ 2 + ∑ i ∈ T, q' i * y' i ^ 2 := by
  have h1 : 2 * m * (p * x) ≤ p * m ^ 2 + p * x ^ 2 := by nlinarith [sq_nonneg (m - x)]
  have h2 : 2 * m * ∑ i ∈ S, q i * y i ≤ (∑ i ∈ S, q i) * m ^ 2 + ∑ i ∈ S, q i * y i ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    nlinarith [sq_nonneg (m - y i), hq i hi]
  have h3 : 2 * m * ∑ i ∈ T, q' i * y' i ≤ (∑ i ∈ T, q' i) * m ^ 2 + ∑ i ∈ T, q' i * y' i ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    nlinarith [sq_nonneg (m - y' i), hq' i hi]
  have h4 : 2 * (w * m ^ 2) = 2 * m * (p * x) + 2 * m * ∑ i ∈ S, q i * y i
      + 2 * m * ∑ i ∈ T, q' i * y' i := by
    have : 2 * (w * m ^ 2) = 2 * m * (w * m) := by ring
    rw [this, hm]; ring
  have h5 : (p + ∑ i ∈ S, q i + ∑ i ∈ T, q' i) * m ^ 2 ≤ w * m ^ 2 :=
    mul_le_mul_of_nonneg_right hsum (sq_nonneg m)
  nlinarith

namespace FVMesh

variable (M : FVMesh C F B) {c : FaceCoeff F B}

/-- arXiv 2609.02721, Lemma A.1, one step.  One forward Euler step does not increase the `L²` norm
(Steps 2 to 10 of the proof of the lemma), for an arbitrary finite polyhedral mesh; only `|a| ≤ b`,
(A.4) and the CFL condition are used.  Conditional on `|a| ≤ b` and (A.4), which the paper derives
from the flux choice (2.6)-(2.7) and from `∇ · a = 0` by the divergence theorem; for the Vlasov
scheme both are proved (`tensorCoeff_admissible`). -/
theorem energy_euler_le (hc : c.Admissible M) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : ∀ K, τ * M.cflRate c K ≤ 1) (u : C → ℝ) :
    M.energy (M.euler c τ u) ≤ M.energy u := by
  -- the weights
  set lp : F → ℝ := fun e => τ * M.area e * (c.b e + c.a e) / 2 with hlp
  set lm : F → ℝ := fun e => τ * M.area e * (c.b e - c.a e) / 2 with hlm
  set r : B → ℝ := fun β => τ * M.bArea β * (c.bB β + c.aB β) / 2 with hr
  set g : B → ℝ := fun β => τ * M.bArea β * (c.bB β - c.aB β) / 2 with hg
  have hlp0 : ∀ e, 0 ≤ lp e := fun e => by
    have := abs_le.1 (hc.abs_le e)
    have h := mul_nonneg hτ (M.area_pos e).le
    simp only [hlp]; apply div_nonneg (mul_nonneg h (by linarith)) (by norm_num)
  have hlm0 : ∀ e, 0 ≤ lm e := fun e => by
    have := abs_le.1 (hc.abs_le e)
    have h := mul_nonneg hτ (M.area_pos e).le
    simp only [hlm]; apply div_nonneg (mul_nonneg h (by linarith)) (by norm_num)
  have hr0 : ∀ β, 0 ≤ r β := fun β => by
    have := abs_le.1 (hc.abs_le_bdry β)
    have h := mul_nonneg hτ (M.bArea_pos β).le
    simp only [hr]; apply div_nonneg (mul_nonneg h (by linarith)) (by norm_num)
  have hg0 : ∀ β, 0 ≤ g β := fun β => by
    have := abs_le.1 (hc.abs_le_bdry β)
    have h := mul_nonneg hτ (M.bArea_pos β).le
    simp only [hg]; apply div_nonneg (mul_nonneg h (by linarith)) (by norm_num)
  -- the total outflow of a cell
  set d : C → ℝ := fun K => ∑ e with M.side₁ e = K, lp e + ∑ e with M.side₂ e = K, lm e
    + ∑ β with M.bCell β = K, r β with hd
  -- cellwise inequality
  have hcell : ∀ K, M.vol K * M.euler c τ u K ^ 2 ≤ (M.vol K - d K) * u K ^ 2
      + ∑ e with M.side₁ e = K, lm e * u (M.side₂ e) ^ 2
      + ∑ e with M.side₂ e = K, lp e * u (M.side₁ e) ^ 2 := by
    intro K
    have hK := (M.vol_pos K).ne'
    have hdiv := hc.div_free K
    have hbal : ∑ e with M.side₁ e = K, lm e + ∑ e with M.side₂ e = K, lp e
        + ∑ β with M.bCell β = K, g β = d K := by
      have e1 : ∑ e with M.side₁ e = K, lp e - ∑ e with M.side₁ e = K, lm e
          = τ * ∑ e with M.side₁ e = K, M.area e * c.a e := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hlp, hlm]; ring
      have e2 : ∑ e with M.side₂ e = K, lp e - ∑ e with M.side₂ e = K, lm e
          = τ * ∑ e with M.side₂ e = K, M.area e * c.a e := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hlp, hlm]; ring
      have e3 : ∑ β with M.bCell β = K, r β - ∑ β with M.bCell β = K, g β
          = τ * ∑ β with M.bCell β = K, M.bArea β * c.aB β := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hr, hg]; ring
      have : τ * (∑ e with M.side₁ e = K, M.area e * c.a e
          - ∑ e with M.side₂ e = K, M.area e * c.a e
          + ∑ β with M.bCell β = K, M.bArea β * c.aB β) = 0 := by rw [hdiv, mul_zero]
      simp only [hd]
      nlinarith
    have hdle : d K ≤ M.vol K := by
      have e1 : ∑ e with M.side₁ e = K, lp e + ∑ e with M.side₁ e = K, lm e
          = τ * ∑ e with M.side₁ e = K, M.area e * c.b e := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hlp, hlm]; ring
      have e2 : ∑ e with M.side₂ e = K, lp e + ∑ e with M.side₂ e = K, lm e
          = τ * ∑ e with M.side₂ e = K, M.area e * c.b e := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hlp, hlm]; ring
      have e3 : ∑ β with M.bCell β = K, r β + ∑ β with M.bCell β = K, g β
          = τ * ∑ β with M.bCell β = K, M.bArea β * c.bB β := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by simp only [hr, hg]; ring
      have h := hcfl K
      have hv := M.vol_pos K
      have h' : τ * (∑ e with M.side₁ e = K, M.area e * c.b e
          + ∑ e with M.side₂ e = K, M.area e * c.b e
          + ∑ β with M.bCell β = K, M.bArea β * c.bB β) ≤ 2 * M.vol K := by
        have : τ * M.cflRate c K * (2 * M.vol K) ≤ 1 * (2 * M.vol K) :=
          mul_le_mul_of_nonneg_right h (by positivity)
        have e : τ * M.cflRate c K * (2 * M.vol K) = τ * (∑ e with M.side₁ e = K, M.area e * c.b e
            + ∑ e with M.side₂ e = K, M.area e * c.b e
            + ∑ β with M.bCell β = K, M.bArea β * c.bB β) := by
          simp only [cflRate]; field_simp
        linarith
      have hdsum : d K = d K := rfl
      nlinarith
    have hG : 0 ≤ ∑ β with M.bCell β = K, g β := Finset.sum_nonneg fun β _ => hg0 β
    refine weighted_sq_le _ _ lm _ lp _ (by linarith) (fun i _ => hlm0 i) (fun i _ => hlp0 i)
      (by linarith) ?_
    -- the update formula (A.3)
    have f1 : τ * ∑ e with M.side₁ e = K, M.faceFlux c u e
        = (∑ e with M.side₁ e = K, lp e) * u K - ∑ e with M.side₁ e = K, lm e * u (M.side₂ e) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have : M.side₁ e = K := (Finset.mem_filter.1 he).2
      simp only [faceFlux, hlp, hlm, this]; ring
    have f2 : τ * ∑ e with M.side₂ e = K, M.faceFlux c u e
        = ∑ e with M.side₂ e = K, lp e * u (M.side₁ e) - (∑ e with M.side₂ e = K, lm e) * u K := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have : M.side₂ e = K := (Finset.mem_filter.1 he).2
      simp only [faceFlux, hlp, hlm, this]; ring
    have f3 : τ * ∑ β with M.bCell β = K, M.bdryFlux c u β
        = (∑ β with M.bCell β = K, r β) * u K := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have : M.bCell e = K := (Finset.mem_filter.1 he).2
      simp only [bdryFlux, hr, this]; ring
    have : M.vol K * M.euler c τ u K = M.vol K * u K
        - τ * (∑ e with M.side₁ e = K, M.faceFlux c u e - ∑ e with M.side₂ e = K, M.faceFlux c u e
          + ∑ β with M.bCell β = K, M.bdryFlux c u β) := by
      simp only [euler, div]; field_simp
    rw [this, mul_add, mul_sub, f1, f2, f3]
    simp only [hd]; ring
  -- summation over the cells
  have s1 : ∑ K, ∑ e with M.side₁ e = K, lm e * u (M.side₂ e) ^ 2
      = ∑ e, lm e * u (M.side₂ e) ^ 2 := Finset.sum_fiberwise _ _ _
  have s2 : ∑ K, ∑ e with M.side₂ e = K, lp e * u (M.side₁ e) ^ 2
      = ∑ e, lp e * u (M.side₁ e) ^ 2 := Finset.sum_fiberwise _ _ _
  have s3 : ∑ K, (∑ e with M.side₁ e = K, lp e) * u K ^ 2 = ∑ e, lp e * u (M.side₁ e) ^ 2 := by
    rw [← Finset.sum_fiberwise _ M.side₁]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
  have s4 : ∑ K, (∑ e with M.side₂ e = K, lm e) * u K ^ 2 = ∑ e, lm e * u (M.side₂ e) ^ 2 := by
    rw [← Finset.sum_fiberwise _ M.side₂]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
  have s5 : ∑ K, (∑ β with M.bCell β = K, r β) * u K ^ 2 = ∑ β, r β * u (M.bCell β) ^ 2 := by
    rw [← Finset.sum_fiberwise _ M.bCell]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
  have hR : 0 ≤ ∑ β, r β * u (M.bCell β) ^ 2 :=
    Finset.sum_nonneg fun β _ => mul_nonneg (hr0 β) (sq_nonneg _)
  calc M.energy (M.euler c τ u) = ∑ K, M.vol K * M.euler c τ u K ^ 2 := rfl
    _ ≤ ∑ K, ((M.vol K - d K) * u K ^ 2 + ∑ e with M.side₁ e = K, lm e * u (M.side₂ e) ^ 2
          + ∑ e with M.side₂ e = K, lp e * u (M.side₁ e) ^ 2) :=
        Finset.sum_le_sum fun K _ => hcell K
    _ = M.energy u - ∑ β, r β * u (M.bCell β) ^ 2 := by
        simp only [Finset.sum_add_distrib, s1, s2, sub_mul, Finset.sum_sub_distrib, hd, add_mul, s3,
          s4, s5, energy]
        ring
    _ ≤ M.energy u := by linarith

end FVMesh

namespace FVMesh

variable (M : FVMesh C F B)

/-- The CFL condition in the form used in the proof. -/
lemma mul_cflRate_le_one {c : ℝ → FaceCoeff F B} {T τ : ℝ} (hτ : 0 ≤ τ)
    (hcfl : ENNReal.ofReal τ ≤ M.tauCFL c T) {t : ℝ} (ht : t ∈ Icc 0 T) (K : C) :
    τ * M.cflRate (c t) K ≤ 1 := by
  have h1 : ENNReal.ofReal (M.cflRate (c t) K)
      ≤ ⨆ t ∈ Icc (0 : ℝ) T, ⨆ K, ENNReal.ofReal (M.cflRate (c t) K) :=
    le_iSup₂_of_le t ht (le_iSup (fun K => ENNReal.ofReal (M.cflRate (c t) K)) K)
  have h2 : ENNReal.ofReal (τ * M.cflRate (c t) K) ≤ 1 := by
    rw [ENNReal.ofReal_mul hτ]
    exact (mul_le_mul' hcfl h1).trans (ENNReal.inv_mul_le_one _)
  exact ENNReal.ofReal_le_one.1 h2

/-- arXiv 2609.02721, Lemma A.1, first claim: `τ_CFL ∈ (0, ∞]` if the dissipation is uniformly
bounded by `ᾱ` (the paper's uniform bound on `α_e`), on an arbitrary finite polyhedral mesh. -/
theorem tauCFL_pos {c : ℝ → FaceCoeff F B} {T ᾱ : ℝ} (hα : 0 ≤ ᾱ)
    (hb : ∀ t ∈ Icc 0 T, ∀ e, (c t).b e ≤ ᾱ) (hbB : ∀ t ∈ Icc 0 T, ∀ β, (c t).bB β ≤ ᾱ) :
    0 < M.tauCFL c T := by
  set ρ : C → ℝ := fun K => ᾱ * (∑ e with M.side₁ e = K, M.area e
    + ∑ e with M.side₂ e = K, M.area e + ∑ β with M.bCell β = K, M.bArea β) / (2 * M.vol K)
  have hρ0 : ∀ K, 0 ≤ ρ K := fun K => by
    have := M.vol_pos K
    have h1 : 0 ≤ ∑ e with M.side₁ e = K, M.area e :=
      Finset.sum_nonneg fun e _ => (M.area_pos e).le
    have h2 : 0 ≤ ∑ e with M.side₂ e = K, M.area e :=
      Finset.sum_nonneg fun e _ => (M.area_pos e).le
    have h3 : 0 ≤ ∑ β with M.bCell β = K, M.bArea β :=
      Finset.sum_nonneg fun e _ => (M.bArea_pos e).le
    positivity
  have hle : ∀ t ∈ Icc (0 : ℝ) T, ∀ K, M.cflRate (c t) K ≤ ∑ K, ρ K := fun t ht K => by
    have hv := M.vol_pos K
    have h1 : ∑ e with M.side₁ e = K, M.area e * (c t).b e
        ≤ ∑ e with M.side₁ e = K, M.area e * ᾱ := Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (hb t ht e) (M.area_pos e).le
    have h2 : ∑ e with M.side₂ e = K, M.area e * (c t).b e
        ≤ ∑ e with M.side₂ e = K, M.area e * ᾱ := Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (hb t ht e) (M.area_pos e).le
    have h3 : ∑ β with M.bCell β = K, M.bArea β * (c t).bB β
        ≤ ∑ β with M.bCell β = K, M.bArea β * ᾱ := Finset.sum_le_sum fun e _ =>
      mul_le_mul_of_nonneg_left (hbB t ht e) (M.bArea_pos e).le
    refine le_trans ?_ (Finset.single_le_sum (fun K _ => hρ0 K) (Finset.mem_univ K))
    simp only [cflRate, ρ, ← Finset.sum_mul] at h1 h2 h3 ⊢
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ENNReal.inv_pos.2 (ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑ K, ρ K))))
  exact iSup₂_le fun t ht => iSup_le fun K => ENNReal.ofReal_le_ofReal (hle t ht K)

/-- arXiv 2609.02721, Lemma A.1, second claim, for the coefficients of an arbitrary finite
polyhedral mesh: the forward Euler finite volume scheme (A.1) with homogeneous inflow is `L²`
stable for `0 < τ ≤ τ_CFL` and all `n` with `tⁿ = n τ ≤ T`.  Conditional on the hypotheses
`|a| ≤ b` and (A.4), collected in `FaceCoeff.Admissible`: on a general mesh the face coefficients
are abstract numbers, while the paper derives `|a| ≤ b` from the flux choice (2.6)-(2.7) and (A.4)
from `∇ · a = 0` by the divergence theorem.  For the Vlasov field on a tensor mesh both are proved,
see `tensorCoeff_admissible`, so `VlasovFV.lemma41_stable` is unconditional.  The norm is
`∑_K |K| u_K²`, which is the `L²` norm of the piecewise constant function, see
`PolyMesh.integral_sq_pwc`. -/
theorem lemmaA1_stable {c : ℝ → FaceCoeff F B} {T τ : ℝ} (hc : ∀ t ∈ Icc 0 T, (c t).Admissible M)
    (hτ : 0 < τ) (hcfl : ENNReal.ofReal τ ≤ M.tauCFL c T) {u : ℕ → C → ℝ}
    (hu : ∀ n : ℕ, u (n + 1) = M.euler (c (n * τ)) τ (u n)) (n : ℕ) (hn : n * τ ≤ T) :
    M.energy (u n) ≤ M.energy (u 0) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hn' : (n : ℝ) * τ ≤ T := by
      push_cast at hn; nlinarith
    have hmem : (n : ℝ) * τ ∈ Icc 0 T := ⟨by positivity, hn'⟩
    rw [hu n]
    exact (M.energy_euler_le (hc _ hmem) hτ.le
      (fun K => M.mul_cflRate_le_one hτ.le hcfl hmem K) _).trans (ih hn')

end FVMesh

/-! ### Geometry of the cells and piecewise constant functions (Section 2) -/

/-- A polyhedral mesh with its geometry.  Besides the data of `FVMesh`: pairwise disjoint measurable
cells of the given volumes in a measure space `(Y, μ)`, the components `normal e s`, `s : D`, of the
unit normals of the interior faces (from `side₁ e` to `side₂ e`), a decomposition of the boundary
faces into pieces `P` with constant outward normal `pNormal` (the pieces `μ` of the paper), and
the closure relation `∑_{e ⊂ ∂K} |e| n_{K,e} = 0` of a polytope, which is the only geometric fact
about polytopes used below (it is the divergence theorem for constant fields; Mathlib has no
divergence theorem on polytopes, so it is a field of the structure). -/
structure PolyMesh (C F B P D Y : Type*) [Fintype F] [Fintype B] [DecidableEq C]
    [MeasurableSpace Y] extends FVMesh C F B where
  /-- The measure of the ambient space. -/
  μ : Measure Y
  /-- The cells. -/
  cell : C → Set Y
  /-- The normal of an interior face. -/
  normal : F → D → ℝ
  /-- The boundary piece of a boundary face. -/
  piece : B → P
  /-- The outward normal of a boundary piece. -/
  pNormal : P → D → ℝ
  cell_meas : ∀ K, MeasurableSet (cell K)
  cell_disj : Pairwise (Function.onFun Disjoint cell)
  vol_eq : ∀ K, μ.real (cell K) = vol K
  closure : ∀ K s, ∑ e with side₁ e = K, area e * normal e s
    - ∑ e with side₂ e = K, area e * normal e s
    + ∑ β with bCell β = K, bArea β * pNormal (piece β) s = 0

/-- The `L²` norm of a piecewise constant function on disjoint measurable cells of finite
measure. -/
lemma integral_sq_sum_indicator {Y ι : Type*} [MeasurableSpace Y] [Fintype ι] {μ : Measure Y}
    {cell : ι → Set Y} (hm : ∀ K, MeasurableSet (cell K))
    (hd : Pairwise (Function.onFun Disjoint cell)) (hf : ∀ K, μ (cell K) ≠ ∞) (u : ι → ℝ) :
    ∫ y, (∑ K, u K * (cell K).indicator (fun _ => (1 : ℝ)) y) ^ 2 ∂μ
      = ∑ K, μ.real (cell K) * u K ^ 2 := by
  classical
  have hpt : ∀ y, (∑ K, u K * (cell K).indicator (fun _ => (1 : ℝ)) y) ^ 2
      = ∑ K, (cell K).indicator (fun _ => u K ^ 2) y := by
    intro y
    by_cases hy : ∃ K, y ∈ cell K
    · obtain ⟨K, hK⟩ := hy
      have hne : ∀ L, L ≠ K → y ∉ cell L := fun L hL hyL =>
        Set.disjoint_left.1 (hd hL) hyL hK
      rw [Finset.sum_eq_single K (fun L _ hL => by simp [hne L hL]) (by simp),
        Finset.sum_eq_single K (fun L _ hL => by simp [hne L hL]) (by simp)]
      simp [hK]
    · simp only [not_exists] at hy
      simp [hy]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun K _ => (integrableOn_const (hf K)).integrable_indicator (hm K)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [integral_indicator_const _ (hm K)]
  simp

namespace PolyMesh

variable {P D Y : Type*} [MeasurableSpace Y] (M : PolyMesh C F B P D Y)

/-- Cells have finite measure. -/
lemma measure_ne_top (K : C) : M.μ (M.cell K) ≠ ∞ := fun h => by
  have := M.vol_eq K
  have hp := M.vol_pos K
  simp [Measure.real, h] at this
  linarith

/-- The piecewise constant function with cell values `u`. -/
def pwc (u : C → ℝ) (y : Y) : ℝ := ∑ K, u K * (M.cell K).indicator (fun _ => (1 : ℝ)) y

/-- arXiv 2609.02721, Section 2.  The energy of `FVMesh` is the squared `L²(Ω)` norm of the
piecewise constant function. -/
theorem integral_sq_pwc (u : C → ℝ) : ∫ y, M.pwc u y ^ 2 ∂M.μ = M.energy u := by
  simp only [pwc, FVMesh.energy]
  rw [integral_sq_sum_indicator M.cell_meas M.cell_disj M.measure_ne_top]
  simp [M.vol_eq]

/-- arXiv 2609.02721, Lemma A.1, second claim, literally in `L²(Ω)`: the piecewise constant
functions of the forward Euler finite volume scheme satisfy `‖û_hⁿ‖_{L²} ≤ ‖û_h⁰‖_{L²}`, here
squared.  Conditional on `FaceCoeff.Admissible`, as `FVMesh.lemmaA1_stable`. -/
theorem lemmaA1_stable_L2 {c : ℝ → FaceCoeff F B} {T τ : ℝ}
    (hc : ∀ t ∈ Icc 0 T, (c t).Admissible M.toFVMesh) (hτ : 0 < τ)
    (hcfl : ENNReal.ofReal τ ≤ M.tauCFL c T) {u : ℕ → C → ℝ}
    (hu : ∀ n : ℕ, u (n + 1) = M.euler (c (n * τ)) τ (u n)) (n : ℕ) (hn : n * τ ≤ T) :
    ∫ y, M.pwc (u n) y ^ 2 ∂M.μ ≤ ∫ y, M.pwc (u 0) y ^ 2 ∂M.μ := by
  rw [integral_sq_pwc, integral_sq_pwc]
  exact M.toFVMesh.lemmaA1_stable hc hτ hcfl hu n hn

/-- The normalised cell indicator `φ_K = χ_K / √|K|`. -/
def φ (K : C) : Y → ℝ := (M.cell K).indicator fun _ => (√(M.vol K))⁻¹

/-- The cell mean `|K|⁻¹ ∫_K b`. -/
def mean (b : Y → ℝ) (K : C) : ℝ := (∫ y in M.cell K, b y ∂M.μ) / M.vol K

/-- The cell mean bounded by a pointwise bound. -/
lemma abs_mean_le {b : Y → ℝ} {α : ℝ} {K : C} (h : ∀ y ∈ M.cell K, |b y| ≤ α) :
    |M.mean b K| ≤ α := by
  have hfin : M.μ (M.cell K) < ∞ := (M.measure_ne_top K).lt_top
  have h1 := norm_setIntegral_le_of_norm_le_const (f := b) hfin
    (fun y hy => by simpa using h y hy)
  have hv := M.vol_pos K
  rw [M.vol_eq, Real.norm_eq_abs] at h1
  rw [mean, abs_div, abs_of_pos hv, div_le_iff₀ hv]
  exact h1

/-- The mean of the absolute value dominates the absolute value of the mean. -/
lemma abs_mean_le_mean_abs (b : Y → ℝ) (K : C) :
    |M.mean b K| ≤ M.mean (fun y => |b y|) K := by
  have hv := M.vol_pos K
  rw [mean, mean, abs_div, abs_of_pos hv]
  exact div_le_div_of_nonneg_right (abs_integral_le_integral_abs) hv.le

/-- The sign indicator `χ(y) = 1` if `n · w(y) ≥ 0` and `0` otherwise: the outflow indicators
`χ_μ^(x)`, `χ_μ^(v)` of the paper. -/
def upInd {Y D : Type*} [Fintype D] (n : D → ℝ) (w : Y → D → ℝ) (y : Y) : ℝ :=
  if 0 ≤ ∑ s, n s * w y s then 1 else 0

variable {D' : Type*} [Fintype D']

/-- Linearity of the cell mean in the transport field. -/
lemma sum_mul_mean (n : D' → ℝ) {w : Y → D' → ℝ} {K : C}
    (hw : ∀ s, IntegrableOn (fun y => w y s) (M.cell K) M.μ) :
    ∑ s, n s * M.mean (fun y => w y s) K = M.mean (fun y => ∑ s, n s * w y s) K := by
  simp only [mean]
  rw [integral_finsetSum _ fun s _ => (hw s).const_mul (n s), Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul]; ring

/-- The upwind identity: `∑_s n_s mean(χ w_s) = (mean(n · w) + mean|n · w|) / 2`.  It says that the
boundary mass matrices `M_{χ_μ v_s}` of (2.10) encode the means `(a + b)/2` of Appendix A. -/
lemma sum_mul_mean_up (n : D' → ℝ) {w : Y → D' → ℝ} {K : C}
    (hw : ∀ s, IntegrableOn (fun y => w y s) (M.cell K) M.μ) :
    ∑ s, n s * M.mean (fun y => upInd n w y * w y s) K
      = (M.mean (fun y => ∑ s, n s * w y s) K + M.mean (fun y => |∑ s, n s * w y s|) K) / 2 := by
  have ht : IntegrableOn (fun y => ∑ s, n s * w y s) (M.cell K) M.μ :=
    integrable_finsetSum _ fun s _ => (hw s).const_mul (n s)
  have hstep : Measurable fun r : ℝ => if 0 ≤ r then (1 : ℝ) else 0 :=
    Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hχ : AEStronglyMeasurable (fun y => upInd n w y) (M.μ.restrict (M.cell K)) :=
    (hstep.comp_aemeasurable ht.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hbd : ∀ᵐ y ∂(M.μ.restrict (M.cell K)), ‖upInd n w y‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [upInd]; split_ifs <;> simp
  have hw' : ∀ s, IntegrableOn (fun y => upInd n w y * w y s) (M.cell K) M.μ := fun s =>
    (hw s).bdd_mul hχ hbd
  rw [M.sum_mul_mean n hw']
  have hpt : ∀ y, ∑ s, n s * (upInd n w y * w y s)
      = ((∑ s, n s * w y s) + |∑ s, n s * w y s|) / 2 := by
    intro y
    have : ∑ s, n s * (upInd n w y * w y s) = upInd n w y * ∑ s, n s * w y s := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [this]
    simp only [upInd]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  simp only [mean, hpt]
  rw [integral_div, integral_add ht ht.abs]
  ring

end PolyMesh

/-! ### The product mesh and the Vlasov face coefficients -/

section Tensor

variable {C₁ F₁ B₁ P₁ D₁ Y₁ C₂ F₂ B₂ P₂ D₂ Y₂ : Type*}
  [Fintype C₁] [Fintype F₁] [Fintype B₁] [Fintype P₁] [Fintype D₁] [DecidableEq C₁]
  [DecidableEq P₁] [MeasurableSpace Y₁]
  [Fintype C₂] [Fintype F₂] [Fintype B₂] [Fintype P₂] [Fintype D₂] [DecidableEq C₂]
  [DecidableEq P₂] [MeasurableSpace Y₂]

/-- The cell of a face of the product mesh: the faces of `K₁ × K₂` are the `e × K₂` and the
`K₁ × f`. -/
def prodIdx {G₁ G₂ : Type*} (s₁ : G₁ → C₁) (s₂ : G₂ → C₂) : (G₁ × C₂) ⊕ (C₁ × G₂) → C₁ × C₂ :=
  Sum.elim (fun p => (s₁ p.1, p.2)) (fun p => (p.1, s₂ p.2))

/-- The faces of a product cell. -/
lemma sum_filter_prodIdx {G₁ G₂ : Type*} [Fintype G₁] [Fintype G₂] (s₁ : G₁ → C₁) (s₂ : G₂ → C₂)
    (g : (G₁ × C₂) ⊕ (C₁ × G₂) → ℝ) (i : C₁) (j : C₂) :
    ∑ x with prodIdx s₁ s₂ x = (i, j), g x
      = ∑ e with s₁ e = i, g (Sum.inl (e, j)) + ∑ f with s₂ f = j, g (Sum.inr (i, f)) := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_eq_single j]
    · by_cases h : s₁ e = i <;> simp [prodIdx, h]
    · intro b _ hb; simp [prodIdx, hb]
    · simp
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun f _ => ?_
      by_cases h : s₂ f = j <;> simp [prodIdx, h]
    · intro b _ hb
      refine Finset.sum_eq_zero fun f _ => ?_
      simp [prodIdx, hb]
    · simp

/-- Exchange of a face sum and a coordinate sum. -/
lemma sum_mul_sum_comm {G D : Type*} [Fintype D] (S : Finset G) (f : G → ℝ) (n : G → D → ℝ)
    (m : D → ℝ) : ∑ e ∈ S, f e * ∑ s, n e s * m s = ∑ s, (∑ e ∈ S, f e * n e s) * m s := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun e _ => by ring

/-- Pulling a constant out of a face sum. -/
lemma sum_mul_const_mul {G : Type*} (S : Finset G) (f m : G → ℝ) (c : ℝ) :
    ∑ e ∈ S, f e * c * m e = c * ∑ e ∈ S, f e * m e := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring

/-- Pulling a constant out of a face sum. -/
lemma sum_const_mul_mul {G : Type*} (S : Finset G) (f m : G → ℝ) (c : ℝ) :
    ∑ e ∈ S, c * f e * m e = c * ∑ e ∈ S, f e * m e := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring

/-- The product of two meshes: cells `K₁ × K₂`, faces `e × K₂` and `K₁ × f`, with the product
measures. -/
def FVMesh.prod (M₁ : FVMesh C₁ F₁ B₁) (M₂ : FVMesh C₂ F₂ B₂) :
    FVMesh (C₁ × C₂) ((F₁ × C₂) ⊕ (C₁ × F₂)) ((B₁ × C₂) ⊕ (C₁ × B₂)) where
  vol p := M₁.vol p.1 * M₂.vol p.2
  vol_pos p := mul_pos (M₁.vol_pos _) (M₂.vol_pos _)
  area := Sum.elim (fun p => M₁.area p.1 * M₂.vol p.2) (fun p => M₁.vol p.1 * M₂.area p.2)
  area_pos := by
    rintro (p | p)
    · exact mul_pos (M₁.area_pos _) (M₂.vol_pos _)
    · exact mul_pos (M₁.vol_pos _) (M₂.area_pos _)
  side₁ := prodIdx M₁.side₁ M₂.side₁
  side₂ := prodIdx M₁.side₂ M₂.side₂
  bArea := Sum.elim (fun p => M₁.bArea p.1 * M₂.vol p.2) (fun p => M₁.vol p.1 * M₂.bArea p.2)
  bArea_pos := by
    rintro (p | p)
    · exact mul_pos (M₁.bArea_pos _) (M₂.vol_pos _)
    · exact mul_pos (M₁.vol_pos _) (M₂.bArea_pos _)
  bCell := prodIdx M₁.bCell M₂.bCell

variable (M₁ : PolyMesh C₁ F₁ B₁ P₁ D₁ Y₁) (M₂ : PolyMesh C₂ F₂ B₂ P₂ D₂ Y₂)

/-- The face coefficients of the numerical flux of Section 2 on the product mesh for the transport
field `a(y₁, y₂) = (w₁(y₂), w₂(y₁))`, global Lax–Friedrichs parameter `α` on interior faces and
upwind on boundary faces.  For `w₁(v) = v`, `w₂(x) = -E(t, x)` this is the Vlasov field
`a = (v, -E(t, x))`.  On `e × K₂` the mean of `n · a` is the cell mean of `n_e · w₁` on `K₂`, on
`K₁ × f` the cell mean of `n_f · w₂` on `K₁`; on boundary faces `b` is the mean of `|n · a|`. -/
def tensorCoeff (w₁ : Y₂ → D₁ → ℝ) (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) :
    FaceCoeff ((F₁ × C₂) ⊕ (C₁ × F₂)) ((B₁ × C₂) ⊕ (C₁ × B₂)) where
  a := Sum.elim (fun p => M₂.mean (fun y => ∑ s, M₁.normal p.1 s * w₁ y s) p.2)
    (fun p => M₁.mean (fun y => ∑ s, M₂.normal p.2 s * w₂ y s) p.1)
  b _ := α
  aB := Sum.elim (fun p => M₂.mean (fun y => ∑ s, M₁.pNormal (M₁.piece p.1) s * w₁ y s) p.2)
    (fun p => M₁.mean (fun y => ∑ s, M₂.pNormal (M₂.piece p.2) s * w₂ y s) p.1)
  bB := Sum.elim (fun p => M₂.mean (fun y => |∑ s, M₁.pNormal (M₁.piece p.1) s * w₁ y s|) p.2)
    (fun p => M₁.mean (fun y => |∑ s, M₂.pNormal (M₂.piece p.2) s * w₂ y s|) p.1)

/-- The first half of the discrete divergence-free identity (A.4) on a product cell: the
contribution of the faces `e × K₂`, which vanishes by the closure relation of `K₁` because `w₁` does
not depend on `y₁`. -/
lemma closure_mean {w : Y₂ → D₁ → ℝ} (hw : ∀ j s, IntegrableOn (fun y => w y s) (M₂.cell j) M₂.μ)
    (i : C₁) (j : C₂) :
    ∑ e with M₁.side₁ e = i, M₁.area e * M₂.mean (fun y => ∑ s, M₁.normal e s * w y s) j
      - ∑ e with M₁.side₂ e = i, M₁.area e * M₂.mean (fun y => ∑ s, M₁.normal e s * w y s) j
      + ∑ β with M₁.bCell β = i,
          M₁.bArea β * M₂.mean (fun y => ∑ s, M₁.pNormal (M₁.piece β) s * w y s) j = 0 := by
  have hm : ∀ n : D₁ → ℝ, M₂.mean (fun y => ∑ s, n s * w y s) j
      = ∑ s, n s * M₂.mean (fun y => w y s) j := fun n => (M₂.sum_mul_mean n (hw j)).symm
  simp only [hm, sum_mul_sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [← sub_mul, ← add_mul, M₁.closure i s, zero_mul]

/-- arXiv 2609.02721, Section 2 and proof of Lemma A.1: the hypotheses of Lemma A.1 hold for the
numerical flux of Section 2 on a product mesh: `|a_e| ≤ b_e` on all faces and the discrete
divergence-free identity (A.4) are derived from the closure relation of the cells and from the
Lax–Friedrichs bound `α ≥ max_e max_{z ∈ e} |n_e · a|`.  (A.4) holds because the transport
field `(w₁(y₂), w₂(y₁))` is divergence free by its structure. -/
theorem tensorCoeff_admissible {w₁ : Y₂ → D₁ → ℝ} {w₂ : Y₁ → D₂ → ℝ} {α : ℝ}
    (hw₁ : ∀ j s, IntegrableOn (fun y => w₁ y s) (M₂.cell j) M₂.μ)
    (hw₂ : ∀ i s, IntegrableOn (fun y => w₂ y s) (M₁.cell i) M₁.μ)
    (hα₁ : ∀ e j, ∀ y ∈ M₂.cell j, |∑ s, M₁.normal e s * w₁ y s| ≤ α)
    (hα₂ : ∀ f i, ∀ y ∈ M₁.cell i, |∑ s, M₂.normal f s * w₂ y s| ≤ α) :
    (tensorCoeff M₁ M₂ w₁ w₂ α).Admissible (M₁.toFVMesh.prod M₂.toFVMesh) where
  abs_le := by
    rintro (⟨e, j⟩ | ⟨i, f⟩)
    · exact M₂.abs_mean_le (hα₁ e j)
    · exact M₁.abs_mean_le (hα₂ f i)
  abs_le_bdry := by
    rintro (⟨β, j⟩ | ⟨i, β⟩)
    · exact M₂.abs_mean_le_mean_abs _ _
    · exact M₁.abs_mean_le_mean_abs _ _
  div_free := by
    rintro ⟨i, j⟩
    have h1 := closure_mean M₁ M₂ hw₁ i j
    have h2 := closure_mean M₂ M₁ hw₂ j i
    have s1 := sum_filter_prodIdx M₁.side₁ M₂.side₁ (fun x =>
      (M₁.toFVMesh.prod M₂.toFVMesh).area x * (tensorCoeff M₁ M₂ w₁ w₂ α).a x) i j
    have s2 := sum_filter_prodIdx M₁.side₂ M₂.side₂ (fun x =>
      (M₁.toFVMesh.prod M₂.toFVMesh).area x * (tensorCoeff M₁ M₂ w₁ w₂ α).a x) i j
    have s3 := sum_filter_prodIdx M₁.bCell M₂.bCell (fun x =>
      (M₁.toFVMesh.prod M₂.toFVMesh).bArea x * (tensorCoeff M₁ M₂ w₁ w₂ α).aB x) i j
    simp only [FVMesh.prod, tensorCoeff, Sum.elim_inl, Sum.elim_inr, sum_mul_const_mul,
      sum_const_mul_mul] at s1 s2 s3
    change ∑ x with prodIdx M₁.side₁ M₂.side₁ x = (i, j), _
      - ∑ x with prodIdx M₁.side₂ M₂.side₂ x = (i, j), _
      + ∑ x with prodIdx M₁.bCell M₂.bCell x = (i, j), _ = 0
    simp only [FVMesh.prod, tensorCoeff]
    rw [s1, s2, s3]
    linear_combination M₂.vol j * h1 + M₁.vol i * h2

end Tensor

/-! ### The matrices of the semi-discretisation (2.10) -/

namespace PolyMesh

variable {P D Y : Type*} [MeasurableSpace Y] (M : PolyMesh C F B P D Y)

/-- The value of the normalised indicator `φ_K` on a face `g` attached to the cell `s g`. -/
def traceφ {G : Type*} (s : G → C) (g : G) (K : C) : ℝ :=
  if s g = K then (√(M.vol K))⁻¹ else 0

/-- The jump `[φ_K]_e` across an interior face. -/
def jumpφ (e : F) (K : C) : ℝ := M.traceφ M.side₁ e K - M.traceφ M.side₂ e K

/-- The average `{φ_K}_e` on an interior face. -/
def avgφ (e : F) (K : C) : ℝ := (M.traceφ M.side₁ e K + M.traceφ M.side₂ e K) / 2

/-- The flux-average matrix `(C_s)_{ij} = ∑_e ∫_e n_{e,s} {φ_j}_e [φ_i]_e dS` of (2.10). -/
def matC (s : D) : Matrix C C ℝ :=
  Matrix.of fun i j => ∑ e, M.area e * M.normal e s * M.avgφ e j * M.jumpφ e i

/-- The jump matrix `D_{ij} = ∑_e ∫_e [φ_j]_e [φ_i]_e dS` of (2.10). -/
def matD : Matrix C C ℝ :=
  Matrix.of fun i j => ∑ e, M.area e * M.jumpφ e j * M.jumpφ e i

/-- The boundary matrix `(B_{μ,s})_{ij} = ∑_{e ∈ ℰ_{b,μ}} ∫_e n_s^μ φ_j φ_i dS` of (2.10). -/
def matB [DecidableEq P] (p : P) (s : D) : Matrix C C ℝ :=
  Matrix.of fun i j => ∑ β with M.piece β = p,
    M.bArea β * M.pNormal p s * M.traceφ M.bCell β j * M.traceφ M.bCell β i

/-- The mass-type matrix `(M_b)_{ij} = ∑_K ∫_K b φ_j φ_i` of (2.10). -/
def matM (b : Y → ℝ) : Matrix C C ℝ :=
  Matrix.of fun i j => ∫ y, b y * M.φ j y * M.φ i y ∂M.μ

/-- The sum over the basis of a face value of a cell function. -/
lemma sum_traceφ_mul {G : Type*} (s : G → C) (g : G) (f : C → ℝ) :
    ∑ K, M.traceφ s g K * f K = f (s g) / √(M.vol (s g)) := by
  simp only [traceφ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [div_eq_inv_mul]

/-- Testing a face sum with the trace of `φ_K` selects the faces of `K`. -/
lemma sum_mul_traceφ {G : Type*} [Fintype G] (s : G → C) (H : G → ℝ) (K : C) :
    ∑ g, H g * M.traceφ s g K = (∑ g with s g = K, H g) / √(M.vol K) := by
  rw [Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [traceφ]
  split_ifs
  · rw [div_eq_mul_inv]
  · simp

/-- The average of a discrete function on a face. -/
lemma sum_avgφ_mul (e : F) (f : C → ℝ) : ∑ K, M.avgφ e K * f K
    = (f (M.side₁ e) / √(M.vol (M.side₁ e)) + f (M.side₂ e) / √(M.vol (M.side₂ e))) / 2 := by
  rw [← M.sum_traceφ_mul, ← M.sum_traceφ_mul, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun K _ => by simp only [avgφ]; ring

/-- The jump of a discrete function across a face. -/
lemma sum_jumpφ_mul (e : F) (f : C → ℝ) : ∑ K, M.jumpφ e K * f K
    = f (M.side₁ e) / √(M.vol (M.side₁ e)) - f (M.side₂ e) / √(M.vol (M.side₂ e)) := by
  rw [← M.sum_traceφ_mul, ← M.sum_traceφ_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun K _ => by simp only [jumpφ]; ring

/-- arXiv 2609.02721, Section 2.  The mass-type matrices of a piecewise constant basis are the
diagonal matrices of cell means. -/
theorem matM_eq_diagonal (b : Y → ℝ) : M.matM b = Matrix.diagonal (M.mean b) := by
  ext i j
  simp only [matM, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    have hpt : ∀ y, b y * M.φ i y * M.φ i y = (M.cell i).indicator (fun y => b y / M.vol i) y := by
      intro y
      by_cases hy : y ∈ M.cell i
      · have hv := M.vol_pos i
        have hs : √(M.vol i) * √(M.vol i) = M.vol i := Real.mul_self_sqrt hv.le
        have hs0 : √(M.vol i) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
        simp only [φ, indicator_of_mem hy]
        rw [mul_assoc, ← mul_inv, hs, div_eq_mul_inv]
      · simp [φ, hy]
    simp_rw [hpt]
    rw [integral_indicator (M.cell_meas i), integral_div]
    simp [mean]
  · have hpt : ∀ y, b y * M.φ j y * M.φ i y = 0 := by
      intro y
      by_cases hy : y ∈ M.cell j
      · have : y ∉ M.cell i := fun hi => Set.disjoint_left.1 (M.cell_disj h) hi hy
        simp [φ, this]
      · simp [φ, hy]
    simp [hpt, Matrix.diagonal_apply_ne _ h]

variable {k : Type*} [Fintype k]

/-- The entries of `C_s U`. -/
lemma matC_mul_apply [Fintype D] (s : D) (U : Matrix C k ℝ) (i : C) (j : k) : (M.matC s * U) i j
    = ∑ e, M.area e * M.normal e s * (∑ K, M.avgφ e K * U K j) * M.jumpφ e i := by
  simp only [Matrix.mul_apply, matC, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun K _ => by ring

/-- The entries of `D U`. -/
lemma matD_mul_apply (U : Matrix C k ℝ) (i : C) (j : k) : (M.matD * U) i j
    = ∑ e, M.area e * (∑ K, M.jumpφ e K * U K j) * M.jumpφ e i := by
  simp only [Matrix.mul_apply, matD, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun K _ => by ring

/-- The entries of `B_{μ,s} U`. -/
lemma matB_mul_apply [DecidableEq P] (p : P) (s : D) (U : Matrix C k ℝ) (i : C) (j : k) :
    (M.matB p s * U) i j = ∑ β with M.piece β = p,
      M.bArea β * M.pNormal p s * (∑ K, M.traceφ M.bCell β K * U K j) * M.traceφ M.bCell β i := by
  simp only [Matrix.mul_apply, matB, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun K _ => by ring

end PolyMesh

section Tensor

variable {C₁ F₁ B₁ P₁ D₁ Y₁ C₂ F₂ B₂ P₂ D₂ Y₂ : Type*}
  [Fintype C₁] [Fintype F₁] [Fintype B₁] [Fintype P₁] [Fintype D₁] [DecidableEq C₁]
  [DecidableEq P₁] [MeasurableSpace Y₁]
  [Fintype C₂] [Fintype F₂] [Fintype B₂] [Fintype P₂] [Fintype D₂] [DecidableEq C₂]
  [DecidableEq P₂] [MeasurableSpace Y₂]
  (M₁ : PolyMesh C₁ F₁ B₁ P₁ D₁ Y₁) (M₂ : PolyMesh C₂ F₂ B₂ P₂ D₂ Y₂)

/-- The linear part of the matrix ODE (2.10), with the sign of a right-hand side:
`L_h(U) = -[∑_s (C_s^(1) U M_{w₁,s}^(2)ᵀ + M_{w₂,s}^(1) U C_s^(2)ᵀ) + (α/2)(D^(1) U + U D^(2)ᵀ)
  + ∑_μ ∑_s B_{μ,s}^(1) U M_{χ_μ w₁,s}^(2)ᵀ + ∑_μ ∑_s M_{χ_μ w₂,s}^(1) U B_{μ,s}^(2)ᵀ]`.
For `w₁(v) = v`, `w₂(x) = -E(t, x)` this is literally (2.10). -/
def tensorL (w₁ : Y₂ → D₁ → ℝ) (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) (U : Matrix C₁ C₂ ℝ) :
    Matrix C₁ C₂ ℝ :=
  -(∑ s, M₁.matC s * U * (M₂.matM fun y => w₁ y s)ᵀ
    + ∑ s, (M₁.matM fun y => w₂ y s) * U * (M₂.matC s)ᵀ
    + (α / 2) • (M₁.matD * U + U * M₂.matDᵀ)
    + ∑ p, ∑ s, M₁.matB p s * U * (M₂.matM fun y => PolyMesh.upInd (M₁.pNormal p) w₁ y * w₁ y s)ᵀ
    + ∑ p, ∑ s, (M₁.matM fun y => PolyMesh.upInd (M₂.pNormal p) w₂ y * w₂ y s) * U * (M₂.matB p s)ᵀ)

/-- The part of (2.10) acting in the first mesh direction. -/
def dirOp (w : Y₂ → D₁ → ℝ) (α : ℝ) (U : Matrix C₁ C₂ ℝ) : Matrix C₁ C₂ ℝ :=
  ∑ s, M₁.matC s * U * (M₂.matM fun y => w y s)ᵀ + (α / 2) • (M₁.matD * U)
    + ∑ p, ∑ s, M₁.matB p s * U * (M₂.matM fun y => PolyMesh.upInd (M₁.pNormal p) w y * w y s)ᵀ

/-- (2.10) is the sum of its two directional parts. -/
lemma tensorL_eq_dirOp (w₁ : Y₂ → D₁ → ℝ) (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) (U : Matrix C₁ C₂ ℝ) :
    tensorL M₁ M₂ w₁ w₂ α U = -(dirOp M₁ M₂ w₁ α U + (dirOp M₂ M₁ w₂ α Uᵀ)ᵀ) := by
  simp only [tensorL, dirOp, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sum,
    Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, smul_add]
  congr 1
  abel

/-- The numerical flux in the first direction, in the scaled values `V`. -/
def dirG (w : Y₂ → D₁ → ℝ) (α : ℝ) (V : C₁ → ℝ) (j : C₂) (e : F₁) : ℝ :=
  M₁.area e * (M₂.mean (fun y => ∑ s, M₁.normal e s * w y s) j
      * ((V (M₁.side₁ e) + V (M₁.side₂ e)) / 2)
    + α / 2 * (V (M₁.side₁ e) - V (M₁.side₂ e)))

/-- The upwind boundary flux in the first direction, in the scaled values `V`. -/
def dirH (w : Y₂ → D₁ → ℝ) (V : C₁ → ℝ) (j : C₂) (β : B₁) : ℝ :=
  M₁.bArea β * ((M₂.mean (fun y => ∑ s, M₁.pNormal (M₁.piece β) s * w y s) j
    + M₂.mean (fun y => |∑ s, M₁.pNormal (M₁.piece β) s * w y s|) j) / 2 * V (M₁.bCell β))

/-- The entries of the first-direction part of (2.10). -/
lemma dirOp_apply {w : Y₂ → D₁ → ℝ} (hw : ∀ j s, IntegrableOn (fun y => w y s) (M₂.cell j) M₂.μ)
    (α : ℝ) (U : Matrix C₁ C₂ ℝ) (i : C₁) (j : C₂) :
    dirOp M₁ M₂ w α U i j
      = (∑ e with M₁.side₁ e = i, dirG M₁ M₂ w α (fun k => U k j / √(M₁.vol k)) j e
        - ∑ e with M₁.side₂ e = i, dirG M₁ M₂ w α (fun k => U k j / √(M₁.vol k)) j e
        + ∑ β with M₁.bCell β = i, dirH M₁ M₂ w (fun k => U k j / √(M₁.vol k)) j β)
      / √(M₁.vol i) := by
  set V : C₁ → ℝ := fun k => U k j / √(M₁.vol k) with hV
  have t1 : (∑ s, M₁.matC s * U * (M₂.matM fun y => w y s)ᵀ) i j
      = ∑ e, M₁.area e * (M₂.mean (fun y => ∑ s, M₁.normal e s * w y s) j
          * ((V (M₁.side₁ e) + V (M₁.side₂ e)) / 2)) * M₁.jumpφ e i := by
    rw [Matrix.sum_apply]
    simp only [PolyMesh.matM_eq_diagonal, Matrix.diagonal_transpose, Matrix.mul_diagonal,
      PolyMesh.matC_mul_apply, PolyMesh.sum_avgφ_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← M₂.sum_mul_mean _ (hw j), Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by simp only [hV]; ring
  have t2 : ((α / 2) • (M₁.matD * U)) i j
      = ∑ e, M₁.area e * (α / 2 * (V (M₁.side₁ e) - V (M₁.side₂ e))) * M₁.jumpφ e i := by
    simp only [Matrix.smul_apply, smul_eq_mul, PolyMesh.matD_mul_apply, PolyMesh.sum_jumpφ_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [hV]; ring
  have t3 : (∑ p, ∑ s, M₁.matB p s * U
        * (M₂.matM fun y => PolyMesh.upInd (M₁.pNormal p) w y * w y s)ᵀ) i j
      = ∑ β, dirH M₁ M₂ w V j β * M₁.traceφ M₁.bCell β i := by
    rw [Matrix.sum_apply, ← Finset.sum_fiberwise _ M₁.piece]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.sum_apply]
    simp only [PolyMesh.matM_eq_diagonal, Matrix.diagonal_transpose, Matrix.mul_diagonal,
      PolyMesh.matB_mul_apply, PolyMesh.sum_traceφ_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hp : M₁.piece β = p := (Finset.mem_filter.1 hβ).2
    simp only [dirH, ← hp]
    rw [← M₂.sum_mul_mean_up _ (hw j), Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by simp only [hV]; ring
  have hsum : ∀ e, dirG M₁ M₂ w α V j e * M₁.jumpφ e i
      = dirG M₁ M₂ w α V j e * M₁.traceφ M₁.side₁ e i
        - dirG M₁ M₂ w α V j e * M₁.traceφ M₁.side₂ e i := fun e => by
    simp only [PolyMesh.jumpφ]; ring
  have t12 : (∑ s, M₁.matC s * U * (M₂.matM fun y => w y s)ᵀ) i j
      + ((α / 2) • (M₁.matD * U)) i j = ∑ e, dirG M₁ M₂ w α V j e * M₁.jumpφ e i := by
    rw [t1, t2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by simp only [dirG]; ring
  have : dirOp M₁ M₂ w α U i j = (∑ s, M₁.matC s * U * (M₂.matM fun y => w y s)ᵀ) i j
      + ((α / 2) • (M₁.matD * U)) i j + (∑ p, ∑ s, M₁.matB p s * U
        * (M₂.matM fun y => PolyMesh.upInd (M₁.pNormal p) w y * w y s)ᵀ) i j := rfl
  rw [this, t12, t3]
  simp only [hsum]
  rw [Finset.sum_sub_distrib, M₁.sum_mul_traceφ, M₁.sum_mul_traceφ, M₁.sum_mul_traceφ]
  ring

/-- The cell averages `û_{ij} = U_{ij} / √(|K_i| |K_j|)` of the piecewise constant function with
coefficient matrix `U` in the basis `φ_i ⊗ φ_j`. -/
def hatU (U : Matrix C₁ C₂ ℝ) (p : C₁ × C₂) : ℝ :=
  U p.1 p.2 / (√(M₁.vol p.1) * √(M₂.vol p.2))

/-- arXiv 2609.02721, Section 2: **the matrix ODE (2.10) is the finite volume cell balance.**  With
the matrices `C_s, D, B_{μ,s}, M_b` defined entrywise as in the paper, the homogeneous right-hand
side `L_h(U)` of (2.10) is the discrete divergence of Appendix A (A.1) on the product mesh, for the
Lax–Friedrichs flux on interior and the upwind flux on boundary faces, in the scaling
`U_{ij} = √(|K_i| |K_j|) û_{ij}`. -/
theorem tensorL_apply {w₁ : Y₂ → D₁ → ℝ} {w₂ : Y₁ → D₂ → ℝ}
    (hw₁ : ∀ j s, IntegrableOn (fun y => w₁ y s) (M₂.cell j) M₂.μ)
    (hw₂ : ∀ i s, IntegrableOn (fun y => w₂ y s) (M₁.cell i) M₁.μ) (α : ℝ)
    (U : Matrix C₁ C₂ ℝ) (i : C₁) (j : C₂) :
    tensorL M₁ M₂ w₁ w₂ α U i j = -(√(M₁.vol i) * √(M₂.vol j))
      * (M₁.toFVMesh.prod M₂.toFVMesh).div (tensorCoeff M₁ M₂ w₁ w₂ α) (hatU M₁ M₂ U) (i, j) := by
  set c := tensorCoeff M₁ M₂ w₁ w₂ α
  set M := M₁.toFVMesh.prod M₂.toFVMesh with hM
  set r := √(M₁.vol i) with hr
  set ρ := √(M₂.vol j) with hρ
  have hr0 : 0 < r := Real.sqrt_pos.2 (M₁.vol_pos i)
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (M₂.vol_pos j)
  have hrr : r * r = M₁.vol i := Real.mul_self_sqrt (M₁.vol_pos i).le
  have hρρ : ρ * ρ = M₂.vol j := Real.mul_self_sqrt (M₂.vol_pos j).le
  have f1 : ∀ e, M.faceFlux c (hatU M₁ M₂ U) (Sum.inl (e, j))
      = ρ * dirG M₁ M₂ w₁ α (fun k => U k j / √(M₁.vol k)) j e := fun e => by
    simp only [FVMesh.faceFlux, dirG, hatU, hM, FVMesh.prod, prodIdx, Sum.elim_inl, c, tensorCoeff]
    rw [← hρ, ← hρρ]
    field_simp
  have f2 : ∀ f, M.faceFlux c (hatU M₁ M₂ U) (Sum.inr (i, f))
      = r * dirG M₂ M₁ w₂ α (fun k => Uᵀ k i / √(M₂.vol k)) i f := fun f => by
    simp only [FVMesh.faceFlux, dirG, hatU, hM, FVMesh.prod, prodIdx, Sum.elim_inr, c, tensorCoeff,
      Matrix.transpose_apply]
    rw [← hr, ← hrr]
    field_simp
  have f3 : ∀ β, M.bdryFlux c (hatU M₁ M₂ U) (Sum.inl (β, j))
      = ρ * dirH M₁ M₂ w₁ (fun k => U k j / √(M₁.vol k)) j β := fun β => by
    simp only [FVMesh.bdryFlux, dirH, hatU, hM, FVMesh.prod, prodIdx, Sum.elim_inl, c, tensorCoeff]
    rw [← hρ, ← hρρ]
    field_simp
  have f4 : ∀ β, M.bdryFlux c (hatU M₁ M₂ U) (Sum.inr (i, β))
      = r * dirH M₂ M₁ w₂ (fun k => Uᵀ k i / √(M₂.vol k)) i β := fun β => by
    simp only [FVMesh.bdryFlux, dirH, hatU, hM, FVMesh.prod, prodIdx, Sum.elim_inr, c, tensorCoeff,
      Matrix.transpose_apply]
    rw [← hr, ← hrr]
    field_simp
  have s1 := sum_filter_prodIdx M₁.side₁ M₂.side₁ (M.faceFlux c (hatU M₁ M₂ U)) i j
  have s2 := sum_filter_prodIdx M₁.side₂ M₂.side₂ (M.faceFlux c (hatU M₁ M₂ U)) i j
  have s3 := sum_filter_prodIdx M₁.bCell M₂.bCell (M.bdryFlux c (hatU M₁ M₂ U)) i j
  have hdiv : M.div c (hatU M₁ M₂ U) (i, j)
      = (∑ x with prodIdx M₁.side₁ M₂.side₁ x = (i, j), M.faceFlux c (hatU M₁ M₂ U) x
        - ∑ x with prodIdx M₁.side₂ M₂.side₂ x = (i, j), M.faceFlux c (hatU M₁ M₂ U) x
        + ∑ x with prodIdx M₁.bCell M₂.bCell x = (i, j), M.bdryFlux c (hatU M₁ M₂ U) x)
        / (M₁.vol i * M₂.vol j) := rfl
  rw [hdiv, s1, s2, s3]
  simp only [f1, f2, f3, f4, ← Finset.mul_sum]
  rw [tensorL_eq_dirOp, Matrix.neg_apply, Matrix.add_apply, Matrix.transpose_apply,
    dirOp_apply M₁ M₂ hw₁, dirOp_apply M₂ M₁ hw₂, ← hr, ← hρ, ← hrr, ← hρρ]
  field_simp
  ring

/-- At the level of cell averages, `∑_K |K| û_K² = ‖U‖_F²`. -/
lemma energy_hatU (U : Matrix C₁ C₂ ℝ) :
    (M₁.toFVMesh.prod M₂.toFVMesh).energy (hatU M₁ M₂ U) = ‖U‖ ^ 2 := by
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
  simp only [FVMesh.energy, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := M₁.vol_pos i
  have h2 := M₂.vol_pos j
  change M₁.vol i * M₂.vol j * (U i j / (√(M₁.vol i) * √(M₂.vol j))) ^ 2 = U i j ^ 2
  rw [div_pow, mul_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
  field_simp

/-- The function `u_h = ∑_{ij} U_{ij} φ_i ⊗ φ_j` of the tensorised finite volume space. -/
def tensorFn (U : Matrix C₁ C₂ ℝ) (z : Y₁ × Y₂) : ℝ :=
  ∑ i, ∑ j, U i j * M₁.φ i z.1 * M₂.φ j z.2

/-- arXiv 2609.02721, Section 2: with normalised cell indicators, `‖u_h‖_{L²(Ω)} = ‖U‖_F`.  Here
`Ω ⊂ Y₁ × Y₂` carries the product measure and the cells are disjoint measurable sets of the
given volumes. -/
theorem integral_sq_tensorFn [SFinite M₂.μ] (U : Matrix C₁ C₂ ℝ) :
    ∫ z, tensorFn M₁ M₂ U z ^ 2 ∂(M₁.μ.prod M₂.μ) = ‖U‖ ^ 2 := by
  set cell : C₁ × C₂ → Set (Y₁ × Y₂) := fun p => M₁.cell p.1 ×ˢ M₂.cell p.2 with hcell
  have hm : ∀ p, MeasurableSet (cell p) := fun p => (M₁.cell_meas _).prod (M₂.cell_meas _)
  have hd : Pairwise (Function.onFun Disjoint cell) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    simp only [Function.onFun, hcell]
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨hx', hy'⟩
    by_cases h : i = k
    · subst h
      have hjl : j ≠ l := fun h' => hne (by rw [h'])
      exact Set.disjoint_left.1 (M₂.cell_disj hjl) hy hy'
    · exact Set.disjoint_left.1 (M₁.cell_disj h) hx hx'
  have hf : ∀ p, (M₁.μ.prod M₂.μ) (cell p) ≠ ∞ := fun p => by
    simp only [hcell]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (M₁.measure_ne_top _) (M₂.measure_ne_top _)
  have hpt : ∀ z, tensorFn M₁ M₂ U z
      = ∑ p, hatU M₁ M₂ U p * (cell p).indicator (fun _ => (1 : ℝ)) z := by
    rintro ⟨x, y⟩
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hx : x ∈ M₁.cell i
    · by_cases hy : y ∈ M₂.cell j
      · have hxy : (x, y) ∈ cell (i, j) := ⟨hx, hy⟩
        simp only [PolyMesh.φ, indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hxy, hatU]
        field_simp
      · have hxy : (x, y) ∉ cell (i, j) := fun h => hy h.2
        simp [PolyMesh.φ, indicator_of_notMem hy, indicator_of_notMem hxy]
    · have hxy : (x, y) ∉ cell (i, j) := fun h => hx h.1
      simp [PolyMesh.φ, indicator_of_notMem hx, indicator_of_notMem hxy]
  simp_rw [hpt]
  rw [integral_sq_sum_indicator hm hd hf, ← energy_hatU M₁ M₂ U]
  simp only [FVMesh.energy]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [hcell]
  rw [measureReal_prod_prod, M₁.vol_eq, M₂.vol_eq]
  rfl

/-- The forward Euler step of (2.10) in the coefficient matrix is the finite volume step (A.1) in
the cell averages. -/
lemma hatU_add_smul_tensorL {w₁ : Y₂ → D₁ → ℝ} {w₂ : Y₁ → D₂ → ℝ}
    (hw₁ : ∀ j s, IntegrableOn (fun y => w₁ y s) (M₂.cell j) M₂.μ)
    (hw₂ : ∀ i s, IntegrableOn (fun y => w₂ y s) (M₁.cell i) M₁.μ) (α τ : ℝ)
    (U : Matrix C₁ C₂ ℝ) :
    hatU M₁ M₂ (U + τ • tensorL M₁ M₂ w₁ w₂ α U)
      = (M₁.toFVMesh.prod M₂.toFVMesh).euler (tensorCoeff M₁ M₂ w₁ w₂ α) τ (hatU M₁ M₂ U) := by
  funext ⟨i, j⟩
  have h1 : √(M₁.vol i) ≠ 0 := (Real.sqrt_pos.2 (M₁.vol_pos i)).ne'
  have h2 : √(M₂.vol j) ≠ 0 := (Real.sqrt_pos.2 (M₂.vol_pos j)).ne'
  simp only [hatU, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    tensorL_apply M₁ M₂ hw₁ hw₂, FVMesh.euler]
  field_simp
  ring

/-- arXiv 2609.02721, Lemma 4.1, one step.  `L²` stability of one forward Euler step of the
tensorised scheme, for the matrix right-hand side (2.10), under the CFL condition of the product
mesh. -/
theorem norm_add_smul_tensorL_le {w₁ : Y₂ → D₁ → ℝ} {w₂ : Y₁ → D₂ → ℝ} {α τ : ℝ}
    (hw₁ : ∀ j s, IntegrableOn (fun y => w₁ y s) (M₂.cell j) M₂.μ)
    (hw₂ : ∀ i s, IntegrableOn (fun y => w₂ y s) (M₁.cell i) M₁.μ)
    (hα₁ : ∀ e j, ∀ y ∈ M₂.cell j, |∑ s, M₁.normal e s * w₁ y s| ≤ α)
    (hα₂ : ∀ f i, ∀ y ∈ M₁.cell i, |∑ s, M₂.normal f s * w₂ y s| ≤ α) (hτ : 0 ≤ τ)
    (hcfl : ∀ K, τ * (M₁.toFVMesh.prod M₂.toFVMesh).cflRate (tensorCoeff M₁ M₂ w₁ w₂ α) K ≤ 1)
    (U : Matrix C₁ C₂ ℝ) : ‖U + τ • tensorL M₁ M₂ w₁ w₂ α U‖ ≤ ‖U‖ := by
  have h := (M₁.toFVMesh.prod M₂.toFVMesh).energy_euler_le
    (tensorCoeff_admissible M₁ M₂ hw₁ hw₂ hα₁ hα₂) hτ hcfl (hatU M₁ M₂ U)
  rw [← hatU_add_smul_tensorL M₁ M₂ hw₁ hw₂, energy_hatU, energy_hatU] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The right-hand side of (2.10) is linear. -/
lemma tensorL_sub (w₁ : Y₂ → D₁ → ℝ) (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) (U V : Matrix C₁ C₂ ℝ) :
    tensorL M₁ M₂ w₁ w₂ α (U - V) = tensorL M₁ M₂ w₁ w₂ α U - tensorL M₁ M₂ w₁ w₂ α V := by
  simp only [tensorL, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, smul_sub, smul_add]
  abel

/-- The index set of the Kronecker terms of (2.10). -/
abbrev KronIdx (D₁ D₂ P₁ P₂ : Type*) : Type _ :=
  (D₁ ⊕ D₂) ⊕ (Unit ⊕ Unit) ⊕ (P₁ × D₁) ⊕ (P₂ × D₂)

/-- The left factors `A_k` of (2.10). -/
def kronA (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) : KronIdx D₁ D₂ P₁ P₂ → Matrix C₁ C₁ ℝ
  | .inl (.inl s) => -M₁.matC s
  | .inl (.inr s) => -(M₁.matM fun y => w₂ y s)
  | .inr (.inl (.inl _)) => -(α / 2) • M₁.matD
  | .inr (.inl (.inr _)) => -(α / 2) • 1
  | .inr (.inr (.inl q)) => -M₁.matB q.1 q.2
  | .inr (.inr (.inr q)) => -(M₁.matM fun y => PolyMesh.upInd (M₂.pNormal q.1) w₂ y * w₂ y q.2)

/-- The right factors `B_k` of (2.10). -/
def kronB (w₁ : Y₂ → D₁ → ℝ) : KronIdx D₁ D₂ P₁ P₂ → Matrix C₂ C₂ ℝ
  | .inl (.inl s) => M₂.matM fun y => w₁ y s
  | .inl (.inr s) => M₂.matC s
  | .inr (.inl (.inl _)) => 1
  | .inr (.inl (.inr _)) => M₂.matD
  | .inr (.inr (.inl q)) => M₂.matM fun y => PolyMesh.upInd (M₁.pNormal q.1) w₁ y * w₁ y q.2
  | .inr (.inr (.inr q)) => M₂.matB q.1 q.2

/-- arXiv 2609.02721, Section 3: the homogeneous right-hand side of (2.10) has the Kronecker form
`L_h(U) = ∑_k A_k U B_kᵀ`. -/
theorem tensorL_eq_kron (w₁ : Y₂ → D₁ → ℝ) (w₂ : Y₁ → D₂ → ℝ) (α : ℝ) (U : Matrix C₁ C₂ ℝ) :
    tensorL M₁ M₂ w₁ w₂ α U = ∑ k, kronA M₁ M₂ w₂ α k * U * (kronB M₁ M₂ w₁ k)ᵀ := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, kronA, kronB, tensorL, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one, Finset.sum_neg_distrib,
    Finset.univ_unique, Finset.sum_singleton, smul_add, neg_smul]
  abel

end Tensor

/-- A Kronecker sum is bounded by the sum of the Frobenius norms of its factors (Section 2 of
arXiv 2609.02721). -/
lemma norm_sum_kron_le {K m n : Type*} [Fintype K] [Fintype m] [Fintype n]
    (A : K → Matrix m m ℝ) (B : K → Matrix n n ℝ) (U : Matrix m n ℝ) :
    ‖∑ k, A k * U * (B k)ᵀ‖ ≤ (∑ k, ‖A k‖ * ‖B k‖) * ‖U‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  calc ‖A k * U * (B k)ᵀ‖ ≤ ‖A k * U‖ * ‖(B k)ᵀ‖ := LeanDLRA.Frobenius.norm_mul_le _ _
    _ ≤ ‖A k‖ * ‖U‖ * ‖B k‖ := by
        rw [LeanDLRA.Frobenius.norm_transpose]
        exact mul_le_mul_of_nonneg_right (LeanDLRA.Frobenius.norm_mul_le _ _) (norm_nonneg _)
    _ = ‖A k‖ * ‖B k‖ * ‖U‖ := by ring

/-- arXiv 2609.02721, Sections 2 and 3: an affine Kronecker-structured field
`F_h(t, U) = ∑_k A_k(t) U B_k(t)ᵀ + G(t)`, such as the right-hand side of (2.10) by
`tensorL_eq_kron` (with `G` the inflow term `tensorInflow`), is globally Lipschitz.  The Lipschitz
constant is any uniform bound of `∑_k ‖A_k(t)‖_F ‖B_k(t)‖_F`. -/
theorem kron_isLipschitzField {K m n : Type*} [Fintype K] [Fintype m] [Fintype n]
    (A : ℝ → K → Matrix m m ℝ) (B : ℝ → K → Matrix n n ℝ) (G : ℝ → Matrix m n ℝ) {L : ℝ}
    (hL : ∀ t, ∑ k, ‖A t k‖ * ‖B t k‖ ≤ L) :
    IsLipschitzField (fun t (U : Matrix m n ℝ) => ∑ k, A t k * U * (B t k)ᵀ + G t) L := by
  intro t U V
  have e : (∑ k, A t k * U * (B t k)ᵀ + G t) - (∑ k, A t k * V * (B t k)ᵀ + G t)
      = ∑ k, A t k * (U - V) * (B t k)ᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    abel
  simp only [e]
  exact (norm_sum_kron_le _ _ _).trans (mul_le_mul_of_nonneg_right (hL t) (norm_nonneg _))

section Inflow

variable {C₁ F₁ B₁ P₁ D₁ Y₁ C₂ F₂ B₂ P₂ D₂ Y₂ N : Type*}
  [Fintype C₁] [Fintype F₁] [Fintype B₁] [Fintype P₁] [Fintype D₁] [DecidableEq C₁]
  [DecidableEq P₁] [MeasurableSpace Y₁]
  [Fintype C₂] [Fintype F₂] [Fintype B₂] [DecidableEq C₂] [MeasurableSpace Y₂] [Fintype N]
  (M₁ : PolyMesh C₁ F₁ B₁ P₁ D₁ Y₁) (M₂ : PolyMesh C₂ F₂ B₂ P₂ D₂ Y₂)

/-- Separable inflow data on the boundary of the first mesh at a fixed time,
`g = ∑_ν g_ν^(1) ⊗ g_ν^(2)`: `gB ν β` is the mean of `g_ν^(1)` over the boundary face `β` and
`g₂ ν` is the second factor. -/
structure SepInflow (N B₁ Y₂ : Type*) where
  /-- The face means of the first factors. -/
  gB : N → B₁ → ℝ
  /-- The second factors. -/
  g₂ : N → Y₂ → ℝ

/-- The inflow vector `(G_{ν,μ,s}^(1))_i = ∑_{e ∈ ℰ_{b,μ}} ∫_e n_s^μ g_ν^(1) φ_i dS`. -/
def inflowG₁ (g : SepInflow N B₁ Y₂) (ν : N) (p : P₁) (s : D₁) (i : C₁) : ℝ :=
  ∑ β with M₁.piece β = p,
    M₁.bArea β * M₁.pNormal p s * g.gB ν β * M₁.traceφ M₁.bCell β i

/-- The inflow vector `(G_{ν,μ,s}^(2))_j = ∑_K ∫_K (1 - χ_μ) w_s g_ν^(2) φ_j`. -/
def inflowG₂ (w : Y₂ → D₁ → ℝ) (g : SepInflow N B₁ Y₂) (ν : N) (p : P₁) (s : D₁) (j : C₂) : ℝ :=
  ∫ y, (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s * g.g₂ ν y * M₂.φ j y ∂M₂.μ

/-- The inflow term `B_h = -∑_ν ∑_μ ∑_s G_{ν,μ,s}^(1) G_{ν,μ,s}^(2)ᵀ` of (2.10), a sum of rank-one
matrices `a_ℓ b_ℓᵀ`. -/
def tensorInflow (w : Y₂ → D₁ → ℝ) (g : SepInflow N B₁ Y₂) : Matrix C₁ C₂ ℝ :=
  -∑ ν, ∑ p, ∑ s, Matrix.vecMulVec (inflowG₁ M₁ g ν p s) (inflowG₂ M₁ M₂ w g ν p s)

/-- The inflow flux `∫_{β × K_j} (1 - χ) (n · w) g` through the face `β × K_j` of the product mesh
(for `w = v` the upwind flux `(n · v) g` on the inflow part `n · v < 0`). -/
def inflowFlux (w : Y₂ → D₁ → ℝ) (g : SepInflow N B₁ Y₂) (β : B₁) (j : C₂) : ℝ :=
  ∑ ν, M₁.bArea β * g.gB ν β * ∫ y in M₂.cell j,
    (1 - PolyMesh.upInd (M₁.pNormal (M₁.piece β)) w y)
      * (∑ s, M₁.pNormal (M₁.piece β) s * w y s) * g.g₂ ν y ∂M₂.μ

/-- arXiv 2609.02721, Section 2: **the inflow term of (2.10) is the upwind inflow of the cell
balance.**  For separable inflow data the rank-structured matrix `B_h` of (2.10) is, in the scaling
`U_{ij} = √(|K_i| |K_j|) û_{ij}`, the sum of the inflow fluxes through the boundary faces of the
cell.  The face means of `g_ν^(1)` are data, as Mathlib has no surface measure on the faces. -/
theorem tensorInflow_apply {w : Y₂ → D₁ → ℝ} (g : SepInflow N B₁ Y₂)
    (hg : ∀ ν p s j, IntegrableOn
      (fun y => (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s * g.g₂ ν y) (M₂.cell j) M₂.μ)
    (i : C₁) (j : C₂) :
    tensorInflow M₁ M₂ w g i j
      = -(∑ β with M₁.bCell β = i, inflowFlux M₁ M₂ w g β j) / (√(M₁.vol i) * √(M₂.vol j)) := by
  have h2 : ∀ ν p s, inflowG₂ M₁ M₂ w g ν p s j
      = (∫ y in M₂.cell j, (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s * g.g₂ ν y ∂M₂.μ)
        / √(M₂.vol j) := by
    intro ν p s
    have hpt : ∀ y, (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s * g.g₂ ν y * M₂.φ j y
        = (M₂.cell j).indicator (fun y => (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s
          * g.g₂ ν y / √(M₂.vol j)) y := by
      intro y
      by_cases hy : y ∈ M₂.cell j
      · simp only [PolyMesh.φ, indicator_of_mem hy, div_eq_mul_inv]
      · simp [PolyMesh.φ, hy]
    simp only [inflowG₂, hpt]
    rw [integral_indicator (M₂.cell_meas j), integral_div]
  have h3 : ∀ ν p, ∑ s, M₁.pNormal p s
        * ∫ y in M₂.cell j, (1 - PolyMesh.upInd (M₁.pNormal p) w y) * w y s * g.g₂ ν y ∂M₂.μ
      = ∫ y in M₂.cell j, (1 - PolyMesh.upInd (M₁.pNormal p) w y)
          * (∑ s, M₁.pNormal p s * w y s) * g.g₂ ν y ∂M₂.μ := by
    intro ν p
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun s _ => (hg ν p s j).const_mul _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  have h4 : ∀ ν p, ∑ s, inflowG₁ M₁ g ν p s i * inflowG₂ M₁ M₂ w g ν p s j
      = ∑ β with M₁.piece β = p, (M₁.bArea β * g.gB ν β * ∫ y in M₂.cell j,
          (1 - PolyMesh.upInd (M₁.pNormal (M₁.piece β)) w y)
            * (∑ s, M₁.pNormal (M₁.piece β) s * w y s) * g.g₂ ν y ∂M₂.μ)
          * M₁.traceφ M₁.bCell β i / √(M₂.vol j) := by
    intro ν p
    simp only [h2, inflowG₁, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hp : M₁.piece β = p := (Finset.mem_filter.1 hβ).2
    rw [hp, ← h3, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have h5 : ∀ ν, ∑ p, ∑ s, inflowG₁ M₁ g ν p s i * inflowG₂ M₁ M₂ w g ν p s j
      = ∑ β, (M₁.bArea β * g.gB ν β * ∫ y in M₂.cell j,
          (1 - PolyMesh.upInd (M₁.pNormal (M₁.piece β)) w y)
            * (∑ s, M₁.pNormal (M₁.piece β) s * w y s) * g.g₂ ν y ∂M₂.μ)
          * M₁.traceφ M₁.bCell β i / √(M₂.vol j) := by
    intro ν
    simp only [h4]
    exact Finset.sum_fiberwise _ _ _
  have h6 : tensorInflow M₁ M₂ w g i j = -∑ ν, ∑ p, ∑ s,
      inflowG₁ M₁ g ν p s i * inflowG₂ M₁ M₂ w g ν p s j := by
    simp [tensorInflow, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [h6]
  simp only [h5]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.sum_div]
  rw [M₁.sum_mul_traceφ]
  simp only [inflowFlux]
  field_simp

end Inflow

/-! ### The rank-adaptive step-and-truncate scheme (Algorithms 1 and 2) -/

section SAT

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A low-rank factorisation `X S Vᵀ` with orthonormal factors. -/
structure LRFactors (m n : Type*) [Fintype m] [Fintype n] where
  /-- The rank parameter. -/
  r : ℕ
  /-- The left factor. -/
  X : Matrix m (Fin r) ℝ
  /-- The core. -/
  S : Matrix (Fin r) (Fin r) ℝ
  /-- The right factor. -/
  V : Matrix n (Fin r) ℝ
  X_orth : Xᵀ * X = 1
  V_orth : Vᵀ * V = 1

/-- The matrix `X S Vᵀ`. -/
def LRFactors.mat (Y : LRFactors m n) : Matrix m n ℝ := Y.X * Y.S * Y.Vᵀ

/-- `Y` is a valid output of the truncated SVD `𝒯_ε^svd(A)` of Algorithm 1: `Y.S = diag(σ)`, `σ ≥
0`, the columns of `Y.X`, `Y.V` are pairs of singular vectors of `A` with singular values `σ`, and
the truncation error is at most `ε`.  Nothing else about the chosen singular triplets is used. The
bound `‖𝒯_ε(A)‖_F ≤ ‖A‖_F` is derived, see `IsTruncSVD.norm_le`. -/
structure IsTruncSVD (ε : ℝ) (A : Matrix m n ℝ) (Y : LRFactors m n) : Prop where
  diag : ∃ σ : Fin Y.r → ℝ, (∀ i, 0 ≤ σ i) ∧ Y.S = Matrix.diagonal σ
  mul_V : A * Y.V = Y.X * Y.S
  transpose_mul_X : Aᵀ * Y.X = Y.V * Y.S
  err : ‖Y.mat - A‖ ≤ ε

/-- arXiv 2609.02721, Algorithm 1: SVD truncation is nonexpansive in the Frobenius norm. -/
theorem IsTruncSVD.norm_le {ε : ℝ} {A : Matrix m n ℝ} {Y : LRFactors m n} (h : IsTruncSVD ε A Y) :
    ‖Y.mat‖ ≤ ‖A‖ := by
  have e : Y.mat = rightProj Y.V A := by
    simp only [LRFactors.mat, rightProj_apply, h.mul_V]
  rw [e]
  exact (isOrthProj_rightProj Y.V_orth).norm_le A

/-- arXiv 2609.02721, Algorithm 1 is executable: the exact SVD is a valid truncation for every
tolerance. -/
theorem exists_isTruncSVD [DecidableEq n] {ε : ℝ} (hε : 0 ≤ ε) (A : Matrix m n ℝ) :
    ∃ Y, IsTruncSVD ε A Y := by
  obtain ⟨r, hr⟩ : ∃ r, A.rank = r := ⟨_, rfl⟩
  obtain ⟨U, V, σ, hU, hV, -, hσ, -, hA⟩ := LeanDLRA.SVD.exists_svd A hr
  refine ⟨⟨r, U, Matrix.diagonal σ, V, hU, hV⟩, ⟨σ, fun i => (hσ i).le, rfl⟩, ?_, ?_, ?_⟩
  · change A * V = U * Matrix.diagonal σ
    rw [hA, Matrix.mul_assoc, hV, Matrix.mul_one]
  · change Aᵀ * U = V * Matrix.diagonal σ
    rw [hA]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, hU, Matrix.mul_one]
  · change ‖U * Matrix.diagonal σ * Vᵀ - A‖ ≤ ε
    rw [← hA, sub_self, norm_zero]
    exact hε

/-- `Q` is an admissible `ortho[A, B]`: it has orthonormal columns whose span contains the
columns of `A` and `B`. -/
def IsOrthoOf {l : Type*} [Fintype l] {q a b : ℕ} (Q : Matrix l (Fin q) ℝ) (A : Matrix l (Fin a) ℝ)
    (B : Matrix l (Fin b) ℝ) : Prop :=
  Qᵀ * Q = 1 ∧ Q * Qᵀ * A = A ∧ Q * Qᵀ * B = B

/-- arXiv 2609.02721, Algorithm 2: `ortho[A, B]` exists; take the left singular vectors of the block
matrix. -/
theorem exists_isOrthoOf {l : Type*} [Fintype l] {a b : ℕ} (A : Matrix l (Fin a) ℝ)
    (B : Matrix l (Fin b) ℝ) : ∃ (q : ℕ) (Q : Matrix l (Fin q) ℝ), IsOrthoOf Q A B := by
  obtain ⟨r, hr⟩ : ∃ r, (Matrix.fromCols A B).rank = r := ⟨_, rfl⟩
  obtain ⟨U, V, σ, hU, -, -, -, -, hA⟩ := LeanDLRA.SVD.exists_svd (Matrix.fromCols A B) hr
  have key : U * Uᵀ * Matrix.fromCols A B = Matrix.fromCols A B := by
    rw [hA]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc U, hU, Matrix.mul_one]
  rw [Matrix.mul_fromCols] at key
  obtain ⟨h1, h2⟩ := Matrix.fromCols_inj key
  exact ⟨_, U, hU, h1, h2⟩

/-- One step of Algorithm 2 (rank-adaptive step-and-truncate) from `Y = (Xⁿ, Sⁿ, Vⁿ)` to `Y'`, with
`G = F_h(tⁿ, Uⁿ)`:
1. `(X̄, S̄, V̄) = 𝒯_{ε₁}^svd(G)`;
2. `X̃ = ortho[Xⁿ, X̄]`, `Ṽ = ortho[Vⁿ, V̄]`;
3. `S̃ⁿ = (X̃ᵀ Xⁿ) Sⁿ (Ṽᵀ Vⁿ)ᵀ`, `S̃ⁿ⁺¹ = S̃ⁿ + τ X̃ᵀ G Ṽ`;
4. `Y' = 𝒯_{ε₂}^svd(X̃ S̃ⁿ⁺¹ Ṽᵀ)`. -/
def IsSATStep (G : Matrix m n ℝ) (τ ε₁ ε₂ : ℝ) (Y Y' : LRFactors m n) : Prop :=
  ∃ (Ybar : LRFactors m n) (q q' : ℕ) (Xt : Matrix m (Fin q) ℝ) (Vt : Matrix n (Fin q') ℝ),
    IsTruncSVD ε₁ G Ybar ∧ IsOrthoOf Xt Y.X Ybar.X ∧ IsOrthoOf Vt Y.V Ybar.V ∧
    IsTruncSVD ε₂ (Xt * ((Xtᵀ * Y.X) * Y.S * (Vtᵀ * Y.V)ᵀ + τ • (Xtᵀ * G * Vt)) * Vtᵀ) Y'

/-- arXiv 2609.02721, Algorithm 2 can always be carried out: a step exists from every state, for all
tolerances `ε₁, ε₂ ≥ 0`. -/
theorem exists_isSATStep [DecidableEq n] (G : Matrix m n ℝ) {τ ε₁ ε₂ : ℝ} (h₁ : 0 ≤ ε₁)
    (h₂ : 0 ≤ ε₂) (Y : LRFactors m n) : ∃ Y', IsSATStep G τ ε₁ ε₂ Y Y' := by
  obtain ⟨Ybar, hbar⟩ := exists_isTruncSVD h₁ G
  obtain ⟨q, Xt, hX⟩ := exists_isOrthoOf Y.X Ybar.X
  obtain ⟨q', Vt, hV⟩ := exists_isOrthoOf Y.V Ybar.V
  obtain ⟨Y', hY'⟩ := exists_isTruncSVD h₂
    (Xt * ((Xtᵀ * Y.X) * Y.S * (Vtᵀ * Y.V)ᵀ + τ • (Xtᵀ * G * Vt)) * Vtᵀ)
  exact ⟨Y', Ybar, q, q', Xt, Vt, hbar, hX, hV, hY'⟩

/-- arXiv 2609.02721, Algorithm 2 can be iterated: from every initial factorisation there is a
whole sequence of steps, for every feedback right-hand side `G`. -/
theorem exists_satSequence [DecidableEq n] (G : ℕ → Matrix m n ℝ → Matrix m n ℝ) {τ ε₁ ε₂ : ℝ}
    (h₁ : 0 ≤ ε₁) (h₂ : 0 ≤ ε₂) (Y₀ : LRFactors m n) :
    ∃ Y : ℕ → LRFactors m n, Y 0 = Y₀ ∧
      ∀ k, IsSATStep (G k (Y k).mat) τ ε₁ ε₂ (Y k) (Y (k + 1)) := by
  choose f hf using fun (k : ℕ) (Y : LRFactors m n) =>
    exists_isSATStep (G k Y.mat) (τ := τ) h₁ h₂ Y
  exact ⟨fun k => Nat.rec Y₀ (fun k Y => f k Y) k, rfl, fun k => hf k _⟩

/-- arXiv 2609.02721, Section 3: the structure of a step of Algorithm 2.  The intermediate matrix
`X̃ S̃ⁿ⁺¹ Ṽᵀ` is the orthogonal projection `P (Uⁿ + τ G)` of the forward Euler step onto
`span X̃ ⊗ span Ṽ`; moreover `P Uⁿ = Uⁿ`, `‖G - P G‖_F ≤ ε₁` by the best approximation property,
and the truncation is nonexpansive. -/
theorem IsSATStep.exists_proj {G : Matrix m n ℝ} {τ ε₁ ε₂ : ℝ} {Y Y' : LRFactors m n}
    (h : IsSATStep G τ ε₁ ε₂ Y Y') :
    ∃ P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, IsOrthProj P ∧ P Y.mat = Y.mat ∧ ‖G - P G‖ ≤ ε₁ ∧
      ‖Y'.mat - P (Y.mat + τ • G)‖ ≤ ε₂ ∧ ‖Y'.mat‖ ≤ ‖P (Y.mat + τ • G)‖ := by
  obtain ⟨Yb, q, q', Xt, Vt, h1, ⟨hXo, hX1, hX2⟩, ⟨hVo, hV1, hV2⟩, h4⟩ := h
  set P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := leftProj Xt * rightProj Vt with hPdef
  have hP : IsOrthProj P := isOrthProj_leftProj_mul_rightProj hXo hVo
  have hPa : ∀ A, P A = Xt * (Xtᵀ * A * Vt) * Vtᵀ := fun A => leftProj_rightProj_apply Xt Vt A
  have hfix : ∀ Z : LRFactors m n, Xt * Xtᵀ * Z.X = Z.X → Vt * Vtᵀ * Z.V = Z.V →
      P Z.mat = Z.mat := by
    intro Z h1 h2
    have h2' : Z.Vᵀ * (Vt * Vtᵀ) = Z.Vᵀ := by
      have := congrArg Matrix.transpose h2
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    rw [hPa]
    simp only [LRFactors.mat]
    calc Xt * (Xtᵀ * (Z.X * Z.S * Z.Vᵀ) * Vt) * Vtᵀ
        = (Xt * Xtᵀ * Z.X) * Z.S * (Z.Vᵀ * (Vt * Vtᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = Z.X * Z.S * Z.Vᵀ := by rw [h1, h2']
  have hmain : Xt * ((Xtᵀ * Y.X) * Y.S * (Vtᵀ * Y.V)ᵀ + τ • (Xtᵀ * G * Vt)) * Vtᵀ
      = P (Y.mat + τ • G) := by
    have e1 : Xt * ((Xtᵀ * Y.X) * Y.S * (Vtᵀ * Y.V)ᵀ) * Vtᵀ = P Y.mat := by
      rw [hfix Y hX1 hV1]
      have h2' : Y.Vᵀ * (Vt * Vtᵀ) = Y.Vᵀ := by
        have := congrArg Matrix.transpose hV1
        simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
      simp only [LRFactors.mat, Matrix.transpose_mul, Matrix.transpose_transpose]
      calc Xt * (Xtᵀ * Y.X * Y.S * (Y.Vᵀ * Vt)) * Vtᵀ
          = (Xt * Xtᵀ * Y.X) * Y.S * (Y.Vᵀ * (Vt * Vtᵀ)) := by simp only [Matrix.mul_assoc]
        _ = Y.X * Y.S * Y.Vᵀ := by rw [hX1, h2']
    rw [map_add, map_smul, ← e1, hPa G, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  refine ⟨P, hP, hfix Y hX1 hV1, ?_, ?_, ?_⟩
  · refine (hP.norm_sub_le_of_mem_range G Yb.mat (hfix Yb hX2 hV2)).trans ?_
    rw [norm_sub_rev]
    exact h1.err
  · rw [← hmain]; exact h4.err
  · rw [← hmain]; exact h4.norm_le

/-- arXiv 2609.02721, proof of Theorem 4.2: stability is inherited by a step of Algorithm 2 from
the full forward Euler step, with no condition on the tolerances; this is
`augmentedBug_euler_norm_le` of the library with the step of the paper. -/
theorem IsSATStep.norm_le {G : Matrix m n ℝ} {τ ε₁ ε₂ : ℝ} {Y Y' : LRFactors m n}
    (h : IsSATStep G τ ε₁ ε₂ Y Y') (hE : ‖Y.mat + τ • G‖ ≤ ‖Y.mat‖) : ‖Y'.mat‖ ≤ ‖Y.mat‖ := by
  obtain ⟨P, hP, -, -, -, h5⟩ := h.exists_proj
  have := augmentedBug_euler_norm_le (F := fun _ => G) (h := τ) (γ := 1) (u₀ := Y.mat)
    (u₁ := Y'.mat) hP (by simpa [eulerStep] using hE) (by simpa [eulerStep] using h5)
  simpa using this

/-- arXiv 2609.02721, proof of Theorem 4.3: the local error of a step of Algorithm 2 against any
comparison matrix `Z`: `‖Uⁿ⁺¹ - Z‖ ≤ ‖Uⁿ + τ G - Z‖ + τ ε₁ + ε₂`. -/
theorem IsSATStep.norm_sub_le {G : Matrix m n ℝ} {τ ε₁ ε₂ : ℝ} {Y Y' : LRFactors m n}
    (h : IsSATStep G τ ε₁ ε₂ Y Y') (hτ : 0 ≤ τ) (Z : Matrix m n ℝ) :
    ‖Y'.mat - Z‖ ≤ ‖Y.mat + τ • G - Z‖ + τ * ε₁ + ε₂ := by
  obtain ⟨P, hP, hfix, h3, h4, -⟩ := h.exists_proj
  have e : Y'.mat - Z = (Y'.mat - P (Y.mat + τ • G)) + (Y.mat + τ • G - Z)
      - τ • (G - P G) := by
    rw [map_add, map_smul, hfix, smul_sub]; abel
  rw [e]
  calc ‖(Y'.mat - P (Y.mat + τ • G)) + (Y.mat + τ • G - Z) - τ • (G - P G)‖
      ≤ ‖(Y'.mat - P (Y.mat + τ • G)) + (Y.mat + τ • G - Z)‖ + ‖τ • (G - P G)‖ :=
        _root_.norm_sub_le _ _
    _ ≤ ‖Y'.mat - P (Y.mat + τ • G)‖ + ‖Y.mat + τ • G - Z‖ + ‖τ • (G - P G)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ε₂ + ‖Y.mat + τ • G - Z‖ + τ * ε₁ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
        have := mul_le_mul_of_nonneg_left h3 hτ
        linarith
    _ = ‖Y.mat + τ • G - Z‖ + τ * ε₁ + ε₂ := by ring

end SAT

/-! ### The Vlasov equation -/

section Vlasov

variable {ιx Fx Bx Px ιv Fv Bv Pv D X : Type*}
  [Fintype ιx] [Fintype Fx] [Fintype Bx] [Fintype Px] [DecidableEq ιx] [DecidableEq Px]
  [Fintype ιv] [Fintype Fv] [Fintype Bv] [Fintype Pv] [DecidableEq ιv] [DecidableEq Pv]
  [Fintype D] [MeasurableSpace X]

/-- The finite volume discretisation of the linear Vlasov equation
`∂_t u + v · ∇_x u - E(t, x) · ∇_v u = 0` on `Ω^(x) × Ω^(v)` of Section 2: a polyhedral mesh of
the space domain in a measure space `X`, a polyhedral mesh of the velocity domain in `D → ℝ`, the
force field `E` and the global Lax–Friedrichs parameter `α`. -/
structure VlasovFV (ιx Fx Bx Px ιv Fv Bv Pv D X : Type*) [Fintype Fx] [Fintype Bx] [DecidableEq ιx]
    [Fintype Fv] [Fintype Bv] [DecidableEq ιv] [MeasurableSpace X] where
  /-- The space mesh. -/
  Mx : PolyMesh ιx Fx Bx Px D X
  /-- The velocity mesh. -/
  Mv : PolyMesh ιv Fv Bv Pv D (D → ℝ)
  /-- The force field. -/
  E : ℝ → X → D → ℝ
  /-- The global Lax–Friedrichs parameter. -/
  α : ℝ → ℝ

namespace VlasovFV

variable (D' : VlasovFV ιx Fx Bx Px ιv Fv Bv Pv D X)

/-- The velocity component `-E` of the transport field. -/
def force (t : ℝ) (x : X) (s : D) : ℝ := -D'.E t x s

/-- The right-hand side `L_h(t, U)` of the matrix ODE (2.10) with homogeneous inflow. -/
def Lh (t : ℝ) (U : Matrix ιx ιv ℝ) : Matrix ιx ιv ℝ :=
  tensorL D'.Mx D'.Mv (fun v => v) (D'.force t) (D'.α t) U

/-- The product mesh of phase space. -/
def mesh : FVMesh (ιx × ιv) ((Fx × ιv) ⊕ (ιx × Fv)) ((Bx × ιv) ⊕ (ιx × Bv)) :=
  D'.Mx.toFVMesh.prod D'.Mv.toFVMesh

/-- The face coefficients of the scheme at time `t`. -/
def coeff (t : ℝ) : FaceCoeff ((Fx × ιv) ⊕ (ιx × Fv)) ((Bx × ιv) ⊕ (ιx × Bv)) :=
  tensorCoeff D'.Mx D'.Mv (fun v => v) (D'.force t) (D'.α t)

/-- The CFL time step (A.2) of the scheme on `[0, T]`. -/
def tauCFL (T : ℝ) : ℝ≥0∞ := D'.mesh.tauCFL D'.coeff T

/-- The standing assumptions on `[0, T]`: integrable transport coefficients on the cells
(bounded domains and a bounded force in the paper), and the Lax–Friedrichs bound
`α(t) ≥ max_e max_{z ∈ e} |n_e · a(t, z)|` on all interior faces `e × K_j` and `K_i × f`. -/
structure IsRegular (T : ℝ) : Prop where
  v_int : ∀ j s, IntegrableOn (fun v : D → ℝ => v s) (D'.Mv.cell j) D'.Mv.μ
  E_int : ∀ t ∈ Icc 0 T, ∀ i s, IntegrableOn (fun x => D'.E t x s) (D'.Mx.cell i) D'.Mx.μ
  α_x : ∀ t ∈ Icc 0 T, ∀ e j, ∀ v ∈ D'.Mv.cell j, |∑ s, D'.Mx.normal e s * v s| ≤ D'.α t
  α_v : ∀ t ∈ Icc 0 T, ∀ f i, ∀ x ∈ D'.Mx.cell i, |∑ s, D'.Mv.normal f s * D'.E t x s| ≤ D'.α t

variable {D'} {T τ : ℝ}

/-- Integrability of the force on the cells. -/
lemma IsRegular.force_int (hD : D'.IsRegular T) {t : ℝ} (ht : t ∈ Icc 0 T) (i : ιx) (s : D) :
    IntegrableOn (fun x => D'.force t x s) (D'.Mx.cell i) D'.Mx.μ :=
  (hD.E_int t ht i s).neg

/-- The Lax–Friedrichs bound for the velocity faces. -/
lemma IsRegular.force_bound (hD : D'.IsRegular T) {t : ℝ} (ht : t ∈ Icc 0 T) (f : Fv) (i : ιx) :
    ∀ x ∈ D'.Mx.cell i, |∑ s, D'.Mv.normal f s * D'.force t x s| ≤ D'.α t := fun x hx => by
  have : ∑ s, D'.Mv.normal f s * D'.force t x s = -∑ s, D'.Mv.normal f s * D'.E t x s := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp [force]
  rw [this, abs_neg]
  exact hD.α_v t ht f i x hx

/-- arXiv 2609.02721, proof of Lemma A.1 for the Vlasov field: the coefficients of the scheme are
admissible; the identity (A.4) and `|a_e| ≤ b_e` are derived from the geometry. -/
theorem IsRegular.admissible (hD : D'.IsRegular T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (D'.coeff t).Admissible D'.mesh :=
  tensorCoeff_admissible D'.Mx D'.Mv hD.v_int (hD.force_int ht) (hD.α_x t ht)
    (fun f i => hD.force_bound ht f i)

/-- arXiv 2609.02721, Lemma 4.1, one step: a forward Euler step of (2.10) is nonexpansive on
`[0, T]` for `0 ≤ τ ≤ τ_CFL`. -/
theorem IsRegular.euler_norm_le (hD : D'.IsRegular T) (hτ : 0 ≤ τ)
    (hcfl : ENNReal.ofReal τ ≤ D'.tauCFL T) {t : ℝ} (ht : t ∈ Icc 0 T) (U : Matrix ιx ιv ℝ) :
    ‖U + τ • D'.Lh t U‖ ≤ ‖U‖ :=
  norm_add_smul_tensorL_le D'.Mx D'.Mv hD.v_int (hD.force_int ht) (hD.α_x t ht)
    (fun f i => hD.force_bound ht f i) hτ
    (fun K => D'.mesh.mul_cflRate_le_one (c := D'.coeff) hτ hcfl ht K) U

/-- arXiv 2609.02721, Lemma A.1, first claim, for the Vlasov scheme: `τ_CFL ∈ (0, ∞]` if `α`
and the normal transport speeds on the boundary pieces are bounded by `ᾱ` on `[0, T]`. -/
theorem tauCFL_pos {ᾱ : ℝ} (hᾱ : 0 ≤ ᾱ) (hα : ∀ t ∈ Icc 0 T, D'.α t ≤ ᾱ)
    (hv : ∀ p j, ∀ v ∈ D'.Mv.cell j, |∑ s, D'.Mx.pNormal p s * v s| ≤ ᾱ)
    (hE : ∀ t ∈ Icc 0 T, ∀ p i, ∀ x ∈ D'.Mx.cell i,
      |∑ s, D'.Mv.pNormal p s * D'.force t x s| ≤ ᾱ) :
    0 < D'.tauCFL T := by
  refine D'.mesh.tauCFL_pos hᾱ (fun t ht _ => hα t ht) ?_
  rintro t ht (⟨β, j⟩ | ⟨i, β⟩)
  · refine le_of_abs_le (D'.Mv.abs_mean_le fun v hv' => ?_)
    rw [abs_abs]
    exact hv _ j v hv'
  · refine le_of_abs_le (D'.Mx.abs_mean_le fun x hx => ?_)
    rw [abs_abs]
    exact hE t ht _ i x hx

/-- arXiv 2609.02721, Lemma 4.1: **`L²` stability of the full forward Euler finite volume scheme**
for the Vlasov equation with homogeneous inflow: for `0 < τ ≤ τ_CFL` and all `n` with
`tⁿ = n τ ≤ T`, `‖Ûⁿ‖_F ≤ ‖Û⁰‖_F`, which is `‖û_hⁿ‖_{L²} ≤ ‖û_h⁰‖_{L²}` by
`integral_sq_tensorFn`.  The scheme is the matrix ODE (2.10) with `g = 0`, with matrices defined as
in the paper. -/
theorem lemma41_stable (hD : D'.IsRegular T) (hτ : 0 < τ) (hcfl : ENNReal.ofReal τ ≤ D'.tauCFL T)
    {U : ℕ → Matrix ιx ιv ℝ} (hU : ∀ k : ℕ, U (k + 1) = U k + τ • D'.Lh (k * τ) (U k)) (n : ℕ)
    (hn : n * τ ≤ T) : ‖U n‖ ≤ ‖U 0‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hn' : (n : ℝ) * τ ≤ T := by
      push_cast at hn; nlinarith
    rw [hU n]
    exact (hD.euler_norm_le hτ.le hcfl ⟨by positivity, hn'⟩ _).trans (ih hn')

/-- arXiv 2609.02721, Theorem 4.2: **stability of the rank-adaptive step-and-truncate scheme.**
Under the hypotheses of Lemma 4.1 (homogeneous inflow), for every initial factorisation and
every `0 < τ ≤ τ_CFL` the iterates of Algorithm 2 satisfy `‖Uⁿ‖_F ≤ ‖U⁰‖_F` for all `n` with
`tⁿ ≤ T`, for all tolerances. -/
theorem theorem42_stable (hD : D'.IsRegular T) (hτ : 0 < τ) (hcfl : ENNReal.ofReal τ ≤ D'.tauCFL T)
    {ε₁ ε₂ : ℝ} {Y : ℕ → LRFactors ιx ιv}
    (hY : ∀ k : ℕ, IsSATStep (D'.Lh (k * τ) (Y k).mat) τ ε₁ ε₂ (Y k) (Y (k + 1))) (n : ℕ)
    (hn : n * τ ≤ T) : ‖(Y n).mat‖ ≤ ‖(Y 0).mat‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hn' : (n : ℝ) * τ ≤ T := by
      push_cast at hn; nlinarith
    exact ((hY n).norm_le (hD.euler_norm_le hτ.le hcfl ⟨by positivity, hn'⟩ _)).trans (ih hn')

/-- arXiv 2609.02721, Theorem 4.3: **error of the rank-adaptive scheme against full forward Euler**,
for nonhomogeneous inflow.  `B t` is the inflow term of (2.10) (in particular `tensorInflow` for
separable data; only its independence of `U` is used), `Y` the iterates of Algorithm 2 and `U` the
full forward Euler iterates, with the same `0 < τ ≤ τ_CFL`.  If `‖U⁰ - Û⁰‖_F ≤ δ` then for
all `n` with `tⁿ ≤ T`, `‖Uⁿ - Ûⁿ‖_F ≤ δ + tⁿ ε₁ + (tⁿ/τ) ε₂ ≤ δ + T ε₁ + (T/τ) ε₂`. -/
theorem theorem43_error (hD : D'.IsRegular T) (hτ : 0 < τ) (hcfl : ENNReal.ofReal τ ≤ D'.tauCFL T)
    {ε₁ ε₂ δ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (B : ℝ → Matrix ιx ιv ℝ)
    {Y : ℕ → LRFactors ιx ιv} {U : ℕ → Matrix ιx ιv ℝ}
    (hY : ∀ k : ℕ, IsSATStep (D'.Lh (k * τ) (Y k).mat + B (k * τ)) τ ε₁ ε₂ (Y k) (Y (k + 1)))
    (hU : ∀ k : ℕ, U (k + 1) = U k + τ • (D'.Lh (k * τ) (U k) + B (k * τ)))
    (hδ : ‖(Y 0).mat - U 0‖ ≤ δ) (n : ℕ) (hn : n * τ ≤ T) :
    ‖(Y n).mat - U n‖ ≤ δ + (n * τ) * ε₁ + (n * τ / τ) * ε₂ ∧
      δ + (n * τ) * ε₁ + (n * τ / τ) * ε₂ ≤ δ + T * ε₁ + T / τ * ε₂ := by
  refine ⟨?_, ?_⟩
  · have e0 : ∀ m : ℕ, (m : ℝ) * τ / τ = m := fun m => by field_simp
    rw [e0]
    induction n with
    | zero => simpa using hδ
    | succ n ih =>
      have hn' : (n : ℝ) * τ ≤ T := by
        push_cast at hn; nlinarith
      have ht : (n : ℝ) * τ ∈ Icc 0 T := ⟨by positivity, hn'⟩
      have hstep := (hY n).norm_sub_le hτ.le (U (n + 1))
      have e : (Y n).mat + τ • (D'.Lh (n * τ) (Y n).mat + B (n * τ)) - U (n + 1)
          = ((Y n).mat - U n) + τ • D'.Lh (n * τ) ((Y n).mat - U n) := by
        rw [hU n]
        simp only [Lh, tensorL_sub, smul_add, smul_sub]
        abel
      rw [e] at hstep
      have h1 := hD.euler_norm_le hτ.le hcfl ht ((Y n).mat - U n)
      have h2 := ih hn'
      push_cast
      nlinarith
  · have h1 : (n : ℝ) * τ * ε₁ ≤ T * ε₁ := mul_le_mul_of_nonneg_right hn hε₁
    have h2 : (n : ℝ) * τ / τ * ε₂ ≤ T / τ * ε₂ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn hτ.le) hε₂
    linarith

/-- arXiv 2609.02721, Section 4, tolerance scaling: if the full forward Euler scheme is first order,
`‖U(tⁿ) - Ûⁿ‖_F ≤ C τ` (a hypothesis in the paper as well), `‖U⁰ - Û⁰‖_F ≤ C τ / 3`, and
`ε₁ = C τ / (3 T)`, `ε₂ = C τ² / (3 T)`, then `‖Uⁿ - Ûⁿ‖_F ≤ C τ` and hence the rank-adaptive scheme
keeps first order, `‖U(tⁿ) - Uⁿ‖_F ≤ 2 C τ`, for all `n` with `tⁿ ≤ T`. -/
theorem tolerance_scaling (hD : D'.IsRegular T) (hT : 0 < T) (hτ : 0 < τ)
    (hcfl : ENNReal.ofReal τ ≤ D'.tauCFL T) {C : ℝ} (hC : 0 ≤ C) (B : ℝ → Matrix ιx ιv ℝ)
    {Y : ℕ → LRFactors ιx ιv} {U : ℕ → Matrix ιx ιv ℝ} {Uex : ℝ → Matrix ιx ιv ℝ}
    (hY : ∀ k : ℕ, IsSATStep (D'.Lh (k * τ) (Y k).mat + B (k * τ)) τ (C * τ / (3 * T))
      (C * τ ^ 2 / (3 * T)) (Y k) (Y (k + 1)))
    (hU : ∀ k : ℕ, U (k + 1) = U k + τ • (D'.Lh (k * τ) (U k) + B (k * τ)))
    (hδ : ‖(Y 0).mat - U 0‖ ≤ C * τ / 3)
    (hex : ∀ k : ℕ, k * τ ≤ T → ‖Uex (k * τ) - U k‖ ≤ C * τ) (n : ℕ) (hn : n * τ ≤ T) :
    ‖(Y n).mat - U n‖ ≤ C * τ ∧ ‖Uex (n * τ) - (Y n).mat‖ ≤ 2 * C * τ := by
  have h := theorem43_error hD hτ hcfl (by positivity) (by positivity) B hY hU hδ n hn
  have e : C * τ / 3 + T * (C * τ / (3 * T)) + T / τ * (C * τ ^ 2 / (3 * T)) = C * τ := by
    field_simp
    ring
  have h1 : ‖(Y n).mat - U n‖ ≤ C * τ := by
    rw [← e]; exact h.1.trans h.2
  refine ⟨h1, ?_⟩
  calc ‖Uex (n * τ) - (Y n).mat‖ = ‖(Uex (n * τ) - U n) - ((Y n).mat - U n)‖ := by
        congr 1; abel
    _ ≤ ‖Uex (n * τ) - U n‖ + ‖(Y n).mat - U n‖ := _root_.norm_sub_le _ _
    _ ≤ C * τ + C * τ := add_le_add (hex n hn) h1
    _ = 2 * C * τ := by ring

/-- arXiv 2609.02721, Section 3: the right-hand side `F_h(t, U) = L_h(t, U) + B_h(t)` of the Vlasov
scheme is globally Lipschitz, with the constant a uniform bound of `∑_k ‖A_k(t)‖_F ‖B_k(t)‖_F`. -/
theorem Fh_isLipschitzField (B : ℝ → Matrix ιx ιv ℝ) {L : ℝ}
    (hL : ∀ t, ∑ k, ‖kronA D'.Mx D'.Mv (D'.force t) (D'.α t) k‖
      * ‖kronB D'.Mx D'.Mv (fun v => v) k‖ ≤ L) :
    IsLipschitzField (fun t U => D'.Lh t U + B t) L := by
  have h := kron_isLipschitzField (fun t => kronA D'.Mx D'.Mv (D'.force t) (D'.α t))
    (fun _ => kronB D'.Mx D'.Mv (fun v => v)) B hL
  simpa only [Lh, tensorL_eq_kron] using h

end VlasovFV

end Vlasov

/-! ### The hypotheses can hold -/

section Example

/-- Two unit cells `[0, 1)`, `[1, 2)` of a space mesh on the real line. -/
def exMeshX : PolyMesh (Fin 2) Unit (Fin 2) (Fin 2) (Fin 1) ℝ where
  vol _ := 1
  vol_pos _ := one_pos
  area _ := 1
  area_pos _ := one_pos
  side₁ _ := 0
  side₂ _ := 1
  bArea _ := 1
  bArea_pos _ := one_pos
  bCell β := β
  μ := volume
  cell K := Ico ((K : ℕ) : ℝ) ((K : ℕ) + 1)
  normal _ _ := 1
  piece β := β
  pNormal p _ := if p = 0 then -1 else 1
  cell_meas _ := measurableSet_Ico
  cell_disj := by
    intro K L h
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    fin_cases K <;> fin_cases L <;> simp_all <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  vol_eq K := by simp [Measure.real]
  closure K s := by
    fin_cases K <;> simp [Finset.sum_filter]

/-- One velocity cell `[-1, 1]`. -/
def exMeshV : PolyMesh Unit Empty (Fin 2) (Fin 2) (Fin 1) (Fin 1 → ℝ) where
  vol _ := 2
  vol_pos _ := two_pos
  area e := e.elim
  area_pos e := e.elim
  side₁ e := e.elim
  side₂ e := e.elim
  bArea _ := 1
  bArea_pos _ := one_pos
  bCell _ := ()
  μ := volume
  cell _ := Icc (fun _ => -1) (fun _ => 1)
  normal e := e.elim
  piece β := β
  pNormal p _ := if p = 0 then -1 else 1
  cell_meas _ := measurableSet_Icc
  cell_disj K L h := (h rfl).elim
  vol_eq _ := by
    simp only [Measure.real, Real.volume_Icc_pi]
    norm_num
  closure K s := by
    simp [Fin.sum_univ_two]

/-- The sample Vlasov problem on the two meshes: `E = 1`, `α = 1`. -/
def exVlasov : VlasovFV (Fin 2) Unit (Fin 2) (Fin 2) Unit Empty (Fin 2) (Fin 2) (Fin 1) ℝ where
  Mx := exMeshX
  Mv := exMeshV
  E _ _ _ := 1
  α _ := 1

/-- Non-vacuity of arXiv 2609.02721, Lemma 4.1 and Theorems 4.2, 4.3: the hypotheses hold for a
sample discretisation with a positive time step. -/
theorem exists_regularVlasov :
    ∃ D' : VlasovFV (Fin 2) Unit (Fin 2) (Fin 2) Unit Empty (Fin 2) (Fin 2) (Fin 1) ℝ,
      D'.IsRegular 1 ∧ ∃ τ : ℝ, 0 < τ ∧ ENNReal.ofReal τ ≤ D'.tauCFL 1 := by
  have hv : ∀ v ∈ exVlasov.Mv.cell (), |v 0| ≤ 1 := fun v hv => by
    have h : v ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := hv
    exact abs_le.2 ⟨h.1 0, h.2 0⟩
  have hreg : exVlasov.IsRegular 1 :=
    { v_int := fun j s => by
        change IntegrableOn (fun v : Fin 1 → ℝ => v s) (Icc (fun _ => -1) (fun _ => 1)) volume
        exact (continuous_apply s).continuousOn.integrableOn_compact isCompact_Icc
      E_int := fun t _ i s => integrableOn_const (exVlasov.Mx.measure_ne_top i)
      α_x := fun t _ e j v hv' => by
        have := hv v hv'
        simpa [exVlasov, exMeshX] using this
      α_v := fun _ _ f => f.elim }
  have hpos : 0 < exVlasov.tauCFL 1 := by
    refine VlasovFV.tauCFL_pos (ᾱ := 1) zero_le_one (fun t _ => le_rfl) ?_ ?_
    · intro p j v hv'
      have := hv v hv'
      fin_cases p <;> simpa [exVlasov, exMeshX] using this
    · intro t _ p i x _
      fin_cases p <;> simp [exVlasov, exMeshV, VlasovFV.force]
  obtain ⟨r, hr0, h0, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  exact ⟨exVlasov, hreg, r, ENNReal.ofReal_pos.1 h0, hr.le⟩

end Example

end

end LeanDLRA.Literature.P2609_02721
