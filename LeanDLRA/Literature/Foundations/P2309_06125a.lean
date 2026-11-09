import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.SVD
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Results of arXiv 2309.06125: Low-rank retractions and DLRA

Séguin, Ceruti and Kressner, *From low-rank retractions to dynamical low-rank approximation and
back*. On the set `M_r` of rank-`r` matrices with the Frobenius inner product, this module defines
the tangent space `tangentSpace Y = {A Y + Y B}`, which is shown to be exactly the set of velocities
of curves on `M_r` (`mem_tangentSpace_iff_velocity`), and its orthogonal projection `tanProj Y`,
which is the library's `tangentProj U V` at a factorized point (eq. (1)). A retraction is defined as
in the condensed form of §2.1 of the paper, through its curves `τ ↦ R_x(τ v)` (`IsRetraction`,
`IsSecondOrderRetraction`), and any retraction has local error `O(τ²)` (eqs. (8)-(9):
`IsRetraction.local_error`, `dlra_local_error`). The orthographic, KLS and KSL retractions are given
in closed form (`orthRetr`, `klsRetr`, `kslRetr`), identified with the outputs of Algorithms 4, 3
and 2 (`algorithm4_eq`, `algorithm3_eq`, `algorithm2_eq`, with eqs. (17)-(20)), shown to be
independent of the factorization, and packaged as maps on `T M_r` (`retrORTH`, `retrKLS`,
`retrKSL`). The closest-point property (15) and the local inverse (16) of `R^ORTH` are
`IsFactorization.normalSlice_inter_rankSet`, `IsFactorization.orthRetr_isMinOn`,
`IsFactorization.tanProj_orthRetr_sub` and `IsFactorization.orthRetr_tanProj_sub`. **Prop. 1** is
`isSecondOrderRetraction_kls`, proved without geodesics from the exact expansion `R^KLS_X(τ Z) =
R^ORTH_X(τ Z) - τ⁴ klsRem(τ)` and `R^ORTH_X(τ Z) = X + τ Z + τ² U_p (S + τ M)⁻¹ V_pᵀ`, which gives
`O(t⁴)` instead of the paper's `o(t³)` (`klsRetr_sub_orthRetr_isBigO`,
`klsRetr_sub_orthRetr_isLittleO`), and `R^KLS` has rank `r` on a neighbourhood of `0`
(`eventually_rank_klsRetr`); the same method proves that `R^ORTH` and `R^KSL` are second-order
retractions. For the SVD retraction (`retrSVD`, the truncated SVD) the first-order expansion and the
local error of projected Euler (10) are proved, but not smoothness. **Prop. 5** has an abstract core
for curves of orthogonal projectors (`IsProjectorCurve.weingarten_eq`, `IsProjectorCurve.pairing`)
and a matrix form: along any curve on `M_r` that is differentiable at `0`, `t ↦ Π(Y t)` is
differentiable at `0` (`isProjectorCurve_tanProj`) and its derivative on normal vectors is the
matrix (34) (`weingarten_eq_deriv`, `weingarten_of_rep`, `weingarten_diagonal`), with `‖W_Y(T, N)‖ ≤
2 ‖T‖ ‖N‖ / σ_r` (`norm_weingarten_le`). **Prop. 6** is `dlra_acceleration`, with the curvature
bound `norm_curvature_term_le`. **Eqs. (13)-(14) are false as literal identities**: the KSL and KLS
schemes with Euler substeps equal `R^KSL` and `R^KLS` of `Δt Π(Y₀) F(Y₀)` only up to an explicit
defect (`IsEulerKSLStep.eq_kslRetr_add`, `IsEulerKLSStep.eq_klsRetr_add`), which vanishes for a
frozen tangent field (`IsEulerKSLStep.eq_kslRetr_of_const`, `IsEulerKLSStep.eq_klsRetr_of_const`),
and which is nonzero in the explicit `2 × 2` examples `eulerKSL_ne_kslRetr`, `eulerKLS_ne_klsRetr`.
All factorizations `X = U S Vᵀ` allow an arbitrary invertible `S`; the paper's diagonal `S` is a
special case.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix ContDiff LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2309_06125

open LeanDLRA.Curvature
open Matrix (colProj)

/-! ### Retractions on a subset of a normed space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two curves with the same value and velocity at `0` differ by `O(τ²)`. -/
lemma isBigO_sq_of_jet {f g : ℝ → E}
    (hf : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ f τ)
    (hg : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ g τ)
    (hf' : DifferentiableAt ℝ (deriv f) 0) (hg' : DifferentiableAt ℝ (deriv g) 0)
    (h0 : f 0 = g 0) (h1 : deriv f 0 = deriv g 0) :
    (fun τ => f τ - g τ) =O[𝓝 0] fun τ : ℝ => τ ^ 2 := by
  set e : ℝ → E := fun τ => f τ - g τ with he
  have hdiff : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ e τ := by
    filter_upwards [hf, hg] with τ h1 h2 using h1.sub h2
  have hderiv : deriv e =ᶠ[𝓝 0] fun τ => deriv f τ - deriv g τ := by
    filter_upwards [hf, hg] with τ h1 h2 using deriv_fun_sub h1 h2
  have hd0 : DifferentiableAt ℝ (fun τ => deriv f τ - deriv g τ) 0 := hf'.sub hg'
  have hd1 := hd0.hasDerivAt.congr_of_eventuallyEq hderiv
  have hz : deriv e 0 = 0 := by rw [hderiv.eq_of_nhds, h1, sub_self]
  obtain ⟨C, hC⟩ := hd1.isBigO_sub.bound
  simp only [hz, sub_zero] at hC
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hdiff.and hC)
  refine Asymptotics.IsBigO.of_bound (max C 0) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with τ hτ
  have hsub : ∀ s ∈ Set.uIcc (0 : ℝ) τ, |s| ≤ |τ| ∧ s ∈ Metric.ball (0 : ℝ) δ := by
    intro s hs
    have hle : |s| ≤ |τ| := by
      have := Set.abs_sub_left_of_mem_uIcc hs
      simpa using this
    refine ⟨hle, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hτ ⊢
    exact lt_of_le_of_lt hle hτ
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le (f := e) (s := Set.uIcc (0 : ℝ) τ)
    (x := 0) (y := τ) (C := max C 0 * |τ|)
    (fun s hs => (hball s (hsub s hs).2).1)
    (fun s hs => by
      have h2 := (hball s (hsub s hs).2).2
      rw [Real.norm_eq_abs] at h2
      calc ‖deriv e s‖ ≤ C * |s| := h2
        _ ≤ max C 0 * |s| := by gcongr; exact le_max_left _ _
        _ ≤ max C 0 * |τ| := mul_le_mul_of_nonneg_left (hsub s hs).1 (le_max_right _ _))
    (convex_uIcc 0 τ) Set.left_mem_uIcc Set.right_mem_uIcc
  have he0 : e 0 = 0 := by simp [he, h0]
  rw [he0, sub_zero, sub_zero, Real.norm_eq_abs] at hbound
  rw [Real.norm_eq_abs, abs_pow, sq]
  rw [mul_assoc] at hbound
  exact hbound

lemma contDiffAt_eventually_differentiableAt {σ : ℝ → E} (h : ContDiffAt ℝ 2 σ 0) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ σ τ := by
  filter_upwards [h.eventually (by simp)] with τ hτ
  exact hτ.differentiableAt (by norm_num)

lemma contDiffAt_differentiableAt_deriv {σ : ℝ → E} (h : ContDiffAt ℝ 2 σ 0) :
    DifferentiableAt ℝ (deriv σ) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ σ) 0 := h.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun τ => fderiv ℝ σ τ 1) 0 := h1.clm_apply contDiffAt_const
  have h3 : deriv σ = fun τ => fderiv ℝ σ τ 1 := by
    funext τ; rfl
  rw [h3]
  exact h2.differentiableAt (by norm_num)

/-- **Retraction** on `M ⊆ E` with tangent spaces `T`, in the condensed form of arXiv 2309.06125,
§2.1: for `x ∈ M`, `v ∈ T x` the map `τ ↦ R x (τ v)` is defined for small `τ`, parametrizes a
smooth curve on `M`, and `σ(0) = x`, `σ'(0) = v`.  `R` is total; values away from the zero section
are irrelevant. -/
structure IsRetraction (M : Set E) (T : E → Set E) (R : E → E → E) : Prop where
  mem : ∀ x ∈ M, ∀ v ∈ T x, ∀ᶠ τ in 𝓝 (0 : ℝ), R x (τ • v) ∈ M
  smooth : ∀ x ∈ M, ∀ v ∈ T x, ContDiffAt ℝ ∞ (fun τ : ℝ => R x (τ • v)) 0
  zero : ∀ x ∈ M, R x 0 = x
  velocity : ∀ x ∈ M, ∀ v ∈ T x, HasDerivAt (fun τ : ℝ => R x (τ • v)) v 0

/-- **Second-order retraction** (arXiv 2309.06125, §2.1): a retraction whose curves have zero
intrinsic acceleration at `τ = 0`.  On a Riemannian submanifold the intrinsic acceleration is the
tangential part `Π(x) σ''(0)` of the extrinsic one (loc. cit., eq. (36)). -/
structure IsSecondOrderRetraction (M : Set E) (T : E → Set E) (Pr : E → E → E)
    (R : E → E → E) : Prop extends IsRetraction M T R where
  acceleration : ∀ x ∈ M, ∀ v ∈ T x, Pr x (deriv (deriv fun τ : ℝ => R x (τ • v)) 0) = 0

/-- **Local error of a retraction step** (arXiv 2309.06125, eq. (8), from Shub 1986): if `Y` passes
through `x` with velocity `v`, then `‖Y τ - R x (τ v)‖ = O(τ²)`.  It is enough that `Y` is
differentiable near `0` and `Y'` differentiable at `0`. -/
theorem IsRetraction.local_error {M : Set E} {T : E → Set E} {R : E → E → E}
    (hR : IsRetraction M T R) {x v : E} (hx : x ∈ M) (hv : v ∈ T x) {Y : ℝ → E}
    (hY : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ Y τ) (hY' : DifferentiableAt ℝ (deriv Y) 0)
    (hY0 : Y 0 = x) (hv' : deriv Y 0 = v) :
    (fun τ => Y τ - R x (τ • v)) =O[𝓝 0] fun τ : ℝ => τ ^ 2 := by
  have h2 : ContDiffAt ℝ 2 (fun τ : ℝ => R x (τ • v)) 0 := by
    simpa using contDiffAt_infty.1 (hR.smooth x hx v hv) 2
  refine isBigO_sq_of_jet hY (contDiffAt_eventually_differentiableAt h2) hY'
    (contDiffAt_differentiableAt_deriv h2) ?_ ?_
  · simp [hY0, hR.zero x hx]
  · rw [hv', (hR.velocity x hx v hv).deriv]

end General

/-! ### Calculus of matrix-valued functions -/

section Calculus

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : WithTop ℕ∞}

lemma contDiffAt_mul {A : F → Matrix m l ℝ} {B : F → Matrix l n ℝ} {x : F}
    (hA : ContDiffAt ℝ N A x) (hB : ContDiffAt ℝ N B x) :
    ContDiffAt ℝ N (fun y => A y * B y) x :=
  (Frobenius.mulCLM (m := m) (l := l) (n := n)).isBoundedBilinearMap.contDiff.comp_contDiffAt x
    (hA.prodMk hB)

lemma contDiffAt_transpose {A : F → Matrix m n ℝ} {x : F} (hA : ContDiffAt ℝ N A x) :
    ContDiffAt ℝ N (fun y => (A y)ᵀ) x :=
  (Frobenius.transposeCLM (m := m) (n := n)).contDiff.comp_contDiffAt x hA

variable [DecidableEq k]

/-- Matrix inversion is smooth at invertible matrices. -/
lemma contDiffAt_matInv {B : Matrix k k ℝ} (hB : IsUnit B.det) :
    ContDiffAt ℝ N (fun C : Matrix k k ℝ => C⁻¹) B := by
  let R : NormedRing (Matrix k k ℝ) := Matrix.frobeniusNormedRing
  let RA : NormedAlgebra ℝ (Matrix k k ℝ) := Matrix.frobeniusNormedAlgebra
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 hB
  obtain ⟨u, rfl⟩ := hu
  have h : ContDiffAt ℝ N Ring.inverse (u : Matrix k k ℝ) := contDiffAt_ringInverse ℝ u
  have h2 : (fun C : Matrix k k ℝ => C⁻¹) = Ring.inverse := by
    funext C; exact Matrix.nonsing_inv_eq_ringInverse C
  rw [h2]
  exact h

lemma contDiffAt_inv {A : F → Matrix k k ℝ} {x : F} (hA : ContDiffAt ℝ N A x)
    (hdet : IsUnit (A x).det) : ContDiffAt ℝ N (fun y => (A y)⁻¹) x :=
  (contDiffAt_matInv hdet).comp x hA

lemma eventually_isUnit_det {X : Type*} [TopologicalSpace X] {A : X → Matrix k k ℝ} {x : X}
    (hA : ContinuousAt A x) (hdet : IsUnit (A x).det) : ∀ᶠ y in 𝓝 x, IsUnit (A y).det := by
  have hc : ContinuousAt (fun t => (A t).det) x := by
    have h : Continuous (fun C : Matrix k k ℝ => C.det) := Continuous.matrix_det continuous_id
    exact h.continuousAt.comp hA
  filter_upwards [hc.eventually_ne hdet.ne_zero] with t ht
  exact isUnit_iff_ne_zero.2 ht

/-- Derivative of the inverse of a matrix curve. -/
lemma hasDerivAt_matInv {A : ℝ → Matrix k k ℝ} {A' : Matrix k k ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hdet : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s)⁻¹) (-((A t)⁻¹ * A' * (A t)⁻¹)) t := by
  have hd : DifferentiableAt ℝ (fun C : Matrix k k ℝ => C⁻¹) (A t) :=
    (contDiffAt_matInv (N := 1) hdet).differentiableAt (by norm_num)
  have hc : HasDerivAt (fun s => (A s)⁻¹) (fderiv ℝ (fun C : Matrix k k ℝ => C⁻¹) (A t) A') t :=
    hd.hasFDerivAt.comp_hasDerivAt t hA
  set D := fderiv ℝ (fun C : Matrix k k ℝ => C⁻¹) (A t) A' with hDdef
  have hev : (fun s => A s * (A s)⁻¹) =ᶠ[𝓝 t] fun _ => (1 : Matrix k k ℝ) := by
    filter_upwards [eventually_isUnit_det hA.continuousAt hdet] with s hs
    exact Matrix.mul_nonsing_inv _ hs
  have hprod := Frobenius.hasDerivAt_mul hA hc
  have hone := (hasDerivAt_const t (1 : Matrix k k ℝ)).congr_of_eventuallyEq hev
  have heq := hprod.unique hone
  have hD : D = -((A t)⁻¹ * A' * (A t)⁻¹) := by
    have h1 : A t * D = -(A' * (A t)⁻¹) := eq_neg_of_add_eq_zero_right heq
    calc D = (A t)⁻¹ * (A t * D) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = -((A t)⁻¹ * A' * (A t)⁻¹) := by
          rw [h1, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hD]
  exact hc

end Calculus

/-! ### The orthogonal projector onto the columns of a matrix -/

section ColP

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]

/-! The orthogonal projector `A (Aᵀ A)⁻¹ Aᵀ` onto the range of a matrix `A` with independent
columns is the core Gram column-space projector `Matrix.colProj` (the local `colP` of an earlier
version of this file was the same matrix, unification batch C2); for full column rank it is the
orthogonal projector `Matrix.rangeProj A` onto the column space (`Matrix.colProj_eq_rangeProj`).
If `A = U₁ S` is a QR factorization, it is `U₁ U₁ᵀ` (`colP_of_qr`), so it is what the
orthonormalization steps of the algorithms of arXiv 2309.06125 compute. -/

/-- `A (Aᵀ A)⁻¹ Aᵀ` is symmetric (the core `Matrix.transpose_colProj`). -/
lemma colP_transpose (A : Matrix m k ℝ) : (colProj A)ᵀ = colProj A :=
  Matrix.transpose_colProj A

/-- `A (Aᵀ A)⁻¹ Aᵀ A = A` for full column rank (the core `Matrix.colProj_mul_self`). -/
lemma colP_mul_self {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) : colProj A * A = A :=
  Matrix.colProj_mul_self h

/-- `Aᵀ A (Aᵀ A)⁻¹ Aᵀ = Aᵀ` for full column rank. -/
lemma transpose_mul_colP {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) : Aᵀ * colProj A = Aᵀ := by
  have := congrArg Matrix.transpose (colP_mul_self h)
  rwa [Matrix.transpose_mul, colP_transpose] at this

/-- `A (Aᵀ A)⁻¹ Aᵀ` is idempotent (the core `Matrix.colProj_mul_colProj`, which needs no rank
hypothesis). -/
lemma colP_idem {A : Matrix m k ℝ} (_h : IsUnit (Aᵀ * A).det) :
    colProj A * colProj A = colProj A :=
  Matrix.colProj_mul_colProj A

/-- The projector depends only on the column space (the core `Matrix.colProj_mul_of_isUnit`). -/
lemma colP_gauge {A : Matrix m k ℝ} {G : Matrix k k ℝ} (hG : IsUnit G.det) :
    colProj (A * G) = colProj A :=
  Matrix.colProj_mul_of_isUnit hG

/-- `U (Uᵀ U)⁻¹ Uᵀ = U Uᵀ` for orthonormal `U` (the core `Matrix.colProj_eq_mul_transpose`). -/
lemma colP_of_orthonormal {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : colProj U = U * Uᵀ :=
  Matrix.colProj_eq_mul_transpose hU

/-- A QR factorization `A = U₁ S` computes the projector: `colProj A = U₁ U₁ᵀ`. -/
lemma colP_of_qr {A U₁ : Matrix m k ℝ} {S : Matrix k k ℝ} (hU : U₁ᵀ * U₁ = 1)
    (hS : IsUnit S.det) (hA : A = U₁ * S) : colProj A = U₁ * U₁ᵀ := by
  rw [hA, colP_gauge hS, colP_of_orthonormal hU]

/-- `A (Aᵀ A)⁻¹ Aᵀ` is an orthogonal projector matrix. -/
lemma isOrthProjMat_colP {A : Matrix m k ℝ} (h : IsUnit (Aᵀ * A).det) :
    IsOrthProjMat (colProj A) :=
  ⟨colP_transpose A, colP_idem h⟩

end ColP

/-! ### The manifold of rank-`r` matrices -/

section Geometry

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- The manifold `M_r` of rank-`r` matrices, as a set. -/
def rankSet (m n : Type*) [Fintype m] [Fintype n] (r : ℕ) : Set (Matrix m n ℝ) :=
  {Y | Y.rank = r}

/-- The tangent space `T_Y M_r = {A Y + Y B}`.  This form needs no factorization of `Y`.  At a
factorized point it is `{U B + C Vᵀ}` (`IsFactorization.mem_tangentSpace_iff`), and at a point of
`M_r` it consists exactly of the velocities of curves on `M_r` (`mem_tangentSpace_iff_velocity`). -/
def tangentSpace (Y : Matrix m n ℝ) : Submodule ℝ (Matrix m n ℝ) where
  carrier := {Z | ∃ (A : Matrix m m ℝ) (B : Matrix n n ℝ), Z = A * Y + Y * B}
  add_mem' := by
    rintro _ _ ⟨A, B, rfl⟩ ⟨C, D, rfl⟩
    exact ⟨A + C, B + D, by simp only [Matrix.add_mul, Matrix.mul_add]; abel⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨A, B, rfl⟩
    exact ⟨c • A, c • B, by simp [Matrix.smul_mul, Matrix.mul_smul, smul_add]⟩

/-- The orthogonal projection `Π(Y)` onto the tangent space `T_Y M_r` (arXiv 2309.06125,
eq. (1)). -/
noncomputable def tanProj (Y : Matrix m n ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  (tangentSpace Y).starProjection

lemma isOrthProj_tanProj (Y : Matrix m n ℝ) : IsOrthProj (tanProj Y) where
  idem x := by
    have h := (Submodule.isIdempotentElem_starProjection (tangentSpace Y)).eq
    exact congrArg (fun P : Matrix m n ℝ →L[ℝ] Matrix m n ℝ => P x) h
  symm x y := Submodule.inner_starProjection_left_eq_right _ x y

lemma tanProj_eq_self_iff {Y Z : Matrix m n ℝ} : tanProj Y Z = Z ↔ Z ∈ tangentSpace Y :=
  Submodule.starProjection_eq_self_iff

lemma mem_orthogonal_iff_tanProj {Y N : Matrix m n ℝ} :
    N ∈ (tangentSpace Y)ᗮ ↔ tanProj Y N = 0 := by
  constructor
  · intro hN
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun w hw => ?_
    rw [sub_zero, real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 hN w hw
  · intro hN
    refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    rw [← tanProj_eq_self_iff.2 hw, (isOrthProj_tanProj Y).symm, hN, inner_zero_right]

/-- A compact factorization `X = U S Vᵀ` with orthonormal columns and invertible `S`.  The paper
uses `S = diag(σ₁, …, σ_r)`; everything below holds for any invertible `S`. -/
structure IsFactorization (X : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthV : Vᵀ * V = 1
  det : IsUnit S.det
  eq : X = U * S * Vᵀ

variable {X Y Z T : Matrix m n ℝ} {U U' Up : Matrix m (Fin r) ℝ} {V V' Vp : Matrix n (Fin r) ℝ}
  {S S' M A : Matrix (Fin r) (Fin r) ℝ}

lemma exists_factorization (hX : X.rank = r) : ∃ U S V, IsFactorization (r := r) X U S V := by
  obtain ⟨U, S, V, hU, hV, hS, h⟩ := (SVD.rank_eq_iff_exists_factor X).1 hX
  exact ⟨U, S, V, hU, hV, hS, h⟩

lemma IsFactorization.rank (h : IsFactorization X U S V) : X.rank = r :=
  (SVD.rank_eq_iff_exists_factor X).2 ⟨U, S, V, h.orthU, h.orthV, h.det, h.eq⟩

lemma IsFactorization.sandwich (h : IsFactorization X U S V) : Uᵀ * X * V = S := by
  rw [h.eq]
  calc Uᵀ * (U * S * Vᵀ) * V = (Uᵀ * U) * S * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h.orthU, h.orthV, Matrix.one_mul, Matrix.mul_one]

lemma IsFactorization.mul_V (h : IsFactorization X U S V) : X * V = U * S := by
  rw [h.eq, Matrix.mul_assoc, h.orthV, Matrix.mul_one]

lemma IsFactorization.Ut_mul (h : IsFactorization X U S V) : Uᵀ * X = S * Vᵀ := by
  rw [h.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.orthU, Matrix.one_mul]

/-- Fixed points of `tangentProj U V` are exactly the elements of the tangent space. -/
lemma IsFactorization.mem_tangentSpace_iff (h : IsFactorization X U S V) (Z : Matrix m n ℝ) :
    Z ∈ tangentSpace X ↔ tangentProj U V Z = Z := by
  rw [tangentProj_eq_self_iff h.orthU h.orthV]
  constructor
  · rintro ⟨A, B, rfl⟩
    refine ⟨S * Vᵀ * B, A * U * S, ?_⟩
    rw [h.eq]
    simp only [Matrix.mul_assoc]
    abel
  · rintro ⟨B, C, rfl⟩
    refine ⟨C * S⁻¹ * Uᵀ, V * S⁻¹ * B, ?_⟩
    have h1 : C * S⁻¹ * Uᵀ * (U * S * Vᵀ) = C * Vᵀ := by
      calc C * S⁻¹ * Uᵀ * (U * S * Vᵀ) = C * (S⁻¹ * ((Uᵀ * U) * S)) * Vᵀ := by
            simp only [Matrix.mul_assoc]
        _ = C * Vᵀ := by
          rw [h.orthU, Matrix.one_mul, Matrix.nonsing_inv_mul _ h.det, Matrix.mul_one]
    have h2 : U * S * Vᵀ * (V * S⁻¹ * B) = U * B := by
      calc U * S * Vᵀ * (V * S⁻¹ * B) = U * (S * ((Vᵀ * V) * S⁻¹)) * B := by
            simp only [Matrix.mul_assoc]
        _ = U * B := by
          rw [h.orthV, Matrix.one_mul, Matrix.mul_nonsing_inv _ h.det, Matrix.mul_one]
    rw [h.eq, h1, h2]
    abel

/-- **Eq. (1) of arXiv 2309.06125**: the projection onto the tangent space is the library's
`tangentProj U V`, `Π(X) Z = U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`. -/
theorem IsFactorization.tanProj_eq (h : IsFactorization X U S V) : tanProj X = tangentProj U V := by
  have hP := isOrthProj_tangentProj (m := m) (n := n) h.orthU h.orthV
  refine ContinuousLinearMap.ext fun q => ?_
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [h.mem_tangentSpace_iff]
    exact hP.idem q
  · rw [h.mem_tangentSpace_iff] at hw
    rw [← hw, ← hP.symm, map_sub, hP.idem, sub_self, inner_zero_left]

lemma IsFactorization.tanProj_apply (h : IsFactorization X U S V) (q : Matrix m n ℝ) :
    tanProj X q = U * Uᵀ * q + q * V * Vᵀ - U * Uᵀ * q * V * Vᵀ := by
  rw [h.tanProj_eq, tangentProj_apply]

/-- A normal vector is annihilated by `Vᵀ` from the right. -/
lemma IsFactorization.normal_mul_V (h : IsFactorization X U S V) {N : Matrix m n ℝ}
    (hN : tanProj X N = 0) : N * V = 0 := by
  rw [h.tanProj_apply] at hN
  have h2 := congrArg (· * V) hN
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc, h.orthV,
    Matrix.mul_one] at h2
  simpa using h2

/-- A normal vector is annihilated by `Uᵀ` from the left. -/
lemma IsFactorization.Ut_mul_normal (h : IsFactorization X U S V) {N : Matrix m n ℝ}
    (hN : tanProj X N = 0) : Uᵀ * N = 0 := by
  rw [h.tanProj_apply] at hN
  have h2 := congrArg (Uᵀ * ·) hN
  have e : ∀ B : Matrix (Fin r) n ℝ, Uᵀ * (U * B) = B := fun B => by
    rw [← Matrix.mul_assoc, h.orthU, Matrix.one_mul]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_zero, Matrix.mul_assoc, e] at h2
  simpa [Matrix.mul_assoc] using h2

/-- The representation `T = U M Vᵀ + U_p Vᵀ + U V_pᵀ`, `Uᵀ U_p = Vᵀ V_p = 0` of a tangent vector
(arXiv 2309.06125, §2.1). -/
structure IsTangentRep (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (M : Matrix (Fin r) (Fin r) ℝ) (Up : Matrix m (Fin r) ℝ) (Vp : Matrix n (Fin r) ℝ)
    (T : Matrix m n ℝ) : Prop where
  gaugeU : Uᵀ * Up = 0
  gaugeV : Vᵀ * Vp = 0
  eq : T = U * M * Vᵀ + Up * Vᵀ + U * Vpᵀ

namespace IsTangentRep

lemma gaugeU' (h : IsTangentRep U V M Up Vp T) : Upᵀ * U = 0 := by
  simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h.gaugeU

lemma gaugeV' (h : IsTangentRep U V M Up Vp T) : Vpᵀ * V = 0 := by
  simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h.gaugeV

lemma mul_right (h : IsTangentRep U V M Up Vp T) (hV : Vᵀ * V = 1) : T * V = U * M + Up := by
  rw [h.eq]
  simp only [Matrix.add_mul, Matrix.mul_assoc, hV, h.gaugeV', Matrix.mul_one, Matrix.mul_zero,
    add_zero]

lemma mul_left (h : IsTangentRep U V M Up Vp T) (hU : Uᵀ * U = 1) : Uᵀ * T = M * Vᵀ + Vpᵀ := by
  have e : ∀ B : Matrix (Fin r) n ℝ, Uᵀ * (U * B) = B := fun B => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e0 : Uᵀ * (Up * Vᵀ) = 0 := by rw [← Matrix.mul_assoc, h.gaugeU, Matrix.zero_mul]
  rw [h.eq]
  simp only [Matrix.mul_add, Matrix.mul_assoc, e, e0, add_zero]

lemma sandwich (h : IsTangentRep U V M Up Vp T) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    Uᵀ * T * V = M := by
  rw [h.mul_left hU, Matrix.add_mul, Matrix.mul_assoc, hV, h.gaugeV', Matrix.mul_one, add_zero]

lemma transpose_mul (h : IsTangentRep U V M Up Vp T) (hU : Uᵀ * U = 1) :
    Tᵀ * U = V * Mᵀ + Vp := by
  have := congrArg Matrix.transpose (h.mul_left hU)
  simpa [Matrix.transpose_mul, Matrix.transpose_add] using this

lemma smul (h : IsTangentRep U V M Up Vp T) (c : ℝ) :
    IsTangentRep U V (c • M) (c • Up) (c • Vp) (c • T) where
  gaugeU := by rw [Matrix.mul_smul, h.gaugeU, smul_zero]
  gaugeV := by rw [Matrix.mul_smul, h.gaugeV, smul_zero]
  eq := by
    rw [h.eq]
    simp only [smul_add, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma add_base (h : IsTangentRep U V M Up Vp T) (hX : X = U * S * Vᵀ) :
    IsTangentRep U V (S + M) Up Vp (X + T) where
  gaugeU := h.gaugeU
  gaugeV := h.gaugeV
  eq := by
    rw [h.eq, hX]
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel

/-- Every matrix with such a representation is tangent. -/
lemma mem_tangentSpace (hT : IsTangentRep U V M Up Vp T) (h : IsFactorization X U S V) :
    T ∈ tangentSpace X := by
  rw [h.mem_tangentSpace_iff, tangentProj_eq_self_iff h.orthU h.orthV]
  refine ⟨M * Vᵀ + Vpᵀ, Up, ?_⟩
  rw [hT.eq, Matrix.mul_add, Matrix.mul_assoc]
  abel

end IsTangentRep

/-- Every tangent vector has the representation of arXiv 2309.06125, §2.1, with `M = Uᵀ T V`,
`U_p = (1 - U Uᵀ) T V`, `V_p = (1 - V Vᵀ) Tᵀ U`. -/
theorem IsFactorization.tangentRep [DecidableEq m] [DecidableEq n] (h : IsFactorization X U S V)
    (hT : T ∈ tangentSpace X) :
    IsTangentRep U V (Uᵀ * T * V) ((1 - U * Uᵀ) * T * V) ((1 - V * Vᵀ) * Tᵀ * U) T where
  gaugeU := by
    have e : Uᵀ * (1 - U * Uᵀ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.orthU, Matrix.one_mul, sub_self]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, e, Matrix.zero_mul]
  gaugeV := by
    have e : Vᵀ * (1 - V * Vᵀ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.orthV, Matrix.one_mul, sub_self]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, e, Matrix.zero_mul]
  eq := by
    have hfix := (h.mem_tangentSpace_iff T).1 hT
    rw [tangentProj_apply] at hfix
    conv_lhs => rw [← hfix]
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    simp
    abel

/-! ### Rank lemmas -/

lemma isUnit_det_of_le_rank {B : Matrix (Fin r) (Fin r) ℝ} (h : r ≤ B.rank) : IsUnit B.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  have hle : B.rank ≤ r := by simpa using B.rank_le_card_width
  have htop : LinearMap.range B.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank ℝ (LinearMap.range B.mulVecLin) = B.rank := rfl
    simp only [this, Module.finrank_pi, Fintype.card_fin]
    omega
  intro y
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (htop ▸ Submodule.mem_top : y ∈ LinearMap.range _)
  exact ⟨x, hx⟩

lemma le_rank_of_isUnit {P : Matrix m n ℝ} {B : Matrix (Fin r) (Fin r) ℝ}
    {C : Matrix (Fin r) m ℝ} {D : Matrix n (Fin r) ℝ} (hB : B = C * P * D) (h : IsUnit B.det) :
    r ≤ P.rank := by
  have h1 : B.rank = r := by
    rw [Matrix.rank_of_isUnit B ((Matrix.isUnit_iff_isUnit_det B).2 h), Fintype.card_fin]
  calc r = B.rank := h1.symm
    _ ≤ (C * P).rank := by rw [hB]; exact Matrix.rank_mul_le_left _ _
    _ ≤ P.rank := Matrix.rank_mul_le_right _ _

/-- If `Uᵀ K` is invertible, then `Kᵀ K` is invertible. -/
lemma isUnit_det_transpose_mul_self {K : Matrix m (Fin r) ℝ} {W : Matrix (Fin r) m ℝ}
    (h : IsUnit (W * K).det) : IsUnit (Kᵀ * K).det := by
  apply isUnit_det_of_le_rank
  rw [Matrix.rank_transpose_mul_self]
  have hr : (W * K).rank = r := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h), Fintype.card_fin]
  calc r = (W * K).rank := hr.symm
    _ ≤ K.rank := Matrix.rank_mul_le_right _ _

/-- A matrix `Y = P Q` that factors through `ℝ^r` and has an invertible `r × r` compression has
rank `r`. -/
lemma rank_eq_of_factor {P : Matrix m (Fin r) ℝ} {Q : Matrix (Fin r) n ℝ} {C : Matrix (Fin r) m ℝ}
    {D : Matrix n (Fin r) ℝ} (hY : Y = P * Q) (h : IsUnit (C * Y * D).det) : Y.rank = r := by
  refine le_antisymm ?_ (le_rank_of_isUnit rfl h)
  calc Y.rank ≤ Q.rank := by rw [hY]; exact Matrix.rank_mul_le_right _ _
    _ ≤ r := by simpa using Q.rank_le_card_height

/-- **Skeleton (cross) decomposition.**  A matrix of rank `≤ r` with invertible compression
`B = Uᵀ Y V` satisfies `Y = Y V B⁻¹ Uᵀ Y`. -/
lemma skeleton {Y : Matrix m n ℝ} {C : Matrix (Fin r) m ℝ} {D : Matrix n (Fin r) ℝ}
    (hY : Y.rank ≤ r) (hB : IsUnit (C * Y * D).det) : Y * D * (C * Y * D)⁻¹ * C * Y = Y := by
  set K := Y * D with hK
  have hB' : C * Y * D = C * K := by rw [hK, Matrix.mul_assoc]
  have hKrank : r ≤ K.rank := by
    rw [hB'] at hB
    exact le_rank_of_isUnit (B := C * K) (P := K) (C := C) (D := 1) (by simp) hB
  have hle : LinearMap.range K.mulVecLin ≤ LinearMap.range Y.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact ⟨D *ᵥ x, by simp [hK, Matrix.mulVec_mulVec]⟩
  have heq : LinearMap.range K.mulVecLin = LinearMap.range Y.mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    change Y.rank ≤ K.rank
    omega
  have hcancel : K * (C * Y * D)⁻¹ * C * K = K := by
    rw [hB'] at hB ⊢
    rw [Matrix.mul_assoc _ C K, Matrix.mul_assoc K, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  rw [Matrix.ext_iff_mulVec]
  intro x
  have hx : Y *ᵥ x ∈ LinearMap.range K.mulVecLin := heq ▸ (⟨x, rfl⟩ : _ ∈ LinearMap.range _)
  obtain ⟨c, hc⟩ := hx
  have hc' : K *ᵥ c = Y *ᵥ x := hc
  calc (K * (C * Y * D)⁻¹ * C * Y) *ᵥ x = (K * (C * Y * D)⁻¹ * C) *ᵥ (Y *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
    _ = (K * (C * Y * D)⁻¹ * C * K) *ᵥ c := by rw [← hc', Matrix.mulVec_mulVec]
    _ = Y *ᵥ x := by rw [hcancel, hc']

/-! ### The retractions in closed form -/

/-- **Orthographic retraction** (arXiv 2309.06125, Algorithm 4), in the basis-free closed form
`W V (Uᵀ W V)⁻¹ Uᵀ W` with `W = X + Z`: Algorithm 4 returns `(W V) (Uᵀ W V)⁻¹ (Wᵀ U)ᵀ`, see
`algorithm4_eq`. -/
noncomputable def orthRetr (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (X Z : Matrix m n ℝ) :
    Matrix m n ℝ :=
  (X + Z) * V * (Uᵀ * (X + Z) * V)⁻¹ * Uᵀ * (X + Z)

/-- **KLS retraction** (arXiv 2309.06125, Algorithm 3): `U₁ U₁ᵀ (X + Z) V₁ V₁ᵀ`, with `U₁`, `V₁`
orthonormal bases of the ranges of `(X + Z) V` and `(X + Z)ᵀ U`.  The projectors are written with
`colProj`, so the value does not depend on the QR factorizations (see `algorithm3_eq`). -/
noncomputable def klsRetr (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (X Z : Matrix m n ℝ) :
    Matrix m n ℝ :=
  colProj ((X + Z) * V) * (X + Z) * colProj ((X + Z)ᵀ * U)

/-- **KSL retraction** (arXiv 2309.06125, Algorithm 2): `U₁ U₁ᵀ (X + Z)`, see `algorithm2_eq`. -/
noncomputable def kslRetr (V : Matrix n (Fin r) ℝ) (X Z : Matrix m n ℝ) : Matrix m n ℝ :=
  colProj ((X + Z) * V) * (X + Z)

namespace IsTangentRep

/-- `W V (Uᵀ W V)⁻¹ Uᵀ W = W + U_p A⁻¹ V_pᵀ` for `W = U A Vᵀ + U_p Vᵀ + U V_pᵀ`. -/
lemma skeleton_eq (rep : IsTangentRep U V A Up Vp T) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : IsUnit A.det) : T * V * (Uᵀ * T * V)⁻¹ * Uᵀ * T = T + Up * A⁻¹ * Vpᵀ := by
  have h1 := rep.mul_right hV
  have h2 := rep.mul_left hU
  have h3 := rep.sandwich hU hV
  have e1 : U * A * A⁻¹ = U := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
  have e2 : Up * A⁻¹ * (A * Vᵀ) = Up * Vᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  rw [h3, Matrix.mul_assoc _ Uᵀ T, h2, h1]
  calc (U * A + Up) * A⁻¹ * (A * Vᵀ + Vpᵀ)
      = U * A * A⁻¹ * (A * Vᵀ) + U * A * A⁻¹ * Vpᵀ + Up * A⁻¹ * (A * Vᵀ) + Up * A⁻¹ * Vpᵀ := by
        simp only [Matrix.add_mul, Matrix.mul_add]
        abel
    _ = T + Up * A⁻¹ * Vpᵀ := by
        rw [e1, e2, rep.eq, Matrix.mul_assoc U A Vᵀ]
        abel

lemma isUnit_K (rep : IsTangentRep U V A Up Vp T) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : IsUnit A.det) : IsUnit ((T * V)ᵀ * (T * V)).det := by
  apply isUnit_det_transpose_mul_self (W := Uᵀ)
  rw [← Matrix.mul_assoc, rep.sandwich hU hV]
  exact hA

lemma isUnit_L (rep : IsTangentRep U V A Up Vp T) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : IsUnit A.det) : IsUnit ((Tᵀ * U)ᵀ * (Tᵀ * U)).det := by
  apply isUnit_det_transpose_mul_self (W := Vᵀ)
  have e : Vᵀ * (Tᵀ * U) = (Uᵀ * T * V)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, rep.sandwich hU hV, Matrix.det_transpose]
  exact hA

/-- `U₁ U₁ᵀ U_p = K (Kᵀ K)⁻¹ U_pᵀ U_p`: the factor `U_p` is reduced by one order. -/
lemma colP_mul_Up (rep : IsTangentRep U V A Up Vp T) (hV : Vᵀ * V = 1) :
    colProj (T * V) * Up = T * V * ((T * V)ᵀ * (T * V))⁻¹ * (Upᵀ * Up) := by
  have h : (T * V)ᵀ * Up = Upᵀ * Up := by
    rw [rep.mul_right hV, Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul,
      Matrix.mul_assoc, rep.gaugeU, Matrix.mul_zero, zero_add]
  rw [Matrix.colProj_def, Matrix.mul_assoc _ _ Up, h]

/-- `V_pᵀ V₁ V₁ᵀ = V_pᵀ V_p (Lᵀ L)⁻¹ Lᵀ`: the factor `V_p` is reduced by one order. -/
lemma Vp_mul_colP (rep : IsTangentRep U V A Up Vp T) (hU : Uᵀ * U = 1) :
    Vpᵀ * colProj (Tᵀ * U) = Vpᵀ * Vp * ((Tᵀ * U)ᵀ * (Tᵀ * U))⁻¹ * (Tᵀ * U)ᵀ := by
  have h : Vpᵀ * (Tᵀ * U) = Vpᵀ * Vp := by
    rw [rep.transpose_mul hU, Matrix.mul_add, ← Matrix.mul_assoc, rep.gaugeV', Matrix.zero_mul,
      zero_add]
  rw [Matrix.colProj_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

end IsTangentRep

/-- Closed form of the orthographic retraction (arXiv 2309.06125, Algorithm 4):
`R^ORTH_X(Z) = X + Z + U_p (S + M)⁻¹ V_pᵀ`. -/
theorem orthRetr_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hA : IsUnit (S + M).det) :
    orthRetr U V X Z = X + Z + Up * (S + M)⁻¹ * Vpᵀ :=
  (rep.add_base h.eq).skeleton_eq h.orthU h.orthV hA

/-- **Difference of the KLS and the orthographic retraction** (full-space form of
arXiv 2309.06125, eq. (20)), with the two factors of order one in `U₁ᵀ U_p` and `V_pᵀ V₁` made
explicit.  Here `K = (X + Z) V`, `L = (X + Z)ᵀ U`. -/
theorem klsRetr_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hA : IsUnit (S + M).det) :
    klsRetr U V X Z = orthRetr U V X Z -
      ((X + Z) * V * (((X + Z) * V)ᵀ * ((X + Z) * V))⁻¹ * (Upᵀ * Up)) * (S + M)⁻¹ *
        (Vpᵀ * Vp * (((X + Z)ᵀ * U)ᵀ * ((X + Z)ᵀ * U))⁻¹ * ((X + Z)ᵀ * U)ᵀ) := by
  have repW := rep.add_base h.eq
  have hK := repW.isUnit_K h.orthU h.orthV hA
  have hL := repW.isUnit_L h.orthU h.orthV hA
  set W := X + Z with hW
  set K := W * V with hKdef
  set L := Wᵀ * U with hLdef
  have hR : orthRetr U V X Z = K * (Uᵀ * W * V)⁻¹ * Lᵀ := by
    rw [orthRetr, ← hW, hKdef, hLdef, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc _ Uᵀ W]
  have hW' : W = orthRetr U V X Z - Up * (S + M)⁻¹ * Vpᵀ := by
    rw [orthRetr_eq h rep hA, ← hW, add_sub_cancel_right]
  have h1 : colProj K * orthRetr U V X Z = orthRetr U V X Z := by
    rw [hR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, colP_mul_self hK]
  have h2 : orthRetr U V X Z * colProj L = orthRetr U V X Z := by
    rw [hR, Matrix.mul_assoc, transpose_mul_colP hL]
  have hP : colProj K * Up = K * (Kᵀ * K)⁻¹ * (Upᵀ * Up) := repW.colP_mul_Up h.orthV
  have hQ : Vpᵀ * colProj L = Vpᵀ * Vp * (Lᵀ * L)⁻¹ * Lᵀ := repW.Vp_mul_colP h.orthU
  calc klsRetr U V X Z = colProj K * W * colProj L := rfl
    _ = colProj K * orthRetr U V X Z * colProj L -
        colProj K * (Up * (S + M)⁻¹ * Vpᵀ) * colProj L := by
        conv_lhs => rw [hW']
        rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = orthRetr U V X Z - (colProj K * Up) * (S + M)⁻¹ * (Vpᵀ * colProj L) := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, hQ]

/-- The KSL retraction differs from the orthographic one by a term with one factor of order one
reduced; compare arXiv 2309.06125, §3.2. -/
theorem kslRetr_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hA : IsUnit (S + M).det) :
    kslRetr V X Z = orthRetr U V X Z -
      ((X + Z) * V * (((X + Z) * V)ᵀ * ((X + Z) * V))⁻¹ * (Upᵀ * Up)) * (S + M)⁻¹ * Vpᵀ := by
  have repW := rep.add_base h.eq
  have hK := repW.isUnit_K h.orthU h.orthV hA
  set W := X + Z with hW
  set K := W * V with hKdef
  have hR : orthRetr U V X Z = K * ((Uᵀ * W * V)⁻¹ * Uᵀ * W) := by
    rw [orthRetr, ← hW, hKdef]
    simp only [Matrix.mul_assoc]
  have hW' : W = orthRetr U V X Z - Up * (S + M)⁻¹ * Vpᵀ := by
    rw [orthRetr_eq h rep hA, ← hW, add_sub_cancel_right]
  have h1 : colProj K * orthRetr U V X Z = orthRetr U V X Z := by
    rw [hR, ← Matrix.mul_assoc, colP_mul_self hK]
  have hP : colProj K * Up = K * (Kᵀ * K)⁻¹ * (Upᵀ * Up) := repW.colP_mul_Up h.orthV
  calc kslRetr V X Z = colProj K * W := rfl
    _ = colProj K * orthRetr U V X Z - colProj K * (Up * (S + M)⁻¹ * Vpᵀ) := by
        conv_lhs => rw [hW']
        rw [Matrix.mul_sub]
    _ = orthRetr U V X Z - (colProj K * Up) * (S + M)⁻¹ * Vpᵀ := by
        rw [h1]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP]

/-! ### Eqs. (15)-(16): closest-point property and inverse of the orthographic retraction -/

/-- The affine slice `X + Z + N_X M_r` of arXiv 2309.06125, eq. (15). -/
def normalSlice (X Z : Matrix m n ℝ) : Set (Matrix m n ℝ) :=
  {Y | Y - (X + Z) ∈ (tangentSpace X)ᗮ}

/-- A point `Y` of the slice has the same compressions as `X + Z`. -/
lemma IsFactorization.compressions (h : IsFactorization X U S V) (hY : Y ∈ normalSlice X Z) :
    Y * V = (X + Z) * V ∧ Uᵀ * Y = Uᵀ * (X + Z) := by
  have hN := mem_orthogonal_iff_tanProj.1 hY
  have h1 := h.normal_mul_V hN
  have h2 := h.Ut_mul_normal hN
  rw [Matrix.sub_mul] at h1
  rw [Matrix.mul_sub] at h2
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- Matrices `U_p B V_pᵀ` are normal at `X`. -/
lemma IsFactorization.tanProj_Up_mul_Vp (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) (B : Matrix (Fin r) (Fin r) ℝ) :
    tanProj X (Up * B * Vpᵀ) = 0 := by
  have e1 : Uᵀ * (Up * B * Vpᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rep.gaugeU, Matrix.zero_mul, Matrix.zero_mul]
  have e2 : Up * B * Vpᵀ * V = 0 := by
    rw [Matrix.mul_assoc, rep.gaugeV', Matrix.mul_zero]
  rw [h.tanProj_apply, e2, Matrix.mul_assoc U, e1]
  simp

/-- Uniqueness in eq. (15) of arXiv 2309.06125: a matrix of rank `≤ r` in the slice is the
orthographic retraction. -/
theorem IsFactorization.eq_orthRetr (h : IsFactorization X U S V) (hY : Y ∈ normalSlice X Z)
    (hrank : Y.rank ≤ r) (hA : IsUnit (Uᵀ * (X + Z) * V).det) : Y = orthRetr U V X Z := by
  obtain ⟨h1, h2⟩ := h.compressions hY
  have hB : Uᵀ * Y * V = Uᵀ * (X + Z) * V := by rw [h2]
  have hsk := skeleton (C := Uᵀ) (D := V) hrank (by rwa [hB])
  rw [orthRetr, ← hsk, hB, h1, Matrix.mul_assoc _ Uᵀ Y, h2, ← Matrix.mul_assoc _ Uᵀ (X + Z)]

/-- The compression of `X + Z` is `S + M`. -/
lemma IsFactorization.compression_eq (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) : Uᵀ * (X + Z) * V = S + M :=
  (rep.add_base h.eq).sandwich h.orthU h.orthV

lemma orthRetr_factor (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (X Z : Matrix m n ℝ) :
    orthRetr U V X Z = ((X + Z) * V) * ((Uᵀ * (X + Z) * V)⁻¹ * Uᵀ * (X + Z)) := by
  simp only [orthRetr, Matrix.mul_assoc]

/-- The orthographic retraction lies in the slice `X + Z + N_X M_r` of arXiv 2309.06125, eq. (15),
and has rank `r`. -/
theorem IsFactorization.orthRetr_mem (h : IsFactorization X U S V)
    (hZ : Z ∈ tangentSpace X) (hA : IsUnit (Uᵀ * (X + Z) * V).det) :
    orthRetr U V X Z ∈ normalSlice X Z ∩ rankSet m n r := by
  classical
  have rep := h.tangentRep hZ
  have hA' : IsUnit (S + Uᵀ * Z * V).det := by rwa [← h.compression_eq rep]
  have hform := orthRetr_eq h rep hA'
  have hmem : orthRetr U V X Z ∈ normalSlice X Z := by
    change orthRetr U V X Z - (X + Z) ∈ (tangentSpace X)ᗮ
    rw [hform, add_sub_cancel_left, mem_orthogonal_iff_tanProj]
    exact h.tanProj_Up_mul_Vp rep _
  refine ⟨hmem, ?_⟩
  obtain ⟨h1, h2⟩ := h.compressions hmem
  have hB : Uᵀ * orthRetr U V X Z * V = Uᵀ * (X + Z) * V := by rw [h2]
  exact rank_eq_of_factor (C := Uᵀ) (D := V) (orthRetr_factor U V X Z) (by rwa [hB])

/-- **Eq. (15) of arXiv 2309.06125, uniqueness form.**  If `Uᵀ (X + Z) V = S + M` is invertible
(which is the case for small `Z`, see `IsFactorization.isUnit_compression`), the slice
`X + Z + N_X M_r` meets `M_r` in exactly one point, the output of Algorithm 4.  In particular the
minimization problem (15) is well posed; `orthRetr_isMinOn` states it in that form. -/
theorem IsFactorization.normalSlice_inter_rankSet
    (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X)
    (hA : IsUnit (Uᵀ * (X + Z) * V).det) :
    normalSlice X Z ∩ rankSet m n r = {orthRetr U V X Z} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨h.orthRetr_mem hZ hA, fun Y hY => ?_⟩
  exact h.eq_orthRetr hY.1 (le_of_eq hY.2) hA

/-- **Eq. (15) of arXiv 2309.06125.**  `R^ORTH_X(Z)` solves
`min {‖X + Z - Y‖_F : Y ∈ (X + Z + N_X M_r) ∩ M_r}`. -/
theorem IsFactorization.orthRetr_isMinOn
    (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X)
    (hA : IsUnit (Uᵀ * (X + Z) * V).det) :
    IsMinOn (fun Y => ‖X + Z - Y‖) (normalSlice X Z ∩ rankSet m n r) (orthRetr U V X Z) := by
  rw [h.normalSlice_inter_rankSet hZ hA]
  exact isMinOn_iff.2 fun Y hY => by rw [Set.mem_singleton_iff.1 hY]

/-- The compression `Uᵀ W V` is invertible if `W` is closer to `X` than `σ_min(S)`.  This is the
meaning of "locally" in eqs. (15)-(16) of arXiv 2309.06125: take `W = X + Z` or `W = Y`. -/
theorem IsFactorization.isUnit_compression
    (h : IsFactorization X U S V) {W : Matrix m n ℝ} {ρ : ℝ}
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    (hW : ‖W - X‖ < ρ) : IsUnit (Uᵀ * W * V).det := by
  classical
  set E := Uᵀ * (W - X) * V with hE
  have hB : Uᵀ * W * V = S + E := by
    rw [hE, ← h.sandwich, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hUt : specNorm Uᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact specNorm_le_one_of_orthonormal h.orthU
  have hVn : specNorm V ≤ 1 := specNorm_le_one_of_orthonormal h.orthV
  have hEn : ‖E‖ ≤ ‖W - X‖ := by
    calc ‖E‖ ≤ specNorm Uᵀ * ‖(W - X) * V‖ := by
          rw [hE, Matrix.mul_assoc]
          exact frob_mul_le _ _
      _ ≤ 1 * ‖(W - X) * V‖ := by gcongr
      _ = ‖(W - X) * V‖ := one_mul _
      _ ≤ ‖W - X‖ * specNorm V := frob_mul_le' _ _
      _ ≤ ‖W - X‖ * 1 := by gcongr
      _ = ‖W - X‖ := mul_one _
  have hEs : specNorm E ≤ ‖W - X‖ := (specNorm_le_frob E).trans hEn
  have hgap : 0 < ρ - ‖W - X‖ := sub_pos.2 hW
  rw [hB]
  refine isUnit_det_of_bounded_below hgap fun v => ?_
  have hadd : Matrix.toEuclideanLin (S + E) v = Matrix.toEuclideanLin S v +
      Matrix.toEuclideanLin E v := by
    rw [map_add, LinearMap.add_apply]
  have h1 := hS v
  have h2 := norm_toEuclideanLin_le E v
  have h3 : ‖Matrix.toEuclideanLin S v‖ ≤ ‖Matrix.toEuclideanLin (S + E) v‖ +
      ‖Matrix.toEuclideanLin E v‖ := by
    rw [hadd]
    simpa using norm_sub_le (Matrix.toEuclideanLin S v + Matrix.toEuclideanLin E v)
      (Matrix.toEuclideanLin E v)
  have h4 : specNorm E * ‖v‖ ≤ ‖W - X‖ * ‖v‖ := by gcongr
  nlinarith

/-- **Eq. (16) of arXiv 2309.06125, left inverse.**  `Π(X) (R^ORTH_X(Z) - X) = Z`. -/
theorem IsFactorization.tanProj_orthRetr_sub
    (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X)
    (hA : IsUnit (Uᵀ * (X + Z) * V).det) : tanProj X (orthRetr U V X Z - X) = Z := by
  classical
  have rep := h.tangentRep hZ
  have hA' : IsUnit (S + Uᵀ * Z * V).det := by rwa [← h.compression_eq rep]
  rw [orthRetr_eq h rep hA', add_assoc, add_sub_cancel_left, map_add, h.tanProj_Up_mul_Vp rep,
    add_zero, tanProj_eq_self_iff.2 hZ]

/-- **Eq. (16) of arXiv 2309.06125, right inverse.**  A matrix `Y` of rank `≤ r` with invertible
compression `Uᵀ Y V` (for instance `‖Y - X‖ < σ_min(S)`, see
`IsFactorization.isUnit_compression`) satisfies `R^ORTH_X(Π(X) (Y - X)) = Y`. -/
theorem IsFactorization.orthRetr_tanProj_sub (h : IsFactorization X U S V)
    (hrank : Y.rank ≤ r) (hY : IsUnit (Uᵀ * Y * V).det) :
    orthRetr U V X (tanProj X (Y - X)) = Y := by
  set Z := tanProj X (Y - X) with hZ
  have hP := isOrthProj_tanProj X
  have hmem : Y ∈ normalSlice X Z := by
    change Y - (X + Z) ∈ (tangentSpace X)ᗮ
    rw [mem_orthogonal_iff_tanProj]
    have e : Y - (X + Z) = (Y - X) - tanProj X (Y - X) := by rw [← hZ]; abel
    rw [e, map_sub, hP.idem, sub_self]
  obtain ⟨-, h2⟩ := h.compressions hmem
  have hB : Uᵀ * (X + Z) * V = Uᵀ * Y * V := by rw [h2]
  exact (h.eq_orthRetr hmem hrank (by rwa [hB])).symm

/-! ### Algorithms 2-4 of arXiv 2309.06125 -/

section Algorithms

variable {U₁ : Matrix m (Fin r) ℝ} {V₁ : Matrix n (Fin r) ℝ}
  {SU SV Sh St S₁ : Matrix (Fin r) (Fin r) ℝ}

/-- Step 5 of Algorithm 3 of arXiv 2309.06125 is `Σ₁ = U₁ᵀ (X + Z) V₁`, the identity stated in the
margin of the algorithm. -/
theorem algorithm3_Sstep (hX : X = U * S * Vᵀ) (rep : IsTangentRep U V M Up Vp Z) :
    U₁ᵀ * U * ((S + M) * (V₁ᵀ * V)ᵀ + Vpᵀ * V₁) + U₁ᵀ * Up * (V₁ᵀ * V)ᵀ = U₁ᵀ * (X + Z) * V₁ := by
  rw [(rep.add_base hX).eq]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  abel

/-- **The KLS retraction is what Algorithm 3 computes** (arXiv 2309.06125): with the QR
factorizations `U₁ S_U = U (S + M) + U_p`, `V₁ S_V = V (S + M)ᵀ + V_p` of steps 1-2, the output
`U₁ Σ₁ Vᵀ₁` of step 8, with `Σ₁` from step 5, is `U₁ U₁ᵀ (X + Z) V₁ V₁ᵀ = klsRetr U V X Z`.  The
optional SVD steps 6-7 do not change the product. -/
theorem algorithm3_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hSU : IsUnit SU.det) (hSV : IsUnit SV.det)
    (hK : U₁ * SU = U * (S + M) + Up) (hL : V₁ * SV = V * (S + M)ᵀ + Vp) :
    U₁ * (U₁ᵀ * U * ((S + M) * (V₁ᵀ * V)ᵀ + Vpᵀ * V₁) + U₁ᵀ * Up * (V₁ᵀ * V)ᵀ) * V₁ᵀ =
      klsRetr U V X Z ∧
    klsRetr U V X Z = U₁ * U₁ᵀ * (X + Z) * V₁ * V₁ᵀ := by
  have repW := rep.add_base h.eq
  have hP : colProj ((X + Z) * V) = U₁ * U₁ᵀ :=
    colP_of_qr hU₁ hSU (by rw [repW.mul_right h.orthV, ← hK])
  have hQ : colProj ((X + Z)ᵀ * U) = V₁ * V₁ᵀ :=
    colP_of_qr hV₁ hSV (by rw [repW.transpose_mul h.orthU, ← hL])
  have h2 : klsRetr U V X Z = U₁ * U₁ᵀ * (X + Z) * V₁ * V₁ᵀ := by
    rw [klsRetr, hP, hQ]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, h2⟩
  rw [algorithm3_Sstep h.eq rep, h2]
  simp only [Matrix.mul_assoc]

/-- **The orthographic retraction is what Algorithm 4 computes** (arXiv 2309.06125). -/
theorem algorithm4_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hK : U₁ * SU = U * (S + M) + Up) (hL : V₁ * SV = V * (S + M)ᵀ + Vp) :
    U₁ * (SU * (S + M)⁻¹ * SVᵀ) * V₁ᵀ = orthRetr U V X Z := by
  have repW := rep.add_base h.eq
  have h1 : (X + Z) * V = U₁ * SU := by rw [repW.mul_right h.orthV, hK]
  have h2 : Uᵀ * (X + Z) = SVᵀ * V₁ᵀ := by
    have := congrArg Matrix.transpose hL
    rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose] at this
    rw [repW.mul_left h.orthU, this]
  rw [orthRetr, h1, h.compression_eq rep, Matrix.mul_assoc _ Uᵀ, h2]
  simp only [Matrix.mul_assoc]

/-- **Eq. (17) of arXiv 2309.06125.** -/
theorem eq17 (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hK : U₁ * SU = U * (S + M) + Up) (hL : V₁ * SV = V * (S + M)ᵀ + Vp) :
    SU = U₁ᵀ * U * (S + M) + U₁ᵀ * Up ∧ SV = V₁ᵀ * V * (S + M)ᵀ + V₁ᵀ * Vp := by
  constructor
  · calc SU = U₁ᵀ * (U₁ * SU) := by rw [← Matrix.mul_assoc, hU₁, Matrix.one_mul]
      _ = _ := by rw [hK, Matrix.mul_add, Matrix.mul_assoc]
  · calc SV = V₁ᵀ * (V₁ * SV) := by rw [← Matrix.mul_assoc, hV₁, Matrix.one_mul]
      _ = _ := by rw [hL, Matrix.mul_add, Matrix.mul_assoc]

/-- **Eqs. (19)-(20) of arXiv 2309.06125**: with `Σ_ORTH = S_U (S + M)⁻¹ S_Vᵀ` and `Σ_KLS` the
matrix of step 5 of Algorithm 3, `Σ_ORTH - Σ_KLS = U₁ᵀ U_p (S + M)⁻¹ V_pᵀ V₁`. -/
theorem eq20 (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hA : IsUnit (S + M).det)
    (hK : U₁ * SU = U * (S + M) + Up) (hL : V₁ * SV = V * (S + M)ᵀ + Vp) :
    SU * (S + M)⁻¹ * SVᵀ -
        (U₁ᵀ * U * ((S + M) * (V₁ᵀ * V)ᵀ + Vpᵀ * V₁) + U₁ᵀ * Up * (V₁ᵀ * V)ᵀ) =
      U₁ᵀ * Up * (S + M)⁻¹ * (Vpᵀ * V₁) := by
  obtain ⟨h1, h2⟩ := eq17 hU₁ hV₁ hK hL
  have h3 : SVᵀ = (S + M) * (V₁ᵀ * V)ᵀ + Vpᵀ * V₁ := by
    rw [h2]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
  set A := S + M
  set G := V₁ᵀ * V
  set Fp := Vpᵀ * V₁
  set Ep := U₁ᵀ * Up
  rw [h3, h1]
  have e1 : U₁ᵀ * U * A * A⁻¹ = U₁ᵀ * U := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
  have e2 : Ep * A⁻¹ * (A * Gᵀ) = Ep * Gᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  calc (U₁ᵀ * U * A + Ep) * A⁻¹ * (A * Gᵀ + Fp) - (U₁ᵀ * U * (A * Gᵀ + Fp) + Ep * Gᵀ)
      = U₁ᵀ * U * A * A⁻¹ * (A * Gᵀ + Fp) + Ep * A⁻¹ * (A * Gᵀ) + Ep * A⁻¹ * Fp
          - (U₁ᵀ * U * (A * Gᵀ + Fp) + Ep * Gᵀ) := by
        rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add (Ep * A⁻¹)]
        abel
    _ = Ep * A⁻¹ * Fp := by
        rw [e1, e2]
        abel

/-- **The KSL retraction is what Algorithm 2 computes** (arXiv 2309.06125): the output
`U₁ Σ₁ V₁ᵀ` of the K-, S- and L-steps equals `U₁ U₁ᵀ (X + Z)`. -/
theorem algorithm2_eq (h : IsFactorization X U S V) (rep : IsTangentRep U V M Up Vp Z)
    (hU₁ : U₁ᵀ * U₁ = 1) (hSh : IsUnit Sh.det)
    (hK : U₁ * Sh = U * (S + M) + Up) (hS : St = Sh - (U₁ᵀ * Up + U₁ᵀ * U * M))
    (hL : V₁ * S₁ᵀ = V * Stᵀ + Zᵀ * U₁) :
    U₁ * S₁ * V₁ᵀ = kslRetr V X Z ∧ kslRetr V X Z = U₁ * U₁ᵀ * (X + Z) := by
  have repW := rep.add_base h.eq
  have hP : colProj ((X + Z) * V) = U₁ * U₁ᵀ :=
    colP_of_qr hU₁ hSh (by rw [repW.mul_right h.orthV, ← hK])
  have h2 : kslRetr V X Z = U₁ * U₁ᵀ * (X + Z) := by rw [kslRetr, hP]
  refine ⟨?_, h2⟩
  have hSh' : Sh = U₁ᵀ * U * (S + M) + U₁ᵀ * Up := by
    calc Sh = U₁ᵀ * (U₁ * Sh) := by rw [← Matrix.mul_assoc, hU₁, Matrix.one_mul]
      _ = _ := by rw [hK, Matrix.mul_add, Matrix.mul_assoc]
  have hSt : St = U₁ᵀ * U * S := by
    rw [hS, hSh', Matrix.mul_add]
    abel
  have ht : S₁ * V₁ᵀ = St * Vᵀ + U₁ᵀ * Z := by
    have := congrArg Matrix.transpose hL
    simpa [Matrix.transpose_mul, Matrix.transpose_add] using this
  rw [h2, Matrix.mul_assoc U₁ S₁, ht, hSt, h.eq, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_assoc]

end Algorithms

/-! ### Independence of the factorization -/

lemma IsFactorization.transpose (h : IsFactorization X U S V) :
    IsFactorization (r := r) Xᵀ V Sᵀ U where
  orthU := h.orthV
  orthV := h.orthU
  det := by rw [Matrix.det_transpose]; exact h.det
  eq := by rw [h.eq]; simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Two orthonormal column bases of the range of `X` differ by an invertible factor. -/
lemma IsFactorization.left_gauge (h : IsFactorization X U S V) (h' : IsFactorization X U' S' V') :
    ∃ G : Matrix (Fin r) (Fin r) ℝ, IsUnit G.det ∧ U' = U * G := by
  have e : U' = X * V' * S'⁻¹ := by
    rw [h'.mul_V, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h'.det, Matrix.mul_one]
  set G := S * Vᵀ * V' * S'⁻¹ with hG
  have hU' : U' = U * G := by
    rw [e, h.eq]
    simp only [hG, Matrix.mul_assoc]
  have hGG : Gᵀ * G = 1 := by
    have hu := h'.orthU
    rw [hU', Matrix.transpose_mul] at hu
    calc Gᵀ * G = Gᵀ * (Uᵀ * U) * G := by rw [h.orthU, Matrix.mul_one]
      _ = Gᵀ * Uᵀ * (U * G) := by simp only [Matrix.mul_assoc]
      _ = 1 := hu
  exact ⟨G, Matrix.isUnit_det_of_left_inverse hGG, hU'⟩

/-- `R^KLS` does not depend on the factorization of `X`, as needed for Algorithm 3 of
arXiv 2309.06125 to define a map on the tangent bundle. -/
theorem IsFactorization.klsRetr_gauge (h : IsFactorization X U S V)
    (h' : IsFactorization X U' S' V') (Z : Matrix m n ℝ) :
    klsRetr U' V' X Z = klsRetr U V X Z := by
  obtain ⟨G, hG, rfl⟩ := h.left_gauge h'
  obtain ⟨H, hH, rfl⟩ := h.transpose.left_gauge h'.transpose
  rw [klsRetr, klsRetr, ← Matrix.mul_assoc (X + Z) V H, ← Matrix.mul_assoc (X + Z)ᵀ U G,
    colP_gauge hH, colP_gauge hG]

/-- `R^KSL` does not depend on the factorization of `X`, as needed for Algorithm 2 of
arXiv 2309.06125 to define a map on the tangent bundle. -/
theorem IsFactorization.kslRetr_gauge (h : IsFactorization X U S V)
    (h' : IsFactorization X U' S' V') (Z : Matrix m n ℝ) : kslRetr V' X Z = kslRetr V X Z := by
  obtain ⟨H, hH, rfl⟩ := h.transpose.left_gauge h'.transpose
  rw [kslRetr, kslRetr, ← Matrix.mul_assoc (X + Z) V H, colP_gauge hH]

/-- `R^ORTH` does not depend on the factorization of `X`, as needed for Algorithm 4 of
arXiv 2309.06125 to define a map on the tangent bundle. -/
theorem IsFactorization.orthRetr_gauge (h : IsFactorization X U S V)
    (h' : IsFactorization X U' S' V') (Z : Matrix m n ℝ) :
    orthRetr U' V' X Z = orthRetr U V X Z := by
  obtain ⟨G, hG, rfl⟩ := h.left_gauge h'
  obtain ⟨H, hH, rfl⟩ := h.transpose.left_gauge h'.transpose
  have hGt : IsUnit Gᵀ.det := by rwa [Matrix.det_transpose]
  have e : (U * G)ᵀ * (X + Z) * (V * H) = Gᵀ * (Uᵀ * (X + Z) * V) * H := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [orthRetr, orthRetr, e, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul]
  calc (X + Z) * (V * H) * (H⁻¹ * ((Uᵀ * (X + Z) * V)⁻¹ * Gᵀ⁻¹)) * (Gᵀ * Uᵀ) * (X + Z)
      = (X + Z) * V * (H * H⁻¹) * (Uᵀ * (X + Z) * V)⁻¹ * (Gᵀ⁻¹ * Gᵀ) * Uᵀ * (X + Z) := by
        simp only [Matrix.mul_assoc]
    _ = (X + Z) * V * (Uᵀ * (X + Z) * V)⁻¹ * Uᵀ * (X + Z) := by
        rw [Matrix.mul_nonsing_inv _ hH, Matrix.nonsing_inv_mul _ hGt, Matrix.mul_one,
          Matrix.mul_one]

/-- A basis pair of a compact factorization of `X` (chosen; the retractions do not depend on the
choice, see `retrORTH_eq`, `retrKLS_eq`, `retrKSL_eq`). -/
noncomputable def basisChoice (r : ℕ) (X : Matrix m n ℝ) :
    Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ :=
  Classical.epsilon fun p => ∃ S, IsFactorization (r := r) X p.1 S p.2

lemma basisChoice_spec (hX : X.rank = r) :
    ∃ S, IsFactorization X (basisChoice r X).1 S (basisChoice r X).2 := by
  obtain ⟨U, S, V, h⟩ := exists_factorization hX
  exact Classical.epsilon_spec (p := fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ =>
    ∃ S, IsFactorization (r := r) X p.1 S p.2) ⟨(U, V), S, h⟩

/-- The orthographic retraction `R^ORTH` as a map on the tangent bundle of `M_r`. -/
noncomputable def retrORTH (r : ℕ) (X Z : Matrix m n ℝ) : Matrix m n ℝ :=
  orthRetr (basisChoice r X).1 (basisChoice r X).2 X Z

/-- The KLS retraction `R^KLS` as a map on the tangent bundle of `M_r`. -/
noncomputable def retrKLS (r : ℕ) (X Z : Matrix m n ℝ) : Matrix m n ℝ :=
  klsRetr (basisChoice r X).1 (basisChoice r X).2 X Z

/-- The KSL retraction `R^KSL` as a map on the tangent bundle of `M_r`. -/
noncomputable def retrKSL (r : ℕ) (X Z : Matrix m n ℝ) : Matrix m n ℝ :=
  kslRetr (basisChoice r X).2 X Z

/-- `retrORTH` is the output of Algorithm 4 of arXiv 2309.06125 for every factorization of `X`. -/
theorem retrORTH_eq (h : IsFactorization X U S V) (Z : Matrix m n ℝ) :
    retrORTH r X Z = orthRetr U V X Z := by
  obtain ⟨S₀, h₀⟩ := basisChoice_spec (r := r) h.rank
  exact h.orthRetr_gauge h₀ Z

/-- `retrKLS` is the output of Algorithm 3 of arXiv 2309.06125 for every factorization of `X`. -/
theorem retrKLS_eq (h : IsFactorization X U S V) (Z : Matrix m n ℝ) :
    retrKLS r X Z = klsRetr U V X Z := by
  obtain ⟨S₀, h₀⟩ := basisChoice_spec (r := r) h.rank
  exact h.klsRetr_gauge h₀ Z

/-- `retrKSL` is the output of Algorithm 2 of arXiv 2309.06125 for every factorization of `X`. -/
theorem retrKSL_eq (h : IsFactorization X U S V) (Z : Matrix m n ℝ) :
    retrKSL r X Z = kslRetr V X Z := by
  obtain ⟨S₀, h₀⟩ := basisChoice_spec (r := r) h.rank
  exact h.kslRetr_gauge h₀ Z

/-! ### Smoothness -/

section Smooth

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : WithTop ℕ∞}

lemma contDiffAt_colP {A : F → Matrix m (Fin r) ℝ} {x : F} (hA : ContDiffAt ℝ N A x)
    (hdet : IsUnit ((A x)ᵀ * A x).det) : ContDiffAt ℝ N (fun y => colProj (A y)) x := by
  simp only [Matrix.colProj_def]
  exact contDiffAt_mul (contDiffAt_mul hA (contDiffAt_inv
    (contDiffAt_mul (contDiffAt_transpose hA) hA) hdet)) (contDiffAt_transpose hA)

/-- `R^ORTH` is jointly smooth in the factors and the tangent vector, wherever `Uᵀ (X + Z) V` is
invertible (the smoothness of the map `R` of arXiv 2309.06125, §2.1, in a chart). -/
theorem contDiffAt_orthRetr (hA : IsUnit (Uᵀ * (X + Z) * V).det) :
    ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ × Matrix m n ℝ =>
      orthRetr p.1 p.2.1 p.2.2.1 p.2.2.2) (U, V, X, Z) := by
  have hu : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.1) (U, V, X, Z) := contDiffAt_fst
  have hv : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.2.1) (U, V, X, Z) := contDiffAt_fst.comp _ contDiffAt_snd
  have hw : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.2.2.1 + p.2.2.2) (U, V, X, Z) :=
    (contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)).add
      (contDiffAt_snd.comp _ (contDiffAt_snd.comp _ contDiffAt_snd))
  have hut := contDiffAt_transpose hu
  exact contDiffAt_mul (contDiffAt_mul (contDiffAt_mul (contDiffAt_mul hw hv)
    (contDiffAt_inv (contDiffAt_mul (contDiffAt_mul hut hw) hv) hA)) hut) hw

/-- `R^KLS` is jointly smooth in the factors and the tangent vector, wherever the two
orthonormalizations are defined (first step of the proof of Prop. 1 of arXiv 2309.06125). -/
theorem contDiffAt_klsRetr (hK : IsUnit (((X + Z) * V)ᵀ * ((X + Z) * V)).det)
    (hL : IsUnit (((X + Z)ᵀ * U)ᵀ * ((X + Z)ᵀ * U)).det) :
    ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ × Matrix m n ℝ =>
      klsRetr p.1 p.2.1 p.2.2.1 p.2.2.2) (U, V, X, Z) := by
  have hu : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.1) (U, V, X, Z) := contDiffAt_fst
  have hv : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.2.1) (U, V, X, Z) := contDiffAt_fst.comp _ contDiffAt_snd
  have hw : ContDiffAt ℝ N (fun p : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ × Matrix m n ℝ ×
      Matrix m n ℝ => p.2.2.1 + p.2.2.2) (U, V, X, Z) :=
    (contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)).add
      (contDiffAt_snd.comp _ (contDiffAt_snd.comp _ contDiffAt_snd))
  exact contDiffAt_mul (contDiffAt_mul (contDiffAt_colP (contDiffAt_mul hw hv) hK) hw)
    (contDiffAt_colP (contDiffAt_mul (contDiffAt_transpose hw) hu) hL)

/-- `R^KSL` is jointly smooth in the factors and the tangent vector, wherever the
orthonormalization is defined (the smoothness of the map `R` of arXiv 2309.06125, §2.1, in a
chart). -/
theorem contDiffAt_kslRetr (hK : IsUnit (((X + Z) * V)ᵀ * ((X + Z) * V)).det) :
    ContDiffAt ℝ N (fun p : Matrix n (Fin r) ℝ × Matrix m n ℝ × Matrix m n ℝ =>
      kslRetr p.1 p.2.1 p.2.2) (V, X, Z) := by
  have hv : ContDiffAt ℝ N (fun p : Matrix n (Fin r) ℝ × Matrix m n ℝ × Matrix m n ℝ => p.1)
      (V, X, Z) := contDiffAt_fst
  have hw : ContDiffAt ℝ N (fun p : Matrix n (Fin r) ℝ × Matrix m n ℝ × Matrix m n ℝ =>
      p.2.1 + p.2.2) (V, X, Z) :=
    (contDiffAt_fst.comp _ contDiffAt_snd).add (contDiffAt_snd.comp _ contDiffAt_snd)
  exact contDiffAt_mul (contDiffAt_colP (contDiffAt_mul hw hv) hK) hw

end Smooth

end Geometry

/-! ### Jets of curves -/

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve of the form `x + τ v + τ² c(τ)`, with `c` of class `C²` at `0`, has value `x`, velocity
`v` and acceleration `2 c(0)` at `0`. -/
lemma jet_of_expansion {γ c : ℝ → E} {x v : E} (hc : ContDiffAt ℝ 2 c 0)
    (he : ∀ᶠ τ in 𝓝 (0 : ℝ), γ τ = x + τ • v + τ ^ 2 • c τ) :
    γ 0 = x ∧ HasDerivAt γ v 0 ∧ deriv (deriv γ) 0 = (2 : ℝ) • c 0 := by
  have hdc := contDiffAt_eventually_differentiableAt hc
  have hdd := (contDiffAt_differentiableAt_deriv hc).hasDerivAt
  have hc1 : HasDerivAt c (deriv c 0) 0 := (hc.differentiableAt (by norm_num)).hasDerivAt
  set g : ℝ → E := fun τ => x + τ • v + τ ^ 2 • c τ with hg
  have hgd : ∀ τ, DifferentiableAt ℝ c τ →
      HasDerivAt g (v + (τ ^ 2 • deriv c τ + (2 * τ) • c τ)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => x + τ • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add x
    have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
    exact h1.add (h2.fun_smul hτ.hasDerivAt)
  have hγg : γ =ᶠ[𝓝 0] g := he
  have h0 : γ 0 = x := by
    have := hγg.self_of_nhds
    simpa [hg] using this
  have hvel : HasDerivAt γ v 0 := by
    have := (hgd 0 hdc.self_of_nhds).congr_of_eventuallyEq hγg
    simpa using this
  refine ⟨h0, hvel, ?_⟩
  have hdγ : deriv γ =ᶠ[𝓝 0] fun τ => v + (τ ^ 2 • deriv c τ + (2 * τ) • c τ) := by
    filter_upwards [hγg.eventuallyEq_nhds, hdc] with τ hτ hd
    rw [hτ.deriv_eq]
    exact (hgd τ hd).deriv
  have hfin : HasDerivAt (fun τ : ℝ => v + (τ ^ 2 • deriv c τ + (2 * τ) • c τ))
      ((2 : ℝ) • c 0) 0 := by
    have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * 0) 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    have h3 := h2.fun_smul hdd
    have h4 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
    have h5 := h4.fun_smul hc1
    have h6 := (h3.add h5).const_add v
    simpa using h6
  exact (hfin.congr_of_eventuallyEq hdγ).deriv

end Jets

/-! ### Prop. 1: the KLS retraction is a second-order retraction -/

section Curves

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {X Z : Matrix m n ℝ} {U Up : Matrix m (Fin r) ℝ} {V Vp : Matrix n (Fin r) ℝ}
  {S M : Matrix (Fin r) (Fin r) ℝ}

/-- The remainder in `R^KLS_X(τ Z) = R^ORTH_X(τ Z) - τ⁴ klsRem(τ)`. -/
noncomputable def klsRem (U Up : Matrix m (Fin r) ℝ) (V Vp : Matrix n (Fin r) ℝ)
    (S M : Matrix (Fin r) (Fin r) ℝ) (X Z : Matrix m n ℝ) (τ : ℝ) : Matrix m n ℝ :=
  ((X + τ • Z) * V * (((X + τ • Z) * V)ᵀ * ((X + τ • Z) * V))⁻¹ * (Upᵀ * Up)) * (S + τ • M)⁻¹ *
    (Vpᵀ * Vp * (((X + τ • Z)ᵀ * U)ᵀ * ((X + τ • Z)ᵀ * U))⁻¹ * ((X + τ • Z)ᵀ * U)ᵀ)

/-- The remainder in `R^KSL_X(τ Z) = R^ORTH_X(τ Z) - τ³ kslRem(τ)`. -/
noncomputable def kslRem (Up : Matrix m (Fin r) ℝ) (V Vp : Matrix n (Fin r) ℝ)
    (S M : Matrix (Fin r) (Fin r) ℝ) (X Z : Matrix m n ℝ) (τ : ℝ) : Matrix m n ℝ :=
  ((X + τ • Z) * V * (((X + τ • Z) * V)ᵀ * ((X + τ • Z) * V))⁻¹ * (Upᵀ * Up)) * (S + τ • M)⁻¹ * Vpᵀ

lemma eventually_isUnit_add_smul (hS : IsUnit S.det) (M : Matrix (Fin r) (Fin r) ℝ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), IsUnit (S + τ • M).det := by
  have hc : ContDiffAt ℝ 0 (fun τ : ℝ => S + τ • M) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  exact eventually_isUnit_det hc.continuousAt (by simpa using hS)

lemma IsFactorization.orthRetr_smul (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) {τ : ℝ} (hτ : IsUnit (S + τ • M).det) :
    orthRetr U V X (τ • Z) = X + τ • Z + τ ^ 2 • (Up * (S + τ • M)⁻¹ * Vpᵀ) := by
  rw [orthRetr_eq h (rep.smul τ) hτ]
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, sq]

lemma IsFactorization.klsRetr_smul (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) {τ : ℝ} (hτ : IsUnit (S + τ • M).det) :
    klsRetr U V X (τ • Z) = orthRetr U V X (τ • Z) - τ ^ 4 • klsRem U Up V Vp S M X Z τ := by
  rw [klsRetr_eq h (rep.smul τ) hτ, klsRem]
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 2
  ring

lemma IsFactorization.kslRetr_smul (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) {τ : ℝ} (hτ : IsUnit (S + τ • M).det) :
    kslRetr V X (τ • Z) = orthRetr U V X (τ • Z) - τ ^ 3 • kslRem Up V Vp S M X Z τ := by
  rw [kslRetr_eq h (rep.smul τ) hτ, kslRem]
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 2
  ring

section

variable {N : WithTop ℕ∞}

lemma contDiffAt_line (X Z : Matrix m n ℝ) : ContDiffAt ℝ N (fun τ : ℝ => X + τ • Z) 0 :=
  contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)

lemma contDiffAt_inv_line (hS : IsUnit S.det) (M : Matrix (Fin r) (Fin r) ℝ) :
    ContDiffAt ℝ N (fun τ : ℝ => (S + τ • M)⁻¹) 0 :=
  contDiffAt_inv (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)) (by simpa using hS)

lemma IsFactorization.contDiffAt_K (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) :
    ContDiffAt ℝ N (fun τ : ℝ => (X + τ • Z) * V *
      (((X + τ • Z) * V)ᵀ * ((X + τ • Z) * V))⁻¹) 0 := by
  have hK : ContDiffAt ℝ N (fun τ : ℝ => (X + τ • Z) * V) 0 :=
    contDiffAt_mul (contDiffAt_line X Z) contDiffAt_const
  have h0 : IsUnit (S + (0 : ℝ) • M).det := by simpa using h.det
  have hdet := ((rep.smul 0).add_base h.eq).isUnit_K h.orthU h.orthV h0
  exact contDiffAt_mul hK (contDiffAt_inv (contDiffAt_mul (contDiffAt_transpose hK) hK) hdet)

lemma IsFactorization.contDiffAt_L (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) :
    ContDiffAt ℝ N (fun τ : ℝ => (((X + τ • Z)ᵀ * U)ᵀ * ((X + τ • Z)ᵀ * U))⁻¹ *
      ((X + τ • Z)ᵀ * U)ᵀ) 0 := by
  have hL : ContDiffAt ℝ N (fun τ : ℝ => (X + τ • Z)ᵀ * U) 0 :=
    contDiffAt_mul (contDiffAt_transpose (contDiffAt_line X Z)) contDiffAt_const
  have h0 : IsUnit (S + (0 : ℝ) • M).det := by simpa using h.det
  have hdet := ((rep.smul 0).add_base h.eq).isUnit_L h.orthU h.orthV h0
  exact contDiffAt_mul (contDiffAt_inv (contDiffAt_mul (contDiffAt_transpose hL) hL) hdet)
    (contDiffAt_transpose hL)

lemma IsFactorization.contDiffAt_klsRem (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) : ContDiffAt ℝ N (klsRem U Up V Vp S M X Z) 0 := by
  have h1 := contDiffAt_mul (contDiffAt_mul (h.contDiffAt_K (N := N) rep)
    (contDiffAt_const (c := Upᵀ * Up))) (contDiffAt_inv_line h.det M)
  have h2 := contDiffAt_mul h1 (contDiffAt_mul (contDiffAt_const (c := Vpᵀ * Vp))
    (h.contDiffAt_L (N := N) rep))
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  simp only [klsRem, Matrix.mul_assoc]

lemma IsFactorization.contDiffAt_kslRem (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) : ContDiffAt ℝ N (kslRem Up V Vp S M X Z) 0 :=
  contDiffAt_mul (contDiffAt_mul (contDiffAt_mul (h.contDiffAt_K (N := N) rep)
    (contDiffAt_const (c := Upᵀ * Up))) (contDiffAt_inv_line h.det M)) contDiffAt_const

lemma IsFactorization.contDiffAt_orth (h : IsFactorization X U S V) :
    ContDiffAt ℝ N (fun τ : ℝ => orthRetr U V X (τ • Z)) 0 := by
  have hline : ContDiffAt ℝ N (fun τ : ℝ => (U, V, X, τ • Z)) 0 :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk (contDiffAt_const.prodMk
      (contDiffAt_id.smul contDiffAt_const)))
  have hA : IsUnit (Uᵀ * (X + (0 : ℝ) • Z) * V).det := by
    simpa [h.sandwich] using h.det
  exact (contDiffAt_orthRetr (N := N) hA).comp (0 : ℝ) hline

lemma IsFactorization.contDiffAt_kls (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) :
    ContDiffAt ℝ N (fun τ : ℝ => klsRetr U V X (τ • Z)) 0 := by
  have hline : ContDiffAt ℝ N (fun τ : ℝ => (U, V, X, τ • Z)) 0 :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk (contDiffAt_const.prodMk
      (contDiffAt_id.smul contDiffAt_const)))
  have h0 : IsUnit (S + (0 : ℝ) • M).det := by simpa using h.det
  have r0 := (rep.smul 0).add_base h.eq
  exact (contDiffAt_klsRetr (N := N) (r0.isUnit_K h.orthU h.orthV h0)
    (r0.isUnit_L h.orthU h.orthV h0)).comp (0 : ℝ) hline

lemma IsFactorization.contDiffAt_ksl (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) :
    ContDiffAt ℝ N (fun τ : ℝ => kslRetr V X (τ • Z)) 0 := by
  have hline : ContDiffAt ℝ N (fun τ : ℝ => (V, X, τ • Z)) 0 :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk (contDiffAt_id.smul contDiffAt_const))
  have h0 : IsUnit (S + (0 : ℝ) • M).det := by simpa using h.det
  have r0 := (rep.smul 0).add_base h.eq
  exact (contDiffAt_kslRetr (N := N) (r0.isUnit_K h.orthU h.orthV h0)).comp (0 : ℝ) hline

end

/-- The three properties of a curve `X + τ Z + τ² c(τ)` with `c(0) = U_p S⁻¹ V_pᵀ`. -/
lemma IsFactorization.curve_props (h : IsFactorization X U S V)
    (rep : IsTangentRep U V M Up Vp Z) {γ c : ℝ → Matrix m n ℝ} (hc : ContDiffAt ℝ 2 c 0)
    (hc0 : c 0 = Up * S⁻¹ * Vpᵀ) (he : ∀ᶠ τ in 𝓝 (0 : ℝ), γ τ = X + τ • Z + τ ^ 2 • c τ) :
    γ 0 = X ∧ HasDerivAt γ Z 0 ∧ tanProj X (deriv (deriv γ) 0) = 0 ∧
      ∀ᶠ τ in 𝓝 (0 : ℝ), IsUnit (Uᵀ * γ τ * V).det := by
  obtain ⟨h0, hvel, hacc⟩ := jet_of_expansion hc he
  refine ⟨h0, hvel, ?_, ?_⟩
  · rw [hacc, hc0, map_smul, h.tanProj_Up_mul_Vp rep, smul_zero]
  · have hcont : ContinuousAt (fun τ => Uᵀ * γ τ * V) 0 :=
      (Frobenius.hasDerivAt_mul_const V (Frobenius.hasDerivAt_const_mul Uᵀ hvel)).continuousAt
    refine eventually_isUnit_det hcont ?_
    simp only [h0, h.sandwich]
    exact h.det

/-- Packaging: a map whose curves at factorized points have the form of `curve_props` and which
factors through `ℝ^r` is a second-order retraction on `M_r`. -/
lemma isSecondOrder_of_curves {R : Matrix m n ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hR : ∀ (X : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), IsFactorization X U S V → ∀ Z ∈ tangentSpace X,
      ContDiffAt ℝ ∞ (fun τ : ℝ => R X (τ • Z)) 0 ∧
      (∀ τ : ℝ, ∃ (P : Matrix m (Fin r) ℝ) (Q : Matrix (Fin r) n ℝ), R X (τ • Z) = P * Q) ∧
      ∃ (M : Matrix (Fin r) (Fin r) ℝ) (Up : Matrix m (Fin r) ℝ) (Vp : Matrix n (Fin r) ℝ)
        (c : ℝ → Matrix m n ℝ), IsTangentRep U V M Up Vp Z ∧ ContDiffAt ℝ 2 c 0 ∧
        c 0 = Up * S⁻¹ * Vpᵀ ∧ ∀ᶠ τ in 𝓝 (0 : ℝ), R X (τ • Z) = X + τ • Z + τ ^ 2 • c τ) :
    IsSecondOrderRetraction (rankSet m n r) (fun X => (tangentSpace X : Set (Matrix m n ℝ)))
      (fun X q => tanProj X q) R := by
  have key : ∀ X ∈ rankSet m n r, ∀ v ∈ tangentSpace X,
      ContDiffAt ℝ ∞ (fun τ : ℝ => R X (τ • v)) 0 ∧
      R X ((0 : ℝ) • v) = X ∧ HasDerivAt (fun τ : ℝ => R X (τ • v)) v 0 ∧
      tanProj X (deriv (deriv fun τ : ℝ => R X (τ • v)) 0) = 0 ∧
      ∀ᶠ τ in 𝓝 (0 : ℝ), R X (τ • v) ∈ rankSet m n r := by
    intro X hX v hv
    obtain ⟨U, S, V, h⟩ := exists_factorization (r := r) hX
    obtain ⟨hsm, hfac, M, Up, Vp, c, rep, hc, hc0, he⟩ := hR X U S V h v hv
    obtain ⟨h0, hvel, hacc, hdet⟩ := h.curve_props rep hc hc0 he
    refine ⟨hsm, h0, hvel, hacc, ?_⟩
    filter_upwards [hdet] with τ hτ
    obtain ⟨P, Q, hPQ⟩ := hfac τ
    exact rank_eq_of_factor (C := Uᵀ) (D := V) hPQ hτ
  refine ⟨⟨fun X hX v hv => (key X hX v hv).2.2.2.2, fun X hX v hv => (key X hX v hv).1,
    fun X hX => ?_, fun X hX v hv => (key X hX v hv).2.2.1⟩,
    fun X hX v hv => (key X hX v hv).2.2.2.1⟩
  simpa using (key X hX 0 (Submodule.zero_mem _)).2.1

/-- **The orthographic retraction is a second-order retraction** (arXiv 2309.06125, §3.3.1, quoted
there from Absil–Malick 2012).  Proved directly: `R^ORTH_X(τ Z) = X + τ Z + τ² U_p (S + τ M)⁻¹ V_pᵀ`
has acceleration `2 U_p S⁻¹ V_pᵀ ∈ N_X M_r` at `τ = 0`.  "Second-order" is the definition of §2.1,
`σ̈(0) = Π(X) σ''(0) = 0` (`IsSecondOrderRetraction`); the equivalent characterization (21) by
`Exp` is not used.  The map is defined on all of `T M_r` by `retrORTH`. -/
theorem isSecondOrderRetraction_orth :
    IsSecondOrderRetraction (rankSet m n r) (fun X => (tangentSpace X : Set (Matrix m n ℝ)))
      (fun X q => tanProj X q) (retrORTH r) := by
  classical
  refine isSecondOrder_of_curves fun X U S V h Z hZ => ?_
  have rep := h.tangentRep hZ
  have e : (fun τ : ℝ => retrORTH r X (τ • Z)) = fun τ => orthRetr U V X (τ • Z) := by
    funext τ
    exact retrORTH_eq h _
  refine ⟨?_, fun τ => ?_, _, _, _, fun τ => (1 - U * Uᵀ) * Z * V * (S + τ • (Uᵀ * Z * V))⁻¹ *
    ((1 - V * Vᵀ) * Zᵀ * U)ᵀ, rep, ?_, by simp, ?_⟩
  · rw [e]
    exact h.contDiffAt_orth
  · exact ⟨_, _, (retrORTH_eq h _).trans (orthRetr_factor U V X _)⟩
  · exact contDiffAt_mul (contDiffAt_mul contDiffAt_const (contDiffAt_inv_line h.det _))
      contDiffAt_const
  · filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    rw [retrORTH_eq h, h.orthRetr_smul rep hτ]

/-- **Prop. 1 of arXiv 2309.06125: the KLS retraction is a second-order retraction.**  For every
`X ∈ M_r` and `Z ∈ T_X M_r` the curve `τ ↦ R^KLS_X(τ Z)` is smooth, lies on `M_r` for small `τ`,
starts at `X` with velocity `Z`, and has zero intrinsic acceleration `Π(X) σ''(0)` at `τ = 0`.

Differences from the paper: "second-order" is the definition of §2.1 (zero intrinsic acceleration,
which by (36) is the tangential part of the extrinsic one).  The paper instead uses the equivalent
characterization (21) by the exponential map, and the second-order property of `R^ORTH` from the
literature; here that property is proved (`isSecondOrderRetraction_orth`) and no geodesics occur.
The comparison with `R^ORTH` is sharper than the paper's `o(t³)`, see
`klsRetr_sub_orthRetr_isBigO`.  Joint smoothness in the factors is `contDiffAt_klsRetr`, and
independence of the factorization is `retrKLS_eq`. -/
theorem isSecondOrderRetraction_kls :
    IsSecondOrderRetraction (rankSet m n r) (fun X => (tangentSpace X : Set (Matrix m n ℝ)))
      (fun X q => tanProj X q) (retrKLS r) := by
  classical
  refine isSecondOrder_of_curves fun X U S V h Z hZ => ?_
  have rep := h.tangentRep hZ
  have e : (fun τ : ℝ => retrKLS r X (τ • Z)) = fun τ => klsRetr U V X (τ • Z) := by
    funext τ
    exact retrKLS_eq h _
  refine ⟨?_, fun τ => ?_, _, _, _, fun τ => (1 - U * Uᵀ) * Z * V * (S + τ • (Uᵀ * Z * V))⁻¹ *
    ((1 - V * Vᵀ) * Zᵀ * U)ᵀ - τ ^ 2 • klsRem U ((1 - U * Uᵀ) * Z * V) V
      ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z τ, rep, ?_, by simp, ?_⟩
  · rw [e]
    exact h.contDiffAt_kls rep
  · refine ⟨(X + τ • Z) * V, ((((X + τ • Z) * V)ᵀ * ((X + τ • Z) * V))⁻¹ * ((X + τ • Z) * V)ᵀ) *
      (X + τ • Z) * colProj ((X + τ • Z)ᵀ * U), ?_⟩
    rw [retrKLS_eq h, klsRetr, Matrix.colProj_def]
    simp only [Matrix.mul_assoc]
  · exact (contDiffAt_mul (contDiffAt_mul contDiffAt_const (contDiffAt_inv_line h.det _))
      contDiffAt_const).sub ((contDiffAt_id.pow 2).smul (h.contDiffAt_klsRem rep))
  · filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    rw [retrKLS_eq h, h.klsRetr_smul rep hτ, h.orthRetr_smul rep hτ, smul_sub, smul_smul,
      add_sub_assoc]
    congr 3
    ring

/-- **The KSL retraction is a second-order retraction** (arXiv 2309.06125, §3.2, quoted there from
Absil–Oseledets 2015, Thm 3.3).  Proved directly, as for `isSecondOrderRetraction_kls`. -/
theorem isSecondOrderRetraction_ksl :
    IsSecondOrderRetraction (rankSet m n r) (fun X => (tangentSpace X : Set (Matrix m n ℝ)))
      (fun X q => tanProj X q) (retrKSL r) := by
  classical
  refine isSecondOrder_of_curves fun X U S V h Z hZ => ?_
  have rep := h.tangentRep hZ
  have e : (fun τ : ℝ => retrKSL r X (τ • Z)) = fun τ => kslRetr V X (τ • Z) := by
    funext τ
    exact retrKSL_eq h _
  refine ⟨?_, fun τ => ?_, _, _, _, fun τ => (1 - U * Uᵀ) * Z * V * (S + τ • (Uᵀ * Z * V))⁻¹ *
    ((1 - V * Vᵀ) * Zᵀ * U)ᵀ - τ • kslRem ((1 - U * Uᵀ) * Z * V) V
      ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z τ, rep, ?_, by simp, ?_⟩
  · rw [e]
    exact h.contDiffAt_ksl rep
  · refine ⟨(X + τ • Z) * V, ((((X + τ • Z) * V)ᵀ * ((X + τ • Z) * V))⁻¹ * ((X + τ • Z) * V)ᵀ) *
      (X + τ • Z), ?_⟩
    rw [retrKSL_eq h, kslRetr, Matrix.colProj_def]
    simp only [Matrix.mul_assoc]
  · exact (contDiffAt_mul (contDiffAt_mul contDiffAt_const (contDiffAt_inv_line h.det _))
      contDiffAt_const).sub (contDiffAt_id.smul (h.contDiffAt_kslRem rep))
  · filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    rw [retrKSL_eq h, h.kslRetr_smul rep hτ, h.orthRetr_smul rep hτ, smul_sub, smul_smul,
      add_sub_assoc]
    congr 3

/-- **The KLS retraction agrees with the orthographic one to high order** (the core of the proof of
Prop. 1 of arXiv 2309.06125).  The paper shows `R^KLS_X(t Z) - R^ORTH_X(t Z) = o(t³)`; the exact
formula `klsRetr_eq` even gives `O(t⁴)`. -/
theorem klsRetr_sub_orthRetr_isBigO (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X) :
    (fun τ : ℝ => klsRetr U V X (τ • Z) - orthRetr U V X (τ • Z)) =O[𝓝 0] fun τ => τ ^ 4 := by
  classical
  have rep := h.tangentRep hZ
  have hrem := (h.contDiffAt_klsRem (N := 0) rep).continuousAt
  have hb : klsRem U ((1 - U * Uᵀ) * Z * V) V ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z
      =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hrem.tendsto.isBigO_one ℝ
  have hs := (Asymptotics.isBigO_refl (fun τ : ℝ => τ ^ 4) (𝓝 0)).smul hb
  simp only [smul_eq_mul, mul_one] at hs
  have hev : (fun τ : ℝ => klsRetr U V X (τ • Z) - orthRetr U V X (τ • Z)) =ᶠ[𝓝 0] fun τ =>
      -(τ ^ 4 • klsRem U ((1 - U * Uᵀ) * Z * V) V ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z
        τ) := by
    filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    rw [h.klsRetr_smul rep hτ]
    abel
  exact hs.neg_left.congr' hev.symm EventuallyEq.rfl

/-- The form stated in the proof of Prop. 1 of arXiv 2309.06125:
`R^KLS_X(t Z) = R^ORTH_X(t Z) + o(t³)`. -/
theorem klsRetr_sub_orthRetr_isLittleO (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X) :
    (fun τ : ℝ => klsRetr U V X (τ • Z) - orthRetr U V X (τ • Z)) =o[𝓝 0] fun τ => τ ^ 3 :=
  (klsRetr_sub_orthRetr_isBigO h hZ).trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num))

/-- `R^KSL_X(t Z) = R^ORTH_X(t Z) + O(t³)` (arXiv 2309.06125, §3.2: "coincides modulo third-order
terms with the orthographic retraction"). -/
theorem kslRetr_sub_orthRetr_isBigO (h : IsFactorization X U S V) (hZ : Z ∈ tangentSpace X) :
    (fun τ : ℝ => kslRetr V X (τ • Z) - orthRetr U V X (τ • Z)) =O[𝓝 0] fun τ => τ ^ 3 := by
  classical
  have rep := h.tangentRep hZ
  have hrem := (h.contDiffAt_kslRem (N := 0) rep).continuousAt
  have hb : kslRem ((1 - U * Uᵀ) * Z * V) V ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z
      =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hrem.tendsto.isBigO_one ℝ
  have hs := (Asymptotics.isBigO_refl (fun τ : ℝ => τ ^ 3) (𝓝 0)).smul hb
  simp only [smul_eq_mul, mul_one] at hs
  have hev : (fun τ : ℝ => kslRetr V X (τ • Z) - orthRetr U V X (τ • Z)) =ᶠ[𝓝 0] fun τ =>
      -(τ ^ 3 • kslRem ((1 - U * Uᵀ) * Z * V) V ((1 - V * Vᵀ) * Zᵀ * U) S (Uᵀ * Z * V) X Z
        τ) := by
    filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    rw [h.kslRetr_smul rep hτ]
    abel
  exact hs.neg_left.congr' hev.symm EventuallyEq.rfl

/-- **`R^KLS` maps a neighbourhood of `0` into `M_r`** (the first paragraph of the proof of Prop. 1
of arXiv 2309.06125): for all sufficiently small `Z`, tangent or not, `R^KLS_X(Z)` has rank `r`. -/
theorem eventually_rank_klsRetr (h : IsFactorization X U S V) :
    ∀ᶠ Z in 𝓝 (0 : Matrix m n ℝ), (klsRetr U V X Z).rank = r := by
  classical
  have hline : ContDiffAt ℝ 0 (fun Z : Matrix m n ℝ => (U, V, X, Z)) 0 :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have rep0 : IsTangentRep U V 0 0 0 (0 : Matrix m n ℝ) :=
    ⟨by simp, by simp, by simp⟩
  have h0 : IsUnit (S + (0 : Matrix (Fin r) (Fin r) ℝ)).det := by simpa using h.det
  have r0 := rep0.add_base h.eq
  have hf : ContDiffAt ℝ 0 (fun Z : Matrix m n ℝ => klsRetr U V X Z) 0 := by
    have hc := contDiffAt_klsRetr (N := 0) (r0.isUnit_K h.orthU h.orthV h0)
      (r0.isUnit_L h.orthU h.orthV h0)
    have hcomp := hc.comp (0 : Matrix m n ℝ) hline
    exact hcomp
  have hg : ContDiffAt ℝ 0 (fun Z : Matrix m n ℝ => Uᵀ * klsRetr U V X Z * V) 0 :=
    contDiffAt_mul (contDiffAt_mul contDiffAt_const hf) contDiffAt_const
  have hX : klsRetr U V X 0 = X := by
    rw [← retrKLS_eq (r := r) h 0]
    exact isSecondOrderRetraction_kls.zero X h.rank
  have hdet : IsUnit (Uᵀ * klsRetr U V X 0 * V).det := by
    rw [hX, h.sandwich]
    exact h.det
  filter_upwards [eventually_isUnit_det hg.continuousAt hdet] with Z hZ
  refine rank_eq_of_factor (C := Uᵀ) (D := V) (P := (X + Z) * V)
    (Q := ((((X + Z) * V)ᵀ * ((X + Z) * V))⁻¹ * ((X + Z) * V)ᵀ) * (X + Z) *
      colProj ((X + Z)ᵀ * U)) ?_ hZ
  rw [klsRetr, Matrix.colProj_def]
  simp only [Matrix.mul_assoc]

end Curves

/-! ### Abstract core of Props. 5 and 6: curves of orthogonal projectors -/

section ProjectorCurve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Pr` is a curve of orthogonal projectors, differentiable at `0` with derivative `D`.  This is
the abstract setting of Props. 5 and 6 of arXiv 2309.06125: `Pr t = Π(γ(t))` for a curve `γ` on an
embedded manifold, and `D = DΠ(x)[w]` with `x = γ(0)`, `w = γ'(0)`. -/
structure IsProjectorCurve (Pr : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) : Prop where
  hasDerivAt : HasDerivAt Pr D 0
  orth : ∀ᶠ t in 𝓝 (0 : ℝ), IsOrthProj (Pr t)

namespace IsProjectorCurve

variable {Pr : ℝ → E →L[ℝ] E} {D : E →L[ℝ] E}

lemma hasDerivAt_apply (hP : IsProjectorCurve Pr D) {G : ℝ → E} {G' : E} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t => Pr t (G t)) (D (G 0) + Pr 0 G') 0 :=
  hP.hasDerivAt.clm_apply hG

lemma hasDerivAt_fixed (hP : IsProjectorCurve Pr D) (x : E) :
    HasDerivAt (fun t => Pr t x) (D x) 0 := by
  simpa using hP.hasDerivAt_apply (hasDerivAt_const (0 : ℝ) x)

lemma orth_zero (hP : IsProjectorCurve Pr D) : IsOrthProj (Pr 0) := hP.orth.self_of_nhds

/-- The product rule applied to `Π² = Π`. -/
lemma leibniz (hP : IsProjectorCurve Pr D) (x : E) : D x = D (Pr 0 x) + Pr 0 (D x) := by
  have h1 := hP.hasDerivAt_apply (hP.hasDerivAt_fixed x)
  have h2 : (fun t => Pr t (Pr t x)) =ᶠ[𝓝 0] fun t => Pr t x := by
    filter_upwards [hP.orth] with t ht using ht.idem x
  exact ((hP.hasDerivAt_fixed x).congr_of_eventuallyEq h2).unique h1

/-- The derivative of a curve of symmetric operators is symmetric. -/
lemma symm (hP : IsProjectorCurve Pr D) (x y : E) : ⟪D x, y⟫ = ⟪x, D y⟫ := by
  have h1 : HasDerivAt (fun t => ⟪Pr t x, y⟫) ⟪D x, y⟫ 0 := by
    simpa using HasDerivAt.inner ℝ (hP.hasDerivAt_fixed x) (hasDerivAt_const (0 : ℝ) y)
  have h2 : HasDerivAt (fun t => ⟪x, Pr t y⟫) ⟪x, D y⟫ 0 := by
    simpa using HasDerivAt.inner ℝ (hasDerivAt_const (0 : ℝ) x) (hP.hasDerivAt_fixed y)
  have h3 : (fun t => ⟪Pr t x, y⟫) =ᶠ[𝓝 0] fun t => ⟪x, Pr t y⟫ := by
    filter_upwards [hP.orth] with t ht using ht.symm x y
  exact (h2.congr_of_eventuallyEq h3).unique h1 |>.symm

/-- `Π D Π = 0`. -/
lemma tan_deriv_tan (hP : IsProjectorCurve Pr D) (x : E) : Pr 0 (D (Pr 0 x)) = 0 := by
  have h := hP.leibniz (Pr 0 x)
  rw [hP.orth_zero.idem] at h
  simpa using h

/-- For a normal vector `n`, the vector `D n` is tangent. -/
lemma tan_deriv_normal (hP : IsProjectorCurve Pr D) {n : E} (hn : Pr 0 n = 0) :
    Pr 0 (D n) = D n := by
  have h := hP.leibniz n
  rw [hn, map_zero, zero_add] at h
  exact h.symm

/-- **Prop. 5 of arXiv 2309.06125 (Absil–Mahony–Trumpf 2013, Thm 1), abstract core.**  For a curve
of orthogonal projectors, normal `n` and any `q` with `Π⊥(0) q = n`:
`D n = Π D n = Π D Π⊥ q`, where `D = DΠ[w]`.  Together with `pairing` this says that `n ↦ D n` is
the Weingarten map of Definition 4.  The abstract form replaces the vector fields of the paper by
a curve of projectors. -/
theorem weingarten_eq (hP : IsProjectorCurve Pr D) {n q : E} (hq : q - Pr 0 q = n) :
    D n = Pr 0 (D n) ∧ Pr 0 (D n) = Pr 0 (D (q - Pr 0 q)) := by
  have hn : Pr 0 n = 0 := by
    rw [← hq, map_sub, hP.orth_zero.idem, sub_self]
  exact ⟨(hP.tan_deriv_normal hn).symm, by rw [hq]⟩

/-- **Definition 4 of arXiv 2309.06125, pointwise form (32).**  If `ζ` is a tangent vector field
along the curve, then `Π⊥ ζ'(0)` is the second fundamental form `II(w, ζ(0))` (Definition 3), and
for normal `n` one has `⟪n, II(w, ζ(0))⟫ = ⟪n, ζ'(0)⟫ = ⟪D n, ζ(0)⟫`. -/
theorem pairing (hP : IsProjectorCurve Pr D) {ζ : ℝ → E} {ζ' : E} (hζ : HasDerivAt ζ ζ' 0)
    (hfix : ∀ᶠ t in 𝓝 (0 : ℝ), Pr t (ζ t) = ζ t) {n : E} (hn : Pr 0 n = 0) :
    ⟪n, ζ' - Pr 0 ζ'⟫ = ⟪D n, ζ 0⟫ ∧ ⟪n, ζ'⟫ = ⟪D n, ζ 0⟫ := by
  have h1 := hP.hasDerivAt_apply hζ
  have h2 : ζ' = D (ζ 0) + Pr 0 ζ' := (hζ.congr_of_eventuallyEq hfix).unique h1
  have h3 : ⟪n, Pr 0 ζ'⟫ = 0 := by
    rw [← hP.orth_zero.symm, hn, inner_zero_left]
  have h4 : ⟪n, ζ'⟫ = ⟪D n, ζ 0⟫ := by
    calc ⟪n, ζ'⟫ = ⟪n, D (ζ 0) + Pr 0 ζ'⟫ := by rw [← h2]
      _ = ⟪n, D (ζ 0)⟫ := by rw [inner_add_right, h3, add_zero]
      _ = ⟪D n, ζ 0⟫ := (hP.symm n (ζ 0)).symm
  exact ⟨by rw [inner_sub_right, h3, sub_zero, h4], h4⟩

/-- **Prop. 6 of arXiv 2309.06125, abstract core**: the extrinsic product rule followed by
projection.  If `y' = Π(t) G(t)`, then `y'' = D G(0) + Π(0) G'(0)` at `0` and the tangential part
is `Π y'' = Π G'(0) + D (Π⊥ G(0))`. -/
theorem acceleration (hP : IsProjectorCurve Pr D) {G : ℝ → E} {G' : E} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t => Pr t (G t)) (D (G 0) + Pr 0 G') 0 ∧
      Pr 0 (D (G 0) + Pr 0 G') = Pr 0 G' + D (G 0 - Pr 0 (G 0)) := by
  refine ⟨hP.hasDerivAt_apply hG, ?_⟩
  have hn : Pr 0 (G 0 - Pr 0 (G 0)) = 0 := by rw [map_sub, hP.orth_zero.idem, sub_self]
  have e : D (G 0) = D (Pr 0 (G 0)) + D (G 0 - Pr 0 (G 0)) := by
    rw [← map_add, add_sub_cancel]
  rw [map_add, hP.orth_zero.idem, e, map_add, hP.tan_deriv_tan, zero_add,
    hP.tan_deriv_normal hn, add_comm]

end IsProjectorCurve

end ProjectorCurve

/-! ### The derivative of the tangent projector along curves on `M_r` -/

section Derivative

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {X : Matrix m n ℝ} {U U' Up : Matrix m (Fin r) ℝ} {V V' Vp : Matrix n (Fin r) ℝ}
  {S S' M : Matrix (Fin r) (Fin r) ℝ} {Y : ℝ → Matrix m n ℝ} {T : Matrix m n ℝ}

lemma hasDerivAt_colP {A : ℝ → Matrix m (Fin r) ℝ} {A' : Matrix m (Fin r) ℝ}
    (hA : HasDerivAt A A' 0) (hdet : IsUnit ((A 0)ᵀ * A 0).det) :
    ∃ P', HasDerivAt (fun t => colProj (A t)) P' 0 := by
  have hAt := Frobenius.hasDerivAt_transpose hA
  have hinv := hasDerivAt_matInv (Frobenius.hasDerivAt_mul hAt hA) hdet
  simp only [Matrix.colProj_def]
  exact ⟨_, Frobenius.hasDerivAt_mul (Frobenius.hasDerivAt_mul hA hinv) hAt⟩

/-- `(1 - U Uᵀ) T V S⁻¹ Uᵀ` plus its transpose: the derivative of the orthogonal projector onto the
range along a curve through `U S Vᵀ` with velocity `T`, see `deriv_range_proj`. -/
noncomputable def dColP [DecidableEq m] (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ) (T : Matrix m n ℝ) : Matrix m m ℝ :=
  (1 - U * Uᵀ) * T * V * S⁻¹ * Uᵀ + ((1 - U * Uᵀ) * T * V * S⁻¹ * Uᵀ)ᵀ

/-- The derivative of a differentiable family of orthogonal projectors `P t` with `P t Y t = Y t`
is determined by the velocity of `Y`. -/
lemma deriv_range_proj [DecidableEq m] {P : ℝ → Matrix m m ℝ} {P' : Matrix m m ℝ}
    (hP : HasDerivAt P P' 0) (hsym : ∀ᶠ t in 𝓝 (0 : ℝ), (P t)ᵀ = P t)
    (hidem : ∀ᶠ t in 𝓝 (0 : ℝ), P t * P t = P t) (hfix : ∀ᶠ t in 𝓝 (0 : ℝ), P t * Y t = Y t)
    (hY : HasDerivAt Y T 0) (h : IsFactorization (Y 0) U S V) (hP0 : P 0 = U * Uᵀ) :
    P' = dColP U S V T ∧ P' * Y 0 = (1 - U * Uᵀ) * T := by
  have e1 : P'ᵀ = P' := by
    have h1 := Frobenius.hasDerivAt_transpose hP
    have h2 : P =ᶠ[𝓝 0] fun t => (P t)ᵀ := by
      filter_upwards [hsym] with t ht using ht.symm
    exact (h1.congr_of_eventuallyEq h2).unique hP
  have e2 : P' * (U * Uᵀ) + U * Uᵀ * P' = P' := by
    have h1 := Frobenius.hasDerivAt_mul hP hP
    have h2 : P =ᶠ[𝓝 0] fun t => P t * P t := by
      filter_upwards [hidem] with t ht using ht.symm
    have h3 := (h1.congr_of_eventuallyEq h2).unique hP
    rwa [hP0] at h3
  have e3 : P' * Y 0 = (1 - U * Uᵀ) * T := by
    have h1 := Frobenius.hasDerivAt_mul hP hY
    have h2 : Y =ᶠ[𝓝 0] fun t => P t * Y t := by
      filter_upwards [hfix] with t ht using ht.symm
    have h3 := (h1.congr_of_eventuallyEq h2).unique hY
    rw [hP0] at h3
    rw [Matrix.sub_mul, Matrix.one_mul, eq_sub_iff_add_eq, h3]
  refine ⟨?_, e3⟩
  have e4 : P' * (U * Uᵀ) = (1 - U * Uᵀ) * T * V * S⁻¹ * Uᵀ := by
    have key : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := by
      calc U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * (S * ((Vᵀ * V) * S⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
        _ = U * Uᵀ := by
            rw [h.orthV, Matrix.one_mul, Matrix.mul_nonsing_inv _ h.det, Matrix.mul_one]
    calc P' * (U * Uᵀ) = P' * (U * S * Vᵀ * (V * S⁻¹ * Uᵀ)) := by rw [key]
      _ = P' * Y 0 * (V * S⁻¹ * Uᵀ) := by
          rw [h.eq]
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [e3]
          simp only [Matrix.mul_assoc]
  have e5 : U * Uᵀ * P' = ((1 - U * Uᵀ) * T * V * S⁻¹ * Uᵀ)ᵀ := by
    rw [← e4, Matrix.transpose_mul, e1, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc P' = P' * (U * Uᵀ) + U * Uᵀ * P' := e2.symm
    _ = dColP U S V T := by rw [e4, e5, dColP]

lemma colP_mul_of_rank {W : Matrix m n ℝ} (hW : W.rank ≤ r) (hB : IsUnit (Uᵀ * W * V).det) :
    colProj (W * V) * W = W := by
  have hsk := skeleton (C := Uᵀ) (D := V) hW hB
  have hK : IsUnit ((W * V)ᵀ * (W * V)).det :=
    isUnit_det_transpose_mul_self (W := Uᵀ) (by rwa [← Matrix.mul_assoc])
  have e : (W * V) * ((Uᵀ * W * V)⁻¹ * Uᵀ * W) = W := by
    conv_rhs => rw [← hsk]
    simp only [Matrix.mul_assoc]
  calc colProj (W * V) * W = colProj (W * V) * ((W * V) * ((Uᵀ * W * V)⁻¹ * Uᵀ * W)) := by rw [e]
    _ = (W * V) * ((Uᵀ * W * V)⁻¹ * Uᵀ * W) := by
        rw [← Matrix.mul_assoc, colP_mul_self hK]
    _ = W := e

lemma IsFactorization.colP_eq {W : Matrix m n ℝ} (h' : IsFactorization W U' S' V')
    {C : Matrix (Fin r) m ℝ} {D : Matrix n (Fin r) ℝ} (hB : IsUnit (C * W * D).det) :
    colProj (W * D) = U' * U'ᵀ := by
  have hG : W * D = U' * (S' * V'ᵀ * D) := by
    rw [h'.eq]
    simp only [Matrix.mul_assoc]
  have hu : IsUnit (S' * V'ᵀ * D).det := by
    have e : C * W * D = (C * U') * (S' * V'ᵀ * D) := by
      rw [Matrix.mul_assoc, hG]
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.det_mul] at hB
    exact isUnit_of_mul_isUnit_right hB
  exact colP_of_qr h'.orthU hu hG

/-- Left multiplication `q ↦ P q` as a continuous linear map. -/
noncomputable abbrev lm (P : Matrix m m ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  Frobenius.mulCLM P

/-- Right multiplication `q ↦ q Q` as a continuous linear map. -/
noncomputable abbrev rm (Q : Matrix n n ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  (Frobenius.mulCLM (m := m) (l := n) (n := n)).flip Q

/-- Near a factorized point, `Π` is given by the two projectors `colProj (W V)`,
`colProj (Wᵀ U)`, which depend differentiably on `W`. -/
lemma tanProj_eq_tangent {W : Matrix m n ℝ} (hrank : W.rank = r)
    (hB : IsUnit (Uᵀ * W * V).det) :
    tanProj W = tangent (lm (colProj (W * V))) (rm (colProj (Wᵀ * U))) := by
  obtain ⟨U', S', V', h'⟩ := exists_factorization (r := r) hrank
  have h1 : colProj (W * V) = U' * U'ᵀ := h'.colP_eq (C := Uᵀ) hB
  have hB' : IsUnit (Vᵀ * Wᵀ * U).det := by
    have e : Vᵀ * Wᵀ * U = (Uᵀ * W * V)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [e, Matrix.det_transpose]
    exact hB
  have h2 : colProj (Wᵀ * U) = V' * V'ᵀ := h'.transpose.colP_eq (C := Vᵀ) hB'
  rw [h'.tanProj_eq, h1, h2]
  refine ContinuousLinearMap.ext fun q => ?_
  rw [tangentProj_apply, tangent_apply]
  simp only [lm, rm, Frobenius.mulCLM_apply, ContinuousLinearMap.flip_apply, Matrix.mul_assoc]

/-- The derivative of the left projector of `Y t` along a curve on `M_r`. -/
lemma deriv_left [DecidableEq m] (h : IsFactorization (Y 0) U S V)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r) (hY : HasDerivAt Y T 0) :
    HasDerivAt (fun t => colProj (Y t * V)) (dColP U S V T) 0 ∧
      dColP U S V T * Y 0 = (1 - U * Uᵀ) * T := by
  have hcomp : ContinuousAt (fun t => Uᵀ * Y t * V) 0 :=
    (Frobenius.hasDerivAt_mul_const V (Frobenius.hasDerivAt_const_mul Uᵀ hY)).continuousAt
  have hB0 : IsUnit (Uᵀ * Y 0 * V).det := by
    rw [h.sandwich]
    exact h.det
  have hB := eventually_isUnit_det hcomp hB0
  have hK := Frobenius.hasDerivAt_mul_const V hY
  have hunit : ∀ {W : Matrix m n ℝ}, IsUnit (Uᵀ * W * V).det →
      IsUnit ((W * V)ᵀ * (W * V)).det := fun hb =>
    isUnit_det_transpose_mul_self (W := Uᵀ) (by rwa [← Matrix.mul_assoc])
  obtain ⟨P', hP'⟩ := hasDerivAt_colP hK (hunit hB0)
  have hP0 : colProj (Y 0 * V) = U * Uᵀ := h.colP_eq (C := Uᵀ) hB0
  have hd := deriv_range_proj hP' (Eventually.of_forall fun t => colP_transpose _)
    (hB.mono fun t ht => colP_idem (hunit ht))
    ((hB.and hrank).mono fun t ht => colP_mul_of_rank (le_of_eq ht.2) ht.1) hY h hP0
  rw [← hd.1]
  exact ⟨hP', hd.2⟩

/-- The operator `DΠ(X)[T]` at `X = U S Vᵀ`. -/
noncomputable def dTanProj [DecidableEq m] [DecidableEq n] (U : Matrix m (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (T : Matrix m n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  lm (dColP U S V T) + rm (dColP V Sᵀ U Tᵀ) -
    ((lm (dColP U S V T)).comp (rm (V * Vᵀ)) + (lm (U * Uᵀ)).comp (rm (dColP V Sᵀ U Tᵀ)))

/-- **Along any curve on `M_r` that is differentiable at `0`, `t ↦ Π(Y t)` is differentiable at
`0`.**  No differentiable factorization of the curve is assumed.  This is what gives the symbol
`DΠ(Y)[T]` of arXiv 2309.06125 a meaning. -/
theorem isProjectorCurve_tanProj [DecidableEq m] [DecidableEq n]
    (h : IsFactorization (Y 0) U S V) (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r)
    (hY : HasDerivAt Y T 0) :
    IsProjectorCurve (fun t => tanProj (Y t)) (dTanProj U S V T) := by
  have hcomp : ContinuousAt (fun t => Uᵀ * Y t * V) 0 :=
    (Frobenius.hasDerivAt_mul_const V (Frobenius.hasDerivAt_const_mul Uᵀ hY)).continuousAt
  have hB0 : IsUnit (Uᵀ * Y 0 * V).det := by
    rw [h.sandwich]
    exact h.det
  have hB := eventually_isUnit_det hcomp hB0
  have hL := deriv_left (Y := fun t => (Y t)ᵀ) (T := Tᵀ) h.transpose
    (hrank.mono fun t ht => by rwa [Matrix.rank_transpose]) (Frobenius.hasDerivAt_transpose hY)
  have hR := deriv_left h hrank hY
  have hP0 : colProj (Y 0 * V) = U * Uᵀ := h.colP_eq (C := Uᵀ) hB0
  have hB0' : IsUnit (Vᵀ * (Y 0)ᵀ * U).det := by
    rw [h.transpose.sandwich]
    exact h.transpose.det
  have hQ0 : colProj ((Y 0)ᵀ * U) = V * Vᵀ := h.transpose.colP_eq (C := Vᵀ) hB0'
  have hLm : HasDerivAt (fun t => lm (n := n) (colProj (Y t * V))) (lm (dColP U S V T)) 0 :=
    (Frobenius.mulCLM (m := m) (l := m) (n := n)).hasFDerivAt.comp_hasDerivAt 0 hR.1
  have hRm : HasDerivAt (fun t => rm (m := m) (colProj ((Y t)ᵀ * U))) (rm (dColP V Sᵀ U Tᵀ)) 0 :=
    ((Frobenius.mulCLM (m := m) (l := n) (n := n)).flip).hasFDerivAt.comp_hasDerivAt 0 hL.1
  have hprod := hLm.clm_comp hRm
  have htan := (hLm.add hRm).sub hprod
  have hev : (fun t => tanProj (Y t)) =ᶠ[𝓝 0] fun t =>
      lm (colProj (Y t * V)) + rm (colProj ((Y t)ᵀ * U)) -
        (lm (colProj (Y t * V))).comp (rm (colProj ((Y t)ᵀ * U))) := by
    filter_upwards [hB, hrank] with t hb hr
    rw [tanProj_eq_tangent hr hb]
    rfl
  have hfin := htan.congr_of_eventuallyEq hev
  rw [hP0, hQ0] at hfin
  exact ⟨hfin, Eventually.of_forall fun t => isOrthProj_tanProj _⟩

/-- **The velocity of a curve on `M_r` is tangent** (the definition of `T_x M` in
arXiv 2309.06125, §2.1, one inclusion). -/
theorem velocity_mem_tangentSpace (h : IsFactorization (Y 0) U S V)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r) (hY : HasDerivAt Y T 0) :
    T ∈ tangentSpace (Y 0) := by
  classical
  have hd := (deriv_left h hrank hY).2
  have hX : Y 0 * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h.eq]
    have : U * S * Vᵀ * (V * Vᵀ) = U * S * Vᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V, h.orthV, Matrix.one_mul]
    rw [this, sub_self]
  have e : (1 - U * Uᵀ) * T * (1 - V * Vᵀ) = 0 := by
    rw [← hd, Matrix.mul_assoc, hX, Matrix.mul_zero]
  rw [h.mem_tangentSpace_iff]
  have := tangentProj_add_normal U V T
  rwa [e, add_zero] at this

/-- **The tangent space consists exactly of the velocities of curves on `M_r`**
(arXiv 2309.06125, §2.1).  This justifies the algebraic definition `tangentSpace`. -/
theorem mem_tangentSpace_iff_velocity (hX : X.rank = r) (Z : Matrix m n ℝ) :
    Z ∈ tangentSpace X ↔ ∃ γ : ℝ → Matrix m n ℝ, γ 0 = X ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), (γ t).rank = r) ∧ HasDerivAt γ Z 0 := by
  constructor
  · intro hZ
    have hR := isSecondOrderRetraction_orth (m := m) (n := n) (r := r)
    refine ⟨fun τ => retrORTH r X (τ • Z), ?_, hR.mem X hX Z hZ, hR.velocity X hX Z hZ⟩
    simpa using hR.zero X hX
  · rintro ⟨γ, rfl, hrank, hγ⟩
    obtain ⟨U, S, V, h⟩ := exists_factorization (r := r) hX
    exact velocity_mem_tangentSpace h hrank hγ

end Derivative

/-! ### Prop. 5: the Weingarten map of `M_r` -/

section Weingarten

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {X : Matrix m n ℝ} {U Up : Matrix m (Fin r) ℝ} {V Vp : Matrix n (Fin r) ℝ}
  {S M : Matrix (Fin r) (Fin r) ℝ} {Y : ℝ → Matrix m n ℝ} {T N q : Matrix m n ℝ}

/-- The Weingarten map of `M_r` at `X = U S Vᵀ`, as in eq. (34) of arXiv 2309.06125, with
`U_p = (1 - U Uᵀ) T V`, `V_p = (1 - V Vᵀ) Tᵀ U`.  For diagonal `S` the matrix `(S⁻¹)ᵀ` is `S⁻¹`
(`weingarten_diagonal`). -/
noncomputable def weingarten [DecidableEq m] [DecidableEq n] (U : Matrix m (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (T N : Matrix m n ℝ) :
    Matrix m n ℝ :=
  N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ * Vᵀ + U * (S⁻¹)ᵀ * ((1 - U * Uᵀ) * T * V)ᵀ * N

variable [DecidableEq m] [DecidableEq n]

/-- **Eq. (34) of arXiv 2309.06125**: for `T = U M Vᵀ + U_p Vᵀ + U V_pᵀ`,
`W_X(T, N) = N V_p S⁻ᵀ Vᵀ + U S⁻ᵀ U_pᵀ N`. -/
theorem weingarten_of_rep (rep : IsTangentRep U V M Up Vp T) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (N : Matrix m n ℝ) :
    weingarten U S V T N = N * Vp * (S⁻¹)ᵀ * Vᵀ + U * (S⁻¹)ᵀ * Upᵀ * N := by
  have e1 : (1 - U * Uᵀ) * T * V = Up := by
    rw [Matrix.mul_assoc, rep.mul_right hV, Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc U Uᵀ (U * M), ← Matrix.mul_assoc Uᵀ U M, hU,
      Matrix.one_mul, Matrix.mul_assoc U Uᵀ Up, rep.gaugeU, Matrix.mul_zero]
    simp
  have e2 : (1 - V * Vᵀ) * Tᵀ * U = Vp := by
    rw [Matrix.mul_assoc, rep.transpose_mul hU, Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc V Vᵀ (V * Mᵀ), ← Matrix.mul_assoc Vᵀ V Mᵀ,
      hV, Matrix.one_mul, Matrix.mul_assoc V Vᵀ Vp, rep.gaugeV, Matrix.mul_zero]
    simp
  rw [weingarten, e1, e2]

/-- **Eq. (34) of arXiv 2309.06125, verbatim** for `S = diag(σ)`:
`W_X(T, N) = N V_p S⁻¹ Vᵀ + U S⁻¹ U_pᵀ N`. -/
theorem weingarten_diagonal (rep : IsTangentRep U V M Up Vp T) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (σ : Fin r → ℝ) (N : Matrix m n ℝ) :
    weingarten U (Matrix.diagonal σ) V T N =
      N * Vp * (Matrix.diagonal σ)⁻¹ * Vᵀ + U * (Matrix.diagonal σ)⁻¹ * Upᵀ * N := by
  rw [weingarten_of_rep rep hU hV, Matrix.transpose_nonsing_inv, Matrix.diagonal_transpose]

/-- `DΠ(X)[T]` acts on normal vectors as the Weingarten map. -/
lemma dTanProj_normal (h : IsFactorization X U S V) (hN : tanProj X N = 0)
    (T : Matrix m n ℝ) : dTanProj U S V T N = weingarten U S V T N := by
  have hV0 := h.normal_mul_V hN
  have hU0 := h.Ut_mul_normal hN
  set C := (1 - U * Uᵀ) * T * V with hC
  set C' := (1 - V * Vᵀ) * Tᵀ * U with hC'
  have e1 : dColP U S V T * N = U * (S⁻¹)ᵀ * Cᵀ * N := by
    rw [dColP, ← hC, Matrix.add_mul, Matrix.mul_assoc _ Uᵀ N, hU0, Matrix.mul_zero, zero_add]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e2 : N * dColP V Sᵀ U Tᵀ = N * C' * (S⁻¹)ᵀ * Vᵀ := by
    have e2b : N * ((1 - V * Vᵀ) * Tᵀ * U * Sᵀ⁻¹ * Vᵀ)ᵀ = 0 := by
      rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.transpose_transpose, hV0,
        Matrix.zero_mul]
    rw [dColP, Matrix.mul_add, e2b, add_zero, Matrix.transpose_nonsing_inv]
    simp only [hC', Matrix.mul_assoc]
  have e3 : dColP U S V T * (N * (V * Vᵀ)) = 0 := by
    rw [← Matrix.mul_assoc N, hV0, Matrix.zero_mul, Matrix.mul_zero]
  have e4 : U * Uᵀ * (N * dColP V Sᵀ U Tᵀ) = 0 := by
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc Uᵀ, hU0, Matrix.zero_mul, Matrix.mul_zero]
  have e5 : dTanProj U S V T N = dColP U S V T * N + N * dColP V Sᵀ U Tᵀ -
      (dColP U S V T * (N * (V * Vᵀ)) + U * Uᵀ * (N * dColP V Sᵀ U Tᵀ)) := rfl
  rw [e5, e3, e4, e1, e2, weingarten, ← hC, ← hC']
  simp only [add_zero, sub_zero]
  abel

/-- **Prop. 5 of arXiv 2309.06125 for `M_r`, eqs. (33)-(34).**  Let `Y` be a curve on `M_r`,
differentiable at `0`, through `Y 0 = U S Vᵀ` with velocity `T`, and let `N = Π⊥(Y 0) q`.  Then
`DΠ(Y 0)[T] N = d/dt Π(Y t) N |₀` exists and equals the matrix `W_{Y 0}(T, N)` of (34), this matrix
is tangent, and it equals `Π DΠ[T] Π⊥ q`.  The paper's vector fields are replaced by the curve `Y`
(`DΠ` is only defined along `M_r`).  The defining relation of Definition 4 is
`pairing_weingarten`. -/
theorem weingarten_eq_deriv (h : IsFactorization (Y 0) U S V)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r) (hY : HasDerivAt Y T 0)
    (hq : q - tanProj (Y 0) q = N) :
    HasDerivAt (fun t => tanProj (Y t) N) (weingarten U S V T N) 0 ∧
      tanProj (Y 0) (weingarten U S V T N) = weingarten U S V T N ∧
      weingarten U S V T N = tanProj (Y 0) (dTanProj U S V T (q - tanProj (Y 0) q)) := by
  have hP := isProjectorCurve_tanProj h hrank hY
  have hn : tanProj (Y 0) N = 0 := by
    rw [← hq, map_sub, (isOrthProj_tanProj _).idem, sub_self]
  have e := dTanProj_normal h hn T
  obtain ⟨h1, -⟩ := hP.weingarten_eq hq
  refine ⟨e ▸ hP.hasDerivAt_fixed N, ?_, ?_⟩
  · rw [← e]
    exact h1.symm
  · rw [hq, ← e]
    exact h1

/-- **Definition 4 of arXiv 2309.06125 for `M_r`, pointwise form (32).**  If `ζ` is a tangent vector
field along a curve `Y` on `M_r` with velocity `T`, then for normal `N` the second fundamental form
`II(T, ζ(0)) = Π⊥ ζ'(0)` of Definition 3 satisfies `⟪N, II(T, ζ(0))⟫ = ⟪W(T, N), ζ(0)⟫`. -/
theorem pairing_weingarten (h : IsFactorization (Y 0) U S V)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r) (hY : HasDerivAt Y T 0)
    {ζ : ℝ → Matrix m n ℝ} {ζ' : Matrix m n ℝ} (hζ : HasDerivAt ζ ζ' 0)
    (hmem : ∀ᶠ t in 𝓝 (0 : ℝ), ζ t ∈ tangentSpace (Y t)) (hN : tanProj (Y 0) N = 0) :
    ⟪N, ζ' - tanProj (Y 0) ζ'⟫ = ⟪weingarten U S V T N, ζ 0⟫ := by
  have hP := isProjectorCurve_tanProj h hrank hY
  rw [← dTanProj_normal h hN T]
  exact (hP.pairing hζ (hmem.mono fun t ht => tanProj_eq_self_iff.2 ht) hN).1

/-- **A quantitative form of the remark after (34) of arXiv 2309.06125**:
`‖W_X(T, N)‖ ≤ 2 ‖T‖ ‖N‖ / σ_r`, in the Frobenius norm, where `ρ` is a lower bound for the singular
values of `S`; for diagonal `S` this hypothesis is `LeanDLRA.Curvature.diagonal_bounded_below`, see
`norm_weingarten_le_diagonal`.  It holds for all `T`, `N`, not only tangent and normal ones.  The
paper states no bound; it only remarks that the curvature grows unbounded as `σ_r(Y) → 0`. -/
theorem norm_weingarten_le (h : IsFactorization X U S V) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    (T N : Matrix m n ℝ) : ‖weingarten U S V T N‖ ≤ 2 * ‖T‖ * ‖N‖ / ρ := by
  have hSi : specNorm S⁻¹ ≤ ρ⁻¹ := specNorm_inv_le hρ hS
  have hSit : specNorm (S⁻¹)ᵀ ≤ ρ⁻¹ := by rwa [specNorm_transpose]
  have hUn : specNorm U ≤ 1 := specNorm_le_one_of_orthonormal h.orthU
  have hVn : specNorm V ≤ 1 := specNorm_le_one_of_orthonormal h.orthV
  have hVt : specNorm Vᵀ ≤ 1 := by rwa [specNorm_transpose]
  have hPU := (isOrthProjMat_mul_transpose h.orthU).compl
  have hPV := (isOrthProjMat_mul_transpose h.orthV).compl
  have hC : ‖(1 - U * Uᵀ) * T * V‖ ≤ ‖T‖ := by
    rw [Matrix.mul_assoc]
    calc ‖(1 - U * Uᵀ) * (T * V)‖ ≤ ‖T * V‖ := hPU.norm_mul_le _
      _ ≤ ‖T‖ * specNorm V := frob_mul_le' _ _
      _ ≤ ‖T‖ * 1 := by gcongr
      _ = ‖T‖ := mul_one _
  have hC' : ‖(1 - V * Vᵀ) * Tᵀ * U‖ ≤ ‖T‖ := by
    rw [Matrix.mul_assoc]
    calc ‖(1 - V * Vᵀ) * (Tᵀ * U)‖ ≤ ‖Tᵀ * U‖ := hPV.norm_mul_le _
      _ ≤ ‖Tᵀ‖ * specNorm U := frob_mul_le' _ _
      _ ≤ ‖Tᵀ‖ * 1 := by gcongr
      _ = ‖T‖ := by rw [mul_one, Frobenius.norm_transpose]
  have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have h1 : ‖N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ * Vᵀ‖ ≤ ‖T‖ * ‖N‖ * ρ⁻¹ := by
    calc ‖N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ * Vᵀ‖
        ≤ ‖N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ‖ * specNorm Vᵀ := frob_mul_le' _ _
      _ ≤ ‖N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ‖ * 1 := by gcongr
      _ = ‖N * ((1 - V * Vᵀ) * Tᵀ * U) * (S⁻¹)ᵀ‖ := mul_one _
      _ ≤ ‖N * ((1 - V * Vᵀ) * Tᵀ * U)‖ * specNorm (S⁻¹)ᵀ := frob_mul_le' _ _
      _ ≤ ‖N * ((1 - V * Vᵀ) * Tᵀ * U)‖ * ρ⁻¹ := by gcongr
      _ ≤ ‖N‖ * ‖(1 - V * Vᵀ) * Tᵀ * U‖ * ρ⁻¹ := by
          gcongr
          exact Frobenius.norm_mul_le _ _
      _ ≤ ‖N‖ * ‖T‖ * ρ⁻¹ := by gcongr
      _ = ‖T‖ * ‖N‖ * ρ⁻¹ := by ring
  have h2 : ‖U * (S⁻¹)ᵀ * ((1 - U * Uᵀ) * T * V)ᵀ * N‖ ≤ ‖T‖ * ‖N‖ * ρ⁻¹ := by
    have hsp : specNorm (U * (S⁻¹)ᵀ) ≤ ρ⁻¹ := by
      calc specNorm (U * (S⁻¹)ᵀ) ≤ specNorm U * specNorm (S⁻¹)ᵀ := specNorm_mul_le _ _
        _ ≤ 1 * ρ⁻¹ := by
            have := specNorm_nonneg (S⁻¹)ᵀ
            gcongr
        _ = ρ⁻¹ := one_mul _
    calc ‖U * (S⁻¹)ᵀ * ((1 - U * Uᵀ) * T * V)ᵀ * N‖
        = ‖U * (S⁻¹)ᵀ * (((1 - U * Uᵀ) * T * V)ᵀ * N)‖ := by rw [Matrix.mul_assoc]
      _ ≤ specNorm (U * (S⁻¹)ᵀ) * ‖((1 - U * Uᵀ) * T * V)ᵀ * N‖ := frob_mul_le _ _
      _ ≤ ρ⁻¹ * ‖((1 - U * Uᵀ) * T * V)ᵀ * N‖ := by gcongr
      _ ≤ ρ⁻¹ * (‖((1 - U * Uᵀ) * T * V)ᵀ‖ * ‖N‖) := by
          gcongr
          exact Frobenius.norm_mul_le _ _
      _ ≤ ρ⁻¹ * (‖T‖ * ‖N‖) := by
          rw [Frobenius.norm_transpose]
          gcongr
      _ = ‖T‖ * ‖N‖ * ρ⁻¹ := by ring
  calc ‖weingarten U S V T N‖ ≤ ‖T‖ * ‖N‖ * ρ⁻¹ + ‖T‖ * ‖N‖ * ρ⁻¹ :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * ‖T‖ * ‖N‖ / ρ := by
        rw [div_eq_mul_inv]
        ring

/-- The bound of `norm_weingarten_le` (not stated in arXiv 2309.06125, see there) for an SVD
`X = U diag(σ) Vᵀ` with `σ_r = ρ ≤ σᵢ`.  Such a decomposition exists for every `X` of rank `r` by
`LeanDLRA.SVD.exists_svd_bounded_below`. -/
theorem norm_weingarten_le_diagonal {σ : Fin r → ℝ}
    (h : IsFactorization X U (Matrix.diagonal σ) V) {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, ρ ≤ σ i)
    (T N : Matrix m n ℝ) :
    ‖weingarten U (Matrix.diagonal σ) V T N‖ ≤ 2 * ‖T‖ * ‖N‖ / ρ :=
  norm_weingarten_le h hρ (diagonal_bounded_below hρ.le hσ) T N

end Weingarten

/-! ### Prop. 6 and the local error of retraction schemes for DLRA -/

section DLRA

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {X : Matrix m n ℝ} {U Up : Matrix m (Fin r) ℝ} {V Vp : Matrix n (Fin r) ℝ}
  {S M : Matrix (Fin r) (Fin r) ℝ} {Y : ℝ → Matrix m n ℝ} {F : Matrix m n ℝ → Matrix m n ℝ}

/-- **Prop. 6 of arXiv 2309.06125, eq. (35).**  Let `Y` solve `Y' = Π(Y) F(Y)` near `t = 0` on `M_r`
and let `F` be differentiable at `Y(0) = U S Vᵀ`.  Then `Y'` is differentiable at `0`, and the
intrinsic acceleration `Ÿ = Π(Y) Y''` (eq. (36)) is
`Ÿ = Π(Y) DF(Y)[Π(Y) F(Y)] + W_Y(Π(Y) F(Y), Π⊥(Y) F(Y))`.
The paper assumes `F` and `Y` smooth; here `F` is differentiable at the point, and neither second
derivatives of `Y` nor a differentiable factorization are assumed.  The statement is at `t = 0`,
which loses nothing because the time origin is arbitrary. -/
theorem dlra_acceleration [DecidableEq m] [DecidableEq n] (h : IsFactorization (Y 0) U S V)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r)
    (hode : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt Y (tanProj (Y t) (F (Y t))) t)
    {DF : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hF : HasFDerivAt F DF (Y 0)) :
    DifferentiableAt ℝ (deriv Y) 0 ∧
      tanProj (Y 0) (deriv (deriv Y) 0) =
        tanProj (Y 0) (DF (tanProj (Y 0) (F (Y 0)))) +
          weingarten U S V (tanProj (Y 0) (F (Y 0))) (F (Y 0) - tanProj (Y 0) (F (Y 0))) := by
  set T := tanProj (Y 0) (F (Y 0)) with hT
  have hY0 : HasDerivAt Y T 0 := hode.self_of_nhds
  have hG : HasDerivAt (fun t => F (Y t)) (DF T) 0 := hF.comp_hasDerivAt 0 hY0
  have hP := isProjectorCurve_tanProj h hrank hY0
  obtain ⟨h1, h2⟩ := hP.acceleration hG
  have hd : deriv Y =ᶠ[𝓝 0] fun t => tanProj (Y t) (F (Y t)) := by
    filter_upwards [hode] with t ht using ht.deriv
  have h3 := h1.congr_of_eventuallyEq hd
  refine ⟨h3.differentiableAt, ?_⟩
  have hN : tanProj (Y 0) (F (Y 0) - T) = 0 := by
    rw [map_sub, hT, (isOrthProj_tanProj _).idem, sub_self]
  rw [h3.deriv, h2, ← dTanProj_normal h hN T]

/-- **The curvature term of Prop. 6 of arXiv 2309.06125** is bounded by `2 B ε / σ_r`, where `B`
bounds `‖F‖`, `ε` is the modeling error (5) and `ρ = σ_r` bounds the singular values of `S` from
below.  This bound is not stated in the paper; it follows from `norm_weingarten_le`. -/
theorem norm_curvature_term_le [DecidableEq m] [DecidableEq n] (h : IsFactorization X U S V)
    {ρ B ε : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖)
    {F₀ : Matrix m n ℝ} (hB : ‖F₀‖ ≤ B) (hε : ‖F₀ - tanProj X F₀‖ ≤ ε) :
    ‖weingarten U S V (tanProj X F₀) (F₀ - tanProj X F₀)‖ ≤ 2 * B * ε / ρ := by
  refine (norm_weingarten_le h hρ hS _ _).trans ?_
  have h1 : ‖tanProj X F₀‖ ≤ B := ((isOrthProj_tanProj X).norm_le F₀).trans hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  gcongr

/-- Non-vacuity of Prop. 6 of arXiv 2309.06125: `Y t = eᵗ X` solves `Y' = Π(Y) F(Y)` on `M_r` for
`F = id`. -/
theorem exists_dlra_curve (hX : X.rank = r) :
    (∀ᶠ t in 𝓝 (0 : ℝ), (Real.exp t • X).rank = r) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t : ℝ => Real.exp t • X)
        (tanProj (Real.exp t • X) (id (Real.exp t • X))) t := by
  classical
  obtain ⟨U, S, V, h⟩ := exists_factorization (r := r) hX
  have hf : ∀ t : ℝ, IsFactorization (Real.exp t • X) U (Real.exp t • S) V := fun t =>
    { orthU := h.orthU
      orthV := h.orthV
      det := by
        rw [Matrix.det_smul]
        exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (Real.exp_pos t).ne')).mul h.det
      eq := by
        rw [h.eq]
        simp only [Matrix.smul_mul, Matrix.mul_smul] }
  refine ⟨Eventually.of_forall fun t => (hf t).rank, Eventually.of_forall fun t => ?_⟩
  have hmem : Real.exp t • X ∈ tangentSpace (Real.exp t • X) := ⟨1, 0, by simp⟩
  rw [id, tanProj_eq_self_iff.2 hmem]
  exact (Real.hasDerivAt_exp t).smul_const X

/-- **Eqs. (8)-(9) of arXiv 2309.06125 for DLRA.**  For every retraction `R` on `M_r` the step
`Y₁ = R_{Y(0)}(Δt Π(Y(0)) F(Y(0)))` has local error `O(Δt²)` with respect to the exact solution of
`Y' = Π(Y) F(Y)`. -/
theorem dlra_local_error {R : Matrix m n ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hR : IsRetraction (rankSet m n r) (fun X => (tangentSpace X : Set (Matrix m n ℝ))) R)
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r)
    (hode : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt Y (tanProj (Y t) (F (Y t))) t)
    (hF : DifferentiableAt ℝ F (Y 0)) :
    (fun dt : ℝ => Y dt - R (Y 0) (dt • tanProj (Y 0) (F (Y 0)))) =O[𝓝 0]
      fun dt : ℝ => dt ^ 2 := by
  classical
  have hr0 : (Y 0).rank = r := hrank.self_of_nhds
  obtain ⟨U, S, V, hfac⟩ := exists_factorization hr0
  obtain ⟨hdd, -⟩ := dlra_acceleration hfac hrank hode hF.hasFDerivAt
  have hmem : tanProj (Y 0) (F (Y 0)) ∈ tangentSpace (Y 0) :=
    Submodule.starProjection_apply_mem _ _
  exact hR.local_error hr0 hmem (hode.mono fun t ht => ht.differentiableAt) hdd rfl
    hode.self_of_nhds.deriv

/-- The step (14) of arXiv 2309.06125, `Y₁ = R^KLS_{Y₀}(Δt Π(Y₀) F(Y₀))`, has local error `O(Δt²)`.
By `isSecondOrderRetraction_orth` and `isSecondOrderRetraction_ksl` the same holds for `R^ORTH` and
`R^KSL`. -/
theorem kls_local_error (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r)
    (hode : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt Y (tanProj (Y t) (F (Y t))) t)
    (hF : DifferentiableAt ℝ F (Y 0)) :
    (fun dt : ℝ => Y dt - retrKLS r (Y 0) (dt • tanProj (Y 0) (F (Y 0)))) =O[𝓝 0]
      fun dt : ℝ => dt ^ 2 :=
  dlra_local_error isSecondOrderRetraction_kls.toIsRetraction hrank hode hF

/-! ### Eqs. (10)-(11): the SVD retraction -/

/-- **The SVD retraction** `R^SVD_X(Z) = Π_{M_r}(X + Z)` (arXiv 2309.06125, eq. (11)), the truncated
SVD `LeanDLRA.EckartYoung.truncation`, a best approximation of rank `≤ r`
(`EckartYoung.norm_sub_truncation_le`).  With this definition the projected forward Euler step (10)
is `retrSVD r Yₖ (Δt Π(Yₖ) F(Yₖ))` by definition. -/
noncomputable def retrSVD [DecidableEq n] (r : ℕ) (X Z : Matrix m n ℝ) : Matrix m n ℝ :=
  EckartYoung.truncation (X + Z) r

/-- `X + Z` has rank at most `2 r` for `Z ∈ T_X M_r` (arXiv 2309.06125, §3.1). -/
theorem rank_add_tangent_le (h : IsFactorization X U S V) {Z : Matrix m n ℝ}
    (hZ : Z ∈ tangentSpace X) : (X + Z).rank ≤ 2 * r := by
  classical
  have rep := (h.tangentRep hZ).add_base h.eq
  have e : X + Z = Matrix.fromCols (U * (S + Uᵀ * Z * V) + (1 - U * Uᵀ) * Z * V) U *
      Matrix.fromRows Vᵀ ((1 - V * Vᵀ) * Zᵀ * U)ᵀ := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.add_mul]
    exact rep.eq
  rw [e]
  refine (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_le_card_height _).trans ?_)
  simp [two_mul]

lemma retrSVD_sub_le [DecidableEq n] (h : IsFactorization X U S V) {Z : Matrix m n ℝ}
    (rep : IsTangentRep U V M Up Vp Z) (hA : IsUnit (S + M).det) :
    ‖retrSVD r X Z - (X + Z)‖ ≤ ‖Up * (S + M)⁻¹ * Vpᵀ‖ := by
  have hZ := rep.mem_tangentSpace h
  have hA' : IsUnit (Uᵀ * (X + Z) * V).det := by rwa [h.compression_eq rep]
  have hmem := (h.orthRetr_mem hZ hA').2
  have hle := EckartYoung.norm_sub_truncation_le (X + Z) (r := r) (le_of_eq hmem)
  rw [norm_sub_rev, orthRetr_eq h rep hA, sub_add_cancel_left, norm_neg] at hle
  exact hle

/-- **First-order property of the SVD retraction** (arXiv 2309.06125, §3.1, quoting Absil–Malick
2012): `R^SVD_X(τ Z) = X + τ Z + O(τ²)`, so `R^SVD_X(0) = X` and the curve has velocity `Z`.  This
holds for the truncation as defined, whichever singular vectors it picks.  Smoothness of `R^SVD`,
and hence `IsRetraction`, is not proved here. -/
theorem retrSVD_curve [DecidableEq n] (h : IsFactorization X U S V) {Z : Matrix m n ℝ}
    (hZ : Z ∈ tangentSpace X) :
    retrSVD r X 0 = X ∧ HasDerivAt (fun τ : ℝ => retrSVD r X (τ • Z)) Z 0 ∧
      (fun τ : ℝ => retrSVD r X (τ • Z) - (X + τ • Z)) =O[𝓝 0] fun τ => τ ^ 2 := by
  classical
  have rep := h.tangentRep hZ
  have h0 : retrSVD r X 0 = X := by
    have hle := EckartYoung.norm_sub_truncation_le X (r := r) (le_of_eq h.rank)
    rw [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at hle
    rw [retrSVD, add_zero]
    exact hle.symm
  set c : ℝ → Matrix m n ℝ := fun τ => (1 - U * Uᵀ) * Z * V * (S + τ • (Uᵀ * Z * V))⁻¹ *
    ((1 - V * Vᵀ) * Zᵀ * U)ᵀ with hc
  have hcc : ContDiffAt ℝ 0 c 0 :=
    contDiffAt_mul (contDiffAt_mul contDiffAt_const (contDiffAt_inv_line h.det _)) contDiffAt_const
  have hb : c =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hcc.continuousAt.tendsto.isBigO_one ℝ
  have hs := (Asymptotics.isBigO_refl (fun τ : ℝ => τ ^ 2) (𝓝 0)).smul hb
  simp only [smul_eq_mul, mul_one] at hs
  have hO : (fun τ : ℝ => retrSVD r X (τ • Z) - (X + τ • Z)) =O[𝓝 0] fun τ => τ ^ 2 := by
    refine (Asymptotics.IsBigO.of_bound 1 ?_).trans hs
    filter_upwards [eventually_isUnit_add_smul h.det (Uᵀ * Z * V)] with τ hτ
    have hle := retrSVD_sub_le h (rep.smul τ) hτ
    have e : (τ • ((1 - U * Uᵀ) * Z * V)) * (S + τ • (Uᵀ * Z * V))⁻¹ *
        (τ • ((1 - V * Vᵀ) * Zᵀ * U))ᵀ = τ ^ 2 • c τ := by
      simp only [hc, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, sq]
    rw [e] at hle
    rw [one_mul]
    exact hle
  refine ⟨h0, ?_, hO⟩
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hzero : retrSVD r X ((0 : ℝ) • Z) = X := by rw [zero_smul, h0]
  have hlo : (fun τ : ℝ => retrSVD r X (τ • Z) - (X + τ • Z)) =o[𝓝 0] fun τ : ℝ => τ :=
    hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
  refine hlo.congr_left fun τ => ?_
  rw [zero_add, hzero, sub_sub]

/-- **The projected forward Euler step (10) has local error `O(Δt²)`** (arXiv 2309.06125, §3.1).
This follows from quasi-optimality of the truncated SVD, without using smoothness of `R^SVD`. -/
theorem projectedEuler_local_error [DecidableEq n]
    (hrank : ∀ᶠ t in 𝓝 (0 : ℝ), (Y t).rank = r)
    (hode : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt Y (tanProj (Y t) (F (Y t))) t)
    (hF : DifferentiableAt ℝ F (Y 0)) :
    (fun dt : ℝ => Y dt - retrSVD r (Y 0) (dt • tanProj (Y 0) (F (Y 0)))) =O[𝓝 0]
      fun dt : ℝ => dt ^ 2 := by
  classical
  obtain ⟨U, S, V, hfac⟩ := exists_factorization (hrank.self_of_nhds)
  obtain ⟨hdd, -⟩ := dlra_acceleration hfac hrank hode hF.hasFDerivAt
  set v := tanProj (Y 0) (F (Y 0)) with hv
  set w : ℝ → Matrix m n ℝ := fun τ => Y 0 + τ • v with hw
  have hwd : ∀ τ, HasDerivAt w v τ := fun τ => by
    have h1 := ((hasDerivAt_id τ).smul_const v).const_add (Y 0)
    rw [one_smul] at h1
    exact h1
  have hdw : deriv w = fun _ => v := funext fun τ => (hwd τ).deriv
  have hO : (fun τ => Y τ - w τ) =O[𝓝 0] fun τ : ℝ => τ ^ 2 := by
    refine isBigO_sq_of_jet (hode.mono fun t ht => ht.differentiableAt)
      (Eventually.of_forall fun τ => (hwd τ).differentiableAt) hdd ?_ (by simp [hw]) ?_
    · rw [hdw]
      exact differentiableAt_const _
    · rw [hode.self_of_nhds.deriv, hdw]
  refine (Asymptotics.IsBigO.of_bound 2 ?_).trans hO
  filter_upwards [hrank] with τ hτ
  have hle := EckartYoung.norm_sub_truncation_le (w τ) (r := r) (B := Y τ) (le_of_eq hτ)
  have htri : ‖Y τ - retrSVD r (Y 0) (τ • v)‖ ≤
      ‖Y τ - w τ‖ + ‖w τ - EckartYoung.truncation (w τ) r‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_sub_rev (w τ) (Y τ)] at hle
  linarith

end DLRA

/-! ### Eqs. (13)-(14): the KLS and KSL schemes with forward Euler substeps -/

section Schemes

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}
  {X : Matrix m n ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
  {S₀ SU SV Sh St S₁ : Matrix (Fin r) (Fin r) ℝ} {F : Matrix m n ℝ → Matrix m n ℝ} {dt : ℝ}

/-- One step of the **KLS scheme** of arXiv 2309.06125, §3.3: the unconventional (BUG) integrator
from `Y₀ = U₀ S₀ V₀ᵀ` with one forward Euler step per substep.  K- and L-steps start at `Y₀`; the
S-step starts at `Ŷ = U₁ (U₁ᵀ U₀ S₀ V₀ᵀ V₁) V₁ᵀ`.  The output is `U₁ S₁ V₁ᵀ`. -/
structure IsEulerKLSStep (F : Matrix m n ℝ → Matrix m n ℝ) (dt : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
    (SU : Matrix (Fin r) (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (SV S₁ : Matrix (Fin r) (Fin r) ℝ) :
    Prop where
  orthU₁ : U₁ᵀ * U₁ = 1
  orthV₁ : V₁ᵀ * V₁ = 1
  detSU : IsUnit SU.det
  detSV : IsUnit SV.det
  kStep : U₁ * SU = U₀ * S₀ + dt • (F (U₀ * S₀ * V₀ᵀ) * V₀)
  lStep : V₁ * SV = V₀ * S₀ᵀ + dt • ((F (U₀ * S₀ * V₀ᵀ))ᵀ * U₀)
  sStep : S₁ = U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁) +
    dt • (U₁ᵀ * F (U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ) * V₁)

/-- One step of the **KSL scheme** of arXiv 2309.06125, §3.2: the projector-splitting integrator
from `Y₀ = U₀ S₀ V₀ᵀ` with one forward Euler step per substep, each evaluating `F` at the current
point.  The output is `U₁ S₁ V₁ᵀ`. -/
structure IsEulerKSLStep (F : Matrix m n ℝ → Matrix m n ℝ) (dt : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
    (Sh St : Matrix (Fin r) (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ)
    (S₁ : Matrix (Fin r) (Fin r) ℝ) : Prop where
  orthU₁ : U₁ᵀ * U₁ = 1
  orthV₁ : V₁ᵀ * V₁ = 1
  detSh : IsUnit Sh.det
  kStep : U₁ * Sh = U₀ * S₀ + dt • (F (U₀ * S₀ * V₀ᵀ) * V₀)
  sStep : St = Sh - dt • (U₁ᵀ * F (U₁ * Sh * V₀ᵀ) * V₀)
  lStep : V₁ * S₁ᵀ = V₀ * Stᵀ + dt • ((F (U₁ * St * V₀ᵀ))ᵀ * U₁)

/-- `Π(X) G` and `G` have the same K-step. -/
lemma IsFactorization.tanProj_mul_V (h : IsFactorization X U₀ S₀ V₀) (G : Matrix m n ℝ) :
    tanProj X G * V₀ = G * V₀ := by
  rw [h.tanProj_apply]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, h.orthV, Matrix.mul_one]
  abel

/-- `Π(X) G` and `G` have the same L-step. -/
lemma IsFactorization.tanProj_transpose_mul_U (h : IsFactorization X U₀ S₀ V₀)
    (G : Matrix m n ℝ) : (tanProj X G)ᵀ * U₀ = Gᵀ * U₀ := by
  have hU : U₀ᵀ * tanProj X G = U₀ᵀ * G := by
    have e : ∀ B : Matrix (Fin r) n ℝ, U₀ᵀ * (U₀ * B) = B := fun B => by
      rw [← Matrix.mul_assoc, h.orthU, Matrix.one_mul]
    rw [h.tanProj_apply]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc, e]
    abel
  have := congrArg Matrix.transpose hU
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using this

/-- **The K- and L-steps of the KLS scheme coincide with those of `R^KLS`** (arXiv 2309.06125,
§3.3).  The Euler substeps from `Y₀` see only `F(Y₀) V₀` and `F(Y₀)ᵀ U₀`, which do not change if
`F(Y₀)` is replaced by `Π(Y₀) F(Y₀)`.  So the scheme (with `F`) and Algorithm 3 (with
`Z = Δt Π(Y₀) F(Y₀)`) compute the same new bases `U₁`, `V₁`. -/
theorem IsEulerKLSStep.bases_eq
    (hs : IsEulerKLSStep F dt U₀ S₀ V₀ U₁ SU V₁ SV S₁) (h : IsFactorization X U₀ S₀ V₀) :
    (X + dt • tanProj X (F X)) * V₀ = U₁ * SU ∧ (X + dt • tanProj X (F X))ᵀ * U₀ = V₁ * SV := by
  have e0 := h.eq
  constructor
  · rw [hs.kStep, ← e0, Matrix.add_mul, h.mul_V, Matrix.smul_mul, h.tanProj_mul_V]
  · rw [hs.lStep, ← e0, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
      Matrix.smul_mul, h.tanProj_transpose_mul_U, h.transpose.mul_V]

/-- **Eq. (14) of arXiv 2309.06125 with its exact defect.**  One step of the KLS scheme is
`Y₁ = R^KLS_{Y₀}(Δt Π(Y₀) F(Y₀)) + Δt U₁ U₁ᵀ (F(Ŷ) - Π(Y₀) F(Y₀)) V₁ V₁ᵀ`.  Eq. (14) states this
without the second term.  The term vanishes if the S-step sees the tangent vector
`Π(Y₀) F(Y₀)`, see `IsEulerKLSStep.eq_klsRetr_of_const`; in general it does not, see
`eulerKLS_ne_klsRetr`. -/
theorem IsEulerKLSStep.eq_klsRetr_add (hs : IsEulerKLSStep F dt U₀ S₀ V₀ U₁ SU V₁ SV S₁)
    (h : IsFactorization X U₀ S₀ V₀) :
    U₁ * S₁ * V₁ᵀ = klsRetr U₀ V₀ X (dt • tanProj X (F X)) +
      dt • (U₁ * U₁ᵀ * (F (U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ) - tanProj X (F X)) *
        (V₁ * V₁ᵀ)) := by
  classical
  obtain ⟨h1, h2⟩ := hs.bases_eq h
  have hP : colProj ((X + dt • tanProj X (F X)) * V₀) = U₁ * U₁ᵀ := colP_of_qr hs.orthU₁ hs.detSU h1
  have hQ : colProj ((X + dt • tanProj X (F X))ᵀ * U₀) = V₁ * V₁ᵀ :=
    colP_of_qr hs.orthV₁ hs.detSV h2
  have eX : U₁ * (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)) * V₁ᵀ = U₁ * U₁ᵀ * X * (V₁ * V₁ᵀ) := by
    rw [h.eq]
    simp only [Matrix.mul_assoc]
  rw [klsRetr, hP, hQ, hs.sStep, Matrix.mul_add, Matrix.add_mul, eX, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  abel

/-- **Eq. (14) of arXiv 2309.06125 for a frozen tangent field.**  If all substeps use one fixed
tangent vector `G ∈ T_{Y₀} M_r` (for instance `G = Π(Y₀) F(Y₀)`), the KLS scheme is exactly
`R^KLS_{Y₀}(Δt G) = U₁ U₁ᵀ (Y₀ + Δt G) V₁ V₁ᵀ`. -/
theorem IsEulerKLSStep.eq_klsRetr_of_const {G : Matrix m n ℝ}
    (hs : IsEulerKLSStep (fun _ => G) dt U₀ S₀ V₀ U₁ SU V₁ SV S₁)
    (h : IsFactorization X U₀ S₀ V₀) (hG : G ∈ tangentSpace X) :
    U₁ * S₁ * V₁ᵀ = klsRetr U₀ V₀ X (dt • G) := by
  have e := hs.eq_klsRetr_add h
  simp only [tanProj_eq_self_iff.2 hG, sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero,
    add_zero] at e
  exact e

/-- **Eq. (13) of arXiv 2309.06125 with its exact defect.**  One step of the KSL scheme is
`Y₁ = R^KSL_{Y₀}(Δt Π(Y₀) F(Y₀)) + Δt U₁ U₁ᵀ (F(Y₀) Q₀ - F(Y₁') Q₀ + F(Y₂') - Π(Y₀) F(Y₀))`, with
`Q₀ = V₀ V₀ᵀ` and the intermediate points `Y₁' = U₁ Ŝ V₀ᵀ`, `Y₂' = U₁ S̃ V₀ᵀ`.  Eq. (13) states this
without the second term; it vanishes for a frozen tangent field
(`IsEulerKSLStep.eq_kslRetr_of_const`), and not in general (`eulerKSL_ne_kslRetr`). -/
theorem IsEulerKSLStep.eq_kslRetr_add (hs : IsEulerKSLStep F dt U₀ S₀ V₀ U₁ Sh St V₁ S₁)
    (h : IsFactorization X U₀ S₀ V₀) :
    U₁ * S₁ * V₁ᵀ = kslRetr V₀ X (dt • tanProj X (F X)) +
      dt • (U₁ * U₁ᵀ * (F X * (V₀ * V₀ᵀ) - F (U₁ * Sh * V₀ᵀ) * (V₀ * V₀ᵀ) + F (U₁ * St * V₀ᵀ) -
        tanProj X (F X))) := by
  classical
  have h1 : (X + dt • tanProj X (F X)) * V₀ = U₁ * Sh := by
    rw [hs.kStep, ← h.eq, Matrix.add_mul, h.mul_V, Matrix.smul_mul, h.tanProj_mul_V]
  have hP : colProj ((X + dt • tanProj X (F X)) * V₀) = U₁ * U₁ᵀ := colP_of_qr hs.orthU₁ hs.detSh h1
  have ht : S₁ * V₁ᵀ = St * V₀ᵀ + dt • (U₁ᵀ * F (U₁ * St * V₀ᵀ)) := by
    have := congrArg Matrix.transpose hs.lStep
    simpa only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_transpose] using this
  have hSh : U₁ * Sh * V₀ᵀ = U₁ * U₁ᵀ * (X + dt • (F X * (V₀ * V₀ᵀ))) := by
    have e1 : U₁ * Sh = U₁ * U₁ᵀ * (U₁ * Sh) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc U₁ᵀ, hs.orthU₁, Matrix.one_mul]
    rw [e1, hs.kStep, ← h.eq, Matrix.mul_assoc, Matrix.add_mul, ← h.eq, Matrix.smul_mul,
      Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  have hSt : U₁ * St * V₀ᵀ = U₁ * U₁ᵀ * (X + dt • (F X * (V₀ * V₀ᵀ))) -
      dt • (U₁ * U₁ᵀ * (F (U₁ * Sh * V₀ᵀ) * (V₀ * V₀ᵀ))) := by
    rw [hs.sStep, Matrix.mul_sub, Matrix.sub_mul, hSh]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [kslRetr, hP, Matrix.mul_assoc U₁ S₁, ht, Matrix.mul_add, ← Matrix.mul_assoc U₁ St, hSt]
  simp only [Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub, Matrix.mul_smul,
    Matrix.mul_assoc]
  abel

/-- **Eq. (13) of arXiv 2309.06125 for a frozen tangent field.**  If all substeps use one fixed
tangent vector `G ∈ T_{Y₀} M_r`, the KSL scheme is exactly `R^KSL_{Y₀}(Δt G)`. -/
theorem IsEulerKSLStep.eq_kslRetr_of_const {G : Matrix m n ℝ}
    (hs : IsEulerKSLStep (fun _ => G) dt U₀ S₀ V₀ U₁ Sh St V₁ S₁)
    (h : IsFactorization X U₀ S₀ V₀) (hG : G ∈ tangentSpace X) :
    U₁ * S₁ * V₁ᵀ = kslRetr V₀ X (dt • G) := by
  have e := hs.eq_kslRetr_add h
  simp only [tanProj_eq_self_iff.2 hG, sub_self, zero_add, Matrix.mul_zero, smul_zero,
    add_zero] at e
  exact e

end Schemes

/-! ### Eqs. (13)-(14) do not hold literally -/

section Counterexamples

/-- The number `1 / √2`. -/
private noncomputable def s₂ : ℝ := √2 / 2

private lemma s₂_mul : s₂ * s₂ = 1 / 2 := by
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold s₂
  nlinarith

private lemma s₂_ne : s₂ ≠ 0 := by
  unfold s₂
  positivity

/-- `e₁ ∈ ℝ²`, as a basis of the column and row space of `exX`. -/
private def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The unit vector `(1, 1) / √2`. -/
private noncomputable def u₁ : Matrix (Fin 2) (Fin 1) ℝ := !![s₂; s₂]

/-- The rank-one matrix `e₁ e₁ᵀ`. -/
private def exX : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- A constant field with a nonzero normal component at `exX`. -/
private def exG : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

private lemma ex_fact : IsFactorization (r := 1) exX e₁ 1 e₁ where
  orthU := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]
  orthV := by
    ext i j
    fin_cases i
    fin_cases j
    simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]
  det := by simp
  eq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exX, e₁, Matrix.mul_apply]

private lemma ex_normal : exG - tanProj exX exG = !![0, 0; 0, 1] := by
  have hP : e₁ * e₁ᵀ = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e₁, Matrix.mul_apply]
  have e : e₁ * e₁ᵀ * exG + exG * e₁ * e₁ᵀ - e₁ * e₁ᵀ * exG * e₁ * e₁ᵀ =
      e₁ * e₁ᵀ * exG + exG * (e₁ * e₁ᵀ) - e₁ * e₁ᵀ * exG * (e₁ * e₁ᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [ex_fact.tanProj_apply, e, hP]
  simp only [exG, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma ex_proj : u₁ * u₁ᵀ = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u₁, Matrix.mul_apply, s₂_mul]

private lemma ex_orth : u₁ᵀ * u₁ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [u₁, Matrix.mul_apply, Fin.sum_univ_two, s₂_mul]
  norm_num

/-- **Eq. (14) of arXiv 2309.06125 fails as an identity.**  For the constant field `F ≡ G`,
`G = [[0, 1], [1, 1]]`, the rank-one point `X = e₁ e₁ᵀ` and `Δt = 1`, one step of the KLS scheme
(BUG with forward Euler substeps; for a constant field these are the exact substeps) gives
`[[1, 1], [1, 1]]`, while `R^KLS_X(Δt Π(X) G) = (3/4) [[1, 1], [1, 1]]`.  The reason is that the
S-step uses `G`, not `Π(X) G`: by `IsEulerKLSStep.eq_klsRetr_add` the two agree only up to
`Δt P₁ Π⊥(X) G Q₁`, which is nonzero when the bases move.  Eq. (14) does hold when the scheme is
applied to the frozen tangent field `Π(X) G`, see `IsEulerKLSStep.eq_klsRetr_of_const`. -/
theorem eulerKLS_ne_klsRetr :
    ∃ (X G : Matrix (Fin 2) (Fin 2) ℝ) (U₀ U₁ V₀ V₁ : Matrix (Fin 2) (Fin 1) ℝ)
      (S₀ SU SV S₁ : Matrix (Fin 1) (Fin 1) ℝ),
      IsFactorization X U₀ S₀ V₀ ∧ IsEulerKLSStep (fun _ => G) 1 U₀ S₀ V₀ U₁ SU V₁ SV S₁ ∧
        U₁ * S₁ * V₁ᵀ ≠ klsRetr U₀ V₀ X ((1 : ℝ) • tanProj X G) := by
  have hs : IsEulerKLSStep (fun _ => exG) 1 e₁ 1 e₁ u₁ !![2 * s₂] u₁ !![2 * s₂]
      (u₁ᵀ * e₁ * 1 * (e₁ᵀ * u₁) + (1 : ℝ) • (u₁ᵀ * exG * u₁)) :=
    { orthU₁ := ex_orth
      orthV₁ := ex_orth
      detSU := by simpa [Matrix.det_fin_one] using s₂_ne
      detSV := by simpa [Matrix.det_fin_one] using s₂_ne
      kStep := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [u₁, e₁, exG, Matrix.mul_apply] <;> nlinarith [s₂_mul]
      lStep := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [u₁, e₁, exG, Matrix.mul_apply] <;> nlinarith [s₂_mul]
      sStep := rfl }
  refine ⟨exX, exG, e₁, u₁, e₁, u₁, 1, _, _, _, ex_fact, hs, fun heq => ?_⟩
  have e := hs.eq_klsRetr_add ex_fact
  rw [heq, ← sub_eq_iff_eq_add', sub_self, ex_normal, ex_proj] at e
  have h00 := congrFun (congrFun e 0) 0
  simp at h00

/-- **Eq. (13) of arXiv 2309.06125 fails as an identity.**  For the same data as in
`eulerKLS_ne_klsRetr`, one step of the KSL scheme with forward Euler substeps gives
`U₁ U₁ᵀ (X + Δt G) = [[1, 1], [1, 1]]`, while `R^KSL_X(Δt Π(X) G) = U₁ U₁ᵀ (X + Δt Π(X) G)` has
second column `(1/2, 1/2)`.  Eq. (13) does hold for the frozen tangent field `Π(X) G`, see
`IsEulerKSLStep.eq_kslRetr_of_const`. -/
theorem eulerKSL_ne_kslRetr :
    ∃ (X G : Matrix (Fin 2) (Fin 2) ℝ) (U₀ U₁ V₀ V₁ : Matrix (Fin 2) (Fin 1) ℝ)
      (S₀ Sh St S₁ : Matrix (Fin 1) (Fin 1) ℝ),
      IsFactorization X U₀ S₀ V₀ ∧ IsEulerKSLStep (fun _ => G) 1 U₀ S₀ V₀ U₁ Sh St V₁ S₁ ∧
        U₁ * S₁ * V₁ᵀ ≠ kslRetr V₀ X ((1 : ℝ) • tanProj X G) := by
  have hGe : exG * e₁ = !![0; 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exG, e₁, Matrix.mul_apply, Fin.sum_univ_two]
  have hSt : !![2 * s₂] - (1 : ℝ) • (u₁ᵀ * exG * e₁) = !![s₂] := by
    rw [Matrix.mul_assoc, hGe]
    ext i j
    fin_cases i
    fin_cases j
    simp [u₁, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hGt : exGᵀ * u₁ = !![s₂; 2 * s₂] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exG, u₁, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hs : IsEulerKSLStep (fun _ => exG) 1 e₁ 1 e₁ u₁ !![2 * s₂]
      (!![2 * s₂] - (1 : ℝ) • (u₁ᵀ * exG * e₁)) u₁ !![2] :=
    { orthU₁ := ex_orth
      orthV₁ := ex_orth
      detSh := by simpa [Matrix.det_fin_one] using s₂_ne
      kStep := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [u₁, e₁, exG, Matrix.mul_apply] <;> nlinarith [s₂_mul]
      sStep := rfl
      lStep := by
        have hT : (!![s₂] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ = !![s₂] := by
          ext i j
          fin_cases i
          fin_cases j
          simp
        rw [hSt, hT]
        simp only [hGt]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [u₁, e₁, Matrix.mul_apply] <;> ring }
  refine ⟨exX, exG, e₁, u₁, e₁, u₁, 1, _, _, _, ex_fact, hs, fun heq => ?_⟩
  have e := hs.eq_kslRetr_add ex_fact
  simp only [sub_self, zero_add] at e
  rw [heq, ← sub_eq_iff_eq_add', sub_self, ex_normal, ex_proj] at e
  have h01 := congrFun (congrFun e 0) 1
  simp at h01

end Counterexamples

/-! ### The library's BUG step for a constant field -/

section BUGConstant

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

lemma odeSolution_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {y : ℝ → E} {a b : ℝ} {c : E} (hy : ODESolution f y a b) (hf : ∀ t x, f t x = c)
    (hab : a ≤ b) : y b = y a + (b - a) • c := by
  have hg : ContinuousOn (fun t => y t - (t - a) • c) (Icc a b) := hy.cont.sub (by fun_prop)
  have hd : ∀ x ∈ Ico a b, HasDerivWithinAt (fun t => y t - (t - a) • c) 0 (Ici x) x := by
    intro x hx
    have h1 := hy.deriv x hx
    rw [hf] at h1
    have h2 : HasDerivWithinAt (fun t => (t - a) • c) c (Ici x) x := by
      have h3 := ((hasDerivAt_id x).sub_const a).smul_const c
      rw [one_smul] at h3
      exact h3.hasDerivWithinAt
    simpa using h1.fun_sub h2
  have h4 := constant_of_has_deriv_right_zero hg hd b ⟨hab, le_refl b⟩
  simp only [sub_self, zero_smul, sub_zero] at h4
  rw [sub_eq_iff_eq_add] at h4
  rw [h4, add_comm]

/-- **BUG with exact substeps coincides with the KLS scheme for a constant field**
(arXiv 2309.06125, §3.3): for `F ≡ G` the exact K-, L- and S-flows of the library's
`MatrixBUG.IsStep` are single forward Euler steps, with the QR factorizations
`K(t₁) = U₁ S_U`, `L(t₁) = V₁ S_V`.  With `IsEulerKLSStep.eq_klsRetr_of_const` this gives
`U₁ S(t₁) V₁ᵀ = R^KLS_X((t₁ - t₀) G)` for tangent `G`. -/
theorem isEulerKLSStep_of_bugStep {G : Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
    {S₀ SU SV : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
    {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hs : MatrixBUG.IsStep (fun _ _ => G) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (ht : t₀ ≤ t₁)
    (hSU : IsUnit SU.det) (hSV : IsUnit SV.det) (hK : K t₁ = U₁ * SU) (hL : Lf t₁ = V₁ * SV) :
    IsEulerKLSStep (fun _ => G) (t₁ - t₀) U₀ S₀ V₀ U₁ SU V₁ SV (S t₁) where
  orthU₁ := hs.orthU₁
  orthV₁ := hs.orthV₁
  detSU := hSU
  detSV := hSV
  kStep := by
    rw [← hK, odeSolution_const (c := G * V₀) hs.kSol (fun _ _ => rfl) ht, hs.kStart]
  lStep := by
    rw [← hL, odeSolution_const (c := Gᵀ * U₀) hs.lSol (fun _ _ => rfl) ht, hs.lStart]
  sStep := by
    rw [odeSolution_const (c := U₁ᵀ * G * V₁) hs.sSol (fun _ _ => rfl) ht, hs.sStart]

end BUGConstant

/-- The local projector `A (Aᵀ A)⁻¹ Aᵀ` of this file, replaced by the core `Matrix.colProj` (the
same matrix: `Matrix.colProj_def`). -/
@[deprecated (since := "2026-11-09")] alias colP := Matrix.colProj

end LeanDLRA.Literature.P2309_06125
