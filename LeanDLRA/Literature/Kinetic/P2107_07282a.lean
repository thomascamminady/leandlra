import LeanDLRA.Control.AdjointDLRA
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Energy

/-!
# Results of arXiv 2107.07282: L²-stability of robust DLRA for hyperbolic problems

This module formalizes Kusch–Einkemmer–Ceruti, *On the stability of robust dynamical low-rank
approximations for hyperbolic problems*, on the actual Lax–Friedrichs matrices `L1 n`, `L2 n ν` of
the periodic grid `ZMod n` (`ν = Δt / Δx`), for a symmetric flux `A` with biggest absolute
eigenvalue `lamMax`.  `lfStep_amplification` and `lfStep_contractive_iff` give the exact
amplification and the sharp CFL condition of the full scheme (Sec. 2.2).  `ksl_lf_unstable` and
`ksl_lf_unstable_rankOne` are Theorem 1.  `scheme31_stable` and `scheme35_stable` are Theorems 2
and 3 for general low-rank states with the CFL condition measured by `λ_max(A)`; with `λ_max(Ã)`,
as printed, both are false (`scheme31_literal_false`, `scheme35_literal_false`).  `scheme31_sharp`
shows that `1/√3` is sharp, and `scheme31_mode`, `scheme35_mode`, `scheme38_mode` are the
single-mode factors of the paper, with equality.  `scheme38_stable` is Theorem 4.
`scattering_ksl`, `scattering_lStep_contractive_iff` and `scheme35_scattering_stable` are Section 5.

## Differences from the paper

* **Grid.**  The paper calls `L⁽¹⁾`, `L⁽²⁾` tridiagonal, but its Fourier ansatz (6) needs periodic
  boundary conditions, so `L1 n`, `L2 n ν` are periodic.  With `Nₓ = n`, `Δx = 2 / n` the angle
  `angle α = 2 π α / n` is the paper's `α π Δx`.  Only `L⁽²⁾ = ν M` depends on `Δt`, `Δx`.
* **Flux.**  `A` is symmetric.  The paper uses this implicitly: it diagonalises `A` unitarily, and
  its examples are symmetric.
* **Theorem 1** needs even `Nₓ`, because a wave number with `cos(ᾱ π Δx) = -1` is required.
* **Theorems 2 and 3.**  The L-step contains the full `A`, not `Ã`, so (29c), (33c) and the bounds
  built on them are wrong, and the theorems fail as printed.  With `λ_max(A)` both are true.
  Theorem 3 then follows substep by substep.  For Theorem 2 the paper's argument has a second gap:
  it takes a maximum over wave numbers in each substep and combines them at one common `α`, but
  `X Xᵀ` couples the modes, and separate maxima only give the factor `1 + c²`.  `core31` is a
  different proof that does not use Fourier analysis at all.  With `T = Xᵀ M X` the S- and L-steps
  give `‖L₁‖² ≤ ‖S̃‖² + 2 c² ‖T S̃‖² + c⁴ ‖T² S̃‖²`.  This growth is paid for by the energy
  `(1 - c²) ‖M K‖²` dissipated in the K-step, by a Cauchy–Schwarz inequality with the adjoint of the
  K-step (`scheme31_arith`), and the constants close exactly at `3 c² ≤ 1`.
* **Theorem 4.**  `Ã` in the CFL condition is `Wⁿ⁺¹ᵀ Aᵀ Wⁿ⁺¹`, as in (39c).
* **Sharper or additional results.**  `lfStep_amplification` shows the bound (8) is attained,
  `scheme31_sharp` is new, and (37), (41) and the factor `G` hold with equality on Fourier modes.
* **QR factorisations** are recorded by their identities.
* **Section 5.**  The first half, the Euler scheme (42), is already in the library:
  `LeanDLRA.OpenProblems.Stability.kslScattering_norm_le_goldenRatio` gives the threshold
  `φ = 1.618…`, which the paper rounds to `1.62`.  It is not repeated here.

The abstract forms `kslEulerStep_unstable`, `kslSplitStep_norm_le`, `bug_euler_norm_le`,
`galerkin_euler_norm_le` and `LeanDLRA.OpenProblems.Stability.compression_bounds` are in the
library.  Left out: the numerical experiments of Sec. 6 and the qualitative Remarks 1–4.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2107_07282

/-! ### Frobenius preliminaries -/

section Prelim

variable {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]

/-- For skew `T` and symmetric `C`, `Z ↦ T Z C` is skew for the Frobenius inner product. -/
lemma inner_skew_symm {T : Matrix p p ℝ} (hT : Tᵀ = -T) {C : Matrix q q ℝ} (hC : Cᵀ = C)
    (Z : Matrix p q ℝ) : ⟪Z, T * Z * C⟫ = 0 := by
  have h1 : ⟪Z, T * Z * C⟫ = ⟪Z * C, T * Z⟫ := by
    rw [Frobenius.inner_mul_right', hC]
  have h2 : ⟪Z * C, T * Z⟫ = -⟪T * Z * C, Z⟫ := by
    rw [Frobenius.inner_mul_left' (Z * C) T Z, hT, Matrix.neg_mul, inner_neg_left,
      Matrix.mul_assoc]
  have h3 : ⟪T * Z * C, Z⟫ = ⟪Z, T * Z * C⟫ := real_inner_comm _ _
  linarith

/-- Right multiplication by a matrix with orthonormal columns is a contraction. -/
lemma norm_mul_orthonormal_le [DecidableEq r] {W : Matrix q r ℝ} (hW : Wᵀ * W = 1)
    (y : Matrix p q ℝ) : ‖y * W‖ ≤ ‖y‖ :=
  LeanDLRA.norm_mul_le_of_orthonormal hW y

/-- Left multiplication by the transpose of a matrix with orthonormal columns is a contraction. -/
lemma norm_transpose_mul_le [DecidableEq r] {X : Matrix p r ℝ} (hX : Xᵀ * X = 1)
    (y : Matrix p q ℝ) : ‖Xᵀ * y‖ ≤ ‖y‖ :=
  LeanDLRA.norm_transpose_mul_le hX y

end Prelim

/-! ### `λ_max(A)` -/

section LamMax

variable {p ι : Type*} [Fintype p] [Fintype ι]

/-- Right multiplication by `diag(d)` amplifies the Frobenius norm by at most `max |d i|`. -/
lemma norm_mul_diagonal_le [DecidableEq ι] (Y : Matrix p ι ℝ) {d : ι → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i, |d i| ≤ ρ) : ‖Y * Matrix.diagonal d‖ ≤ ρ * ‖Y‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (norm_nonneg _))).1 ?_
  rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_diagonal, mul_pow, mul_comm]
  have := (sq_le_sq₀ (abs_nonneg _) hρ).2 (h j)
  rw [sq_abs] at this
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

variable [DecidableEq ι]

/-- `λ_max(A)`: the biggest absolute eigenvalue of a symmetric matrix `A`. -/
noncomputable def lamMax {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : ℝ := ⨆ i, |hA.eigenvalues i|

lemma lamMax_nonneg {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : 0 ≤ lamMax hA :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma abs_eigenvalue_le_lamMax {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    |hA.eigenvalues i| ≤ lamMax hA :=
  le_ciSup (f := fun i => |hA.eigenvalues i|) (Set.finite_range _).bddAbove i

omit [Fintype ι] [DecidableEq ι] in
lemma transpose_eq_of_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : Aᵀ = A := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA

/-- `‖y A‖_F ≤ λ_max(A) ‖y‖_F` for symmetric `A` (arXiv 2107.07282, Sec. 2.2: the eigenvalue bound
behind (7)), by the spectral theorem. -/
theorem norm_mul_le_lamMax {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (y : Matrix p ι ℝ) :
    ‖y * A‖ ≤ lamMax hA * ‖y‖ := by
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have hUm : U ∈ Matrix.unitaryGroup ι ℝ := hA.eigenvectorUnitary.2
  have hE : A = U * Matrix.diagonal hA.eigenvalues * Uᵀ := by
    have h2 : A = U * Matrix.diagonal hA.eigenvalues * star U := by
      simpa [Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hU1 : Uᵀ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hUm
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hU2 : Uᵀᵀ * Uᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hUm
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.transpose_transpose U] at this
  have e : y * A = y * U * Matrix.diagonal hA.eigenvalues * Uᵀ :=
    (congrArg (y * ·) hE).trans (by simp only [Matrix.mul_assoc])
  rw [e, Frobenius.norm_mul_transpose_of_orthonormal hU1]
  have hyU : ‖y * U‖ = ‖y‖ := by
    have := Frobenius.norm_mul_transpose_of_orthonormal hU2 y
    rwa [Matrix.transpose_transpose] at this
  rw [← hyU]
  exact norm_mul_diagonal_le _ (lamMax_nonneg hA) (abs_eigenvalue_le_lamMax hA)

/-- Compressions do not increase the bound: `‖y Wᵀ A W‖_F ≤ λ_max(A) ‖y‖_F` for orthonormal `W`
(arXiv 2107.07282, needed for the corrected Theorems 2 and 3). -/
theorem norm_mul_compress_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {r : Type*} [Fintype r]
    [DecidableEq r] {W : Matrix ι r ℝ} (hW : Wᵀ * W = 1) (y : Matrix p r ℝ) :
    ‖y * (Wᵀ * A * W)‖ ≤ lamMax hA * ‖y‖ := by
  have e : y * (Wᵀ * A * W) = y * Wᵀ * A * W := by simp only [Matrix.mul_assoc]
  rw [e]
  calc ‖y * Wᵀ * A * W‖ ≤ ‖y * Wᵀ * A‖ := norm_mul_orthonormal_le hW _
    _ ≤ lamMax hA * ‖y * Wᵀ‖ := norm_mul_le_lamMax hA _
    _ = lamMax hA * ‖y‖ := by rw [Frobenius.norm_mul_transpose_of_orthonormal hW]

end LamMax

/-! ### Lax–Friedrichs pairs -/

section Pair

variable {m q : Type*} [Fintype m] [DecidableEq m] [Fintype q]

/-- The algebra of `L = L⁽¹⁾` and `M = (Δx/Δt) L⁽²⁾`: `L` is symmetric, `M` is skew, they commute,
and `L² - M² = 1` (the matrix form of `cos² + sin² = 1`). -/
structure IsLFPair (L M : Matrix m m ℝ) : Prop where
  symm : Lᵀ = L
  skew : Mᵀ = -M
  comm : L * M = M * L
  pyth : L * L - M * M = 1

/-- The step `Z ↦ L Z - ν M Z B`. -/
def flow (L M : Matrix m m ℝ) (ν : ℝ) (B : Matrix q q ℝ) (Z : Matrix m q ℝ) : Matrix m q ℝ :=
  L * Z - ν • (M * Z * B)

omit [DecidableEq m] in
/-- `M` commutes with the step (a discrete Fourier multiplier). -/
lemma mul_flow {L M : Matrix m m ℝ} (hcomm : L * M = M * L) (ν : ℝ) (B : Matrix q q ℝ)
    (Z : Matrix m q ℝ) : M * flow L M ν B Z = flow L M ν B (M * Z) := by
  simp only [flow, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm]

namespace IsLFPair

variable {L M : Matrix m m ℝ} (hP : IsLFPair L M)
include hP

/-- `‖L Z‖² + ‖M Z‖² = ‖Z‖²`. -/
lemma norm_sq_add (Z : Matrix m q ℝ) : ‖L * Z‖ ^ 2 + ‖M * Z‖ ^ 2 = ‖Z‖ ^ 2 := by
  have h1 : ‖L * Z‖ ^ 2 = ⟪Z, L * L * Z⟫ := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, hP.symm, Matrix.mul_assoc]
  have h2 : ‖M * Z‖ ^ 2 = -⟪Z, M * M * Z⟫ := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, hP.skew, Matrix.neg_mul,
      inner_neg_right, Matrix.mul_assoc]
  have h3 : ⟪Z, (L * L - M * M) * Z⟫ = ‖Z‖ ^ 2 := by
    rw [hP.pyth, Matrix.one_mul, real_inner_self_eq_norm_sq]
  rw [Matrix.sub_mul, inner_sub_right] at h3
  linarith

lemma skew_mul : (L * M)ᵀ = -(L * M) := by
  rw [Matrix.transpose_mul, hP.symm, hP.skew, Matrix.neg_mul, hP.comm]

/-- The energy identity: the cross term of a Lax–Friedrichs step vanishes. -/
lemma flow_norm_sq {B : Matrix q q ℝ} (hB : Bᵀ = B) (ν : ℝ) (Z : Matrix m q ℝ) :
    ‖flow L M ν B Z‖ ^ 2 = ‖L * Z‖ ^ 2 + ν ^ 2 * ‖M * Z * B‖ ^ 2 := by
  have hc : ⟪L * Z, M * Z * B⟫ = 0 := by
    have e : M * Z * B = M * (Z * B) := Matrix.mul_assoc _ _ _
    rw [e, Frobenius.inner_mul_left, hP.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact inner_skew_symm hP.skew_mul hB Z
  rw [flow, @norm_sub_sq_real, norm_smul, mul_pow, inner_smul_right, hc, Real.norm_eq_abs, sq_abs]
  ring

/-- Damping form of the CFL bound: `‖L Z - ν M Z B‖² ≤ ‖Z‖² - (1 - c²) ‖M Z‖²`. -/
lemma flow_norm_sq_le {B : Matrix q q ℝ} (hB : Bᵀ = B) {ν ρ : ℝ} (hρ : 0 ≤ ρ)
    (hb : ∀ y : Matrix m q ℝ, ‖y * B‖ ≤ ρ * ‖y‖) (Z : Matrix m q ℝ) :
    ‖flow L M ν B Z‖ ^ 2 ≤ ‖Z‖ ^ 2 - (1 - (ν * ρ) ^ 2) * ‖M * Z‖ ^ 2 := by
  have h1 := hP.norm_sq_add Z
  have h2 : ‖M * Z * B‖ ^ 2 ≤ ρ ^ 2 * ‖M * Z‖ ^ 2 := by
    have := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (norm_nonneg _))).2 (hb (M * Z))
    rwa [mul_pow] at this
  rw [hP.flow_norm_sq hB]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ν)]

/-- The Lax–Friedrichs step is a contraction under the CFL condition. -/
lemma flow_norm_le {B : Matrix q q ℝ} (hB : Bᵀ = B) {ν ρ : ℝ} (hρ : 0 ≤ ρ)
    (hb : ∀ y : Matrix m q ℝ, ‖y * B‖ ≤ ρ * ‖y‖) (hc : (ν * ρ) ^ 2 ≤ 1) (Z : Matrix m q ℝ) :
    ‖flow L M ν B Z‖ ≤ ‖Z‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  have h := hP.flow_norm_sq_le hB hρ hb (ν := ν) Z
  have : 0 ≤ (1 - (ν * ρ) ^ 2) * ‖M * Z‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- `flow L M (-ν) B` is the adjoint of `flow L M ν B`. -/
lemma inner_flow {B : Matrix q q ℝ} (hB : Bᵀ = B) (ν : ℝ) (w Z : Matrix m q ℝ) :
    ⟪w, flow L M ν B Z⟫ = ⟪flow L M (-ν) B w, Z⟫ := by
  have h1 : ⟪w, L * Z⟫ = ⟪L * w, Z⟫ := by
    rw [Frobenius.inner_mul_left, hP.symm]
  have h2 : ⟪w, M * Z * B⟫ = -⟪M * w * B, Z⟫ := by
    rw [Frobenius.inner_mul_right', hB, Frobenius.inner_mul_left', hP.skew, Matrix.neg_mul,
      inner_neg_left, ← Matrix.mul_assoc]
  simp only [flow, inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left, h1, h2]
  simp

end IsLFPair

end Pair

/-! ### The periodic Lax–Friedrichs matrices -/

section Periodic

variable (n : ℕ) [NeZero n]

/-- The cyclic shift `(S x)_j = x_{j+1}` on the periodic grid `ZMod n`. -/
def shift : Matrix (ZMod n) (ZMod n) ℝ := Matrix.of fun i j => if j = i + 1 then 1 else 0

variable {n}

lemma shift_mul {q : Type*} (Z : Matrix (ZMod n) q ℝ) (i : ZMod n) (j : q) :
    (shift n * Z) i j = Z (i + 1) j := by
  simp [shift, Matrix.mul_apply]

lemma shift_transpose_mul {q : Type*} (Z : Matrix (ZMod n) q ℝ) (i : ZMod n) (j : q) :
    ((shift n)ᵀ * Z) i j = Z (i - 1) j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, shift, Matrix.of_apply]
  rw [Finset.sum_eq_single (i - 1)]
  · simp
  · intro b _ hb
    have h : ¬ i = b + 1 := fun h => hb (by rw [h]; ring)
    simp [h]
  · simp

lemma shift_mul_transpose : shift n * (shift n)ᵀ = 1 := by
  ext i j
  rw [shift_mul, Matrix.transpose_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [shift, h]
  · simp [shift, h]

lemma shift_transpose_mul_self : (shift n)ᵀ * shift n = 1 := by
  ext i j
  rw [shift_transpose_mul, Matrix.one_apply]
  by_cases h : i = j
  · simp [shift, h]
  · simp [shift, h, Ne.symm h]

variable (n)

/-- `L⁽¹⁾` on the periodic grid: `(L⁽¹⁾ x)_j = (x_{j+1} + x_{j-1}) / 2`. -/
noncomputable def L1 : Matrix (ZMod n) (ZMod n) ℝ := (1 / 2 : ℝ) • (shift n + (shift n)ᵀ)

/-- `L⁽²⁾` for `Δt / Δx = ν` on the periodic grid:
`(L⁽²⁾ x)_j = ν (x_{j+1} - x_{j-1}) / 2`. -/
noncomputable def L2 (ν : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  (ν / 2) • (shift n - (shift n)ᵀ)

variable {n}

omit [NeZero n] in
/-- `L2` is `ν • L2 1`. -/
lemma L2_eq (ν : ℝ) : L2 n ν = ν • L2 n 1 := by
  simp only [L2, smul_smul]
  congr 1
  ring

/-- The columnwise action of `L⁽¹⁾`. -/
lemma L1_mul_apply {q : Type*} (Z : Matrix (ZMod n) q ℝ) (i : ZMod n) (j : q) :
    (L1 n * Z) i j = (Z (i + 1) j + Z (i - 1) j) / 2 := by
  rw [L1, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_apply, Matrix.add_apply, shift_mul,
    shift_transpose_mul, smul_eq_mul]
  ring

/-- The columnwise action of `L⁽²⁾`. -/
lemma L2_mul_apply {q : Type*} (ν : ℝ) (Z : Matrix (ZMod n) q ℝ) (i : ZMod n) (j : q) :
    (L2 n ν * Z) i j = ν / 2 * (Z (i + 1) j - Z (i - 1) j) := by
  rw [L2, Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply, shift_mul,
    shift_transpose_mul, smul_eq_mul]

/-- The periodic matrices form a Lax–Friedrichs pair (arXiv 2107.07282, Sec. 2.2): `L⁽¹⁾` is
symmetric, `L⁽²⁾` is skew, they commute, and `(L⁽¹⁾)² - (L⁽²⁾ / ν)² = I`, which is the matrix
form of `cos² + sin² = 1` for the multipliers `D⁽¹⁾`, `D⁽²⁾` of (6). -/
theorem isLFPair_periodic : IsLFPair (L1 n) (L2 n 1) where
  symm := by simp [L1, add_comm]
  skew := by
    simp only [L2, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
    rw [← smul_neg, neg_sub]
  comm := by
    have h1 := shift_mul_transpose (n := n)
    have h2 := shift_transpose_mul_self (n := n)
    simp only [L1, L2, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, h1, h2]
    module
  pyth := by
    have h1 := shift_mul_transpose (n := n)
    have h2 := shift_transpose_mul_self (n := n)
    simp only [L1, L2, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, h1, h2]
    module

end Periodic

/-! ### Theorem 2: the centered PtD projector-splitting scheme (31) -/

section Scheme31

variable {n : ℕ} [NeZero n] {r K : Type*} [Fintype r] [Fintype K] [DecidableEq r] [DecidableEq K]

/-- One step of the scheme (31) from `uⁿ = Kⁿ Wᵀ`.  `K₀ = Xⁿ Sⁿ`, `W = Wⁿ` and `X₁ = Xⁿ⁺¹`,
`St₀ = S̃ⁿ`, `St₁ = S̃ⁿ⁺¹`, `L₁ = Lⁿ⁺¹`; the next iterate is `uⁿ⁺¹ = X₁ L₁`. -/
structure Scheme31 (ν : ℝ) (A : Matrix K K ℝ) (W : Matrix K r ℝ) (K₀ X₁ : Matrix (ZMod n) r ℝ)
    (St₀ St₁ : Matrix r r ℝ) (L₁ : Matrix r K ℝ) : Prop where
  /-- (31a), with the QR factorisation `Kⁿ⁺¹ = Xⁿ⁺¹ S̃ⁿ`. -/
  kStep : X₁ * St₀ = L1 n * K₀ - L2 n ν * K₀ * (Wᵀ * Aᵀ * W)
  /-- (31b). -/
  sStep : St₁ = St₀ + X₁ᵀ * L2 n ν * X₁ * St₀ * (Wᵀ * Aᵀ * W)
  /-- (31c), with `Lⁿ = S̃ⁿ⁺¹ Wᵀ`. -/
  lStep : L₁ = St₁ * Wᵀ - X₁ᵀ * L2 n ν * X₁ * St₁ * Wᵀ * Aᵀ

omit [Fintype r] [DecidableEq r] [DecidableEq K] in
lemma compress_transpose {A : Matrix K K ℝ} (hA : A.IsHermitian) (W : Matrix K r ℝ) :
    (Wᵀ * Aᵀ * W)ᵀ = Wᵀ * Aᵀ * W := by
  simp [Matrix.transpose_mul, transpose_eq_of_isHermitian hA, Matrix.mul_assoc]

omit [Fintype K] [DecidableEq r] [DecidableEq K] in
/-- The cross term of `Z + ν T Z C` vanishes for skew `T` and symmetric `C`. -/
lemma norm_sq_add_skew {T : Matrix r r ℝ} (hT : Tᵀ = -T) {q : Type*} [Fintype q]
    {C : Matrix q q ℝ} (hC : Cᵀ = C) (ν : ℝ) (Z : Matrix r q ℝ) :
    ‖Z + ν • (T * Z * C)‖ ^ 2 = ‖Z‖ ^ 2 + ν ^ 2 * ‖T * Z * C‖ ^ 2 := by
  rw [@norm_add_sq_real, norm_smul, mul_pow, inner_smul_right, inner_skew_symm hT hC Z,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The real-number core of the proof of `scheme31_stable`. -/
lemma scheme31_arith {a b g c2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hc0 : 0 ≤ c2)
    (hc : 3 * c2 ≤ 1) (hab : 0 ≤ a - (1 - c2) * b) (hcs : a ^ 2 ≤ (a - (1 - c2) * b) * g) :
    2 * c2 * a + c2 ^ 2 * b ≤ (1 - c2) * g := by
  rcases eq_or_lt_of_le hab with h0 | hpos
  · have ha0 : a = 0 := by
      have : a ^ 2 ≤ 0 := by rw [← h0] at hcs; simpa using hcs
      nlinarith [sq_nonneg a]
    have hb0 : (1 - c2) * b = 0 := by linarith
    have hd : 1 - c2 ≠ 0 := by intro h; linarith
    have hb0' : b = 0 := by simpa [hd] using hb0
    subst ha0 hb0'
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hpos
    have hkey : (a - (1 - c2) * b) * (2 * c2 * a + c2 ^ 2 * b) ≤ (1 - c2) * a ^ 2 := by
      have t1 : 0 ≤ (1 - 3 * c2) * a ^ 2 := mul_nonneg (by linarith) (sq_nonneg a)
      have t2 : 0 ≤ c2 * (2 - 3 * c2) * (a * b) :=
        mul_nonneg (mul_nonneg hc0 (by linarith)) (mul_nonneg ha hb)
      have t3 : 0 ≤ c2 ^ 2 * (1 - c2) * b ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg b)
      nlinarith
    have hd : 0 ≤ 1 - c2 := by linarith
    calc (a - (1 - c2) * b) * (2 * c2 * a + c2 ^ 2 * b) ≤ (1 - c2) * a ^ 2 := hkey
      _ ≤ (1 - c2) * ((a - (1 - c2) * b) * g) := mul_le_mul_of_nonneg_left hcs hd
      _ = (a - (1 - c2) * b) * ((1 - c2) * g) := by ring

lemma sq_amp {x y ν ρ : ℝ} (hx : 0 ≤ x) (h : x ≤ ρ * y) :
    ν ^ 2 * x ^ 2 ≤ (ν * ρ) ^ 2 * y ^ 2 := by
  have h1 : x ^ 2 ≤ (ρ * y) ^ 2 := pow_le_pow_left₀ hx h 2
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ν)
  calc ν ^ 2 * x ^ 2 ≤ ν ^ 2 * (ρ * y) ^ 2 := h2
    _ = (ν * ρ) ^ 2 * y ^ 2 := by ring

omit [DecidableEq K] in
/-- The abstract core of Theorem 2 of arXiv 2107.07282, for a new proof: for a Lax–Friedrichs pair
`L, M`, symmetric `B`, `C` with `‖y B‖ ≤ ρ ‖y‖`, `‖y C‖ ≤ ρ ‖y‖` and `3 (ν ρ)² ≤ 1`, the K-step
dissipates enough energy to pay for the amplification in the S- and L-steps. -/
theorem core31 {m : Type*} [Fintype m] [DecidableEq m] {L M : Matrix m m ℝ} (hP : IsLFPair L M)
    {B : Matrix r r ℝ} (hBt : Bᵀ = B) {C : Matrix K K ℝ} (hCt : Cᵀ = C) {ρ ν : ℝ} (hρ : 0 ≤ ρ)
    (hc3 : 3 * (ν * ρ) ^ 2 ≤ 1) (hbm : ∀ y : Matrix m r ℝ, ‖y * B‖ ≤ ρ * ‖y‖)
    (hbr : ∀ y : Matrix r r ℝ, ‖y * B‖ ≤ ρ * ‖y‖) (hbk : ∀ y : Matrix r K ℝ, ‖y * C‖ ≤ ρ * ‖y‖)
    {W : Matrix K r ℝ} (hW : Wᵀ * W = 1) {K₀ X₁ : Matrix m r ℝ} (hX₁ : X₁ᵀ * X₁ = 1)
    {St₀ St₁ : Matrix r r ℝ} {L₁ : Matrix r K ℝ} (hK : X₁ * St₀ = flow L M ν B K₀)
    (hS : St₁ = St₀ + ν • (X₁ᵀ * M * X₁ * St₀ * B))
    (hL : L₁ = St₁ * Wᵀ + (-ν) • (X₁ᵀ * M * X₁ * (St₁ * Wᵀ) * C)) :
    ‖L₁‖ ^ 2 ≤ ‖K₀‖ ^ 2 := by
  obtain ⟨T, hTdef⟩ : ∃ T, T = X₁ᵀ * M * X₁ := ⟨_, rfl⟩
  rw [← hTdef] at hS hL
  have hT : Tᵀ = -T := by
    simp only [hTdef, Matrix.transpose_mul, Matrix.transpose_transpose, hP.skew, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.mul_assoc]
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = (ν * ρ) ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c2 := hc2 ▸ sq_nonneg _
  rw [← hc2] at hc3
  -- the L-step
  have hA' : ‖L₁‖ ^ 2 ≤ ‖St₁‖ ^ 2 + c2 * ‖T * St₁‖ ^ 2 := by
    have e : T * (St₁ * Wᵀ) = (T * St₁) * Wᵀ := (Matrix.mul_assoc _ _ _).symm
    have h := sq_amp (ν := ν) (norm_nonneg _) (hbk (T * (St₁ * Wᵀ)))
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hW, ← hc2] at h
    rw [hL, norm_sq_add_skew hT hCt, Frobenius.norm_mul_transpose_of_orthonormal hW, e, neg_sq]
    linarith
  -- the S-step
  have hB' : ‖St₁‖ ^ 2 ≤ ‖St₀‖ ^ 2 + c2 * ‖T * St₀‖ ^ 2 := by
    have h := sq_amp (ν := ν) (norm_nonneg _) (hbr (T * St₀))
    rw [← hc2] at h
    rw [hS, norm_sq_add_skew hT hBt]
    linarith
  -- `T` applied to the S-step
  obtain ⟨y, hy⟩ : ∃ y, y = T * St₀ := ⟨_, rfl⟩
  have hC' : ‖T * St₁‖ ^ 2 ≤ ‖y‖ ^ 2 + c2 * ‖T * y‖ ^ 2 := by
    have e : T * St₁ = y + ν • (T * y * B) := by
      rw [hS, Matrix.mul_add, Matrix.mul_smul, hy]
      simp only [Matrix.mul_assoc]
    have h := sq_amp (ν := ν) (norm_nonneg _) (hbr (T * y))
    rw [← hc2] at h
    rw [e, norm_sq_add_skew hT hBt]
    linarith
  obtain ⟨w, hw⟩ : ∃ w, w = X₁ * y := ⟨_, rfl⟩
  have hwn : ‖w‖ = ‖y‖ := hw ▸ Frobenius.norm_mul_of_orthonormal hX₁ y
  have hD : ‖T * y‖ ≤ ‖M * w‖ := by
    have e : T * y = X₁ᵀ * (M * w) := by
      simp only [hTdef, hw, Matrix.mul_assoc]
    rw [e]
    exact norm_transpose_mul_le hX₁ _
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = X₁ * St₀ := ⟨_, rfl⟩
  rw [← hYdef] at hK
  have hE : ⟪w, M * Y⟫ = ‖y‖ ^ 2 := by
    rw [hw, Frobenius.inner_mul_left, ← real_inner_self_eq_norm_sq]
    congr 1
    simp only [hy, hTdef, hYdef, Matrix.mul_assoc]
  obtain ⟨G, hG⟩ : ∃ G, G = M * K₀ := ⟨_, rfl⟩
  have hF : ⟪w, M * Y⟫ = ⟪flow L M (-ν) B w, G⟫ := by
    rw [hK, mul_flow hP.comm, hP.inner_flow hBt, hG]
  have hρ2 : (-ν * ρ) ^ 2 = c2 := by rw [hc2]; ring
  have hGG := hP.flow_norm_sq_le hBt hρ hbm (ν := -ν) w
  rw [hρ2, hwn] at hGG
  have hHH := hP.flow_norm_sq_le hBt hρ hbm (ν := ν) K₀
  rw [← hK, ← hc2, ← hG] at hHH
  have hab : 0 ≤ ‖y‖ ^ 2 - (1 - c2) * ‖M * w‖ ^ 2 := (sq_nonneg _).trans hGG
  have hcs : (‖y‖ ^ 2) ^ 2 ≤ (‖y‖ ^ 2 - (1 - c2) * ‖M * w‖ ^ 2) * ‖G‖ ^ 2 := by
    have h1 : ‖y‖ ^ 2 ≤ ‖flow L M (-ν) B w‖ * ‖G‖ := by
      rw [← hE, hF]
      exact real_inner_le_norm _ _
    calc (‖y‖ ^ 2) ^ 2 ≤ (‖flow L M (-ν) B w‖ * ‖G‖) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ = ‖flow L M (-ν) B w‖ ^ 2 * ‖G‖ ^ 2 := by rw [mul_pow]
      _ ≤ (‖y‖ ^ 2 - (1 - c2) * ‖M * w‖ ^ 2) * ‖G‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hGG (sq_nonneg _)
  have hmain := scheme31_arith (sq_nonneg ‖y‖) (sq_nonneg ‖M * w‖) (sq_nonneg ‖G‖) hc0 hc3 hab hcs
  have hYn : ‖Y‖ = ‖St₀‖ := hYdef ▸ Frobenius.norm_mul_of_orthonormal hX₁ St₀
  have hTy : ‖T * y‖ ^ 2 ≤ ‖M * w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have h1 := mul_le_mul_of_nonneg_left hC' hc0
  have h2 := mul_le_mul_of_nonneg_left hTy (mul_nonneg hc0 hc0)
  rw [hYn] at hHH
  rw [← hy] at hB'
  nlinarith

/-- **Theorem 2, corrected** (arXiv 2107.07282).  If `λ_max(A) Δt / Δx ≤ 1/√3`, then the scheme (31)
satisfies `‖uⁿ⁺¹‖_F ≤ ‖uⁿ‖_F` for every low-rank state and all bases.  There are two differences
from the paper.  The CFL condition uses `A` and not `Ã`; with `Ã` the statement is false
(`scheme31_literal_false`).  The proof is new (`core31`), since the paper's proof is only valid
for a single Fourier mode.  The result holds for general states, and `1/√3` is sharp
(`scheme31_sharp`). -/
theorem scheme31_stable {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (hcfl : ν * lamMax hA ≤ 1 / √3) {W : Matrix K r ℝ} (hW : Wᵀ * W = 1)
    {K₀ X₁ : Matrix (ZMod n) r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {St₀ St₁ : Matrix r r ℝ}
    {L₁ : Matrix r K ℝ} (hs : Scheme31 ν A W K₀ X₁ St₀ St₁ L₁) :
    ‖X₁ * L₁‖ ≤ ‖K₀ * Wᵀ‖ := by
  have hρ : 0 ≤ lamMax hA := lamMax_nonneg hA
  have hAt : Aᵀ = A := transpose_eq_of_isHermitian hA
  have hc3 : 3 * (ν * lamMax hA) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ ν * lamMax hA := mul_nonneg hν hρ
    have h1 : (ν * lamMax hA) ^ 2 ≤ (1 / √3) ^ 2 := pow_le_pow_left₀ h0 hcfl 2
    rw [div_pow, Real.sq_sqrt (by norm_num)] at h1
    linarith
  have hL2 : L2 n ν = ν • L2 n 1 := L2_eq ν
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Frobenius.norm_mul_of_orthonormal hX₁, Frobenius.norm_mul_transpose_of_orthonormal hW]
  have hb1 : ∀ y : Matrix (ZMod n) r ℝ, ‖y * (Wᵀ * Aᵀ * W)‖ ≤ lamMax hA * ‖y‖ := fun y => by
    rw [hAt]; exact norm_mul_compress_le hA hW y
  have hb2 : ∀ y : Matrix r r ℝ, ‖y * (Wᵀ * Aᵀ * W)‖ ≤ lamMax hA * ‖y‖ := fun y => by
    rw [hAt]; exact norm_mul_compress_le hA hW y
  have hb3 : ∀ y : Matrix r K ℝ, ‖y * Aᵀ‖ ≤ lamMax hA * ‖y‖ := fun y => by
    rw [hAt]; exact norm_mul_le_lamMax hA y
  refine core31 (St₀ := St₀) (St₁ := St₁) (isLFPair_periodic (n := n)) (compress_transpose hA W)
    (by rw [hAt, hAt]) hρ hc3 hb1 hb2 hb3 hW hX₁ ?_ ?_ ?_
  · rw [hs.kStep, hL2, flow, Matrix.smul_mul, Matrix.smul_mul]
  · rw [hs.sStep, hL2]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  · rw [hs.lStep, hL2, neg_smul, sub_eq_add_neg]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

end Scheme31

/-! ### Fourier modes on the periodic grid -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- `cs x = Re e^{2π i x / n}`. -/
noncomputable def cs (x : ZMod n) : ℝ := (ZMod.stdAddChar x : ℂ).re

/-- `sn x = Im e^{2π i x / n}`. -/
noncomputable def sn (x : ZMod n) : ℝ := (ZMod.stdAddChar x : ℂ).im

/-- The angle `θ_α = α π Δx = 2 π α / n` of the wave number `α` (for `Δx = 2 / n`). -/
noncomputable def angle (α : ZMod n) : ℝ := 2 * Real.pi * α.val / n

lemma stdAddChar_eq (α : ZMod n) :
    (ZMod.stdAddChar α : ℂ) = Complex.exp ((angle α : ℝ) * Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := n) (α.val : ℤ)
  have e : (((α.val : ℤ) : ZMod n)) = α := by simp
  rw [e] at h
  rw [h, angle]
  congr 1
  push_cast
  ring

lemma stdAddChar_eq_cs_sn (x : ZMod n) :
    (ZMod.stdAddChar x : ℂ) = (cs x : ℂ) + (sn x : ℂ) * Complex.I := by
  simp [cs, sn, Complex.re_add_im]

lemma cs_eq_cos (α : ZMod n) : cs α = Real.cos (angle α) := by
  rw [cs, stdAddChar_eq, Complex.exp_ofReal_mul_I_re]

lemma sn_eq_sin (α : ZMod n) : sn α = Real.sin (angle α) := by
  rw [sn, stdAddChar_eq, Complex.exp_ofReal_mul_I_im]

lemma cs_sq_add_sn_sq (x : ZMod n) : cs x ^ 2 + sn x ^ 2 = 1 := by
  rw [cs_eq_cos, sn_eq_sin, Real.cos_sq_add_sin_sq]

lemma cs_add (x y : ZMod n) : cs (x + y) = cs x * cs y - sn x * sn y := by
  simp [cs, sn, AddChar.map_add_eq_mul, Complex.mul_re]

lemma sn_add (x y : ZMod n) : sn (x + y) = cs x * sn y + sn x * cs y := by
  simp [cs, sn, AddChar.map_add_eq_mul, Complex.mul_im]

lemma cs_neg (x : ZMod n) : cs (-x) = cs x := by
  have h : (ZMod.stdAddChar (-x) : ℂ) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
    rw [AddChar.map_neg_eq_conj]
  simp [cs, h]

lemma sn_neg (x : ZMod n) : sn (-x) = -sn x := by
  have h : (ZMod.stdAddChar (-x) : ℂ) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
    rw [AddChar.map_neg_eq_conj]
  simp [sn, h]

/-- The real Fourier plane of the wave number `α`: its columns are `(cos θ_α j)_j`, `(sin θ_α j)_j`
(up to `j ↦ α j` the columns of `Eₓ` split into real and imaginary parts). -/
noncomputable def plane (α : ZMod n) : Matrix (ZMod n) (Fin 2) ℝ :=
  Matrix.of fun j i => ![cs (α * j), sn (α * j)] i

/-- The quarter turn `J`, with `Jᵀ = -J`, `J² = -1`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

lemma L1_mul_plane (α : ZMod n) : L1 n * plane α = cs α • plane α := by
  ext j i
  rw [L1_mul_apply]
  have e1 : α * (j + 1) = α * j + α := by ring
  have e2 : α * (j - 1) = α * j + -α := by ring
  fin_cases i
  · simp only [plane, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, e1, e2, cs_add, cs_neg,
      sn_neg, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    ring
  · simp only [plane, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, e1, e2, sn_add, cs_neg,
      sn_neg, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

lemma L2_mul_plane (ν : ℝ) (α : ZMod n) : L2 n ν * plane α = (ν * sn α) • (plane α * J) := by
  ext j i
  rw [L2_mul_apply]
  have e1 : α * (j + 1) = α * j + α := by ring
  have e2 : α * (j - 1) = α * j + -α := by ring
  fin_cases i
  · simp [plane, J, Matrix.mul_apply, Fin.sum_univ_two, e1, e2, cs_add, cs_neg, sn_neg]
    ring
  · simp [plane, J, Matrix.mul_apply, Fin.sum_univ_two, e1, e2, sn_add, cs_neg, sn_neg]
    ring

/-- The sum of `e^{2 i θ_α j}` vanishes unless `2 α = 0`. -/
lemma sum_double {α : ZMod n} (hα : 2 * α ≠ 0) :
    ∑ j, (cs (α * j) ^ 2 - sn (α * j) ^ 2) = 0 ∧ ∑ j, cs (α * j) * sn (α * j) = 0 := by
  have h := AddChar.sum_mulShift (R := ZMod n) (R' := ℂ) (ψ := ZMod.stdAddChar) (2 * α)
    (ZMod.isPrimitive_stdAddChar n)
  simp only [hα, ↓reduceIte, Nat.cast_zero] at h
  have e : ∀ x : ZMod n, (ZMod.stdAddChar (x * (2 * α)) : ℂ) =
      ((cs (α * x) ^ 2 - sn (α * x) ^ 2 : ℝ) : ℂ) +
        ((2 * (cs (α * x) * sn (α * x)) : ℝ) : ℂ) * Complex.I := by
    intro x
    have e1 : x * (2 * α) = α * x + α * x := by ring
    rw [e1, AddChar.map_add_eq_mul, stdAddChar_eq_cs_sn]
    have hI := Complex.I_sq
    push_cast
    linear_combination ((sn (α * x) : ℂ) ^ 2) * hI
  simp only [e] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add, Complex.zero_re, Complex.zero_im] at hre him
  refine ⟨hre, ?_⟩
  rw [← Finset.mul_sum] at him
  simpa using him

/-- The sum of the moduli. -/
lemma sum_cs_sq_add (α : ZMod n) : ∑ j, (cs (α * j) ^ 2 + sn (α * j) ^ 2) = n := by
  simp [cs_sq_add_sn_sq, ZMod.card]

/-- The normalised Fourier plane. -/
noncomputable def planeU (α : ZMod n) : Matrix (ZMod n) (Fin 2) ℝ := √(2 / n) • plane α

lemma n_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

lemma planeU_orthonormal {α : ZMod n} (hα : 2 * α ≠ 0) : (planeU α)ᵀ * planeU α = 1 := by
  obtain ⟨h1, h2⟩ := sum_double hα
  have h3 := sum_cs_sq_add α
  have hadd := Finset.sum_add_distrib (s := Finset.univ) (f := fun j => cs (α * j) ^ 2)
    (g := fun j => sn (α * j) ^ 2)
  have hsub := Finset.sum_sub_distrib (s := Finset.univ) (f := fun j => cs (α * j) ^ 2)
    (g := fun j => sn (α * j) ^ 2)
  rw [h1] at hsub
  rw [h3] at hadd
  have hc : ∑ j, cs (α * j) * cs (α * j) = n / 2 := by
    simp only [← pow_two]
    linarith
  have hs : ∑ j, sn (α * j) * sn (α * j) = n / 2 := by
    simp only [← pow_two]
    linarith
  have h2' : ∑ j, sn (α * j) * cs (α * j) = 0 := by
    simpa [mul_comm] using h2
  have hsq : √(2 / (n : ℝ)) * √(2 / (n : ℝ)) = 2 / n := Real.mul_self_sqrt (by positivity)
  have hn := (n_pos (n := n)).ne'
  have hp : (plane α)ᵀ * plane α = ((n : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i k
    fin_cases i <;> fin_cases k
    · simpa [plane, Matrix.mul_apply] using hc
    · simpa [plane, Matrix.mul_apply] using h2
    · simpa [plane, Matrix.mul_apply] using h2'
    · simpa [plane, Matrix.mul_apply] using hs
  rw [planeU, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, hp,
    smul_smul]
  have : 2 / (n : ℝ) * (n / 2) = 1 := by field_simp
  rw [this, one_smul]

lemma L1_mul_planeU (α : ZMod n) : L1 n * planeU α = cs α • planeU α := by
  rw [planeU, Matrix.mul_smul, L1_mul_plane, smul_comm]

lemma L2_mul_planeU (ν : ℝ) (α : ZMod n) :
    L2 n ν * planeU α = (ν * sn α) • (planeU α * J) := by
  rw [planeU, Matrix.mul_smul, L2_mul_plane, Matrix.smul_mul, smul_comm]

/-! #### Discrete Fourier transform and Parseval's identity -/

/-- The discrete Fourier transform `x̂(α) = ∑_j x_j e^{-i θ_α j}` of a real grid function. -/
noncomputable def hat (x : ZMod n → ℝ) (α : ZMod n) : ℂ :=
  ∑ j, (x j : ℂ) * ZMod.stdAddChar (-(α * j))

/-- **Parseval's identity** on the periodic grid. -/
lemma parseval (x : ZMod n → ℝ) :
    ∑ α, Complex.normSq (hat x α) = n * ∑ j, x j ^ 2 := by
  have key : ∀ j k : ZMod n, ∑ α : ZMod n, (ZMod.stdAddChar (α * (k - j)) : ℂ) =
      if k - j = 0 then (n : ℂ) else 0 := by
    intro j k
    have := AddChar.sum_mulShift (R := ZMod n) (R' := ℂ) (ψ := ZMod.stdAddChar) (k - j)
      (ZMod.isPrimitive_stdAddChar n)
    simpa [ZMod.card] using this
  have hexp : ∀ α, ((Complex.normSq (hat x α) : ℝ) : ℂ) =
      ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * ZMod.stdAddChar (α * (k - j)) := by
    intro α
    rw [← Complex.mul_conj, hat, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, neg_neg]
    have e : α * (k - j) = -(α * j) + α * k := by ring
    rw [e, AddChar.map_add_eq_mul]
    ring
  apply Complex.ofReal_injective
  push_cast
  simp only [hexp]
  calc ∑ α : ZMod n, ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * ZMod.stdAddChar (α * (k - j))
      = ∑ j, ∑ k, ∑ α : ZMod n, (x j : ℂ) * (x k : ℂ) * ZMod.stdAddChar (α * (k - j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ k, (x j : ℂ) * (x k : ℂ) * (if k - j = 0 then (n : ℂ) else 0) := by
        simp only [← Finset.mul_sum, key]
    _ = ∑ j, (x j : ℂ) * (x j : ℂ) * n := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [sub_eq_zero]
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
    _ = n * ∑ j, (x j : ℂ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- The transform of a shifted grid function. -/
lemma hat_shift (x : ZMod n → ℝ) (d α : ZMod n) :
    hat (fun j => x (j + d)) α = ZMod.stdAddChar (α * d) * hat x α := by
  rw [hat, hat, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight d) (fun j => (ZMod.stdAddChar (α * d) : ℂ) *
    ((x j : ℂ) * ZMod.stdAddChar (-(α * j))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : -(α * j) = α * d + -(α * (j + d)) := by ring
  simp only [Equiv.coe_addRight]
  rw [e, AddChar.map_add_eq_mul]
  ring

lemma hat_shift_neg (x : ZMod n → ℝ) (α : ZMod n) :
    hat (fun j => x (j - 1)) α = ZMod.stdAddChar (-α) * hat x α := by
  simpa [sub_eq_add_neg] using hat_shift x (-1) α

lemma hat_shift_one (x : ZMod n → ℝ) (α : ZMod n) :
    hat (fun j => x (j + 1)) α = ZMod.stdAddChar α * hat x α := by
  simpa using hat_shift x 1 α

/-- `(L⁽¹⁾ x)^(α) = cos θ_α x̂(α)`: the entries `D⁽¹⁾_{αα}`. -/
lemma hat_L1 (x : ZMod n → ℝ) (α : ZMod n) :
    hat (fun j => (x (j + 1) + x (j - 1)) / 2) α = (cs α : ℂ) * hat x α := by
  have e : hat (fun j => (x (j + 1) + x (j - 1)) / 2) α =
      (hat (fun j => x (j + 1)) α + hat (fun j => x (j - 1)) α) / 2 := by
    simp only [hat, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, hat_shift_one, hat_shift_neg, stdAddChar_eq_cs_sn, stdAddChar_eq_cs_sn, cs_neg, sn_neg]
  push_cast
  ring

/-- `(M x)^(α) = i sin θ_α x̂(α)`: the entries `D⁽²⁾_{αα}` for `ν = 1`. -/
lemma hat_M (x : ZMod n → ℝ) (α : ZMod n) :
    hat (fun j => (x (j + 1) - x (j - 1)) / 2) α = (sn α : ℂ) * Complex.I * hat x α := by
  have e : hat (fun j => (x (j + 1) - x (j - 1)) / 2) α =
      (hat (fun j => x (j + 1)) α - hat (fun j => x (j - 1)) α) / 2 := by
    simp only [hat, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, hat_shift_one, hat_shift_neg, stdAddChar_eq_cs_sn, stdAddChar_eq_cs_sn, cs_neg, sn_neg]
  push_cast
  ring

/-- The columnwise bound: Parseval turns the two sums into a sum over wave numbers. -/
lemma column_bound (x : ZMod n → ℝ) {c2 g2 : ℝ}
    (hg : ∀ α : ZMod n, cs α ^ 2 + c2 * sn α ^ 2 ≤ g2) :
    ∑ j, ((x (j + 1) + x (j - 1)) / 2) ^ 2 + c2 * ∑ j, ((x (j + 1) - x (j - 1)) / 2) ^ 2
      ≤ g2 * ∑ j, x j ^ 2 := by
  have hn := n_pos (n := n)
  have h1 := parseval (fun j => (x (j + 1) + x (j - 1)) / 2)
  have h2 := parseval (fun j => (x (j + 1) - x (j - 1)) / 2)
  have h3 := parseval x
  simp only [hat_L1, hat_M, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I,
    mul_one] at h1 h2
  refine le_of_mul_le_mul_left ?_ hn
  calc (n : ℝ) * (∑ j, ((x (j + 1) + x (j - 1)) / 2) ^ 2 +
        c2 * ∑ j, ((x (j + 1) - x (j - 1)) / 2) ^ 2)
      = ∑ α, (cs α ^ 2 + c2 * sn α ^ 2) * Complex.normSq (hat x α) := by
        rw [mul_add, mul_left_comm, ← h1, ← h2, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun α _ => by ring
    _ ≤ ∑ α, g2 * Complex.normSq (hat x α) :=
        Finset.sum_le_sum fun α _ =>
          mul_le_mul_of_nonneg_right (hg α) (Complex.normSq_nonneg _)
    _ = (n : ℝ) * (g2 * ∑ j, x j ^ 2) := by
        rw [← Finset.mul_sum, h3]
        ring

/-- The matrix form of `column_bound`. -/
lemma L1_L2_bound {q : Type*} [Fintype q] (u : Matrix (ZMod n) q ℝ) {c2 g2 : ℝ}
    (hg : ∀ α : ZMod n, cs α ^ 2 + c2 * sn α ^ 2 ≤ g2) :
    ‖L1 n * u‖ ^ 2 + c2 * ‖L2 n 1 * u‖ ^ 2 ≤ g2 * ‖u‖ ^ 2 := by
  simp only [Frobenius.norm_sq_eq_sum, L1_mul_apply, L2_mul_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => (1 / 2 * (u (i + 1) j - u (i - 1) j)) ^ 2),
    Finset.sum_comm (f := fun i j => u i j ^ 2), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have := column_bound (fun j => u j k) hg
  have e : ∀ j, (1 / 2 * (u (j + 1) k - u (j - 1) k)) ^ 2 = ((u (j + 1) k - u (j - 1) k) / 2) ^ 2 :=
    fun j => by ring
  simpa only [e] using this

lemma cs_zero : cs (0 : ZMod n) = 1 := by simp [cs]

omit [NeZero n] in
lemma two_ne_zero_of_three_le (hn : 3 ≤ n) : 2 * (1 : ZMod n) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by simpa using h
  have := (ZMod.natCast_eq_zero_iff 2 n).1 h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma sn_one_pos (hn : 3 ≤ n) : 0 < sn (1 : ZMod n) := by
  have hv : (1 : ZMod n).val = 1 := by
    exact ZMod.val_one'' (by omega)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.pi_pos
  rw [sn_eq_sin, angle, hv]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [Nat.cast_one, mul_one, div_lt_iff₀ (by linarith)]
    nlinarith

end Fourier

/-! ### Section 2.2: the full Lax–Friedrichs scheme -/

section FullScheme

variable {n : ℕ} [NeZero n] {K : Type*} [Fintype K]

/-- The full scheme (4): `uⁿ⁺¹ = L⁽¹⁾ uⁿ - L⁽²⁾ uⁿ Aᵀ`. -/
noncomputable def lfStep (ν : ℝ) (A : Matrix K K ℝ) (u : Matrix (ZMod n) K ℝ) :
    Matrix (ZMod n) K ℝ :=
  L1 n * u - L2 n ν * u * Aᵀ

lemma lfStep_eq_flow (ν : ℝ) (A : Matrix K K ℝ) (u : Matrix (ZMod n) K ℝ) :
    lfStep ν A u = flow (L1 n) (L2 n 1) ν Aᵀ u := by
  rw [lfStep, flow, L2_eq ν, Matrix.smul_mul, Matrix.smul_mul]

/-- The scheme (4) of arXiv 2107.07282 written out: with `ν = Δt / Δx` this is the Euler step of
(2), `uⱼⁿ⁺¹ = (uⱼ₋₁ + uⱼ₊₁) / 2 - (Δt / (2 Δx)) A (uⱼ₊₁ - uⱼ₋₁)`, on the periodic grid. -/
theorem lfStep_apply (ν : ℝ) (A : Matrix K K ℝ) (u : Matrix (ZMod n) K ℝ) (j : ZMod n) (k : K) :
    lfStep ν A u j k =
      (u (j - 1) k + u (j + 1) k) / 2 - ν / 2 * ∑ l, A k l * (u (j + 1) l - u (j - 1) l) := by
  rw [lfStep, Matrix.sub_apply, L1_mul_apply, Matrix.mul_apply, Finset.mul_sum]
  simp only [L2_mul_apply, Matrix.transpose_apply]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun l _ => by ring

/-- **Energy identity for the scheme (4)** (arXiv 2107.07282, Sec. 2.2, without the Fourier
transform).  For symmetric `A` the cross term vanishes, because `L⁽¹⁾` is symmetric, `L⁽²⁾` is skew
and they commute. -/
theorem lfStep_norm_sq (ν : ℝ) {A : Matrix K K ℝ} (hA : Aᵀ = A) (u : Matrix (ZMod n) K ℝ) :
    ‖lfStep ν A u‖ ^ 2 = ‖L1 n * u‖ ^ 2 + ‖L2 n ν * u * A‖ ^ 2 := by
  have hAt : Aᵀᵀ = Aᵀ := by rw [hA, hA]
  rw [lfStep_eq_flow, (isLFPair_periodic (n := n)).flow_norm_sq hAt, L2_eq ν, Matrix.smul_mul,
    Matrix.smul_mul, norm_smul, hA, mul_pow, Real.norm_eq_abs, sq_abs]

variable [DecidableEq K]

/-- `‖y Aᵀ‖ ≤ λ_max(A) ‖y‖`. -/
lemma norm_mul_transpose_le {p : Type*} [Fintype p] {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (y : Matrix p K ℝ) : ‖y * Aᵀ‖ ≤ lamMax hA * ‖y‖ := by
  rw [transpose_eq_of_isHermitian hA]
  exact norm_mul_le_lamMax hA y

/-- **`L²`-stability of the full scheme under the classical CFL condition**
(arXiv 2107.07282, Sec. 2.2): `λ_max(A) Δt / Δx ≤ 1` gives `‖uⁿ⁺¹‖_F ≤ ‖uⁿ‖_F`.  The matrices are
the periodic ones, as the Fourier ansatz (6) of the paper requires, and `A` is symmetric. -/
theorem lfStep_norm_le {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (hc : ν * lamMax hA ≤ 1) (u : Matrix (ZMod n) K ℝ) : ‖lfStep ν A u‖ ≤ ‖u‖ := by
  have hAt : Aᵀᵀ = Aᵀ := by rw [transpose_eq_of_isHermitian hA, transpose_eq_of_isHermitian hA]
  rw [lfStep_eq_flow]
  have h0 : 0 ≤ ν * lamMax hA := mul_nonneg hν (lamMax_nonneg hA)
  exact (isLFPair_periodic (n := n)).flow_norm_le hAt (lamMax_nonneg hA)
    (norm_mul_transpose_le hA) (by nlinarith) u

/-- The amplification factor `√(cos²(α π Δx) + c² sin²(α π Δx))` of the wave number `α`. -/
noncomputable def ampl (c : ℝ) (α : ZMod n) : ℝ :=
  √(Real.cos (angle α) ^ 2 + c ^ 2 * Real.sin (angle α) ^ 2)

lemma ampl_sq (c : ℝ) (α : ZMod n) : ampl c α ^ 2 = cs α ^ 2 + c ^ 2 * sn α ^ 2 := by
  rw [ampl, Real.sq_sqrt (by positivity), cs_eq_cos, sn_eq_sin]

omit [Fintype K] [DecidableEq K] in
lemma norm_sq_vecMulVec [Fintype K] (f : ZMod n → ℝ) (a : K → ℝ) :
    ‖Matrix.vecMulVec f a‖ ^ 2 = (∑ j, f j ^ 2) * ∑ k, a k ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.vecMulVec_apply, mul_pow]

omit [NeZero n] [DecidableEq K] in
lemma vecMulVec_mul_transpose {A : Matrix K K ℝ} {a : K → ℝ} {lam : ℝ}
    (ha : A.mulVec a = lam • a) (f : ZMod n → ℝ) :
    Matrix.vecMulVec f a * Aᵀ = lam • Matrix.vecMulVec f a := by
  ext j k
  have h := congrFun ha k
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  calc ∑ l, f j * a l * A k l = f j * ∑ l, A k l * a l := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    _ = lam * (f j * a k) := by rw [h]; ring

omit [DecidableEq K] in
/-- The step on `f aᵀ` for an eigenvector `a`. -/
lemma lfStep_vecMulVec (ν : ℝ) {A : Matrix K K ℝ} {a : K → ℝ} {lam : ℝ}
    (ha : A.mulVec a = lam • a) (f : ZMod n → ℝ) :
    lfStep ν A (Matrix.vecMulVec f a) = Matrix.vecMulVec
      (fun j => (f (j + 1) + f (j - 1)) / 2 - ν * lam * ((f (j + 1) - f (j - 1)) / 2)) a := by
  ext j k
  rw [lfStep, Matrix.mul_assoc, vecMulVec_mul_transpose ha, Matrix.sub_apply, L1_mul_apply,
    Matrix.mul_smul, Matrix.smul_apply, L2_mul_apply]
  simp only [Matrix.vecMulVec_apply, smul_eq_mul]
  ring

omit [DecidableEq K] in
/-- Every wave number `α` and eigenpair `(lam, a)` give a state amplified at least by the factor
`√(cos² θ_α + (ν lam)² sin² θ_α)`: the two real parts `cos(θ_α j) aᵀ`, `sin(θ_α j) aᵀ` of the mode
share the amplification. -/
lemma exists_mode_ge (ν : ℝ) {A : Matrix K K ℝ} {a : K → ℝ} {lam : ℝ} (ha0 : a ≠ 0)
    (ha : A.mulVec a = lam • a) (α : ZMod n) :
    ∃ u : Matrix (ZMod n) K ℝ, u ≠ 0 ∧
      (cs α ^ 2 + (ν * lam) ^ 2 * sn α ^ 2) * ‖u‖ ^ 2 ≤ ‖lfStep ν A u‖ ^ 2 := by
  set u₁ : Matrix (ZMod n) K ℝ := Matrix.vecMulVec (fun j => cs (α * j)) a with hu₁
  set u₂ : Matrix (ZMod n) K ℝ := Matrix.vecMulVec (fun j => sn (α * j)) a with hu₂
  set G := cs α ^ 2 + (ν * lam) ^ 2 * sn α ^ 2 with hG
  set κ := ν * lam * sn α with hκ
  have e1 : α * (1 : ZMod n) = α := mul_one α
  have s1 : ∀ j : ZMod n, (cs (α * (j + 1)) + cs (α * (j - 1))) / 2 - ν * lam *
      ((cs (α * (j + 1)) - cs (α * (j - 1))) / 2) = cs α * cs (α * j) + κ * sn (α * j) := by
    intro j
    have h1 : α * (j + 1) = α * j + α := by ring
    have h2 : α * (j - 1) = α * j + -α := by ring
    rw [h1, h2, cs_add, cs_add, cs_neg, sn_neg, hκ]
    ring
  have s2 : ∀ j : ZMod n, (sn (α * (j + 1)) + sn (α * (j - 1))) / 2 - ν * lam *
      ((sn (α * (j + 1)) - sn (α * (j - 1))) / 2) = cs α * sn (α * j) - κ * cs (α * j) := by
    intro j
    have h1 : α * (j + 1) = α * j + α := by ring
    have h2 : α * (j - 1) = α * j + -α := by ring
    rw [h1, h2, sn_add, sn_add, cs_neg, sn_neg, hκ]
    ring
  have hΦ₁ : lfStep ν A u₁ = Matrix.vecMulVec
      (fun j => cs α * cs (α * j) + κ * sn (α * j)) a := by
    rw [hu₁, lfStep_vecMulVec ν ha]
    simp only [s1]
  have hΦ₂ : lfStep ν A u₂ = Matrix.vecMulVec
      (fun j => cs α * sn (α * j) - κ * cs (α * j)) a := by
    rw [hu₂, lfStep_vecMulVec ν ha]
    simp only [s2]
  have hterm : ∀ j : ZMod n, (cs α * cs (α * j) + κ * sn (α * j)) ^ 2 +
      (cs α * sn (α * j) - κ * cs (α * j)) ^ 2 =
      G * (cs (α * j) ^ 2 + sn (α * j) ^ 2) := fun j => by
    rw [hG, hκ]; ring
  have hsum : ‖lfStep ν A u₁‖ ^ 2 + ‖lfStep ν A u₂‖ ^ 2 = G * (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2) := by
    obtain ⟨N, hN⟩ : ∃ N, N = ∑ k, a k ^ 2 := ⟨_, rfl⟩
    calc ‖lfStep ν A u₁‖ ^ 2 + ‖lfStep ν A u₂‖ ^ 2
        = (∑ j, (cs α * cs (α * j) + κ * sn (α * j)) ^ 2) * N +
          (∑ j, (cs α * sn (α * j) - κ * cs (α * j)) ^ 2) * N := by
          rw [hΦ₁, hΦ₂, norm_sq_vecMulVec, norm_sq_vecMulVec, hN]
      _ = (∑ j, ((cs α * cs (α * j) + κ * sn (α * j)) ^ 2 +
          (cs α * sn (α * j) - κ * cs (α * j)) ^ 2)) * N := by
          rw [Finset.sum_add_distrib, add_mul]
      _ = (∑ j, G * (cs (α * j) ^ 2 + sn (α * j) ^ 2)) * N := by
          simp only [hterm]
      _ = G * ((∑ j, cs (α * j) ^ 2) * N + (∑ j, sn (α * j) ^ 2) * N) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          ring
      _ = G * (‖u₁‖ ^ 2 + ‖u₂‖ ^ 2) := by
          rw [hu₁, hu₂, norm_sq_vecMulVec, norm_sq_vecMulVec, hN]
  by_cases h₁ : G * ‖u₁‖ ^ 2 ≤ ‖lfStep ν A u₁‖ ^ 2
  · refine ⟨u₁, ?_, h₁⟩
    intro h0
    apply ha0
    ext k
    have := congrFun (congrFun h0 0) k
    simpa [hu₁, Matrix.vecMulVec_apply, cs_zero] using this
  · refine ⟨u₂, ?_, by linarith⟩
    intro h0
    apply h₁
    have : lfStep ν A u₂ = 0 := by rw [h0]; simp [lfStep]
    rw [this, h0] at hsum
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      at hsum
    linarith

/-- The upper bound (8) of arXiv 2107.07282, Sec. 2.2, by Parseval's identity: `g` is any bound of
the amplification factors of all wave numbers. -/
theorem lfStep_norm_le_ampl {ν g : ℝ} {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (hg0 : 0 ≤ g) (hg : ∀ α : ZMod n, ampl (ν * lamMax hA) α ≤ g) (u : Matrix (ZMod n) K ℝ) :
    ‖lfStep ν A u‖ ≤ g * ‖u‖ := by
  have hAt : Aᵀᵀ = Aᵀ := by rw [transpose_eq_of_isHermitian hA, transpose_eq_of_isHermitian hA]
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hg0 (norm_nonneg _))).1 ?_
  have hb : ∀ y : Matrix (ZMod n) K ℝ, ν ^ 2 * ‖y * Aᵀ‖ ^ 2 ≤ (ν * lamMax hA) ^ 2 * ‖y‖ ^ 2 :=
    fun y => sq_amp (norm_nonneg _) (norm_mul_transpose_le hA y)
  have hk : ∀ α : ZMod n, cs α ^ 2 + (ν * lamMax hA) ^ 2 * sn α ^ 2 ≤ g ^ 2 := fun α => by
    rw [← ampl_sq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hg α) 2
  have h1 := L1_L2_bound u hk
  rw [lfStep_eq_flow, (isLFPair_periodic (n := n)).flow_norm_sq hAt, mul_pow]
  have h2 := hb (L2 n 1 * u)
  linarith

/-- **Exact amplification of the full scheme** (arXiv 2107.07282, Sec. 2.2, eq. (7)–(8)).  On the
periodic grid with symmetric `A`, the operator `Φ : u ↦ L⁽¹⁾ u - L⁽²⁾ u Aᵀ` on `ℝ^{Nₓ×(N+1)}` with
the Frobenius norm has norm exactly `g = max_α √(cos²(α π Δx) + c² sin²(α π Δx))`,
`c = λ_max(A) Δt / Δx`: the bound holds for all `u` and it is attained.  (The paper only states
the upper bound.) -/
theorem lfStep_amplification [Nonempty K] (ν : ℝ) {A : Matrix K K ℝ} (hA : A.IsHermitian) :
    (∀ u : Matrix (ZMod n) K ℝ,
      ‖lfStep ν A u‖ ≤ (⨆ α : ZMod n, ampl (ν * lamMax hA) α) * ‖u‖) ∧
    ∃ u : Matrix (ZMod n) K ℝ, u ≠ 0 ∧
      ‖lfStep ν A u‖ = (⨆ α : ZMod n, ampl (ν * lamMax hA) α) * ‖u‖ := by
  set g := ⨆ α : ZMod n, ampl (ν * lamMax hA) α with hgdef
  have hg0 : 0 ≤ g := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hg : ∀ α : ZMod n, ampl (ν * lamMax hA) α ≤ g := fun α =>
    le_ciSup (f := fun α : ZMod n => ampl (ν * lamMax hA) α) (Set.finite_range _).bddAbove α
  have hup := lfStep_norm_le_ampl hA hg0 hg
  refine ⟨hup, ?_⟩
  obtain ⟨α, hα⟩ := exists_eq_ciSup_of_finite (f := fun α : ZMod n => ampl (ν * lamMax hA) α)
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => |hA.eigenvalues i|)
  have ha0 : (⇑(hA.eigenvectorBasis i) : K → ℝ) ≠ 0 := by
    intro h
    apply hA.eigenvectorBasis.orthonormal.ne_zero i
    ext k
    simpa using congrFun h k
  obtain ⟨u, hu0, hu⟩ := exists_mode_ge (n := n) ν ha0 (hA.mulVec_eigenvectorBasis i) α
  refine ⟨u, hu0, le_antisymm (hup u) ?_⟩
  have hlam : hA.eigenvalues i ^ 2 = lamMax hA ^ 2 := by
    rw [← sq_abs, hi, lamMax]
  have hG : cs α ^ 2 + (ν * hA.eigenvalues i) ^ 2 * sn α ^ 2 = g ^ 2 := by
    rw [mul_pow, hlam, ← mul_pow ν, ← ampl_sq, hgdef, ← hα]
  rw [hG, ← mul_pow] at hu
  exact (sq_le_sq₀ (mul_nonneg hg0 (norm_nonneg _)) (norm_nonneg _)).1 hu

/-- **The classical CFL condition is sharp** (arXiv 2107.07282, Sec. 2.2): on a periodic grid with
`Nₓ ≥ 3` cells the scheme (4) is `L²`-stable if and only if `λ_max(A) Δt / Δx ≤ 1`.  (For `Nₓ ≤ 2`
the discrete derivative vanishes, so `Nₓ ≥ 3` is needed.) -/
theorem lfStep_contractive_iff (hn : 3 ≤ n) {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ}
    (hA : A.IsHermitian) :
    (∀ u : Matrix (ZMod n) K ℝ, ‖lfStep ν A u‖ ≤ ‖u‖) ↔ ν * lamMax hA ≤ 1 := by
  refine ⟨fun hc => ?_, fun hc => lfStep_norm_le hν hA hc⟩
  by_contra hgt
  have hgt : 1 < ν * lamMax hA := not_le.1 hgt
  rcases isEmpty_or_nonempty K with hK | hK
  · have : lamMax hA = 0 := by simp [lamMax]
    rw [this] at hgt
    linarith
  obtain ⟨-, u, hu0, hu⟩ := lfStep_amplification (n := n) ν hA
  have h1 : 1 < ampl (ν * lamMax hA) (1 : ZMod n) := by
    have hs := sn_one_pos (n := n) hn
    have h2 : (1 : ℝ) ^ 2 < ampl (ν * lamMax hA) (1 : ZMod n) ^ 2 := by
      rw [ampl_sq]
      have := cs_sq_add_sn_sq (1 : ZMod n)
      have h3 : 1 < (ν * lamMax hA) ^ 2 := by nlinarith
      nlinarith [mul_pos (sub_pos.2 h3) (pow_pos hs 2)]
    exact (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1 h2
  have hg : ampl (ν * lamMax hA) (1 : ZMod n) ≤ ⨆ α : ZMod n, ampl (ν * lamMax hA) α :=
    le_ciSup (f := fun α : ZMod n => ampl (ν * lamMax hA) α) (Set.finite_range _).bddAbove _
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have := hc u
  rw [hu] at this
  nlinarith

end FullScheme

/-! ### Theorem 3: the stabilised PtD projector-splitting scheme (35) -/

section Scheme35

variable {n : ℕ} [NeZero n] {r K : Type*} [Fintype r] [Fintype K] [DecidableEq r] [DecidableEq K]

/-- One step of the scheme (35) from `uⁿ = K₀ Wᵀ` (`K₀ = Xⁿ Sⁿ`, `W = Wⁿ`) to `uⁿ⁺¹ = X₁ L₁`. -/
structure Scheme35 (ν : ℝ) (A : Matrix K K ℝ) (W : Matrix K r ℝ) (K₀ X₁ : Matrix (ZMod n) r ℝ)
    (St₀ St₁ : Matrix r r ℝ) (L₁ : Matrix r K ℝ) : Prop where
  /-- (35a), with the QR factorisation `Kⁿ⁺¹ = Xⁿ⁺¹ S̃ⁿ`. -/
  kStep : X₁ * St₀ = L1 n * K₀ - L2 n ν * K₀ * (Wᵀ * Aᵀ * W)
  /-- (35b). -/
  sStep : St₁ = X₁ᵀ * L1 n * X₁ * St₀ + X₁ᵀ * L2 n ν * X₁ * St₀ * (Wᵀ * Aᵀ * W)
  /-- (35c), with `Lⁿ = S̃ⁿ⁺¹ Wᵀ`. -/
  lStep : L₁ = X₁ᵀ * L1 n * X₁ * (St₁ * Wᵀ) - X₁ᵀ * L2 n ν * X₁ * (St₁ * Wᵀ) * Aᵀ

/-- **Theorem 3, corrected** (arXiv 2107.07282).  Under `λ_max(A) Δt / Δx ≤ 1` every substep of the
scheme (35) is a contraction, hence `‖uⁿ⁺¹‖_F ≤ ‖uⁿ‖_F`, for every low-rank state and all bases.
The paper states the CFL condition with `λ_max(Ã)`, `Ã = Wᵀ Aᵀ W`, but the L-step involves the full
`A`, and with `Ã` the theorem is false: `scheme35_literal_false`. -/
theorem scheme35_stable {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (hcfl : ν * lamMax hA ≤ 1) {W : Matrix K r ℝ} (hW : Wᵀ * W = 1)
    {K₀ X₁ : Matrix (ZMod n) r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {St₀ St₁ : Matrix r r ℝ}
    {L₁ : Matrix r K ℝ} (hs : Scheme35 ν A W K₀ X₁ St₀ St₁ L₁) :
    ‖St₀‖ ≤ ‖K₀‖ ∧ ‖St₁‖ ≤ ‖St₀‖ ∧ ‖L₁‖ ≤ ‖St₁‖ ∧ ‖X₁ * L₁‖ ≤ ‖K₀ * Wᵀ‖ := by
  have hP := isLFPair_periodic (n := n)
  have hρ : 0 ≤ lamMax hA := lamMax_nonneg hA
  have hAt : Aᵀ = A := transpose_eq_of_isHermitian hA
  have h0 : 0 ≤ ν * lamMax hA := mul_nonneg hν hρ
  have hc : (ν * lamMax hA) ^ 2 ≤ 1 := by nlinarith
  have hc' : (-ν * lamMax hA) ^ 2 ≤ 1 := by rw [neg_mul, neg_sq]; exact hc
  have hb1 : ∀ y : Matrix (ZMod n) r ℝ, ‖y * (Wᵀ * Aᵀ * W)‖ ≤ lamMax hA * ‖y‖ := fun y => by
    rw [hAt]; exact norm_mul_compress_le hA hW y
  have hBt := compress_transpose hA W
  have hAt' : Aᵀᵀ = Aᵀ := by rw [hAt, hAt]
  have hL2 : L2 n ν = ν • L2 n 1 := L2_eq ν
  have e1 : ‖St₀‖ ≤ ‖K₀‖ := by
    rw [← Frobenius.norm_mul_of_orthonormal hX₁ St₀, hs.kStep, hL2, Matrix.smul_mul,
      Matrix.smul_mul]
    exact hP.flow_norm_le hBt hρ hb1 hc K₀
  have e2 : ‖St₁‖ ≤ ‖St₀‖ := by
    have h : St₁ = X₁ᵀ * flow (L1 n) (L2 n 1) (-ν) (Wᵀ * Aᵀ * W) (X₁ * St₀) := by
      rw [hs.sStep, hL2, flow, Matrix.mul_sub, neg_smul, Matrix.mul_neg, sub_neg_eq_add]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [h, ← Frobenius.norm_mul_of_orthonormal hX₁ St₀]
    exact (norm_transpose_mul_le hX₁ _).trans (hP.flow_norm_le hBt hρ hb1 hc' _)
  have e3 : ‖L₁‖ ≤ ‖St₁‖ := by
    have h : L₁ = X₁ᵀ * flow (L1 n) (L2 n 1) ν Aᵀ (X₁ * (St₁ * Wᵀ)) := by
      rw [hs.lStep, hL2, flow, Matrix.mul_sub]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [h, ← Frobenius.norm_mul_transpose_of_orthonormal hW St₁,
      ← Frobenius.norm_mul_of_orthonormal hX₁ (St₁ * Wᵀ)]
    exact (norm_transpose_mul_le hX₁ _).trans
      (hP.flow_norm_le hAt' hρ (norm_mul_transpose_le hA) hc _)
  refine ⟨e1, e2, e3, ?_⟩
  rw [Frobenius.norm_mul_of_orthonormal hX₁, Frobenius.norm_mul_transpose_of_orthonormal hW]
  exact e3.trans (e2.trans e1)

end Scheme35

/-! ### Fourier-mode states of the two schemes -/

section Modes

variable {n : ℕ} [NeZero n]

lemma J_mul_self : J * J = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

lemma J_transpose : Jᵀ = -J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J]

lemma norm_planeU_sq {α : ZMod n} (hα : 2 * α ≠ 0) : ‖planeU α‖ ^ 2 = 2 := by
  have h := planeU_orthonormal hα
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, h]
  simp

lemma norm_scalar_J_sq (p q : ℝ) :
    ‖p • (1 : Matrix (Fin 2) (Fin 2) ℝ) - q • J‖ ^ 2 = 2 * (p ^ 2 + q ^ 2) := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [J, Fin.sum_univ_two]
  ring

/-- The compressions of the periodic matrices to a Fourier plane. -/
lemma planeU_compress_L1 {α : ZMod n} (hα : 2 * α ≠ 0) :
    (planeU α)ᵀ * L1 n * planeU α = cs α • 1 := by
  rw [Matrix.mul_assoc, L1_mul_planeU, Matrix.mul_smul, planeU_orthonormal hα]

lemma planeU_compress_L2 {α : ZMod n} (hα : 2 * α ≠ 0) (ν : ℝ) :
    (planeU α)ᵀ * L2 n ν * planeU α = (ν * sn α) • J := by
  rw [Matrix.mul_assoc, L2_mul_planeU, Matrix.mul_smul, ← Matrix.mul_assoc,
    planeU_orthonormal hα, Matrix.one_mul]

/-- **Single-mode amplification of the scheme (31)** (arXiv 2107.07282, proof of Theorem 2, the
factor `G`).  Let `A = ρ I`, `W = I`, and let the state be the rank-2 Fourier mode `X = planeU α`.
With `κ = ρ (Δt / Δx) sin θ_α`, the scheme (31) produces
`‖uⁿ⁺¹‖_F = (1 + κ²) √(cos² θ_α + κ²) ‖uⁿ‖_F`. -/
theorem scheme31_mode {α : ZMod n} (hα : 2 * α ≠ 0) (ν ρ : ℝ) :
    let κ := ν * ρ * sn α
    let St₀ : Matrix (Fin 2) (Fin 2) ℝ := cs α • 1 - κ • J
    let St₁ := St₀ + κ • (J * St₀)
    let L₁ := (1 + κ ^ 2) • St₀
    Scheme31 ν (ρ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 (planeU α) (planeU α) St₀ St₁ L₁ ∧
      ‖planeU α * L₁‖ =
        (1 + κ ^ 2) * √(cs α ^ 2 + κ ^ 2) * ‖planeU α * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ := by
  intro κ St₀ St₁ L₁
  have hB : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (ρ • 1)ᵀ * 1 = ρ • 1 := by simp
  have hLs : St₁ - κ • (J * St₁) = L₁ := by
    have hJJ := J_mul_self
    simp only [St₁, L₁, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ]
    simp only [smul_add, add_smul, Matrix.neg_mul, Matrix.one_mul, smul_smul]
    module
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hB, L1_mul_planeU, L2_mul_planeU]
    simp only [St₀, κ, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 2
    ring
  · rw [hB, planeU_compress_L2 hα]
    simp only [St₁, κ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    congr 2
    ring
  · rw [planeU_compress_L2 hα]
    simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_smul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul]
    rw [← hLs]
    simp only [κ]
    congr 2
    ring
  · rw [Matrix.transpose_one, Matrix.mul_one,
      Frobenius.norm_mul_of_orthonormal (planeU_orthonormal hα)]
    have h0 : 0 ≤ 1 + κ ^ 2 := by positivity
    have h1 : ‖St₀‖ ^ 2 = (cs α ^ 2 + κ ^ 2) * ‖planeU α‖ ^ 2 := by
      rw [norm_scalar_J_sq, norm_planeU_sq hα]
      ring
    have h2 : ‖St₀‖ = √(cs α ^ 2 + κ ^ 2) * ‖planeU α‖ := by
      rw [← Real.sqrt_sq (norm_nonneg St₀), h1, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (norm_nonneg _)]
    simp only [L₁]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, h2]
    ring

/-- **Single-mode amplification of the scheme (35)** (arXiv 2107.07282, eq. (37), with equality):
for `A = ρ I`, `W = I`, the rank-2 Fourier mode `X = planeU α` and `κ = ρ (Δt / Δx) sin θ_α`,
`‖uⁿ⁺¹‖_F² = (cos² θ_α + κ²)³ ‖uⁿ‖_F²`. -/
theorem scheme35_mode {α : ZMod n} (hα : 2 * α ≠ 0) (ν ρ : ℝ) :
    let κ := ν * ρ * sn α
    let St₀ : Matrix (Fin 2) (Fin 2) ℝ := cs α • 1 - κ • J
    let St₁ : Matrix (Fin 2) (Fin 2) ℝ := (cs α ^ 2 + κ ^ 2) • 1
    let L₁ := (cs α ^ 2 + κ ^ 2) • St₀
    Scheme35 ν (ρ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 (planeU α) (planeU α) St₀ St₁ L₁ ∧
      ‖planeU α * L₁‖ ^ 2 =
        (cs α ^ 2 + κ ^ 2) ^ 3 * ‖planeU α * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ ^ 2 := by
  intro κ St₀ St₁ L₁
  have hB : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (ρ • 1)ᵀ * 1 = ρ • 1 := by simp
  have hJJ := J_mul_self
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hB, L1_mul_planeU, L2_mul_planeU]
    simp only [St₀, κ, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 2
    ring
  · rw [hB, planeU_compress_L1 hα, planeU_compress_L2 hα]
    simp only [St₁, St₀, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, hJJ, smul_smul, smul_sub, smul_neg]
    simp only [κ]
    module
  · rw [planeU_compress_L1 hα, planeU_compress_L2 hα]
    simp only [L₁, St₁, St₀, Matrix.transpose_one, Matrix.mul_one,
      Matrix.transpose_smul, Matrix.mul_smul, smul_smul, smul_sub]
    simp only [κ]
    module
  · rw [Matrix.transpose_one, Matrix.mul_one,
      Frobenius.norm_mul_of_orthonormal (planeU_orthonormal hα)]
    simp only [L₁]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_scalar_J_sq, norm_planeU_sq hα]
    ring

end Modes

/-! ### The CFL condition of Theorems 2 and 3 with `λ_max(Ã)` is not sufficient -/

section Literal

variable {n : ℕ} [NeZero n]

/-- `W = [I; 0]`, two orthonormal columns in `ℝ⁴`. -/
def W4 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0; 0, 0]

/-- The flux matrix `A = [0 I; I 0]`, with `Wᵀ A W = 0`. -/
def A4 : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

lemma W4_orthonormal : W4ᵀ * W4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W4, Matrix.mul_apply, Fin.sum_univ_four]

lemma A4_transpose : A4ᵀ = A4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A4]

lemma A4_isHermitian (a : ℝ) : (a • A4).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul,
    A4_transpose]

lemma compress_A4 (a : ℝ) : W4ᵀ * (a • A4)ᵀ * W4 = 0 := by
  rw [Matrix.transpose_smul, A4_transpose, Matrix.mul_smul, Matrix.smul_mul]
  have : W4ᵀ * A4 * W4 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W4, A4, Matrix.mul_apply, Fin.sum_univ_four]
  rw [this, smul_zero]

lemma norm_W4_sq (p q : ℝ) : ‖p • W4ᵀ - q • (J * (W4ᵀ * A4))‖ ^ 2 = 2 * (p ^ 2 + q ^ 2) := by
  have h1 : W4ᵀ * A4 = !![0, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W4, A4, Matrix.mul_apply, Fin.sum_univ_four]
  have h2 : J * (!![0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 2) (Fin 4) ℝ) =
      !![0, 0, 0, 1; 0, 0, -1, 0] := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [J]
  have h : p • W4ᵀ - q • (J * (W4ᵀ * A4)) = !![p, 0, 0, -q; 0, p, q, 0] := by
    rw [h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [W4]
  rw [h, Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, Fin.sum_univ_four]
  ring

lemma lamMax_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ}
    (hB : B.IsHermitian) (h0 : B = 0) : lamMax hB = 0 := by
  have : hB.eigenvalues = 0 := hB.eigenvalues_eq_zero_iff.2 h0
  simp [lamMax, this]

/-- The rank-2 mode state for the flux `a A4`: the scheme (31) ignores the compressed flux and the
L-step sees the full `A`. -/
lemma scheme31_offdiag {α : ZMod n} (hα : 2 * α ≠ 0) (ν a : ℝ) :
    let γ := cs α
    let κ := ν * a * sn α
    let L₁ := γ • W4ᵀ - (γ * κ) • (J * (W4ᵀ * A4))
    Scheme31 ν (a • A4) W4 (planeU α) (planeU α) (γ • 1) (γ • 1) L₁ ∧
      ‖planeU α * L₁‖ ^ 2 = γ ^ 2 * (1 + κ ^ 2) * ‖planeU α * W4ᵀ‖ ^ 2 := by
  intro γ κ L₁
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [compress_A4, L1_mul_planeU]
    simp [γ]
  · rw [compress_A4]
    simp
  · rw [planeU_compress_L2 hα]
    simp only [L₁, κ, Matrix.transpose_smul, A4_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, Matrix.mul_assoc]
    congr 2
    ring
  · rw [Frobenius.norm_mul_of_orthonormal (planeU_orthonormal hα),
      Frobenius.norm_mul_transpose_of_orthonormal W4_orthonormal, norm_W4_sq, norm_planeU_sq hα]
    ring

/-- The same state for the scheme (35). -/
lemma scheme35_offdiag {α : ZMod n} (hα : 2 * α ≠ 0) (ν a : ℝ) :
    let γ := cs α
    let κ := ν * a * sn α
    let L₁ := (γ ^ 3) • W4ᵀ - (γ ^ 2 * κ) • (J * (W4ᵀ * A4))
    Scheme35 ν (a • A4) W4 (planeU α) (planeU α) (γ • 1) ((γ ^ 2) • 1) L₁ ∧
      ‖planeU α * L₁‖ ^ 2 = γ ^ 4 * (γ ^ 2 + κ ^ 2) * ‖planeU α * W4ᵀ‖ ^ 2 := by
  intro γ κ L₁
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [compress_A4, L1_mul_planeU]
    simp [γ]
  · rw [compress_A4, planeU_compress_L1 hα]
    simp [γ, smul_smul, pow_two]
  · rw [planeU_compress_L1 hα, planeU_compress_L2 hα]
    simp only [L₁, κ, γ, Matrix.transpose_smul, A4_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, Matrix.mul_assoc]
    congr 2
    ring
  · rw [Frobenius.norm_mul_of_orthonormal (planeU_orthonormal hα),
      Frobenius.norm_mul_transpose_of_orthonormal W4_orthonormal, norm_W4_sq, norm_planeU_sq hα]
    ring

lemma cs_one_three : cs (1 : ZMod 3) = -1 / 2 := by
  have hv : (1 : ZMod 3).val = 1 := rfl
  have e : 2 * Real.pi * (1 : ℕ) / (3 : ℕ) = Real.pi - Real.pi / 3 := by
    push_cast
    ring
  rw [cs_eq_cos, angle, hv, e, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma sn_one_three_sq : sn (1 : ZMod 3) ^ 2 = 3 / 4 := by
  have := cs_sq_add_sn_sq (1 : ZMod 3)
  rw [cs_one_three] at this
  linarith

lemma two_ne_zero_three : 2 * (1 : ZMod 3) ≠ 0 := by decide

/-- **Theorem 2 of arXiv 2107.07282 is false as stated, with `λ_max(Ã)`.**  The paper's CFL
condition `λ_max(Ã) Δt / Δx ≤ 1/√3` with `Ã = Wᵀ Aᵀ W` does not imply stability of (31).  For every
`Δt / Δx = ν > 0`, on the grid with three cells, there is a symmetric `A` with `Ã = 0` and a rank-2
state amplified by (31).  Its L-step uses the full `A`: the identification of the L-step in (29c)
and (33c) with the compressed `Ã` is wrong.  The correct statement is `scheme31_stable`. -/
theorem scheme31_literal_false {ν : ℝ} (hν : 0 < ν) :
    ∃ (A : Matrix (Fin 4) (Fin 4) ℝ) (W : Matrix (Fin 4) (Fin 2) ℝ)
      (K₀ X₁ : Matrix (ZMod 3) (Fin 2) ℝ) (St₀ St₁ : Matrix (Fin 2) (Fin 2) ℝ)
      (L₁ : Matrix (Fin 2) (Fin 4) ℝ) (_ : A.IsHermitian) (hÃ : (Wᵀ * Aᵀ * W).IsHermitian),
      Wᵀ * W = 1 ∧ K₀ᵀ * K₀ = 1 ∧ X₁ᵀ * X₁ = 1 ∧ Scheme31 ν A W K₀ X₁ St₀ St₁ L₁ ∧
        ν * lamMax hÃ ≤ 1 / √3 ∧ ‖K₀ * Wᵀ‖ < ‖X₁ * L₁‖ := by
  have hα := two_ne_zero_three
  obtain ⟨hs, hn⟩ := scheme31_offdiag hα ν (5 / ν)
  have hz : W4ᵀ * ((5 / ν) • A4)ᵀ * W4 = 0 := compress_A4 _
  have hH : (W4ᵀ * ((5 / ν) • A4)ᵀ * W4).IsHermitian := by
    rw [hz]; exact Matrix.isHermitian_zero
  refine ⟨_, _, _, _, _, _, _, A4_isHermitian _, hH, W4_orthonormal, planeU_orthonormal hα,
    planeU_orthonormal hα, hs, ?_, ?_⟩
  · rw [lamMax_eq_zero hH hz, mul_zero]
    positivity
  · refine (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [hn, cs_one_three]
    have hk : (ν * (5 / ν) * sn (1 : ZMod 3)) ^ 2 = 75 / 4 := by
      have : ν * (5 / ν) = 5 := by field_simp
      rw [this, mul_pow, sn_one_three_sq]
      norm_num
    rw [hk]
    have hp : 0 < ‖planeU (1 : ZMod 3) * W4ᵀ‖ ^ 2 := by
      rw [Frobenius.norm_mul_transpose_of_orthonormal W4_orthonormal, norm_planeU_sq hα]
      norm_num
    nlinarith

/-- **Theorem 3 of arXiv 2107.07282 is false as stated, with `λ_max(Ã)`.**  As in
`scheme31_literal_false`: `Ã = 0`, so the paper's CFL condition holds trivially, but the scheme (35)
amplifies a rank-2 state, because its L-step uses the full `A`.  The correct statement is
`scheme35_stable`. -/
theorem scheme35_literal_false {ν : ℝ} (hν : 0 < ν) :
    ∃ (A : Matrix (Fin 4) (Fin 4) ℝ) (W : Matrix (Fin 4) (Fin 2) ℝ)
      (K₀ X₁ : Matrix (ZMod 3) (Fin 2) ℝ) (St₀ St₁ : Matrix (Fin 2) (Fin 2) ℝ)
      (L₁ : Matrix (Fin 2) (Fin 4) ℝ) (_ : A.IsHermitian) (hÃ : (Wᵀ * Aᵀ * W).IsHermitian),
      Wᵀ * W = 1 ∧ K₀ᵀ * K₀ = 1 ∧ X₁ᵀ * X₁ = 1 ∧ Scheme35 ν A W K₀ X₁ St₀ St₁ L₁ ∧
        ν * lamMax hÃ ≤ 1 ∧ ‖K₀ * Wᵀ‖ < ‖X₁ * L₁‖ := by
  have hα := two_ne_zero_three
  obtain ⟨hs, hn⟩ := scheme35_offdiag hα ν (5 / ν)
  have hz : W4ᵀ * ((5 / ν) • A4)ᵀ * W4 = 0 := compress_A4 _
  have hH : (W4ᵀ * ((5 / ν) • A4)ᵀ * W4).IsHermitian := by
    rw [hz]; exact Matrix.isHermitian_zero
  refine ⟨_, _, _, _, _, _, _, A4_isHermitian _, hH, W4_orthonormal, planeU_orthonormal hα,
    planeU_orthonormal hα, hs, ?_, ?_⟩
  · rw [lamMax_eq_zero hH hz, mul_zero]
    norm_num
  · refine (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [hn, cs_one_three]
    have hk : (ν * (5 / ν) * sn (1 : ZMod 3)) ^ 2 = 75 / 4 := by
      have : ν * (5 / ν) = 5 := by field_simp
      rw [this, mul_pow, sn_one_three_sq]
      norm_num
    rw [hk]
    have hp : 0 < ‖planeU (1 : ZMod 3) * W4ᵀ‖ ^ 2 := by
      rw [Frobenius.norm_mul_transpose_of_orthonormal W4_orthonormal, norm_planeU_sq hα]
      norm_num
    nlinarith

end Literal

/-! ### Sharpness of `1/√3` in Theorem 2 -/

section Sharp

lemma lamMax_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {ρ : ℝ}
    (hA : (ρ • (1 : Matrix ι ι ℝ)).IsHermitian) : lamMax hA = |ρ| := by
  have h : ∀ i, hA.eigenvalues i = ρ := by
    intro i
    have h1 := hA.mulVec_eigenvectorBasis i
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero i
    obtain ⟨k, hk⟩ : ∃ k, (hA.eigenvectorBasis i) k ≠ 0 := by
      by_contra hall
      apply hne
      ext k
      by_contra hk
      exact hall ⟨k, hk⟩
    have h2 := congrFun h1 k
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hk h2).symm
  simp [lamMax, h]

/-- For `c² > 1/3` the single-mode factor of (31) exceeds `1` at small `s = sin² θ`. -/
lemma sharp_arith {c2 : ℝ} (hc : 1 < 3 * c2) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ → 1 < (1 + c2 * s) ^ 2 * (1 - s + c2 * s) := by
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = 3 * c2 ^ 2 - 2 * c2 := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = c2 ^ 2 * (1 - c2) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = |e1| + |e2| + 1 := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; positivity
  have hδ : 0 < 3 * c2 - 1 := by linarith
  refine ⟨min 1 ((3 * c2 - 1) / (2 * B)), lt_min one_pos (by positivity), fun s hs0 hs => ?_⟩
  have hs1 : s < 1 := hs.trans_le (min_le_left _ _)
  have hs2 : s * (2 * B) < 3 * c2 - 1 :=
    (lt_div_iff₀ (by positivity)).1 (hs.trans_le (min_le_right _ _))
  have h1 : -(|e1| * s) ≤ e1 * s := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le e1) hs0.le
    linarith
  have h2 : e2 * s ^ 2 ≤ |e2| * s := by
    have hss : s ^ 2 ≤ s := by nlinarith
    calc e2 * s ^ 2 ≤ |e2| * s ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self e2) (sq_nonneg s)
      _ ≤ |e2| * s := mul_le_mul_of_nonneg_left hss (abs_nonneg _)
  have hq : 0 < (3 * c2 - 1) + e1 * s - e2 * s ^ 2 := by
    have h3 : B * s = |e1| * s + |e2| * s + s := by rw [hB]; ring
    nlinarith
  have e : (1 + c2 * s) ^ 2 * (1 - s + c2 * s) - 1 =
      s * ((3 * c2 - 1) + e1 * s - e2 * s ^ 2) := by
    rw [he1, he2]
    ring
  have := mul_pos hs0 hq
  linarith

/-- **The constant `1/√3` of Theorem 2 is sharp** (arXiv 2107.07282, Theorem 2 only claims the
sufficiency).  If `λ_max(A) Δt / Δx > 1/√3` for `A = ρ I`, then on all sufficiently fine periodic
grids the scheme (31) amplifies a rank-2 Fourier mode. -/
theorem scheme31_sharp {ν ρ : ℝ} (hA : (ρ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHermitian)
    (hc : 1 / √3 < ν * lamMax hA) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
      ∃ (K₀ X₁ : Matrix (ZMod n) (Fin 2) ℝ) (St₀ St₁ L₁ : Matrix (Fin 2) (Fin 2) ℝ),
        K₀ᵀ * K₀ = 1 ∧ X₁ᵀ * X₁ = 1 ∧ Scheme31 ν (ρ • 1) 1 K₀ X₁ St₀ St₁ L₁ ∧
          ‖K₀ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ < ‖X₁ * L₁‖ := by
  rw [lamMax_smul_one] at hc
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = (ν * ρ) ^ 2 := ⟨_, rfl⟩
  have hc3 : 1 < 3 * c2 := by
    have h0 : (0 : ℝ) < 1 / √3 := by positivity
    have h1 : (1 / √3) ^ 2 < (ν * |ρ|) ^ 2 := pow_lt_pow_left₀ hc h0.le two_ne_zero
    rw [div_pow, Real.sq_sqrt (by norm_num), mul_pow, sq_abs] at h1
    rw [hc2, mul_pow]
    linarith
  obtain ⟨s₀, hs₀, hsharp⟩ := sharp_arith hc3
  have ht : Tendsto (fun n : ℕ => Real.sin (2 * Real.pi * 1 / n) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 * Real.pi * 1) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := (Real.continuous_sin.tendsto 0).comp h1
    simpa [Function.comp_def] using h2.pow 2
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (ht.eventually_lt_const hs₀)
  refine ⟨max n₁ 3, fun n _ hn => ?_⟩
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hα := two_ne_zero_of_three_le hn3
  obtain ⟨hs, hnorm⟩ := scheme31_mode hα ν ρ
  refine ⟨_, _, _, _, _, planeU_orthonormal hα, planeU_orthonormal hα, hs, ?_⟩
  rw [hnorm]
  have hsn := sn_one_pos (n := n) hn3
  have hs0 : 0 < sn (1 : ZMod n) ^ 2 := pow_pos hsn 2
  have hslt : sn (1 : ZMod n) ^ 2 < s₀ := by
    have hv : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
    have := hn₁ n ((le_max_left _ _).trans hn)
    rw [sn_eq_sin, angle, hv]
    simpa using this
  have hmain := hsharp _ hs0 hslt
  have hk : (ν * ρ * sn (1 : ZMod n)) ^ 2 = c2 * sn (1 : ZMod n) ^ 2 := by
    rw [hc2]
    ring
  have hcs : cs (1 : ZMod n) ^ 2 = 1 - sn (1 : ZMod n) ^ 2 := by
    have := cs_sq_add_sn_sq (1 : ZMod n)
    linarith
  rw [hk, hcs]
  have hp : 0 < ‖planeU (1 : ZMod n) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ := by
    rw [Matrix.transpose_one, Matrix.mul_one]
    have := norm_planeU_sq hα
    have h0 := norm_nonneg (planeU (1 : ZMod n))
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, t = √(1 - sn (1 : ZMod n) ^ 2 + c2 * sn (1 : ZMod n) ^ 2) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
  have htsq : t ^ 2 = 1 - sn (1 : ZMod n) ^ 2 + c2 * sn (1 : ZMod n) ^ 2 := by
    rw [ht]
    refine Real.sq_sqrt ?_
    have : 0 < 1 - sn (1 : ZMod n) ^ 2 + c2 * sn (1 : ZMod n) ^ 2 := by
      by_contra hneg
      have hle := not_lt.1 hneg
      have hpos : 0 ≤ (1 + c2 * sn (1 : ZMod n) ^ 2) ^ 2 := sq_nonneg _
      have := mul_nonpos_of_nonneg_of_nonpos hpos hle
      linarith
    exact this.le
  rw [← ht]
  have hprod : 1 < (1 + c2 * sn (1 : ZMod n) ^ 2) * t := by
    have hc0 : 0 < c2 := by linarith
    have h0 : 0 ≤ (1 + c2 * sn (1 : ZMod n) ^ 2) * t := by positivity
    rw [← htsq] at hmain
    refine lt_of_pow_lt_pow_left₀ 2 h0 ?_
    rw [mul_pow, one_pow]
    exact hmain
  nlinarith

end Sharp

/-! ### Theorem 1: instability of the discretize-first projector-splitting integrator -/

section Theorem1

variable {n : ℕ} [NeZero n] {K : Type*} [Fintype K]

variable (n) in
/-- The wave number `ᾱ` with `cos(ᾱ π Δx) = -1`, for even `Nₓ = n`. -/
noncomputable def hiMode : ZMod n := ((n / 2 : ℕ) : ZMod n)

variable (n) in
/-- The highest mode `e^{i ᾱ π x_j}`, see `altMode_eq`: `(-1)ʲ`. -/
noncomputable def altMode (j : ZMod n) : ℝ := cs (hiMode n * j)

lemma stdAddChar_hiMode (hn : Even n) : (ZMod.stdAddChar (hiMode n) : ℂ) = -1 := by
  obtain ⟨m, hm⟩ := hn
  have hm2 : n / 2 = m := by omega
  have hm0 : (m : ℂ) ≠ 0 := by
    have : m ≠ 0 := by
      have := NeZero.ne n
      omega
    exact_mod_cast this
  have h := ZMod.stdAddChar_coe (N := n) ((n / 2 : ℕ) : ℤ)
  have e : (((n / 2 : ℕ) : ℤ) : ZMod n) = hiMode n := by
    rw [Int.cast_natCast, hiMode]
  rw [e] at h
  rw [h, ← Complex.exp_pi_mul_I]
  congr 1
  rw [hm2]
  conv_lhs => rw [hm]
  push_cast
  field_simp
  ring

lemma cs_hiMode (hn : Even n) : cs (hiMode n) = -1 := by
  simp [cs, stdAddChar_hiMode hn]

lemma sn_hiMode (hn : Even n) : sn (hiMode n) = 0 := by
  simp [sn, stdAddChar_hiMode hn]

lemma altMode_succ (hn : Even n) (j : ZMod n) : altMode n (j + 1) = -altMode n j := by
  have e : hiMode n * (j + 1) = hiMode n * j + hiMode n := by ring
  rw [altMode, altMode, e, cs_add, cs_hiMode hn, sn_hiMode hn]
  ring

lemma altMode_pred (hn : Even n) (j : ZMod n) : altMode n (j - 1) = -altMode n j := by
  have e : hiMode n * (j - 1) = hiMode n * j + -hiMode n := by ring
  rw [altMode, altMode, e, cs_add, cs_neg, sn_neg, cs_hiMode hn, sn_hiMode hn]
  ring

/-- The highest mode of the proof of Theorem 1 of arXiv 2107.07282 is `(-1)ʲ`. -/
theorem altMode_eq (hn : Even n) (j : ZMod n) : altMode n j = (-1) ^ j.val := by
  have e : hiMode n * j = j.val • hiMode n := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  have h : (ZMod.stdAddChar (hiMode n * j) : ℂ) = (-1) ^ j.val := by
    rw [e, AddChar.map_nsmul_eq_pow, stdAddChar_hiMode hn]
  have h2 : ((-1 : ℂ) ^ j.val) = (((-1 : ℝ) ^ j.val : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [altMode, cs, h, h2, Complex.ofReal_re]

lemma altMode_sq (hn : Even n) (j : ZMod n) : altMode n j ^ 2 = 1 := by
  rw [altMode_eq hn, ← pow_mul, mul_comm, pow_mul]
  simp

/-- The right-hand side `F` of the semi-discrete system (3). -/
noncomputable def lfField (Δt ν : ℝ) (A : Matrix K K ℝ) (u : Matrix (ZMod n) K ℝ) :
    Matrix (ZMod n) K ℝ :=
  (1 / Δt) • ((L1 n - 1) * u - L2 n ν * u * Aᵀ)

/-- The explicit Euler step of (3) is the scheme (4) (arXiv 2107.07282, Sec. 2.1). -/
theorem eulerStep_lfField {Δt : ℝ} (hΔt : Δt ≠ 0) (ν : ℝ) (A : Matrix K K ℝ)
    (u : Matrix (ZMod n) K ℝ) : eulerStep (lfField Δt ν A) Δt u = lfStep ν A u := by
  rw [eulerStep, lfField, smul_smul, mul_one_div_cancel hΔt, one_smul, lfStep, Matrix.sub_mul,
    Matrix.one_mul]
  abel

lemma lfField_alt (hn : Even n) (Δt ν : ℝ) (A : Matrix K K ℝ) (w : K → ℝ) (t : ℝ) :
    lfField Δt ν A (t • Matrix.vecMulVec (altMode n) w) =
      (-2 * t / Δt) • Matrix.vecMulVec (altMode n) w := by
  have h1 : L1 n * Matrix.vecMulVec (altMode n) w = -Matrix.vecMulVec (altMode n) w := by
    ext j k
    rw [L1_mul_apply]
    simp only [Matrix.vecMulVec_apply, Matrix.neg_apply, altMode_succ hn, altMode_pred hn]
    ring
  have h2 : L2 n ν * Matrix.vecMulVec (altMode n) w = 0 := by
    ext j k
    rw [L2_mul_apply]
    simp only [Matrix.vecMulVec_apply, Matrix.zero_apply, altMode_succ hn, altMode_pred hn]
    ring
  simp only [lfField, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, h1, h2, Matrix.zero_mul,
    smul_zero, sub_zero, smul_smul]
  have e : -Matrix.vecMulVec (altMode n) w - Matrix.vecMulVec (altMode n) w =
      (-2 : ℝ) • Matrix.vecMulVec (altMode n) w := by module
  rw [e, smul_smul]
  congr 1
  ring

/-- **Theorem 1** (arXiv 2107.07282): the projector-splitting integrator applied to the
Lax–Friedrichs discretisation, i.e. the scheme (28), is `L²`-unstable, for every `Δt`, `Δx` and
every `A`.  For even `Nₓ = n`, let `u = e wᵀ` be the highest mode `e = ((-1)ʲ)_j` with an arbitrary
`w`.  If `u` lies in the new left and the old right basis (`P₁ u = u`, `Q₀ u = u`, any rank), then
one step gives `u ↦ 3 u`, whereas the full scheme gives `u ↦ -u`.  `kslEulerStep` with
`F = lfField` is the scheme (28) in full-space form.  The paper takes rank one; see
`ksl_lf_unstable_rankOne`.  The abstract form is `kslEulerStep_unstable`, whose field differs from
`F` away from the multiples of `u`. -/
theorem ksl_lf_unstable (hn : Even n) {Δt : ℝ} (hΔt : Δt ≠ 0) (ν : ℝ) (A : Matrix K K ℝ)
    (w : K → ℝ) {P₁ Q₀ : Matrix (ZMod n) K ℝ →L[ℝ] Matrix (ZMod n) K ℝ}
    (h₁ : P₁ (Matrix.vecMulVec (altMode n) w) = Matrix.vecMulVec (altMode n) w)
    (h₀ : Q₀ (Matrix.vecMulVec (altMode n) w) = Matrix.vecMulVec (altMode n) w) :
    eulerStep (lfField Δt ν A) Δt (Matrix.vecMulVec (altMode n) w) =
        -Matrix.vecMulVec (altMode n) w ∧
      kslEulerStep P₁ Q₀ (lfField Δt ν A) Δt (Matrix.vecMulVec (altMode n) w) =
        (3 : ℝ) • Matrix.vecMulVec (altMode n) w := by
  obtain ⟨U, hU⟩ : ∃ U, U = Matrix.vecMulVec (altMode n) w := ⟨_, rfl⟩
  rw [← hU] at h₁ h₀ ⊢
  have hF : ∀ t : ℝ, lfField Δt ν A (t • U) = (-2 * t / Δt) • U := fun t => by
    rw [hU]; exact lfField_alt hn Δt ν A w t
  have hF1 : lfField Δt ν A U = (-2 / Δt) • U := by
    have := hF 1
    rwa [one_smul, mul_one] at this
  have hd : ∀ t : ℝ, Δt * (t / Δt) = t := fun t => by field_simp
  have hK : kslK Q₀ (lfField Δt ν A) Δt U = (-1 : ℝ) • U := by
    rw [kslK, hF1, map_smul, h₀, smul_smul, hd]
    module
  have hS : kslS P₁ Q₀ (lfField Δt ν A) Δt ((-1 : ℝ) • U) = (-3 : ℝ) • U := by
    rw [kslS, map_smul, h₁, hF, map_smul, map_smul, h₀, h₁, smul_smul, hd]
    module
  have hL : kslL P₁ (lfField Δt ν A) Δt ((-3 : ℝ) • U) = (3 : ℝ) • U := by
    rw [kslL, hF, map_smul, h₁, smul_smul, hd]
    module
  refine ⟨?_, ?_⟩
  · rw [eulerStep, hF1, smul_smul, hd]
    module
  · rw [kslEulerStep, hK, hS, hL]

/-- **Theorem 1 in the setting of the paper**: rank one, `X = e / √n`, `W = w` with `‖w‖ = 1`.
The state `u = e wᵀ ≠ 0` keeps its norm under the full scheme and is amplified by exactly `3` by
the scheme (28). -/
theorem ksl_lf_unstable_rankOne (hn : Even n) {Δt : ℝ} (hΔt : Δt ≠ 0) (ν : ℝ) (A : Matrix K K ℝ)
    {w : K → ℝ} (hw : ∑ k, w k ^ 2 = 1) :
    ∃ (X : Matrix (ZMod n) Unit ℝ) (W : Matrix K Unit ℝ), Xᵀ * X = 1 ∧ Wᵀ * W = 1 ∧
      Matrix.vecMulVec (altMode n) w ≠ 0 ∧
      ‖eulerStep (lfField Δt ν A) Δt (Matrix.vecMulVec (altMode n) w)‖ =
        ‖Matrix.vecMulVec (altMode n) w‖ ∧
      ‖kslEulerStep (leftProj X) (rightProj W) (lfField Δt ν A) Δt
        (Matrix.vecMulVec (altMode n) w)‖ = 3 * ‖Matrix.vecMulVec (altMode n) w‖ := by
  have hnp := n_pos (n := n)
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnp.le
  have hsq0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnp).ne'
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix (ZMod n) Unit ℝ,
      X = (1 / √(n : ℝ)) • Matrix.replicateCol Unit (altMode n) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix K Unit ℝ, W = Matrix.replicateCol Unit w := ⟨_, rfl⟩
  have hX : Xᵀ * X = 1 := by
    ext a b
    have hs : ∑ j : ZMod n, altMode n j * altMode n j = n := by
      simp only [← pow_two, altMode_sq hn]
      simp [ZMod.card]
    have e : ∀ j : ZMod n, 1 / √(n : ℝ) * altMode n j * (1 / √(n : ℝ) * altMode n j) =
        1 / n * (altMode n j * altMode n j) := fun j => by
      have : (1 : ℝ) / n = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
        rw [div_mul_div_comm, one_mul, hsq]
      rw [this]
      ring
    simp only [hXdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.replicateCol_apply, smul_eq_mul, e, ← Finset.mul_sum, hs]
    simp [hnp.ne']
  have hW : Wᵀ * W = 1 := by
    ext a b
    simp only [hWdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.replicateCol_apply,
      ← pow_two, hw]
    simp
  have hU : Matrix.vecMulVec (altMode n) w = √(n : ℝ) • (X * Wᵀ) := by
    ext j k
    simp only [hXdef, hWdef, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.replicateCol_apply, smul_eq_mul]
    simp only [Fintype.univ_unit, Finset.sum_singleton]
    field_simp
  have h₁ : leftProj X (Matrix.vecMulVec (altMode n) w) = Matrix.vecMulVec (altMode n) w := by
    rw [hU, leftProj_apply, Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, hX, Matrix.one_mul]
  have h₀ : rightProj W (Matrix.vecMulVec (altMode n) w) = Matrix.vecMulVec (altMode n) w := by
    rw [hU, rightProj_apply, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_assoc X, Matrix.mul_assoc X, hW, Matrix.one_mul]
  obtain ⟨he, hk⟩ := ksl_lf_unstable hn hΔt ν A w h₁ h₀
  refine ⟨X, W, hX, hW, ?_, ?_, ?_⟩
  · intro h0
    have h2 := norm_sq_vecMulVec (altMode n) w
    rw [h0, hw, mul_one] at h2
    simp only [altMode_sq hn] at h2
    simp [ZMod.card] at h2
    exact hnp.ne' h2.symm
  · rw [he, norm_neg]
  · rw [hk, norm_smul]
    norm_num

end Theorem1

/-! ### Theorem 4: the unconventional integrator -/

section Scheme38

variable {n : ℕ} [NeZero n] {r K : Type*} [Fintype r] [Fintype K] [DecidableEq r] [DecidableEq K]

/-- One step of the unconventional integrator (38) from `uⁿ = X₀ S₀ W₀ᵀ` to `uⁿ⁺¹ = X₁ S₁ W₁ᵀ`.
`X₁`, `W₁` come from the QR factorisations of `Kⁿ⁺¹`, `Lⁿ⁺¹`.  The S-step starts from
`ū = X₁ M S₀ Nᵀ W₁ᵀ`, `M = X₁ᵀ X₀`, `N = W₁ᵀ W₀`. -/
structure Scheme38 (ν : ℝ) (A : Matrix K K ℝ) (X₀ : Matrix (ZMod n) r ℝ) (S₀ : Matrix r r ℝ)
    (W₀ : Matrix K r ℝ) (X₁ : Matrix (ZMod n) r ℝ) (W₁ : Matrix K r ℝ) (S₁ : Matrix r r ℝ) :
    Prop where
  /-- (38a). -/
  kStep : ∃ R : Matrix r r ℝ, X₁ * R = lfStep ν A (X₀ * S₀ * W₀ᵀ) * W₀
  /-- (38b). -/
  lStep : ∃ R : Matrix r r ℝ, R * W₁ᵀ = X₀ᵀ * lfStep ν A (X₀ * S₀ * W₀ᵀ)
  /-- (38c). -/
  sStep : S₁ = X₁ᵀ * lfStep ν A (X₁ * (X₁ᵀ * X₀) * S₀ * (W₁ᵀ * W₀)ᵀ * W₁ᵀ) * W₁

omit [DecidableEq K] in
/-- The core of Theorem 4 of arXiv 2107.07282: the S-step (38c) as a contraction, for any bound `ρ`
of the compressed flux. -/
theorem scheme38_aux {ν ρ : ℝ} (hρ : 0 ≤ ρ) (hc : (ν * ρ) ^ 2 ≤ 1) {A : Matrix K K ℝ}
    (hA : A.IsHermitian) {X₀ X₁ : Matrix (ZMod n) r ℝ} {S₀ S₁ : Matrix r r ℝ}
    {W₀ W₁ : Matrix K r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) (hW₁ : W₁ᵀ * W₁ = 1)
    (hb : ∀ y : Matrix (ZMod n) r ℝ, ‖y * (W₁ᵀ * Aᵀ * W₁)‖ ≤ ρ * ‖y‖)
    (hs : Scheme38 ν A X₀ S₀ W₀ X₁ W₁ S₁) :
    ‖X₁ * S₁ * W₁ᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
  obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = (X₁ᵀ * X₀) * S₀ * (W₁ᵀ * W₀)ᵀ := ⟨_, rfl⟩
  have e1 : X₁ * (X₁ᵀ * X₀) * S₀ * (W₁ᵀ * W₀)ᵀ * W₁ᵀ = X₁ * Sb * W₁ᵀ := by
    rw [hSb]
    simp only [Matrix.mul_assoc]
  have e2 : lfStep ν A (X₁ * Sb * W₁ᵀ) * W₁ =
      flow (L1 n) (L2 n 1) ν (W₁ᵀ * Aᵀ * W₁) (X₁ * Sb) := by
    have h1 : L1 n * (X₁ * Sb * W₁ᵀ) * W₁ = L1 n * (X₁ * Sb) := by
      calc L1 n * (X₁ * Sb * W₁ᵀ) * W₁ = L1 n * (X₁ * Sb) * (W₁ᵀ * W₁) := by
            simp only [Matrix.mul_assoc]
        _ = L1 n * (X₁ * Sb) := by rw [hW₁, Matrix.mul_one]
    have h2 : L2 n 1 * (X₁ * Sb * W₁ᵀ) * Aᵀ * W₁ = L2 n 1 * (X₁ * Sb) * (W₁ᵀ * Aᵀ * W₁) := by
      simp only [Matrix.mul_assoc]
    rw [lfStep, flow, L2_eq ν, Matrix.sub_mul, h1]
    simp only [Matrix.smul_mul, h2]
  have e3 : ‖Sb‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
    have : Sb = X₁ᵀ * (X₀ * S₀ * W₀ᵀ) * W₁ := by
      rw [hSb, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact (norm_mul_orthonormal_le hW₁ _).trans (norm_transpose_mul_le hX₁ _)
  have e4 : S₁ = X₁ᵀ * flow (L1 n) (L2 n 1) ν (W₁ᵀ * Aᵀ * W₁) (X₁ * Sb) := by
    rw [hs.sStep, e1, Matrix.mul_assoc, e2]
  rw [Frobenius.norm_mul_transpose_of_orthonormal hW₁, Frobenius.norm_mul_of_orthonormal hX₁, e4]
  calc ‖X₁ᵀ * flow (L1 n) (L2 n 1) ν (W₁ᵀ * Aᵀ * W₁) (X₁ * Sb)‖
      ≤ ‖flow (L1 n) (L2 n 1) ν (W₁ᵀ * Aᵀ * W₁) (X₁ * Sb)‖ := norm_transpose_mul_le hX₁ _
    _ ≤ ‖X₁ * Sb‖ :=
        (isLFPair_periodic (n := n)).flow_norm_le (compress_transpose hA W₁) hρ hb hc _
    _ = ‖Sb‖ := Frobenius.norm_mul_of_orthonormal hX₁ Sb
    _ ≤ _ := e3

omit [DecidableEq K] in
/-- **Theorem 4** (arXiv 2107.07282): the unconventional integrator (38) is `L²`-stable under
`λ_max(Ã) Δt / Δx ≤ 1`.  Here `Ã = Wⁿ⁺¹ᵀ Aᵀ Wⁿ⁺¹` is built with the *new* basis, which is the matrix
`Ãⁿ⁺¹` in the S-step (39c) of the paper's proof, while the theorem's `Ã` is not indexed.  The QR
relations for `X₁`, `W₁` are not used: the bases may be arbitrary.  The abstract form is
`bug_euler_norm_le`, which assumes the bound for the full step instead of the CFL condition. -/
theorem scheme38_stable {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ} (hA : A.IsHermitian)
    {X₀ X₁ : Matrix (ZMod n) r ℝ} {S₀ S₁ : Matrix r r ℝ} {W₀ W₁ : Matrix K r ℝ}
    (hÃ : (W₁ᵀ * Aᵀ * W₁).IsHermitian) (hcfl : ν * lamMax hÃ ≤ 1) (hX₁ : X₁ᵀ * X₁ = 1)
    (hW₁ : W₁ᵀ * W₁ = 1) (hs : Scheme38 ν A X₀ S₀ W₀ X₁ W₁ S₁) :
    ‖X₁ * S₁ * W₁ᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
  have h0 : 0 ≤ ν * lamMax hÃ := mul_nonneg hν (lamMax_nonneg hÃ)
  exact scheme38_aux (lamMax_nonneg hÃ) (by nlinarith) hA hX₁ hW₁ (norm_mul_le_lamMax hÃ) hs

/-- Theorem 4 of arXiv 2107.07282 under the CFL condition `λ_max(A) Δt / Δx ≤ 1` of the full
problem, which implies the bound on the compressed flux used in the proof. -/
theorem scheme38_stable_of_lamMax {ν : ℝ} (hν : 0 ≤ ν) {A : Matrix K K ℝ} (hA : A.IsHermitian)
    (hcfl : ν * lamMax hA ≤ 1) {X₀ X₁ : Matrix (ZMod n) r ℝ} {S₀ S₁ : Matrix r r ℝ}
    {W₀ W₁ : Matrix K r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) (hW₁ : W₁ᵀ * W₁ = 1)
    (hs : Scheme38 ν A X₀ S₀ W₀ X₁ W₁ S₁) : ‖X₁ * S₁ * W₁ᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
  have h0 : 0 ≤ ν * lamMax hA := mul_nonneg hν (lamMax_nonneg hA)
  refine scheme38_aux (lamMax_nonneg hA) (by nlinarith) hA hX₁ hW₁ (fun y => ?_) hs
  rw [transpose_eq_of_isHermitian hA]
  exact norm_mul_compress_le hA hW₁ y

/-- **Single-mode amplification of the integrator (38)** (arXiv 2107.07282, eq. (40)–(41), with
equality): for `A = ρ I`, `W = I`, the rank-2 Fourier mode `X = planeU α` and
`κ = ρ (Δt / Δx) sin θ_α`, `‖uⁿ⁺¹‖_F² = (cos² θ_α + κ²) ‖uⁿ‖_F²`.  This also shows that the
hypotheses of `scheme38_stable` can hold. -/
theorem scheme38_mode {α : ZMod n} (hα : 2 * α ≠ 0) (ν ρ : ℝ) :
    let κ := ν * ρ * sn α
    let St : Matrix (Fin 2) (Fin 2) ℝ := cs α • 1 - κ • J
    Scheme38 ν (ρ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (planeU α) 1 1 (planeU α) 1 St ∧
      ‖planeU α * St * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ ^ 2 =
        (cs α ^ 2 + κ ^ 2) *
          ‖planeU α * (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ ^ 2 := by
  intro κ St
  have hO := planeU_orthonormal hα
  have hΦ : lfStep ν (ρ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (planeU α) = planeU α * St := by
    rw [lfStep, L1_mul_planeU, L2_mul_planeU]
    simp only [St, κ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, smul_smul]
    congr 2
    ring
  have hXSt : (planeU α)ᵀ * (planeU α * St) = St := by
    rw [← Matrix.mul_assoc, hO, Matrix.one_mul]
  refine ⟨⟨⟨St, ?_⟩, ⟨St, ?_⟩, ?_⟩, ?_⟩
  · simp only [Matrix.mul_one, Matrix.transpose_one, hΦ]
  · simp only [Matrix.mul_one, Matrix.transpose_one, hΦ, hXSt]
  · simp only [Matrix.mul_one, Matrix.transpose_one, hO, hΦ, hXSt]
  · simp only [Matrix.transpose_one, Matrix.mul_one]
    rw [Frobenius.norm_mul_of_orthonormal hO, norm_scalar_J_sq, norm_planeU_sq hα]
    ring

end Scheme38

/-! ### Section 5: scattering -/

section Scattering

variable {m r K : Type*} [Fintype m] [Fintype r] [Fintype K]

/-- The S-step and K-step of a right-acting field cancel (arXiv 2107.07282, Sec. 5, from (43)): if
`S' = -S B` and `K' = K B` on `[t₀, t₁]` and `K(t₀) = X S(t₁)`, then `K(t₁) = X S(t₀)`. -/
theorem scattering_cancel {B : Matrix r r ℝ} {X : Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
    {Kk : ℝ → Matrix m r ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hS : ODESolution (fun _ Y => -(Y * B)) S t₀ t₁)
    (hK : ODESolution (fun _ Y => Y * B) Kk t₀ t₁) (h0 : Kk t₀ = X * S t₁) :
    Kk t₁ = X * S t₀ := by
  have hY : ODESolution (fun _ (Y : Matrix m r ℝ) => -(Y * B)) (fun t => X * S t) t₀ t₁ := by
    refine ⟨(Frobenius.leftMulCLM X).continuous.comp_continuousOn hS.cont, fun t ht' => ?_⟩
    have h := Frobenius.hasDerivWithinAt_const_mul X (hS.deriv t ht')
    convert h using 1
    rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hf : Continuous (Function.uncurry fun (_ : ℝ) (Y : Matrix m r ℝ) => -(Y * B)) :=
    ((Frobenius.rightMulCLM (m := m) B).continuous.comp continuous_snd).neg
  have hL : IsLipschitzField (fun (_ : ℝ) (Y : Matrix m r ℝ) => -(Y * B)) ‖B‖ := by
    intro _ x y
    have e : -(x * B) - -(y * B) = -((x - y) * B) := by
      rw [Matrix.sub_mul]
      abel
    rw [e, norm_neg]
    exact (Frobenius.norm_mul_le _ _).trans_eq (mul_comm _ _)
  have h := AdjointDLRA.odeSolution_eq_reverse (g := fun _ Y => Y * B) hf hL
    (fun _ x => by simp) hY hK h0 t₁ ⟨ht, le_rfl⟩
  simpa using h

/-- **Scattering: K- and S-substeps cancel** (arXiv 2107.07282, Sec. 5, eq. (43)).  For the
scattering part `F(Y) = Y G`, take the substeps in the paper's order: the L-step gives some `L₁`
with `L₁ = S₁ W₁ᵀ`, then `S' = -S W₁ᵀ G W₁`, `S(t₀) Wⁿ⁺¹ᵀ = L₁`, then `K' = K W₁ᵀ G W₁`,
`K(t₀) = X S(t₁)`.  The final state `K(t₁) W₁ᵀ` is `X L₁`: only the L-step acts. -/
theorem scattering_ksl {G : Matrix K K ℝ} {X : Matrix m r ℝ} {W₁ : Matrix K r ℝ}
    {L₁ : Matrix r K ℝ} {S : ℝ → Matrix r r ℝ} {Kk : ℝ → Matrix m r ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hS : ODESolution (fun _ Y => -(Y * (W₁ᵀ * G * W₁))) S t₀ t₁) (hS0 : S t₀ * W₁ᵀ = L₁)
    (hK : ODESolution (fun _ Y => Y * (W₁ᵀ * G * W₁)) Kk t₀ t₁) (hK0 : Kk t₀ = X * S t₁) :
    Kk t₁ * W₁ᵀ = X * L₁ := by
  rw [scattering_cancel ht hS hK hK0, ← hS0, Matrix.mul_assoc]

variable [DecidableEq K]

omit [Fintype K] in
lemma one_add_smul_diagonal (Δt : ℝ) (g : K → ℝ) :
    (1 : Matrix K K ℝ) + Δt • Matrix.diagonal g = Matrix.diagonal fun l => 1 + Δt * g l := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- The Euler L-step of the scattering part (arXiv 2107.07282, Sec. 5):
`‖Lⁿ⁺¹‖_F ≤ max_l |1 + Δt G_ll| ‖Lⁿ⁺¹ᐟ²‖_F` for diagonal `G`. -/
theorem scattering_lStep_norm_le {g : K → ℝ} {Δt ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ l, |1 + Δt * g l| ≤ ρ) (L : Matrix r K ℝ) :
    ‖L * (1 + Δt • Matrix.diagonal g)‖ ≤ ρ * ‖L‖ := by
  rw [one_add_smul_diagonal]
  exact norm_mul_diagonal_le L hρ h

/-- **Scattering: the classical constraint** (arXiv 2107.07282, Sec. 5).  For diagonal `G ≤ 0` the
Euler L-step `L ↦ L (I + Δt G)` is a contraction if and only if `max_l |G_ll| Δt ≤ 2`, the
constraint of the full problem.  (The first scheme of Sec. 5, which keeps the Euler K- and S-steps,
is treated in `LeanDLRA.OpenProblems.Stability.kslScattering_norm_le_goldenRatio`.)  The paper
states the sufficiency, and the necessity is added here. -/
theorem scattering_lStep_contractive_iff [Nonempty r] {g : K → ℝ} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (hg : ∀ l, g l ≤ 0) :
    (∀ L : Matrix r K ℝ, ‖L * (1 + Δt • Matrix.diagonal g)‖ ≤ ‖L‖) ↔ ∀ l, Δt * |g l| ≤ 2 := by
  classical
  have habs : ∀ l, Δt * |g l| = -(Δt * g l) := fun l => by
    rw [abs_of_nonpos (hg l)]
    ring
  constructor
  · intro h l
    obtain ⟨i⟩ := ‹Nonempty r›
    have hn := h (Matrix.single i l 1)
    rw [one_add_smul_diagonal] at hn
    have e : Matrix.single i l (1 : ℝ) * Matrix.diagonal (fun l => 1 + Δt * g l) =
        (1 + Δt * g l) • Matrix.single i l (1 : ℝ) := by
      ext a b
      simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
      by_cases hb : l = b
      · subst hb
        ring
      · simp [hb]
    have hp : 0 < ‖Matrix.single i l (1 : ℝ)‖ := by
      refine norm_pos_iff.2 fun h0 => ?_
      have := congrFun (congrFun h0 i) l
      simp at this
    rw [e, norm_smul, Real.norm_eq_abs] at hn
    have h1 : |1 + Δt * g l| ≤ 1 := by
      by_contra hgt
      nlinarith [not_le.1 hgt]
    rw [habs]
    linarith [(abs_le.1 h1).1]
  · intro h L
    have := scattering_lStep_norm_le (g := g) (Δt := Δt) zero_le_one (fun l => ?_) L
    · rwa [one_mul] at this
    · have h2 := h l
      rw [habs] at h2
      have h3 := mul_nonpos_of_nonneg_of_nonpos hΔt (hg l)
      exact abs_le.2 ⟨by linarith, by linarith⟩

end Scattering

/-! ### The full algorithm of Section 5 -/

section Algorithm

variable {n : ℕ} [NeZero n] {r K : Type*} [Fintype r] [Fintype K] [DecidableEq r] [DecidableEq K]

/-- **The stabilised algorithm of Section 5** (arXiv 2107.07282): streaming by (35) followed by the
scattering L-step `Lⁿ⁺¹ = Lⁿ⁺¹ᐟ² (I + Δt G)`, with diagonal `G ≤ 0`, is `L²`-stable under
`λ_max(A) Δt / Δx ≤ 1` and `max_l |G_ll| Δt ≤ 2`. -/
theorem scheme35_scattering_stable {ν Δt : ℝ} (hν : 0 ≤ ν) (hΔt : 0 ≤ Δt) {A : Matrix K K ℝ}
    (hA : A.IsHermitian) (hcfl : ν * lamMax hA ≤ 1) {g : K → ℝ} (hg : ∀ l, g l ≤ 0)
    (hscat : ∀ l, Δt * |g l| ≤ 2) {W : Matrix K r ℝ} (hW : Wᵀ * W = 1)
    {K₀ X₁ : Matrix (ZMod n) r ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {St₀ St₁ : Matrix r r ℝ}
    {L₁ : Matrix r K ℝ} (hs : Scheme35 ν A W K₀ X₁ St₀ St₁ L₁) :
    ‖X₁ * (L₁ * (1 + Δt • Matrix.diagonal g))‖ ≤ ‖K₀ * Wᵀ‖ := by
  obtain ⟨-, -, -, h⟩ := scheme35_stable hν hA hcfl hW hX₁ hs
  have h1 : ‖L₁ * (1 + Δt • Matrix.diagonal g)‖ ≤ ‖L₁‖ := by
    rcases isEmpty_or_nonempty r with hr | hr
    · have : L₁ * (1 + Δt • Matrix.diagonal g) = 0 := by
        ext i
        exact (hr.false i).elim
      rw [this, norm_zero]
      exact norm_nonneg _
    · exact (scattering_lStep_contractive_iff hΔt hg).2 hscat L₁
  rw [Frobenius.norm_mul_of_orthonormal hX₁]
  rw [Frobenius.norm_mul_of_orthonormal hX₁] at h
  exact h1.trans h

end Algorithm

end LeanDLRA.Literature.P2107_07282
