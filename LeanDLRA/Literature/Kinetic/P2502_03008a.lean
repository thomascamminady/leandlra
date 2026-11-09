import LeanDLRA.Classical.SVD
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2502.03008: energy-stable multiplicative DLRA, Su–Olson

This module formalizes the stability analysis of Baumann, Einkemmer, Klingenberg and Kusch for
the concrete discretization of the multiplicative Su–Olson problem, not only its abstract core: the
periodic stencils `D^x`, `D^xx`, `D⁺` on `ZMod N` (`lemma_1_skew`, `lemma_1_skew_self`,
`lemma_1_symm`, `lemma_1_neg_sq`), the moment matrix `A_{kℓ} = ⟨P_k, μ P_ℓ⟩_μ` of the normalized
Legendre polynomials (`isL2Orthonormal_legendreP`) with spectrum in `[-1, 1]`
(`abs_eigenvalue_le`), the CFL inequality (`lemma_2`), the instability of the advection form (10)
(`theorem_1`), the energy stability of the conservative scheme (11) (`theorem_2`), and the energy
stability of the DLRA scheme (19) with the augmentations (19b), (19d), (19i) and either truncation
(`theorem_3`, `theorem_3_svd`, `theorem_3_conservative`). The heart of Theorem 3 is
`IsAugmentedUpdate.isConservativeStep`: before truncation the low-rank update is exactly a solution
of the full scheme (11).

## Differences from the paper

* Grid and moments: the spatial index is `ZMod N`, `Δx > 0` is arbitrary (the paper has
  `Δx = 1/N_x`, its numerics `Δx = 20/N_x`), and the energy theorems hold for the moment matrix of
  every `L²(-1, 1)`-orthonormal family `P` of continuous functions, the Legendre case being
  `P = legendreP K`. `|A|` is taken from an arbitrary diagonalization.
* Hypotheses left implicit in the paper are stated: `Δt > 0`, `σ ≥ 0`, `B⁰ > 0`, and `D⁺` periodic,
  which Lemma 1 requires. The bound `|σ_m| ≤ 1` on the spectrum of `A`, which Lemma 2 needs and
  which the paper takes from its reference [1], is proved.
* Theorem 1: the paper proves the reduction to forward Euler with centred differences for the first
  step (`v¹` is no longer constant) and quotes the instability of that scheme. Here the reduction
  is proved, the instability of the reduced scheme is proved in von Neumann's sense
  (`ftcsC_mode`, `norm_amplification_sq`, `not_isVonNeumannStable`), and it is added that one step
  of (10) itself strictly increases the energy (`advection_energy_eq`). What is not formalized is
  a von Neumann analysis of the variable-coefficient scheme (10) over several steps, which the paper
  does not give either.
* Theorem 3: `qr` is the core capture predicate `Matrix.IsOrthCapture`, which allows rank
  deficiency. The paper ends its proof by noting that
  the truncation does not alter the zeroth moment, the property the conservative truncation of its
  Section 5.4 is designed to have. The proof here does not use it: what the energy bound uses is
  that both truncations are `v¹ = v̂¹ Π` with an orthogonal projector `Π`
  (`energy_le_of_isRightProjection`, `IsSVDTruncation.isRightProjection`,
  `IsConservativeTruncation.isRightProjection`). The bound holds for arbitrary `K*`, `L*`
  (`energy_le_of_isAugmentedUpdate`), so the transposition in the printed formula (19c), kept in
  `lStep`, does not matter.
* In (19h) the symbol `K*` means `X̂̂* Ŝ̂*`, not the `K*` of (19a); this reading is forced by the
  rank of (19j).

Non-vacuity: `exists_isConservativeStep`, `exists_isAdvectionStep`, `exists_isDLRAStep`,
`exists_isSVDTruncation`, `exists_isConservativeTruncation`. Theorem 4 of the paper is the sibling
slice. No claim of the paper was found to be false.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2502_03008

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### The periodic stencils -/

section Stencils

variable {N : ℕ} [NeZero N]

/-- The periodic centred stencil `D^x` of arXiv 2502.03008, Section 3.2: `D^x_{j,j±1} = ±1/(2Δx)`,
indices being taken modulo `N_x`. The two contributions are added, which only matters for
`N_x ≤ 2`, where `j + 1 = j - 1`. -/
noncomputable def Dx (Δx : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun j i => ((if i = j + 1 then 1 else 0) - (if i = j - 1 then 1 else 0)) / (2 * Δx)

/-- The periodic stabilisation stencil `D^xx` of arXiv 2502.03008, Section 3.2:
`D^xx_{jj} = -1/Δx`, `D^xx_{j,j±1} = 1/(2Δx)`. -/
noncomputable def Dxx (Δx : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun j i =>
    ((if i = j + 1 then 1 else 0) - 2 * (if i = j then 1 else 0) + (if i = j - 1 then 1 else 0))
      / (2 * Δx)

/-- The periodic one-sided stencil `D⁺` of arXiv 2502.03008, Lemma 1: `D⁺_{jj} = -1/√(2Δx)`,
`D⁺_{j,j+1} = 1/√(2Δx)`. -/
noncomputable def Dplus (Δx : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  Matrix.of fun j i => ((if i = j + 1 then 1 else 0) - (if i = j then 1 else 0)) / √(2 * Δx)

lemma Dx_mulVec (Δx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    (Dx Δx *ᵥ z) j = (z (j + 1) - z (j - 1)) / (2 * Δx) := by
  simp [Dx, mulVec, dotProduct, sub_div, sub_mul, ite_div, Finset.sum_sub_distrib,
    ite_mul, Finset.sum_ite_eq']
  ring

lemma Dxx_mulVec (Δx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    (Dxx Δx *ᵥ z) j = (z (j + 1) - 2 * z j + z (j - 1)) / (2 * Δx) := by
  simp [Dxx, mulVec, dotProduct, sub_div, add_div, sub_mul, add_mul, ite_div,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, Finset.sum_ite_eq', mul_ite]
  ring

lemma Dplus_mulVec (Δx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    (Dplus Δx *ᵥ z) j = (z (j + 1) - z j) / √(2 * Δx) := by
  simp [Dplus, mulVec, dotProduct, sub_div, sub_mul, ite_div, Finset.sum_sub_distrib,
    ite_mul, Finset.sum_ite_eq']
  ring

omit [NeZero N] in
lemma Dx_transpose (Δx : ℝ) : (Dx Δx : Matrix (ZMod N) (ZMod N) ℝ)ᵀ = -Dx Δx := by
  ext j i
  simp only [transpose_apply, Dx, Matrix.of_apply, Matrix.neg_apply]
  have h1 : (j = i + 1) = (i = j - 1) := by
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp [h]
  have h2 : (j = i - 1) = (i = j + 1) := by
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp [h]
  simp only [h1, h2]
  ring

omit [NeZero N] in
lemma Dxx_transpose (Δx : ℝ) : (Dxx Δx : Matrix (ZMod N) (ZMod N) ℝ)ᵀ = Dxx Δx := by
  ext j i
  simp only [transpose_apply, Dxx, Matrix.of_apply]
  have h1 : (j = i + 1) = (i = j - 1) := by
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp [h]
  have h2 : (j = i - 1) = (i = j + 1) := by
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp [h]
  have h3 : (j = i) = (i = j) := by
    simp only [eq_iff_iff]
    exact eq_comm
  simp only [h1, h2, h3]
  ring

lemma Dplus_transpose_mulVec (Δx : ℝ) (z : ZMod N → ℝ) (j : ZMod N) :
    ((Dplus Δx)ᵀ *ᵥ z) j = (z (j - 1) - z j) / √(2 * Δx) := by
  simp only [mulVec, dotProduct, transpose_apply, Dplus, Matrix.of_apply]
  have h1 (x : ZMod N) : (j = x + 1) = (x = j - 1) := by
    simp only [eq_iff_iff]
    constructor <;> intro h <;> simp [h]
  have h3 (x : ZMod N) : (j = x) = (x = j) := by
    simp only [eq_iff_iff]
    exact eq_comm
  simp only [h1, h3]
  simp [sub_div, sub_mul, ite_div, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq']
  ring

lemma sum_shift_add (f : ZMod N → ℝ) : ∑ j, f (j + 1) = ∑ j, f j :=
  Equiv.sum_comp (Equiv.addRight 1) f

lemma sum_shift_sub (f : ZMod N → ℝ) : ∑ j, f (j - 1) = ∑ j, f j :=
  Equiv.sum_comp (Equiv.subRight 1) f

lemma Dxx_eq_neg_Dplus_mul (Δx : ℝ) (hΔx : 0 < Δx) :
    (Dxx Δx : Matrix (ZMod N) (ZMod N) ℝ) = -(Dplus Δx * (Dplus Δx)ᵀ) := by
  refine Matrix.ext_iff_mulVec.2 fun z => ?_
  ext j
  have h : √(2 * Δx) ^ 2 = 2 * Δx := Real.sq_sqrt (by positivity)
  have h0 : √(2 * Δx) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Pi.neg_apply, Dxx_mulVec, Dplus_mulVec,
    Dplus_transpose_mulVec, Dplus_transpose_mulVec, add_sub_cancel_right]
  generalize √(2 * Δx) = s at h h0 ⊢
  rw [← h]
  field_simp
  ring

/-- **Lemma 1, skew-symmetry of `D^x`** (arXiv 2502.03008, Lemma 1):
`∑ y_j D^x_{ji} z_i = -∑ z_j D^x_{ji} y_i`. -/
theorem lemma_1_skew (Δx : ℝ) (y z : ZMod N → ℝ) :
    ∑ i, ∑ j, y j * Dx Δx j i * z i = -∑ i, ∑ j, z j * Dx Δx j i * y i := by
  have h (a b : ZMod N → ℝ) : ∑ i, ∑ j, a j * Dx Δx j i * b i = a ⬝ᵥ (Dx Δx *ᵥ b) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h, h, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Dx_transpose,
    Matrix.neg_mulVec, dotProduct_neg]

/-- **Lemma 1, `D^x` has vanishing quadratic form** (arXiv 2502.03008, Lemma 1):
`∑ z_j D^x_{ji} z_i = 0`. -/
theorem lemma_1_skew_self (Δx : ℝ) (z : ZMod N → ℝ) :
    ∑ i, ∑ j, z j * Dx Δx j i * z i = 0 := by
  have := lemma_1_skew Δx z z
  linarith

/-- **Lemma 1, symmetry of `D^xx`** (arXiv 2502.03008, Lemma 1):
`∑ y_j D^xx_{ji} z_i = ∑ z_j D^xx_{ji} y_i`. -/
theorem lemma_1_symm (Δx : ℝ) (y z : ZMod N → ℝ) :
    ∑ i, ∑ j, y j * Dxx Δx j i * z i = ∑ i, ∑ j, z j * Dxx Δx j i * y i := by
  have h (a b : ZMod N → ℝ) : ∑ i, ∑ j, a j * Dxx Δx j i * b i = a ⬝ᵥ (Dxx Δx *ᵥ b) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h, h, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Dxx_transpose]

/-- **Lemma 1, `D^xx` is a negative square** (arXiv 2502.03008, Lemma 1):
`∑ z_j D^xx_{ji} z_i = -∑_j (∑_i D⁺_{ji} z_i)²`. The paper's `D⁺` is taken periodic, as the
identity requires (`D⁺_{N_x,1} = 1/√(2Δx)`, which the paper leaves implicit). -/
theorem lemma_1_neg_sq (Δx : ℝ) (hΔx : 0 < Δx) (z : ZMod N → ℝ) :
    ∑ i, ∑ j, z j * Dxx Δx j i * z i = -∑ j, (∑ i, Dplus Δx j i * z i) ^ 2 := by
  have h : ∑ i, ∑ j, z j * Dxx Δx j i * z i = z ⬝ᵥ (Dxx Δx *ᵥ z) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hsq : √(2 * Δx) ^ 2 = 2 * Δx := Real.sq_sqrt (by positivity)
  have h0 : √(2 * Δx) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hp (j : ZMod N) : ∑ i, Dplus Δx j i * z i = (z (j + 1) - z j) / √(2 * Δx) := by
    rw [← Dplus_mulVec]
    rfl
  simp only [hp, h, dotProduct, Dxx_mulVec, div_pow, hsq]
  have e1 : ∑ j, z j * z (j + 1) = ∑ j, z (j - 1) * z j := by
    rw [← sum_shift_sub (fun j => z j * z (j + 1))]
    simp
  have e2 : ∑ j, z (j + 1) ^ 2 = ∑ j, z j ^ 2 := sum_shift_add fun j => z j ^ 2
  have key : ∑ j, z j * ((z (j + 1) - 2 * z j + z (j - 1)) / (2 * Δx)) =
      (∑ j, z j * z (j + 1) + ∑ j, z j * z (j - 1) - 2 * ∑ j, z j ^ 2) / (2 * Δx) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have key2 : ∑ j, (z (j + 1) - z j) ^ 2 / (2 * Δx) =
      (2 * ∑ j, z j ^ 2 - 2 * ∑ j, z j * z (j + 1)) / (2 * Δx) := by
    rw [← Finset.sum_div]
    congr 1
    have : ∑ j, (z (j + 1) - z j) ^ 2 =
        ∑ j, z (j + 1) ^ 2 - 2 * ∑ j, z j * z (j + 1) + ∑ j, z j ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, e2]
    ring
  rw [key, key2]
  have e3 : ∑ j, z j * z (j - 1) = ∑ j, z j * z (j + 1) := by
    rw [e1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e3]
  ring

end Stencils

/-! ### The moment matrix `A`, `|A|` and `|A|^{1/2}` -/

section Moments

variable {K : ℕ}

/-- Continuous functions on `[-1, 1]` that are orthonormal for `⟨f, g⟩_μ = ∫_{-1}^{1} f g dμ`. -/
structure IsL2Orthonormal (P : Fin K → ℝ → ℝ) : Prop where
  continuous : ∀ k, Continuous (P k)
  orthonormal : ∀ k l, ∫ μ in (-1 : ℝ)..1, P k μ * P l μ = if k = l then 1 else 0

/-- The moment matrix `A_{kℓ} = ⟨P_k, μ P_ℓ⟩_μ`. -/
noncomputable def momentMatrix (P : Fin K → ℝ → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun k l => ∫ μ in (-1 : ℝ)..1, P k μ * (μ * P l μ)

lemma momentMatrix_transpose (P : Fin K → ℝ → ℝ) : (momentMatrix P)ᵀ = momentMatrix P := by
  ext k l
  simp only [momentMatrix, transpose_apply, Matrix.of_apply]
  exact intervalIntegral.integral_congr fun μ _ => by ring

/-- `A = Q M Qᵀ` with `Q` orthogonal and `M` diagonal. -/
structure IsDiagonalization (A Q : Matrix (Fin K) (Fin K) ℝ) (M : Fin K → ℝ) : Prop where
  orthogonal : Qᵀ * Q = 1
  eq : A = Q * diagonal M * Qᵀ

/-- `|A| = Q |M| Qᵀ`. -/
noncomputable def absMat (Q : Matrix (Fin K) (Fin K) ℝ) (M : Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  Q * diagonal (fun m => |M m|) * Qᵀ

/-- `|A|^{1/2} = Q |M|^{1/2} Qᵀ`. -/
noncomputable def sqrtAbsMat (Q : Matrix (Fin K) (Fin K) ℝ) (M : Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  Q * diagonal (fun m => √|M m|) * Qᵀ

lemma IsDiagonalization.transpose_eq {A Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization A Q M) : Aᵀ = A := by
  rw [hd.eq]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma IsDiagonalization.mul_transpose {A Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization A Q M) : Q * Qᵀ = 1 :=
  mul_eq_one_comm.1 hd.orthogonal

lemma absMat_transpose (Q : Matrix (Fin K) (Fin K) ℝ) (M : Fin K → ℝ) :
    (absMat Q M)ᵀ = absMat Q M := by
  simp [absMat, Matrix.transpose_mul, Matrix.mul_assoc]

lemma sqrtAbsMat_transpose (Q : Matrix (Fin K) (Fin K) ℝ) (M : Fin K → ℝ) :
    (sqrtAbsMat Q M)ᵀ = sqrtAbsMat Q M := by
  simp [sqrtAbsMat, Matrix.transpose_mul, Matrix.mul_assoc]

lemma absMat_eq_sqrtAbsMat_mul {A Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization A Q M) : absMat Q M = sqrtAbsMat Q M * (sqrtAbsMat Q M)ᵀ := by
  rw [sqrtAbsMat_transpose]
  have : sqrtAbsMat Q M * sqrtAbsMat Q M =
      Q * (diagonal (fun m => √|M m|) * (Qᵀ * Q) * diagonal (fun m => √|M m|)) * Qᵀ := by
    simp only [sqrtAbsMat, Matrix.mul_assoc]
  rw [this, hd.orthogonal, Matrix.mul_one, Matrix.diagonal_mul_diagonal, absMat]
  congr 3
  ext m
  exact (Real.mul_self_sqrt (abs_nonneg _)).symm

/-- Quadratic forms of orthonormal functions: `∫ w (∑ c_k P_k)² = ∑∑ c_k c_ℓ ∫ w P_k P_ℓ`. -/
lemma integral_mul_sum_sq {P : Fin K → ℝ → ℝ} (hP : ∀ k, Continuous (P k)) {w : ℝ → ℝ}
    (hw : Continuous w) (c : Fin K → ℝ) :
    ∫ μ in (-1 : ℝ)..1, w μ * (∑ k, c k * P k μ) ^ 2 =
      ∑ k, ∑ l, c k * c l * ∫ μ in (-1 : ℝ)..1, w μ * (P k μ * P l μ) := by
  have h (μ : ℝ) : w μ * (∑ k, c k * P k μ) ^ 2 =
      ∑ k, ∑ l, c k * c l * (w μ * (P k μ * P l μ)) := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      exact intervalIntegral.integral_const_mul _ _
    · intro l _
      have := hP k
      have := hP l
      exact (by fun_prop :
        Continuous fun μ => c k * c l * (w μ * (P k μ * P l μ))).intervalIntegrable _ _
  · intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop

/-- The moment matrix of an orthonormal family has quadratic form between `-‖c‖²` and `‖c‖²`,
because `|μ| ≤ 1` on `[-1, 1]`. -/
lemma abs_dotProduct_momentMatrix_le {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P)
    (c : Fin K → ℝ) : |c ⬝ᵥ (momentMatrix P *ᵥ c)| ≤ c ⬝ᵥ c := by
  have hc : ∑ k, ∑ l, c k * c l * ∫ μ in (-1 : ℝ)..1, 1 * (P k μ * P l μ) = c ⬝ᵥ c := by
    simp [dotProduct, hP.orthonormal, mul_ite]
  have hA : ∑ k, ∑ l, c k * c l * ∫ μ in (-1 : ℝ)..1, (fun μ => μ) μ * (P k μ * P l μ) =
      c ⬝ᵥ (momentMatrix P *ᵥ c) := by
    simp only [dotProduct, mulVec, momentMatrix, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have : ∫ μ in (-1 : ℝ)..1, μ * (P k μ * P l μ) = ∫ μ in (-1 : ℝ)..1, P k μ * (μ * P l μ) :=
      intervalIntegral.integral_congr fun μ _ => by ring
    rw [this]
    ring
  have h1 := integral_mul_sum_sq hP.continuous (w := fun _ => 1) continuous_const c
  have h2 := integral_mul_sum_sq hP.continuous (w := fun μ => μ) continuous_id c
  have hcont : Continuous fun μ => (∑ k, c k * P k μ) ^ 2 := by
    have : ∀ k, Continuous (P k) := hP.continuous
    fun_prop
  have hi : IntervalIntegrable (fun μ => (∑ k, c k * P k μ) ^ 2) MeasureTheory.volume (-1) 1 :=
    hcont.intervalIntegrable _ _
  have hi' : IntervalIntegrable (fun μ => μ * (∑ k, c k * P k μ) ^ 2) MeasureTheory.volume (-1) 1 :=
    (continuous_id.mul hcont).intervalIntegrable _ _
  have h3 : 0 ≤ ∫ μ in (-1 : ℝ)..1, (1 - μ) * (∑ k, c k * P k μ) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun μ hμ =>
      mul_nonneg (by linarith [hμ.2]) (sq_nonneg _)
  have h4 : 0 ≤ ∫ μ in (-1 : ℝ)..1, (1 + μ) * (∑ k, c k * P k μ) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun μ hμ =>
      mul_nonneg (by linarith [hμ.1]) (sq_nonneg _)
  simp only [sub_mul, add_mul, one_mul] at h3 h4
  simp only [one_mul] at h1
  rw [intervalIntegral.integral_sub hi hi'] at h3
  rw [intervalIntegral.integral_add hi hi'] at h4
  simp only [one_mul] at hc
  rw [h1, hc] at h3 h4
  rw [h2, hA] at h3 h4
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **The spectrum of `A` lies in `[-1, 1]`** (used silently in arXiv 2502.03008, Lemma 2): the
fact behind the CFL condition `Δt ≤ Δx`. It is derived from `A_{kℓ} = ⟨P_k, μ P_ℓ⟩_μ`, for every
orthonormal family. -/
theorem abs_eigenvalue_le {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P)
    {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) (m : Fin K) : |M m| ≤ 1 := by
  set e : Fin K → ℝ := Pi.single m 1 with he
  set q : Fin K → ℝ := Q *ᵥ e with hq
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hqq : q ⬝ᵥ q = 1 := by
    rw [hq, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose, hd.orthogonal, Matrix.one_mulVec, hee]
  have hqA : q ⬝ᵥ (momentMatrix P *ᵥ q) = M m := by
    have hAQ : Qᵀ * momentMatrix P * Q = diagonal M := by
      rw [hd.eq]
      calc Qᵀ * (Q * diagonal M * Qᵀ) * Q = (Qᵀ * Q) * diagonal M * (Qᵀ * Q) := by
            simp only [Matrix.mul_assoc]
        _ = diagonal M := by rw [hd.orthogonal, Matrix.one_mul, Matrix.mul_one]
    calc q ⬝ᵥ (momentMatrix P *ᵥ q)
        = e ⬝ᵥ ((Qᵀ * momentMatrix P * Q) *ᵥ e) := by
          have key (w : Fin K → ℝ) : (Q *ᵥ e) ⬝ᵥ w = e ⬝ᵥ (Qᵀ *ᵥ w) := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
          rw [hq, key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = M m := by rw [hAQ]; simp [he]
  have := abs_dotProduct_momentMatrix_le hP q
  rwa [hqA, hqq] at this

/-- Every symmetric matrix has a diagonalization `A = Q M Qᵀ`, the one that defines `|A|` in
arXiv 2502.03008, Section 3.1. -/
theorem exists_isDiagonalization {A : Matrix (Fin K) (Fin K) ℝ} (hA : Aᵀ = A) :
    ∃ Q M, IsDiagonalization A Q M := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_⟩
  · simpa [star_eq_conjTranspose] using Unitary.coe_star_mul_self hH.eigenvectorUnitary
  · have := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this

end Moments

/-! ### The normalized Legendre polynomials -/

section Legendre

variable {K : ℕ}

open Polynomial in
/-- The real shifted Legendre polynomial `p_n` on `[0, 1]`, with `p_n(0) = 1`. -/
noncomputable def shifted (n : ℕ) : ℝ[X] := (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

open Polynomial in
/-- The Rodrigues weight `Xⁿ (1 - X)ⁿ`. -/
noncomputable def rodrigues (n : ℕ) : ℝ[X] := X ^ n * (1 - X) ^ n

open Polynomial in
lemma factorial_mul_shifted (n : ℕ) :
    (C (n.factorial : ℝ)) * shifted n = derivative^[n] (rodrigues n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, ← Polynomial.iterate_derivative_map] at h
  simpa [shifted, rodrigues] using h

open Polynomial in
lemma rodrigues_eval_zero {n j : ℕ} (h : j < n) : (derivative^[j] (rodrigues n)).eval 0 = 0 := by
  obtain ⟨g, hg⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd (p := rodrigues n) (q := X) (n := n) j
    (Dvd.intro _ rfl)
  rw [hg, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]

open Polynomial in
lemma rodrigues_eval_one {n j : ℕ} (h : j < n) : (derivative^[j] (rodrigues n)).eval 1 = 0 := by
  obtain ⟨g, hg⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd (p := rodrigues n)
    (q := 1 - X) (n := n) j (Dvd.intro_left _ rfl)
  rw [hg, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self, zero_pow (by omega), zero_mul]

open Polynomial in
/-- Integration by parts for polynomials on `[0, 1]`. -/
lemma integral_eval_mul_derivative (p q : ℝ[X]) :
    ∫ x in (0 : ℝ)..1, p.eval x * (derivative q).eval x =
      p.eval 1 * q.eval 1 - p.eval 0 * q.eval 0 -
        ∫ x in (0 : ℝ)..1, (derivative p).eval x * q.eval x := by
  refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => p.hasDerivAt x)
    (fun x _ => q.hasDerivAt x) ?_ ?_ <;>
  exact (Polynomial.continuous _).intervalIntegrable _ _

open Polynomial in
/-- `n` integrations by parts against the Rodrigues weight. -/
lemma integral_mul_iterate_rodrigues (p : ℝ[X]) (n j : ℕ) (hj : j ≤ n) :
    ∫ x in (0 : ℝ)..1, p.eval x * (derivative^[n] (rodrigues n)).eval x =
      (-1) ^ j * ∫ x in (0 : ℝ)..1,
        (derivative^[j] p).eval x * (derivative^[n - j] (rodrigues n)).eval x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega)]
    have hn : n - j = (n - (j + 1)) + 1 := by omega
    rw [hn, Function.iterate_succ_apply', integral_eval_mul_derivative,
      rodrigues_eval_zero (by omega), rodrigues_eval_one (by omega),
      ← Function.iterate_succ_apply' derivative j p]
    simp only [mul_zero, sub_self, zero_sub, pow_succ, Nat.succ_eq_add_one]
    ring

open Polynomial in
/-- `p_n` is orthogonal to the polynomials of degree `< n`. -/
lemma integral_mul_shifted_eq_zero {p : ℝ[X]} {n : ℕ} (hp : p.natDegree < n) :
    ∫ x in (0 : ℝ)..1, p.eval x * (shifted n).eval x = 0 := by
  have h := integral_mul_iterate_rodrigues p n n le_rfl
  rw [Polynomial.iterate_derivative_eq_zero hp, ← factorial_mul_shifted] at h
  simp only [eval_zero, zero_mul, intervalIntegral.integral_zero, mul_zero, eval_mul, eval_C] at h
  have h' : ∫ x in (0 : ℝ)..1, eval x p * ((n.factorial : ℝ) * eval x (shifted n)) =
      (n.factorial : ℝ) * ∫ x in (0 : ℝ)..1, eval x p * eval x (shifted n) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [h'] at h
  exact (mul_eq_zero.1 h).resolve_left (by positivity)

lemma natDegree_shifted (n : ℕ) : (shifted n).natDegree = n := by
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  rw [shifted, Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_shiftedLegendre]

/-- The Beta integral `∫₀¹ xᵃ (1-x)ᵇ dx = a! b! / (a+b+1)!`. -/
lemma integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b =
      (a.factorial * b.factorial : ℝ) / (a + b + 1).factorial := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow]
    simp [Nat.factorial_succ]
    field_simp
  | succ b ih =>
    have hA : (a : ℝ) + 1 ≠ 0 := by positivity
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (u := fun x : ℝ => (1 - x) ^ (b + 1)) (v := fun x : ℝ => x ^ (a + 1) / ((a : ℝ) + 1))
      (u' := fun x : ℝ => -(((b : ℝ) + 1) * (1 - x) ^ b)) (v' := fun x : ℝ => x ^ a)
      (fun x _ => by
        have := ((hasDerivAt_id x).const_sub 1).fun_pow (b + 1)
        simpa using this)
      (fun x _ => by
        have := (hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)
        convert this using 1
        simp only [Nat.add_sub_cancel]
        push_cast
        field_simp)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have h1 : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) =
        ∫ x in (0 : ℝ)..1, (1 - x) ^ (b + 1) * x ^ a :=
      intervalIntegral.integral_congr fun x _ => by simp [mul_comm]
    have h2 : ∫ x in (0 : ℝ)..1, -(((b : ℝ) + 1) * (1 - x) ^ b) * (x ^ (a + 1) / ((a : ℝ) + 1)) =
        -(((b : ℝ) + 1) / ((a : ℝ) + 1)) * ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      field_simp
    rw [h1, h, h2, ih (a + 1)]
    have e : a + (b + 1) + 1 = a + 1 + b + 1 := by omega
    rw [e, Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    have hF : (((a + 1 + b + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [one_pow, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, sub_zero, one_mul]
    field_simp
    ring

open Polynomial in
/-- The value `∫₀¹ p_n² = 1/(2n+1)`. -/
lemma integral_shifted_sq (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (shifted n).eval x * (shifted n).eval x = 1 / (2 * (n : ℝ) + 1) := by
  have h := integral_mul_iterate_rodrigues (shifted n) n n le_rfl
  have hc : derivative^[n] (shifted n) =
      C ((n.factorial : ℝ) * ((-1) ^ n * ((2 * n).choose n : ℝ))) := by
    have hd : (derivative^[n] (shifted n)).natDegree = 0 := by
      have := natDegree_iterate_derivative (shifted n) n
      rw [natDegree_shifted] at this
      omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, coeff_iterate_derivative]
    simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul, shifted, coeff_map,
      coeff_shiftedLegendre]
    congr 1
    simp [two_mul]
  rw [← factorial_mul_shifted, hc, Nat.sub_self, Function.iterate_zero, id] at h
  simp only [eval_mul, eval_C] at h
  have h1 : ∫ x in (0 : ℝ)..1, eval x (shifted n) * ((n.factorial : ℝ) * eval x (shifted n)) =
      (n.factorial : ℝ) * ∫ x in (0 : ℝ)..1, eval x (shifted n) * eval x (shifted n) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have h2 : ∫ x in (0 : ℝ)..1, (n.factorial : ℝ) * ((-1) ^ n * ((2 * n).choose n : ℝ)) *
      eval x (rodrigues n) = (n.factorial : ℝ) * ((-1) ^ n * ((2 * n).choose n : ℝ)) *
        ((n.factorial * n.factorial : ℝ) / (n + n + 1).factorial) := by
    rw [intervalIntegral.integral_const_mul, ← integral_pow_mul_one_sub_pow]
    congr 1
    exact intervalIntegral.integral_congr fun x _ => by simp [rodrigues]
  rw [h1, h2] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hm : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hch : ((2 * n).choose n : ℝ) * (n.factorial * n.factorial) = (2 * n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    exact_mod_cast (by rw [← this]; ring)
  have hfac : ((n + n + 1).factorial : ℝ) = (2 * (n : ℝ) + 1) * (2 * n).factorial := by
    rw [show n + n + 1 = 2 * n + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hF : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  rw [h, hfac]
  have e : (-1 : ℝ) ^ n * ((n.factorial : ℝ) * ((-1) ^ n * ((2 * n).choose n : ℝ)) *
      ((n.factorial * n.factorial : ℝ) / ((2 * (n : ℝ) + 1) * (2 * n).factorial))) =
      ((-1 : ℝ) ^ n * (-1) ^ n) * (n.factorial : ℝ) *
        ((((2 * n).choose n : ℝ) * (n.factorial * n.factorial)) /
          ((2 * (n : ℝ) + 1) * (2 * n).factorial)) := by
    ring
  rw [e, hm, hch]
  field_simp

/-- The normalized Legendre polynomials `P_k(μ) = √((2k+1)/2) L_k(μ)`, with
`L_k(μ) = p_k((1 - μ)/2)` (the normalization of Mathlib's `shiftedLegendre`, which gives
`L_k(1) = 1`). In particular `P_0 = 1/√2` and `P_1(μ) = √(3/2) μ`. -/
noncomputable def legendreP (K : ℕ) (k : Fin K) (μ : ℝ) : ℝ :=
  √((2 * (k : ℝ) + 1) / 2) * (shifted k).eval ((1 - μ) / 2)

/-- The substitution `x = (1 - μ)/2`. -/
lemma integral_comp_half (f : ℝ → ℝ) :
    ∫ μ in (-1 : ℝ)..1, f ((1 - μ) / 2) = 2 * ∫ x in (0 : ℝ)..1, f x := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (-1 : ℝ)) (b := 1) f
    (c := 1 / 2) (by norm_num) (1 / 2)
  have e (μ : ℝ) : (1 : ℝ) / 2 - 1 / 2 * μ = (1 - μ) / 2 := by ring
  simp only [e] at h
  rw [h]
  norm_num

lemma integral_shifted_mul (k l : ℕ) :
    ∫ x in (0 : ℝ)..1, (shifted k).eval x * (shifted l).eval x =
      if k = l then 1 / (2 * (l : ℝ) + 1) else 0 := by
  split_ifs with h
  · subst h
    exact integral_shifted_sq k
  · rcases lt_or_gt_of_ne h with h | h
    · exact integral_mul_shifted_eq_zero (by rwa [natDegree_shifted])
    · have := integral_mul_shifted_eq_zero (p := shifted l) (n := k)
        (by rwa [natDegree_shifted])
      exact (intervalIntegral.integral_congr fun x _ => mul_comm _ _).trans this

/-- **The normalized Legendre polynomials are orthonormal** on `[-1, 1]`, the property
`⟨P_k, P_ℓ⟩_μ = δ_{kℓ}` of arXiv 2502.03008, Section 3.1. Proved from Rodrigues' formula. -/
theorem isL2Orthonormal_legendreP (K : ℕ) : IsL2Orthonormal (legendreP K) := by
  refine ⟨fun k => ?_, fun k l => ?_⟩
  · unfold legendreP
    exact continuous_const.mul ((shifted k).continuous.comp (by fun_prop))
  · have h : ∫ μ in (-1 : ℝ)..1, legendreP K k μ * legendreP K l μ =
        √((2 * (k : ℝ) + 1) / 2) * √((2 * (l : ℝ) + 1) / 2) *
          (2 * ∫ x in (0 : ℝ)..1, (shifted k).eval x * (shifted l).eval x) := by
      rw [← integral_comp_half (fun x => (shifted k).eval x * (shifted l).eval x),
        ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun μ _ => by
        simp only [legendreP]
        ring
    rw [h, integral_shifted_mul]
    by_cases hkl : k = l
    · subst hkl
      have hs : √((2 * ((k : ℕ) : ℝ) + 1) / 2) * √((2 * ((k : ℕ) : ℝ) + 1) / 2) =
          (2 * ((k : ℕ) : ℝ) + 1) / 2 := Real.mul_self_sqrt (by positivity)
      simp only [ite_true, hs]
      have : (2 * ((k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    · have : (k : ℕ) ≠ l := fun e => hkl (Fin.ext e)
      simp [this, hkl]

lemma shifted_zero : shifted 0 = 1 := by
  simp [shifted, Polynomial.shiftedLegendre]

lemma eval_shifted_one (x : ℝ) : (shifted 1).eval x = 1 - 2 * x := by
  simp [shifted, Polynomial.shiftedLegendre, Finset.sum_range_succ]
  ring

/-- For `N_μ ≥ 2` the Legendre moment matrix does not annihilate the vector of ones, whose entries
are the `v⁰_{jk} = 1` of arXiv 2502.03008, Theorem 1. Its first entry is `1/√3`. -/
theorem momentMatrix_legendreP_mulVec_one_ne_zero (hK : 2 ≤ K) :
    Matrix.mulVec (momentMatrix (legendreP K)) (fun _ => 1) ≠ 0 := by
  set i0 : Fin K := ⟨0, by omega⟩ with hi0
  set i1 : Fin K := ⟨1, by omega⟩ with hi1
  have hP0 (μ : ℝ) : legendreP K i0 μ * μ = 1 / √3 * legendreP K i1 μ := by
    simp only [legendreP, hi0, hi1, Nat.cast_zero, Nat.cast_one, shifted_zero,
      Polynomial.eval_one, eval_shifted_one]
    have e0 : (2 * (0 : ℝ) + 1) / 2 = 1 / 2 := by norm_num
    have e1 : (2 * (1 : ℝ) + 1) / 2 = 3 * (1 / 2) := by norm_num
    have h3 : (√3 : ℝ) ≠ 0 := by positivity
    rw [e0, e1, Real.sqrt_mul (by norm_num)]
    field_simp
    ring
  have hrow (l : Fin K) : momentMatrix (legendreP K) i0 l = 1 / √3 * (if i1 = l then 1 else 0) := by
    rw [← (isL2Orthonormal_legendreP K).orthonormal i1 l, ← intervalIntegral.integral_const_mul]
    simp only [momentMatrix, Matrix.of_apply]
    refine intervalIntegral.integral_congr fun μ _ => ?_
    change legendreP K i0 μ * (μ * legendreP K l μ) =
      1 / √3 * (legendreP K i1 μ * legendreP K l μ)
    rw [← mul_assoc, hP0, mul_assoc]
  intro h
  have := congrFun h i0
  simp only [Matrix.mulVec, dotProduct, mul_one, hrow, Pi.zero_apply] at this
  rw [← Finset.mul_sum] at this
  simp at this

end Legendre

/-! ### Lemma 2 -/

section Lemma2

variable {N : ℕ} [NeZero N] {K : ℕ}

/-- The column version of Lemma 2: for one eigenvalue `a` with `|a| ≤ 1`, the upwind combination
of `D^x` and `D^xx` is controlled by `D⁺`. -/
lemma column_cfl {Δx Δt : ℝ} (hΔx : 0 < Δx) (hCFL : Δt ≤ Δx) {a : ℝ}
    (ha : |a| ≤ 1) (z : ZMod N → ℝ) :
    Δt / 2 * ∑ i, (((Dx Δx)ᵀ *ᵥ z) i * a - ((Dxx Δx)ᵀ *ᵥ z) i * |a|) ^ 2 ≤
      ∑ i, (((Dplus Δx)ᵀ *ᵥ z) i * √|a|) ^ 2 := by
  set D := ∑ i, (z (i + 1) - z i) ^ 2 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : √(2 * Δx) ^ 2 = 2 * Δx := Real.sq_sqrt (by positivity)
  have hs0 : √(2 * Δx) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hshift : ∑ i, (z i - z (i - 1)) ^ 2 = D := by
    rw [hD, ← sum_shift_sub (fun i => (z (i + 1) - z i) ^ 2)]
    simp
  have hr : ∑ i, (((Dplus Δx)ᵀ *ᵥ z) i * √|a|) ^ 2 = |a| / (2 * Δx) * D := by
    rw [← hshift, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Dplus_transpose_mulVec, mul_pow, div_pow, hsq, Real.sq_sqrt (abs_nonneg a)]
    field_simp
    ring
  have hl : ∑ i, (((Dx Δx)ᵀ *ᵥ z) i * a - ((Dxx Δx)ᵀ *ᵥ z) i * |a|) ^ 2 = a ^ 2 / Δx ^ 2 * D := by
    rw [Dx_transpose, Dxx_transpose]
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.neg_mulVec, Pi.neg_apply, Dx_mulVec, Dxx_mulVec]
      field_simp
      ring
    · rw [abs_of_neg h, ← hshift, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.neg_mulVec, Pi.neg_apply, Dx_mulVec, Dxx_mulVec]
      field_simp
      ring
  rw [hl, hr]
  have hb : Δt * a ^ 2 ≤ |a| * Δx := by
    have h1 : a ^ 2 ≤ |a| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg a]
    calc Δt * a ^ 2 ≤ Δx * |a| := mul_le_mul hCFL h1 (sq_nonneg a) hΔx.le
      _ = |a| * Δx := mul_comm _ _
  have : |a| / (2 * Δx) * D - Δt / 2 * (a ^ 2 / Δx ^ 2 * D) =
      (|a| * Δx - Δt * a ^ 2) * D / (2 * Δx ^ 2) := by
    field_simp
  have h2 : 0 ≤ (|a| * Δx - Δt * a ^ 2) * D / (2 * Δx ^ 2) :=
    div_nonneg (mul_nonneg (by linarith) hD0) (by positivity)
  linarith

/-- arXiv 2502.03008, Lemma 2, in matrix form, for any `A = Q M Qᵀ` with `|M_m| ≤ 1`. -/
theorem lemma_2_matrix {Δx Δt : ℝ} (hΔx : 0 < Δx) (hCFL : Δt ≤ Δx)
    {A Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ} (hd : IsDiagonalization A Q M)
    (hM : ∀ m, |M m| ≤ 1) (u : Matrix (ZMod N) (Fin K) ℝ) :
    Δt / 2 * ‖(Dx (N := N) Δx)ᵀ * u * A - (Dxx (N := N) Δx)ᵀ * u * absMat Q M‖ ^ 2 ≤
      ‖(Dplus (N := N) Δx)ᵀ * u * sqrtAbsMat Q M‖ ^ 2 := by
  set w := u * Q with hw
  have h1 : (Dx (N := N) Δx)ᵀ * u * A - (Dxx (N := N) Δx)ᵀ * u * absMat Q M =
      ((Dx (N := N) Δx)ᵀ * w * diagonal M -
        (Dxx (N := N) Δx)ᵀ * w * diagonal fun m => |M m|) * Qᵀ := by
    rw [hd.eq, hw, absMat, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have h2 : (Dplus (N := N) Δx)ᵀ * u * sqrtAbsMat Q M =
      ((Dplus (N := N) Δx)ᵀ * w * diagonal fun m => √|M m|) * Qᵀ := by
    rw [hw, sqrtAbsMat]
    simp only [Matrix.mul_assoc]
  rw [h1, h2, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hd.orthogonal,
    LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hd.orthogonal,
    LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum, Finset.sum_comm,
    Finset.sum_comm (f := fun i m =>
      (((Dplus (N := N) Δx)ᵀ * w * diagonal fun m => √|M m|) i m) ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  simp only [Matrix.sub_apply, Matrix.mul_diagonal]
  exact column_cfl hΔx hCFL (hM m) (fun i => w i m)

/-- Index form of the triple product `Dᵀ u A`. -/
lemma transpose_mul_mul_apply (D : Matrix (ZMod N) (ZMod N) ℝ) (u : Matrix (ZMod N) (Fin K) ℝ)
    (A : Matrix (Fin K) (Fin K) ℝ) (i : ZMod N) (l : Fin K) :
    (Dᵀ * u * A) i l = ∑ j, ∑ k, D j i * u j k * A k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- **Lemma 2 (CFL inequality)** (arXiv 2502.03008, Lemma 2; the paper cites its reference [1],
Lemma 5.2): if `Δt ≤ Δx`, then for every `u`
`(Δt/2) ∑_{iℓ} (∑_{jk} (D^x_{ji} u_{jk} A_{kℓ} - D^xx_{ji} u_{jk} |A|_{kℓ}))²
  - ∑_{iℓ} (∑_{jk} D⁺_{ji} u_{jk} |A|^{1/2}_{kℓ})² ≤ 0`.
Here `A` is the moment matrix of any `L²(-1, 1)`-orthonormal family, in particular of the normalized
Legendre polynomials (`isL2Orthonormal_legendreP`), and `Q M Qᵀ` is any diagonalization of `A`.
The bound `|M_m| ≤ 1` on the spectrum, used silently in the paper, is proved in
`abs_eigenvalue_le`. Differences from the paper: `Δx > 0` is arbitrary (the paper has
`Δx = 1/N_x`, and `Δx = 20/N_x` in its numerics). -/
theorem lemma_2 {Δx Δt : ℝ} (hΔx : 0 < Δx) (hCFL : Δt ≤ Δx)
    {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P) {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) (u : Matrix (ZMod N) (Fin K) ℝ) :
    Δt / 2 * ∑ i, ∑ l, (∑ j, ∑ k,
        (Dx Δx j i * u j k * momentMatrix P k l - Dxx Δx j i * u j k * absMat Q M k l)) ^ 2 -
      ∑ i, ∑ l, (∑ j, ∑ k, Dplus Δx j i * u j k * sqrtAbsMat Q M k l) ^ 2 ≤ 0 := by
  have h := lemma_2_matrix hΔx hCFL hd (abs_eigenvalue_le hP hd) u
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum] at h
  simp only [Matrix.sub_apply, transpose_mul_mul_apply, ← Finset.sum_sub_distrib] at h
  linarith

end Lemma2

/-! ### The conservative scheme (11) and Theorem 2 -/

section Conservative

variable {N : ℕ} [NeZero N] {K : ℕ} [NeZero K]

/-- The total energy `E = ½ ‖u‖_F² + ½ ‖B‖_E²` with `u_{jk} = B_j v_{jk}` (arXiv 2502.03008,
Definitions 2 and 3). -/
noncomputable def energy (B : ZMod N → ℝ) (v : Matrix (ZMod N) (Fin K) ℝ) : ℝ :=
  1 / 2 * ∑ j, ∑ k, (B j * v j k) ^ 2 + 1 / 2 * ∑ j, B j ^ 2

/-- The Kronecker symbol `δ_{k0}`. -/
noncomputable def delta0 (k : Fin K) : ℝ := if k = 0 then 1 else 0

/-- One step of the fully discrete **conservative scheme** (11a), (11b) of arXiv 2502.03008, from
`(v₀, B₀)` to `(v₁, B₁)`. It is implicit: see `exists_isConservativeStep` for solvability. -/
structure IsConservativeStep (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ)
    (B₀ B₁ : ZMod N → ℝ) (v₀ v₁ : Matrix (ZMod N) (Fin K) ℝ) : Prop where
  /-- Equation (11a). -/
  v_eq : ∀ j k, v₁ j k = v₀ j k
    - Δt * ∑ i, ∑ l, 1 / B₀ j * Dx Δx j i * B₀ i * v₀ i l * A k l
    + Δt * ∑ i, ∑ l, 1 / B₀ j * Dxx Δx j i * B₀ i * v₀ i l * absA k l
    + σ * Δt * (B₁ j / B₀ j) * (√2 * delta0 k - v₁ j k)
    - Δt * (1 / B₀ j) * ((B₁ j - B₀ j) / Δt) * v₁ j k
  /-- Equation (11b). -/
  B_eq : ∀ j, B₁ j = B₀ j + σ * Δt * B₁ j * (√2 * v₁ j 0 - 2)

omit [NeZero K] in
lemma sum_weighted (D : Matrix (ZMod N) (ZMod N) ℝ) (B : ZMod N → ℝ)
    (v : Matrix (ZMod N) (Fin K) ℝ) (A : Matrix (Fin K) (Fin K) ℝ) (c : ℝ) (j : ZMod N)
    (k : Fin K) :
    ∑ i, ∑ l, c * D j i * B i * v i l * A k l = c * (D * (diagonal B * v) * Aᵀ) j k := by
  have h (l : Fin K) : (D * (diagonal B * v)) j l = ∑ i, D j i * (B i * v i l) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
  rw [Matrix.mul_apply]
  simp only [h, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

omit [NeZero K] in
lemma energy_eq (B : ZMod N → ℝ) (v : Matrix (ZMod N) (Fin K) ℝ) :
    energy B v = 1 / 2 * ‖diagonal B * v‖ ^ 2 + 1 / 2 * ∑ j, B j ^ 2 := by
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum, energy]
  simp only [Matrix.diagonal_mul]

omit [NeZero K] in
lemma inner_skew_self {A : Matrix (Fin K) (Fin K) ℝ} (hA : Aᵀ = A) (Δx : ℝ)
    (u : Matrix (ZMod N) (Fin K) ℝ) :
    ⟪u, (Dx (N := N) Δx * u * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ = 0 := by
  have h : ⟪u, (Dx (N := N) Δx * u * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ =
      -⟪u, (Dx (N := N) Δx * u * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ := by
    conv_lhs => rw [Matrix.mul_assoc, LeanDLRA.Frobenius.inner_mul_left', Dx_transpose,
      Matrix.neg_mul, inner_neg_left, ← LeanDLRA.Frobenius.inner_mul_right, real_inner_comm]
    rw [hA]
  linarith

omit [NeZero K] in
/-- `⟨u, D^xx u |A|⟩ = -‖(D⁺)ᵀ u |A|^{1/2}‖²`. -/
lemma inner_Dxx_self {R : Matrix (Fin K) (Fin K) ℝ} {Δx : ℝ} (hΔx : 0 < Δx)
    (u : Matrix (ZMod N) (Fin K) ℝ) :
    ⟪u, (Dxx (N := N) Δx * u * (R * Rᵀ)ᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ =
      -‖(Dplus (N := N) Δx)ᵀ * u * R‖ ^ 2 := by
  have hRR : (R * Rᵀ)ᵀ = R * Rᵀ := by simp [Matrix.transpose_mul]
  rw [hRR, Dxx_eq_neg_Dplus_mul Δx hΔx, ← real_inner_self_eq_norm_sq, Matrix.neg_mul,
    Matrix.neg_mul, inner_neg_right, ← Matrix.mul_assoc _ R Rᵀ,
    LeanDLRA.Frobenius.inner_mul_right', Matrix.transpose_transpose,
    Matrix.mul_assoc (Dplus Δx) _ u, Matrix.mul_assoc (Dplus Δx),
    LeanDLRA.Frobenius.inner_mul_left', ← Matrix.mul_assoc _ u R]

omit [NeZero N] [NeZero K] in
/-- Clearing denominators in (11a). -/
lemma scheme_rearrange {Δt σ x y t s b0 b1 d : ℝ} (ht : Δt ≠ 0) (hb : b0 ≠ 0)
    (hx : x = y - Δt * (1 / b0 * t) + Δt * (1 / b0 * s) + σ * Δt * (b1 / b0) * (d - x)
      - Δt * (1 / b0) * ((b1 - b0) / Δt) * x) :
    b0 * x = b0 * y - Δt * t + Δt * s + σ * Δt * b1 * (d - x) - (b1 - b0) * x := by
  have h := congrArg (fun z => b0 * z) hx
  beta_reduce at h
  rw [h]
  field_simp

/-- The absorption terms of the two energy balances combine into a negative square. -/
lemma absorption_identity (x : Fin K → ℝ) :
    ∑ k, x k * (√2 * delta0 k - x k) + (√2 * x 0 - 2) =
      -∑ k, (x k - √2 * delta0 k) ^ 2 := by
  have h1 : ∑ k, x k * delta0 k = x 0 := by simp [delta0]
  have h2 : ∑ k : Fin K, delta0 k = 1 := by simp [delta0]
  have h3 (k : Fin K) : delta0 k ^ 2 = delta0 k := by
    by_cases h : k = 0 <;> simp [delta0, h]
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : ∑ k, x k * (√2 * delta0 k - x k) = √2 * x 0 - ∑ k, x k ^ 2 := by
    rw [← h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k, (x k - √2 * delta0 k) ^ 2 = ∑ k, x k ^ 2 - 2 * √2 * x 0 + 2 := by
    have : ∑ k, (x k - √2 * delta0 k) ^ 2 =
        ∑ k, x k ^ 2 - 2 * √2 * ∑ k, x k * delta0 k + 2 * ∑ k : Fin K, delta0 k := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x k - √2 * delta0 k) ^ 2 =
          x k ^ 2 - 2 * √2 * (x k * delta0 k) + √2 ^ 2 * delta0 k ^ 2 := by ring
      rw [this, hs, h3]
    rw [this, h1, h2, mul_one]
  rw [e1, e2]
  ring

/-- **The energy estimate behind arXiv 2502.03008, Theorem 2**, for a matrix `A = Q M Qᵀ` with
`|M_m| ≤ 1`. It is `theorem_2` without the moment structure of `A`. -/
theorem energy_le_of_isConservativeStep {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt)
    (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ) {A Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization A Q M) (hM : ∀ m, |M m| ≤ 1) {B₀ B₁ : ZMod N → ℝ}
    (hB₀ : ∀ j, B₀ j ≠ 0) {v₀ v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h : IsConservativeStep Δx Δt σ A (absMat Q M) B₀ B₁ v₀ v₁) :
    energy B₁ v₁ ≤ energy B₀ v₀ := by
  have hA := hd.transpose_eq
  set absA := absMat Q M with habsA
  set R := sqrtAbsMat Q M with hR
  have hRR : absA = R * Rᵀ := absMat_eq_sqrtAbsMat_mul hd
  have hRT : absAᵀ = absA := absMat_transpose Q M
  set u₀ : Matrix (ZMod N) (Fin K) ℝ := diagonal B₀ * v₀ with hu₀
  set u₁ : Matrix (ZMod N) (Fin K) ℝ := diagonal B₁ * v₁ with hu₁
  set T : Matrix (ZMod N) (Fin K) ℝ := Dx (N := N) Δx * u₀ * Aᵀ with hT
  set S : Matrix (ZMod N) (Fin K) ℝ := Dxx (N := N) Δx * u₀ * absAᵀ with hS
  set C : ℝ := ∑ j, ∑ k, B₁ j ^ 2 * v₁ j k * (√2 * delta0 k - v₁ j k) with hC
  have hu₀a (j : ZMod N) (k : Fin K) : u₀ j k = B₀ j * v₀ j k := by
    simp only [hu₀, Matrix.diagonal_mul]
  have hu₁a (j : ZMod N) (k : Fin K) : u₁ j k = B₁ j * v₁ j k := by
    simp only [hu₁, Matrix.diagonal_mul]
  -- equation (14), pointwise
  have hpt (j : ZMod N) (k : Fin K) : u₁ j k * u₁ j k = u₀ j k * u₁ j k - Δt * (u₁ j k * T j k)
      + Δt * (u₁ j k * S j k) + σ * Δt * (B₁ j ^ 2 * v₁ j k * (√2 * delta0 k - v₁ j k)) := by
    have e := h.v_eq j k
    rw [sum_weighted, sum_weighted] at e
    have e' := scheme_rearrange hΔt.ne' (hB₀ j) e
    rw [hu₀a, hu₁a]
    linear_combination (B₁ j * v₁ j k) * e'
  have h14 : ‖u₁‖ ^ 2 = ⟪u₀, u₁⟫ - Δt * ⟪u₁, T⟫ + Δt * ⟪u₁, S⟫ + σ * Δt * C := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [LeanDLRA.Frobenius.inner_def, hC, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hpt j k
  set w : Matrix (ZMod N) (Fin K) ℝ := u₀ - u₁ with hw
  set Y : Matrix (ZMod N) (Fin K) ℝ :=
    (Dx (N := N) Δx)ᵀ * u₁ * A - (Dxx (N := N) Δx)ᵀ * u₁ * absA with hY
  set G : Matrix (ZMod N) (Fin K) ℝ := (Dplus (N := N) Δx)ᵀ * u₁ * R with hG
  have hL2 : Δt / 2 * ‖Y‖ ^ 2 ≤ ‖G‖ ^ 2 := lemma_2_matrix hΔx hCFL hd hM u₁
  have hskew := inner_skew_self hA Δx u₁
  have hneg : ⟪u₁, (Dxx (N := N) Δx * u₁ * absAᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ = -‖G‖ ^ 2 := by
    rw [hRR]
    exact inner_Dxx_self hΔx u₁
  have hTs : T = Dx (N := N) Δx * w * Aᵀ + Dx (N := N) Δx * u₁ * Aᵀ := by
    rw [hT, hw, ← Matrix.add_mul, ← Matrix.mul_add, sub_add_cancel]
  have hSs : S = Dxx (N := N) Δx * w * absAᵀ + Dxx (N := N) Δx * u₁ * absAᵀ := by
    rw [hS, hw, ← Matrix.add_mul, ← Matrix.mul_add, sub_add_cancel]
  have hadj (D : Matrix (ZMod N) (ZMod N) ℝ) (Z : Matrix (Fin K) (Fin K) ℝ) :
      ⟪u₁, (D * w * Zᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ =
        ⟪(Dᵀ * u₁ * Z : Matrix (ZMod N) (Fin K) ℝ), w⟫ := by
    rw [LeanDLRA.Frobenius.inner_mul_right', Matrix.transpose_transpose,
      LeanDLRA.Frobenius.inner_mul_left']
    exact congrArg (fun X => ⟪X, w⟫) (Matrix.mul_assoc Dᵀ u₁ Z).symm
  have hYw : ⟪u₁, (Dx (N := N) Δx * w * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫
      - ⟪u₁, (Dxx (N := N) Δx * w * absAᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ = ⟪Y, w⟫ := by
    rw [hadj, hadj, hY, inner_sub_left]
  have hyoung : 0 ≤ Δt ^ 2 * ‖Y‖ ^ 2 + 2 * Δt * ⟪Y, w⟫ + ‖w‖ ^ 2 := by
    have := norm_add_sq_real (Δt • Y) w
    rw [norm_smul, mul_pow, real_inner_smul_left, Real.norm_eq_abs, sq_abs] at this
    have h0 : 0 ≤ ‖Δt • Y + w‖ ^ 2 := by positivity
    linarith
  have hnw : ‖w‖ ^ 2 = ‖u₀‖ ^ 2 - 2 * ⟪u₀, u₁⟫ + ‖u₁‖ ^ 2 := norm_sub_sq_real u₀ u₁
  have hL2' : Δt * (Δt / 2 * ‖Y‖ ^ 2) ≤ Δt * ‖G‖ ^ 2 := mul_le_mul_of_nonneg_left hL2 hΔt.le
  have h15 : 1 / 2 * ‖u₁‖ ^ 2 ≤ 1 / 2 * ‖u₀‖ ^ 2 + σ * Δt * C := by
    rw [hTs, hSs, inner_add_right, inner_add_right, hskew, hneg] at h14
    have : Δt * ⟪Y, w⟫ = Δt * ⟪u₁, (Dx (N := N) Δx * w * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫
        - Δt * ⟪u₁, (Dxx (N := N) Δx * w * absAᵀ : Matrix (ZMod N) (Fin K) ℝ)⟫ := by
      rw [← hYw]
      ring
    nlinarith
  have h12 : 1 / 2 * ∑ j, B₁ j ^ 2 ≤ 1 / 2 * ∑ j, B₀ j ^ 2 +
      σ * Δt * ∑ j, B₁ j ^ 2 * (√2 * v₁ j 0 - 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have e : B₁ j * B₁ j = B₀ j * B₁ j + σ * Δt * (B₁ j ^ 2 * (√2 * v₁ j 0 - 2)) := by
      linear_combination (B₁ j) * h.B_eq j
    nlinarith [sq_nonneg (B₁ j - B₀ j)]
  have habs : C + ∑ j, B₁ j ^ 2 * (√2 * v₁ j 0 - 2) ≤ 0 := by
    have : C + ∑ j, B₁ j ^ 2 * (√2 * v₁ j 0 - 2) =
        -∑ j, B₁ j ^ 2 * ∑ k, (v₁ j k - √2 * delta0 k) ^ 2 := by
      rw [hC, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := absorption_identity (fun k => v₁ j k)
      have h1 : ∑ k, B₁ j ^ 2 * v₁ j k * (√2 * delta0 k - v₁ j k) =
          B₁ j ^ 2 * ∑ k, v₁ j k * (√2 * delta0 k - v₁ j k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h1]
      linear_combination (B₁ j ^ 2) * this
    rw [this, neg_nonpos]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hsd : 0 ≤ σ * Δt := mul_nonneg hσ hΔt.le
  have h3 := mul_nonpos_of_nonneg_of_nonpos hsd habs
  rw [energy_eq, energy_eq]
  rw [mul_add] at h3
  linarith

/-- **Theorem 2 (energy stability of the conservative scheme)** (arXiv 2502.03008, Theorem 2):
under `Δt ≤ Δx`, every solution `(v₁, B₁)` of the fully discrete conservative scheme (11) satisfies
`E¹ ≤ E⁰` with `E = ½ ‖u‖_F² + ½ ‖B‖_E²`, `u_{jk} = B_j v_{jk}`.

`A` is the moment matrix of an `L²(-1, 1)`-orthonormal family, in particular of the normalized
Legendre polynomials (`isL2Orthonormal_legendreP`), and `|A| = Q |M| Qᵀ` for any diagonalization.
Differences from the paper: `Δx > 0` is arbitrary (the paper has `Δx = 1/N_x`); `σ ≥ 0` and
`Δt > 0` are stated (the paper leaves them implicit); `B₀ > 0` is only used through `B₀ j ≠ 0`, and
no sign of `B₁` is needed. Solutions exist: `exists_isConservativeStep`. -/
theorem theorem_2 {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt) (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ)
    {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P) {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) {B₀ B₁ : ZMod N → ℝ} (hB₀ : ∀ j, 0 < B₀ j)
    {v₀ v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h : IsConservativeStep Δx Δt σ (momentMatrix P) (absMat Q M) B₀ B₁ v₀ v₁) :
    energy B₁ v₁ ≤ energy B₀ v₀ :=
  energy_le_of_isConservativeStep hΔx hΔt hCFL hσ hd (abs_eigenvalue_le hP hd)
    (fun j => (hB₀ j).ne') h

/-- The explicit part `F_{jk}` of (11a), that is `v⁰_{jk} - Δt ∑∑ (1/B⁰_j) D^x_{ji} B⁰_i v⁰_{iℓ}
A_{kℓ} + Δt ∑∑ (1/B⁰_j) D^xx_{ji} B⁰_i v⁰_{iℓ} |A|_{kℓ}`. -/
noncomputable def explicitPart (Δx Δt : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (v₀ : Matrix (ZMod N) (Fin K) ℝ) : Matrix (ZMod N) (Fin K) ℝ :=
  Matrix.of fun j k => v₀ j k
    - Δt * ∑ i, ∑ l, 1 / B₀ j * Dx Δx j i * B₀ i * v₀ i l * A k l
    + Δt * ∑ i, ∑ l, 1 / B₀ j * Dxx Δx j i * B₀ i * v₀ i l * absA k l

/-- The form (18) of the scheme, which is what the DLRA scheme discretizes. If the two equations
(18a), (18b) hold, so does (11). -/
lemma isConservativeStep_of_reduced {Δx Δt σ : ℝ} (hΔt : Δt ≠ 0)
    {A absA : Matrix (Fin K) (Fin K) ℝ} {B₀ B₁ : ZMod N → ℝ} (hB₀ : ∀ j, B₀ j ≠ 0)
    {v₀ v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h18a : ∀ j k, (1 + σ * Δt) * (B₁ j / B₀ j) * v₁ j k =
      explicitPart Δx Δt A absA B₀ v₀ j k + √2 * (σ * Δt) * (B₁ j / B₀ j) * delta0 k)
    (h18b : ∀ j, B₁ j / B₀ j = 1 + σ * Δt * (B₁ j / B₀ j) * (√2 * v₁ j 0 - 2)) :
    IsConservativeStep Δx Δt σ A absA B₀ B₁ v₀ v₁ := by
  constructor
  · intro j k
    have e := h18a j k
    simp only [explicitPart, Matrix.of_apply] at e
    have e1 : Δt * (1 / B₀ j) * ((B₁ j - B₀ j) / Δt) = B₁ j / B₀ j - 1 := by
      have := hB₀ j
      field_simp
    rw [e1]
    linear_combination e
  · intro j
    have hb := hB₀ j
    have e := h18b j
    have e1 : B₁ j = B₀ j * (B₁ j / B₀ j) := by field_simp
    calc B₁ j = B₀ j * (B₁ j / B₀ j) := e1
      _ = B₀ j * (1 + σ * Δt * (B₁ j / B₀ j) * (√2 * v₁ j 0 - 2)) := by rw [← e]
      _ = B₀ j + σ * Δt * (B₀ j * (B₁ j / B₀ j)) * (√2 * v₁ j 0 - 2) := by ring
      _ = B₀ j + σ * Δt * B₁ j * (√2 * v₁ j 0 - 2) := by rw [← e1]

omit [NeZero N] [NeZero K] in
/-- The coupled equations for `B¹/B⁰` and the zeroth moment are linear in `r = B¹/B⁰` and
`r φ`, with determinant `1 + 3 s`, `s = σΔt`. -/
lemma solve_zeroth {s F : ℝ} (hs : 0 ≤ s) (h : 1 + s + √2 * s * F ≠ 0) :
    ∃ r φ : ℝ, r ≠ 0 ∧ r = 1 + s * r * (√2 * φ - 2) ∧ (1 + s) * r * φ = F + √2 * s * r := by
  have h1 : 1 + s ≠ 0 := by positivity
  have h3 : 1 + 3 * s ≠ 0 := by positivity
  have hs2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set r := (1 + s + √2 * s * F) / (1 + 3 * s) with hr
  have hr0 : r ≠ 0 := div_ne_zero h h3
  have hr' : r * (1 + 3 * s) = 1 + s + √2 * s * F := by
    rw [hr]
    field_simp
  refine ⟨r, (F + √2 * s * r) / ((1 + s) * r), hr0, ?_, by field_simp⟩
  have hx : (1 + s) * r * ((F + √2 * s * r) / ((1 + s) * r)) = F + √2 * s * r := by
    field_simp
  generalize (F + √2 * s * r) / ((1 + s) * r) = x at hx ⊢
  apply mul_left_cancel₀ h1
  linear_combination (-s * √2) * hx + hr' - s ^ 2 * r * hs2

/-- **Solvability of the implicit scheme (11)** (non-vacuity of `theorem_2`). As remarked in
arXiv 2502.03008, Section 5.2, the equations for `(B¹/B⁰) v¹_{j0}` and `B¹/B⁰` couple; the system
is linear with determinant `1 + 3 σΔt > 0`, and (11) has a solution as soon as the resulting ratio
`B¹_j/B⁰_j = (1 + σΔt + √2 σΔt F_{j0}) / (1 + 3 σΔt)` is nonzero. For `σ = 0` the ratio is `1`. -/
theorem exists_isConservativeStep {Δx Δt σ : ℝ} (hΔt : 0 < Δt) (hσ : 0 ≤ σ)
    (A absA : Matrix (Fin K) (Fin K) ℝ) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, B₀ j ≠ 0)
    (v₀ : Matrix (ZMod N) (Fin K) ℝ)
    (hr : ∀ j, 1 + σ * Δt + √2 * (σ * Δt) * explicitPart Δx Δt A absA B₀ v₀ j 0 ≠ 0) :
    ∃ (B₁ : ZMod N → ℝ) (v₁ : Matrix (ZMod N) (Fin K) ℝ),
      IsConservativeStep Δx Δt σ A absA B₀ B₁ v₀ v₁ := by
  have hs0 : 0 ≤ σ * Δt := mul_nonneg hσ hΔt.le
  have h1 : 1 + σ * Δt ≠ 0 := by positivity
  choose r φ hr0 hr1 hr2 using fun j => solve_zeroth hs0 (hr j)
  have hratio (j : ZMod N) : B₀ j * r j / B₀ j = r j := by
    have := hB₀ j
    field_simp
  refine ⟨fun j => B₀ j * r j, Matrix.of fun j k =>
    if k = 0 then φ j else explicitPart Δx Δt A absA B₀ v₀ j k / ((1 + σ * Δt) * r j), ?_⟩
  refine isConservativeStep_of_reduced hΔt.ne' hB₀ (fun j k => ?_) (fun j => ?_)
  · simp only [Matrix.of_apply, hratio, delta0]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true, mul_one]
      exact hr2 j
    · have := hr0 j
      simp only [hk, ite_false, mul_zero, add_zero]
      field_simp
  · simp only [Matrix.of_apply, hratio, ite_true]
    exact hr1 j

end Conservative

/-! ### The advection form (10) and Theorem 1 -/

section Advection

variable {N : ℕ} [NeZero N] {K : ℕ} [NeZero K]

/-- One step of the fully discrete **advection form** (10a), (10b) of arXiv 2502.03008. -/
structure IsAdvectionStep (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ)
    (B₀ B₁ : ZMod N → ℝ) (v₀ v₁ : Matrix (ZMod N) (Fin K) ℝ) : Prop where
  /-- Equation (10a). -/
  v_eq : ∀ j k, v₁ j k = v₀ j k
    - Δt * ∑ i, ∑ l, Dx Δx j i * v₀ i l * A k l
    + Δt * ∑ i, ∑ l, Dxx Δx j i * v₀ i l * absA k l
    + σ * Δt * (√2 * delta0 k - v₁ j k)
    - Δt * (1 / B₀ j) * ((B₁ j - B₀ j) / Δt) * v₁ j k
    - Δt * ∑ i, ∑ l, v₀ j l / B₀ j * Dx Δx j i * B₀ i * A k l
  /-- Equation (10b). -/
  B_eq : ∀ j, B₁ j = B₀ j + σ * Δt * B₁ j * (√2 * v₁ j 0 - 2)

omit [NeZero K] in
lemma mul_mul_transpose_apply (D : Matrix (ZMod N) (ZMod N) ℝ) (u : Matrix (ZMod N) (Fin K) ℝ)
    (A : Matrix (Fin K) (Fin K) ℝ) (j : ZMod N) (k : Fin K) :
    (D * u * Aᵀ) j k = ∑ i, ∑ l, D j i * u i l * A k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Forward Euler with centred differences for `∂ₜ u + μ ∂ₓ u = 0`:
`u¹_{jk} = u⁰_{jk} - Δt ∑∑ D^x_{ji} u⁰_{iℓ} A_{kℓ}`. -/
noncomputable def ftcs (Δx Δt : ℝ) (A : Matrix (Fin K) (Fin K) ℝ)
    (u : Matrix (ZMod N) (Fin K) ℝ) : Matrix (ZMod N) (Fin K) ℝ :=
  Matrix.of fun j k => u j k - Δt * ∑ i, ∑ l, Dx Δx j i * u i l * A k l

omit [NeZero K] in
lemma sum_Dx_apply (Δx : ℝ) (j : ZMod N) : ∑ i, Dx (N := N) Δx j i = 0 := by
  have := Dx_mulVec (N := N) Δx (fun _ => 1) j
  simp only [mulVec, dotProduct, mul_one] at this
  rw [this]
  norm_num

omit [NeZero K] in
lemma sum_Dxx_apply (Δx : ℝ) (j : ZMod N) : ∑ i, Dxx (N := N) Δx j i = 0 := by
  have := Dxx_mulVec (N := N) Δx (fun _ => 1) j
  simp only [mulVec, dotProduct, mul_one] at this
  rw [this]
  norm_num

omit [NeZero K] in
lemma sum_mul_const (D : Matrix (ZMod N) (ZMod N) ℝ) (hD : ∀ j, ∑ i, D j i = 0)
    (c : Fin K → ℝ) (A : Matrix (Fin K) (Fin K) ℝ) (j : ZMod N) (k : Fin K) :
    ∑ i, ∑ l, D j i * c l * A k l = 0 := by
  have : ∑ i, ∑ l, D j i * c l * A k l = (∑ i, D j i) * ∑ l, c l * A k l := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this, hD, zero_mul]

/-- Data that are constant in space: `v_{jk} = c_k`. -/
def constInSpace (c : Fin K → ℝ) : Matrix (ZMod N) (Fin K) ℝ := Matrix.of fun _ k => c k

omit [NeZero N] [NeZero K] in
@[simp] lemma constInSpace_apply (c : Fin K → ℝ) (j : ZMod N) (k : Fin K) :
    constInSpace c j k = c k := rfl

/-- **Reduction step in Theorem 1** (arXiv 2502.03008, proof of Theorem 1): for `σ = 0` and data
`v⁰` that are constant in space (`v⁰_{jk} = c_k`, the paper's example being `c_k = 1`) the
advection scheme (10) has `B¹ = B⁰`, and `u = B v` evolves by forward Euler with centred
differences. -/
theorem advection_reduces_to_ftcs {Δx Δt : ℝ} {A absA : Matrix (Fin K) (Fin K) ℝ}
    {B₀ B₁ : ZMod N → ℝ} (hB₀ : ∀ j, B₀ j ≠ 0) (c : Fin K → ℝ)
    {v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h : IsAdvectionStep Δx Δt 0 A absA B₀ B₁ (constInSpace c) v₁) :
    B₁ = B₀ ∧ diagonal B₁ * v₁ = ftcs Δx Δt A (diagonal B₀ * constInSpace (N := N) c) := by
  have hB : B₁ = B₀ := by
    ext j
    simpa using h.B_eq j
  refine ⟨hB, ?_⟩
  subst hB
  ext j k
  have e := h.v_eq j k
  simp only [constInSpace_apply, sum_mul_const _ (sum_Dx_apply Δx) c A j k,
    sum_mul_const _ (sum_Dxx_apply Δx) c absA j k] at e
  simp only [ftcs, Matrix.of_apply, Matrix.diagonal_mul, constInSpace_apply]
  have hb := hB₀ j
  have e2 : ∑ i, ∑ l, c l / B₁ j * Dx Δx j i * B₁ i * A k l =
      1 / B₁ j * ∑ i, ∑ l, Dx Δx j i * (B₁ i * c l) * A k l := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    field_simp
  rw [e2] at e
  simp only [sub_self, zero_div, mul_zero, zero_mul, add_zero, sub_zero] at e
  rw [e]
  field_simp

omit [NeZero K] in
/-- The skew form of the growth in arXiv 2502.03008, Theorem 1:
`‖u - Δt S u‖² = ‖u‖² + Δt² ‖S u‖²`, with `S u = D^x u Aᵀ`. -/
theorem norm_sq_ftcs {Δx Δt : ℝ} {A : Matrix (Fin K) (Fin K) ℝ} (hA : Aᵀ = A)
    (u : Matrix (ZMod N) (Fin K) ℝ) :
    ‖ftcs Δx Δt A u‖ ^ 2 = ‖u‖ ^ 2 + Δt ^ 2 *
      ‖(Dx (N := N) Δx * u * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)‖ ^ 2 := by
  have h : ftcs Δx Δt A u = u - Δt • (Dx (N := N) Δx * u * Aᵀ) := by
    ext j k
    simp only [ftcs, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      mul_mul_transpose_apply]
  rw [h, norm_sub_sq_real, norm_smul, mul_pow, real_inner_smul_right, inner_skew_self hA,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The amplification factor `1 - i a (Δt/Δx) sin(2π m/N)` of forward Euler with centred
differences for the wave number `m` and the speed `a`. -/
noncomputable def amplification (Δx Δt a : ℝ) (m : ZMod N) : ℂ :=
  1 - Complex.I * ((a * (Δt / Δx) * Real.sin (2 * Real.pi * m.val / N) : ℝ) : ℂ)

/-- The complex version of `ftcs`, on which the von Neumann analysis is done. -/
noncomputable def ftcsC (Δx Δt : ℝ) (A : Matrix (Fin K) (Fin K) ℝ)
    (u : Matrix (ZMod N) (Fin K) ℂ) : Matrix (ZMod N) (Fin K) ℂ :=
  Matrix.of fun j k => u j k - Δt * ∑ i, ∑ l, (Dx Δx j i : ℂ) * u i l * (A k l : ℂ)

omit [NeZero K] in
/-- `ftcsC` is the complexification of `ftcs`. -/
lemma ftcsC_map_ofReal (Δx Δt : ℝ) (A : Matrix (Fin K) (Fin K) ℝ)
    (u : Matrix (ZMod N) (Fin K) ℝ) :
    ftcsC Δx Δt A (u.map Complex.ofReal) = (ftcs Δx Δt A u).map Complex.ofReal := by
  ext j k
  simp [ftcsC, ftcs]

/-- The Fourier mode `e^{2π i m j / N}`. -/
noncomputable def fourierMode (m j : ZMod N) : ℂ := ZMod.stdAddChar (m * j)

omit [NeZero K] in
/-- **The von Neumann ansatz** behind arXiv 2502.03008, Theorem 1: a Fourier mode in space times an
eigenvector of `A` is an eigenfunction of forward Euler with centred differences, with eigenvalue
`amplification`. -/
theorem ftcsC_mode {Δx : ℝ} (hΔx : Δx ≠ 0) (Δt : ℝ) {A : Matrix (Fin K) (Fin K) ℝ} {a : ℝ}
    {w : Fin K → ℝ} (hw : A *ᵥ w = a • w) (m : ZMod N) :
    ftcsC Δx Δt A (Matrix.of fun j k => fourierMode m j * (w k : ℂ)) =
      amplification Δx Δt a m • (Matrix.of fun j k => fourierMode m j * (w k : ℂ) :
        Matrix (ZMod N) (Fin K) ℂ) := by
  have hrow (j : ZMod N) : ∑ i, (Dx Δx j i : ℂ) * fourierMode m i =
      fourierMode m j * (Complex.I * ((Real.sin (2 * Real.pi * m.val / N) / Δx : ℝ) : ℂ)) := by
    have hD (f : ZMod N → ℂ) : ∑ i, (Dx Δx j i : ℂ) * f i =
        (f (j + 1) - f (j - 1)) / (2 * Δx) := by
      have hDa (i : ZMod N) : (Dx Δx j i : ℂ) =
          ((if i = j + 1 then (1 : ℂ) else 0) - (if i = j - 1 then 1 else 0)) / (2 * Δx) := by
        simp only [Dx, Matrix.of_apply]
        split_ifs <;> simp
      calc ∑ i, (Dx Δx j i : ℂ) * f i
          = ∑ i, ((if i = j + 1 then f i else 0) - (if i = j - 1 then f i else 0)) / (2 * Δx) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hDa]
            split_ifs <;> ring
        _ = (f (j + 1) - f (j - 1)) / (2 * Δx) := by
            rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
            simp
    set θ : ℝ := 2 * Real.pi * m.val / N with hθ
    have he : ZMod.stdAddChar m = Complex.exp (θ * Complex.I) := by
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hθ]
      push_cast
      ring_nf
    have he' : ZMod.stdAddChar (-m) = Complex.exp ((-θ : ℝ) * Complex.I) := by
      rw [AddChar.map_neg_eq_inv, he, ← Complex.exp_neg]
      push_cast
      ring_nf
    have h1 : fourierMode m (j + 1) = fourierMode m j * ZMod.stdAddChar m := by
      simp only [fourierMode, mul_add, mul_one, AddChar.map_add_eq_mul]
    have h2 : fourierMode m (j - 1) = fourierMode m j * ZMod.stdAddChar (-m) := by
      have : m * (j - 1) = m * j + -m := by ring
      simp only [fourierMode]
      rw [this, AddChar.map_add_eq_mul]
    have hc : (Δx : ℂ) ≠ 0 := by exact_mod_cast hΔx
    rw [hD, h1, h2, he, he', Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    field_simp
    ring
  have hcol (k : Fin K) : ∑ l, (w l : ℂ) * (A k l : ℂ) = (a : ℂ) * (w k : ℂ) := by
    have := congrFun hw k
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [← Complex.ofReal_mul, ← this]
    push_cast
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  ext j k
  simp only [ftcsC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, amplification]
  have hsum : ∑ i, ∑ l, (Dx Δx j i : ℂ) * (fourierMode m i * (w l : ℂ)) * (A k l : ℂ) =
      (∑ i, (Dx Δx j i : ℂ) * fourierMode m i) * ∑ l, (w l : ℂ) * (A k l : ℂ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsum, hrow, hcol]
  have : (Δx : ℂ) ≠ 0 := by exact_mod_cast hΔx
  push_cast
  field_simp

omit [NeZero N] in
/-- The amplification factor of arXiv 2502.03008, Theorem 1: `|g|² = 1 + (a (Δt/Δx) sin θ)²`. -/
theorem norm_amplification_sq (Δx Δt a : ℝ) (m : ZMod N) :
    ‖amplification Δx Δt a m‖ ^ 2 =
      1 + (a * (Δt / Δx) * Real.sin (2 * Real.pi * m.val / N)) ^ 2 := by
  rw [Complex.sq_norm, amplification]
  generalize a * (Δt / Δx) * Real.sin (2 * Real.pi * m.val / N) = t
  simp [Complex.normSq_apply]
  ring

/-- The condition of von Neumann for forward Euler with centred differences at the fixed CFL number
`ν = Δt/Δx`, on the grids `Δx = 1/N`: there is `C` with `|g(m)| ≤ 1 + C Δt` for every grid and
every wave number. -/
def IsVonNeumannStable (a ν : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (m : ZMod N),
    ‖amplification (1 / (N : ℝ)) (ν / N) a m‖ ≤ 1 + C * (ν / N)

/-- **Forward Euler with centred differences is not von Neumann stable** at any CFL number
`ν > 0` as soon as the speed `a` is nonzero. This is the fact which arXiv 2502.03008, Theorem 1,
quotes from LeVeque's book. -/
theorem not_isVonNeumannStable {a ν : ℝ} (ha : a ≠ 0) (hν : 0 < ν) :
    ¬ IsVonNeumannStable a ν := by
  rintro ⟨C, hC⟩
  set g := √(1 + (a * ν) ^ 2) with hg
  have hg1 : 1 < g := by
    rw [hg, Real.lt_sqrt (by norm_num)]
    have : 0 < (a * ν) ^ 2 := by positivity
    linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (|C| * ν / (4 * (g - 1)))
  have hL0 : 0 < (L : ℝ) :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg (abs_nonneg C) hν.le) (by linarith)) hL
  have hLn : 0 < L := by exact_mod_cast hL0
  have : NeZero (4 * L) := ⟨by omega⟩
  have h := hC (4 * L) (L : ZMod (4 * L))
  have hval : ((L : ZMod (4 * L))).val = L := ZMod.val_natCast_of_lt (by omega)
  have hNc : ((4 * L : ℕ) : ℝ) = 4 * L := by push_cast; ring
  have hsin : Real.sin (2 * Real.pi * ((L : ZMod (4 * L))).val / ((4 * L : ℕ) : ℝ)) = 1 := by
    rw [hval, hNc]
    have : 2 * Real.pi * L / (4 * L) = Real.pi / 2 := by
      field_simp
      ring
    rw [this, Real.sin_pi_div_two]
  have hn := norm_amplification_sq (N := 4 * L) (1 / ((4 * L : ℕ) : ℝ)) (ν / ((4 * L : ℕ) : ℝ)) a
    (L : ZMod (4 * L))
  have e : a * (ν / ((4 * L : ℕ) : ℝ) / (1 / ((4 * L : ℕ) : ℝ))) * 1 = a * ν := by
    rw [hNc]
    field_simp
  rw [hsin, e] at hn
  have hgn : ‖amplification (N := 4 * L) (1 / ((4 * L : ℕ) : ℝ)) (ν / ((4 * L : ℕ) : ℝ)) a
      (L : ZMod (4 * L))‖ = g := by
    rw [hg, ← hn, Real.sqrt_sq (norm_nonneg _)]
  rw [hgn, hNc] at h
  have hb : C * (ν / (4 * L)) ≤ |C| * ν / (4 * L) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hν.le)
      (by positivity)
  have hc : |C| * ν / (4 * L) < g - 1 := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by linarith)] at hL
    linarith
  linarith

omit [NeZero K] in
lemma transport_constInSpace_apply (Δx : ℝ) (B : ZMod N → ℝ) (c : Fin K → ℝ)
    (A : Matrix (Fin K) (Fin K) ℝ) (j : ZMod N) (k : Fin K) :
    (Dx (N := N) Δx * (diagonal B * constInSpace (N := N) c) * Aᵀ) j k =
      (Dx Δx *ᵥ B) j * (A *ᵥ c) k := by
  rw [mul_mul_transpose_apply]
  simp only [Matrix.diagonal_mul, constInSpace_apply, mulVec, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- For `σ = 0` the scheme (10) of arXiv 2502.03008 is explicit, so it has a solution from
space-constant data. -/
theorem exists_isAdvectionStep (Δx Δt : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ)
    (B₀ : ZMod N → ℝ) (c : Fin K → ℝ) :
    ∃ v₁ : Matrix (ZMod N) (Fin K) ℝ, IsAdvectionStep Δx Δt 0 A absA B₀ B₀ (constInSpace c) v₁ := by
  refine ⟨Matrix.of fun j k => c k - Δt * ∑ i, ∑ l, c l / B₀ j * Dx Δx j i * B₀ i * A k l,
    ⟨fun j k => ?_, fun j => by simp⟩⟩
  simp only [constInSpace_apply, Matrix.of_apply, sum_mul_const _ (sum_Dx_apply Δx) c A j k,
    sum_mul_const _ (sum_Dxx_apply Δx) c absA j k]
  simp

/-- **The advection scheme gains energy** (arXiv 2502.03008, Section 4.1) whenever the
space-constant data are moved at all: from `v⁰_{jk} = c_k` with `σ = 0`, one step of (10) gives
`E¹ = E⁰ + ½ Δt² ‖D^x u⁰ A‖²`, for every `Δt`, in contrast to `theorem_2`. -/
theorem advection_energy_eq {Δx Δt : ℝ} {A absA : Matrix (Fin K) (Fin K) ℝ} (hA : Aᵀ = A)
    {B₀ B₁ : ZMod N → ℝ} (hB₀ : ∀ j, B₀ j ≠ 0) (c : Fin K → ℝ)
    {v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h : IsAdvectionStep Δx Δt 0 A absA B₀ B₁ (constInSpace c) v₁) :
    energy B₁ v₁ = energy B₀ (constInSpace c) + Δt ^ 2 / 2 *
      ‖(Dx (N := N) Δx * (diagonal B₀ * constInSpace (N := N) c) * Aᵀ :
        Matrix (ZMod N) (Fin K) ℝ)‖ ^ 2 := by
  obtain ⟨rfl, hu⟩ := advection_reduces_to_ftcs hB₀ c h
  rw [energy_eq, energy_eq, hu, norm_sq_ftcs hA]
  ring

omit [NeZero K] in
/-- Any nonzero symmetric matrix has a nonzero eigenvalue. -/
lemma exists_eigenpair {A : Matrix (Fin K) (Fin K) ℝ} (hA : Aᵀ = A) (h : A ≠ 0) :
    ∃ (a : ℝ) (w : Fin K → ℝ), a ≠ 0 ∧ w ≠ 0 ∧ A *ᵥ w = a • w := by
  obtain ⟨Q, M, hd⟩ := exists_isDiagonalization hA
  obtain ⟨m, hm⟩ : ∃ m, M m ≠ 0 := by
    by_contra hc
    apply h
    have : M = 0 := funext fun m => not_not.1 fun hm => hc ⟨m, hm⟩
    rw [hd.eq, this]
    simp
  have hQ := hd.orthogonal
  refine ⟨M m, Q *ᵥ Pi.single m 1, hm, fun h0 => ?_, ?_⟩
  · have h1 := congrArg (fun v => Qᵀ *ᵥ v) h0
    simp only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have := congrFun h1 m
    simp at this
  · conv_lhs => rw [hd.eq]
    rw [Matrix.mulVec_mulVec]
    have : Q * diagonal M * Qᵀ * Q = Q * diagonal M := by
      rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
    have hd2 : diagonal M *ᵥ (Pi.single m 1 : Fin K → ℝ) = M m • Pi.single m 1 := by
      rw [Matrix.diagonal_mulVec_single, mul_one]
      ext i
      by_cases hi : i = m
      · subst hi
        simp
      · simp [Pi.single_eq_of_ne hi]
    rw [this, ← Matrix.mulVec_mulVec, hd2, Matrix.mulVec_smul]

omit [NeZero N] [NeZero K] in
/-- A growing Fourier mode (arXiv 2502.03008, Theorem 1) exists on every grid with at least three
points. -/
theorem exists_one_lt_norm_amplification (hN : 3 ≤ N) {Δx Δt a : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt)
    (ha : a ≠ 0) : ∃ m : ZMod N, 1 < ‖amplification Δx Δt a m‖ := by
  refine ⟨1, ?_⟩
  have hval : (1 : ZMod N).val = 1 := by
    have : Fact (1 < N) := ⟨by omega⟩
    exact ZMod.val_one N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hsin : 0 < Real.sin (2 * Real.pi * ((1 : ZMod N).val : ℝ) / N) := by
    rw [hval]
    apply Real.sin_pos_of_pos_of_lt_pi
    · have := Real.pi_pos
      positivity
    · rw [div_lt_iff₀ hN0]
      have := Real.pi_pos
      push_cast
      nlinarith
  have hn := norm_amplification_sq Δx Δt a (1 : ZMod N)
  have hpos : 0 < (a * (Δt / Δx) * Real.sin (2 * Real.pi * ((1 : ZMod N).val : ℝ) / N)) ^ 2 := by
    have : a * (Δt / Δx) * Real.sin (2 * Real.pi * ((1 : ZMod N).val : ℝ) / N) ≠ 0 := by
      have h1 : Δt / Δx ≠ 0 := (div_pos hΔt hΔx).ne'
      exact mul_ne_zero (mul_ne_zero ha h1) hsin.ne'
    positivity
  have h1 : (1 : ℝ) ^ 2 < ‖amplification Δx Δt a (1 : ZMod N)‖ ^ 2 := by
    rw [hn]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- **Theorem 1 (the advection form is not von Neumann stable)** (arXiv 2502.03008, Theorem 1).
For `N_x ≥ 3`, `N_μ ≥ 2`, any `Δx, Δt > 0` and any matrix `|A|`, with `A` the Legendre moment matrix
and `σ = 0`, there are initial values `v⁰_{jk} = 1`, `B⁰ > 0` such that

* the scheme (10) has a solution;
* every solution has `B¹ = B⁰` and evolves `u = B v` by forward Euler with centred differences for
  `∂ₜ u + μ ∂ₓ u = 0`, as in the paper's proof;
* the energy strictly grows, `E⁰ < E¹` (for every `Δt`, not only outside a CFL condition);
* `A` has an eigenvalue `a ≠ 0`, for which a Fourier mode has amplification factor of modulus
  `> 1` (`ftcsC_mode` shows that `amplification` is the eigenvalue of forward Euler with centred
  differences on such a mode), and von Neumann's condition `|g| ≤ 1 + C Δt` fails at every CFL
  number `ν > 0`, the case `ν ≤ 1` of `theorem_2` included.

Differences from the paper: the paper only quotes the instability of forward Euler with centred
differences (its reference [21]); here it is proved, for that reduced scheme. The reduction holds
for the first step only, since `v¹` is no longer constant: the von Neumann statement concerns the
reduced scheme, as in the paper, while the energy growth is a statement about (10) itself. The
scheme needs `N_x ≥ 3`, `N_μ ≥ 2`, as `D^x = 0` for `N_x ≤ 2` and `A = 0` for `N_μ = 1`. -/
theorem theorem_1 (hN : 3 ≤ N) (hK : 2 ≤ K) {Δx Δt : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt)
    (absA : Matrix (Fin K) (Fin K) ℝ) :
    ∃ B₀ : ZMod N → ℝ, (∀ j, 0 < B₀ j) ∧
      (∃ v₁ : Matrix (ZMod N) (Fin K) ℝ, IsAdvectionStep Δx Δt 0 (momentMatrix (legendreP K)) absA
        B₀ B₀ (constInSpace fun _ => 1) v₁) ∧
      (∀ (B₁ : ZMod N → ℝ) (v₁ : Matrix (ZMod N) (Fin K) ℝ),
        IsAdvectionStep Δx Δt 0 (momentMatrix (legendreP K)) absA B₀ B₁
          (constInSpace fun _ => 1) v₁ →
        B₁ = B₀ ∧
        diagonal B₁ * v₁ = ftcs Δx Δt (momentMatrix (legendreP K))
          (diagonal B₀ * constInSpace (N := N) (K := K) fun _ => 1) ∧
        energy B₀ (constInSpace (N := N) (K := K) fun _ => 1) < energy B₁ v₁) ∧
      ∃ (a : ℝ) (w : Fin K → ℝ), a ≠ 0 ∧ w ≠ 0 ∧ momentMatrix (legendreP K) *ᵥ w = a • w ∧
        (∃ m : ZMod N, 1 < ‖amplification Δx Δt a m‖) ∧
        ∀ ν : ℝ, 0 < ν → ¬ IsVonNeumannStable a ν := by
  set A := momentMatrix (legendreP K) with hAdef
  have hA : Aᵀ = A := momentMatrix_transpose _
  have hne : A *ᵥ (fun _ => 1) ≠ 0 := momentMatrix_legendreP_mulVec_one_ne_zero hK
  have hne0 : A ≠ 0 := fun h0 => hne (by rw [h0, Matrix.zero_mulVec])
  have hN2 : ((1 : ZMod N) + 1) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod N) = 0 := by
      have : ((2 : ℕ) : ZMod N) = 1 + 1 := by norm_num
      rw [this, h]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  set B₀ : ZMod N → ℝ := fun j => if j = 0 then 2 else 1 with hB
  have hB₀ (j : ZMod N) : 0 < B₀ j := by
    simp only [hB]
    split_ifs <;> norm_num
  have hD : (Dx Δx *ᵥ B₀) 1 ≠ 0 := by
    rw [Dx_mulVec]
    have : (2 * Δx) ≠ 0 := by positivity
    simp only [hB, sub_self, ite_true, hN2, ite_false]
    norm_num
    exact hΔx.ne'
  refine ⟨B₀, hB₀, exists_isAdvectionStep Δx Δt A absA B₀ _, fun B₁ v₁ h => ?_, ?_⟩
  · have hred := advection_reduces_to_ftcs (fun j => (hB₀ j).ne') _ h
    refine ⟨hred.1, hred.2, ?_⟩
    rw [advection_energy_eq hA (fun j => (hB₀ j).ne') _ h]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    have hnz : (Dx (N := N) Δx * (diagonal B₀ * constInSpace (N := N) (K := K) fun _ => 1) * Aᵀ :
        Matrix (ZMod N) (Fin K) ℝ) ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 1) k
      rw [transport_constInSpace_apply] at this
      exact (mul_ne_zero hD hk) this
    have : 0 < ‖(Dx (N := N) Δx * (diagonal B₀ * constInSpace (N := N) (K := K) fun _ => 1) * Aᵀ :
        Matrix (ZMod N) (Fin K) ℝ)‖ := norm_pos_iff.2 hnz
    have h2 : 0 < Δt ^ 2 / 2 * ‖(Dx (N := N) Δx * (diagonal B₀ * constInSpace (N := N) (K := K)
      fun _ => 1) * Aᵀ : Matrix (ZMod N) (Fin K) ℝ)‖ ^ 2 := by positivity
    linarith
  · obtain ⟨a, w, ha, hw, hAw⟩ := exists_eigenpair hA hne0
    exact ⟨a, w, ha, hw, hAw, exists_one_lt_norm_amplification hN hΔx hΔt ha,
      fun ν hν => not_isVonNeumannStable ha hν⟩

end Advection

/-! ### The augmented DLRA scheme (19) and Theorem 3 -/

section DLRA

variable {N : ℕ} [NeZero N] {K : ℕ} [NeZero K]

/-! `Q = qr(Y)` (`Q` has orthonormal columns and `Y = Q R`; the triangular shape of `R` plays no
role, and `Q` may have any number of columns, which covers rank-deficient `Y`) is the core capture
predicate `Matrix.IsOrthCapture Q Y` (`Qᵀ Q = 1`, `Q Qᵀ Y = Y`), equivalently
`Qᵀ Q = 1 ∧ ∃ R, Y = Q R` (`Matrix.isOrthCapture_iff`). The local `IsQR` of an earlier version
of this file was that conjunction (unification batch C4); it is not the core `Matrix.IsQR`, which
also asks for a square upper triangular `R`. -/

section QR

lemma IsQR.capture {m ι κ : Type*} [Fintype m] [Fintype ι] [DecidableEq ι] {Q : Matrix m ι ℝ}
    {Y : Matrix m κ ℝ} (h : IsOrthCapture Q Y) : Q * Qᵀ * Y = Y :=
  h.capture

lemma capture_fromCols {m κ κ' : Type*} [Fintype m] {P : Matrix m m ℝ} {Y : Matrix m κ ℝ}
    {Z : Matrix m κ' ℝ} (h : P * Matrix.fromCols Y Z = Matrix.fromCols Y Z) :
    P * Y = Y ∧ P * Z = Z := by
  rw [Matrix.mul_fromCols] at h
  exact Matrix.fromCols_inj h

lemma mul_transpose_transpose {m ι : Type*} [Fintype ι] (Q : Matrix m ι ℝ) :
    (Q * Qᵀ)ᵀ = Q * Qᵀ := by
  simp [Matrix.transpose_mul]

/-- A matrix captured by `Q` stays captured by a basis `Q'` capturing `Q`. -/
lemma capture_trans {m ι ι' κ : Type*} [Fintype m] [Fintype ι] [Fintype ι']
    {Q : Matrix m ι ℝ} {Q' : Matrix m ι' ℝ} {Y : Matrix m κ ℝ} (h : Q * Qᵀ * Y = Y)
    (h' : Q' * Q'ᵀ * Q = Q) : Q' * Q'ᵀ * Y = Y := by
  have : Y = Q * (Qᵀ * Y) := by rw [← Matrix.mul_assoc, h]
  rw [this, ← Matrix.mul_assoc, h']

/-- Every matrix has a `qr` in the sense of arXiv 2502.03008, Section 5.1. -/
theorem exists_isQR {m κ : Type*} [Fintype m] [Finite κ] (Y : Matrix m κ ℝ) :
    ∃ (n : ℕ) (Q : Matrix m (Fin n) ℝ), IsOrthCapture Q Y := by
  have := Fintype.ofFinite κ
  obtain ⟨U, hU, hc⟩ := LeanDLRA.exists_orthonormal_capture Y le_rfl
    (by simpa using Y.rank_le_card_height)
  exact ⟨Y.rank, U, hU, hc⟩

/-- The augmented bases represent `X⁰ S⁰ V⁰ᵀ` exactly. -/
lemma reconstruct_of_capture {m n c a b : Type*} [Fintype m] [Fintype n] [Fintype c] [Fintype a]
    [Fintype b] {Xs : Matrix m a ℝ} {Vs : Matrix n b ℝ} {X₀ : Matrix m c ℝ} (S₀ : Matrix c c ℝ)
    {V₀ : Matrix n c ℝ} (hX : Xs * Xsᵀ * X₀ = X₀) (hV : Vs * Vsᵀ * V₀ = V₀) :
    Xs * (Xsᵀ * X₀ * S₀ * (Vsᵀ * V₀)ᵀ) * Vsᵀ = X₀ * S₀ * V₀ᵀ := by
  have h : V₀ᵀ * (Vs * Vsᵀ) = V₀ᵀ := by
    conv_rhs => rw [← hV, Matrix.transpose_mul, mul_transpose_transpose]
  calc Xs * (Xsᵀ * X₀ * S₀ * (Vsᵀ * V₀)ᵀ) * Vsᵀ
      = (Xs * Xsᵀ * X₀) * S₀ * (V₀ᵀ * (Vs * Vsᵀ)) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = X₀ * S₀ * V₀ᵀ := by rw [hX, h]

/-- The projected transport term equals the full transport term, once the bases contain
`C X⁰` and `Z V⁰`. This is what the augmentations (19b), (19d) are for. -/
lemma transport_exact {m n c : Type*} [Fintype m] [Fintype n] [Fintype c] {PX C : Matrix m m ℝ}
    {PV Z : Matrix n n ℝ} {X₀ : Matrix m c ℝ} {S₀ : Matrix c c ℝ} {V₀ : Matrix n c ℝ}
    (hX : PX * (C * X₀) = C * X₀) (hV : V₀ᵀ * Zᵀ * PV = V₀ᵀ * Zᵀ) :
    PX * C * (X₀ * S₀ * V₀ᵀ) * Zᵀ * PV = C * (X₀ * S₀ * V₀ᵀ) * Zᵀ := by
  calc PX * C * (X₀ * S₀ * V₀ᵀ) * Zᵀ * PV
      = (PX * (C * X₀)) * S₀ * (V₀ᵀ * Zᵀ * PV) := by simp only [Matrix.mul_assoc]
    _ = C * (X₀ * S₀ * V₀ᵀ) * Zᵀ := by
        rw [hX, hV]
        simp only [Matrix.mul_assoc]

lemma right_capture {n c : Type*} [Fintype n] {P Z : Matrix n n ℝ}
    {V₀ : Matrix n c ℝ} (hP : Pᵀ = P) (hZ : Zᵀ = Z) (h : P * (Zᵀ * V₀) = Zᵀ * V₀) :
    V₀ᵀ * Zᵀ * P = V₀ᵀ * Zᵀ := by
  have := congrArg Matrix.transpose h
  simpa [Matrix.transpose_mul, hP, hZ, Matrix.mul_assoc] using this

lemma mulVec_of_mul_replicateCol {m : Type*} [Fintype m] {P : Matrix m m ℝ} {φ : m → ℝ}
    (h : P * Matrix.replicateCol Unit φ = Matrix.replicateCol Unit φ) : P *ᵥ φ = φ := by
  ext i
  simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun h i) ()

/-- The coefficient update (19j) recovers `K*,trans V̂̂*ᵀ (I - e₁e₁ᵀ) + v₀¹ e₁ᵀ`. -/
lemma vhat_eq_of_capture {m n a b t w : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    [Fintype t] [Fintype w] [DecidableEq n] {Xo : Matrix m a ℝ} {Vo : Matrix n b ℝ}
    {Xt : Matrix m t ℝ} (St : Matrix t w ℝ) {Vs : Matrix n w ℝ} {φ : m → ℝ} {e : n → ℝ}
    (hXt : Xo * Xoᵀ * Xt = Xt) (hφ : (Xo * Xoᵀ) *ᵥ φ = φ) (hVs : Vo * Voᵀ * Vs = Vs)
    (he : (Vo * Voᵀ) *ᵥ e = e) :
    Xo * (Xoᵀ * Xt * St * Vsᵀ * (1 - Matrix.vecMulVec e e) * Vo
        + Xoᵀ * Matrix.vecMulVec φ e * Vo) * Voᵀ =
      Xt * St * Vsᵀ * (1 - Matrix.vecMulVec e e) + Matrix.vecMulVec φ e := by
  set PV := Vo * Voᵀ with hPV
  set E := Matrix.vecMulVec e e with hE
  have hPVt : PVᵀ = PV := mul_transpose_transpose Vo
  have hPe : e ᵥ* PV = e := by
    conv_lhs => rw [← hPVt, Matrix.vecMul_transpose, he]
  have hVsP : Vsᵀ * PV = Vsᵀ := by
    conv_rhs => rw [← hVs, Matrix.transpose_mul, hPVt]
  have hEP : E * PV = E := by rw [hE, Matrix.vecMulVec_mul, hPe]
  have h1 : Vsᵀ * (1 - E) * PV = Vsᵀ * (1 - E) := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hEP, Matrix.mul_sub, Matrix.mul_sub, hVsP,
      Matrix.mul_one]
  have h2 : Matrix.vecMulVec φ e * PV = Matrix.vecMulVec φ e := by
    rw [Matrix.vecMulVec_mul, hPe]
  have h3 : Xo * Xoᵀ * Matrix.vecMulVec φ e = Matrix.vecMulVec φ e := by
    rw [Matrix.mul_vecMulVec, hφ]
  calc Xo * (Xoᵀ * Xt * St * Vsᵀ * (1 - E) * Vo + Xoᵀ * Matrix.vecMulVec φ e * Vo) * Voᵀ
      = (Xo * Xoᵀ * Xt) * St * (Vsᵀ * (1 - E) * PV) +
          (Xo * Xoᵀ * Matrix.vecMulVec φ e) * PV := by
        simp only [hPV, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = Xt * St * Vsᵀ * (1 - E) + Matrix.vecMulVec φ e := by
        rw [hXt, h1, h3, h2]
        simp only [Matrix.mul_assoc]

end QR

/-- The matrix of `w ↦ (1/B) ⊙ D (B ⊙ w)`. -/
noncomputable def weighted (B : ZMod N → ℝ) (D : Matrix (ZMod N) (ZMod N) ℝ) :
    Matrix (ZMod N) (ZMod N) ℝ :=
  diagonal (fun j => 1 / B j) * D * diagonal B

/-- The first unit vector `e₁` of the direction space. -/
noncomputable def e₁ : Fin K → ℝ := Pi.single 0 1

omit [NeZero K] in
lemma weighted_mul_mul_apply (B : ZMod N → ℝ) (D : Matrix (ZMod N) (ZMod N) ℝ)
    (v : Matrix (ZMod N) (Fin K) ℝ) (A : Matrix (Fin K) (Fin K) ℝ) (j : ZMod N) (k : Fin K) :
    (weighted B D * v * Aᵀ) j k = 1 / B j * (D * (diagonal B * v) * Aᵀ) j k := by
  have : weighted B D * v * Aᵀ = diagonal (fun j => 1 / B j) * (D * (diagonal B * v) * Aᵀ) := by
    simp only [weighted, Matrix.mul_assoc]
  rw [this, Matrix.diagonal_mul]

omit [NeZero K] in
lemma explicitPart_eq (Δx Δt : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (v₀ : Matrix (ZMod N) (Fin K) ℝ) :
    explicitPart Δx Δt A absA B₀ v₀ = v₀ - Δt • (weighted B₀ (Dx Δx) * v₀ * Aᵀ)
      + Δt • (weighted B₀ (Dxx Δx) * v₀ * absAᵀ) := by
  ext j k
  simp only [explicitPart, Matrix.of_apply, sum_weighted, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, weighted_mul_mul_apply]

variable {r ιXh ιVh ιXs ιVs ιXt ιXo ιVo : Type*}

/-- The intermediate quantities of one step of the DLRA scheme (19) of arXiv 2502.03008, in its
notation: `Kstar`, `Lstar` are `K*`, `L*` of (19a), (19c), `Xh`, `Vh` are `X̂*`, `V̂*`, `Xs`, `Vs`,
`Ss` are the doubly hatted `X*`, `V*`, `S*` (rank `4r`), `B₁` is `B¹`, `φ` is the zeroth moment
`v¹_0`, `Xt`, `St` are the doubly hatted `X*,trans`, `S*,trans`, and `Xo`, `So`, `Vo` are the
doubly hatted `X¹`, `S¹`, `V¹` (rank `4r + 1`). -/
structure Stage (N K : ℕ) (r ιXh ιVh ιXs ιVs ιXt ιXo ιVo : Type*) where
  /-- `K*`, spatial update. -/
  Kstar : Matrix (ZMod N) r ℝ
  /-- `L*`, directional update. -/
  Lstar : Matrix (Fin K) r ℝ
  /-- The spatial basis `X̂*` of rank `2r`. -/
  Xh : Matrix (ZMod N) ιXh ℝ
  /-- The directional basis `V̂*` of rank `2r`. -/
  Vh : Matrix (Fin K) ιVh ℝ
  /-- The augmented spatial basis of rank `4r`. -/
  Xs : Matrix (ZMod N) ιXs ℝ
  /-- The augmented directional basis of rank `4r`. -/
  Vs : Matrix (Fin K) ιVs ℝ
  /-- The coefficient matrix of the S-step. -/
  Ss : Matrix ιXs ιVs ℝ
  /-- The internal energy at `t₁`. -/
  B₁ : ZMod N → ℝ
  /-- The zeroth moment `v¹_{j0}` at `t₁`. -/
  φ : ZMod N → ℝ
  /-- The spatial factor of the transformed `K*,trans`. -/
  Xt : Matrix (ZMod N) ιXt ℝ
  /-- The coefficient factor of the transformed `K*,trans`. -/
  St : Matrix ιXt ιVs ℝ
  /-- The spatial basis of rank `4r + 1`. -/
  Xo : Matrix (ZMod N) ιXo ℝ
  /-- The directional basis of rank `4r + 1`. -/
  Vo : Matrix (Fin K) ιVo ℝ
  /-- The coefficient matrix before truncation. -/
  So : Matrix ιXo ιVo ℝ

/-- The result `v̂¹ = X̂̂¹ Ŝ̂¹ V̂̂¹ᵀ` of a step of (19) before truncation. -/
def Stage.vhat [Fintype ιXo] [Fintype ιVo] (d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo) :
    Matrix (ZMod N) (Fin K) ℝ :=
  d.Xo * d.So * d.Voᵀ

/-- `S̃⁰ = M̂̂ S⁰ N̂̂ᵀ` with `M̂̂ = X̂̂*ᵀ X⁰`, `N̂̂ = V̂̂*ᵀ V⁰`. -/
def Stage.Stilde [Fintype r] (d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ) : Matrix ιXs ιVs ℝ :=
  d.Xsᵀ * X₀ * S₀ * (d.Vsᵀ * V₀)ᵀ

variable [Fintype r] [Fintype ιXh] [Fintype ιVh] [Fintype ιXs] [Fintype ιVs] [Fintype ιXt]
  [Fintype ιXo] [Fintype ιVo] [DecidableEq ιXh] [DecidableEq ιVh] [DecidableEq ιXs]
  [DecidableEq ιVs] [DecidableEq ιXt] [DecidableEq ιXo] [DecidableEq ιVo]

/-- One step of the scheme (19) of arXiv 2502.03008 from `(X⁰, S⁰, V⁰, B⁰)`, from the basis
augmentations (19b), (19d) up to the coefficient matrix (19j), before truncation, for arbitrary
`K*`, `L*` (which enter through (19b), (19d) only). `qr` is `Matrix.IsOrthCapture`. -/
structure IsAugmentedUpdate (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ)
    (d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo) : Prop where
  /-- `X̂* = qr([K*, X⁰])`. -/
  qr_Xh : IsOrthCapture d.Xh (Matrix.fromCols d.Kstar X₀)
  /-- (19b). -/
  qr_Xs : IsOrthCapture d.Xs (Matrix.fromCols (Matrix.fromCols d.Xh (weighted B₀ (Dx Δx) * X₀))
    (weighted B₀ (Dxx Δx) * X₀))
  /-- `V̂* = qr([L*, V⁰])`. -/
  qr_Vh : IsOrthCapture d.Vh (Matrix.fromCols d.Lstar V₀)
  /-- (19d). -/
  qr_Vs : IsOrthCapture d.Vs (Matrix.fromCols (Matrix.fromCols d.Vh (Aᵀ * V₀)) (absAᵀ * V₀))
  /-- (19e). -/
  S_eq : d.Ss = (1 / (1 + σ * Δt)) • (d.Stilde X₀ S₀ V₀
    - Δt • (d.Xsᵀ * weighted B₀ (Dx Δx) * d.Xs * d.Stilde X₀ S₀ V₀ * (d.Vsᵀ * Aᵀ * d.Vs))
    + Δt • (d.Xsᵀ * weighted B₀ (Dxx Δx) * d.Xs * d.Stilde X₀ S₀ V₀ * (d.Vsᵀ * absAᵀ * d.Vs)))
  /-- (19f). -/
  moment_eq : ∀ j, d.B₁ j / B₀ j * d.φ j = 1 / (1 + σ * Δt) * (X₀ * S₀ * V₀ᵀ) j 0
    - Δt / (1 + σ * Δt) *
      (weighted B₀ (Dx Δx) * (d.Xs * d.Stilde X₀ S₀ V₀ * d.Vsᵀ) * Aᵀ) j 0
    + Δt / (1 + σ * Δt) *
      (weighted B₀ (Dxx Δx) * (d.Xs * d.Stilde X₀ S₀ V₀ * d.Vsᵀ) * absAᵀ) j 0
    + √2 * σ * Δt / (1 + σ * Δt) * (d.B₁ j / B₀ j)
  /-- (19g). -/
  B_eq : ∀ j, d.B₁ j / B₀ j = 1 + σ * Δt * (d.B₁ j / B₀ j) * (√2 * d.φ j - 2)
  /-- The QR decomposition after (19h): the basis is orthonormal... -/
  Xt_orth : d.Xtᵀ * d.Xt = 1
  /-- ... and factors `K*,trans_{jp} = (B⁰_j/B¹_j) K*_{jp}`, where `K* = X̂̂* Ŝ̂*`. -/
  trans_eq : d.Xt * d.St = diagonal (fun j => B₀ j / d.B₁ j) * (d.Xs * d.Ss)
  /-- (19i), space. -/
  qr_Xo : IsOrthCapture d.Xo (Matrix.fromCols (Matrix.replicateCol Unit d.φ) d.Xt)
  /-- (19i), direction. -/
  qr_Vo : IsOrthCapture d.Vo (Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) d.Vs)
  /-- (19j). -/
  So_eq : d.So = d.Xoᵀ * d.Xt * d.St * d.Vsᵀ *
      (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K))) * d.Vo
    + d.Xoᵀ * Matrix.vecMulVec d.φ (e₁ (K := K)) * d.Vo

omit [NeZero N] in
lemma mul_one_sub_e₁_apply (G : Matrix (ZMod N) (Fin K) ℝ) (j : ZMod N) (k : Fin K) :
    (G * (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K))) :
      Matrix (ZMod N) (Fin K) ℝ) j k = G j k * (1 - delta0 k) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.sub_apply,
    Matrix.vecMulVec_apply, e₁, Matrix.mulVec_single_one]
  by_cases hk : k = 0
  · subst hk
    simp [delta0]
  · simp [delta0, hk]

/-- **The DLRA update before truncation is the full update.** With the augmentations (19b), (19d)
and the moment and direction augmentations (19i), the matrix `v̂¹ = X̂̂¹ Ŝ̂¹ V̂̂¹ᵀ` together with
`B¹` solves the full scheme (11) from `(X⁰ S⁰ V⁰ᵀ, B⁰)` exactly. This is the core of the proof of
arXiv 2502.03008, Theorem 3, whose final identity is the equation (14) of the full scheme. -/
theorem IsAugmentedUpdate.isConservativeStep {Δx Δt σ : ℝ} {A absA : Matrix (Fin K) (Fin K) ℝ}
    {B₀ : ZMod N → ℝ} {X₀ : Matrix (ZMod N) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin K) r ℝ}
    {d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo} (hΔt : 0 < Δt) (hσ : 0 ≤ σ)
    (hB₀ : ∀ j, B₀ j ≠ 0) (hA : Aᵀ = A) (habs : absAᵀ = absA)
    (h : IsAugmentedUpdate Δx Δt σ A absA B₀ X₀ S₀ V₀ d) :
    IsConservativeStep Δx Δt σ A absA B₀ d.B₁ (X₀ * S₀ * V₀ᵀ) d.vhat := by
  have hs0 : 0 ≤ σ * Δt := mul_nonneg hσ hΔt.le
  have h1 : 1 + σ * Δt ≠ 0 := by positivity
  have hr (j : ZMod N) : d.B₁ j / B₀ j ≠ 0 := by
    intro h0
    have := h.B_eq j
    rw [h0] at this
    simp at this
  have hB₁ (j : ZMod N) : d.B₁ j ≠ 0 := fun h0 => hr j (by rw [h0, zero_div])
  obtain ⟨-, hcXh⟩ := capture_fromCols h.qr_Xh.capture
  obtain ⟨hcXs12, hcC2⟩ := capture_fromCols h.qr_Xs.capture
  obtain ⟨hcXsh, hcC1⟩ := capture_fromCols hcXs12
  obtain ⟨-, hcVh⟩ := capture_fromCols h.qr_Vh.capture
  obtain ⟨hcVs12, hcabs⟩ := capture_fromCols h.qr_Vs.capture
  obtain ⟨hcVsh, hcA⟩ := capture_fromCols hcVs12
  have hcX0 := capture_trans hcXh hcXsh
  have hcV0 := capture_trans hcVh hcVsh
  have hZ : d.Xs * d.Stilde X₀ S₀ V₀ * d.Vsᵀ = X₀ * S₀ * V₀ᵀ :=
    reconstruct_of_capture S₀ hcX0 hcV0
  have hPV : (d.Vs * d.Vsᵀ)ᵀ = d.Vs * d.Vsᵀ := mul_transpose_transpose d.Vs
  have hVA : V₀ᵀ * Aᵀ * (d.Vs * d.Vsᵀ) = V₀ᵀ * Aᵀ := right_capture hPV hA hcA
  have hVabs : V₀ᵀ * absAᵀ * (d.Vs * d.Vsᵀ) = V₀ᵀ * absAᵀ := right_capture hPV habs hcabs
  set C1 := weighted B₀ (Dx (N := N) Δx) with hC1
  set C2 := weighted B₀ (Dxx (N := N) Δx) with hC2
  set St0 := d.Stilde X₀ S₀ V₀ with hSt0
  set F := explicitPart Δx Δt A absA B₀ (X₀ * S₀ * V₀ᵀ) with hF
  have hG : d.Xs * d.Ss * d.Vsᵀ = (1 / (1 + σ * Δt)) • F := by
    have e1 : d.Xs * (d.Xsᵀ * C1 * d.Xs * St0 * (d.Vsᵀ * Aᵀ * d.Vs)) * d.Vsᵀ =
        d.Xs * d.Xsᵀ * C1 * (d.Xs * St0 * d.Vsᵀ) * Aᵀ * (d.Vs * d.Vsᵀ) := by
      simp only [Matrix.mul_assoc]
    have e2 : d.Xs * (d.Xsᵀ * C2 * d.Xs * St0 * (d.Vsᵀ * absAᵀ * d.Vs)) * d.Vsᵀ =
        d.Xs * d.Xsᵀ * C2 * (d.Xs * St0 * d.Vsᵀ) * absAᵀ * (d.Vs * d.Vsᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [h.S_eq, hF, explicitPart_eq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul]
    rw [e1, e2, hZ, transport_exact hcC1 hVA, transport_exact hcC2 hVabs]
  obtain ⟨hcXoφ, hcXoXt⟩ := capture_fromCols h.qr_Xo.capture
  obtain ⟨hcVoe, hcVoVs⟩ := capture_fromCols h.qr_Vo.capture
  have hvhat : d.vhat = d.Xt * d.St * d.Vsᵀ * (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K)))
      + Matrix.vecMulVec d.φ (e₁ (K := K)) := by
    rw [Stage.vhat, h.So_eq]
    exact vhat_eq_of_capture d.St hcXoXt (mulVec_of_mul_replicateCol hcXoφ) hcVoVs
      (mulVec_of_mul_replicateCol hcVoe)
  have hentry (j : ZMod N) (k : Fin K) : d.vhat j k =
      B₀ j / d.B₁ j * ((d.Xs * d.Ss * d.Vsᵀ) j k * (1 - delta0 k)) + d.φ j * delta0 k := by
    have e : d.Xt * d.St * d.Vsᵀ * (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K))) =
        diagonal (fun j => B₀ j / d.B₁ j) *
          (d.Xs * d.Ss * d.Vsᵀ * (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K)))) := by
      rw [h.trans_eq]
      simp only [Matrix.mul_assoc]
    have he (k : Fin K) : e₁ (K := K) k = delta0 k := by
      simp [e₁, delta0, Pi.single_apply]
    rw [hvhat, Matrix.add_apply, e, Matrix.diagonal_mul, mul_one_sub_e₁_apply,
      Matrix.vecMulVec_apply, he]
  have hδ0 : delta0 (0 : Fin K) = 1 := by simp [delta0]
  have hG' (j : ZMod N) (k : Fin K) : (d.Xs * d.Ss * d.Vsᵀ) j k = 1 / (1 + σ * Δt) * F j k := by
    rw [hG, Matrix.smul_apply, smul_eq_mul]
  have hm (j : ZMod N) : (1 + σ * Δt) * (d.B₁ j / B₀ j * d.φ j) =
      F j 0 + √2 * (σ * Δt) * (d.B₁ j / B₀ j) := by
    rw [h.moment_eq j, hZ, hF, explicitPart_eq]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  refine isConservativeStep_of_reduced hΔt.ne' hB₀ (fun j k => ?_) (fun j => ?_)
  · rw [hentry]
    have hb := hB₀ j
    have hb1 := hB₁ j
    by_cases hk : k = 0
    · subst hk
      rw [hδ0]
      have := hm j
      simp only [sub_self, mul_zero, zero_add, mul_one]
      linarith
    · have hδ : delta0 k = 0 := by simp [delta0, hk]
      rw [hδ, hG']
      simp only [sub_zero, mul_one, mul_zero, add_zero]
      field_simp
      rfl
  · rw [hentry, hδ0]
    simp only [sub_self, mul_zero, zero_add, mul_one]
    exact h.B_eq j

/-- A truncation of the form `v¹ = v̂¹ Π` with an orthogonal projector `Π` of the direction space.
Both the truncated SVD of Section 5.1 of arXiv 2502.03008 and the conservative truncation of its
Section 5.4 are of this form: `IsSVDTruncation.isRightProjection`,
`IsConservativeTruncation.isRightProjection`. -/
def IsRightProjection (vh v₁ : Matrix (ZMod N) (Fin K) ℝ) : Prop :=
  ∃ Pr : Matrix (Fin K) (Fin K) ℝ, Prᵀ = Pr ∧ Pr * Pr = Pr ∧ v₁ = vh * Pr

omit [NeZero K] in
/-- **Truncation does not increase the energy** (the step of arXiv 2502.03008, Theorem 3, that the
paper does not spell out). The truncation is optimal in the unweighted norm of `v`, the energy
involves `B¹ v`, but both are compatible because a row scaling commutes with a projection from the
right. -/
theorem energy_le_of_isRightProjection (B : ZMod N → ℝ) {vh v₁ : Matrix (ZMod N) (Fin K) ℝ}
    (h : IsRightProjection vh v₁) : energy B v₁ ≤ energy B vh := by
  obtain ⟨Pr, hs, hp, rfl⟩ := h
  rw [energy_eq, energy_eq, ← Matrix.mul_assoc]
  set u := diagonal B * vh with hu
  have h1 : ⟪u * Pr, u * Pr⟫ = ⟪u, u * Pr⟫ := by
    rw [LeanDLRA.Frobenius.inner_mul_right, Matrix.mul_assoc, hs, hp]
  have h2 : ‖u - u * Pr‖ ^ 2 = ‖u‖ ^ 2 - ‖u * Pr‖ ^ 2 := by
    rw [norm_sub_sq_real, ← h1, real_inner_self_eq_norm_sq]
    ring
  have h3 : 0 ≤ ‖u - u * Pr‖ ^ 2 := by positivity
  linarith

/-- arXiv 2502.03008, Theorem 3, for every update of the form (19b)-(19j), with arbitrary `K*`,
`L*`. -/
theorem energy_le_of_isAugmentedUpdate {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt)
    (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ) {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P)
    {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, 0 < B₀ j)
    {X₀ : Matrix (ZMod N) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin K) r ℝ}
    {d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo}
    (h : IsAugmentedUpdate Δx Δt σ (momentMatrix P) (absMat Q M) B₀ X₀ S₀ V₀ d)
    {v₁ : Matrix (ZMod N) (Fin K) ℝ} (hT : IsRightProjection d.vhat v₁) :
    energy d.B₁ v₁ ≤ energy B₀ (X₀ * S₀ * V₀ᵀ) :=
  (energy_le_of_isRightProjection d.B₁ hT).trans <| theorem_2 hΔx hΔt hCFL hσ hP hd hB₀ <|
    h.isConservativeStep hΔt hσ (fun j => (hB₀ j).ne') hd.transpose_eq (absMat_transpose Q M)

omit [NeZero N] in
/-- `qr([e₁, Vs])` of arXiv 2502.03008, (19i), can be taken with first column `e₁`, as the
conservative truncation of its Section 5.4 assumes. -/
theorem exists_isQR_e₁ {w : Type*} [Fintype w] (Vs : Matrix (Fin K) w ℝ) :
    ∃ (n : ℕ) (Vrem : Matrix (Fin K) (Fin n) ℝ),
      IsOrthCapture (Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem)
        (Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vs) := by
  set U₀ := Matrix.replicateCol Unit (e₁ (K := K)) with hU₀
  have hU₀U₀ : U₀ᵀ * U₀ = 1 := by
    ext x y
    simp [hU₀, Matrix.mul_apply, e₁, Pi.single_apply]
  have hrank : (((1 : Matrix (Fin K) (Fin K) ℝ) - U₀ * U₀ᵀ) * Vs).rank + 1 ≤ K := by
    have h1 : (1 : Matrix (Fin K) (Fin K) ℝ) - U₀ * U₀ᵀ =
        diagonal fun k => if k = 0 then 0 else 1 := by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        by_cases hx : x = 0 <;> simp [hU₀, Matrix.mul_apply, e₁, hx]
      · simp only [Matrix.sub_apply, Matrix.one_apply_ne hxy, Matrix.diagonal_apply_ne _ hxy]
        have : (U₀ * U₀ᵀ) x y = e₁ (K := K) x * e₁ (K := K) y := by
          simp [hU₀, Matrix.mul_apply]
        rw [this]
        by_cases hx : x = 0
        · have hy : y ≠ 0 := fun hy => hxy (hx.trans hy.symm)
          simp [e₁, Pi.single_apply, hy]
        · simp [e₁, Pi.single_apply, hx]
    have h2 : (diagonal fun k : Fin K => if k = 0 then (0 : ℝ) else 1).rank = K - 1 := by
      rw [Matrix.rank_diagonal]
      have : Fintype.card {i : Fin K // (if i = 0 then (0 : ℝ) else 1) ≠ 0} =
          Fintype.card {i : Fin K // i ≠ 0} := by
        refine Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)
        by_cases h : i = 0 <;> simp [h]
      rw [this, Fintype.card_subtype_compl]
      simp
    have h3 := Matrix.rank_mul_le_left ((1 : Matrix (Fin K) (Fin K) ℝ) - U₀ * U₀ᵀ) Vs
    rw [h1, h2] at h3
    rw [h1]
    have := NeZero.pos K
    omega
  obtain ⟨U, hU, hUU₀, hcap⟩ := LeanDLRA.exists_orthonormal_capture_compl U₀ hU₀U₀ Vs le_rfl
    (by simpa [add_comm] using hrank)
  refine ⟨_, U, Matrix.isOrthCapture_iff.2 ⟨?_, ?_⟩⟩
  · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hU₀U₀, hU, hUU₀]
    have h0 : U₀ᵀ * U = 0 := by
      have := congrArg Matrix.transpose hUU₀
      simpa [Matrix.transpose_mul] using this
    rw [h0, Matrix.fromBlocks_one]
  · set Q := Matrix.fromCols U₀ U with hQ
    refine ⟨Qᵀ * Matrix.fromCols U₀ Vs, ?_⟩
    have hQQ : Q * Qᵀ = U₀ * U₀ᵀ + U * Uᵀ := by
      rw [hQ, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
    rw [← Matrix.mul_assoc, hQQ, Matrix.mul_fromCols]
    have h0 : Uᵀ * U₀ = 0 := hUU₀
    congr 1
    · rw [Matrix.add_mul, Matrix.mul_assoc U₀, hU₀U₀, Matrix.mul_one, Matrix.mul_assoc U, h0,
        Matrix.mul_zero, add_zero]
    · have e : Vs = U₀ * U₀ᵀ * Vs + (1 - U₀ * U₀ᵀ) * Vs := by
        rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
      have hPP : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
        calc U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * (U₀ᵀ * U₀) * U₀ᵀ := by simp only [Matrix.mul_assoc]
          _ = U₀ * U₀ᵀ := by rw [hU₀U₀, Matrix.mul_one]
      have h2 : U * Uᵀ * (U₀ * U₀ᵀ * Vs) = 0 := by
        calc U * Uᵀ * (U₀ * U₀ᵀ * Vs) = U * (Uᵀ * U₀) * (U₀ᵀ * Vs) := by
              simp only [Matrix.mul_assoc]
          _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
      have h3 : U₀ * U₀ᵀ * ((1 - U₀ * U₀ᵀ) * Vs) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, Matrix.zero_mul]
      have h4 : U₀ * U₀ᵀ * (U₀ * U₀ᵀ * Vs) = U₀ * U₀ᵀ * Vs := by
        rw [← Matrix.mul_assoc, hPP]
      calc Vs = U₀ * U₀ᵀ * Vs + (1 - U₀ * U₀ᵀ) * Vs := e
        _ = (U₀ * U₀ᵀ + U * Uᵀ) * (U₀ * U₀ᵀ * Vs + (1 - U₀ * U₀ᵀ) * Vs) := by
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h2, h3, h4, hcap, add_zero,
              zero_add]
        _ = (U₀ * U₀ᵀ + U * Uᵀ) * Vs := congrArg _ e.symm

/-- The K-step (19a) of arXiv 2502.03008 in matrix form, with `K⁰ = X⁰ S⁰`. -/
noncomputable def kStep (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ) :
    Matrix (ZMod N) r ℝ :=
  (1 / (1 + σ * Δt)) • (X₀ * S₀ - Δt • (weighted B₀ (Dx Δx) * (X₀ * S₀) * (V₀ᵀ * Aᵀ * V₀))
    + Δt • (weighted B₀ (Dxx Δx) * (X₀ * S₀) * (V₀ᵀ * absAᵀ * V₀)))

/-- The L-step (19c) of arXiv 2502.03008 in matrix form, with `L⁰ = V⁰ S⁰ᵀ`, as printed there, with
`D^x_{ij}` in place of the `D^x_{ji}` that the Galerkin condition would give. This makes no
difference to the theorems below, which hold for arbitrary `L*`. -/
noncomputable def lStep (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ) :
    Matrix (Fin K) r ℝ :=
  (1 / (1 + σ * Δt)) • (V₀ * S₀ᵀ
    - Δt • (Aᵀ * (V₀ * S₀ᵀ) *
      (X₀ᵀ * diagonal B₀ * Dx (N := N) Δx * diagonal (fun j => 1 / B₀ j) * X₀))
    + Δt • (absAᵀ * (V₀ * S₀ᵀ) *
      (X₀ᵀ * diagonal B₀ * Dxx (N := N) Δx * diagonal (fun j => 1 / B₀ j) * X₀)))

/-- One step of the DLRA scheme (19) of arXiv 2502.03008, before truncation: the K- and L-steps
(19a), (19c) together with `IsAugmentedUpdate`. -/
structure IsDLRAStep (Δx Δt σ : ℝ) (A absA : Matrix (Fin K) (Fin K) ℝ) (B₀ : ZMod N → ℝ)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ)
    (d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo) : Prop
    extends IsAugmentedUpdate Δx Δt σ A absA B₀ X₀ S₀ V₀ d where
  /-- (19a). -/
  K_eq : d.Kstar = kStep Δx Δt σ A absA B₀ X₀ S₀ V₀
  /-- (19c). -/
  L_eq : d.Lstar = lStep Δx Δt σ A absA B₀ X₀ S₀ V₀

/-- **Theorem 3 (energy stability of the DLRA scheme)** (arXiv 2502.03008, Theorem 3): under
`Δt ≤ Δx`, one step of the scheme (19), from `v⁰ = X⁰ S⁰ V⁰ᵀ` to `v¹` followed by any truncation of
the form `v¹ = v̂¹ Π` with an orthogonal projector `Π`, satisfies `E¹ ≤ E⁰`. The two truncations of
the paper are of this form, see `theorem_3_svd` and `theorem_3_conservative`.

Here `A` is the moment matrix of an `L²(-1, 1)`-orthonormal family, in particular of the normalized
Legendre polynomials (`isL2Orthonormal_legendreP`), `|A| = Q |M| Qᵀ` for any diagonalization, and
`qr` is `Matrix.IsOrthCapture`, so that bases may have any number of columns and rank deficiency
is allowed.
Differences from the paper: `Δx > 0` is arbitrary; `σ ≥ 0`, `Δt > 0`, `B⁰ > 0` are stated; the
orthonormality of `X⁰` and `V⁰` is not needed. `B¹ ≠ 0`, needed in (19h), is derived from (19g).
The paper closes the proof by noting that truncation leaves the zeroth moment unchanged, the design
property of the conservative truncation of its Section 5.4. This proof does not use it: it uses
that the truncation is a projection from the right, `energy_le_of_isRightProjection`, which also
covers the truncated SVD. See `exists_isDLRAStep` for non-vacuity. -/
theorem theorem_3 {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt) (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ)
    {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P) {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, 0 < B₀ j)
    {X₀ : Matrix (ZMod N) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin K) r ℝ}
    {d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo}
    (h : IsDLRAStep Δx Δt σ (momentMatrix P) (absMat Q M) B₀ X₀ S₀ V₀ d)
    {v₁ : Matrix (ZMod N) (Fin K) ℝ} (hT : IsRightProjection d.vhat v₁) :
    energy d.B₁ v₁ ≤ energy B₀ (X₀ * S₀ * V₀ᵀ) :=
  energy_le_of_isAugmentedUpdate hΔx hΔt hCFL hσ hP hd hB₀ h.toIsAugmentedUpdate hT

section Truncation

lemma submatrix_transpose_mul {b ρ : Type*} [Fintype b] [DecidableEq ρ] {n : ℕ}
    {Q : Matrix b (Fin n) ℝ} (hQ : Qᵀ * Q = 1) (f : ρ ↪ Fin n) :
    (Q.submatrix id f)ᵀ * Q.submatrix id f = 1 := by
  ext x y
  have := congrFun (congrFun hQ (f x)) (f y)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id] at this ⊢
  rw [this, Matrix.one_apply, Matrix.one_apply]
  simp [f.injective.eq_iff]

/-- The truncated SVD of `S = P diag(s) Qᵀ` satisfies `S Q_f = P_f diag(s_f)`. -/
lemma truncated_svd_eq {a b ρ : Type*} [Fintype b] [DecidableEq ρ] [Fintype ρ] {n : ℕ}
    {S : Matrix a b ℝ} {P : Matrix a (Fin n) ℝ} {Q : Matrix b (Fin n) ℝ}
    {s : Fin n → ℝ} (f : ρ ↪ Fin n) (hQ : Qᵀ * Q = 1) (hS : S = P * diagonal s * Qᵀ) :
    P.submatrix id f * diagonal (s ∘ f) = S * Q.submatrix id f := by
  have h1 : Qᵀ * Q.submatrix id f = (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id f := by
    rw [← hQ]
    ext x y
    simp [Matrix.mul_apply]
  rw [hS, Matrix.mul_assoc, h1]
  ext x y
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply]

/-- The rank-truncation step of the (augmented) BUG integrator of arXiv 2502.03008, Section 5.1:
take an SVD `Ŝ̂¹ = P̂ Σ Q̂ᵀ`, keep some of the singular triples (those selected by the embedding
`f`; the paper keeps the `r₁` largest, with `r₁` chosen by the tolerance `ϑ`), and set
`X¹ = X̂̂¹ P¹`, `V¹ = V̂̂¹ Q¹`, `S¹ = Σ_{r₁}`. -/
def IsSVDTruncation {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (Xo : Matrix (ZMod N) ιXo ℝ)
    (So : Matrix ιXo ιVo ℝ) (Vo : Matrix (Fin K) ιVo ℝ) (X₁ : Matrix (ZMod N) ρ ℝ)
    (S₁ : Matrix ρ ρ ℝ) (V₁ : Matrix (Fin K) ρ ℝ) : Prop :=
  ∃ (n : ℕ) (P : Matrix ιXo (Fin n) ℝ) (Q : Matrix ιVo (Fin n) ℝ) (s : Fin n → ℝ) (f : ρ ↪ Fin n),
    Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ So = P * diagonal s * Qᵀ ∧
      X₁ = Xo * P.submatrix id f ∧ V₁ = Vo * Q.submatrix id f ∧ S₁ = diagonal (s ∘ f)

/-- The truncated SVD of arXiv 2502.03008, Section 5.1, is a projection from the right. -/
theorem IsSVDTruncation.isRightProjection {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    {Xo : Matrix (ZMod N) ιXo ℝ} {So : Matrix ιXo ιVo ℝ} {Vo : Matrix (Fin K) ιVo ℝ}
    {X₁ : Matrix (ZMod N) ρ ℝ} {S₁ : Matrix ρ ρ ℝ} {V₁ : Matrix (Fin K) ρ ℝ}
    (hVo : Voᵀ * Vo = 1) (h : IsSVDTruncation Xo So Vo X₁ S₁ V₁) :
    IsRightProjection (Xo * So * Voᵀ) (X₁ * S₁ * V₁ᵀ) := by
  obtain ⟨n, P, Q, s, f, -, hQ, hS, rfl, rfl, rfl⟩ := h
  set Qf := Q.submatrix id f with hQf
  have hQQ : Qfᵀ * Qf = 1 := submatrix_transpose_mul hQ f
  have hSQ : P.submatrix id f * diagonal (s ∘ f) = So * Qf := truncated_svd_eq f hQ hS
  refine ⟨Vo * Qf * Qfᵀ * Voᵀ, ?_, ?_, ?_⟩
  · simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · calc Vo * Qf * Qfᵀ * Voᵀ * (Vo * Qf * Qfᵀ * Voᵀ)
        = Vo * Qf * (Qfᵀ * (Voᵀ * Vo) * Qf) * Qfᵀ * Voᵀ := by simp only [Matrix.mul_assoc]
      _ = Vo * Qf * Qfᵀ * Voᵀ := by rw [hVo, Matrix.mul_one, hQQ, Matrix.mul_one]
  · calc Xo * P.submatrix id f * diagonal (s ∘ f) * (Vo * Qf)ᵀ
        = Xo * (P.submatrix id f * diagonal (s ∘ f)) * Qfᵀ * Voᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Xo * So * (Voᵀ * Vo) * Qf * Qfᵀ * Voᵀ := by
          rw [hSQ, hVo]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Xo * So * Voᵀ * (Vo * Qf * Qfᵀ * Voᵀ) := by simp only [Matrix.mul_assoc]

/-- **arXiv 2502.03008, Theorem 3, with the truncation of its Section 5.1**: `E¹ ≤ E⁰` holds for
the truncated SVD. The proof uses no property of the zeroth moment, only that the truncation is a
projection from the right. -/
theorem theorem_3_svd {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt) (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ)
    {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P) {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, 0 < B₀ j)
    {X₀ : Matrix (ZMod N) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin K) r ℝ}
    {d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo ιVo}
    (h : IsDLRAStep Δx Δt σ (momentMatrix P) (absMat Q M) B₀ X₀ S₀ V₀ d)
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {X₁ : Matrix (ZMod N) ρ ℝ} {S₁ : Matrix ρ ρ ℝ}
    {V₁ : Matrix (Fin K) ρ ℝ} (hT : IsSVDTruncation d.Xo d.So d.Vo X₁ S₁ V₁) :
    energy d.B₁ (X₁ * S₁ * V₁ᵀ) ≤ energy B₀ (X₀ * S₀ * V₀ᵀ) :=
  theorem_3 hΔx hΔt hCFL hσ hP hd hB₀ h (hT.isRightProjection h.qr_Vo.1)

/-- The conservative truncation of arXiv 2502.03008, Section 5.4, steps 1 to 6. The directional
basis is `V̂̂¹ = [e₁, Vrem]`, the coefficient matrix `So` has columns indexed by `Unit ⊕ ιq`:

1. `K̂̂¹ = X̂̂¹ Ŝ̂¹` is split into its first column `K^cons` and the rest `K^rem`;
2. `X^cons = K^cons/‖K^cons‖`, `S^cons = ‖K^cons‖`;
3. `K^rem = Xrem Srem`, a QR decomposition;
4. `Srem = P diag(s) Qᵀ`, an SVD, of which the triples selected by `f` are kept, giving
   `X^{1,rem} = Xrem P_f` and `V^{1,rem} = Vrem Q_f`;
5. `[X^cons, X^{1,rem}] = X¹ R¹` and `[e₁, V^{1,rem}] = V¹ R²`, QR decompositions;
6. `S¹ = R¹ diag(S^cons, s_f) R²ᵀ`. -/
def IsConservativeTruncation {ιq ρ₁ ρ₂ : Type*} [Fintype ιq] [Fintype ρ₁] [DecidableEq ρ₁]
    [Fintype ρ₂] [DecidableEq ρ₂]
    (Xo : Matrix (ZMod N) ιXo ℝ) (So : Matrix ιXo (Unit ⊕ ιq) ℝ) (Vrem : Matrix (Fin K) ιq ℝ)
    (X₁ : Matrix (ZMod N) ρ₁ ℝ) (S₁ : Matrix ρ₁ ρ₂ ℝ) (V₁ : Matrix (Fin K) ρ₂ ℝ) : Prop :=
  ∃ (l n t : ℕ) (Xrem : Matrix (ZMod N) (Fin l) ℝ) (Srem : Matrix (Fin l) ιq ℝ)
    (P : Matrix (Fin l) (Fin n) ℝ) (Q : Matrix ιq (Fin n) ℝ) (s : Fin n → ℝ)
    (f : Fin t ↪ Fin n) (R₁ : Matrix ρ₁ (Unit ⊕ Fin t) ℝ) (R₂ : Matrix ρ₂ (Unit ⊕ Fin t) ℝ),
    Xremᵀ * Xrem = 1 ∧ (Xo * So).submatrix id Sum.inr = Xrem * Srem ∧
    Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ Srem = P * diagonal s * Qᵀ ∧
    X₁ᵀ * X₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧
    Matrix.fromCols (Matrix.replicateCol Unit fun j =>
        (Xo * So) j (Sum.inl ()) / √(∑ i, (Xo * So) i (Sum.inl ()) ^ 2))
      (Xrem * P.submatrix id f) = X₁ * R₁ ∧
    Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) (Vrem * Q.submatrix id f) = V₁ * R₂ ∧
    S₁ = R₁ * (diagonal (Sum.elim (fun _ => √(∑ i, (Xo * So) i (Sum.inl ()) ^ 2)) (s ∘ f)) :
      Matrix (Unit ⊕ Fin t) (Unit ⊕ Fin t) ℝ) * R₂ᵀ

omit [NeZero K] in
lemma mul_fromCols_transpose {m q : Type*} [Fintype q] (G : Matrix m (Unit ⊕ q) ℝ)
    (e : Fin K → ℝ) (W : Matrix (Fin K) q ℝ) :
    G * (Matrix.fromCols (Matrix.replicateCol Unit e) W)ᵀ =
      Matrix.vecMulVec (fun j => G j (Sum.inl ())) e + G.submatrix id Sum.inr * Wᵀ := by
  ext i k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.vecMulVec_apply]

omit [NeZero K] in
lemma fromCols_diagonal_fromCols {m ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (x : m → ℝ) (Y : Matrix m ρ ℝ) (c : ℝ) (t : ρ → ℝ) (e : Fin K → ℝ) (W : Matrix (Fin K) ρ ℝ) :
    Matrix.fromCols (Matrix.replicateCol Unit x) Y *
        (diagonal (Sum.elim (fun _ => c) t) : Matrix (Unit ⊕ ρ) (Unit ⊕ ρ) ℝ) *
        (Matrix.fromCols (Matrix.replicateCol Unit e) W)ᵀ =
      Matrix.vecMulVec (fun j => x j * c) e + Y * diagonal t * Wᵀ := by
  ext i k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.vecMulVec_apply, Matrix.diagonal_apply]

/-- The conservative truncation of arXiv 2502.03008, Section 5.4, is a projection from the right:
`Π = e₁ e₁ᵀ + W Wᵀ` with `W = Vrem Q_f`. -/
theorem IsConservativeTruncation.isRightProjection {ιq ρ₁ ρ₂ : Type*} [Fintype ιq]
    [Fintype ρ₁] [DecidableEq ρ₁] [Fintype ρ₂] [DecidableEq ρ₂] [DecidableEq ιq]
    {Xo : Matrix (ZMod N) ιXo ℝ} {So : Matrix ιXo (Unit ⊕ ιq) ℝ} {Vrem : Matrix (Fin K) ιq ℝ}
    {X₁ : Matrix (ZMod N) ρ₁ ℝ} {S₁ : Matrix ρ₁ ρ₂ ℝ} {V₁ : Matrix (Fin K) ρ₂ ℝ}
    (hV : (Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem)ᵀ *
      Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem = 1)
    (h : IsConservativeTruncation Xo So Vrem X₁ S₁ V₁) :
    IsRightProjection
      (Xo * So * (Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem)ᵀ)
      (X₁ * S₁ * V₁ᵀ) := by
  obtain ⟨l, n, t, Xrem, Srem, P, Q, s, f, R₁, R₂, -, hK, -, hQ, hS, -, -, hX, hV', rfl⟩ := h
  set G := Xo * So with hG
  set Kc : ZMod N → ℝ := fun j => G j (Sum.inl ()) with hKc
  set c := √(∑ i, G i (Sum.inl ()) ^ 2) with hc
  set Krem := G.submatrix id Sum.inr with hKrem
  set Qf := Q.submatrix id f with hQf
  set e := e₁ (K := K) with he
  set W := Vrem * Qf with hW
  have hQQ : Qfᵀ * Qf = 1 := submatrix_transpose_mul hQ f
  have hSQ : P.submatrix id f * diagonal (s ∘ f) = Srem * Qf := truncated_svd_eq f hQ hS
  have hee : e ⬝ᵥ e = 1 := by simp [he, e₁]
  have hVV : Vremᵀ * Vrem = 1 := by
    ext x y
    have := congrFun (congrFun hV (Sum.inr x)) (Sum.inr y)
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hVe : Vremᵀ *ᵥ e = 0 := by
    ext x
    have := congrFun (congrFun hV (Sum.inr x)) (Sum.inl ())
    simpa [Matrix.mul_apply, mulVec, dotProduct] using this
  have hWW : Wᵀ * W = 1 := by
    calc Wᵀ * W = Qfᵀ * (Vremᵀ * Vrem) * Qf := by
          simp only [hW, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hVV, Matrix.mul_one, hQQ]
  have hWe : Wᵀ *ᵥ e = 0 := by
    rw [hW, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hVe, Matrix.mulVec_zero]
  have heW : e ᵥ* W = 0 := by
    rw [← Matrix.mulVec_transpose, hWe]
  have hKcc : (fun j => Kc j / c * c) = Kc := by
    ext j
    by_cases h0 : c = 0
    · have hs : ∑ i, G i (Sum.inl ()) ^ 2 = 0 :=
        (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg (G i (Sum.inl ())))).1 h0
      have : Kc j ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 hs j (Finset.mem_univ j)
      have : Kc j = 0 := by simpa using this
      simp [this]
    · field_simp
  have hE : Matrix.vecMulVec e e * Matrix.vecMulVec e e = Matrix.vecMulVec e e := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
  have hEW : Matrix.vecMulVec e e * (W * Wᵀ) = 0 := by
    rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, heW]
    simp
  have hWE : W * Wᵀ * Matrix.vecMulVec e e = 0 := by
    rw [Matrix.mul_vecMulVec, ← Matrix.mulVec_mulVec, hWe]
    simp
  have hWWW : W * Wᵀ * (W * Wᵀ) = W * Wᵀ := by
    calc W * Wᵀ * (W * Wᵀ) = W * (Wᵀ * W) * Wᵀ := by simp only [Matrix.mul_assoc]
      _ = W * Wᵀ := by rw [hWW, Matrix.mul_one]
  refine ⟨Matrix.vecMulVec e e + W * Wᵀ, ?_, ?_, ?_⟩
  · simp [Matrix.transpose_add, Matrix.transpose_mul]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hE, hEW, hWE, hWWW, add_zero, zero_add]
  · have h1 : X₁ * (R₁ * (diagonal (Sum.elim (fun _ => c) (s ∘ f)) :
        Matrix (Unit ⊕ Fin t) (Unit ⊕ Fin t) ℝ) * R₂ᵀ) * V₁ᵀ =
        (X₁ * R₁) * (diagonal (Sum.elim (fun _ => c) (s ∘ f)) :
          Matrix (Unit ⊕ Fin t) (Unit ⊕ Fin t) ℝ) * (V₁ * R₂)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hGV : G * (Matrix.fromCols (Matrix.replicateCol Unit e) Vrem)ᵀ =
        Matrix.vecMulVec Kc e + Krem * Vremᵀ := mul_fromCols_transpose G e Vrem
    have h2 : Xrem * P.submatrix id f * diagonal (s ∘ f) * Wᵀ = Krem * Qf * Wᵀ := by
      rw [Matrix.mul_assoc Xrem, hSQ, ← Matrix.mul_assoc Xrem, ← hK]
    have a1 : Matrix.vecMulVec Kc e * Matrix.vecMulVec e e = Matrix.vecMulVec Kc e := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
    have a2 : Matrix.vecMulVec Kc e * (W * Wᵀ) = 0 := by
      rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_vecMul, heW]
      ext i k
      simp [Matrix.vecMulVec_apply]
    have a3 : Krem * Vremᵀ * Matrix.vecMulVec e e = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_vecMulVec, hVe]
      simp
    have a4 : Krem * Vremᵀ * (W * Wᵀ) = Krem * Qf * Wᵀ := by
      have hWW' : W * Wᵀ = Vrem * (Qf * Wᵀ) := by
        rw [← Matrix.mul_assoc]
      calc Krem * Vremᵀ * (W * Wᵀ) = Krem * (Vremᵀ * Vrem) * (Qf * Wᵀ) := by
            rw [hWW']
            simp only [Matrix.mul_assoc]
        _ = Krem * Qf * Wᵀ := by rw [hVV, Matrix.mul_one, Matrix.mul_assoc]
    rw [h1, ← hX, ← hV', fromCols_diagonal_fromCols, hKcc, hGV, h2, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, a1, a2, a3, a4, add_zero, zero_add]

/-- **arXiv 2502.03008, Theorem 3, with the conservative truncation of its Section 5.4**. Here the
directional basis `V̂̂¹ = qr([e₁, V̂̂*])` has first column `e₁`, as this truncation requires. -/
theorem theorem_3_conservative {ιq ρ₁ ρ₂ : Type*} [Fintype ιq] [DecidableEq ιq] [Fintype ρ₁]
    [DecidableEq ρ₁] [Fintype ρ₂] [DecidableEq ρ₂] {Δx Δt σ : ℝ} (hΔx : 0 < Δx) (hΔt : 0 < Δt)
    (hCFL : Δt ≤ Δx) (hσ : 0 ≤ σ) {P : Fin K → ℝ → ℝ} (hP : IsL2Orthonormal P)
    {Q : Matrix (Fin K) (Fin K) ℝ} {M : Fin K → ℝ}
    (hd : IsDiagonalization (momentMatrix P) Q M) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, 0 < B₀ j)
    {X₀ : Matrix (ZMod N) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin K) r ℝ}
    {d : Stage N K r ιXh ιVh ιXs ιVs ιXt ιXo (Unit ⊕ ιq)}
    (h : IsDLRAStep Δx Δt σ (momentMatrix P) (absMat Q M) B₀ X₀ S₀ V₀ d)
    {Vrem : Matrix (Fin K) ιq ℝ}
    (hVo : d.Vo = Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem)
    {X₁ : Matrix (ZMod N) ρ₁ ℝ} {S₁ : Matrix ρ₁ ρ₂ ℝ} {V₁ : Matrix (Fin K) ρ₂ ℝ}
    (hT : IsConservativeTruncation d.Xo d.So Vrem X₁ S₁ V₁) :
    energy d.B₁ (X₁ * S₁ * V₁ᵀ) ≤ energy B₀ (X₀ * S₀ * V₀ᵀ) := by
  refine theorem_3 hΔx hΔt hCFL hσ hP hd hB₀ h ?_
  have hV := h.qr_Vo.1
  rw [hVo] at hV
  have := hT.isRightProjection hV
  rwa [← hVo] at this

/-- **Non-vacuity of arXiv 2502.03008, Theorem 3**: from every low-rank state a step of the scheme
(19) exists, the QR decompositions being taken by `exists_isQR`, as soon as `B¹` is defined, that
is, as soon as the ratio `B¹_j/B⁰_j` computed from (19f), (19g) is nonzero. The basis `V̂̂¹` can be
taken with first column `e₁`, so the hypotheses of `theorem_3_conservative` can hold together; see
also `exists_isSVDTruncation`, `exists_isConservativeTruncation`. -/
theorem exists_isDLRAStep {Δx Δt σ : ℝ} (hΔt : 0 < Δt) (hσ : 0 ≤ σ)
    (A absA : Matrix (Fin K) (Fin K) ℝ) {B₀ : ZMod N → ℝ} (hB₀ : ∀ j, B₀ j ≠ 0)
    (X₀ : Matrix (ZMod N) r ℝ) (S₀ : Matrix r r ℝ) (V₀ : Matrix (Fin K) r ℝ)
    (hr : ∀ j, 1 + σ * Δt +
      √2 * (σ * Δt) * explicitPart Δx Δt A absA B₀ (X₀ * S₀ * V₀ᵀ) j 0 ≠ 0) :
    ∃ (n₁ n₂ n₃ n₄ n₅ n₆ n₇ : ℕ)
      (d : Stage N K r (Fin n₁) (Fin n₂) (Fin n₃) (Fin n₄) (Fin n₅) (Fin n₆) (Unit ⊕ Fin n₇))
      (Vrem : Matrix (Fin K) (Fin n₇) ℝ), IsDLRAStep Δx Δt σ A absA B₀ X₀ S₀ V₀ d ∧
        d.Vo = Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem := by
  have hs0 : 0 ≤ σ * Δt := mul_nonneg hσ hΔt.le
  have h1 : 1 + σ * Δt ≠ 0 := by positivity
  obtain ⟨n₁, Xh, qXh⟩ := exists_isQR (Matrix.fromCols (kStep Δx Δt σ A absA B₀ X₀ S₀ V₀) X₀)
  obtain ⟨n₂, Vh, qVh⟩ := exists_isQR (Matrix.fromCols (lStep Δx Δt σ A absA B₀ X₀ S₀ V₀) V₀)
  obtain ⟨n₃, Xs, qXs⟩ := exists_isQR (Matrix.fromCols (Matrix.fromCols Xh
    (weighted B₀ (Dx Δx) * X₀)) (weighted B₀ (Dxx Δx) * X₀))
  obtain ⟨n₄, Vs, qVs⟩ := exists_isQR (Matrix.fromCols (Matrix.fromCols Vh (Aᵀ * V₀)) (absAᵀ * V₀))
  choose ρ φ hρ0 hρ1 hρ2 using fun j => solve_zeroth hs0 (hr j)
  set St0 : Matrix (Fin n₃) (Fin n₄) ℝ := Xsᵀ * X₀ * S₀ * (Vsᵀ * V₀)ᵀ with hSt0
  set Ss : Matrix (Fin n₃) (Fin n₄) ℝ := (1 / (1 + σ * Δt)) • (St0
    - Δt • (Xsᵀ * weighted B₀ (Dx Δx) * Xs * St0 * (Vsᵀ * Aᵀ * Vs))
    + Δt • (Xsᵀ * weighted B₀ (Dxx Δx) * Xs * St0 * (Vsᵀ * absAᵀ * Vs))) with hSs
  set B₁ : ZMod N → ℝ := fun j => B₀ j * ρ j with hB₁
  obtain ⟨n₅, Xt, qXt⟩ := exists_isQR (diagonal (fun j => B₀ j / B₁ j) * (Xs * Ss))
  obtain ⟨hXt, St, hSt⟩ := Matrix.isOrthCapture_iff.1 qXt
  obtain ⟨n₆, Xo, qXo⟩ := exists_isQR (Matrix.fromCols (Matrix.replicateCol Unit φ) Xt)
  obtain ⟨n₇, Vrem, qVo⟩ := exists_isQR_e₁ Vs
  set Vo := Matrix.fromCols (Matrix.replicateCol Unit (e₁ (K := K))) Vrem with hVo
  have hratio (j : ZMod N) : B₁ j / B₀ j = ρ j := by
    have := hB₀ j
    simp only [hB₁]
    field_simp
  obtain ⟨-, hcXh⟩ := capture_fromCols qXh.capture
  obtain ⟨hcXs12, -⟩ := capture_fromCols qXs.capture
  obtain ⟨hcXsh, -⟩ := capture_fromCols hcXs12
  obtain ⟨-, hcVh⟩ := capture_fromCols qVh.capture
  obtain ⟨hcVs12, -⟩ := capture_fromCols qVs.capture
  obtain ⟨hcVsh, -⟩ := capture_fromCols hcVs12
  have hZ : Xs * St0 * Vsᵀ = X₀ * S₀ * V₀ᵀ :=
    reconstruct_of_capture S₀ (capture_trans hcXh hcXsh) (capture_trans hcVh hcVsh)
  refine ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇,
    { Kstar := kStep Δx Δt σ A absA B₀ X₀ S₀ V₀
      Lstar := lStep Δx Δt σ A absA B₀ X₀ S₀ V₀
      Xh := Xh, Vh := Vh, Xs := Xs, Vs := Vs, Ss := Ss, B₁ := B₁, φ := φ, Xt := Xt, St := St
      Xo := Xo, Vo := Vo
      So := Xoᵀ * Xt * St * Vsᵀ *
          (1 - Matrix.vecMulVec (e₁ (K := K)) (e₁ (K := K))) * Vo
        + Xoᵀ * Matrix.vecMulVec φ (e₁ (K := K)) * Vo }, Vrem, ?_, rfl⟩
  refine ⟨⟨qXh, qXs, qVh, qVs, rfl, fun j => ?_, fun j => ?_, hXt, hSt.symm, qXo, qVo, rfl⟩,
    rfl, rfl⟩
  · change B₁ j / B₀ j * φ j = 1 / (1 + σ * Δt) * (X₀ * S₀ * V₀ᵀ) j 0
      - Δt / (1 + σ * Δt) * (weighted B₀ (Dx Δx) * (Xs * St0 * Vsᵀ) * Aᵀ) j 0
      + Δt / (1 + σ * Δt) * (weighted B₀ (Dxx Δx) * (Xs * St0 * Vsᵀ) * absAᵀ) j 0
      + √2 * σ * Δt / (1 + σ * Δt) * (B₁ j / B₀ j)
    rw [hratio, hZ]
    have e := hρ2 j
    rw [explicitPart_eq] at e
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e
    field_simp
    linarith
  · change B₁ j / B₀ j = 1 + σ * Δt * (B₁ j / B₀ j) * (√2 * φ j - 2)
    rw [hratio]
    exact hρ1 j

/-- **Non-vacuity of the truncation of arXiv 2502.03008, Section 5.1**: for every `t` not exceeding
the rank of `Ŝ̂¹`, truncating to its `t` largest singular values is an `IsSVDTruncation`. -/
theorem exists_isSVDTruncation (Xo : Matrix (ZMod N) ιXo ℝ) (So : Matrix ιXo ιVo ℝ)
    (Vo : Matrix (Fin K) ιVo ℝ) {t : ℕ} (ht : t ≤ So.rank) :
    ∃ (X₁ : Matrix (ZMod N) (Fin t) ℝ) (S₁ : Matrix (Fin t) (Fin t) ℝ)
      (V₁ : Matrix (Fin K) (Fin t) ℝ), IsSVDTruncation Xo So Vo X₁ S₁ V₁ := by
  obtain ⟨U, V, σ, hU, hV, -, -, -, hS⟩ := LeanDLRA.SVD.exists_svd So rfl
  exact ⟨_, _, _, So.rank, U, V, σ, Fin.castLEEmb ht, hU, hV, hS, rfl, rfl, rfl⟩

/-- **Non-vacuity of the conservative truncation of arXiv 2502.03008, Section 5.4**. -/
theorem exists_isConservativeTruncation {ιq : Type*} [Fintype ιq] [DecidableEq ιq]
    (Xo : Matrix (ZMod N) ιXo ℝ) (So : Matrix ιXo (Unit ⊕ ιq) ℝ) (Vrem : Matrix (Fin K) ιq ℝ) :
    ∃ (n₁ n₂ : ℕ) (X₁ : Matrix (ZMod N) (Fin n₁) ℝ) (S₁ : Matrix (Fin n₁) (Fin n₂) ℝ)
      (V₁ : Matrix (Fin K) (Fin n₂) ℝ), IsConservativeTruncation Xo So Vrem X₁ S₁ V₁ := by
  obtain ⟨l, Xrem, qXrem⟩ := exists_isQR ((Xo * So).submatrix id Sum.inr)
  obtain ⟨hXrem, Srem, hK⟩ := Matrix.isOrthCapture_iff.1 qXrem
  obtain ⟨P, Q, s, hP, hQ, -, -, -, hS⟩ := LeanDLRA.SVD.exists_svd Srem rfl
  obtain ⟨n₁, X₁, qX₁⟩ := exists_isQR (Matrix.fromCols (Matrix.replicateCol Unit fun j =>
      (Xo * So) j (Sum.inl ()) / √(∑ i, (Xo * So) i (Sum.inl ()) ^ 2))
    (Xrem * P.submatrix id (Function.Embedding.refl (Fin Srem.rank))))
  obtain ⟨n₂, V₁, qV₁⟩ := exists_isQR (Matrix.fromCols
    (Matrix.replicateCol Unit (e₁ (K := K)))
    (Vrem * Q.submatrix id (Function.Embedding.refl (Fin Srem.rank))))
  obtain ⟨hX₁, R₁, hR₁⟩ := Matrix.isOrthCapture_iff.1 qX₁
  obtain ⟨hV₁, R₂, hR₂⟩ := Matrix.isOrthCapture_iff.1 qV₁
  exact ⟨n₁, n₂, X₁, _, V₁, l, Srem.rank, Srem.rank, Xrem, Srem, P, Q, s,
    Function.Embedding.refl _, R₁, R₂, hXrem, hK, hP, hQ, hS, hX₁, hV₁, hR₁, hR₂, rfl⟩

end Truncation

end DLRA

/-- The local `qr` predicate of this file (`Qᵀ Q = 1 ∧ ∃ R, Y = Q R`), replaced by the core
`Matrix.IsOrthCapture` (equivalent: `Matrix.isOrthCapture_iff`). -/
@[deprecated (since := "2026-11-09")] alias IsQR := Matrix.IsOrthCapture

end LeanDLRA.Literature.P2502_03008
