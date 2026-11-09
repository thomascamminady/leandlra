import LeanDLRA.Classical.SVD
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2402.16746: AP energy-stable DLRA for thermal radiative transfer

This module proves Theorem 7 of Patwardhan, Frank and Kusch (`theorem_7`): the asymptotic-preserving
rank-adaptive BUG integrator for the linearised thermal radiative transfer equations is energy
stable under the CFL condition (3.4). It is proved for the fully discrete scheme itself, not for an
abstract core: the staggered periodic grid (`dPlus`, `dMinus`, `flux`), the `P_N` closure with the
Gauss–Legendre factorisation `A_f = T_f M T_fᵀ` (`pnFlux`, `legendreN`, `IsGaussLegendre`,
`gaussRows`, `Apos`, `Aneg`, `bPN`, `betaN`), the energy (`energy`) and all steps of Section 4.2
(`APBUGStep`): K- and L-step (4.2), (4.3), augmentation, S-step (4.23), the truncation (4.17)–(4.19)
of the remainder only, and the updates (4.20), (4.21). A sharper CFL condition suffices
(`theorem_7_sharp`). The ingredients are the energy estimate of Appendix A (`energy_le_core`, with
Lemmas 2, 3, 5 as `sum_mul_dPlus`, `sum_dPlus_sq_le`, `inner_flux_self`, and in place of the false
Lemma 6 the bound `norm_fluxAdj_sq_le`),
the Galerkin test of the S-step (`galerkin_test`, `APBUGStep.initial_eq`), and two facts about the
truncation: it keeps the moment `g b` entering the macro update (`APBUGStep.moment_eq`) and it does
not increase the norm (`APBUGStep.norm_new_le`). The paper's proof mentions only the second one, but
the first is needed as well, because the macro update (4.20) uses the truncated `g`, while the
S-step is tested with the untruncated one.

## Differences from the paper

* Boundary conditions: the grid is periodic (`ZMod n`, `Δx > 0` arbitrary). The paper also allows
  zero boundary values, which are not treated: `norm_fluxAdj_sq_le` uses `‖𝒟⁻ φ‖ = ‖𝒟⁺ φ‖`.
* Moments: `Fin N` carries the moments `k = 1, …, N` of the paper, so index `0` is `k = 1`. The
  matrix `A_f` has the entries `a_k` of the paper's display of `A`, and `P_k` is defined through its
  three-term recurrence (`legendreN_zero`, `legendreN_one`, `legendreN_two` give the first three).
  The Gauss data are the roots of `P_{N+1}` and the Christoffel numbers. That `T_f` is orthogonal,
  `A_f = T_f M T_fᵀ`, `∑ w_k = 2` and `β_N ≥ 2` are proved, not assumed.
* `T = (√w_k P_i(μ_k))` is the `N × (N+1)` matrix of the paper; `A^± = ½ T (M ± |M|) Tᵀ` and
  `T Tᵀ = 1`, but `Tᵀ T ≠ 1`.
* Lemmas 2 and 3 are proved for scalar sequences; the paper's vector-valued forms follow
  componentwise.
* Lemma 6 as printed, with the right side `2 β_N ∑ (𝒟⁺g)ᵀ A² 𝒟⁺g`, is false
  (`P2402_16746a.lemma_6_false`), and so is the first identity of Lemma 4
  (`P2402_16746a.lemma_4_false`). What is proved instead, `norm_fluxAdj_sq_le`, has the right side
  `∑_k μ_k² ‖𝒟⁺ v̂_k‖² = ∑ (𝒟⁺g)ᵀ T M² Tᵀ 𝒟⁺g` (not `A²`) with the constant `1`, and it suffices.
  Also `1/(4 c)` can replace `1/(5 c β_N)` in (3.4) (`theorem_7_sharp`).
* Lemma 5, second identity: the printed last term has the sign of
  `(gⁿ - gⁿ⁺¹)ᵀ(A⁺𝒟⁺ + A⁻𝒟⁻)gⁿ⁺¹`, opposite to the paper's own (A.13); the identity proved here,
  `inner_flux_split`, has the sign of (A.13), `(gⁿ⁺¹ - gⁿ)ᵀ(A⁺𝒟⁺ + A⁻𝒟⁻)gⁿ⁺¹`. The proof only uses
  the term in absolute value.
* `ε > 0` is a field of `Params` (the paper divides by `ε` in (A.4b)).
* Reading of the scheme: `K̂ᵃᵖ` is the block of columns of `X̂ Ŝ`, and `S̃ⁿ = M̂ Sⁿ N̂ᵀ`; the
  reasons are given at `APBUGStep`. The protected block may have any width, the bases need only
  contain the required vectors, and any selection of singular triples is allowed.
* The result is for one step, as in the paper. The K- and L-steps are part of `APBUGStep`, but the
  energy bound does not use them, so it holds for all `K(t_{n+1})`, `L(t_{n+1})`.

Non-vacuity: `exists_isGaussLegendre`, `exists_APBUGStep`, `bPN_ne_zero`. Theorems 1–6 of the paper
are the sibling slice; the case `gh = g1` of `energy_le_core` is the estimate of Theorem 2.
Theorem 7 holds as stated; Lemmas 4 and 6, which its proof uses, are false as printed (sibling
slice).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2402_16746

namespace APEnergy

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ### Periodic difference operators (Lemmas 2 and 3 of the paper) -/

section Grid

variable {n : ℕ} [NeZero n]

/-- The forward difference on the periodic grid `ZMod n`.  With `φ i = φ_{i+1/2}` this is
`𝒟⁺ φ_{i+1/2} = (φ_{i+3/2} - φ_{i+1/2}) / Δx`; with `φ i = φ_i` it is
`δ⁰ φ_{i+1/2} = (φ_{i+1} - φ_i) / Δx`. -/
noncomputable def dPlus (Δx : ℝ) (φ : ZMod n → ℝ) (i : ZMod n) : ℝ := (φ (i + 1) - φ i) / Δx

/-- The backward difference on the periodic grid `ZMod n`.  With `φ i = φ_{i+1/2}` this is both
`𝒟⁻ φ_{i+1/2} = (φ_{i+1/2} - φ_{i-1/2}) / Δx` and `𝒟⁰ φ_i = (φ_{i+1/2} - φ_{i-1/2}) / Δx`. -/
noncomputable def dMinus (Δx : ℝ) (φ : ZMod n → ℝ) (i : ZMod n) : ℝ := (φ i - φ (i - 1)) / Δx

lemma sum_shift_add (f : ZMod n → ℝ) : ∑ i, f (i + 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.addRight 1) f

lemma sum_shift_sub (f : ZMod n → ℝ) : ∑ i, f (i - 1) = ∑ i, f i :=
  Equiv.sum_comp (Equiv.subRight 1) f

lemma dMinus_eq (Δx : ℝ) (φ : ZMod n → ℝ) (i : ZMod n) :
    dMinus Δx φ i = dPlus Δx φ (i - 1) := by
  simp [dMinus, dPlus]

/-- **Lemma 2** of arXiv 2402.16746 (summation by parts, eq. (A.1)), for periodic boundary values
and scalar sequences (the paper's `ℝ^N`-valued form follows componentwise). The paper also allows
zero boundary values; those are not treated here. -/
theorem sum_mul_dPlus (Δx : ℝ) (ζ φ : ZMod n → ℝ) :
    ∑ i, ζ i * dPlus Δx φ i = -∑ i, dMinus Δx ζ i * φ i := by
  have h : ∑ i, ζ (i - 1) * φ i = ∑ i, ζ i * φ (i + 1) := by
    rw [← sum_shift_add (fun i => ζ (i - 1) * φ i)]
    simp
  have e1 : ∀ i, ζ i * dPlus Δx φ i = (ζ i * φ (i + 1) - ζ i * φ i) / Δx := fun i => by
    simp only [dPlus]
    ring
  have e2 : ∀ i, dMinus Δx ζ i * φ i = (ζ i * φ i - ζ (i - 1) * φ i) / Δx := fun i => by
    simp only [dMinus]
    ring
  simp only [e1, e2, ← Finset.sum_div, Finset.sum_sub_distrib, h]
  ring

/-- **Lemma 2** of arXiv 2402.16746 (eq. (A.1)), the other sign, for periodic boundary values. -/
theorem sum_mul_dMinus (Δx : ℝ) (ζ φ : ZMod n → ℝ) :
    ∑ i, ζ i * dMinus Δx φ i = -∑ i, dPlus Δx ζ i * φ i := by
  have h := sum_mul_dPlus Δx φ ζ
  have e1 : ∑ i, ζ i * dMinus Δx φ i = ∑ i, dMinus Δx φ i * ζ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∑ i, dPlus Δx ζ i * φ i = ∑ i, φ i * dPlus Δx ζ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, e2, h, neg_neg]

/-- Periodicity: `‖𝒟⁻ φ‖ = ‖𝒟⁺ φ‖`. -/
lemma sum_dMinus_sq (Δx : ℝ) (φ : ZMod n → ℝ) :
    ∑ i, dMinus Δx φ i ^ 2 = ∑ i, dPlus Δx φ i ^ 2 := by
  simp only [dMinus_eq]
  exact sum_shift_sub (fun i => dPlus Δx φ i ^ 2)

/-- **Lemma 3** of arXiv 2402.16746 (eq. (A.2)): `∑ (𝒟⁺ φ)² ≤ 4/Δx² ∑ φ²`, for scalar sequences
on the periodic grid (the paper's `ℝ^{N+1}`-valued form follows by summing over components). -/
theorem sum_dPlus_sq_le {Δx : ℝ} (φ : ZMod n → ℝ) :
    ∑ i, dPlus Δx φ i ^ 2 ≤ 4 / Δx ^ 2 * ∑ i, φ i ^ 2 := by
  have h : ∀ i, dPlus Δx φ i ^ 2 ≤ (2 * φ (i + 1) ^ 2 + 2 * φ i ^ 2) / Δx ^ 2 := fun i => by
    simp only [dPlus, div_pow]
    gcongr
    nlinarith [sq_nonneg (φ (i + 1) + φ i)]
  calc ∑ i, dPlus Δx φ i ^ 2 ≤ ∑ i, (2 * φ (i + 1) ^ 2 + 2 * φ i ^ 2) / Δx ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = 4 / Δx ^ 2 * ∑ i, φ i ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_shift_add (fun i => φ i ^ 2)]
        ring

/-- The identity behind Lemma 5: `∑ (𝒟⁻ φ) φ = (Δx/2) ∑ (𝒟⁺ φ)²`. -/
lemma sum_dMinus_mul_self {Δx : ℝ} (hΔx : Δx ≠ 0) (φ : ZMod n → ℝ) :
    ∑ i, dMinus Δx φ i * φ i = Δx / 2 * ∑ i, dPlus Δx φ i ^ 2 := by
  have h : ∑ i, φ (i - 1) * φ i = ∑ i, φ i * φ (i + 1) := by
    rw [← sum_shift_add (fun i => φ (i - 1) * φ i)]
    simp
  have e1 : ∀ i, dMinus Δx φ i * φ i = (φ i ^ 2 - φ (i - 1) * φ i) / Δx := fun i => by
    simp only [dMinus]
    ring
  have e2 : ∀ i, Δx / 2 * dPlus Δx φ i ^ 2 =
      (φ (i + 1) ^ 2 + φ i ^ 2 - 2 * (φ i * φ (i + 1))) / (2 * Δx) := fun i => by
    simp only [dPlus]
    field_simp
    ring
  have e3 : ∑ i, φ (i + 1) ^ 2 = ∑ i, φ i ^ 2 := sum_shift_add (fun i => φ i ^ 2)
  rw [Finset.mul_sum]
  simp only [e1, e2, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, h, e3]
  field_simp
  ring

/-- The identity behind Lemma 5: `∑ (𝒟⁺ φ) φ = -(Δx/2) ∑ (𝒟⁺ φ)²`. -/
lemma sum_dPlus_mul_self {Δx : ℝ} (hΔx : Δx ≠ 0) (φ : ZMod n → ℝ) :
    ∑ i, dPlus Δx φ i * φ i = -(Δx / 2 * ∑ i, dPlus Δx φ i ^ 2) := by
  have h := sum_mul_dPlus Δx φ φ
  have e : ∑ i, dPlus Δx φ i * φ i = ∑ i, φ i * dPlus Δx φ i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, h, sum_dMinus_mul_self hΔx]

end Grid

/-! ### The flux operators -/

section Flux

variable {n : ℕ} [NeZero n] {ν κ : Type*} [Fintype ν] [Fintype κ]

/-- `𝒟⁺` applied to each column of a matrix whose rows are indexed by the grid. -/
noncomputable def DP (Δx : ℝ) (G : Matrix (ZMod n) ν ℝ) : Matrix (ZMod n) ν ℝ :=
  Matrix.of fun i k => dPlus Δx (fun j => G j k) i

/-- `𝒟⁻` applied to each column of a matrix whose rows are indexed by the grid. -/
noncomputable def DM (Δx : ℝ) (G : Matrix (ZMod n) ν ℝ) : Matrix (ZMod n) ν ℝ :=
  Matrix.of fun i k => dMinus Δx (fun j => G j k) i

lemma DP_mul (Δx : ℝ) (G : Matrix (ZMod n) ν ℝ) (B : Matrix ν κ ℝ) :
    DP Δx (G * B) = DP Δx G * B := by
  ext i k
  simp only [DP, dPlus, Matrix.of_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma DM_mul (Δx : ℝ) (G : Matrix (ZMod n) ν ℝ) (B : Matrix ν κ ℝ) :
    DM Δx (G * B) = DM Δx G * B := by
  ext i k
  simp only [DM, dMinus, Matrix.of_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma DP_sub (Δx : ℝ) (F G : Matrix (ZMod n) ν ℝ) : DP Δx (F - G) = DP Δx F - DP Δx G := by
  ext i k
  simp only [DP, dPlus, Matrix.of_apply, Matrix.sub_apply]
  ring

lemma DM_sub (Δx : ℝ) (F G : Matrix (ZMod n) ν ℝ) : DM Δx (F - G) = DM Δx F - DM Δx G := by
  ext i k
  simp only [DM, dMinus, Matrix.of_apply, Matrix.sub_apply]
  ring

/-- Summation by parts for matrices: `⟪𝒟⁻ F, G⟫ = -⟪F, 𝒟⁺ G⟫`. -/
lemma inner_DM (Δx : ℝ) (F G : Matrix (ZMod n) ν ℝ) : ⟪DM Δx F, G⟫ = -⟪F, DP Δx G⟫ := by
  simp only [Frobenius.inner_def, DM, DP, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i k => F i k * dPlus Δx (fun j => G j k) i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [sum_mul_dPlus, neg_neg]

/-- Summation by parts for matrices: `⟪𝒟⁺ F, G⟫ = -⟪F, 𝒟⁻ G⟫`. -/
lemma inner_DP (Δx : ℝ) (F G : Matrix (ZMod n) ν ℝ) : ⟪DP Δx F, G⟫ = -⟪F, DM Δx G⟫ := by
  linarith [inner_DM Δx G F, real_inner_comm (DP Δx F) G, real_inner_comm (DM Δx G) F]

/-- The upwind flux `ℒ g_{i+1/2} = (A⁺ 𝒟⁻ + A⁻ 𝒟⁺) g_{i+1/2}`, written for the matrix `g` whose
rows are the vectors `g_{i+1/2}`. Since `A^±` are symmetric, it acts on the right. -/
noncomputable def flux (Δx : ℝ) (Ap Am : Matrix ν ν ℝ) (g : Matrix (ZMod n) ν ℝ) :
    Matrix (ZMod n) ν ℝ :=
  DM Δx g * Ap + DP Δx g * Am

/-- Minus the adjoint of the flux: `(A⁺ 𝒟⁺ + A⁻ 𝒟⁻) g_{i+1/2}`. -/
noncomputable def fluxAdj (Δx : ℝ) (Ap Am : Matrix ν ν ℝ) (g : Matrix (ZMod n) ν ℝ) :
    Matrix (ZMod n) ν ℝ :=
  DP Δx g * Ap + DM Δx g * Am

lemma inner_flux (Δx : ℝ) {Ap Am : Matrix ν ν ℝ} (hp : Apᵀ = Ap) (hm : Amᵀ = Am)
    (F G : Matrix (ZMod n) ν ℝ) : ⟪flux Δx Ap Am F, G⟫ = -⟪F, fluxAdj Δx Ap Am G⟫ := by
  simp only [flux, fluxAdj, inner_add_left, inner_add_right, Frobenius.inner_mul_right, hp, hm,
    inner_DM, inner_DP, DP_mul, DM_mul]
  ring

/-- The second identity of Lemma 5 of arXiv 2402.16746, the splitting of the term `⟪ℒ gⁿ, gⁿ⁺¹⟫`,
with the sign of (A.13) (the printed Lemma 5 has the opposite sign in the last term). -/
lemma inner_flux_split (Δx : ℝ) {Ap Am : Matrix ν ν ℝ} (hp : Apᵀ = Ap) (hm : Amᵀ = Am)
    (g g₁ : Matrix (ZMod n) ν ℝ) :
    ⟪flux Δx Ap Am g, g₁⟫ = ⟪flux Δx Ap Am g₁, g₁⟫ + ⟪g₁ - g, fluxAdj Δx Ap Am g₁⟫ := by
  have e : flux Δx Ap Am g = flux Δx Ap Am g₁ + flux Δx Ap Am (g - g₁) := by
    simp only [flux, DP_sub, DM_sub, Matrix.sub_mul]
    abel
  rw [e, inner_add_left, inner_flux Δx hp hm (g - g₁), ← neg_sub g g₁, inner_neg_left]

end Flux

/-! ### Eigen-coordinates: Lemmas 4, 5 and 6 of the paper -/

section Coordinates

variable {n : ℕ} [NeZero n] {ν κ : Type*} [Fintype ν] [Fintype κ] [DecidableEq ν] [DecidableEq κ]

/-- `A⁺ = ½ T (M + |M|) Tᵀ`. -/
noncomputable def Apos (T : Matrix ν κ ℝ) (μ : κ → ℝ) : Matrix ν ν ℝ :=
  T * diagonal (fun k => (μ k + |μ k|) / 2) * Tᵀ

/-- `A⁻ = ½ T (M - |M|) Tᵀ`. -/
noncomputable def Aneg (T : Matrix ν κ ℝ) (μ : κ → ℝ) : Matrix ν ν ℝ :=
  T * diagonal (fun k => (μ k - |μ k|) / 2) * Tᵀ

lemma Apos_transpose (T : Matrix ν κ ℝ) (μ : κ → ℝ) : (Apos T μ)ᵀ = Apos T μ := by
  simp [Apos, Matrix.transpose_mul, Matrix.mul_assoc]

lemma Aneg_transpose (T : Matrix ν κ ℝ) (μ : κ → ℝ) : (Aneg T μ)ᵀ = Aneg T μ := by
  simp [Aneg, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The quantity `‖𝒟⁺ v̂_k‖²` (without the factor `Δx`). -/
noncomputable def Zk (Δx : ℝ) (v : Matrix (ZMod n) κ ℝ) (k : κ) : ℝ :=
  ∑ i, dPlus Δx (fun j => v j k) i ^ 2

lemma Zk_nonneg (Δx : ℝ) (v : Matrix (ZMod n) κ ℝ) (k : κ) : 0 ≤ Zk Δx v k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma inner_mul_diagonal (A B : Matrix (ZMod n) κ ℝ) (d : κ → ℝ) :
    ⟪A * diagonal d, B⟫ = ∑ k, d k * ∑ i, A i k * B i k := by
  simp only [Frobenius.inner_def, Matrix.mul_diagonal, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- `⟪A T D Tᵀ, g⟫ = ⟪A T D, g T⟫`. -/
lemma inner_mul_conj (A g : Matrix (ZMod n) ν ℝ) (T : Matrix ν κ ℝ) (d : κ → ℝ) :
    ⟪A * (T * diagonal d * Tᵀ), g⟫ = ⟪A * T * diagonal d, g * T⟫ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right, Matrix.transpose_transpose,
    Matrix.mul_assoc A T]

/-- **Lemma 5** of arXiv 2402.16746, first identity, in the coordinates `v̂ = g T` of Lemma 4:
`∑ gᵀ ℒ g = (Δx/2) ∑_k |μ_k| ‖𝒟⁺ v̂_k‖²`. -/
theorem inner_flux_self {Δx : ℝ} (hΔx : Δx ≠ 0) (T : Matrix ν κ ℝ) (μ : κ → ℝ)
    (g : Matrix (ZMod n) ν ℝ) :
    ⟪flux Δx (Apos T μ) (Aneg T μ) g, g⟫ = Δx / 2 * ∑ k, |μ k| * Zk Δx (g * T) k := by
  have h1 : ⟪DM Δx g * Apos T μ, g⟫ =
      ∑ k, (μ k + |μ k|) / 2 * (Δx / 2 * Zk Δx (g * T) k) := by
    rw [Apos, inner_mul_conj, ← DM_mul, inner_mul_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Zk, ← sum_dMinus_mul_self hΔx]
    rfl
  have h2 : ⟪DP Δx g * Aneg T μ, g⟫ =
      ∑ k, (μ k - |μ k|) / 2 * -(Δx / 2 * Zk Δx (g * T) k) := by
    rw [Aneg, inner_mul_conj, ← DP_mul, inner_mul_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Zk, ← sum_dPlus_mul_self hΔx]
    rfl
  rw [flux, inner_add_left, h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The bound used in place of Lemma 6** of arXiv 2402.16746:
`∑ |(A⁺ 𝒟⁺ + A⁻ 𝒟⁻) g|² ≤ ∑_k μ_k² ‖𝒟⁺ v̂_k‖²`, `v̂ = g T`, from `T Tᵀ = 1`.  The right side is
`∑ (𝒟⁺g)ᵀ T M² Tᵀ 𝒟⁺g`, not the printed `2 β_N ∑ (𝒟⁺g)ᵀ A² 𝒟⁺g`; the printed Lemma 6 is false
(`P2402_16746a.lemma_6_false`, where `A = 0` but `A^± ≠ 0`). -/
theorem norm_fluxAdj_sq_le {T : Matrix ν κ ℝ} (hT : T * Tᵀ = 1) (Δx : ℝ) (μ : κ → ℝ)
    (g : Matrix (ZMod n) ν ℝ) :
    ‖fluxAdj Δx (Apos T μ) (Aneg T μ) g‖ ^ 2 ≤ ∑ k, μ k ^ 2 * Zk Δx (g * T) k := by
  set v := g * T with hv
  set Y : Matrix (ZMod n) κ ℝ := DP Δx v * diagonal (fun k => (μ k + |μ k|) / 2) +
    DM Δx v * diagonal (fun k => (μ k - |μ k|) / 2) with hY
  have e : fluxAdj Δx (Apos T μ) (Aneg T μ) g = Y * Tᵀ := by
    simp only [fluxAdj, Apos, Aneg, hY, hv, DP_mul, DM_mul, Matrix.add_mul, Matrix.mul_assoc]
  have hT' : Tᵀᵀ * Tᵀ = 1 := by rwa [Matrix.transpose_transpose]
  have hle : ‖Y * Tᵀ‖ ≤ ‖Y‖ := norm_mul_le_of_orthonormal hT' Y
  have hY2 : ‖Y‖ ^ 2 = ∑ k, μ k ^ 2 * Zk Δx v k := by
    rw [Frobenius.norm_sq_eq_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hent : ∀ i, Y i k = (μ k + |μ k|) / 2 * dPlus Δx (fun j => v j k) i +
        (μ k - |μ k|) / 2 * dMinus Δx (fun j => v j k) i := fun i => by
      simp only [hY, Matrix.add_apply, Matrix.mul_diagonal, DP, DM, Matrix.of_apply]
      ring
    simp only [hent]
    rcases le_total 0 (μ k) with h | h
    · rw [abs_of_nonneg h, Zk, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [abs_of_nonpos h, Zk, ← sum_dMinus_sq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, ← hY2]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- The bound on the coupling term, the part of Lemmas 4 and 6 of arXiv 2402.16746 used for
`𝒟⁰ g₁`.  Here `b_j = √2 ∑_k t_k μ_k T_{jk}`, i.e. `b = γ₀ a` with `a` the off-block of the first
row `t` of `T_f M T_fᵀ`, and `∑ t_k² = 1`. -/
theorem sum_dMinus_moment_sq_le (T : Matrix ν κ ℝ) (Δx : ℝ) (μ t : κ → ℝ)
    (ht : ∑ k, t k ^ 2 = 1) {b : ν → ℝ} (hb : ∀ j, b j = √2 * ∑ k, t k * μ k * T j k)
    (g : Matrix (ZMod n) ν ℝ) :
    ∑ i, dMinus Δx (g *ᵥ b) i ^ 2 ≤ 2 * ∑ k, μ k ^ 2 * Zk Δx (g * T) k := by
  set v := g * T with hv
  have hq : ∀ i, dMinus Δx (g *ᵥ b) i =
      √2 * ∑ k, t k * (μ k * dMinus Δx (fun j => v j k) i) := fun i => by
    have e : ∀ i', (g *ᵥ b) i' = √2 * ∑ k, t k * (μ k * v i' k) := fun i' => by
      simp only [Matrix.mulVec, dotProduct, hb, hv, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    simp only [dMinus, e, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, mul_div_assoc,
      Finset.sum_div]
  have hi : ∀ i, dMinus Δx (g *ᵥ b) i ^ 2 ≤
      2 * ∑ k, μ k ^ 2 * dMinus Δx (fun j => v j k) i ^ 2 := fun i => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t
      (fun k => μ k * dMinus Δx (fun j => v j k) i)
    rw [ht, one_mul] at hcs
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num)]
    calc 2 * (∑ k, t k * (μ k * dMinus Δx (fun j => v j k) i)) ^ 2
        ≤ 2 * ∑ k, (μ k * dMinus Δx (fun j => v j k) i) ^ 2 := by gcongr
      _ = 2 * ∑ k, μ k ^ 2 * dMinus Δx (fun j => v j k) i ^ 2 := by
          simp only [mul_pow]
  calc ∑ i, dMinus Δx (g *ᵥ b) i ^ 2
      ≤ ∑ i, 2 * ∑ k, μ k ^ 2 * dMinus Δx (fun j => v j k) i ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 2 * ∑ k, μ k ^ 2 * Zk Δx v k := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, Zk, sum_dMinus_sq]

/-- `∑_k ‖𝒟⁺ v̂_k‖² ≤ 4/Δx² ‖g‖²`, from Lemma 3 of arXiv 2402.16746, since `v̂ = g T` is isometric
because `T Tᵀ = 1`. -/
theorem sum_Zk_le {T : Matrix ν κ ℝ} (hT : T * Tᵀ = 1) (Δx : ℝ) (g : Matrix (ZMod n) ν ℝ) :
    ∑ k, Zk Δx (g * T) k ≤ 4 / Δx ^ 2 * ‖g‖ ^ 2 := by
  have hT' : Tᵀᵀ * Tᵀ = 1 := by rwa [Matrix.transpose_transpose]
  have hiso : ‖g * T‖ = ‖g‖ := by
    have := Frobenius.norm_mul_transpose_of_orthonormal hT' g
    rwa [Matrix.transpose_transpose] at this
  rw [← hiso, Frobenius.norm_sq_eq_sum, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => sum_dPlus_sq_le _

end Coordinates

/-! ### The energy estimate of the linearised scheme -/

section Energy

/-- Physical and discretisation parameters of the linearised scheme (3.3) of arXiv 2402.16746:
`ε`, the speed of light `c`, the radiation constant `a`, the specific heat `c_ν`, the steps `Δt`,
`Δx`, the lower bound `σ₀ > 0` of the absorption cross section, and the cross section at the cell
centres (`σ i = σᵃ_i`) and at the interfaces (`σf i = σᵃ_{i+1/2}`). -/
structure Params (n : ℕ) where
  /-- The scaling parameter. -/
  ε : ℝ
  /-- The speed of light. -/
  c : ℝ
  /-- The radiation constant. -/
  a : ℝ
  /-- The specific heat. -/
  cν : ℝ
  /-- The time step. -/
  Δt : ℝ
  /-- The mesh width. -/
  Δx : ℝ
  /-- The lower bound of the cross section. -/
  σ₀ : ℝ
  /-- The cross section at the cell centres. -/
  σ : ZMod n → ℝ
  /-- The cross section at the interfaces. -/
  σf : ZMod n → ℝ
  ε_pos : 0 < ε
  c_pos : 0 < c
  a_pos : 0 < a
  cν_pos : 0 < cν
  Δt_pos : 0 < Δt
  Δx_pos : 0 < Δx
  σ₀_pos : 0 < σ₀
  σ_ge : ∀ i, σ₀ ≤ σ i
  σf_ge : ∀ i, σ₀ ≤ σf i

variable {n : ℕ} [NeZero n] {ν η : Type*} [Fintype ν] [Fintype η] [DecidableEq ν] [DecidableEq η]

/-- `κ = 2 / c_ν`. -/
noncomputable def Params.κ (p : Params n) : ℝ := 2 / p.cν

/-- The macroscopic variable `a T + (ε²/c) h` of the energy. -/
noncomputable def macroVar (p : Params n) (T h : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  p.a * T i + p.ε ^ 2 / p.c * h i

/-- The coupling `δ⁰(a c T + ε² h)_{i+1/2}` of the micro equation (linear emission, `Ψ = 1`). -/
noncomputable def coupling (p : Params n) (T h : ZMod n → ℝ) : ZMod n → ℝ :=
  dPlus p.Δx fun i => p.a * p.c * T i + p.ε ^ 2 * h i

/-- The energy of arXiv 2402.16746, Theorems 2 and 4, with `γ₀ = √2` and `‖φ‖² = ∑ φ² Δx`:
`eⁿ = ‖a T + (ε²/c) h‖² + ‖(ε/(γ₀ c)) g‖² + ‖√(a c_ν / 2) T‖²`. -/
noncomputable def energy (p : Params n) (T h : ZMod n → ℝ) (g : Matrix (ZMod n) ν ℝ) : ℝ :=
  ∑ i, (p.a * T i + p.ε ^ 2 / p.c * h i) ^ 2 * p.Δx +
    ∑ i, ∑ k, (p.ε / (√2 * p.c) * g i k) ^ 2 * p.Δx +
      ∑ i, (√(p.a * p.cν / 2) * T i) ^ 2 * p.Δx

lemma energy_eq (p : Params n) (T h : ZMod n → ℝ) (g : Matrix (ZMod n) ν ℝ) :
    energy p T h g = p.Δx * (∑ i, macroVar p T h i ^ 2 + p.ε ^ 2 / (2 * p.c ^ 2) * ‖g‖ ^ 2 +
      p.a * p.cν / 2 * ∑ i, T i ^ 2) := by
  have hpos : 0 ≤ p.a * p.cν / 2 := by
    have := p.a_pos
    have := p.cν_pos
    positivity
  have e2 : ∀ x : ℝ, (p.ε / (√2 * p.c) * x) ^ 2 = p.ε ^ 2 / (2 * p.c ^ 2) * x ^ 2 := fun x => by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  have e3 : ∀ x : ℝ, (√(p.a * p.cν / 2) * x) ^ 2 = p.a * p.cν / 2 * x ^ 2 := fun x => by
    rw [mul_pow, Real.sq_sqrt hpos]
  simp only [energy, e2, e3, Frobenius.norm_sq_eq_sum, macroVar, ← Finset.sum_mul,
    ← Finset.mul_sum]
  ring

/-- The macroscopic part of the energy estimate: (A.5) and (A.10) of arXiv 2402.16746 added, as an
identity (the paper drops the term `‖T^{n+1} - Tⁿ‖²`). -/
lemma macro_identity (p : Params n) {Tn hn Tn1 hn1 q : ZMod n → ℝ}
    (hmacro : ∀ i, p.ε ^ 2 / p.c * ((hn1 i - hn i) / p.Δt) + p.a * p.κ * p.σ i * hn1 i +
      1 / 2 * dMinus p.Δx q i = -p.σ i * hn1 i)
    (htemp : ∀ i, (Tn1 i - Tn i) / p.Δt = p.κ * p.σ i * hn1 i) :
    (∑ i, macroVar p Tn1 hn1 i ^ 2 - ∑ i, macroVar p Tn hn i ^ 2 +
        ∑ i, (macroVar p Tn1 hn1 i - macroVar p Tn hn i) ^ 2) +
      p.a * p.cν / 2 * (∑ i, Tn1 i ^ 2 - ∑ i, Tn i ^ 2 + ∑ i, (Tn1 i - Tn i) ^ 2) +
        p.Δt * ∑ i, dMinus p.Δx q i * macroVar p Tn1 hn1 i =
      -(2 * p.Δt * (p.ε ^ 2 / p.c) * ∑ i, p.σ i * hn1 i ^ 2) := by
  have hΔt : p.Δt ≠ 0 := p.Δt_pos.ne'
  have hκ : p.κ * p.cν = 2 := by
    have := p.cν_pos.ne'
    simp only [Params.κ]
    field_simp
  have hpt : ∀ i, (macroVar p Tn1 hn1 i ^ 2 - macroVar p Tn hn i ^ 2 +
      (macroVar p Tn1 hn1 i - macroVar p Tn hn i) ^ 2) +
      p.a * p.cν / 2 * (Tn1 i ^ 2 - Tn i ^ 2 + (Tn1 i - Tn i) ^ 2) +
        p.Δt * (dMinus p.Δx q i * macroVar p Tn1 hn1 i) =
      -(2 * p.Δt * (p.ε ^ 2 / p.c) * (p.σ i * hn1 i ^ 2)) := fun i => by
    have hT : Tn1 i - Tn i = p.Δt * (p.κ * p.σ i * hn1 i) := by
      have := htemp i
      field_simp at this ⊢
      linarith
    have hh : p.ε ^ 2 / p.c * (hn1 i - hn i) =
        p.Δt * (-p.σ i * hn1 i - p.a * p.κ * p.σ i * hn1 i - 1 / 2 * dMinus p.Δx q i) := by
      have h := hmacro i
      have e : p.ε ^ 2 / p.c * (hn1 i - hn i) =
          p.Δt * (p.ε ^ 2 / p.c * ((hn1 i - hn i) / p.Δt)) := by
        field_simp
      rw [e]
      congr 1
      linarith
    have hP : macroVar p Tn1 hn1 i - macroVar p Tn hn i =
        p.Δt * (-p.σ i * hn1 i - 1 / 2 * dMinus p.Δx q i) := by
      have e : macroVar p Tn1 hn1 i - macroVar p Tn hn i =
          p.a * (Tn1 i - Tn i) + p.ε ^ 2 / p.c * (hn1 i - hn i) := by
        simp only [macroVar]
        ring
      rw [e, hT, hh]
      ring
    have hP1 : macroVar p Tn1 hn1 i = p.a * Tn1 i + p.ε ^ 2 / p.c * hn1 i := rfl
    generalize macroVar p Tn1 hn1 i = P1 at hP hP1 ⊢
    generalize macroVar p Tn hn i = P0 at hP ⊢
    have e0 : P0 = P1 - p.Δt * (-p.σ i * hn1 i - 1 / 2 * dMinus p.Δx q i) := by linarith
    have e1 : Tn i = Tn1 i - p.Δt * (p.κ * p.σ i * hn1 i) := by linarith
    rw [e0, e1, hP1]
    linear_combination (p.a * Tn1 i * p.Δt * p.σ i * hn1 i) * hκ
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset (ZMod n)) = Finset.univ)
    (fun i _ => hpt i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib] at h
  exact h

lemma inner_vecMulVec (d : ZMod n → ℝ) (b : ν → ℝ) (G : Matrix (ZMod n) ν ℝ) :
    ⟪vecMulVec d b, G⟫ = ∑ i, d i * (G *ᵥ b) i := by
  simp only [Frobenius.inner_def, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma coupling_eq (p : Params n) (T h : ZMod n → ℝ) (i : ZMod n) :
    coupling p T h i = p.c * dPlus p.Δx (macroVar p T h) i := by
  have := p.c_pos.ne'
  simp only [coupling, dPlus, macroVar]
  field_simp

/-- The pairing of the micro-macro coupling with a micro iterate, using Lemma 2 (eq. (A.8)). -/
lemma inner_coupling (p : Params n) (T h : ZMod n → ℝ) (b : ν → ℝ) (G : Matrix (ZMod n) ν ℝ) :
    ⟪vecMulVec (coupling p T h) b, G⟫ =
      -(p.c * ∑ i, dMinus p.Δx (G *ᵥ b) i * macroVar p T h i) := by
  have h1 := sum_mul_dMinus p.Δx (macroVar p T h) (G *ᵥ b)
  have h2 : ∑ i, dMinus p.Δx (G *ᵥ b) i * macroVar p T h i =
      ∑ i, macroVar p T h i * dMinus p.Δx (G *ᵥ b) i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [inner_vecMulVec, h2, h1, mul_neg, neg_neg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coupling_eq, mul_assoc]

lemma inner_sub_self_eq (x y : Matrix (ZMod n) ν ℝ) :
    ⟪x - y, x⟫ = 1 / 2 * (‖x‖ ^ 2 - ‖y‖ ^ 2 + ‖x - y‖ ^ 2) := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
  ring

lemma le_inner_diagonal (p : Params n) (G : Matrix (ZMod n) ν ℝ) :
    p.σ₀ * ‖G‖ ^ 2 ≤ ⟪diagonal p.σf * G, G⟫ := by
  rw [Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  simp only [Frobenius.inner_def, Matrix.diagonal_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  nlinarith [p.σf_ge i, sq_nonneg (G i k)]

lemma young_one (x y d : ℝ) : -(d * (x * y)) ≤ y ^ 2 + d ^ 2 / 4 * x ^ 2 := by
  nlinarith [sq_nonneg (y + d / 2 * x)]

lemma young_two (r d x y : ℝ) : r * d * (x * y) ≤ r ^ 2 / 2 * x ^ 2 + d ^ 2 / 2 * y ^ 2 := by
  nlinarith [sq_nonneg (r * x - d * y)]

/-- **The energy estimate** behind arXiv 2402.16746, Theorems 2, 4 and 7, for a single step, on the
periodic grid and with the bound `4 c Δt μ_k² ≤ 2 ε Δx |μ_k| + σ₀ Δx²`.  This is the argument of
Appendix A of the paper, eqs. (A.4)–(A.11), with `g_{new}` split in two: the micro iterate `gh`
that is tested in the micro equation `hgal`, and the iterate `g1` that enters the macro equations.
The argument only needs that `g1` has the moment `gh *ᵥ b` and norm at most `‖gh‖`. -/
theorem energy_le_core (p : Params n) {T : Matrix ν η ℝ} (hT : T * Tᵀ = 1) (μ t : η → ℝ)
    (ht : ∑ k, t k ^ 2 = 1) {b : ν → ℝ} (hb : ∀ j, b j = √2 * ∑ k, t k * μ k * T j k)
    (hCFL : ∀ k, 4 * p.c * p.Δt * μ k ^ 2 ≤ 2 * p.ε * p.Δx * |μ k| + p.σ₀ * p.Δx ^ 2)
    {Tn hn Tn1 hn1 : ZMod n → ℝ} {g gh g1 : Matrix (ZMod n) ν ℝ}
    (hgal : p.ε ^ 2 / p.c * (1 / p.Δt) * ⟪gh - g, gh⟫ +
      p.ε * ⟪flux p.Δx (Apos T μ) (Aneg T μ) g, gh⟫ + ⟪vecMulVec (coupling p Tn hn) b, gh⟫ +
        ⟪diagonal p.σf * gh, gh⟫ = 0)
    (hmoment : g1 *ᵥ b = gh *ᵥ b) (hnorm : ‖g1‖ ≤ ‖gh‖)
    (hmacro : ∀ i, p.ε ^ 2 / p.c * ((hn1 i - hn i) / p.Δt) + p.a * p.κ * p.σ i * hn1 i +
      1 / 2 * dMinus p.Δx (g1 *ᵥ b) i = -p.σ i * hn1 i)
    (htemp : ∀ i, (Tn1 i - Tn i) / p.Δt = p.κ * p.σ i * hn1 i) :
    energy p Tn1 hn1 g1 ≤ energy p Tn hn g := by
  have hc := p.c_pos
  have hε := p.ε_pos
  have hΔt := p.Δt_pos
  have hΔx := p.Δx_pos
  have hσ₀ := p.σ₀_pos
  have ha := p.a_pos
  have hcν := p.cν_pos
  rw [hmoment] at hmacro
  set A := Apos T μ with hA
  set B := Aneg T μ with hB
  set q := gh *ᵥ b with hq
  set w := fluxAdj p.Δx A B gh with hw
  set v := gh * T with hv
  set P1 := macroVar p Tn1 hn1 with hP1
  set P0 := macroVar p Tn hn with hP0
  set Eg := p.ε ^ 2 / (2 * p.c ^ 2) with hEg
  set α := p.Δt / p.c with hα
  set β := p.ε * p.Δt / p.c with hβ
  set Z := ∑ k, μ k ^ 2 * Zk p.Δx v k with hZ
  set Zabs := ∑ k, |μ k| * Zk p.Δx v k with hZabs
  set Z0 := ∑ k, Zk p.Δx v k with hZ0
  set Sh := ∑ i, p.σ i * hn1 i ^ 2 with hSh
  set Sq := ∑ i, dMinus p.Δx q i ^ 2 with hSq
  have hEg0 : 0 ≤ Eg := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  -- The macroscopic identity.
  have hI := macro_identity p hmacro htemp
  -- The micro equation tested with `gh`.
  have hII : Eg * (‖gh‖ ^ 2 - ‖g‖ ^ 2 + ‖gh - g‖ ^ 2) + β * ⟪flux p.Δx A B g, gh⟫ -
      p.Δt * ∑ i, dMinus p.Δx q i * P0 i + α * ⟪diagonal p.σf * gh, gh⟫ = 0 := by
    have e := hgal
    rw [inner_coupling, inner_sub_self_eq] at e
    have e' : Eg * (‖gh‖ ^ 2 - ‖g‖ ^ 2 + ‖gh - g‖ ^ 2) + β * ⟪flux p.Δx A B g, gh⟫ -
        p.Δt * ∑ i, dMinus p.Δx q i * P0 i + α * ⟪diagonal p.σf * gh, gh⟫ =
        α * (p.ε ^ 2 / p.c * (1 / p.Δt) * (1 / 2 * (‖gh‖ ^ 2 - ‖g‖ ^ 2 + ‖gh - g‖ ^ 2)) +
          p.ε * ⟪flux p.Δx A B g, gh⟫ + -(p.c * ∑ i, dMinus p.Δx q i * P0 i) +
            ⟪diagonal p.σf * gh, gh⟫) := by
      simp only [hEg, hα, hβ]
      field_simp
      ring
    rw [e', e, mul_zero]
  -- The flux term.
  have hsplit := inner_flux_split p.Δx (Apos_transpose T μ) (Aneg_transpose T μ) g gh
  have hL0 : ⟪flux p.Δx A B gh, gh⟫ = p.Δx / 2 * Zabs := inner_flux_self hΔx.ne' T μ gh
  -- Young's inequality for the macroscopic cross term.
  have hY1 : -(p.Δt * ∑ i, dMinus p.Δx q i * (P1 i - P0 i)) ≤
      ∑ i, (P1 i - P0 i) ^ 2 + p.Δt ^ 2 / 4 * Sq := by
    rw [hSq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => young_one _ _ _
  have hsum : ∑ i, dMinus p.Δx q i * (P1 i - P0 i) =
      ∑ i, dMinus p.Δx q i * P1 i - ∑ i, dMinus p.Δx q i * P0 i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- Young's inequality for the transport cross term.
  have hY2 : -(β * ⟪gh - g, w⟫) ≤ Eg * ‖gh - g‖ ^ 2 + p.Δt ^ 2 / 2 * ‖w‖ ^ 2 := by
    have h1 : -⟪gh - g, w⟫ ≤ ‖gh - g‖ * ‖w‖ := by
      have := abs_real_inner_le_norm (gh - g) w
      linarith [neg_abs_le ⟪gh - g, w⟫]
    have h2 : β * (‖gh - g‖ * ‖w‖) ≤ Eg * ‖gh - g‖ ^ 2 + p.Δt ^ 2 / 2 * ‖w‖ ^ 2 := by
      have e1 : β = p.ε / p.c * p.Δt := by
        simp only [hβ]
        ring
      have e2 : Eg = (p.ε / p.c) ^ 2 / 2 := by
        simp only [hEg]
        field_simp
      rw [e1, e2]
      exact young_two _ _ _ _
    have h3 := mul_le_mul_of_nonneg_left h1 hβ0
    rw [mul_neg] at h3
    linarith
  -- Lemmas 3, 4, 5 and 6.
  have hSqZ : Sq ≤ 2 * Z := sum_dMinus_moment_sq_le T p.Δx μ t ht hb gh
  have hwZ : ‖w‖ ^ 2 ≤ Z := norm_fluxAdj_sq_le hT p.Δx μ gh
  have hZ0G : p.Δx ^ 2 / 4 * Z0 ≤ ‖gh‖ ^ 2 := by
    have h := sum_Zk_le hT p.Δx gh
    have e : ‖gh‖ ^ 2 = p.Δx ^ 2 / 4 * (4 / p.Δx ^ 2 * ‖gh‖ ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hσG := le_inner_diagonal p gh
  -- The CFL condition, summed over the nodes.
  have hcfl : 4 * p.c * p.Δt * Z ≤ 2 * p.ε * p.Δx * Zabs + p.σ₀ * p.Δx ^ 2 * Z0 := by
    simp only [hZ, hZabs, hZ0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := mul_le_mul_of_nonneg_right (hCFL k) (Zk_nonneg p.Δx v k)
    linarith
  have hfinal : p.Δt ^ 2 * Z - β * (p.Δx / 2 * Zabs) - α * (p.σ₀ * (p.Δx ^ 2 / 4 * Z0)) ≤ 0 := by
    have e : p.Δt ^ 2 * Z - β * (p.Δx / 2 * Zabs) - α * (p.σ₀ * (p.Δx ^ 2 / 4 * Z0)) =
        α / 4 * (4 * p.c * p.Δt * Z - (2 * p.ε * p.Δx * Zabs + p.σ₀ * p.Δx ^ 2 * Z0)) := by
      simp only [hα, hβ]
      field_simp
      ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hS1 : p.Δt ^ 2 / 4 * Sq ≤ p.Δt ^ 2 / 2 * Z := by
    have := mul_le_mul_of_nonneg_left hSqZ (by positivity : 0 ≤ p.Δt ^ 2 / 4)
    linarith
  have hS2 : p.Δt ^ 2 / 2 * ‖w‖ ^ 2 ≤ p.Δt ^ 2 / 2 * Z :=
    mul_le_mul_of_nonneg_left hwZ (by positivity)
  have hS3 : α * (p.σ₀ * (p.Δx ^ 2 / 4 * Z0)) ≤ α * ⟪diagonal p.σf * gh, gh⟫ :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hZ0G hσ₀.le).trans hσG) hα0
  have hSh0 : 0 ≤ Sh := Finset.sum_nonneg fun i _ => by
    have := p.σ_ge i
    have : 0 ≤ p.σ i := by linarith
    positivity
  have hSh1 : 0 ≤ 2 * p.Δt * (p.ε ^ 2 / p.c) * Sh := by positivity
  have hTd : 0 ≤ p.a * p.cν / 2 * ∑ i, (Tn1 i - Tn i) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hL : β * ⟪flux p.Δx A B g, gh⟫ = β * (p.Δx / 2 * Zabs) + β * ⟪gh - g, w⟫ := by
    rw [hsplit, hL0]
    ring
  have hg1 : Eg * ‖g1‖ ^ 2 ≤ Eg * ‖gh‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hEg0
  rw [energy_eq, energy_eq]
  refine mul_le_mul_of_nonneg_left ?_ hΔx.le
  rw [hsum] at hY1
  have hI' : (∑ i, P1 i ^ 2 - ∑ i, P0 i ^ 2 + ∑ i, (P1 i - P0 i) ^ 2) +
      p.a * p.cν / 2 * (∑ i, Tn1 i ^ 2 - ∑ i, Tn i ^ 2 + ∑ i, (Tn1 i - Tn i) ^ 2) +
        p.Δt * ∑ i, dMinus p.Δx q i * P1 i = -(2 * p.Δt * (p.ε ^ 2 / p.c) * Sh) := hI
  linarith

end Energy

/-! ### The asymptotic-preserving augmented BUG step -/

section Step

variable {n : ℕ} [NeZero n] {ν α β ξ ϖ ω ρ ρq τ θ ρ₁ : Type*}
  [Fintype ν] [Fintype α] [Fintype β] [Fintype ξ] [Fintype ϖ] [Fintype ω] [Fintype ρ] [Fintype ρq]
  [Fintype τ] [Fintype θ] [Fintype ρ₁]
  [DecidableEq ν] [DecidableEq α] [DecidableEq β] [DecidableEq ξ] [DecidableEq ϖ] [DecidableEq ω]
  [DecidableEq ρ] [DecidableEq ρq] [DecidableEq τ] [DecidableEq θ] [DecidableEq ρ₁]

/-- The direction `(σᵃ)⁻¹ δ⁰(a c T)` (`Ψ = 1`) added to the spatial basis in Section 4.2 of
arXiv 2402.16746. -/
noncomputable def apFlux (p : Params n) (T : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  (p.σf i)⁻¹ * dPlus p.Δx (fun j => p.a * p.c * T j) i

variable (ξ ρ ρq τ) in
/-- **One step of the asymptotic-preserving augmented BUG scheme** of arXiv 2402.16746, Section 4.2,
for the linearised problem (`B(T) = a c T`, so `Ψ = 1`), from `(Tⁿ, hⁿ, Xⁿ Sⁿ Vⁿᵀ)` to
`(Tⁿ⁺¹, hⁿ⁺¹, Xⁿ⁺¹ Sⁿ⁺¹ Vⁿ⁺¹ᵀ)`, all equations being the paper's.

* Step 1: the K-step (4.2) and L-step (4.3) and the augmented bases: `X̂` has orthonormal columns
  and captures `(σᵃ)⁻¹ δ⁰(a c T)`, `K(t_{n+1})`, `Xⁿ`; `V̂ = [V̂ᵃᵖ, V̂ʳᵉᵐ]` has orthonormal columns
  and captures `L(t_{n+1})`, `Vⁿ`, and `b` lies in the range of `V̂ᵃᵖ`.
* Step 2: the S-step (4.23) from `S̃ = X̂ᵀ Xⁿ Sⁿ Vⁿᵀ V̂`.
* Step 3: `X̂ Ŝ = [K̂ᵃᵖ, K̂ʳᵉᵐ]`, `K̂ʳᵉᵐ = X̂ʳᵉᵐ Ŝʳᵉᵐ` (QR), `Ŝʳᵉᵐ = U Σ Wᵀ` (SVD), a selection
  `keep` of singular triples giving `Û`, `Ŵ`, `Σ̂`; `K̂ᵃᵖ = Xᵃᵖ Sᵃᵖ` (QR),
  `Xⁿ⁺¹ R₂ = [Xᵃᵖ, X̂ʳᵉᵐ Û]` (QR), `Sⁿ⁺¹ = R₂ diag(Sᵃᵖ, Σ̂)` (4.19), and `Vⁿ⁺¹ = [V̂ᵃᵖ, V̂ʳᵉᵐ Ŵ]`.
* Step 4: the updates (4.20), (4.21) of `h` and `T`. In (4.20) the term `(γ₁/2) 𝒟⁰ g₁` is written
  `½ 𝒟⁰ (g b)`, which is the same for `b = (γ₁, 0, …, 0)ᵀ`.

Differences from the paper. The paper has one protected column (`ω = Unit`; `b` is one vector), and
the index types are `2 r + 1`, `2 r`, `r*`, `r* + 1`; general index types are allowed here, which
also covers rank-deficient QR factorisations, and every selection of singular values is allowed, so
the tolerance `ϑ` of the truncation plays no role. The paper writes
`K̂ᵃᵖ = [(σᵃ)⁻¹ Ψⁿ δ⁰(a c Tⁿ)]`. That cannot be meant literally for `ε > 0`: `K̂ᵃᵖ` is defined by
`K̂ = X̂ Ŝ = [K̂ᵃᵖ K̂ʳᵉᵐ]`, the proof of Theorem 6 uses this equation, and the proof of Theorem 7
needs it. So `K̂ᵃᵖ` is the block of columns of `X̂ Ŝ` belonging to `V̂ᵃᵖ` here, which is a
multiple of `(σᵃ)⁻¹ δ⁰(a c Tⁿ)` only in the limit `ε → 0`, by (4.22). The display
`S̃ⁿ = M̂ᵀ Sⁿ N̂ᵀ` of the paper has incompatible sizes and is read as `M̂ Sⁿ N̂ᵀ`. -/
structure APBUGStep (p : Params n) (Ap Am : Matrix ν ν ℝ) (b : ν → ℝ)
    (Tn hn : ZMod n → ℝ) (X : Matrix (ZMod n) α ℝ) (S : Matrix α β ℝ) (V : Matrix ν β ℝ)
    (Tn1 hn1 : ZMod n → ℝ) (X1 : Matrix (ZMod n) ρ₁ ℝ) (S1 : Matrix ρ₁ (ω ⊕ θ) ℝ)
    (V1 : Matrix ν (ω ⊕ θ) ℝ) where
  X_orth : Xᵀ * X = 1
  V_orth : Vᵀ * V = 1
  /-- `K(t_{n+1})`. -/
  K1 : Matrix (ZMod n) β ℝ
  /-- The K-step (4.2). -/
  kStep : (p.ε ^ 2 / p.c) • ((1 / p.Δt) • (K1 - X * S)) =
    -(p.ε • (DM p.Δx (X * S) * (Vᵀ * Ap * V) + DP p.Δx (X * S) * (Vᵀ * Am * V))) -
      vecMulVec (coupling p Tn hn) (Vᵀ *ᵥ b) - diagonal p.σf * K1
  /-- `L(t_{n+1})`. -/
  L1 : Matrix ν α ℝ
  /-- The L-step (4.3). -/
  lStep : (p.ε ^ 2 / p.c) • ((1 / p.Δt) • (L1 - V * Sᵀ)) =
    -(p.ε • (Ap * (V * Sᵀ) * ((DM p.Δx X)ᵀ * X) + Am * (V * Sᵀ) * ((DP p.Δx X)ᵀ * X))) -
      vecMulVec b (Xᵀ *ᵥ coupling p Tn hn) - L1 * (Xᵀ * diagonal p.σf * X)
  /-- `X̂ⁿ⁺¹`. -/
  Xh : Matrix (ZMod n) ξ ℝ
  Xh_orth : Xhᵀ * Xh = 1
  Xh_ap : (Xh * Xhᵀ) *ᵥ apFlux p Tn = apFlux p Tn
  Xh_K : Xh * Xhᵀ * K1 = K1
  Xh_X : Xh * Xhᵀ * X = X
  /-- `V̂ᵃᵖ`. -/
  Vap : Matrix ν ω ℝ
  /-- `V̂ʳᵉᵐ`. -/
  Vrem : Matrix ν ρ ℝ
  /-- `V̂ⁿ⁺¹`. -/
  Vh : Matrix ν (ω ⊕ ρ) ℝ
  Vh_eq : Vh = fromCols Vap Vrem
  Vh_orth : Vhᵀ * Vh = 1
  Vh_b : ∃ s, b = Vap *ᵥ s
  Vh_L : Vh * Vhᵀ * L1 = L1
  Vh_V : Vh * Vhᵀ * V = V
  /-- `S̃ⁿ`. -/
  Stilde : Matrix ξ (ω ⊕ ρ) ℝ
  Stilde_eq : Stilde = Xhᵀ * X * S * Vᵀ * Vh
  /-- `Ŝⁿ⁺¹`. -/
  Sh : Matrix ξ (ω ⊕ ρ) ℝ
  /-- The S-step (4.23). -/
  sStep : (p.ε ^ 2 / p.c) • ((1 / p.Δt) • (Sh - Stilde)) =
    -(p.ε • (Xhᵀ * DM p.Δx Xh * Stilde * (Vhᵀ * Ap * Vh) +
        Xhᵀ * DP p.Δx Xh * Stilde * (Vhᵀ * Am * Vh))) -
      vecMulVec (Xhᵀ *ᵥ coupling p Tn hn) (Vhᵀ *ᵥ b) - Xhᵀ * diagonal p.σf * Xh * Sh
  /-- `K̂ᵃᵖ`. -/
  Kap : Matrix (ZMod n) ω ℝ
  /-- `K̂ʳᵉᵐ`. -/
  Krem : Matrix (ZMod n) ρ ℝ
  split : Xh * Sh = fromCols Kap Krem
  /-- `X̂ʳᵉᵐ`. -/
  Xrem : Matrix (ZMod n) ρq ℝ
  /-- `Ŝʳᵉᵐ`. -/
  Srem : Matrix ρq ρ ℝ
  Xrem_orth : Xremᵀ * Xrem = 1
  qr_rem : Krem = Xrem * Srem
  /-- The left singular vectors of `Ŝʳᵉᵐ`. -/
  U : Matrix ρq τ ℝ
  /-- The right singular vectors of `Ŝʳᵉᵐ`. -/
  W : Matrix ρ τ ℝ
  /-- The singular values of `Ŝʳᵉᵐ`. -/
  s : τ → ℝ
  U_orth : Uᵀ * U = 1
  W_orth : Wᵀ * W = 1
  svd : Srem = U * diagonal s * Wᵀ
  /-- The selection of the singular triples that are kept. -/
  keep : θ → τ
  keep_inj : Function.Injective keep
  /-- `Xᵃᵖ`. -/
  Xap : Matrix (ZMod n) ω ℝ
  /-- `Sᵃᵖ`. -/
  Sap : Matrix ω ω ℝ
  Xap_orth : Xapᵀ * Xap = 1
  qr_ap : Kap = Xap * Sap
  /-- `R₂`. -/
  R2 : Matrix ρ₁ (ω ⊕ θ) ℝ
  X1_orth : X1ᵀ * X1 = 1
  qr_new : X1 * R2 = fromCols Xap (Xrem * U.submatrix id keep)
  S1_eq : S1 = R2 * fromBlocks Sap 0 0 (diagonal (s ∘ keep))
  V1_eq : V1 = fromCols Vap (Vrem * W.submatrix id keep)
  /-- The update (4.20) of `h`. -/
  hStep : ∀ i, p.ε ^ 2 / p.c * ((hn1 i - hn i) / p.Δt) + p.a * p.κ * p.σ i * hn1 i +
    1 / 2 * dMinus p.Δx ((X1 * S1 * V1ᵀ) *ᵥ b) i = -p.σ i * hn1 i
  /-- The update (4.21) of `T`. -/
  TStep : ∀ i, (Tn1 i - Tn i) / p.Δt = p.κ * p.σ i * hn1 i

/-- A Galerkin step tested with its result: the argument (4.12)–(4.13) of arXiv 2402.16746. -/
lemma galerkin_test (p : Params n) {Ap Am : Matrix ν ν ℝ} {Xh : Matrix (ZMod n) ξ ℝ}
    {Vh : Matrix ν ϖ ℝ} (hX : Xhᵀ * Xh = 1) (hV : Vhᵀ * Vh = 1) {St Sh : Matrix ξ ϖ ℝ}
    {d : ZMod n → ℝ} {b : ν → ℝ}
    (hS : (p.ε ^ 2 / p.c) • ((1 / p.Δt) • (Sh - St)) =
      -(p.ε • (Xhᵀ * DM p.Δx Xh * St * (Vhᵀ * Ap * Vh) +
          Xhᵀ * DP p.Δx Xh * St * (Vhᵀ * Am * Vh))) -
        vecMulVec (Xhᵀ *ᵥ d) (Vhᵀ *ᵥ b) - Xhᵀ * diagonal p.σf * Xh * Sh) :
    p.ε ^ 2 / p.c * (1 / p.Δt) * ⟪Xh * Sh * Vhᵀ - Xh * St * Vhᵀ, Xh * Sh * Vhᵀ⟫ +
      p.ε * ⟪flux p.Δx Ap Am (Xh * St * Vhᵀ), Xh * Sh * Vhᵀ⟫ +
        ⟪vecMulVec d b, Xh * Sh * Vhᵀ⟫ + ⟪diagonal p.σf * (Xh * Sh * Vhᵀ), Xh * Sh * Vhᵀ⟫ = 0 := by
  have key1 : ∀ M : Matrix ξ ϖ ℝ, ⟪Xh * M * Vhᵀ, Xh * Sh * Vhᵀ⟫ = ⟪M, Sh⟫ := fun M => by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose, Matrix.mul_assoc (Xh * Sh), hV,
      Matrix.mul_one, Frobenius.inner_mul_mul_of_orthonormal hX]
  have key2 : ∀ G : Matrix (ZMod n) ν ℝ, ⟪Xhᵀ * G * Vh, Sh⟫ = ⟪G, Xh * Sh * Vhᵀ⟫ := fun G => by
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose,
      Matrix.mul_assoc Xh]
  have e1 : Xhᵀ * flux p.Δx Ap Am (Xh * St * Vhᵀ) * Vh =
      Xhᵀ * DM p.Δx Xh * St * (Vhᵀ * Ap * Vh) + Xhᵀ * DP p.Δx Xh * St * (Vhᵀ * Am * Vh) := by
    simp only [flux, DM_mul, DP_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : Xhᵀ * vecMulVec d b * Vh = vecMulVec (Xhᵀ *ᵥ d) (Vhᵀ *ᵥ b) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose,
      Matrix.mulVec_transpose]
  have e3 : Xhᵀ * (diagonal p.σf * (Xh * Sh * Vhᵀ)) * Vh = Xhᵀ * diagonal p.σf * Xh * Sh := by
    calc Xhᵀ * (diagonal p.σf * (Xh * Sh * Vhᵀ)) * Vh
        = Xhᵀ * diagonal p.σf * Xh * Sh * (Vhᵀ * Vh) := by simp only [Matrix.mul_assoc]
      _ = Xhᵀ * diagonal p.σf * Xh * Sh := by rw [hV, Matrix.mul_one]
  rw [← e1, ← e2, ← e3] at hS
  have h := congrArg (fun M => ⟪M, Sh⟫) hS
  simp only [real_inner_smul_left, inner_sub_left, inner_neg_left, key2] at h
  rw [inner_sub_left, key1 Sh, key1 St]
  linear_combination h

lemma orth_submatrix {m : Type*} [Fintype m] {U : Matrix m τ ℝ} (hU : Uᵀ * U = 1) {keep : θ → τ}
    (hk : Function.Injective keep) : (U.submatrix id keep)ᵀ * U.submatrix id keep = 1 := by
  ext i j
  have h := congrFun (congrFun hU (keep i)) (keep j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hk.eq_iff] at h
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

lemma norm_diagonal_sq (d : τ → ℝ) : ‖(diagonal d : Matrix τ τ ℝ)‖ ^ 2 = ∑ i, d i ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp

lemma sum_comp_le {keep : θ → τ} (hk : Function.Injective keep) (f : τ → ℝ)
    (hf : ∀ i, 0 ≤ f i) : ∑ k, f (keep k) ≤ ∑ i, f i := by
  have e : ∑ k, f (keep k) = ∑ i ∈ Finset.univ.image keep, f i :=
    (Finset.sum_image fun _ _ _ _ h => hk h).symm
  rw [e]
  exact Finset.sum_le_univ_sum_of_nonneg hf

/-- Pythagoras for the splitting along an orthonormal block `Va`. -/
lemma pyth_aux {Va : Matrix ν ω ℝ} (hVa : Vaᵀ * Va = 1) (K : Matrix (ZMod n) ω ℝ)
    (Y : Matrix (ZMod n) θ ℝ) (Z : Matrix ν θ ℝ) (hZ : Vaᵀ * Z = 0) :
    ‖K * Vaᵀ + Y * Zᵀ‖ ^ 2 = ‖K‖ ^ 2 + ‖Y * Zᵀ‖ ^ 2 := by
  have h0 : ⟪K * Vaᵀ, Y * Zᵀ⟫ = 0 := by
    rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, Matrix.mul_assoc, hZ,
      Matrix.mul_zero, inner_zero_left]
  rw [norm_add_sq_real, h0, Frobenius.norm_mul_transpose_of_orthonormal hVa]
  ring

namespace APBUGStep

variable {p : Params n} {Ap Am : Matrix ν ν ℝ} {b : ν → ℝ} {Tn hn : ZMod n → ℝ}
  {X : Matrix (ZMod n) α ℝ} {S : Matrix α β ℝ} {V : Matrix ν β ℝ} {Tn1 hn1 : ZMod n → ℝ}
  {X1 : Matrix (ZMod n) ρ₁ ℝ} {S1 : Matrix ρ₁ (ω ⊕ θ) ℝ} {V1 : Matrix ν (ω ⊕ θ) ℝ}

/-- The orthonormality of `V̂ = [V̂ᵃᵖ, V̂ʳᵉᵐ]`, block by block. -/
lemma blocks (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    st.Vapᵀ * st.Vap = 1 ∧ st.Vapᵀ * st.Vrem = 0 ∧ st.Vremᵀ * st.Vap = 0 ∧
      st.Vremᵀ * st.Vrem = 1 := by
  have h := st.Vh_orth
  rw [st.Vh_eq, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
    at h
  simpa using Matrix.fromBlocks_inj.1 h

/-- The Galerkin initial value is `gⁿ`, since the augmented bases contain the old ones: the
identity `X̂ S̃ V̂ᵀ = Xⁿ Sⁿ Vⁿᵀ` in the proof of Theorem 7 of arXiv 2402.16746. -/
lemma initial_eq (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    st.Xh * st.Stilde * st.Vhᵀ = X * S * Vᵀ := by
  have hV : Vᵀ * (st.Vh * st.Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose st.Vh_V
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc st.Xh * st.Stilde * st.Vhᵀ
      = st.Xh * st.Xhᵀ * X * S * (Vᵀ * (st.Vh * st.Vhᵀ)) := by
        simp only [st.Stilde_eq, Matrix.mul_assoc]
    _ = X * S * Vᵀ := by rw [st.Xh_X, hV]

/-- The solution before truncation, split along `V̂ = [V̂ᵃᵖ, V̂ʳᵉᵐ]`. -/
lemma hat_eq (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    st.Xh * st.Sh * st.Vhᵀ = st.Kap * st.Vapᵀ + st.Krem * st.Vremᵀ := by
  rw [st.split, st.Vh_eq, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

/-- The solution after truncation, split along `Vⁿ⁺¹`; the protected block is unchanged. -/
lemma new_eq (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    X1 * S1 * V1ᵀ = st.Kap * st.Vapᵀ +
      st.Xrem * st.U.submatrix id st.keep * diagonal (st.s ∘ st.keep) *
        (st.Vrem * st.W.submatrix id st.keep)ᵀ := by
  have h : X1 * S1 * V1ᵀ = X1 * (st.R2 * fromBlocks st.Sap 0 0 (diagonal (st.s ∘ st.keep))) *
      (fromCols st.Vap (st.Vrem * st.W.submatrix id st.keep))ᵀ :=
    congrArg₂ (fun A D => X1 * A * Dᵀ) st.S1_eq st.V1_eq
  rw [h, ← Matrix.mul_assoc X1, st.qr_new, Matrix.fromCols_mul_fromBlocks,
    Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, st.qr_ap]
  simp

/-- The truncation keeps the moment `g b`, which is the moment entering the macro update. -/
lemma moment_eq (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    (X1 * S1 * V1ᵀ) *ᵥ b = (st.Xh * st.Sh * st.Vhᵀ) *ᵥ b := by
  obtain ⟨c, hc⟩ := st.Vh_b
  obtain ⟨-, -, h3, -⟩ := st.blocks
  have key : ∀ M : Matrix (ZMod n) ν ℝ, M *ᵥ b = M *ᵥ (st.Vap *ᵥ c) := fun M => congrArg _ hc
  have h4 : (st.Vrem * st.W.submatrix id st.keep)ᵀ * st.Vap = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [key, key, st.new_eq, st.hat_eq, Matrix.add_mulVec, Matrix.add_mulVec]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ st.Vap,
    Matrix.mul_assoc st.Krem, h4, h3]
  simp

/-- **The truncation does not increase the norm**, `‖Xⁿ⁺¹ Sⁿ⁺¹ Vⁿ⁺¹ᵀ‖ ≤ ‖X̂ Ŝ V̂ᵀ‖` (proof of
Theorem 7 of arXiv 2402.16746). -/
lemma norm_new_le (st : APBUGStep ξ ρ ρq τ p Ap Am b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    ‖X1 * S1 * V1ᵀ‖ ≤ ‖st.Xh * st.Sh * st.Vhᵀ‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := st.blocks
  set Uh := st.U.submatrix id st.keep with hUh
  set Wh := st.W.submatrix id st.keep with hWh
  set Vw := st.Vrem * Wh with hVw
  set Xr := st.Xrem * Uh with hXr
  set D : Matrix θ θ ℝ := diagonal (st.s ∘ st.keep) with hD
  have hU : Uhᵀ * Uh = 1 := orth_submatrix st.U_orth st.keep_inj
  have hW : Whᵀ * Wh = 1 := orth_submatrix st.W_orth st.keep_inj
  have hVwo : Vwᵀ * Vw = 1 := by
    rw [hVw, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc st.Vremᵀ, h4,
      Matrix.one_mul, hW]
  have hXro : Xrᵀ * Xr = 1 := by
    rw [hXr, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc st.Xremᵀ, st.Xrem_orth,
      Matrix.one_mul, hU]
  have hVaw : st.Vapᵀ * Vw = 0 := by
    rw [hVw, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have hnew : ‖X1 * S1 * V1ᵀ‖ ^ 2 = ‖st.Kap‖ ^ 2 + ‖D‖ ^ 2 := by
    rw [st.new_eq, ← hUh, ← hWh, pyth_aux h1 _ _ _ hVaw,
      Frobenius.norm_mul_transpose_of_orthonormal hVwo,
      Frobenius.norm_mul_of_orthonormal hXro]
  have hhat : ‖st.Xh * st.Sh * st.Vhᵀ‖ ^ 2 = ‖st.Kap‖ ^ 2 + ‖diagonal st.s‖ ^ 2 := by
    have e : ‖st.Krem‖ = ‖(diagonal st.s : Matrix τ τ ℝ)‖ := by
      rw [st.qr_rem, Frobenius.norm_mul_of_orthonormal st.Xrem_orth, st.svd,
        Frobenius.norm_mul_transpose_of_orthonormal st.W_orth,
        Frobenius.norm_mul_of_orthonormal st.U_orth]
    rw [st.hat_eq, pyth_aux h1 _ _ _ h2, Frobenius.norm_mul_transpose_of_orthonormal h4, e]
  have hle : ‖D‖ ^ 2 ≤ ‖(diagonal st.s : Matrix τ τ ℝ)‖ ^ 2 := by
    rw [hD, norm_diagonal_sq, norm_diagonal_sq]
    exact sum_comp_le st.keep_inj (fun i => st.s i ^ 2) fun _ => sq_nonneg _
  have : ‖X1 * S1 * V1ᵀ‖ ^ 2 ≤ ‖st.Xh * st.Sh * st.Vhᵀ‖ ^ 2 := by
    rw [hnew, hhat]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

end APBUGStep

/-- **Energy stability of one AP augmented BUG step, sharp form** (arXiv 2402.16746, Theorem 7, for
the bound `4 c Δt μ_k² ≤ 2 ε Δx |μ_k| + σ₀ Δx²`), for any `T` with orthonormal rows, any nodes `μ`
and `b_j = √2 ∑_k t_k μ_k T_{jk}` with `∑ t_k² = 1`. -/
theorem energy_le_of_step (p : Params n) {T : Matrix ν ϖ ℝ} (hT : T * Tᵀ = 1) (μ t : ϖ → ℝ)
    (ht : ∑ k, t k ^ 2 = 1) {b : ν → ℝ} (hb : ∀ j, b j = √2 * ∑ k, t k * μ k * T j k)
    (hCFL : ∀ k, 4 * p.c * p.Δt * μ k ^ 2 ≤ 2 * p.ε * p.Δx * |μ k| + p.σ₀ * p.Δx ^ 2)
    {Tn hn Tn1 hn1 : ZMod n → ℝ} {X : Matrix (ZMod n) α ℝ} {S : Matrix α β ℝ} {V : Matrix ν β ℝ}
    {X1 : Matrix (ZMod n) ρ₁ ℝ} {S1 : Matrix ρ₁ (ω ⊕ θ) ℝ} {V1 : Matrix ν (ω ⊕ θ) ℝ}
    (st : APBUGStep ξ ρ ρq τ p (Apos T μ) (Aneg T μ) b Tn hn X S V Tn1 hn1 X1 S1 V1) :
    energy p Tn1 hn1 (X1 * S1 * V1ᵀ) ≤ energy p Tn hn (X * S * Vᵀ) := by
  have hgal := galerkin_test p st.Xh_orth st.Vh_orth st.sStep
  rw [st.initial_eq] at hgal
  exact energy_le_core p hT μ t ht hb hCFL hgal st.moment_eq st.norm_new_le st.hStep st.TStep

end Step

/-! ### The `P_N` data: Legendre polynomials and Gauss–Legendre quadrature -/

section PN

/-- The entries `a_k = (k+1) / √((2k+1)(2k+3))` of the flux matrix of arXiv 2402.16746, Section
2.1.2. -/
noncomputable def pnCoeff (k : ℕ) : ℝ := ((k : ℝ) + 1) / √((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3))

lemma pnCoeff_pos (k : ℕ) : 0 < pnCoeff k := by
  unfold pnCoeff
  positivity

lemma pnCoeff_zero : pnCoeff 0 = 1 / √3 := by
  norm_num [pnCoeff]

/-- The normalized Legendre polynomials `P_k`, through their three-term recurrence
`x P_k = a_{k-1} P_{k-1} + a_k P_{k+1}`, `P_0 = 1/√2` (see `legendreN_one`, `legendreN_two`). -/
noncomputable def legendreN : ℕ → ℝ → ℝ
  | 0, _ => 1 / √2
  | 1, x => x * (1 / √2) / pnCoeff 0
  | k + 2, x => (x * legendreN (k + 1) x - pnCoeff k * legendreN k x) / pnCoeff (k + 1)

lemma legendreN_zero (x : ℝ) : legendreN 0 x = 1 / √2 := rfl

/-- `P_1(x) = √(3/2) x`. -/
lemma legendreN_one (x : ℝ) : legendreN 1 x = √(3 / 2) * x := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  rw [legendreN, pnCoeff_zero, Real.sqrt_div (by norm_num)]
  field_simp

/-- `P_2(x) = √(5/8) (3 x² - 1)`, which is `√(5/2)` times the Legendre polynomial of degree two. -/
lemma legendreN_two (x : ℝ) : legendreN 2 x = √(5 / 8) * (3 * x ^ 2 - 1) := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h15 : pnCoeff 1 = 2 / (√3 * √5) := by
    rw [pnCoeff, ← Real.sqrt_mul (by norm_num)]
    norm_num
  have h58 : √(5 / 8 : ℝ) = √5 / (2 * √2) := by
    rw [Real.sqrt_div (by norm_num), show (8 : ℝ) = 2 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [legendreN, legendreN_one, legendreN_zero, pnCoeff_zero, h15, h58,
    Real.sqrt_div (by norm_num)]
  have h2' : (√2 : ℝ) ≠ 0 := by positivity
  have h3' : (√3 : ℝ) ≠ 0 := by positivity
  have h5' : (√5 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [h2, h3, h5]

/-- The recurrence, row `0`. -/
lemma legendreN_rec_zero (x : ℝ) : pnCoeff 0 * legendreN 1 x = x * legendreN 0 x := by
  have := pnCoeff_pos 0
  have e : legendreN 1 x = x * (1 / √2) / pnCoeff 0 := rfl
  rw [e, legendreN_zero]
  field_simp

/-- The recurrence, row `k + 1`. -/
lemma legendreN_rec_succ (k : ℕ) (x : ℝ) :
    pnCoeff k * legendreN k x + pnCoeff (k + 1) * legendreN (k + 2) x =
      x * legendreN (k + 1) x := by
  have := pnCoeff_pos (k + 1)
  rw [legendreN]
  field_simp
  ring

/-- The matrix `A_f ∈ ℝ^{(N+1)×(N+1)}` of arXiv 2402.16746, Appendix A, tridiagonal with entries
`a_k`, in the indices `0, …, N`. The flux matrix `A` of Section 2.1.2 is the block with indices
`1, …, N`. -/
noncomputable def pnFlux (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 = j then pnCoeff i else if (j : ℕ) + 1 = i then pnCoeff j else 0

lemma pnFlux_transpose (N : ℕ) : (pnFlux N)ᵀ = pnFlux N := by
  ext i j
  simp only [pnFlux, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h1 : (j : ℕ) + 1 = i
  · have h2 : ¬ (i : ℕ) + 1 = j := by omega
    simp [h1, h2]
  · simp [h1]

/-- The action of the tridiagonal matrix `A_f`, row by row. -/
lemma pnFlux_mulVec_gen (N : ℕ) (f : ℕ → ℝ) (i : Fin (N + 1)) :
    (pnFlux N *ᵥ fun j : Fin (N + 1) => f j) i =
      (if (i : ℕ) < N then pnCoeff i * f (i + 1) else 0) +
        if (i : ℕ) = 0 then 0 else pnCoeff (i - 1) * f (i - 1) := by
  obtain ⟨m, hm⟩ := i
  have e : (pnFlux N *ᵥ fun j : Fin (N + 1) => f j) ⟨m, hm⟩ =
      ∑ j ∈ Finset.range (N + 1), (if m + 1 = j then pnCoeff m else
        if j + 1 = m then pnCoeff j else 0) * f j := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (if m + 1 = j then pnCoeff m else if j + 1 = m then pnCoeff j else 0) * f j)]
    simp [Matrix.mulVec, dotProduct, pnFlux]
  rw [e]
  cases m with
  | zero =>
    have hsplit : ∀ j ∈ Finset.range (N + 1),
        (if 0 + 1 = j then pnCoeff 0 else if j + 1 = 0 then pnCoeff j else 0) * f j =
          if j = 1 then pnCoeff 0 * f 1 else 0 := fun j _ => by
      by_cases h : j = 1
      · simp [h]
      · have h' : ¬ 0 + 1 = j := by omega
        simp [h, h']
    rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_eq']
    by_cases hN : 0 < N
    · have h1 : 1 ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
      simp [h1, hN]
    · have h1 : 1 ∉ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        omega
      simp [h1, hN]
  | succ m =>
    have hsplit : ∀ j ∈ Finset.range (N + 1),
        (if m + 1 + 1 = j then pnCoeff (m + 1) else
          if j + 1 = m + 1 then pnCoeff j else 0) * f j =
          (if j = m + 2 then pnCoeff (m + 1) * f (m + 2) else 0) +
            if j = m then pnCoeff m * f m else 0 := fun j _ => by
      by_cases h : j = m + 2
      · have h' : ¬ j = m := by omega
        simp [h]
      · by_cases h2 : j = m
        · have h5 : ¬ m + 1 + 1 = m := by omega
          simp [h2, h5]
        · have h3 : ¬ m + 1 + 1 = j := by omega
          simp [h, h2, h3]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have hmem : m ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    by_cases hN : m + 1 < N
    · have h1 : m + 2 ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
      simp [h1, hmem, hN]
    · have h1 : m + 2 ∉ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        omega
      simp [h1, hmem, hN]

/-- The value of the tridiagonal form on the vector of the `P_i(x)`. -/
lemma pnFlux_mulVec (N : ℕ) (x : ℝ) (i : Fin (N + 1)) :
    (pnFlux N *ᵥ fun j : Fin (N + 1) => legendreN j x) i =
      x * legendreN i x - if (i : ℕ) = N then pnCoeff N * legendreN (N + 1) x else 0 := by
  rw [pnFlux_mulVec_gen N (fun j => legendreN j x) i]
  obtain ⟨m, hm⟩ := i
  simp only
  cases m with
  | zero =>
    have := legendreN_rec_zero x
    by_cases hN : 0 < N
    · have h2 : ¬ 0 = N := by omega
      simp only [hN, ite_true, h2, ite_false, sub_zero]
      simp only [zero_add]
      linarith
    · have h2 : N = 0 := by omega
      subst h2
      simp only [lt_self_iff_false, ite_false, ite_true, zero_add]
      linarith
  | succ m =>
    have hrec := legendreN_rec_succ m x
    have h0 : ¬ m + 1 = 0 := by omega
    by_cases hN : m + 1 < N
    · have h2 : ¬ m + 1 = N := by omega
      simp only [hN, ite_true, h0, ite_false, h2, sub_zero, Nat.add_sub_cancel]
      linarith
    · have h2 : m + 1 = N := by omega
      subst h2
      simp only [lt_self_iff_false, ite_false, ite_true, h0, zero_add, Nat.add_sub_cancel]
      linarith

/-- Every eigenvector of `A_f` is a multiple of `(P_i(λ))_i`, and `P_{N+1}(λ) = 0` (the eigenvalues
of the Jacobi matrix are the Gauss nodes). -/
lemma eigen_structure (N : ℕ) {u : Fin (N + 1) → ℝ} {lam : ℝ} (h : pnFlux N *ᵥ u = lam • u) :
    (∀ i : Fin (N + 1), u i = √2 * u 0 * legendreN i lam) ∧
      (u ≠ 0 → legendreN (N + 1) lam = 0) := by
  set f : ℕ → ℝ := fun j => if hj : j < N + 1 then u ⟨j, hj⟩ else 0 with hf
  have hfj : ∀ j : Fin (N + 1), f j = u j := fun j => by
    simp only [hf, j.isLt, dite_true]
  have hfu : (fun j : Fin (N + 1) => f j) = u := funext hfj
  set c := √2 * u 0 with hc
  have hrow : ∀ m (hm : m < N + 1), (if m < N then pnCoeff m * f (m + 1) else 0) +
      (if m = 0 then 0 else pnCoeff (m - 1) * f (m - 1)) = lam * f m := fun m hm => by
    have h1 := congrFun h ⟨m, hm⟩
    rw [← hfu, pnFlux_mulVec_gen] at h1
    simpa using h1
  have hf0 : f 0 = c * legendreN 0 lam := by
    have h2 : (√2 : ℝ) ≠ 0 := by positivity
    have e : f 0 = u 0 := by simp [hf]
    rw [e, legendreN_zero, hc]
    field_simp
  have hclaim : ∀ m, (m ≤ N → f m = c * legendreN m lam) ∧
      (m + 1 ≤ N → f (m + 1) = c * legendreN (m + 1) lam) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => hf0, fun h1 => ?_⟩
      have hr := hrow 0 (by omega)
      have h0 : 0 < N := by omega
      simp only [h0, ite_true, add_zero, zero_add] at hr
      have hrec := legendreN_rec_zero lam
      have ha := (pnCoeff_pos 0).ne'
      apply mul_left_cancel₀ ha
      calc pnCoeff 0 * f 1 = lam * f 0 := hr
        _ = pnCoeff 0 * (c * legendreN 1 lam) := by
            rw [hf0]
            linear_combination (-c) * hrec
    | succ m ih =>
      refine ⟨ih.2, fun h1 => ?_⟩
      have hr := hrow (m + 1) (by omega)
      have h0 : m + 1 < N := by omega
      have h2 : ¬ m + 1 = 0 := by omega
      simp only [h0, ite_true, h2, ite_false, Nat.add_sub_cancel] at hr
      have hrec := legendreN_rec_succ m lam
      have ha := (pnCoeff_pos (m + 1)).ne'
      have e1 := ih.1 (by omega)
      have e2 := ih.2 (by omega)
      apply mul_left_cancel₀ ha
      rw [e1, e2] at hr
      linear_combination hr - c * hrec
  have hall : ∀ i : Fin (N + 1), u i = c * legendreN i lam := fun i => by
    rw [← hfj i]
    exact (hclaim i).1 (by omega)
  refine ⟨hall, fun hu => ?_⟩
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu
    ext i
    rw [hall, h0, zero_mul]
    rfl
  have hfN : f N = c * legendreN N lam := (hclaim N).1 le_rfl
  have hr := hrow N (by omega)
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp only [lt_self_iff_false, ite_false, ite_true, add_zero] at hr
    have hrec := legendreN_rec_zero lam
    have ha := (pnCoeff_pos 0).ne'
    rw [hfN] at hr
    have h3 : c * (pnCoeff 0 * legendreN 1 lam) = 0 := by
      rw [hrec]
      linear_combination -hr
    simpa [hc0, ha] using h3
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 : ¬ M + 1 = 0 := by omega
    simp only [lt_self_iff_false, ite_false, h2, zero_add, Nat.add_sub_cancel] at hr
    have hrec := legendreN_rec_succ M lam
    have ha := (pnCoeff_pos (M + 1)).ne'
    have e1 := (hclaim M).1 (by omega)
    rw [e1, hfN] at hr
    have h3 : c * (pnCoeff (M + 1) * legendreN (M + 2) lam) = 0 := by
      linear_combination c * hrec - hr
    simpa [hc0, ha] using h3

/-- **Gauss–Legendre nodes and weights** with `N + 1` points: the nodes `μ_k` are the `N + 1` roots
of `P_{N+1}` and the weights are the Christoffel numbers `w_k = (∑_{i ≤ N} P_i(μ_k)²)⁻¹`, the
classical formula for the Gauss weights in terms of orthonormal polynomials. -/
structure IsGaussLegendre (N : ℕ) (μ w : Fin (N + 1) → ℝ) : Prop where
  injective : Function.Injective μ
  root : ∀ k, legendreN (N + 1) (μ k) = 0
  weight : ∀ k, w k = (∑ i : Fin (N + 1), legendreN i (μ k) ^ 2)⁻¹

/-- The matrix `T_f = (√w_k P_i(μ_k))_{i,k = 0, …, N}` of arXiv 2402.16746, Appendix A. -/
noncomputable def gaussT {N : ℕ} (μ w : Fin (N + 1) → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i k => √(w k) * legendreN i (μ k)

/-- The matrix `T = (√w_k P_i(μ_k))_{i = 1, …, N, k = 0, …, N}` of arXiv 2402.16746, Section 3.1,
`T ∈ ℝ^{N × (N+1)}`: the rows of `T_f` other than the row of `P_0`. -/
noncomputable def gaussRows {N : ℕ} (μ w : Fin (N + 1) → ℝ) : Matrix (Fin N) (Fin (N + 1)) ℝ :=
  (gaussT μ w).submatrix Fin.succ id

/-- The constant `β_N = max_k w_k (N + 1)` of arXiv 2402.16746, Lemma 6. -/
noncomputable def betaN {N : ℕ} (w : Fin (N + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w * ((N : ℝ) + 1)

/-- The vector `b = (γ₁, 0, …, 0)ᵀ ∈ ℝ^N`, `γ₁² = 2/3`, of arXiv 2402.16746, Section 2.1.2. -/
noncomputable def bPN (N : ℕ) : Fin N → ℝ := fun j => if (j : ℕ) = 0 then √(2 / 3) else 0

lemma sum_legendreN_sq_pos (N : ℕ) (x : ℝ) : 0 < ∑ i : Fin (N + 1), legendreN i x ^ 2 := by
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨0, Finset.mem_univ _, ?_⟩
  simp only [Fin.val_zero, legendreN_zero]
  positivity

namespace IsGaussLegendre

variable {N : ℕ} {μ w : Fin (N + 1) → ℝ}

lemma weight_pos (hG : IsGaussLegendre N μ w) (k : Fin (N + 1)) : 0 < w k := by
  rw [hG.weight]
  exact inv_pos.2 (sum_legendreN_sq_pos N _)

/-- The vector `(P_i(μ_k))_i` is an eigenvector of `A_f`, since `P_{N+1}(μ_k) = 0`. -/
lemma mulVec_eq (hG : IsGaussLegendre N μ w) (k : Fin (N + 1)) :
    pnFlux N *ᵥ (fun j : Fin (N + 1) => legendreN j (μ k)) =
      μ k • fun j : Fin (N + 1) => legendreN j (μ k) := by
  ext i
  rw [pnFlux_mulVec, hG.root]
  simp

/-- Orthogonality of the columns of `T_f`: eigenvectors of a symmetric matrix for different
eigenvalues. -/
lemma sum_mul_eq_zero (hG : IsGaussLegendre N μ w) {k l : Fin (N + 1)} (hkl : k ≠ l) :
    ∑ i : Fin (N + 1), legendreN i (μ k) * legendreN i (μ l) = 0 := by
  set u : Fin (N + 1) → ℝ := fun j => legendreN j (μ k) with hu
  set v : Fin (N + 1) → ℝ := fun j => legendreN j (μ l) with hv
  have h1 : u ⬝ᵥ (pnFlux N *ᵥ v) = μ l * (u ⬝ᵥ v) := by
    rw [hG.mulVec_eq l, dotProduct_smul, smul_eq_mul]
  have h2 : u ⬝ᵥ (pnFlux N *ᵥ v) = μ k * (u ⬝ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, pnFlux_transpose, hG.mulVec_eq k,
      smul_dotProduct, smul_eq_mul]
  have h3 : (μ k - μ l) * (u ⬝ᵥ v) = 0 := by linarith
  have h4 : μ k - μ l ≠ 0 := sub_ne_zero.2 fun h => hkl (hG.injective h)
  have h5 := (mul_eq_zero.1 h3).resolve_left h4
  simpa [dotProduct, hu, hv] using h5

/-- `T_f` is orthogonal: `T_fᵀ T_f = 1`. -/
lemma transpose_mul_self (hG : IsGaussLegendre N μ w) : (gaussT μ w)ᵀ * gaussT μ w = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gaussT, Matrix.of_apply, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl
    have hw := hG.weight_pos k
    have e : ∀ i : Fin (N + 1), √(w k) * legendreN i (μ k) * (√(w k) * legendreN i (μ k)) =
        w k * legendreN i (μ k) ^ 2 := fun i => by
      have := Real.mul_self_sqrt hw.le
      calc _ = (√(w k) * √(w k)) * legendreN i (μ k) ^ 2 := by ring
        _ = _ := by rw [this]
    have hs := sum_legendreN_sq_pos N (μ k)
    have h1 : w k * ∑ i : Fin (N + 1), legendreN i (μ k) ^ 2 = 1 := by
      rw [hG.weight k]
      exact inv_mul_cancel₀ hs.ne'
    simp only [e, ← Finset.mul_sum, h1, ↓reduceIte]
  · simp only [hkl, ↓reduceIte]
    have e : ∀ i : Fin (N + 1), √(w k) * legendreN i (μ k) * (√(w l) * legendreN i (μ l)) =
        √(w k) * √(w l) * (legendreN i (μ k) * legendreN i (μ l)) := fun i => by ring
    simp only [e, ← Finset.mul_sum, hG.sum_mul_eq_zero hkl, mul_zero]

lemma mul_transpose_self (hG : IsGaussLegendre N μ w) : gaussT μ w * (gaussT μ w)ᵀ = 1 :=
  mul_eq_one_comm.1 hG.transpose_mul_self

/-- `A_f = T_f M T_fᵀ`, the factorisation used in arXiv 2402.16746, Section 3.1 and Appendix A. -/
lemma pnFlux_eq (hG : IsGaussLegendre N μ w) :
    pnFlux N = gaussT μ w * diagonal μ * (gaussT μ w)ᵀ := by
  have h : pnFlux N * gaussT μ w = gaussT μ w * diagonal μ := by
    ext i k
    have e := congrFun (hG.mulVec_eq k) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [gaussT, Matrix.of_apply]
    calc ∑ j, pnFlux N i j * (√(w k) * legendreN j (μ k))
        = √(w k) * ∑ j, pnFlux N i j * legendreN j (μ k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = √(w k) * legendreN i (μ k) * μ k := by
          rw [e]
          ring
  calc pnFlux N = pnFlux N * (gaussT μ w * (gaussT μ w)ᵀ) := by
        rw [hG.mul_transpose_self, Matrix.mul_one]
    _ = gaussT μ w * diagonal μ * (gaussT μ w)ᵀ := by rw [← Matrix.mul_assoc, h]

/-- `T Tᵀ = 1`: the rows of `T` are orthonormal. -/
lemma rows_mul_transpose (hG : IsGaussLegendre N μ w) :
    gaussRows μ w * (gaussRows μ w)ᵀ = 1 := by
  ext i j
  have h := congrFun (congrFun hG.mul_transpose_self i.succ) j.succ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.succ_inj] at h
  simpa [gaussRows, Matrix.mul_apply, Matrix.one_apply] using h

/-- The row of `P_0` in `T_f` has norm one. -/
lemma sum_first_row_sq (hG : IsGaussLegendre N μ w) : ∑ k, gaussT μ w 0 k ^ 2 = 1 := by
  have h := congrFun (congrFun hG.mul_transpose_self 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  simpa [sq] using h

/-- The weights sum to `2`. -/
lemma sum_weight (hG : IsGaussLegendre N μ w) : ∑ k, w k = 2 := by
  have h := hG.sum_first_row_sq
  have e : ∀ k, gaussT μ w 0 k ^ 2 = w k / 2 := fun k => by
    simp only [gaussT, Matrix.of_apply, Fin.val_zero, legendreN_zero, mul_pow, div_pow, one_pow]
    rw [Real.sq_sqrt (hG.weight_pos k).le, Real.sq_sqrt (by norm_num)]
    ring
  simp only [e, ← Finset.sum_div] at h
  linarith

/-- `β_N ≥ 2`: the maximal weight is at least the mean weight. -/
lemma two_le_betaN (hG : IsGaussLegendre N μ w) : 2 ≤ betaN w := by
  have h := Finset.sum_le_card_nsmul Finset.univ w
    (Finset.univ.sup' Finset.univ_nonempty w) fun k hk => Finset.le_sup' w hk
  rw [hG.sum_weight, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  push_cast at h
  rw [betaN]
  linarith

/-- The first row of `A_f` gives `b`: `b_j = √2 ∑_k (T_f)_{0k} μ_k T_{jk}`, i.e. `b = γ₀ a` in the
notation of Appendix A of arXiv 2402.16746. -/
lemma bPN_eq (hG : IsGaussLegendre N μ w) (j : Fin N) :
    bPN N j = √2 * ∑ k, gaussT μ w 0 k * μ k * gaussRows μ w j k := by
  have h := congrFun (congrFun hG.pnFlux_eq 0) j.succ
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at h
  have e : ∑ k, gaussT μ w 0 k * μ k * gaussRows μ w j k = pnFlux N 0 j.succ := by
    rw [h]
    rfl
  rw [e, bPN]
  simp only [pnFlux, Matrix.of_apply, Fin.val_zero, Fin.val_succ]
  by_cases hj : (j : ℕ) = 0
  · simp only [hj, ↓reduceIte, pnCoeff_zero]
    rw [Real.sqrt_div (by norm_num)]
    ring
  · simp [hj]

end IsGaussLegendre

/-- Non-vacuity of `IsGaussLegendre`, the Gauss data of arXiv 2402.16746, Section 3.1: for every `N`
there are Gauss–Legendre nodes and weights. They are obtained, as in the Golub–Welsch algorithm,
from the spectral theorem for `A_f`. -/
theorem exists_isGaussLegendre (N : ℕ) : ∃ μ w, IsGaussLegendre N μ w := by
  have hH : (pnFlux N).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, pnFlux_transpose]
  set e := hH.eigenvectorBasis with he
  set lam := hH.eigenvalues with hlam
  have hu : ∀ k, pnFlux N *ᵥ (⇑(e k)) = lam k • (⇑(e k)) := hH.mulVec_eigenvectorBasis
  have hne : ∀ k, (⇑(e k) : Fin (N + 1) → ℝ) ≠ 0 := fun k h0 => by
    have h1 : e k = 0 := by
      ext i
      exact congrFun h0 i
    exact (e.orthonormal.ne_zero k) h1
  refine ⟨lam, fun k => (∑ i : Fin (N + 1), legendreN i (lam k) ^ 2)⁻¹, ⟨?_, ?_, fun _ => rfl⟩⟩
  · intro k l hkl
    by_contra hne'
    have h0 : ∑ i, e k i * e l i = 0 := by
      have := e.orthonormal.2 hne'
      simpa [PiLp.inner_apply, mul_comm] using this
    obtain ⟨h1, -⟩ := eigen_structure N (hu k)
    obtain ⟨h2, -⟩ := eigen_structure N (hu l)
    set a0 := √2 * e k 0 with ha0
    set b0 := √2 * e l 0 with hb0
    have ha : a0 ≠ 0 := fun h => hne k (funext fun i => by
      rw [h1, h, zero_mul]
      rfl)
    have hb : b0 ≠ 0 := fun h => hne l (funext fun i => by
      rw [h2, h, zero_mul]
      rfl)
    have h3 : a0 * b0 * ∑ i : Fin (N + 1), legendreN i (lam k) ^ 2 = 0 := by
      rw [← h0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i, h2 i, ← hkl]
      ring
    exact (mul_ne_zero (mul_ne_zero ha hb) (sum_legendreN_sq_pos N _).ne') h3
  · exact fun k => (eigen_structure N (hu k)).2 (hne k)

/-- The block of `A_f` with indices `1, …, N` is `A = T M Tᵀ = A⁺ + A⁻` (arXiv 2402.16746,
Section 3.1): the flux matrix of the paper is the tridiagonal matrix with entries `a_k`. -/
lemma Apos_add_Aneg {N : ℕ} {μ w : Fin (N + 1) → ℝ} (hG : IsGaussLegendre N μ w) :
    Apos (gaussRows μ w) μ + Aneg (gaussRows μ w) μ = (pnFlux N).submatrix Fin.succ Fin.succ := by
  have e : Apos (gaussRows μ w) μ + Aneg (gaussRows μ w) μ =
      gaussRows μ w * diagonal μ * (gaussRows μ w)ᵀ := by
    rw [Apos, Aneg, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
    congr 3
    ext k
    ring
  rw [e, hG.pnFlux_eq]
  ext i j
  simp [gaussRows, Matrix.mul_apply]

/-- The CFL condition in the form `Δt ≤ 1/(C c) (2 ε Δx/|μ| + σ₀ Δx²/μ²)`, `C ≥ 4`, gives the bound
used in the energy estimate. -/
lemma cfl_aux {c Δt ε Δx σ₀ C μ : ℝ} (hc : 0 < c) (hε : 0 < ε) (hΔx : 0 < Δx) (hσ₀ : 0 < σ₀)
    (hC : 4 ≤ C) (hμ : μ ≠ 0)
    (h : Δt ≤ 1 / (C * c) * (2 * ε * Δx / |μ| + σ₀ * Δx ^ 2 / μ ^ 2)) :
    4 * c * Δt * μ ^ 2 ≤ 2 * ε * Δx * |μ| + σ₀ * Δx ^ 2 := by
  have hC0 : 0 < C := by linarith
  have habs : 0 < |μ| := abs_pos.2 hμ
  have hsq : 0 < μ ^ 2 := by positivity
  set Y := 2 * ε * Δx / |μ| + σ₀ * Δx ^ 2 / μ ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have e : μ ^ 2 * Y = 2 * ε * Δx * |μ| + σ₀ * Δx ^ 2 := by
    rw [hY, ← sq_abs μ]
    field_simp
  rw [← e]
  calc 4 * c * Δt * μ ^ 2 ≤ 4 * c * (1 / (C * c) * Y) * μ ^ 2 := by gcongr
    _ = 4 / C * (μ ^ 2 * Y) := by
        field_simp
    _ ≤ 1 * (μ ^ 2 * Y) := by
        gcongr
        rw [div_le_one hC0]
        exact hC
    _ = μ ^ 2 * Y := one_mul _

end PN

section Main

variable {n : ℕ} [NeZero n] {N : ℕ} {α β ξ ω ρ ρq τ θ ρ₁ : Type*}
  [Fintype α] [Fintype β] [Fintype ξ] [Fintype ω] [Fintype ρ] [Fintype ρq]
  [Fintype τ] [Fintype θ] [Fintype ρ₁]
  [DecidableEq α] [DecidableEq β] [DecidableEq ξ] [DecidableEq ω]
  [DecidableEq ρ] [DecidableEq ρq] [DecidableEq τ] [DecidableEq θ] [DecidableEq ρ₁]

/-- **Theorem 7 of arXiv 2402.16746, with a better constant**: the conclusion of `theorem_7` under
`Δt ≤ 1/(4 c) (2 ε Δx/|μ_k| + σ₀ Δx²/μ_k²)` for all `μ_k ≠ 0`. Since `β_N ≥ 2`, the constant
`1/(4 c)` improves the `1/(5 c β_N)` of the paper by at least the factor `5/2`, and it does not
depend on `N`. The improvement comes from the sharper form of Lemma 6, `norm_fluxAdj_sq_le`, and of
the coupling bound, `sum_dMinus_moment_sq_le`. -/
theorem theorem_7_sharp (p : Params n) {μ w : Fin (N + 1) → ℝ} (hG : IsGaussLegendre N μ w)
    (hCFL : ∀ k, μ k ≠ 0 →
      p.Δt ≤ 1 / (4 * p.c) * (2 * p.ε * p.Δx / |μ k| + p.σ₀ * p.Δx ^ 2 / μ k ^ 2))
    {Tn hn Tn1 hn1 : ZMod n → ℝ} {X : Matrix (ZMod n) α ℝ} {S : Matrix α β ℝ}
    {V : Matrix (Fin N) β ℝ} {X1 : Matrix (ZMod n) ρ₁ ℝ} {S1 : Matrix ρ₁ (ω ⊕ θ) ℝ}
    {V1 : Matrix (Fin N) (ω ⊕ θ) ℝ}
    (st : APBUGStep ξ ρ ρq τ p (Apos (gaussRows μ w) μ) (Aneg (gaussRows μ w) μ) (bPN N)
      Tn hn X S V Tn1 hn1 X1 S1 V1) :
    energy p Tn1 hn1 (X1 * S1 * V1ᵀ) ≤ energy p Tn hn (X * S * Vᵀ) := by
  refine energy_le_of_step p hG.rows_mul_transpose μ (gaussT μ w 0) hG.sum_first_row_sq hG.bPN_eq
    (fun k => ?_) st
  by_cases hμ : μ k = 0
  · have := p.ε_pos
    have := p.Δx_pos
    have := p.σ₀_pos
    simp only [hμ]
    simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_add]
    positivity
  · exact cfl_aux p.c_pos p.ε_pos p.Δx_pos p.σ₀_pos le_rfl hμ (hCFL k hμ)

/-- **Theorem 7 of arXiv 2402.16746** (energy stability of the asymptotic-preserving rank-adaptive
BUG scheme): under the CFL condition (3.4),
`Δt ≤ 1/(5 c β_N) (2 ε Δx/|μ_k| + σ₀ Δx²/μ_k²)` for all `k` with `μ_k ≠ 0`, one step of the scheme
of Section 4.2 for the linearised problem satisfies `eⁿ⁺¹ ≤ eⁿ`, with the energy of Theorem 4,
`eⁿ = ‖a Tⁿ + (ε²/c) hⁿ‖² + ‖(ε/(γ₀ c)) Xⁿ Sⁿ Vⁿᵀ‖² + ‖√(a c_ν/2) Tⁿ‖²`.

This is the paper's scheme on the concrete grid and moment system, see `APBUGStep`: the `P_N`
closure with `N` moments, `μ, w` the Gauss–Legendre data, `T`, `A^±`, `b` as in the paper. The
differences are that the grid is periodic (the paper also allows zero boundary values), `ε > 0`
(a field of `Params`), and the reading of `K̂ᵃᵖ` explained at `APBUGStep`. A sharper form is
`theorem_7_sharp`. Non-vacuity: `exists_isGaussLegendre`, `exists_APBUGStep`. -/
theorem theorem_7 (p : Params n) {μ w : Fin (N + 1) → ℝ} (hG : IsGaussLegendre N μ w)
    (hCFL : ∀ k, μ k ≠ 0 →
      p.Δt ≤ 1 / (5 * p.c * betaN w) * (2 * p.ε * p.Δx / |μ k| + p.σ₀ * p.Δx ^ 2 / μ k ^ 2))
    {Tn hn Tn1 hn1 : ZMod n → ℝ} {X : Matrix (ZMod n) α ℝ} {S : Matrix α β ℝ}
    {V : Matrix (Fin N) β ℝ} {X1 : Matrix (ZMod n) ρ₁ ℝ} {S1 : Matrix ρ₁ (ω ⊕ θ) ℝ}
    {V1 : Matrix (Fin N) (ω ⊕ θ) ℝ}
    (st : APBUGStep ξ ρ ρq τ p (Apos (gaussRows μ w) μ) (Aneg (gaussRows μ w) μ) (bPN N)
      Tn hn X S V Tn1 hn1 X1 S1 V1) :
    energy p Tn1 hn1 (X1 * S1 * V1ᵀ) ≤ energy p Tn hn (X * S * Vᵀ) := by
  refine energy_le_of_step p hG.rows_mul_transpose μ (gaussT μ w 0) hG.sum_first_row_sq hG.bPN_eq
    (fun k => ?_) st
  by_cases hμ : μ k = 0
  · have := p.ε_pos
    have := p.Δx_pos
    have := p.σ₀_pos
    simp only [hμ]
    simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_add]
    positivity
  · have hβ := hG.two_le_betaN
    have hk := hCFL k hμ
    rw [show 5 * p.c * betaN w = (5 * betaN w) * p.c by ring] at hk
    exact cfl_aux p.c_pos p.ε_pos p.Δx_pos p.σ₀_pos (by linarith) hμ hk

end Main

/-! ### Non-vacuity: the scheme can be carried out -/

section Existence

variable {n : ℕ} [NeZero n] {ν α β : Type*} [Fintype ν] [Fintype α] [Fintype β]
  [DecidableEq ν] [DecidableEq α] [DecidableEq β]

lemma isUnit_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix (ZMod n) ι ℝ)
    {d : ZMod n → ℝ} (hd : ∀ i, 0 ≤ d i) {c : ℝ} (hc : 0 < c) :
    IsUnit (c • (1 : Matrix ι ι ℝ) + Zᵀ * diagonal d * Z) := by
  have h1 : (c • (1 : Matrix ι ι ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have h2 : (Zᵀ * diagonal d * Z).PosSemidef := by
    have hD : (diagonal d).PosSemidef := Matrix.posSemidef_diagonal_iff.2 hd
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.conjTranspose_mul_mul_same Z
  exact (h1.add_posSemidef h2).isUnit

lemma exists_left_solve {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {M : Matrix ι ι ℝ} {c : ℝ} (hM : IsUnit (c • (1 : Matrix ι ι ℝ) + M)) (Y0 F : Matrix ι κ ℝ) :
    ∃ Y, c • (Y - Y0) = F - M * Y := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hM
  refine ⟨(c • (1 : Matrix ι ι ℝ) + M)⁻¹ * (c • Y0 + F), ?_⟩
  set Y := (c • (1 : Matrix ι ι ℝ) + M)⁻¹ * (c • Y0 + F) with hY
  have h : (c • (1 : Matrix ι ι ℝ) + M) * Y = c • Y0 + F := by
    rw [hY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]

lemma exists_right_solve {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {M : Matrix ι ι ℝ} {c : ℝ} (hM : IsUnit (c • (1 : Matrix ι ι ℝ) + M)) (Y0 F : Matrix κ ι ℝ) :
    ∃ Y, c • (Y - Y0) = F - Y * M := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hM
  refine ⟨(c • Y0 + F) * (c • (1 : Matrix ι ι ℝ) + M)⁻¹, ?_⟩
  set Y := (c • Y0 + F) * (c • (1 : Matrix ι ι ℝ) + M)⁻¹ with hY
  have h : Y * (c • (1 : Matrix ι ι ℝ) + M) = c • Y0 + F := by
    rw [hY, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]

/-- The unit vector `b / ‖b‖` as a one-column matrix with `b = V̂ᵃᵖ s`. -/
lemma exists_unit_column {b : ν → ℝ} (hb : b ≠ 0) :
    ∃ (A : Matrix ν (Fin 1) ℝ) (s : Fin 1 → ℝ), Aᵀ * A = 1 ∧ b = A *ᵥ s := by
  set t := ∑ j, b j ^ 2 with ht
  have ht0 : 0 < t := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
    have hj' : b j ≠ 0 := hj
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, by positivity⟩
  have hr : √t ≠ 0 := by positivity
  refine ⟨Matrix.of fun j _ => b j / √t, fun _ => √t, ?_, ?_⟩
  · ext i j
    obtain rfl : i = j := Subsingleton.elim i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply_eq]
    have e : ∀ x, b x / √t * (b x / √t) = b x ^ 2 / t := fun x => by
      rw [div_mul_div_comm, Real.mul_self_sqrt ht0.le, sq]
    simp only [e, ← Finset.sum_div, ← ht]
    exact div_self ht0.ne'
  · ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one]
    field_simp

/-- **Non-vacuity of `APBUGStep`** (the scheme of arXiv 2402.16746, Section 4.2). For all data with
orthonormal `Xⁿ`, `Vⁿ` and `b ≠ 0`, one step of the scheme can be carried out: the implicit K-, L-
and S-steps are solvable, and the augmented bases, the QR factorisations and the SVD exist. -/
theorem exists_APBUGStep (p : Params n) (Ap Am : Matrix ν ν ℝ) {b : ν → ℝ} (hb : b ≠ 0)
    (Tn hn : ZMod n → ℝ) {X : Matrix (ZMod n) α ℝ} (S : Matrix α β ℝ) {V : Matrix ν β ℝ}
    (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) :
    ∃ (rξ rρ rq rτ r₁ : ℕ) (Tn1 hn1 : ZMod n → ℝ) (X1 : Matrix (ZMod n) (Fin r₁) ℝ)
      (S1 : Matrix (Fin r₁) (Fin 1 ⊕ Fin rτ) ℝ) (V1 : Matrix ν (Fin 1 ⊕ Fin rτ) ℝ),
      Nonempty (APBUGStep (Fin rξ) (Fin rρ) (Fin rq) (Fin rτ) p Ap Am b Tn hn X S V Tn1 hn1 X1 S1
        V1) := by
  have hc := p.c_pos
  have hε := p.ε_pos
  have hΔt := p.Δt_pos
  have hσf : ∀ i, 0 ≤ p.σf i := fun i => p.σ₀_pos.le.trans (p.σf_ge i)
  have hσc : ∀ i, 0 ≤ p.σ i := fun i => p.σ₀_pos.le.trans (p.σ_ge i)
  set c0 := p.ε ^ 2 / p.c * (1 / p.Δt) with hc0
  have hc00 : 0 < c0 := by positivity
  -- The K-step.
  have hUK : IsUnit (c0 • (1 : Matrix (ZMod n) (ZMod n) ℝ) + diagonal p.σf) := by
    simpa using isUnit_shift (1 : Matrix (ZMod n) (ZMod n) ℝ) hσf hc00
  obtain ⟨K1, hK1⟩ := exists_left_solve hUK (X * S)
    (-(p.ε • (DM p.Δx (X * S) * (Vᵀ * Ap * V) + DP p.Δx (X * S) * (Vᵀ * Am * V))) -
      vecMulVec (coupling p Tn hn) (Vᵀ *ᵥ b))
  -- The L-step.
  obtain ⟨L1, hL1⟩ := exists_right_solve (isUnit_shift X hσf hc00) (V * Sᵀ)
    (-(p.ε • (Ap * (V * Sᵀ) * ((DM p.Δx X)ᵀ * X) + Am * (V * Sᵀ) * ((DP p.Δx X)ᵀ * X))) -
      vecMulVec b (Xᵀ *ᵥ coupling p Tn hn))
  -- The augmented spatial basis.
  set W0 : Matrix (ZMod n) (Fin 1) ℝ := Matrix.of fun i _ => apFlux p Tn i with hW0
  obtain ⟨Xh, hXh, hXcap⟩ := LeanDLRA.exists_orthonormal_capture (r := _)
    (fromCols (fromCols W0 K1) X) le_rfl (Matrix.rank_le_card_height _)
  rw [Matrix.mul_fromCols, Matrix.mul_fromCols] at hXcap
  have hXc := Matrix.fromCols_inj hXcap
  have hXc2 := Matrix.fromCols_inj hXc.1
  have hXap : (Xh * Xhᵀ) *ᵥ apFlux p Tn = apFlux p Tn := by
    ext i
    have := congrFun (congrFun hXc2.1 i) 0
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hW0] using this
  -- The augmented angular basis.
  obtain ⟨Vap, s0, hVap, hbV⟩ := exists_unit_column hb
  set K2 := fromCols L1 V with hK2
  have hzero : Vapᵀ * ((1 - Vap * Vapᵀ) * K2) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hVap,
      Matrix.one_mul, sub_self, Matrix.zero_mul]
  have hrk : 1 + ((1 - Vap * Vapᵀ) * K2).rank ≤ Fintype.card ν := by
    have h1 := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
    rw [Matrix.rank_transpose, LeanDLRA.rank_eq_card_of_transpose_mul_eq_one hVap,
      Fintype.card_fin] at h1
    exact h1
  obtain ⟨Vrem, hVrem, h₁₀, hcap⟩ := LeanDLRA.exists_orthonormal_capture_compl Vap hVap K2 le_rfl
    (by rwa [Fintype.card_fin])
  obtain ⟨hVh, hVcap, -⟩ := LeanDLRA.fromCols_orthonormal_capture hVap hVrem h₁₀ hcap
  set Vh := fromCols Vap Vrem with hVhdef
  have hVcap' : Vh * Vhᵀ * fromCols L1 V = fromCols L1 V := hVcap
  rw [Matrix.mul_fromCols] at hVcap'
  have hVc := Matrix.fromCols_inj hVcap'
  -- The S-step.
  set St := Xhᵀ * X * S * Vᵀ * Vh with hSt
  obtain ⟨Sh, hSh⟩ := exists_left_solve (isUnit_shift Xh hσf hc00) St
    (-(p.ε • (Xhᵀ * DM p.Δx Xh * St * (Vhᵀ * Ap * Vh) + Xhᵀ * DP p.Δx Xh * St * (Vhᵀ * Am * Vh))) -
      vecMulVec (Xhᵀ *ᵥ coupling p Tn hn) (Vhᵀ *ᵥ b))
  -- The QR factorisations and the SVD.
  set Kap := (Xh * Sh).toCols₁ with hKap
  set Krem := (Xh * Sh).toCols₂ with hKrem
  obtain ⟨Xrem, hXrem, hXremc⟩ := LeanDLRA.exists_orthonormal_capture Krem le_rfl
    (Matrix.rank_le_card_height _)
  set Srem := Xremᵀ * Krem with hSrem
  obtain ⟨U, W, sv, hU, hW, -, -, -, hsvd⟩ := LeanDLRA.SVD.exists_svd Srem rfl
  have hone : 1 ≤ Fintype.card (ZMod n) := by
    rw [ZMod.card]
    exact NeZero.pos n
  obtain ⟨Xap, hXapo, hXapc⟩ := LeanDLRA.exists_orthonormal_capture (r := 1) Kap
    (by simpa using Kap.rank_le_card_width) hone
  set Xt := fromCols Xap (Xrem * U.submatrix id id) with hXt
  obtain ⟨X1, hX1, hX1c⟩ := LeanDLRA.exists_orthonormal_capture Xt le_rfl
    (Matrix.rank_le_card_height _)
  set Sn := fromBlocks (Xapᵀ * Kap) 0 0 (diagonal (sv ∘ id)) with hSn
  set S1 := X1ᵀ * Xt * Sn with hS1
  set V1 := fromCols Vap (Vrem * W.submatrix id id) with hV1
  -- The macroscopic update.
  set q := (X1 * S1 * V1ᵀ) *ᵥ b with hq
  have hκ : 0 < p.κ := div_pos two_pos p.cν_pos
  have hD : ∀ i, 0 < c0 + p.a * p.κ * p.σ i + p.σ i := fun i => by
    have := p.a_pos
    have := hσc i
    positivity
  set hn1 : ZMod n → ℝ := fun i =>
    (c0 * hn i - 1 / 2 * dMinus p.Δx q i) / (c0 + p.a * p.κ * p.σ i + p.σ i) with hhn1
  set Tn1 : ZMod n → ℝ := fun i => Tn i + p.Δt * (p.κ * p.σ i * hn1 i) with hTn1
  refine ⟨(fromCols (fromCols W0 K1) X).rank, ((1 - Vap * Vapᵀ) * K2).rank, Krem.rank, Srem.rank,
    Xt.rank, Tn1, hn1, X1, S1, V1, ⟨?_⟩⟩
  exact
    { X_orth := hX
      V_orth := hV
      K1 := K1
      kStep := by rw [smul_smul]; exact hK1
      L1 := L1
      lStep := by rw [smul_smul]; exact hL1
      Xh := Xh
      Xh_orth := hXh
      Xh_ap := hXap
      Xh_K := hXc2.2
      Xh_X := hXc.2
      Vap := Vap
      Vrem := Vrem
      Vh := Vh
      Vh_eq := rfl
      Vh_orth := hVh
      Vh_b := ⟨s0, hbV⟩
      Vh_L := hVc.1
      Vh_V := hVc.2
      Stilde := St
      Stilde_eq := rfl
      Sh := Sh
      sStep := by rw [smul_smul]; exact hSh
      Kap := Kap
      Krem := Krem
      split := (Matrix.fromCols_toCols _).symm
      Xrem := Xrem
      Srem := Srem
      Xrem_orth := hXrem
      qr_rem := by rw [hSrem, ← Matrix.mul_assoc, hXremc]
      U := U
      W := W
      s := sv
      U_orth := hU
      W_orth := hW
      svd := hsvd
      keep := id
      keep_inj := Function.injective_id
      Xap := Xap
      Sap := Xapᵀ * Kap
      Xap_orth := hXapo
      qr_ap := by rw [← Matrix.mul_assoc, hXapc]
      R2 := X1ᵀ * Xt
      X1_orth := hX1
      qr_new := by rw [← Matrix.mul_assoc, hX1c]
      S1_eq := rfl
      V1_eq := rfl
      hStep := fun i => by
        have hne := (hD i).ne'
        have e : p.ε ^ 2 / p.c * ((hn1 i - hn i) / p.Δt) = c0 * (hn1 i - hn i) := by
          simp only [hc0]
          ring
        have e2 : (c0 + p.a * p.κ * p.σ i + p.σ i) * hn1 i =
            c0 * hn i - 1 / 2 * dMinus p.Δx q i := by
          simp only [hhn1]
          field_simp
        rw [e]
        linear_combination e2
      TStep := fun i => by
        simp only [hTn1]
        field_simp
        ring }

/-- `b ≠ 0` for `N ≥ 1`. -/
lemma bPN_ne_zero (N : ℕ) [NeZero N] : bPN N ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [bPN] at h0

end Existence

end APEnergy

end LeanDLRA.Literature.P2402_16746
