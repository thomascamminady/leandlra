import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Results of arXiv 2609.20292: Further DLRA approaches for SDEs

This module formalizes the algebraic core of Remark 2.3 (Consistency of DLRA approaches) of
arXiv 2609.20292 (Kazashi, Nobile, Zoccolan). Let `U ∈ ℝ^{k×d}` have orthonormal rows
(`U Uᵀ = I`), so `P_U^⊥ = I - Uᵀ U` is the complementary projector on `ℝ^d`. Let the diffusion
`b_t` take values in the row space of `U`, i.e. `b_t = Uᵀ β_t` almost surely for some
`β_t ∈ ℝ^{k×m}`. Then the diffusion correction `C_Y⁻¹ U E[b bᵀ] P_U^⊥` in the equation for `U`
vanishes, and the resulting DO equation coincides with the one without that term.

Proved here (on matrices, with `E` the entrywise Bochner integral `expMat`):

* `extra_term_eq_expMat` (Remark 2.3, middle equality): `U E[b bᵀ] = E[β βᵀ] U`.
* `extra_term_vanishes` (Remark 2.3): `C_Y⁻¹ (U E[b bᵀ] P_U^⊥) = 0` for every `C_Y`.
* `drift_equation_unchanged`: for any drift term `D`, `C_Y⁻¹ (D + U E[b bᵀ] P_U^⊥) = C_Y⁻¹ D`.
* A non-vacuity `example` (`U = (1, 0)`, constant `β`, Dirac measure).

Differences from the paper and what is left out:

* The paper's `C_Y` is the Gramian `E[Y Yᵀ]`, invertible under its standing assumptions. The
  proofs do not use invertibility: `C_Y⁻¹` is Mathlib's matrix inverse, and the vanishing holds
  for any `C_Y⁻¹`.
* The paper's `b` and `β` are random fields with progressive measurability and a.s. continuous
  paths. These serve well-posedness of the DO equations, not the algebraic identity, so they are
  omitted; the statements are therefore at least as strong. `b = Uᵀ β` is assumed almost surely.
* Expectations are entrywise Bochner integrals over an arbitrary measure `μ` (the paper's `E` is
  the case of a probability measure). Linearity `E[A M B] = A E[M] B` needs the entries of `β βᵀ`
  to be integrable, assumed as `hβ` (finite second moments, presupposed by `E[β βᵀ]` in the
  paper).
* Not formalized: the derivation of the DO equations (paper eqs. (17), (18), (20)), which uses a
  formal variational first-order argument; the staggered scheme of Sec. 2.6, eqs. (35)-(36); the
  Stratonovich part (Sec. 3), including the weighted empirical tangent projector of Sec. 3.2,
  eqs. (42)-(46).

Core definitions used: the matrix transpose and the row-orthonormality convention `U * Uᵀ = 1`
(as in `LeanDLRA.Matrix.Projectors`). No projector or substep structure is defined: `P_U^⊥` is
written `1 - Uᵀ * U`, the complement of the row projector `rightProj Uᵀ`.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2609_20292

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Entrywise expectation of a matrix-valued random variable: `(E M)_{ij} = ∫ M_{ij} dμ`. -/
noncomputable def expMat {p q : Type*} (μ : Measure Ω) (M : Ω → Matrix p q ℝ) : Matrix p q ℝ :=
  fun i j => ∫ ω, M ω i j ∂μ

/-- Expectations of almost surely equal matrix-valued functions agree. -/
lemma expMat_congr_ae {p q : Type*} {μ : Measure Ω} {M N : Ω → Matrix p q ℝ} (h : M =ᵐ[μ] N) :
    expMat μ M = expMat μ N := by
  funext i j
  exact integral_congr_ae (h.mono fun ω hω => congrFun (congrFun hω i) j)

/-- Linearity of the entrywise expectation under constant left and right multiplication, for
matrix-valued functions whose entries are integrable. -/
lemma expMat_mul_mul {p q r s : Type*} [Fintype q] [Fintype r] (μ : Measure Ω)
    (A : Matrix p q ℝ) (B : Matrix r s ℝ) (M : Ω → Matrix q r ℝ)
    (hM : ∀ i j, Integrable (fun ω => M ω i j) μ) :
    expMat μ (fun ω => A * M ω * B) = A * expMat μ M * B := by
  funext i j
  simp only [expMat, Matrix.mul_apply, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      have h : ∀ ω, A i y * M ω y x * B x j = (A i y * B x j) * M ω y x := fun ω => by ring
      simp_rw [h]
      rw [integral_const_mul]
      ring
    · intro y _
      exact ((hM y x).const_mul (A i y)).mul_const (B x j)
  · intro x _
    exact integrable_finsetSum _ fun y _ => ((hM y x).const_mul (A i y)).mul_const (B x j)

/-- For `U Uᵀ = 1`, the projector `1 - Uᵀ U` annihilates `Q U` for every `Q`. -/
lemma mul_perp_eq_zero {k d : ℕ} (Q : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin k) (Fin d) ℝ)
    (hU : U * Uᵀ = 1) : Q * U * (1 - Uᵀ * U) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc Q U, ← Matrix.mul_assoc U Uᵀ U, hU,
    Matrix.one_mul, sub_self]

/-- **Remark 2.3, middle identity** (arXiv 2609.20292, Remark 2.3). If `b = Uᵀ β` almost surely with
`U Uᵀ = 1` and the second moments of `β` are integrable, then `U E[b bᵀ] = E[β βᵀ] U`. -/
theorem extra_term_eq_expMat {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {k d m : ℕ} (U : Matrix (Fin k) (Fin d) ℝ) (hU : U * Uᵀ = 1)
    (β : Ω' → Matrix (Fin k) (Fin m) ℝ)
    (hβ : ∀ p q : Fin k, Integrable (fun ω => (β ω * (β ω)ᵀ) p q) μ)
    (b : Ω' → Matrix (Fin d) (Fin m) ℝ) (hb : ∀ᵐ ω ∂μ, b ω = Uᵀ * β ω) :
    U * expMat μ (fun ω => b ω * (b ω)ᵀ) = expMat μ (fun ω => β ω * (β ω)ᵀ) * U := by
  have h1 : expMat μ (fun ω => b ω * (b ω)ᵀ)
      = expMat μ (fun ω => Uᵀ * (β ω * (β ω)ᵀ) * U) := by
    refine expMat_congr_ae (hb.mono fun ω hω => ?_)
    simp only [hω, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, expMat_mul_mul μ Uᵀ U (fun ω => β ω * (β ω)ᵀ) hβ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᵀ, hU, Matrix.one_mul]

/-- **Remark 2.3** (arXiv 2609.20292). Let `U` have orthonormal rows, `b = Uᵀ β` almost surely with
`β` having integrable second moments, and let `C_Y` be any matrix. Then the diffusion correction
`C_Y⁻¹ U E[b bᵀ] P_U^⊥`, with `P_U^⊥ = 1 - Uᵀ U`, vanishes. -/
theorem extra_term_vanishes {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {k d m : ℕ} (U : Matrix (Fin k) (Fin d) ℝ) (hU : U * Uᵀ = 1)
    (β : Ω' → Matrix (Fin k) (Fin m) ℝ)
    (hβ : ∀ p q : Fin k, Integrable (fun ω => (β ω * (β ω)ᵀ) p q) μ)
    (b : Ω' → Matrix (Fin d) (Fin m) ℝ) (hb : ∀ᵐ ω ∂μ, b ω = Uᵀ * β ω)
    (CY : Matrix (Fin k) (Fin k) ℝ) :
    CY⁻¹ * (U * expMat μ (fun ω => b ω * (b ω)ᵀ) * (1 - Uᵀ * U)) = 0 := by
  rw [extra_term_eq_expMat μ U hU β hβ b hb, mul_perp_eq_zero _ U hU, Matrix.mul_zero]

/-- **Remark 2.3, consequence** (arXiv 2609.20292). For any drift term `D`, the right-hand side
  of the
`U`-equation with the diffusion correction equals the one without it: `C_Y⁻¹ (D + U E[b bᵀ] P_U^⊥)
= C_Y⁻¹ D`. -/
theorem drift_equation_unchanged {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    {k d m : ℕ} (U : Matrix (Fin k) (Fin d) ℝ) (hU : U * Uᵀ = 1)
    (β : Ω' → Matrix (Fin k) (Fin m) ℝ)
    (hβ : ∀ p q : Fin k, Integrable (fun ω => (β ω * (β ω)ᵀ) p q) μ)
    (b : Ω' → Matrix (Fin d) (Fin m) ℝ) (hb : ∀ᵐ ω ∂μ, b ω = Uᵀ * β ω)
    (CY : Matrix (Fin k) (Fin k) ℝ) (D : Matrix (Fin k) (Fin d) ℝ) :
    CY⁻¹ * (D + U * expMat μ (fun ω => b ω * (b ω)ᵀ) * (1 - Uᵀ * U)) = CY⁻¹ * D := by
  rw [Matrix.mul_add, extra_term_vanishes μ U hU β hβ b hb CY, add_zero]

/-- Non-vacuity data: `U = (1, 0)` has orthonormal rows (`k = 1`, `d = 2`), and `β ≡ 1` (`m =
  1`). -/
def exU : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

/-- Non-vacuity data: the constant diffusion coefficient `β ≡ 1`. -/
def exβ : Unit → Matrix (Fin 1) (Fin 1) ℝ := fun _ => !![1]

lemma exU_mul_transpose : exU * exUᵀ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [exU, Matrix.mul_apply]

/-- Non-vacuity: `extra_term_vanishes` applies on the Dirac probability measure with `b = Uᵀ β`
(so `hb` holds for every realization), and the conclusion is the vanishing of the correction. -/
example (CY : Matrix (Fin 1) (Fin 1) ℝ) :
    CY⁻¹ * (exU * expMat (Measure.dirac ()) (fun ω => (exUᵀ * exβ ω) * (exUᵀ * exβ ω)ᵀ) *
      (1 - exUᵀ * exU)) = 0 :=
  extra_term_vanishes (Measure.dirac ()) exU exU_mul_transpose exβ (fun _ _ => Integrable.of_finite)
    (fun ω => exUᵀ * exβ ω) (ae_of_all _ fun _ => rfl) CY

end LeanDLRA.Literature.P2609_20292
