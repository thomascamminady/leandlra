import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2607.03402: Sketched DLRA: orthogonal vs oblique projections

Formalized: **Sec. 5.2** (Loewner bounds for sketch-orthonormal bases). Let `Θ` ε-embed the range
of `P` (`(1-ε)‖Pc‖² ≤ ‖ΘPc‖² ≤ (1+ε)‖Pc‖²` for all coefficient vectors `c`, with `0 ≤ ε < 1`),
and let `ΘP` have orthonormal columns. Then `(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I` in the Loewner order
(`sketch_embed_loewner`). The statement is over real matrices, with `Pc` ranging over `range P`.
A non-vacuity example with `P = e₁`, `Θ = I`, `ε = 1/2` is included.

Left out, with reasons:
* **Prop. 2.2 and Cor. 2.3** (two-sided OSE bound `|⟨ΘZΩᵀ, ΘZ'Ωᵀ⟩ − ⟨Z, Z'⟩| ≤ (2ε+ε²)‖Z‖‖Z'‖`):
  not formalized. The deterministic argument needs the embedding of the combined column and row
  spaces and a Frobenius-norm estimate for the cross terms, which was out of time budget. The
  probability statement is out of scope.
* **Prop. 3.1** (factor ODEs under the Euclidean gauge for sketch-orthogonal factors): not
  formalized. The derivative computation with matrix inverses was out of time budget.
* **Prop. 4.4** (oblique sketch DLRA equals DLRA iff a sketched orthogonality condition): already
  proved in `LeanDLRA/Matrix/Interpolation.lean` as `isObliqueProj_sketchTangentProj` and
  `sketchTangentProj_eq_iff`, with eq. (15) as `norm_sketchTangentProj_sub_le`. Not duplicated here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix MatrixOrder

namespace LeanDLRA.Literature.P2607_03402

/-- Quadratic form of `PᵀP`: `xᵀ (PᵀP) x = ‖P x‖²`. -/
private lemma quad_transpose_mul_self {m k : Type*} [Fintype m] [Fintype k] (P : Matrix m k ℝ)
    (x : k → ℝ) : x ⬝ᵥ ((Pᵀ * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Sec. 5.2 of arXiv 2607.03402** (Loewner form of the near-orthonormality of sketched bases).
Let `P : ℝ^{m×k}` and let `Θ : ℝ^{p×m}` ε-embed the range of `P`, in the sense that
`(1-ε)‖Pc‖² ≤ ‖ΘPc‖² ≤ (1+ε)‖Pc‖²` for every coefficient vector `c` (so `Pc` ranges over
`range P`), with `0 ≤ ε < 1`.  If `ΘP` has orthonormal columns, `(ΘP)ᵀ(ΘP) = I`, then
`(1+ε)⁻¹ I ⪯ PᵀP ⪯ (1-ε)⁻¹ I` in the Loewner order. -/
theorem sketch_embed_loewner {m k p : Type*} [Fintype m] [Fintype k] [Fintype p] [DecidableEq k]
    (P : Matrix m k ℝ) (Θ : Matrix p m ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hemb : ∀ c : k → ℝ,
      (1 - ε) * ((P *ᵥ c) ⬝ᵥ (P *ᵥ c)) ≤ (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) ∧
        (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) ≤ (1 + ε) * ((P *ᵥ c) ⬝ᵥ (P *ᵥ c)))
    (hP : (Θ * P)ᵀ * (Θ * P) = 1) :
    ((1 + ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) ≤ Pᵀ * P ∧
      Pᵀ * P ≤ ((1 - ε)⁻¹ : ℝ) • (1 : Matrix k k ℝ) := by
  have hnorm : ∀ c : k → ℝ, c ⬝ᵥ c = (Θ *ᵥ (P *ᵥ c)) ⬝ᵥ (Θ *ᵥ (P *ᵥ c)) := by
    intro c
    have h := quad_transpose_mul_self (Θ * P) c
    rw [hP, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
    exact h
  have hpos1 : (0 : ℝ) < 1 + ε := by linarith
  have hpos2 : (0 : ℝ) < 1 - ε := by linarith
  have hlow : ∀ c : k → ℝ, (1 + ε)⁻¹ * (c ⬝ᵥ c) ≤ (P *ᵥ c) ⬝ᵥ (P *ᵥ c) := by
    intro c
    have h := (hemb c).2
    rw [← hnorm c] at h
    rw [inv_mul_le_iff₀ hpos1]
    linarith
  have hup : ∀ c : k → ℝ, (P *ᵥ c) ⬝ᵥ (P *ᵥ c) ≤ (1 - ε)⁻¹ * (c ⬝ᵥ c) := by
    intro c
    have h := (hemb c).1
    rw [← hnorm c] at h
    rw [le_inv_mul_iff₀ hpos2]
    linarith
  have hH : (Pᵀ * P).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self P
  have hI : ∀ a : ℝ, (a • (1 : Matrix k k ℝ)).IsHermitian := fun a => by
    simp [Matrix.IsHermitian]
  constructor
  · rw [Matrix.le_iff]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hH.sub (hI _))
    intro x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, quad_transpose_mul_self, smul_eq_mul]
    linarith [hlow x]
  · rw [Matrix.le_iff]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((hI _).sub hH)
    intro x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, quad_transpose_mul_self, smul_eq_mul]
    linarith [hup x]

/-- Non-vacuity: `P = e₁ ∈ ℝ²` and `Θ = I` satisfy the hypotheses of `sketch_embed_loewner`
with `ε = 1/2`, so the conclusion is not vacuous. -/
example :
    ((1 + (1 / 2 : ℝ))⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ≤
        (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![(1 : ℝ); 0] ∧
      (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![(1 : ℝ); 0] ≤
        ((1 - (1 / 2 : ℝ))⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  apply sketch_embed_loewner (!![(1 : ℝ); 0] : Matrix (Fin 2) (Fin 1) ℝ)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) (by norm_num) (by norm_num)
  · intro c
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    constructor
    · nlinarith [sq_nonneg (c 0)]
    · nlinarith [sq_nonneg (c 0)]
  · ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]

end LeanDLRA.Literature.P2607_03402
