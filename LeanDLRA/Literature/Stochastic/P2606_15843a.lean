import Mathlib
import LeanDLRA.Foundations.Projector

/-!
# Results of arXiv 2606.15843: Long-time behaviour of DLRA for SDEs

This module formalizes the abstract linear-algebra core of the DLRA projector `P_Y` of the paper
(Lemma 3.4, on a real inner product space `E`) and the algebraic step of Proposition 3.5 (the
row-space projector `P_U = Uᵀ U` of `ℝ^d` is the identity at full rank `r = d`).

* `gramY`, `projY`: the Gram matrix `C_Y = (⟪Y_i, Y_j⟫)` and the explicit operator
  `P_Y u = E[u Yᵀ] C_Y⁻¹ Y` of the paper, where `E[u Yᵀ]_j = ⟪u, Y_j⟫`.
* `gramY_isUnit`: linear independence of `Y` makes `C_Y` invertible (the paper assumes this).
* `projY_eq_starProjection`: `P_Y` is the orthogonal projection onto `span{Y_1, …, Y_r}`.
* `lemma_3_4_projY` (**Lemma 3.4**, arXiv 2606.15843, abstract form): `P_Y` is an orthogonal
  projector with `‖P_Y‖ ≤ 1`. It is stated on a real inner product space `E`, not on the
  `ℝ^d`-valued `L²(Ω; ℝ^d)` of the paper. The `ℝ^d`-valued operator acts componentwise, and that
  componentwise statement is not proved in this file. The paper's standing hypothesis that
  `Y_1, …, Y_r` are linearly independent is kept.
* `prop_3_5_drift_diffusion` (algebraic step of **Proposition 3.5**, arXiv 2606.15843): if
  `r = d` and `U ∈ ℝ^{r×d}` has orthonormal rows (`U Uᵀ = I_r`, (1.3)), then `P_U = Uᵀ U = I_d`,
  so the drift `(Id − P_U) v + P_U b` of the DLR SDE (1.5) equals `b` for every `v` (in particular
  `v = P_Y b`) and the diffusion `P_U σ` equals `σ`. This is the step of the paper's proof that
  reduces (1.5) to the original SDE (1.1). Not formalized: the conclusion
  `E[sup_t |X_t^{(r)} − X_t|²] = 0`, which follows by pathwise uniqueness for (1.1) and needs
  stochastic calculus that the library lacks.
* `prop_3_5_projY_eq_id`: when `r` equals the dimension of a finite-dimensional `E`, `P_Y = id`.
  This is NOT the paper's step: in the paper `P_Y` acts on the infinite-dimensional `L²(Ω)` and
  `r = d` refers to the state dimension, so `P_Y ≠ id` in general. At `r = d` the paper's drift
  is independent of `P_Y` because `Id − P_U = 0` (see `prop_3_5_drift_diffusion`). The lemma is
  kept as a statement about the abstract operator only.
* the unnamed `example`s at the end of the file: `U = I_2` satisfies the hypotheses of
  `prop_3_5_drift_diffusion`, and the basis of `EuclideanSpace ℝ (Fin 2)` those of
  `prop_3_5_projY_eq_id`, so neither theorem is vacuous.

Not formalized, and why:
* **Theorem 4.4** (uniform-in-time second moments): its proof applies Itô's formula to the
  DLRA SDE. The library has no Itô calculus for SDEs.
* **Theorem 4.5** (Wasserstein stability `W₂²(μ_t, ν_t) ≤ e^{δt} W₂²(μ, ν) + C(d−r)/|δ|`):
  needs Itô's formula and the Wasserstein-2 distance, which Mathlib lacks.
* **Example 4.6** (Ornstein–Uhlenbeck sharpness): needs the Gaussian (Bures) formula for `W₂`,
  which the library lacks.

Core definitions used from the library: `LeanDLRA.IsOrthProj`
(`LeanDLRA/Foundations/Projector.lean`) and its lemma `IsOrthProj.opNorm_le`. The file adds the
local definitions `gramY` and `projY`, which encode the paper's Gram formula for `P_Y`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2606_15843

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram matrix `C_Y = (⟪Y_i, Y_j⟫)_{i,j}` of a finite family. -/
noncomputable def gramY {r : ℕ} (Y : Fin r → E) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => ⟪Y i, Y j⟫

/-- The DLRA projector of the paper, `P_Y u = E[u Yᵀ] C_Y⁻¹ Y`, written with
`E[u Yᵀ]_j = ⟪u, Y_j⟫`: `P_Y u = ∑_i (∑_j ⟪u, Y_j⟫ (C_Y⁻¹)_{j i}) Y_i`. -/
noncomputable def projY {r : ℕ} (Y : Fin r → E) (u : E) : E :=
  ∑ i, (∑ j, ⟪u, Y j⟫ * (gramY Y)⁻¹ j i) • Y i

/-- Linear independence makes the Gram matrix invertible. -/
lemma gramY_isUnit {r : ℕ} {Y : Fin r → E} (hY : LinearIndependent ℝ Y) :
    IsUnit (gramY Y) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ c : Fin r → ℝ, gramY Y *ᵥ c = 0 → c = 0 := by
    intro c hc
    have h1 : ⟪∑ i, c i • Y i, ∑ i, c i • Y i⟫ = ∑ i, c i * (gramY Y *ᵥ c) i := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        Matrix.mulVec, dotProduct, gramY, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_comm (Y i) (Y j)]
      ring
    have h2 : ⟪∑ i, c i • Y i, ∑ i, c i • Y i⟫ = 0 := by
      rw [h1, hc]; simp
    have h3 : ∑ i, c i • Y i = 0 := inner_self_eq_zero.mp h2
    exact funext fun i => by simpa using Fintype.linearIndependent_iff.mp hY c h3 i
  intro c d hcd
  have hsub : gramY Y *ᵥ (c - d) = 0 := by rw [Matrix.mulVec_sub, hcd, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

/-- The span of a finite family is finite dimensional, hence complete, so its orthogonal
projection exists. -/
instance spanY_finiteDim {r : ℕ} (Y : Fin r → E) :
    FiniteDimensional ℝ (Submodule.span ℝ (Set.range Y)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range Y)

instance spanY_complete {r : ℕ} (Y : Fin r → E) :
    CompleteSpace (Submodule.span ℝ (Set.range Y)) :=
  FiniteDimensional.complete ℝ _

/-- `P_Y` is the orthogonal projection onto `span{Y_1, …, Y_r}`. -/
lemma projY_eq_starProjection {r : ℕ} {Y : Fin r → E} (hY : LinearIndependent ℝ Y) (u : E) :
    projY Y u = (Submodule.span ℝ (Set.range Y)).starProjection u := by
  have hinv : (gramY Y)⁻¹ * gramY Y = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gramY_isUnit hY))
  have hl : ∀ l, ⟪projY Y u, Y l⟫ = ⟪u, Y l⟫ := by
    intro l
    unfold projY
    rw [sum_inner]
    simp only [real_inner_smul_left, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hj : ∀ j, ∑ i, (⟪u, Y j⟫ * (gramY Y)⁻¹ j i) * ⟪Y i, Y l⟫
        = ⟪u, Y j⟫ * (1 : Matrix (Fin r) (Fin r) ℝ) j l := by
      intro j
      rw [← hinv, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [gramY, Matrix.of_apply]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j]
    simp [Matrix.one_apply]
  have hmem : projY Y u ∈ Submodule.span ℝ (Set.range Y) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem ?_).symm
  intro w hw
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  simp only [inner_sum, real_inner_smul_right]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [inner_sub_left, hl l, sub_self, mul_zero]

/-- **Lemma 3.4** of arXiv 2606.15843 (abstract form): for linearly independent `Y_1, …, Y_r`
the operator `P_Y u = E[u Yᵀ] C_Y⁻¹ Y` is an orthogonal projector with `‖P_Y‖ ≤ 1`.
The statement is on a real inner product space `E`; see the module docstring. -/
theorem lemma_3_4_projY {r : ℕ} {Y : Fin r → E} (hY : LinearIndependent ℝ Y) :
    ∃ P : E →L[ℝ] E, (∀ u, P u = projY Y u) ∧ IsOrthProj P ∧ ‖P‖ ≤ 1 := by
  refine ⟨(Submodule.span ℝ (Set.range Y)).starProjection,
    fun u => (projY_eq_starProjection hY u).symm, ?_, ?_⟩
  · refine ⟨fun x => Submodule.starProjection_eq_self_iff.mpr
      ((Submodule.span ℝ (Set.range Y)).starProjection_apply_mem x), fun x y => ?_⟩
    exact (Submodule.span ℝ (Set.range Y)).starProjection_isSymmetric x y
  · refine IsOrthProj.opNorm_le ?_
    refine ⟨fun x => Submodule.starProjection_eq_self_iff.mpr
      ((Submodule.span ℝ (Set.range Y)).starProjection_apply_mem x), fun x y => ?_⟩
    exact (Submodule.span ℝ (Set.range Y)).starProjection_isSymmetric x y

/-- Full-rank property of the abstract operator `P_Y`: when `r` equals the dimension of a
finite-dimensional `E` and `Y` is linearly independent, `P_Y u = u` for all `u`. This is not the
step of Proposition 3.5 of arXiv 2606.15843 (there `P_Y` acts on `L²(Ω)` and `r = d` is the state
dimension); that step is `prop_3_5_drift_diffusion`. -/
theorem prop_3_5_projY_eq_id [FiniteDimensional ℝ E] {r : ℕ} {Y : Fin r → E}
    (hY : LinearIndependent ℝ Y) (hr : r = Module.finrank ℝ E) (u : E) :
    projY Y u = u := by
  have hspan : Submodule.span ℝ (Set.range Y) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hY (by simpa using hr)
  rw [projY_eq_starProjection hY]
  refine Submodule.starProjection_eq_self_iff.mpr ?_
  rw [hspan]
  exact Submodule.mem_top

/-- **Algebraic step of Proposition 3.5** of arXiv 2606.15843. Let `r = d` and let
`U ∈ ℝ^{r×d}` have orthonormal rows, `U Uᵀ = I_r` (condition (1.3)). Then the row-space projector
is `P_U = Uᵀ U = I_d`, the drift `(Id − P_U) v + P_U b` of the DLR SDE (1.5) equals `b` for every
`v` (the paper has `v = P_Y b(t, X_t^{(r)})`), and the diffusion `P_U σ` equals `σ`. So at full
rank (1.5) is the original SDE (1.1), as in the paper's proof. The step from here to
`E[sup_t |X_t^{(r)} − X_t|²] = 0` (pathwise uniqueness for (1.1)) is not formalized. -/
theorem prop_3_5_drift_diffusion {r d m : ℕ} (hr : r = d) (U : Matrix (Fin r) (Fin d) ℝ)
    (hU : U * Uᵀ = 1) (v b : Fin d → ℝ) (σ : Matrix (Fin d) (Fin m) ℝ) :
    Uᵀ * U = 1 ∧ (1 - Uᵀ * U) *ᵥ v + (Uᵀ * U) *ᵥ b = b ∧ (Uᵀ * U) * σ = σ := by
  subst hr
  have h : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  refine ⟨h, ?_, ?_⟩
  · rw [h, sub_self, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec]
  · rw [h, Matrix.one_mul]

/-- Non-vacuity: `U = I_2` has orthonormal rows with `r = d = 2`. -/
example (v b : Fin 2 → ℝ) (σ : Matrix (Fin 2) (Fin 3) ℝ) :
    (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) *ᵥ v + ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) *ᵥ b
      = b :=
  (prop_3_5_drift_diffusion rfl (1 : Matrix (Fin 2) (Fin 2) ℝ) (by simp) v b σ).2.1

/-- Non-vacuity: the standard orthonormal basis of `EuclideanSpace ℝ (Fin 2)` is linearly
independent with `r = 2 = dim`, so the hypotheses of `prop_3_5_projY_eq_id` are satisfiable and
the conclusion `P_Y = id` is attained. -/
example (u : EuclideanSpace ℝ (Fin 2)) :
    projY (⇑(EuclideanSpace.basisFun (Fin 2) ℝ)) u = u :=
  prop_3_5_projY_eq_id (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.linearIndependent
    (by simp) u

end LeanDLRA.Literature.P2606_15843
