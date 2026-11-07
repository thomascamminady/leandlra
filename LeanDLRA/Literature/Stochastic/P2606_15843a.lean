import Mathlib
import LeanDLRA.Foundations.Projector

/-!
# Results of arXiv 2606.15843: Long-time behaviour of DLRA for SDEs

This module formalizes the abstract linear-algebra core of the DLRA projector `P_Y` of the paper
(Lemma 3.4 and the algebraic part of Proposition 3.5), on a real inner product space `E`.

* `gramY`, `projY`: the Gram matrix `C_Y = (⟪Y_i, Y_j⟫)` and the explicit operator
  `P_Y u = E[u Yᵀ] C_Y⁻¹ Y` of the paper, where `E[u Yᵀ]_j = ⟪u, Y_j⟫`.
* `gramY_isUnit`: linear independence of `Y` makes `C_Y` invertible (the paper assumes this).
* `projY_eq_starProjection`: `P_Y` is the orthogonal projection onto `span{Y_1, …, Y_r}`.
* `lemma_3_4_projY` (**Lemma 3.4**, arXiv 2606.15843, abstract form): `P_Y` is an orthogonal
  projector with `‖P_Y‖ ≤ 1`. It is stated on a real inner product space `E`, not on the
  `ℝ^d`-valued `L²(Ω; ℝ^d)` of the paper. The `ℝ^d`-valued operator acts componentwise, and that
  componentwise statement is not proved in this file. The paper's standing hypothesis that
  `Y_1, …, Y_r` are linearly independent is kept.
* `prop_3_5_projY_eq_id` (algebraic part of **Proposition 3.5**, arXiv 2606.15843): when `r` equals
  the dimension of `E`, `P_Y = id`. This is the identity the paper uses to show that the DLR
  equation reduces to the original SDE at full rank.
  Not formalized: the SDE consequence (that the DLRA SDE coincides with the original SDE and the
  `L²(Ω)` consistency via uniqueness). That needs stochastic calculus that the library lacks.
* the unnamed `example` at the end of the file: the basis of `EuclideanSpace ℝ (Fin 2)` satisfies
  the hypotheses of Proposition 3.5 with `r = 2`, so the theorem is not vacuous.

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

/-- **Algebraic part of Proposition 3.5** of arXiv 2606.15843: when `r` equals the dimension of
`E` and `Y` is linearly independent, `P_Y u = u` for all `u`. -/
theorem prop_3_5_projY_eq_id [FiniteDimensional ℝ E] {r : ℕ} {Y : Fin r → E}
    (hY : LinearIndependent ℝ Y) (hr : r = Module.finrank ℝ E) (u : E) :
    projY Y u = u := by
  have hspan : Submodule.span ℝ (Set.range Y) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hY (by simpa using hr)
  rw [projY_eq_starProjection hY]
  refine Submodule.starProjection_eq_self_iff.mpr ?_
  rw [hspan]
  exact Submodule.mem_top

/-- Non-vacuity: the standard orthonormal basis of `EuclideanSpace ℝ (Fin 2)` is linearly
independent with `r = 2 = dim`, so Proposition 3.5's hypotheses are satisfiable and the
conclusion `P_Y = id` is attained. -/
example (u : EuclideanSpace ℝ (Fin 2)) :
    projY (⇑(EuclideanSpace.basisFun (Fin 2) ℝ)) u = u :=
  prop_3_5_projY_eq_id (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.linearIndependent
    (by simp) u

end LeanDLRA.Literature.P2606_15843
