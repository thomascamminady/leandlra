import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Foundations.Existence
import LeanDLRA.Integrators.Matrix.ParallelBUG
import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Research.SameMinibatchAugmentation
import LeanDLRA.Training.Descent
import LeanDLRA.Training.GradientFlowConvergence

/-!
# Results of arXiv 2410.18720: GeoLoRA, low-rank neural network training

Algorithm 1 of the paper, on real matrices with the Frobenius norm, and its analysis.  One iteration
is `IsGeoLoRAStep` / `IsGeoLoRAUpdate`: the factor updates (6) with the factor gradients of the
chain rule, the augmented bases (7), the assembly (8), and any truncation.  `geoWhat_eq` proves
`Ŵ = W₀ - λ P(W₀) G`, `truncation_spec` the error of the SVD truncation, and `tangentAt` is the
tangent projector `P(W)` of (18) as a function of `W` alone, with `tangentAt_eq` and a measurability
proof.  **Thm 6**: `update_eq_euler`, `hasDerivWithinAt_KL_of_factorODE`, `odeSolution_frozen_lift`.
**Thm 1**: the printed bound is false (`LeanDLRA.StochasticDescent.SameBatchExample`,
`geoLoRA_bound_false`, `geoLoRA_bound_false_mainText`); `descent_estimate` and
`descent_estimate_of_variance` are the corrected statements, with expectations on a general
probability space; the deterministic abstract form is `LeanDLRA.loss_truncated_geoLoRAStep_le`.
**Thm 2**: `convergence`, with a filtration, conditional unbiasedness (`condExp_sample_eq` for
independent minibatches) and the tower property; with the stochastic gradient in the conclusion,
as printed, it is false (`stochastic_conclusion_false`).  The abstract deterministic form is
`LeanDLRA.frequently_geoLoRA_tangentGrad_sq_lt`.  **Thm 3**: `error_bound`, `riemannian_flow_close`,
`theorem3`; constants that depend only on `L` and `B`, as printed, do not exist
(`not_uniformErrorBound`), since they must contain `T e^{βT}`.  **Props 1–3**: on a block mask
`Π Z = ∑ᵢ Eᵢ Z Fᵢ` (`blockMask`), which contains the mask `M ⊙ ·` of App. I
(`blockMask_adjacency`), `multilayer_step` and `global_truncation` are Prop. 1,
`mem_range_blockMask_of_flow` (with `mem_range_blockMask_of_continuous`, `exists_flow_instance`) is
Prop. 2, whose proof in the paper is circular, and `block_flow_iff` is Prop. 3.  Differences from
the paper are in the docstrings: the gradient bound `B` replaces `L` in the truncation term of
Thm 1, criterion (9) controls `‖W₁ - Ŵ‖²`, not `‖W₁ - Ŵ‖` (`truncation_spec`), and the fixed-point
model of the network plays no role.  The zero initialisation `S₀ = 0` of Sec. 4.1, where `S₀⁻¹`
is replaced by `I`, and the numerics are not formalized.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2410_18720

open LeanDLRA.MatrixParallelBUG

/-! ### Factor gradients and the update (6) -/

section Factors

/-- Chain rule for a linear reparametrisation: if `ℒ` has gradient `G` at `T x` and
`⟪G, T y⟫ = ⟪G', y⟫` for all `y`, then `ℒ ∘ T` has gradient `G'` at `x`. -/
theorem hasFDerivAt_comp_clm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ℒ : E → ℝ} (T : F →L[ℝ] E) {x : F} {G : E}
    {G' : F} (hT : ∀ y, ⟪G, T y⟫ = ⟪G', y⟫) (hℒ : HasFDerivAt ℒ (innerSL ℝ G) (T x)) :
    HasFDerivAt (fun y => ℒ (T y)) (innerSL ℝ G') x := by
  have e : innerSL ℝ G' = (innerSL ℝ G).comp T := by
    ext y
    simp [hT]
  rw [e]
  exact hℒ.comp x T.hasFDerivAt

/-- A gradient is unique. -/
theorem gradient_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ}
    {x G G' : E} (h : HasFDerivAt f (innerSL ℝ G) x) (h' : HasFDerivAt f (innerSL ℝ G') x) :
    G = G' := by
  have e := h.unique h'
  refine ext_inner_right ℝ fun y => ?_
  simpa using congrArg (fun φ : E →L[ℝ] ℝ => φ y) e

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable {ℒ : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ}

/-- `∇_U ℒ(U S Vᵀ) = ∇ℒ(U S Vᵀ) V Sᵀ` (chain rule, arXiv 2410.18720, proof of Thm 6; eq. (2) of the
paper prints `V S`, which agrees for the diagonal `S` of Algorithm 1). -/
theorem hasFDerivAt_factorU {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun X : Matrix m r ℝ => ℒ (X * S * Vᵀ)) (innerSL ℝ (G * V * Sᵀ)) U := by
  have e : ∀ X : Matrix m r ℝ, X * S * Vᵀ = Frobenius.rightMulCLM (S * Vᵀ) X := fun X => by
    simp [Matrix.mul_assoc]
  simp only [e] at h ⊢
  refine hasFDerivAt_comp_clm _ (fun Y => ?_) h
  rw [Frobenius.rightMulCLM_apply, Frobenius.inner_mul_right' G Y, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `∇_V ℒ(U S Vᵀ) = ∇ℒ(U S Vᵀ)ᵀ U S` (chain rule, arXiv 2410.18720, proof of Thm 6; eq. (2) of the
paper prints `U Sᵀ`, which agrees for the diagonal `S` of Algorithm 1). -/
theorem hasFDerivAt_factorV {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun X : Matrix n r ℝ => ℒ (U * S * Xᵀ)) (innerSL ℝ (Gᵀ * U * S)) V := by
  let T : Matrix n r ℝ →L[ℝ] Matrix m n ℝ :=
    (Frobenius.leftMulCLM (U * S)).comp Frobenius.transposeCLM
  have e : ∀ X : Matrix n r ℝ, U * S * Xᵀ = T X := fun _ => rfl
  simp only [e] at h ⊢
  refine hasFDerivAt_comp_clm T (fun Y => ?_) h
  rw [← e, Frobenius.inner_mul_left' G (U * S) Yᵀ, ← Frobenius.inner_transpose,
    Matrix.transpose_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `∇_S ℒ(U S Vᵀ) = Uᵀ ∇ℒ(U S Vᵀ) V`. -/
theorem hasFDerivAt_factorS {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun X : Matrix r r ℝ => ℒ (U * X * Vᵀ)) (innerSL ℝ (Uᵀ * G * V)) S := by
  let T : Matrix r r ℝ →L[ℝ] Matrix m n ℝ :=
    (Frobenius.leftMulCLM U).comp (Frobenius.rightMulCLM Vᵀ)
  have e : ∀ X : Matrix r r ℝ, U * X * Vᵀ = T X := fun X => by
    simp [T, Matrix.mul_assoc]
  simp only [e] at h ⊢
  refine hasFDerivAt_comp_clm T (fun Y => ?_) h
  rw [← e, Matrix.mul_assoc, Frobenius.inner_mul_left' G U (Y * Vᵀ),
    Frobenius.inner_mul_right' _ Y, Matrix.transpose_transpose]

/-- `∇_K ℒ(K Vᵀ) = ∇ℒ(K Vᵀ) V`. -/
theorem hasFDerivAt_factorK {K : Matrix m r ℝ} {V : Matrix n r ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (K * Vᵀ)) :
    HasFDerivAt (fun X : Matrix m r ℝ => ℒ (X * Vᵀ)) (innerSL ℝ (G * V)) K := by
  have e : ∀ X : Matrix m r ℝ, X * Vᵀ = Frobenius.rightMulCLM Vᵀ X := fun _ => rfl
  simp only [e] at h ⊢
  refine hasFDerivAt_comp_clm _ (fun Y => ?_) h
  rw [Frobenius.rightMulCLM_apply, Frobenius.inner_mul_right' G Y, Matrix.transpose_transpose]

/-- `∇_L ℒ(U Lᵀ) = ∇ℒ(U Lᵀ)ᵀ U`. -/
theorem hasFDerivAt_factorL {U : Matrix m r ℝ} {L : Matrix n r ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (U * Lᵀ)) :
    HasFDerivAt (fun X : Matrix n r ℝ => ℒ (U * Xᵀ)) (innerSL ℝ (Gᵀ * U)) L := by
  let T : Matrix n r ℝ →L[ℝ] Matrix m n ℝ := (Frobenius.leftMulCLM U).comp Frobenius.transposeCLM
  have e : ∀ X : Matrix n r ℝ, U * Xᵀ = T X := fun _ => rfl
  simp only [e] at h ⊢
  refine hasFDerivAt_comp_clm T (fun Y => ?_) h
  rw [← e, Frobenius.inner_mul_left' G U Yᵀ, ← Frobenius.inner_transpose,
    Matrix.transpose_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The update (6) of `S`: `S^new = S₀ - λ GS` for the gradient `GS = ∇_S ℒ` (arXiv 2410.18720,
eq. (6)). -/
def sNew (S₀ GS : Matrix r r ℝ) (lr : ℝ) : Matrix r r ℝ := S₀ - lr • GS

/-- The update (6) of `K`: `K^new = U₀ S₀ - λ GU S₀⁻ᵀ` for `GU = ∇_U ℒ` (arXiv 2410.18720,
eq. (6)). -/
noncomputable def kNew [DecidableEq r] (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (GU : Matrix m r ℝ) (lr : ℝ) : Matrix m r ℝ :=
  U₀ * S₀ - lr • (GU * (S₀⁻¹)ᵀ)

/-- The update (6) of `L`: `L^new = V₀ S₀ᵀ - λ GV S₀⁻¹` for `GV = ∇_V ℒ` (arXiv 2410.18720,
eq. (6)). -/
noncomputable def lNew [DecidableEq r] (V₀ : Matrix n r ℝ) (S₀ : Matrix r r ℝ)
    (GV : Matrix n r ℝ) (lr : ℝ) : Matrix n r ℝ :=
  V₀ * S₀ᵀ - lr • (GV * S₀⁻¹)

/-- The robust gradient of the `K`-equation of (27): `K ↦ ∇ℒ(K V₀ᵀ) V₀`. -/
def gradK (g : Matrix m n ℝ → Matrix m n ℝ) (V₀ : Matrix n r ℝ) (K : Matrix m r ℝ) :
    Matrix m r ℝ :=
  g (K * V₀ᵀ) * V₀

/-- The robust gradient of the `L`-equation of (27): `L ↦ ∇ℒ(U₀ Lᵀ)ᵀ U₀`. -/
def gradL (g : Matrix m n ℝ → Matrix m n ℝ) (U₀ : Matrix m r ℝ) (L : Matrix n r ℝ) :
    Matrix n r ℝ :=
  (g (U₀ * Lᵀ))ᵀ * U₀

/-- The gradient of the `S`-equation of (27): `S ↦ U₀ᵀ ∇ℒ(U₀ S V₀ᵀ) V₀`. -/
def gradS (g : Matrix m n ℝ → Matrix m n ℝ) (U₀ : Matrix m r ℝ) (V₀ : Matrix n r ℝ)
    (S : Matrix r r ℝ) : Matrix r r ℝ :=
  U₀ᵀ * g (U₀ * S * V₀ᵀ) * V₀

variable {g : Matrix m n ℝ → Matrix m n ℝ}

/-- **The right-hand sides of (27) are the gradients of the frozen-basis losses**
(arXiv 2410.18720, Thm 6): `-gradK`, `-gradL`, `-gradS` are `-∇_K ℒ(K V₀ᵀ)`, `-∇_L ℒ(U₀ Lᵀ)` and
`-∇_S ℒ(U₀ S V₀ᵀ)`.  (`ℒ` may be the stochastic loss of a fixed sample.) -/
theorem hasFDerivAt_frozen (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (U₀ : Matrix m r ℝ)
    (V₀ : Matrix n r ℝ) :
    (∀ K, HasFDerivAt (fun X => ℒ (X * V₀ᵀ)) (innerSL ℝ (gradK g V₀ K)) K) ∧
    (∀ L, HasFDerivAt (fun X => ℒ (U₀ * Xᵀ)) (innerSL ℝ (gradL g U₀ L)) L) ∧
    (∀ S, HasFDerivAt (fun X => ℒ (U₀ * X * V₀ᵀ)) (innerSL ℝ (gradS g U₀ V₀ S)) S) :=
  ⟨fun _ => hasFDerivAt_factorK (hℒ _), fun _ => hasFDerivAt_factorL (hℒ _),
    fun _ => hasFDerivAt_factorS (hℒ _)⟩

variable [DecidableEq r]

omit [Fintype m] in
/-- With the chain rule the `S⁻¹` in (6) cancels: `K^new = U₀ S₀ - λ G V₀`. -/
theorem kNew_eq {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : IsUnit S₀.det) (V₀ : Matrix n r ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) :
    kNew U₀ S₀ (G * V₀ * S₀ᵀ) lr = U₀ * S₀ - lr • (G * V₀) := by
  rw [kNew, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hS₀,
    Matrix.transpose_one, Matrix.mul_one]

omit [Fintype n] in
/-- With the chain rule the `S⁻¹` in (6) cancels: `L^new = V₀ S₀ᵀ - λ Gᵀ U₀`. -/
theorem lNew_eq {V₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : IsUnit S₀.det) (U₀ : Matrix m r ℝ)
    (G : Matrix m n ℝ) (lr : ℝ) :
    lNew V₀ S₀ (Gᵀ * U₀ * S₀) lr = V₀ * S₀ᵀ - lr • (Gᵀ * U₀) := by
  rw [lNew, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS₀, Matrix.mul_one]

/-- **Thm 6 of arXiv 2410.18720, discrete part: the update (6) is the explicit Euler step of (27).**
Let `ℒ` have gradient `g`, let `S₀` be invertible, and let `GU`, `GV`, `GS` be the gradients of
`U ↦ ℒ(U S₀ V₀ᵀ)`, `V ↦ ℒ(U₀ S₀ Vᵀ)`, `S ↦ ℒ(U₀ S V₀ᵀ)` used by Algorithm 1 (they are unique).  Then
`K^new`, `L^new`, `S^new` of (6) are one explicit Euler step of size `λ` of
`K̇ = -∇_K ℒ(K V₀ᵀ)`, `L̇ = -∇_L ℒ(U₀ Lᵀ)`, `Ṡ = -∇_S ℒ(U₀ S V₀ᵀ)` from
`K(0) = U₀ S₀`, `L(0) = V₀ S₀ᵀ`, `S(0) = S₀`.  (The paper prints `L(0) = S₀ᵀ V₀`, which has the
wrong shape.)  No orthonormality is needed here. -/
theorem update_eq_euler (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) {U₀ : Matrix m r ℝ}
    {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} (hS₀ : IsUnit S₀.det) {GU : Matrix m r ℝ}
    {GV : Matrix n r ℝ} {GS : Matrix r r ℝ}
    (hGU : HasFDerivAt (fun X => ℒ (X * S₀ * V₀ᵀ)) (innerSL ℝ GU) U₀)
    (hGV : HasFDerivAt (fun X => ℒ (U₀ * S₀ * Xᵀ)) (innerSL ℝ GV) V₀)
    (hGS : HasFDerivAt (fun X => ℒ (U₀ * X * V₀ᵀ)) (innerSL ℝ GS) S₀) (lr : ℝ) :
    kNew U₀ S₀ GU lr = U₀ * S₀ - lr • gradK g V₀ (U₀ * S₀) ∧
    lNew V₀ S₀ GV lr = V₀ * S₀ᵀ - lr • gradL g U₀ (V₀ * S₀ᵀ) ∧
    sNew S₀ GS lr = S₀ - lr • gradS g U₀ V₀ S₀ := by
  have e : U₀ * (V₀ * S₀ᵀ)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [gradient_unique hGU (hasFDerivAt_factorU (hℒ _)), kNew_eq hS₀, gradK]
  · rw [gradient_unique hGV (hasFDerivAt_factorV (hℒ _)), lNew_eq hS₀, gradL, e]
  · rw [gradient_unique hGS (hasFDerivAt_factorS (hℒ _)), sNew, gradS]

/-- **Thm 6 of arXiv 2410.18720, continuous part (eq. (28)).**  If at time `t` the factors of the
Riemannian flow satisfy eq. (4), `U̇ = -(I - U Uᵀ) G V S⁻¹`, `Ṡ = -Uᵀ G V`,
`V̇ = -(I - V Vᵀ) Gᵀ U S⁻ᵀ` with `S t` invertible, then `K = U S` and `L = V Sᵀ` satisfy
`K̇ = -G V` and `L̇ = -Gᵀ U`: the `S⁻¹` disappears.  (Orthonormality is not needed.) -/
theorem hasDerivWithinAt_KL_of_factorODE [DecidableEq m] [DecidableEq n]
    {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {G : Matrix m n ℝ}
    {s : Set ℝ} {t : ℝ} (hdet : IsUnit (S t).det)
    (hU : HasDerivWithinAt U (-((1 - U t * (U t)ᵀ) * G * V t * (S t)⁻¹)) s t)
    (hS : HasDerivWithinAt S (-((U t)ᵀ * G * V t)) s t)
    (hV : HasDerivWithinAt V (-((1 - V t * (V t)ᵀ) * Gᵀ * U t * ((S t)⁻¹)ᵀ)) s t) :
    HasDerivWithinAt (fun τ => U τ * S τ) (-(G * V t)) s t ∧
      HasDerivWithinAt (fun τ => V τ * (S τ)ᵀ) (-(Gᵀ * U t)) s t := by
  constructor
  · have h := Frobenius.hasDerivWithinAt_mul hU hS
    convert h using 1
    rw [Matrix.neg_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hdet, Matrix.mul_neg]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  · have h := Frobenius.hasDerivWithinAt_mul hV (Frobenius.hasDerivWithinAt_transpose hS)
    convert h using 1
    have e : ((S t)⁻¹)ᵀ * (S t)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one]
    rw [Matrix.neg_mul, Matrix.mul_assoc _ (((S t)⁻¹)ᵀ), e, Matrix.mul_one, Matrix.transpose_neg,
      Matrix.mul_neg]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    abel

omit [DecidableEq r] in
/-- **Thm 6 of arXiv 2410.18720, link with the BUG substeps.**  The frozen-basis flows (27), lifted
to the full space, are the parallel BUG substeps of `Ẇ = -∇ℒ(W)`: `YK = K V₀ᵀ`, `YL = U₀ Lᵀ`,
`YS = U₀ S V₀ᵀ` solve `YK' = -Q₀ ∇ℒ(YK)`, `YL' = -P₀ ∇ℒ(YL)`, `YS' = -P₀ Q₀ ∇ℒ(YS)`, where
`P₀ = leftProj U₀`, `Q₀ = rightProj V₀`. -/
theorem odeSolution_frozen_lift {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {a b : ℝ}
    {K : ℝ → Matrix m r ℝ} {L : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ}
    (hK : ODESolution (fun _ X => -gradK g V₀ X) K a b)
    (hL : ODESolution (fun _ X => -gradL g U₀ X) L a b)
    (hS : ODESolution (fun _ X => -gradS g U₀ V₀ X) S a b) :
    ODESolution (fun _ Y => rightProj V₀ (-g Y)) (fun t => K t * V₀ᵀ) a b ∧
    ODESolution (fun _ Y => leftProj U₀ (-g Y)) (fun t => U₀ * (L t)ᵀ) a b ∧
    ODESolution (fun _ Y => leftProj U₀ (rightProj V₀ (-g Y))) (fun t => U₀ * S t * V₀ᵀ) a b := by
  refine ⟨MatrixKSL.odeSolution_kField (F := fun _ Y => -g Y) ⟨hK.cont, fun t ht => ?_⟩,
    MatrixKSL.odeSolution_lField (F := fun _ Y => -g Y) ⟨hL.cont, fun t ht => ?_⟩,
    odeSolution_sField (F := fun _ Y => -g Y) ⟨hS.cont, fun t ht => ?_⟩⟩
  · simpa [MatrixKSL.kField, gradK, Matrix.neg_mul] using hK.deriv t ht
  · simpa [MatrixKSL.lField, gradL, Matrix.neg_mul, Matrix.transpose_neg] using hL.deriv t ht
  · simpa [sField, gradS, Matrix.neg_mul, Matrix.mul_neg] using hS.deriv t ht

end Factors

/-! ### One iteration of Algorithm 1 -/

section Step

variable {m n r s s' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s] [Fintype s']
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] [DecidableEq s']

/-- **One iteration of Algorithm 1 of arXiv 2410.18720** at `W₀ = U₀ S₀ V₀ᵀ`, with the (possibly
stochastic) ambient gradient `G`: `U₀`, `V₀` orthonormal and `S₀` invertible (Algorithm 1 takes it
diagonal), the factor gradients are those of the chain rule, `∇_U = G V₀ S₀ᵀ`, `∇_V = Gᵀ U₀ S₀`,
`∇_S = U₀ᵀ G V₀`, and `Û = [U₀, Ũ]`, `V̂ = [V₀, Ṽ]` are orthonormal with the ranges of `Û`, `V̂`
containing `K^new`, `L^new` (eq. (7), `ortho([U₀, K^new])` and `ortho([V₀, L^new])`).
The number of new columns is free, as in rank-deficient QR. -/
structure IsGeoLoRAStep (G : Matrix m n ℝ) (lr : ℝ) (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (Ut : Matrix m s ℝ) (Vt : Matrix n s' ℝ) : Prop where
  orthU : U₀ᵀ * U₀ = 1
  orthV : V₀ᵀ * V₀ = 1
  detS : IsUnit S₀.det
  orthUhat : (Matrix.fromCols U₀ Ut)ᵀ * Matrix.fromCols U₀ Ut = 1
  orthVhat : (Matrix.fromCols V₀ Vt)ᵀ * Matrix.fromCols V₀ Vt = 1
  capK : Matrix.fromCols U₀ Ut * (Matrix.fromCols U₀ Ut)ᵀ * kNew U₀ S₀ (G * V₀ * S₀ᵀ) lr =
    kNew U₀ S₀ (G * V₀ * S₀ᵀ) lr
  capL : Matrix.fromCols V₀ Vt * (Matrix.fromCols V₀ Vt)ᵀ * lNew V₀ S₀ (Gᵀ * U₀ * S₀) lr =
    lNew V₀ S₀ (Gᵀ * U₀ * S₀) lr

/-- The iterate before truncation, `Ŵ = Û Ŝ V̂ᵀ` with the coefficient matrix `Ŝ` of eq. (8) of
arXiv 2410.18720, `Ŝ = [[S^new, L^new,ᵀ Ṽ], [Ũᵀ K^new, 0]]`. -/
noncomputable def geoWhat (G : Matrix m n ℝ) (lr : ℝ) (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (Ut : Matrix m s ℝ) (Vt : Matrix n s' ℝ) : Matrix m n ℝ :=
  augmented U₀ Ut V₀ Vt (sNew S₀ (U₀ᵀ * G * V₀) lr) (kNew U₀ S₀ (G * V₀ * S₀ᵀ) lr)
    (lNew V₀ S₀ (Gᵀ * U₀ * S₀) lr)

omit [Fintype r] [Fintype s] [DecidableEq m] in
/-- The blocks of an orthonormal `[U₀, Ũ]`. -/
lemma fromCols_orth {U₀ : Matrix m r ℝ} {Ut : Matrix m s ℝ}
    (h : (Matrix.fromCols U₀ Ut)ᵀ * Matrix.fromCols U₀ Ut = 1) :
    Utᵀ * U₀ = 0 ∧ Utᵀ * Ut = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at h
  obtain ⟨-, -, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  exact ⟨h3, h4⟩

/-- If the orthonormal `[U₀, Ũ]` contains `K`, the new directions capture `(I - U₀U₀ᵀ) K`. -/
lemma capture_of_fromCols {U₀ : Matrix m r ℝ} {Ut : Matrix m s ℝ} {k : Type*} {K : Matrix m k ℝ}
    (h : (Matrix.fromCols U₀ Ut)ᵀ * Matrix.fromCols U₀ Ut = 1)
    (hK : Matrix.fromCols U₀ Ut * (Matrix.fromCols U₀ Ut)ᵀ * K = K) :
    Ut * Utᵀ * ((1 - U₀ * U₀ᵀ) * K) = (1 - U₀ * U₀ᵀ) * K := by
  have h1 : (1 - U₀ * U₀ᵀ) * K = Ut * Utᵀ * K := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, Matrix.add_mul] at hK
    rw [Matrix.sub_mul, Matrix.one_mul]
    nth_rewrite 1 [← hK]
    abel
  have h2 : Ut * Utᵀ * (Ut * Utᵀ * K) = Ut * (Utᵀ * Ut) * Utᵀ * K := by
    simp only [Matrix.mul_assoc]
  rw [h1, h2, (fromCols_orth h).2, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] in
/-- The parallel BUG update with the Euler substeps of (6). -/
lemma parallelBUG_update {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU : U₀ᵀ * U₀ = 1)
    (hV : V₀ᵀ * V₀ = 1) (S₀ : Matrix r r ℝ) (G : Matrix m n ℝ) (lr : ℝ) :
    parallelBUG (leftProj U₀) (rightProj V₀) ((U₀ * S₀ - lr • (G * V₀)) * V₀ᵀ)
        (U₀ * (V₀ * S₀ᵀ - lr • (Gᵀ * U₀))ᵀ) (U₀ * sNew S₀ (U₀ᵀ * G * V₀) lr * V₀ᵀ) =
      U₀ * S₀ * V₀ᵀ - lr • tangentProj U₀ V₀ G := by
  have hPY : leftProj U₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [Matrix.mul_assoc]; exact leftProj_mul_left hU _
  have hQY : rightProj V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := rightProj_mul_transpose hV _
  have e1 : (U₀ * S₀ - lr • (G * V₀)) * V₀ᵀ =
      U₀ * S₀ * V₀ᵀ + (-lr) • rightProj V₀ G := by
    rw [Matrix.sub_mul, Matrix.smul_mul, rightProj_apply, neg_smul]
    abel
  have e2 : U₀ * (V₀ * S₀ᵀ - lr • (Gᵀ * U₀))ᵀ =
      U₀ * S₀ * V₀ᵀ + (-lr) • leftProj U₀ G := by
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_smul, leftProj_apply, neg_smul]
    rw [Matrix.mul_assoc U₀ S₀, Matrix.mul_assoc U₀ U₀ᵀ G]
    abel
  have e3 : U₀ * sNew S₀ (U₀ᵀ * G * V₀) lr * V₀ᵀ =
      U₀ * S₀ * V₀ᵀ + (-lr) • leftProj U₀ (rightProj V₀ G) := by
    rw [leftProj_rightProj_apply, sNew, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, neg_smul]
    abel
  have e4 : tangentProj U₀ V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ :=
    tangentProj_mul_mul_transpose hU V₀ S₀
  rw [e1, e2, e3, parallelBUG_euler (leftProj_rightProj_comm U₀ V₀) hPY hQY]
  change tangentProj U₀ V₀ _ = _
  rw [map_add, map_smul, e4, neg_smul, sub_eq_add_neg]

omit [DecidableEq m] [DecidableEq n] in
/-- **The assembled update is the tangent-projected gradient step** (arXiv 2410.18720, proof of
Thm 1/Thm 4): `Ŵ = Û Ŝ V̂ᵀ = W₀ - λ P(W₀) G` with the tangent projector at `W₀ = U₀ S₀ V₀ᵀ`
of eq. (18).  This holds for every `G`, in particular for a stochastic gradient. -/
theorem geoWhat_eq {G : Matrix m n ℝ} {lr : ℝ} {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {Ut : Matrix m s ℝ} {Vt : Matrix n s' ℝ}
    (h : IsGeoLoRAStep G lr U₀ S₀ V₀ Ut Vt) :
    geoWhat G lr U₀ S₀ V₀ Ut Vt = U₀ * S₀ * V₀ᵀ - lr • tangentProj U₀ V₀ G := by
  classical
  have hK := kNew_eq (U₀ := U₀) h.detS V₀ G lr
  have hL := lNew_eq (V₀ := V₀) h.detS U₀ G lr
  have hcK := capture_of_fromCols h.orthUhat h.capK
  have hcL := capture_of_fromCols h.orthVhat h.capL
  have e := augmented_eq_parallelBUG (U₀ := U₀) (V₀ := V₀)
    (sNew S₀ (U₀ᵀ * G * V₀) lr) (fromCols_orth h.orthUhat).1 hcK (fromCols_orth h.orthVhat).1 hcL
  rw [hK, hL] at e
  rw [geoWhat, hK, hL, e]
  exact parallelBUG_update h.orthU h.orthV S₀ G lr

omit [DecidableEq m] [DecidableEq n] in
/-- **Algorithm 1 can always be run** (non-vacuity of `IsGeoLoRAStep`): if `2 r` does not exceed the
matrix dimensions, the augmented bases of eq. (7) with `r` new columns exist for every `G`. -/
theorem exists_isGeoLoRAStep {r : ℕ} {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
    {V₀ : Matrix n (Fin r) ℝ} (hU : U₀ᵀ * U₀ = 1) (hV : V₀ᵀ * V₀ = 1) (hS : IsUnit S₀.det)
    (G : Matrix m n ℝ) (lr : ℝ) (hm : r + r ≤ Fintype.card m) (hn : r + r ≤ Fintype.card n) :
    ∃ (Ut : Matrix m (Fin r) ℝ) (Vt : Matrix n (Fin r) ℝ),
      IsGeoLoRAStep G lr U₀ S₀ V₀ Ut Vt := by
  obtain ⟨Ut, -, -, h1, h2, -⟩ :=
    exists_parallel_augmented_basis U₀ hU (kNew U₀ S₀ (G * V₀ * S₀ᵀ) lr) hm
  obtain ⟨Vt, -, -, h3, h4, -⟩ :=
    exists_parallel_augmented_basis V₀ hV (lNew V₀ S₀ (Gᵀ * U₀ * S₀) lr) hn
  exact ⟨Ut, Vt, hU, hV, hS, h1, h3, h2, h4⟩

end Step

/-! ### The truncation step -/

section Truncation

variable {m n ρ ρ' κ : Type*} [Fintype m] [Fintype n] [Fintype ρ] [Fintype ρ'] [Fintype κ]
  [DecidableEq κ]

/-- The Frobenius norm of a diagonal matrix. -/
lemma norm_sq_diagonal (d : κ → ℝ) : ‖(Matrix.diagonal d : Matrix κ κ ℝ)‖ ^ 2 = ∑ i, d i ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ hj.symm]
  · simp

lemma orth_mul {a b c : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    [DecidableEq c] {A : Matrix a b ℝ} {B : Matrix b c ℝ} (hA : Aᵀ * A = 1)
    (hB : Bᵀ * B = 1) : (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hB]

omit [Fintype κ] in
lemma orth_submatrix {P : Matrix ρ κ ℝ} (hP : Pᵀ * P = 1) (keep : Finset κ) :
    (P.submatrix id ((↑) : keep → κ))ᵀ * P.submatrix id ((↑) : keep → κ) = 1 := by
  have h : (Pᵀ).submatrix ((↑) : keep → κ) id * P.submatrix id ((↑) : keep → κ) =
      (Pᵀ * P).submatrix (↑) (↑) :=
    (Matrix.submatrix_mul _ _ _ id _ Function.bijective_id).symm
  rw [Matrix.transpose_submatrix, h, hP, Matrix.submatrix_one _ Subtype.val_injective]

omit [Fintype ρ] [Fintype ρ'] in
lemma submatrix_diagonal (P : Matrix ρ κ ℝ) (Q : Matrix ρ' κ ℝ) (σ : κ → ℝ) (keep : Finset κ) :
    P.submatrix id ((↑) : keep → κ) * Matrix.diagonal (fun i : keep => σ i) *
        (Q.submatrix id ((↑) : keep → κ))ᵀ =
      P * Matrix.diagonal (fun i => if i ∈ keep then σ i else 0) * Qᵀ := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  rw [Finset.sum_coe_sort keep (fun i => P a i * σ i * Q b i)]
  calc ∑ i ∈ keep, P a i * σ i * Q b i
      = ∑ i ∈ keep, P a i * (if i ∈ keep then σ i else 0) * Q b i :=
        Finset.sum_congr rfl fun i hi => by simp [hi]
    _ = ∑ i, P a i * (if i ∈ keep then σ i else 0) * Q b i :=
        Finset.sum_subset (Finset.subset_univ keep) fun i _ hi => by simp [hi]

/-- **The truncation step of Algorithm 1** (arXiv 2410.18720, eq. (9) and the text after it).  Let
`Û`, `V̂` be orthonormal and `Ŝ = P Σ Qᵀ` be a singular value decomposition (`P`, `Q` with
orthonormal columns).  Keeping the singular values indexed by `keep`, the new factors
`U₁ = Û P_keep`, `V₁ = V̂ Q_keep`, `S₁ = Σ_keep` are orthonormal, and
`‖Û Ŝ V̂ᵀ - U₁ S₁ V₁ᵀ‖² = ∑_{i ∉ keep} sᵢ²`.  So the criterion (9), `∑_{i ∉ keep} sᵢ² < ϑ`, gives
`‖Ŵ - W₁‖ < √ϑ` in the Frobenius norm, whereas Step 3 of the proof of Thm 3 of the paper uses
`‖Ŵ - W₁‖ ≤ ϑ`; below the truncation error is therefore measured directly by `‖W₁ - Ŵ‖`. -/
theorem truncation_spec [DecidableEq ρ] [DecidableEq ρ'] {Uh : Matrix m ρ ℝ} {Vh : Matrix n ρ' ℝ}
    (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1) {P : Matrix ρ κ ℝ} {Q : Matrix ρ' κ ℝ}
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) (σ : κ → ℝ) (keep : Finset κ) :
    (Uh * P.submatrix id ((↑) : keep → κ))ᵀ * (Uh * P.submatrix id ((↑) : keep → κ)) = 1 ∧
    (Vh * Q.submatrix id ((↑) : keep → κ))ᵀ * (Vh * Q.submatrix id ((↑) : keep → κ)) = 1 ∧
    ‖Uh * (P * Matrix.diagonal σ * Qᵀ) * Vhᵀ -
        (Uh * P.submatrix id ((↑) : keep → κ)) * Matrix.diagonal (fun i : keep => σ i) *
          (Vh * Q.submatrix id ((↑) : keep → κ))ᵀ‖ ^ 2 =
      ∑ i ∈ keepᶜ, σ i ^ 2 := by
  refine ⟨orth_mul hUh (orth_submatrix hP keep), orth_mul hVh (orth_submatrix hQ keep), ?_⟩
  have e : Uh * (P * Matrix.diagonal σ * Qᵀ) * Vhᵀ -
        (Uh * P.submatrix id ((↑) : keep → κ)) * Matrix.diagonal (fun i : keep => σ i) *
          (Vh * Q.submatrix id ((↑) : keep → κ))ᵀ =
      (Uh * P) * (Matrix.diagonal (fun i => if i ∈ keep then 0 else σ i) * (Vh * Q)ᵀ) := by
    have e1 : (Uh * P.submatrix id ((↑) : keep → κ)) * Matrix.diagonal (fun i : keep => σ i) *
          (Vh * Q.submatrix id ((↑) : keep → κ))ᵀ =
        Uh * (P.submatrix id ((↑) : keep → κ) * Matrix.diagonal (fun i : keep => σ i) *
          (Q.submatrix id ((↑) : keep → κ))ᵀ) * Vhᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have e2 : Matrix.diagonal σ = Matrix.diagonal (fun i => if i ∈ keep then σ i else 0) +
        Matrix.diagonal (fun i => if i ∈ keep then 0 else σ i) := by
      rw [Matrix.diagonal_add]
      congr 1
      ext i
      by_cases h : i ∈ keep <;> simp [h]
    rw [e1, submatrix_diagonal]
    nth_rewrite 1 [e2]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
      add_sub_cancel_left]
  rw [e, Frobenius.norm_mul_of_orthonormal (orth_mul hUh hP),
    Frobenius.norm_mul_transpose_of_orthonormal (orth_mul hVh hQ), norm_sq_diagonal]
  calc ∑ i, (if i ∈ keep then 0 else σ i) ^ 2
      = ∑ i ∈ keepᶜ, (if i ∈ keep then 0 else σ i) ^ 2 :=
        (Finset.sum_subset (Finset.subset_univ keepᶜ) fun i _ hi => by
          rw [Finset.mem_compl, not_not] at hi
          simp [hi]).symm
    _ = ∑ i ∈ keepᶜ, σ i ^ 2 := Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_compl] at hi
        simp [hi]

end Truncation

/-! ### The intrinsic tangent projector `P(W)` and its measurability -/

section Intrinsic

variable {m n : Type*} [Fintype m] [Fintype n]

/-- One Gram–Schmidt update of a projector `Q` by a vector `a`: with `c = a - Q a`,
`Q ↦ Q + c cᵀ / ‖c‖²` (and `Q ↦ Q` if `c = 0`, by the convention `0⁻¹ = 0`). -/
noncomputable def gsStep (Q : Matrix m m ℝ) (a : m → ℝ) : Matrix m m ℝ :=
  Q + ((a - Q *ᵥ a) ⬝ᵥ (a - Q *ᵥ a))⁻¹ • Matrix.vecMulVec (a - Q *ᵥ a) (a - Q *ᵥ a)

/-- The orthogonal projector onto the column space of `A`, computed by Gram–Schmidt over the
columns (`colProj_spec`). -/
noncomputable def colProj (A : Matrix m n ℝ) : Matrix m m ℝ :=
  ((Finset.univ : Finset n).toList).foldl (fun Q j => gsStep Q (Aᵀ j)) 0

/-- The properties of a partial Gram–Schmidt projector for the columns `J` of `A`. -/
structure IsColProj (A : Matrix m n ℝ) (J : Set n) (Q : Matrix m m ℝ) : Prop where
  symm : Qᵀ = Q
  idem : Q * Q = Q
  fix : ∀ j ∈ J, Q *ᵥ Aᵀ j = Aᵀ j
  fac : ∃ C : Matrix n m ℝ, Q = A * C

lemma IsColProj.step {A : Matrix m n ℝ} {J : Set n} {Q : Matrix m m ℝ}
    (h : IsColProj A J Q) (j : n) : IsColProj A (insert j J) (gsStep Q (Aᵀ j)) := by
  classical
  set a := Aᵀ j with ha
  set c := a - Q *ᵥ a with hc
  have hgs : gsStep Q a = Q + (c ⬝ᵥ c)⁻¹ • Matrix.vecMulVec c c := rfl
  have h1 : Q *ᵥ c = 0 := by
    rw [hc, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h.idem, sub_self]
  have h2 : c ᵥ* Q = 0 := by
    rw [← Matrix.mulVec_transpose, h.symm, h1]
  have h3 : ∀ x, Q *ᵥ x = x → c ⬝ᵥ x = 0 := fun x hx => by
    rw [← hx, Matrix.dotProduct_mulVec, h2, zero_dotProduct]
  have h4 : c ⬝ᵥ a = c ⬝ᵥ c := by
    have : a = c + Q *ᵥ a := by rw [hc]; abel
    nth_rewrite 1 [this]
    rw [dotProduct_add, Matrix.dotProduct_mulVec, h2, zero_dotProduct, add_zero]
  have hmul : ∀ x, gsStep Q a *ᵥ x = Q *ᵥ x + ((c ⬝ᵥ c)⁻¹ * (c ⬝ᵥ x)) • c := fun x => by
    rw [hgs, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
  have hc0 : c ⬝ᵥ c = 0 → c = 0 := dotProduct_self_eq_zero.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgs, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_vecMulVec, h.symm]
  · have e1 : Q * Matrix.vecMulVec c c = 0 := by
      rw [Matrix.mul_vecMulVec, h1, Matrix.zero_vecMulVec]
    have e2 : Matrix.vecMulVec c c * Q = 0 := by
      rw [Matrix.vecMulVec_mul, h2, Matrix.vecMulVec_zero]
    have e3 : Matrix.vecMulVec c c * Matrix.vecMulVec c c = (c ⬝ᵥ c) • Matrix.vecMulVec c c := by
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    rw [hgs, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h.idem, Matrix.mul_smul, e1,
      Matrix.smul_mul, e2, Matrix.smul_mul, Matrix.mul_smul, e3]
    by_cases h0 : c ⬝ᵥ c = 0
    · simp [hc0 h0]
    · rw [smul_smul, smul_smul]
      simp only [smul_zero, add_zero, zero_add]
      congr 2
      field_simp
  · intro i hi
    rcases hi with rfl | hi
    · change gsStep Q a *ᵥ a = a
      rw [hmul, h4]
      by_cases h0 : c ⬝ᵥ c = 0
      · have hc' := hc0 h0
        have hca : Q *ᵥ a = a := (sub_eq_zero.1 hc').symm
        rw [hc', smul_zero, add_zero, hca]
      · rw [inv_mul_cancel₀ h0, one_smul, hc]
        abel
    · rw [hmul, h3 _ (h.fix i hi), mul_zero, zero_smul, add_zero, h.fix i hi]
  · obtain ⟨C, hC⟩ := h.fac
    have hw : c = A *ᵥ (Pi.single j 1 - C *ᵥ a) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hC, Matrix.mulVec_single_one]
      rfl
    refine ⟨C + (c ⬝ᵥ c)⁻¹ • Matrix.vecMulVec (Pi.single j 1 - C *ᵥ a) c, ?_⟩
    rw [hgs, Matrix.mul_add, ← hC, Matrix.mul_smul, Matrix.mul_vecMulVec, ← hw]

/-- `colProj A` is the orthogonal projector onto the column space of `A`. -/
theorem colProj_spec (A : Matrix m n ℝ) : IsColProj A Set.univ (colProj A) := by
  classical
  have key : ∀ (l : List n) (J : Set n) (Q : Matrix m m ℝ), IsColProj A J Q →
      IsColProj A (J ∪ {j | j ∈ l}) (l.foldl (fun Q j => gsStep Q (Aᵀ j)) Q) := by
    intro l
    induction l with
    | nil => intro J Q h; simpa using h
    | cons j l ih =>
      intro J Q h
      have := ih _ _ (h.step j)
      have e : insert j J ∪ {i | i ∈ l} = J ∪ {i | i ∈ j :: l} := by
        ext i
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_cons]
        tauto
      rwa [e] at this
  have h0 : IsColProj A ∅ (0 : Matrix m m ℝ) :=
    ⟨by simp, by simp, by simp, ⟨0, by simp⟩⟩
  have := key (Finset.univ : Finset n).toList ∅ 0 h0
  have e : (∅ : Set n) ∪ {i | i ∈ (Finset.univ : Finset n).toList} = Set.univ := by
    ext i; simp
  rw [e] at this
  exact this

lemma colProj_mul (A : Matrix m n ℝ) : colProj A * A = A := by
  ext i j
  exact congrFun ((colProj_spec A).fix j (Set.mem_univ j)) i

/-- **Identification of `colProj`**: if `A = U B` with `U` orthonormal and `B` right invertible
(`range A = range U`), then `colProj A = U Uᵀ`. -/
theorem colProj_eq {r : Type*} [Fintype r] [DecidableEq r] {A : Matrix m n ℝ} {U : Matrix m r ℝ}
    {B : Matrix r n ℝ} {B' : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hA : A = U * B) (hB : B * B' = 1) :
    colProj A = U * Uᵀ := by
  set Q := colProj A with hQ
  have hspec := colProj_spec A
  have h1 : Q * U = U := by
    have e : U = A * B' := by rw [hA, Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, colProj_mul]
  obtain ⟨C, hC⟩ := hspec.fac
  have h2 : U * Uᵀ * Q = Q := by
    have hC' : Q = U * (B * C) := by rw [hQ, hC, hA, Matrix.mul_assoc]
    rw [hC', ← Matrix.mul_assoc, Matrix.mul_assoc U, hU, Matrix.mul_one]
  calc Q = (U * Uᵀ * Q)ᵀ := by rw [h2, hspec.symm]
    _ = Q * U * Uᵀ := by
      rw [Matrix.transpose_mul, hspec.symm, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    _ = U * Uᵀ := by rw [h1]

/-- The tangent projector `P(W) Z = P_col Z + Z P_row - P_col Z P_row` of arXiv 2410.18720,
eq. (18), defined from `W` alone, with `P_col`, `P_row` the orthogonal projectors onto the column
and row space of `W` (for every `W`, whatever its rank). -/
noncomputable def tangentAt (W : Matrix m n ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangent (Frobenius.leftMulCLM (colProj W)) (Frobenius.rightMulCLM (colProj Wᵀ))

/-- **`P(W)` is the tangent projector of eq. (18)**: for `W = U S Vᵀ` with orthonormal `U`, `V`
and invertible `S`, `P(W) = U Uᵀ (·) + (·) V Vᵀ - U Uᵀ (·) V Vᵀ`. -/
theorem tangentAt_eq {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix m r ℝ}
    {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) : tangentAt (U * S * Vᵀ) = tangentProj U V := by
  have h1 : colProj (U * S * Vᵀ) = U * Uᵀ :=
    colProj_eq (B := S * Vᵀ) (B' := V * S⁻¹) hU (Matrix.mul_assoc _ _ _) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ hS])
  have h2 : colProj (U * S * Vᵀ)ᵀ = V * Vᵀ :=
    colProj_eq (B := Sᵀ * Uᵀ) (B' := U * (S⁻¹)ᵀ) hV (by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, ← Matrix.transpose_mul,
        Matrix.nonsing_inv_mul _ hS, Matrix.transpose_one])
  rw [tangentAt, h1, h2]
  rfl

/-- `P(W)` is an orthogonal projector for every `W`. -/
theorem isOrthProj_tangentAt (W : Matrix m n ℝ) : IsOrthProj (tangentAt W) := by
  have hP := colProj_spec W
  have hQ := colProj_spec Wᵀ
  have hL : IsOrthProj (Frobenius.leftMulCLM (colProj W) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    ⟨fun X => by simp [← Matrix.mul_assoc, hP.idem], fun X Y => by
      simp only [Frobenius.leftMulCLM_apply]
      rw [Frobenius.inner_mul_left, hP.symm]⟩
  have hR : IsOrthProj (Frobenius.rightMulCLM (colProj Wᵀ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    ⟨fun X => by simp [Matrix.mul_assoc, hQ.idem], fun X Y => by
      simp only [Frobenius.rightMulCLM_apply]
      rw [Frobenius.inner_mul_right, hQ.symm]⟩
  exact hL.tangent hR fun X => by simp [Matrix.mul_assoc]

/-! Measurability: `P(W)` is a Borel function of `W`, entrywise through Gram–Schmidt. -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Entrywise measurability of a matrix-valued map. -/
def EntryMeasurable {a b : Type*} (f : Ω → Matrix a b ℝ) : Prop :=
  ∀ i j, Measurable fun ω => f ω i j

omit [Fintype m] [Fintype n] in
lemma EntryMeasurable.add {f f' : Ω → Matrix m n ℝ} (h : EntryMeasurable f)
    (h' : EntryMeasurable f') : EntryMeasurable fun ω => f ω + f' ω :=
  fun i j => (h i j).add (h' i j)

omit [Fintype m] [Fintype n] in
lemma EntryMeasurable.sub {f f' : Ω → Matrix m n ℝ} (h : EntryMeasurable f)
    (h' : EntryMeasurable f') : EntryMeasurable fun ω => f ω - f' ω :=
  fun i j => (h i j).sub (h' i j)

omit [Fintype m] [Fintype n] in
lemma EntryMeasurable.mul {k : Type*} [Fintype k] {f : Ω → Matrix m k ℝ} {f' : Ω → Matrix k n ℝ}
    (h : EntryMeasurable f) (h' : EntryMeasurable f') : EntryMeasurable fun ω => f ω * f' ω :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact Finset.measurable_fun_sum _ fun k _ => (h i k).mul (h' k j)

omit [Fintype m] [Fintype n] in
lemma EntryMeasurable.transpose {f : Ω → Matrix m n ℝ} (h : EntryMeasurable f) :
    EntryMeasurable fun ω => (f ω)ᵀ :=
  fun i j => h j i

lemma EntryMeasurable.gsStep {Q : Ω → Matrix m m ℝ} {a : Ω → m → ℝ} (hQ : EntryMeasurable Q)
    (ha : ∀ i, Measurable fun ω => a ω i) : EntryMeasurable fun ω => gsStep (Q ω) (a ω) := by
  have hc : ∀ i, Measurable fun ω => (a ω - Q ω *ᵥ a ω) i := fun i => by
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    exact (ha i).sub (Finset.measurable_fun_sum _ fun k _ => (hQ i k).mul (ha k))
  intro i j
  simp only [P2410_18720.gsStep, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  refine (hQ i j).add (Measurable.mul (Measurable.inv ?_) ((hc i).mul (hc j)))
  simp only [dotProduct]
  exact Finset.measurable_fun_sum _ fun k _ => (hc k).mul (hc k)

lemma EntryMeasurable.colProj {A : Ω → Matrix m n ℝ} (hA : EntryMeasurable A) :
    EntryMeasurable fun ω => colProj (A ω) := by
  have key : ∀ (l : List n) (Q : Ω → Matrix m m ℝ), EntryMeasurable Q →
      EntryMeasurable fun ω => l.foldl (fun Q j => P2410_18720.gsStep Q ((A ω)ᵀ j))
        (Q ω) := by
    intro l
    induction l with
    | nil => exact fun Q hQ => hQ
    | cons j l ih =>
      intro Q hQ
      exact ih _ (hQ.gsStep fun i => hA i j)
  exact key _ _ fun _ _ => measurable_const

omit [Fintype m] [Fintype n] in
lemma continuous_entry (i : m) (j : n) [Fintype m] [Fintype n] :
    Continuous fun X : Matrix m n ℝ => X i j :=
  (continuous_apply j).comp (continuous_apply i)

lemma entryMeasurable_of_stronglyMeasurable {f : Ω → Matrix m n ℝ} (hf : StronglyMeasurable f) :
    EntryMeasurable f :=
  fun i j => ((continuous_entry i j).comp_stronglyMeasurable hf).measurable

lemma stronglyMeasurable_of_entryMeasurable {f : Ω → Matrix m n ℝ} (hf : EntryMeasurable f) :
    StronglyMeasurable f := by
  classical
  have e : f = fun ω => ∑ i, ∑ j, f ω i j • Matrix.single i j (1 : ℝ) := by
    funext ω
    conv_lhs => rw [Matrix.matrix_eq_sum_single (f ω)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => Finset.stronglyMeasurable_fun_sum _
    fun j _ => (hf i j).stronglyMeasurable.smul_const _

/-- `(W, Y) ↦ P(W) Y` preserves strong measurability, with respect to any `σ`-algebra. -/
theorem stronglyMeasurable_tangentAt_apply {W Y : Ω → Matrix m n ℝ} (hW : StronglyMeasurable W)
    (hY : StronglyMeasurable Y) : StronglyMeasurable fun ω => tangentAt (W ω) (Y ω) := by
  classical
  have hW' := entryMeasurable_of_stronglyMeasurable hW
  have hY' := entryMeasurable_of_stronglyMeasurable hY
  have hP := hW'.colProj
  have hQ := hW'.transpose.colProj
  have e : (fun ω => tangentAt (W ω) (Y ω)) = fun ω =>
      colProj (W ω) * Y ω + Y ω * colProj (W ω)ᵀ - colProj (W ω) * (Y ω * colProj (W ω)ᵀ) := by
    funext ω
    simp [tangentAt, tangent_apply]
  rw [e]
  exact stronglyMeasurable_of_entryMeasurable (((hP.mul hY').add (hY'.mul hQ)).sub
    (hP.mul (hY'.mul hQ)))

end Intrinsic

/-! ### The stochastic estimates -/

section Stochastic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ℒ : E → ℝ} {g : E → E} {β B : ℝ}

/-- The pointwise form of one truncated projected stochastic gradient step, split into the
true gradient `g x` and the noise `G - g x`:
`ℒ(x₁) ≤ ℒ(x) - λ(1 - βλ/2) ‖P g‖² - λ(1 - βλ) ⟪P g, G - g⟫ + βλ²/2 ‖P(G - g)‖² + B ‖x₁ - x̂‖`
with `x̂ = x - λ P G`. -/
theorem step_bound (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B) {P : E →L[ℝ] E}
    (hP : IsOrthProj P) (x G x₁ : E) (lr : ℝ) :
    ℒ x₁ ≤ ℒ x - lr * (1 - β * lr / 2) * ‖P (g x)‖ ^ 2 -
        lr * (1 - β * lr) * ⟪P (g x), G - g x⟫ + β * lr ^ 2 / 2 * ‖P (G - g x)‖ ^ 2 +
      B * ‖x₁ - (x - lr • P G)‖ := by
  have h1 := StochasticDescent.loss_sub_smul_le hℒ hg x (P G) lr
  have h2 := abs_energy_sub_le hℒ (x := x₁) (z := x - lr • P G) (fun w _ => hB w)
  have h3 := (abs_le.1 h2).2
  set y := P (g x) with hy
  set d := G - g x with hd
  have hG : G = g x + d := by rw [hd]; abel
  have e1 : ⟪g x, P G⟫ = ‖y‖ ^ 2 + ⟪y, d⟫ := by
    rw [← hP.symm, ← hy]
    nth_rewrite 1 [hG]
    rw [inner_add_right, hy, hP.inner_self_apply]
  have e2 : ‖P G‖ ^ 2 = ‖y‖ ^ 2 + 2 * ⟪y, d⟫ + ‖P d‖ ^ 2 := by
    have : P G = y + P d := by rw [hG, map_add]
    rw [this, norm_add_sq_real, hy, hP.inner_comp]
  rw [e1, e2] at h1
  nlinarith

/-- The real inner product as a continuous bilinear map. -/
noncomputable def innerBilin : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 fun x y => by
    simpa using norm_inner_le_norm (𝕜 := ℝ) x y

@[simp] lemma innerBilin_apply (x y : E) : innerBilin x y = ⟪x, y⟫ := rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integrable_inner_of_bound {Y D : Ω → E} {C : ℝ} (hY : AEStronglyMeasurable Y μ)
    (hYC : ∀ ω, ‖Y ω‖ ≤ C) (hD : Integrable D μ) : Integrable (fun ω => ⟪Y ω, D ω⟫) μ := by
  refine (hD.norm.const_mul C).mono' (hY.inner hD.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  calc ‖⟪Y ω, D ω⟫‖ ≤ ‖Y ω‖ * ‖D ω‖ := norm_inner_le_norm (𝕜 := ℝ) (Y ω) (D ω)
    _ ≤ C * ‖D ω‖ := mul_le_mul_of_nonneg_right (hYC ω) (norm_nonneg _)

/-- **Martingale differences are orthogonal to the past**: if `Y` is bounded and `m₀`-measurable
and `μ[D | m₀] = 0`, then `E ⟪Y, D⟫ = 0`. -/
theorem integral_inner_eq_zero [CompleteSpace E] {m₀ : MeasurableSpace Ω} (hm : m₀ ≤ mΩ)
    {Y D : Ω → E} {C : ℝ} (hY : StronglyMeasurable[m₀] Y) (hYC : ∀ ω, ‖Y ω‖ ≤ C)
    (hD : Integrable D μ) (hcond : μ[D | m₀] =ᵐ[μ] 0) : ∫ ω, ⟪Y ω, D ω⟫ ∂μ = 0 := by
  have hint : Integrable (fun ω => innerBilin (Y ω) (D ω)) μ :=
    integrable_inner_of_bound (hY.mono hm).aestronglyMeasurable hYC hD
  have h1 := condExp_bilin_of_stronglyMeasurable_left innerBilin hY hint hD
  have h2 : ∫ ω, innerBilin (Y ω) (D ω) ∂μ = ∫ ω, (μ[fun ω => innerBilin (Y ω) (D ω) | m₀]) ω ∂μ :=
    (integral_condExp hm).symm
  simp only [innerBilin_apply] at h2 h1
  rw [h2]
  have h3 : (μ[fun ω => ⟪Y ω, D ω⟫ | m₀]) =ᵐ[μ] 0 := by
    filter_upwards [h1, hcond] with ω h4 h5
    rw [h4, h5]
    simp
  rw [integral_congr_ae h3]
  simp

omit [IsProbabilityMeasure μ] in
/-- Integration of `step_bound`. -/
theorem integral_step_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B) {Pr : Ω → E →L[ℝ] E}
    (hP : ∀ ω, IsOrthProj (Pr ω)) {W₀ W₁ G : Ω → E} (lr : ℝ)
    (h0 : Integrable (fun ω => ℒ (W₀ ω)) μ) (h1 : Integrable (fun ω => ℒ (W₁ ω)) μ)
    (hY : Integrable (fun ω => ‖Pr ω (g (W₀ ω))‖ ^ 2) μ)
    (hYD : Integrable (fun ω => ⟪Pr ω (g (W₀ ω)), G ω - g (W₀ ω)⟫) μ)
    (hPD : Integrable (fun ω => ‖Pr ω (G ω - g (W₀ ω))‖ ^ 2) μ)
    (htr : Integrable (fun ω => ‖W₁ ω - (W₀ ω - lr • Pr ω (G ω))‖) μ) :
    ∫ ω, ℒ (W₁ ω) ∂μ ≤ ∫ ω, ℒ (W₀ ω) ∂μ -
        lr * (1 - β * lr / 2) * ∫ ω, ‖Pr ω (g (W₀ ω))‖ ^ 2 ∂μ -
        lr * (1 - β * lr) * ∫ ω, ⟪Pr ω (g (W₀ ω)), G ω - g (W₀ ω)⟫ ∂μ +
        β * lr ^ 2 / 2 * ∫ ω, ‖Pr ω (G ω - g (W₀ ω))‖ ^ 2 ∂μ +
      B * ∫ ω, ‖W₁ ω - (W₀ ω - lr • Pr ω (G ω))‖ ∂μ := by
  have i1 : Integrable (fun ω => ℒ (W₀ ω) - lr * (1 - β * lr / 2) * ‖Pr ω (g (W₀ ω))‖ ^ 2) μ :=
    h0.sub (hY.const_mul _)
  have i2 : Integrable (fun ω => ℒ (W₀ ω) - lr * (1 - β * lr / 2) * ‖Pr ω (g (W₀ ω))‖ ^ 2 -
      lr * (1 - β * lr) * ⟪Pr ω (g (W₀ ω)), G ω - g (W₀ ω)⟫) μ := i1.sub (hYD.const_mul _)
  have i3 : Integrable (fun ω => ℒ (W₀ ω) - lr * (1 - β * lr / 2) * ‖Pr ω (g (W₀ ω))‖ ^ 2 -
      lr * (1 - β * lr) * ⟪Pr ω (g (W₀ ω)), G ω - g (W₀ ω)⟫ +
      β * lr ^ 2 / 2 * ‖Pr ω (G ω - g (W₀ ω))‖ ^ 2) μ := i2.add (hPD.const_mul _)
  have i4 : Integrable (fun ω => ℒ (W₀ ω) - lr * (1 - β * lr / 2) * ‖Pr ω (g (W₀ ω))‖ ^ 2 -
      lr * (1 - β * lr) * ⟪Pr ω (g (W₀ ω)), G ω - g (W₀ ω)⟫ +
      β * lr ^ 2 / 2 * ‖Pr ω (G ω - g (W₀ ω))‖ ^ 2 +
      B * ‖W₁ ω - (W₀ ω - lr • Pr ω (G ω))‖) μ := i3.add (htr.const_mul B)
  have hle := integral_mono h1 i4
    (fun ω => step_bound hℒ hg hB (hP ω) (W₀ ω) (G ω) (W₁ ω) lr)
  rw [integral_add i3 (htr.const_mul B), integral_add i2 (hPD.const_mul _),
    integral_sub i1 (hYD.const_mul _), integral_sub h0 (hY.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hle
  exact hle

/-- Abstract core of Thm 2 of arXiv 2410.18720: an adapted projected stochastic gradient iteration
with unbiased gradients, bounded variance, summable expected truncation errors and Robbins–Monro
step sizes has `liminf E ‖Π_k ∇ℒ(W_k)‖² = 0`, in the form of `b_k < ε` for infinitely many `k`. -/
theorem exists_expected_projGrad_lt [CompleteSpace E]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hB : ∀ x, ‖g x‖ ≤ B) (hβ : 0 ≤ β) {ℱ : Filtration ℕ mΩ} {W G : ℕ → Ω → E}
    {Pr : ℕ → Ω → E →L[ℝ] E} {lr : ℕ → ℝ} {σsq D ℒinf : ℝ}
    (hW : ∀ k, StronglyMeasurable[ℱ k] (W k)) (hW0 : Integrable (fun ω => ℒ (W 0 ω)) μ)
    (hGm : ∀ k, StronglyMeasurable (G k)) (hG2 : ∀ k, Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hmean : ∀ k, μ[G k | ℱ k] =ᵐ[μ] fun ω => g (W k ω))
    (hvar : ∀ k, ∫ ω, ‖G k ω - g (W k ω)‖ ^ 2 ∂μ ≤ σsq)
    (hP : ∀ k ω, IsOrthProj (Pr k ω))
    (hPg : ∀ k, StronglyMeasurable[ℱ k] fun ω => Pr k ω (g (W k ω)))
    (hPG : ∀ k, StronglyMeasurable fun ω => Pr k ω (G k ω))
    (htr : ∀ k, Integrable (fun ω => ‖W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))‖) μ)
    (hD : ∀ n, ∑ k ∈ range n, ∫ ω, ‖W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))‖ ∂μ ≤ D)
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hlr0 : ∀ k, 0 ≤ lr k) (hdiv : ¬ Summable lr)
    (hsq : Summable fun k => lr k ^ 2) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ∫ ω, ‖Pr k ω (g (W k ω))‖ ^ 2 ∂μ < ε := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := β.toNNReal) fun x y => by
    rw [Real.coe_toNNReal _ hβ, dist_eq_norm, dist_eq_norm]
    exact hg x y).continuous
  have hℒc : Continuous ℒ := continuous_of_hasFDerivAt_innerSL hℒ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hgW : ∀ k, StronglyMeasurable[ℱ k] fun ω => g (W k ω) := fun k =>
    hgc.comp_stronglyMeasurable (hW k)
  have hgWi : ∀ k, Integrable (fun ω => g (W k ω)) μ := fun k =>
    Integrable.of_bound ((hgW k).mono (ℱ.le k)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => hB _)
  have hGi : ∀ k, Integrable (G k) μ := fun k =>
    ((memLp_two_iff_integrable_sq_norm (hGm k).aestronglyMeasurable).2 (hG2 k)).integrable
      one_le_two
  have hDi : ∀ k, Integrable (fun ω => G k ω - g (W k ω)) μ := fun k => (hGi k).sub (hgWi k)
  have hcond : ∀ k, μ[fun ω => G k ω - g (W k ω) | ℱ k] =ᵐ[μ] 0 := fun k => by
    have e1 := condExp_sub (hGi k) (hgWi k) (ℱ k)
    have e2 : μ[fun ω => g (W k ω) | ℱ k] = fun ω => g (W k ω) :=
      condExp_of_stronglyMeasurable (ℱ.le k) (hgW k) (hgWi k)
    filter_upwards [e1, hmean k] with ω h1 h2
    have h3 : (μ[G k - fun ω => g (W k ω) | ℱ k]) ω = 0 := by
      rw [h1, Pi.sub_apply, h2, e2, sub_self]
    exact h3
  have hDsq : ∀ k, Integrable (fun ω => ‖G k ω - g (W k ω)‖ ^ 2) μ := fun k => by
    refine (((hG2 k).const_mul 2).add (integrable_const (2 * B ^ 2))).mono'
      (((hGm k).sub ((hgW k).mono (ℱ.le k))).norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have h1 := norm_sub_le (G k ω) (g (W k ω))
    have h2 := hB (W k ω)
    have h3 := norm_nonneg (G k ω - g (W k ω))
    have h4 := norm_nonneg (G k ω)
    have h5 := norm_nonneg (g (W k ω))
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖G k ω‖ - B), sq_nonneg (‖G k ω‖ - ‖g (W k ω)‖)]
  have hYb : ∀ k ω, ‖Pr k ω (g (W k ω))‖ ≤ B := fun k ω =>
    ((hP k ω).norm_le _).trans (hB _)
  have hYm : ∀ k, StronglyMeasurable fun ω => Pr k ω (g (W k ω)) := fun k =>
    (hPg k).mono (ℱ.le k)
  have hYsq : ∀ k, Integrable (fun ω => ‖Pr k ω (g (W k ω))‖ ^ 2) μ := fun k =>
    Integrable.of_bound ((hYm k).norm.pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hYb k ω) 2)
  have hPDe : ∀ k ω, Pr k ω (G k ω - g (W k ω)) = Pr k ω (G k ω) - Pr k ω (g (W k ω)) :=
    fun k ω => map_sub _ _ _
  have hPDsq : ∀ k, Integrable (fun ω => ‖Pr k ω (G k ω - g (W k ω))‖ ^ 2) μ := fun k => by
    refine (hDsq k).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · simp only [hPDe]
      exact (((hPG k).sub (hYm k)).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hP k ω).norm_le _) 2
  have hYD : ∀ k, Integrable (fun ω => ⟪Pr k ω (g (W k ω)), G k ω - g (W k ω)⟫) μ := fun k =>
    integrable_inner_of_bound (hYm k).aestronglyMeasurable (hYb k) (hDi k)
  have hYD0 : ∀ k, ∫ ω, ⟪Pr k ω (g (W k ω)), G k ω - g (W k ω)⟫ ∂μ = 0 := fun k =>
    integral_inner_eq_zero (ℱ.le k) (hPg k) (hYb k) (hDi k) (hcond k)
  have hLi : ∀ k, Integrable (fun ω => ℒ (W k ω)) μ := by
    intro k
    induction k with
    | zero => exact hW0
    | succ k ih =>
      refine (ih.norm.add ((htr k).add ((hGi k).norm.const_mul |lr k|) |>.const_mul B)).mono'
        (hℒc.comp_stronglyMeasurable ((hW (k + 1)).mono (ℱ.le _))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      have h1 := abs_energy_sub_le hℒ (x := W (k + 1) ω) (z := W k ω) (fun w _ => hB w)
      have h2 : ‖W (k + 1) ω - W k ω‖ ≤
          ‖W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))‖ + |lr k| * ‖G k ω‖ := by
        have e : W (k + 1) ω - W k ω = (W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))) -
            lr k • Pr k ω (G k ω) := by abel
        rw [e]
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((hP k ω).norm_le _) (abs_nonneg _)
      have h3 := abs_le.1 h1
      have h4 : B * ‖W (k + 1) ω - W k ω‖ ≤ B * (‖W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))‖ +
          |lr k| * ‖G k ω‖) := mul_le_mul_of_nonneg_left h2 hB0
      simp only [Pi.add_apply, Real.norm_eq_abs]
      refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg (ℒ (W k ω)), le_abs_self (ℒ (W k ω)),
        neg_abs_le (ℒ (W k ω))]
  set a : ℕ → ℝ := fun k => ∫ ω, ℒ (W k ω) ∂μ with ha
  set b : ℕ → ℝ := fun k => ∫ ω, ‖Pr k ω (g (W k ω))‖ ^ 2 ∂μ with hb
  set τ : ℕ → ℝ := fun k => ∫ ω, ‖W (k + 1) ω - (W k ω - lr k • Pr k ω (G k ω))‖ ∂μ with hτ
  have hb0 : ∀ k, 0 ≤ b k := fun k => integral_nonneg fun ω => by positivity
  have hbB : ∀ k, b k ≤ B ^ 2 := fun k => by
    have := integral_mono (hYsq k) (integrable_const (B ^ 2)) fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) (hYb k ω) 2
    simpa using this
  have hv : ∀ k, ∫ ω, ‖Pr k ω (G k ω - g (W k ω))‖ ^ 2 ∂μ ≤ σsq := fun k =>
    (integral_mono (hPDsq k) (hDsq k) fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) ((hP k ω).norm_le _) 2).trans (hvar k)
  have ha0 : ∀ k, ℒinf ≤ a k := fun k => by
    have := integral_mono (integrable_const ℒinf) (hLi k) fun ω => hinf (W k ω)
    simpa using this
  have hrec : ∀ k, lr k * b k ≤ a k - a (k + 1) + (β / 2 * (B ^ 2 + σsq) * lr k ^ 2 + B * τ k) := by
    intro k
    have h1 := integral_step_le hℒ hg hB (hP k) (lr k) (hLi k) (hLi (k + 1)) (hYsq k) (hYD k)
      (hPDsq k) (htr k)
    rw [hYD0 k] at h1
    have h2 : 0 ≤ β * lr k ^ 2 / 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left (hv k) h2
    have h4 := mul_le_mul_of_nonneg_left (hbB k) h2
    simp only [ha, hb, hτ] at h1 h3 h4 ⊢
    nlinarith
  have hC : ∀ n, ∑ k ∈ range n, lr k * b k ≤
      a 0 - ℒinf + (β / 2 * (B ^ 2 + σsq) * ∑' k, lr k ^ 2 + B * D) := fun n => by
    have hσ0 : 0 ≤ σsq := (integral_nonneg fun ω => by positivity).trans (hvar 0)
    have h1 := sum_le_of_le_sub_add hrec n
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 : β / 2 * (B ^ 2 + σsq) * ∑ k ∈ range n, lr k ^ 2 ≤
        β / 2 * (B ^ 2 + σsq) * ∑' k, lr k ^ 2 :=
      mul_le_mul_of_nonneg_left (hsq.sum_le_tsum _ fun k _ => sq_nonneg _) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (hD n) hB0
    have h4 := ha0 n
    linarith
  exact exists_lt_of_sum_mul_le hlr0 hb0 hdiv hC hε N

end Stochastic

/-! ### Theorems 1 and 2 for Algorithm 1 -/

section Convergence

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `Wh` is obtained from `W` by steps 1–3 of Algorithm 1 of arXiv 2410.18720 with the ambient
gradient `G` and the learning rate `lr`, for some factorization `W = U S Vᵀ` of some rank `r` and
some augmented bases (`Ŵ = Û Ŝ V̂ᵀ`, before truncation).  All sizes may depend on the iteration
and on the sample. -/
def IsGeoLoRAUpdate (G : Matrix m n ℝ) (lr : ℝ) (W Wh : Matrix m n ℝ) : Prop :=
  ∃ (r s s' : ℕ) (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (Ut : Matrix m (Fin s) ℝ) (Vt : Matrix n (Fin s') ℝ),
    IsGeoLoRAStep G lr U S V Ut Vt ∧ W = U * S * Vᵀ ∧ Wh = geoWhat G lr U S V Ut Vt

/-- The update of Algorithm 1 is `Ŵ = W - λ P(W) G`, and `P(W)` is an orthogonal projector. -/
theorem IsGeoLoRAUpdate.eq {G W Wh : Matrix m n ℝ} {lr : ℝ} (h : IsGeoLoRAUpdate G lr W Wh) :
    Wh = W - lr • tangentAt W G := by
  obtain ⟨r, s, s', U, S, V, Ut, Vt, hs, rfl, rfl⟩ := h
  rw [geoWhat_eq hs, tangentAt_eq hs.orthU hs.orthV hs.detS]

theorem IsGeoLoRAUpdate.isOrthProj {G W Wh : Matrix m n ℝ} {lr : ℝ}
    (h : IsGeoLoRAUpdate G lr W Wh) : IsOrthProj (tangentAt W) := by
  obtain ⟨r, s, s', U, S, V, Ut, Vt, hs, rfl, -⟩ := h
  rw [tangentAt_eq hs.orthU hs.orthV hs.detS]
  exact isOrthProj_tangentProj hs.orthU hs.orthV

variable {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β B : ℝ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Corrected Thm 1 of arXiv 2410.18720 (stochastic descent estimate).**  Let `W₀` be the current
iterate, `G` a minibatch gradient on a probability space with `E G = ∇ℒ(W₀)` and `E ‖G‖² < ∞`, `Ŵ`
the result of steps 1–3 of Algorithm 1 for each sample, and `W₁` the truncated iterate.  If `ℒ` is
`β`-smooth with `‖∇ℒ‖ ≤ B`, then

`E ℒ(W₁) ≤ ℒ(W₀) - λ(1 - βλ/2) ‖P(W₀) ∇ℒ(W₀)‖² + βλ²/2 E ‖P(W₀)(G - ∇ℒ(W₀))‖² + B E ‖W₁ - Ŵ‖`.

Differences from the paper.  The printed bound
`E ℒ(W₁) ≤ ℒ(W₀) - λ(1 - Lλ²/2) E ‖P(W₀) G‖² + L E ‖W₁ - Ŵ‖` is **false**, with the printed factor
and with the factor `1 - Lλ/2` of its proof: see `LeanDLRA.StochasticDescent.SameBatchExample`,
`geoLoRA_bound_false` and `geoLoRA_bound_false_mainText`.  The published proof uses the minibatch
gradient `G` in place of `∇ℒ` in the descent lemma; here the noise appears as the variance
term, which vanishes for exact gradients (`G = ∇ℒ(W₀)`, the deterministic form of the theorem).
The last term has the gradient bound `B` (the paper's `L` there, from a mean value argument);
the proof needs no restriction on `λ`.  See `descent_estimate_of_variance` for the bound in terms
of `E ‖P(W₀) G‖²`. -/
theorem descent_estimate (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B) {W₀ : Matrix m n ℝ}
    {G Wh W₁ : Ω → Matrix m n ℝ} {lr : ℝ} (hGm : AEStronglyMeasurable G μ)
    (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) μ) (hmean : ∫ ω, G ω ∂μ = g W₀)
    (hstep : ∀ ω, IsGeoLoRAUpdate (G ω) lr W₀ (Wh ω)) (hW₁ : AEStronglyMeasurable W₁ μ)
    (htr : Integrable (fun ω => ‖W₁ ω - Wh ω‖) μ) :
    ∫ ω, ℒ (W₁ ω) ∂μ ≤ ℒ W₀ - lr * (1 - β * lr / 2) * ‖tangentAt W₀ (g W₀)‖ ^ 2 +
      β * lr ^ 2 / 2 * ∫ ω, ‖tangentAt W₀ (G ω - g W₀)‖ ^ 2 ∂μ + B * ∫ ω, ‖W₁ ω - Wh ω‖ ∂μ := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨ω₀⟩ := hne
  have hT : IsOrthProj (tangentAt W₀) := (hstep ω₀).isOrthProj
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hGi : Integrable G μ :=
    ((memLp_two_iff_integrable_sq_norm hGm).2 hG2).integrable one_le_two
  have hDi : Integrable (fun ω => G ω - g W₀) μ := hGi.sub (integrable_const _)
  have hDsq : Integrable (fun ω => ‖G ω - g W₀‖ ^ 2) μ := by
    refine ((hG2.const_mul 2).add (integrable_const (2 * ‖g W₀‖ ^ 2))).mono'
      (hDi.aestronglyMeasurable.norm.pow 2) (Eventually.of_forall fun ω => ?_)
    have h1 := norm_sub_le (G ω) (g W₀)
    have h3 := norm_nonneg (G ω - g W₀)
    have h4 := norm_nonneg (G ω)
    have h5 := norm_nonneg (g W₀)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖G ω‖ - ‖g W₀‖)]
  have hPD : Integrable (fun ω => ‖tangentAt W₀ (G ω - g W₀)‖ ^ 2) μ := by
    refine hDsq.mono' (((tangentAt W₀).continuous.comp_aestronglyMeasurable
      hDi.aestronglyMeasurable).norm.pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hT.norm_le _) 2
  have hWh : ∀ ω, Wh ω = W₀ - lr • tangentAt W₀ (G ω) := fun ω => (hstep ω).eq
  have hL1 : Integrable (fun ω => ℒ (W₁ ω)) μ := by
    refine ((integrable_const |ℒ W₀|).add ((htr.add (hGi.norm.const_mul |lr|)).const_mul B)).mono'
      ((continuous_of_hasFDerivAt_innerSL hℒ).comp_aestronglyMeasurable hW₁)
      (Eventually.of_forall fun ω => ?_)
    have h1 := abs_energy_sub_le hℒ (x := W₁ ω) (z := W₀) (fun w _ => hB w)
    have h2 : ‖W₁ ω - W₀‖ ≤ ‖W₁ ω - Wh ω‖ + |lr| * ‖G ω‖ := by
      have e : W₁ ω - W₀ = (W₁ ω - Wh ω) - lr • tangentAt W₀ (G ω) := by
        rw [hWh ω]; abel
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hT.norm_le _) (abs_nonneg _)
    have h3 := abs_le.1 h1
    have h4 := mul_le_mul_of_nonneg_left h2 hB0
    simp only [Pi.add_apply, Real.norm_eq_abs]
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg (ℒ W₀), le_abs_self (ℒ W₀),
      neg_abs_le (ℒ W₀)]
  have hYD : ∫ ω, ⟪tangentAt W₀ (g W₀), G ω - g W₀⟫ ∂μ = 0 := by
    rw [integral_inner hDi, integral_sub hGi (integrable_const _), hmean]
    simp
  have htr' : Integrable (fun ω => ‖W₁ ω - (W₀ - lr • tangentAt W₀ (G ω))‖) μ := by
    simpa only [hWh] using htr
  have h := integral_step_le hℒ hg hB (Pr := fun _ => tangentAt W₀) (fun _ => hT)
    (W₀ := fun _ => W₀) lr (integrable_const _) hL1 (integrable_const _)
    (hDi.const_inner _) hPD htr'
  rw [hYD] at h
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero] at h
  simpa only [hWh] using h

/-- Bias–variance splitting of the tangent gradient: for `E G = g₀`,
`E ‖T G‖² = ‖T g₀‖² + E ‖T (G - g₀)‖²`. -/
theorem integral_norm_sq_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : E →L[ℝ] E} (hT : IsOrthProj T) {G : Ω → E} {g₀ : E}
    (hGm : AEStronglyMeasurable G μ) (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) μ)
    (hmean : ∫ ω, G ω ∂μ = g₀) :
    ∫ ω, ‖T (G ω)‖ ^ 2 ∂μ = ‖T g₀‖ ^ 2 + ∫ ω, ‖T (G ω - g₀)‖ ^ 2 ∂μ := by
  have hGi : Integrable G μ :=
    ((memLp_two_iff_integrable_sq_norm hGm).2 hG2).integrable one_le_two
  have hDi : Integrable (fun ω => G ω - g₀) μ := hGi.sub (integrable_const _)
  have hTG : Integrable (fun ω => ‖T (G ω)‖ ^ 2) μ := by
    refine hG2.mono' ((T.continuous.comp_aestronglyMeasurable hGm).norm.pow 2)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hT.norm_le _) 2
  have hin : Integrable (fun ω => ⟪T g₀, G ω - g₀⟫) μ := hDi.const_inner _
  have hin0 : ∫ ω, ⟪T g₀, G ω - g₀⟫ ∂μ = 0 := by
    rw [integral_inner hDi, integral_sub hGi (integrable_const _), hmean]
    simp
  have e : ∀ ω, ‖T (G ω - g₀)‖ ^ 2 = ‖T (G ω)‖ ^ 2 - ‖T g₀‖ ^ 2 - 2 * ⟪T g₀, G ω - g₀⟫ := by
    intro ω
    have h1 : T (G ω) = T g₀ + T (G ω - g₀) := by rw [← map_add]; congr 1; abel
    rw [h1, norm_add_sq_real, hT.inner_comp]
    have h2 : T g₀ + T (G ω - g₀) - T g₀ = T (G ω - g₀) := by abel
    ring
  have i1 : Integrable (fun ω => ‖T (G ω)‖ ^ 2 - ‖T g₀‖ ^ 2) μ := hTG.sub (integrable_const _)
  simp only [e]
  rw [integral_sub i1 (hin.const_mul 2), integral_sub hTG (integrable_const _),
    integral_const_mul, hin0]
  simp

/-- **Corrected Thm 1 of arXiv 2410.18720, in the form of the paper**: under the hypotheses of
`descent_estimate`,
`E ℒ(W₁) ≤ ℒ(W₀) - λ(1 - βλ/2) E ‖P(W₀) G‖² + λ E ‖P(W₀)(G - ∇ℒ(W₀))‖² + B E ‖W₁ - Ŵ‖`.
This is the printed inequality (with the factor of its proof) plus the term `λ · variance`, which
cannot be dropped (`geoLoRA_bound_false`; there this inequality is an equality). -/
theorem descent_estimate_of_variance (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B) {W₀ : Matrix m n ℝ}
    {G Wh W₁ : Ω → Matrix m n ℝ} {lr : ℝ} (hGm : AEStronglyMeasurable G μ)
    (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) μ) (hmean : ∫ ω, G ω ∂μ = g W₀)
    (hstep : ∀ ω, IsGeoLoRAUpdate (G ω) lr W₀ (Wh ω)) (hW₁ : AEStronglyMeasurable W₁ μ)
    (htr : Integrable (fun ω => ‖W₁ ω - Wh ω‖) μ) :
    ∫ ω, ℒ (W₁ ω) ∂μ ≤ ℒ W₀ - lr * (1 - β * lr / 2) * ∫ ω, ‖tangentAt W₀ (G ω)‖ ^ 2 ∂μ +
      lr * ∫ ω, ‖tangentAt W₀ (G ω - g W₀)‖ ^ 2 ∂μ + B * ∫ ω, ‖W₁ ω - Wh ω‖ ∂μ := by
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have h := descent_estimate hℒ hg hB hGm hG2 hmean hstep hW₁ htr
  rw [integral_norm_sq_split (hstep ω₀).isOrthProj hGm hG2 hmean]
  nlinarith

/-- **Corrected Thm 2 of arXiv 2410.18720 (convergence), with expectations.**  Let
`(ℱ_k)` be a filtration, `W_k` the `ℱ_k`-measurable iterates, `G_k` measurable minibatch gradients
with `E ‖G_k‖² < ∞`, unbiased given the past, `E[G_k | ℱ_k] = ∇ℒ(W_k)` (see
`condExp_sample_eq` for independent minibatches), and with bounded variance, `E ‖G_k - ∇ℒ(W_k)‖² ≤
σ²`.  Let every iteration be a step of Algorithm 1, for every sample, with arbitrary ranks and any
integrable truncation with `∑_k E ‖W_{k+1} - Ŵ_k‖ ≤ D`.  If `ℒ ≥ ℒ_inf` is `β`-smooth with
`‖∇ℒ‖ ≤ B`, `E |ℒ(W₀)| < ∞` and `λ_k ≥ 0` satisfy the Robbins–Monro conditions, then

`liminf_k E ‖P(W_k) ∇ℒ(W_k)‖² = 0`.

Differences from the paper.  The paper's conclusion contains the stochastic gradient; read
literally, `liminf E ‖P(W_k) G_k‖² = 0` is false (`stochastic_conclusion_false`), so this theorem
has the deterministic gradient `∇ℒ`.  The proof in the paper rests on the printed Thm 1, which is
false; here the variance enters and is summable through `∑ λ_k² < ∞`.  The variance bound `σ²`
follows from the paper's Assumption 3, `‖F(Z) - f(Z)‖ ≤ C` (App. C.3).  The restriction
`λ_k ≤ 2/L` is not needed.  The rank need not stabilise: only the sum of the truncation errors
matters.  The measurability of `P(W_k)` is proved (`stronglyMeasurable_tangentAt_apply`). -/
theorem convergence (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B) (hβ : 0 ≤ β)
    {ℱ : Filtration ℕ mΩ} {W G Wh : ℕ → Ω → Matrix m n ℝ} {lr : ℕ → ℝ} {σsq D ℒinf : ℝ}
    (hW : ∀ k, StronglyMeasurable[ℱ k] (W k)) (hW0 : Integrable (fun ω => ℒ (W 0 ω)) μ)
    (hGm : ∀ k, StronglyMeasurable (G k)) (hG2 : ∀ k, Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hmean : ∀ k, μ[G k | ℱ k] =ᵐ[μ] fun ω => g (W k ω))
    (hvar : ∀ k, ∫ ω, ‖G k ω - g (W k ω)‖ ^ 2 ∂μ ≤ σsq)
    (hstep : ∀ k ω, IsGeoLoRAUpdate (G k ω) (lr k) (W k ω) (Wh k ω))
    (htr : ∀ k, Integrable (fun ω => ‖W (k + 1) ω - Wh k ω‖) μ)
    (hD : ∀ n, ∑ k ∈ range n, ∫ ω, ‖W (k + 1) ω - Wh k ω‖ ∂μ ≤ D)
    (hinf : ∀ x, ℒinf ≤ ℒ x) (hlr0 : ∀ k, 0 ≤ lr k) (hdiv : ¬ Summable lr)
    (hsq : Summable fun k => lr k ^ 2) :
    liminf (fun k => ∫ ω, ‖tangentAt (W k ω) (g (W k ω))‖ ^ 2 ∂μ) atTop = 0 := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := β.toNNReal) fun x y => by
    rw [Real.coe_toNNReal _ hβ, dist_eq_norm, dist_eq_norm]
    exact hg x y).continuous
  have hWh : ∀ k ω, Wh k ω = W k ω - lr k • tangentAt (W k ω) (G k ω) := fun k ω =>
    (hstep k ω).eq
  have key := fun ε (hε : 0 < ε) N => exists_expected_projGrad_lt hℒ hg hB hβ (ℱ := ℱ) (W := W)
    (G := G) (Pr := fun k ω => tangentAt (W k ω)) (lr := lr) hW hW0 hGm hG2 hmean hvar
    (fun k ω => (hstep k ω).isOrthProj)
    (fun k => stronglyMeasurable_tangentAt_apply (mΩ := ℱ k) (hW k)
      (hgc.comp_stronglyMeasurable (hW k)))
    (fun k => stronglyMeasurable_tangentAt_apply ((hW k).mono (ℱ.le k)) (hGm k))
    (by simpa only [hWh] using htr) (by simpa only [hWh] using hD) hinf hlr0 hdiv hsq hε N
  set b : ℕ → ℝ := fun k => ∫ ω, ‖tangentAt (W k ω) (g (W k ω))‖ ^ 2 ∂μ with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => integral_nonneg fun ω => by positivity
  have hbB : ∀ k, b k ≤ B ^ 2 := fun k => by
    have hle : ∀ ω, ‖tangentAt (W k ω) (g (W k ω))‖ ^ 2 ≤ B ^ 2 := fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) (((hstep k ω).isOrthProj.norm_le _).trans (hB _)) 2
    calc b k ≤ ∫ _, B ^ 2 ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity)
            (integrable_const _) (Eventually.of_forall hle)
      _ = B ^ 2 := by simp
  have hbdd : IsBoundedUnder (· ≥ ·) atTop b := isBoundedUnder_of ⟨0, hb0⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop b :=
    (isBoundedUnder_of ⟨B ^ 2, hbB⟩).isCoboundedUnder_ge
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_liminf_of_le hcobdd (Eventually.of_forall hb0))
  rw [zero_add]
  refine liminf_le_of_frequently_le ?_ hbdd
  rw [frequently_atTop]
  intro N
  obtain ⟨k, hk, hlt⟩ := key ε hε N
  exact ⟨k, hk, hlt.le⟩

end Convergence

/-! ### Independent minibatches -/

section Sampling

open ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω Ξ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]

/-- **Unbiasedness given the past, for independent minibatches.**  Let the minibatch `ξ`, with
values in a finite set, be independent of the past `m₀`, and let `φ x ω` (the gradient for the
sample `x` at the iterate reached at `ω`) be `m₀`-measurable and bounded for each `x`.  Then
`E[φ(ξ, ·) | m₀] = ∑ₓ P(ξ = x) φ x`.  For `φ x ω = f x (W ω)` with `W` `m₀`-measurable, this is the
hypothesis of `convergence`, with `∇ℒ = ∑ₓ P(ξ = x) f x`, in the i.i.d. sampling of the paper. -/
theorem condExp_sample_eq {ξ : Ω → Ξ} (hξ : Measurable ξ) {m₀ : MeasurableSpace Ω} (hm : m₀ ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) m₀ μ) {φ : Ξ → Ω → E} {C : ℝ}
    (hφ : ∀ x, StronglyMeasurable[m₀] (φ x)) (hC : ∀ x ω, ‖φ x ω‖ ≤ C) :
    μ[fun ω => φ (ξ ω) ω | m₀] =ᵐ[μ] fun ω => ∑ x, μ.real (ξ ⁻¹' {x}) • φ x ω := by
  classical
  set i : Ξ → Ω → ℝ := fun x => (ξ ⁻¹' {x}).indicator 1 with hi
  have hA : ∀ x, MeasurableSet[MeasurableSpace.comap ξ inferInstance] (ξ ⁻¹' {x}) := fun x =>
    ⟨{x}, measurableSet_singleton x, rfl⟩
  have hA' : ∀ x, MeasurableSet[mΩ] (ξ ⁻¹' {x}) := fun x => hξ (measurableSet_singleton x)
  have him : ∀ x, StronglyMeasurable[MeasurableSpace.comap ξ inferInstance] (i x) := fun x =>
    stronglyMeasurable_const.indicator (hA x)
  have hii : ∀ x, Integrable (i x) μ := fun x =>
    (integrable_const (1 : ℝ)).indicator (hA' x)
  have hprod : ∀ x, Integrable (i x • φ x) μ := fun x => by
    refine Integrable.of_bound ((hii x).aestronglyMeasurable.smul
      ((hφ x).mono hm).aestronglyMeasurable) C (Eventually.of_forall fun ω => ?_)
    have h1 : ‖i x ω‖ ≤ 1 := by
      by_cases h : ω ∈ ξ ⁻¹' {x} <;> simp [hi, h]
    have h2 := hC x ω
    have h3 : (i x • φ x) ω = i x ω • φ x ω := rfl
    rw [h3, norm_smul]
    nlinarith [norm_nonneg (φ x ω), norm_nonneg (i x ω)]
  have hrep : (fun ω => φ (ξ ω) ω) = ∑ x, (i x • φ x) := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (ξ ω)]
    · simp [hi]
    · intro x _ hx
      have : ω ∉ ξ ⁻¹' {x} := fun h => hx h.symm
      simp [hi, this]
    · simp
  have hterm : ∀ x, μ[i x • φ x | m₀] =ᵐ[μ] fun ω => μ.real (ξ ⁻¹' {x}) • φ x ω := fun x => by
    have h1 := condExp_smul_of_aestronglyMeasurable_right (hii x) (hprod x)
      (hφ x).aestronglyMeasurable
    have h2 := condExp_indep_eq hξ.comap_le hm (him x) hind
    have h3 : ∫ ω, i x ω ∂μ = μ.real (ξ ⁻¹' {x}) := by
      have h6 := integral_indicator_const (μ := μ) (1 : ℝ) (hA' x)
      rw [smul_eq_mul, mul_one] at h6
      exact h6
    filter_upwards [h1, h2] with ω h4 h5
    rw [h4, Pi.smul_apply', h5, h3]
  have hsum := condExp_finsetSum (s := Finset.univ) (fun x _ => hprod x) m₀
  rw [hrep]
  refine hsum.trans ?_
  have hall : ∀ᵐ ω ∂μ, ∀ x, (μ[i x • φ x | m₀]) ω = μ.real (ξ ⁻¹' {x}) • φ x ω :=
    ae_all_iff.2 hterm
  filter_upwards [hall] with ω hω
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun x _ => hω x

end Sampling

/-! ### Theorem 3: the robust error bound -/

section ErrorBound

variable {m n : Type*} [Fintype m] [Fintype n]
variable {g : Matrix m n ℝ → Matrix m n ℝ} {β B ε σ ϑ lr t₀ : ℝ}

/-- **Thm 3 of arXiv 2410.18720, first bound, with explicit constants.**  Let `∇ℒ = g` be
`β`-Lipschitz and bounded by `B`, let `A` solve the gradient flow `Ȧ = -∇ℒ(A)` of eq. (12) on
`[t₀, t₀ + N λ]`, and let `W_k` be `N` iterations of Algorithm 1 with constant learning rate
`λ > 0`, where the gradient is exact up to `‖G_k - ∇ℒ(W_k)‖ ≤ σ` (the paper has `σ = 0`), the
truncation satisfies `‖W_{k+1} - Ŵ_k‖ ≤ ϑ` and `‖(I - P(W_k)) ∇ℒ(W_k)‖ ≤ ε`.  Then, for `k λ ≤ T`,

`‖W_k - A(t₀ + k λ)‖ ≤ e^{βT} (‖W_0 - A(t₀)‖ + T (β B λ / 2 + ε + σ) + k ϑ)`.

No constant depends on `S⁻¹` and the ranks may change.  Differences from the paper: the
smallness of the normal component is assumed at the iterates only (the paper assumes it near the
flow, and uses it at the iterates); the constants depend on `T`, which is unavoidable
(`not_uniformErrorBound`); `ϑ` bounds the truncation error in the Frobenius norm (see
`truncation_spec`).  The abstract iteration is
`LeanDLRA.GradientFlowConvergence.projectedGradient_global_error`. -/
theorem error_bound (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β)
    (hB : ∀ x, ‖g x‖ ≤ B) (hlr : 0 < lr) (hε0 : 0 ≤ ε) (hσ0 : 0 ≤ σ) {N : ℕ}
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution (fun _ x => -g x) A t₀ (t₀ + N * lr))
    {W Wh G : ℕ → Matrix m n ℝ} (hstep : ∀ k < N, IsGeoLoRAUpdate (G k) lr (W k) (Wh k))
    (hnormal : ∀ k < N, ‖(1 - tangentAt (W k)) (g (W k))‖ ≤ ε)
    (hnoise : ∀ k < N, ‖G k - g (W k)‖ ≤ σ) (htr : ∀ k < N, ‖W (k + 1) - Wh k‖ ≤ ϑ) {T : ℝ} :
    ∀ k ≤ N, (k : ℝ) * lr ≤ T → ‖W k - A (t₀ + k * lr)‖ ≤
      Real.exp (β * T) * (‖W 0 - A t₀‖ + T * (β * B * lr / 2 + ε + σ) + k * ϑ) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) β := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily hF hBF (fun _ => continuous_const) (t₀ := t₀) hlr.le W
  classical
  set Pr : ℕ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ := fun k =>
    if k < N then tangentAt (W k) else 0 with hPr
  have hPrk : ∀ k < N, Pr k = tangentAt (W k) := fun k hk => by simp [hPr, hk]
  refine GradientFlowConvergence.projectedGradient_global_error (g := G) (Pr := Pr) hg hβ hB hlr.le
    hε0 hσ0 hA (fun k _ => (hΦ k).1) (fun k _ => (hΦ k).2) (fun k => ?_) (fun k hk => ?_) hnoise
    (fun k hk => ?_)
  · by_cases hk : k < N
    · rw [hPrk k hk]
      exact (hstep k hk).isOrthProj
    · simp only [hPr, hk, ite_false]
      exact IsOrthProj.zero
  · rw [hPrk k hk]
    exact hnormal k hk
  · rw [hPrk k hk, ← (hstep k hk).eq]
    exact htr k hk

/-- Inversion is continuous on invertible matrices. -/
lemma continuousOn_inv {r : Type*} [Fintype r] [DecidableEq r] {S : ℝ → Matrix r r ℝ} {s : Set ℝ}
    (hS : ContinuousOn S s) (hdet : ∀ t ∈ s, IsUnit (S t).det) :
    ContinuousOn (fun t => (S t)⁻¹) s := by
  have e : (fun t => (S t)⁻¹) = fun t => ((S t).det)⁻¹ • (S t).adjugate := by
    funext t
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun t => (S t).det) s :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hS
  have h2 : ContinuousOn (fun t => (S t).adjugate) s :=
    (Continuous.matrix_adjugate continuous_id).comp_continuousOn hS
  exact (h1.inv₀ fun t ht => (hdet t ht).ne_zero).smul h2

/-- The right-hand side bound needed to keep the factors of (4) orthonormal, from compactness. -/
lemma exists_bound_factor {r : Type*} [Fintype r] [DecidableEq r] {U : ℝ → Matrix m r ℝ}
    {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ} {Ad : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hU : ContinuousOn U (Icc a b)) (hS : ContinuousOn S (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hAd : ContinuousOn Ad (Icc a b))
    (hdet : ∀ t ∈ Icc a b, IsUnit (S t).det) :
    (∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(U t)ᵀ * (Ad t * V t * (S t)⁻¹)‖ ≤ C) ∧
    (∀ b' < b, ∃ C, ∀ t ∈ Ico a b', ‖(V t)ᵀ * ((Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ)‖ ≤ C) := by
  have hSi := continuousOn_inv hS hdet
  have h1 : ContinuousOn (fun t => (U t)ᵀ * (Ad t * V t * (S t)⁻¹)) (Icc a b) :=
    GaugeODE.continuousOn_mul (GaugeODE.continuousOn_transpose hU)
      (GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul hAd hV) hSi)
  have h2 : ContinuousOn (fun t => (V t)ᵀ * ((Ad t)ᵀ * U t * ((S t)⁻¹)ᵀ)) (Icc a b) :=
    GaugeODE.continuousOn_mul (GaugeODE.continuousOn_transpose hV)
      (GaugeODE.continuousOn_mul
        (GaugeODE.continuousOn_mul (GaugeODE.continuousOn_transpose hAd) hU)
        (GaugeODE.continuousOn_transpose hSi))
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
  exact ⟨fun b' hb' => ⟨C₁, fun t ht => hC₁ t ⟨ht.1, (ht.2.trans hb').le⟩⟩,
    fun b' hb' => ⟨C₂, fun t ht => hC₂ t ⟨ht.1, (ht.2.trans hb').le⟩⟩⟩

variable {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq m] [DecidableEq n]

/-- The Riemannian flow in the factor form (4) of arXiv 2410.18720 is close to the gradient flow
(the step `‖W(t) - W_RF(t)‖ ≤ c ε` of the proof of Thm 3): if `U`, `S`, `V` solve eq. (4) on
`[a, b]` with orthonormal initial factors and `S` invertible on `[a, b]`, then `U`, `V` stay
orthonormal, `Y = U S Vᵀ` solves `Ẏ = -P(Y) ∇ℒ(Y)`, and, if the normal component along `Y` is at
most `ε`, then `‖Y(t) - A(t)‖ ≤ e^{β(t-a)} (‖Y(a) - A(a)‖ + ε (t - a))`. -/
theorem riemannian_flow_close (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hε0 : 0 ≤ ε)
    {a b : ℝ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution (fun _ x => -g x) A a b)
    {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * (-g (U t * S t * (V t)ᵀ)) * V t * (S t)⁻¹) U a b)
    (hS : ODESolution (fun t _ => (U t)ᵀ * (-g (U t * S t * (V t)ᵀ)) * V t) S a b)
    (hV : ODESolution (fun t X => (1 - X * Xᵀ) * (-g (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)
      V a b)
    (hdet : ∀ t ∈ Icc a b, IsUnit (S t).det) (hUa : (U a)ᵀ * U a = 1) (hVa : (V a)ᵀ * V a = 1)
    (hnormal : ∀ t ∈ Ico a b, ‖(1 - tangentProj (U t) (V t)) (g (U t * S t * (V t)ᵀ))‖ ≤ ε) :
    (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1) ∧
      ODESolution (fun t x => tangentProj (U t) (V t) (-g x)) (fun t => U t * S t * (V t)ᵀ) a b ∧
      ∀ t ∈ Icc a b, ‖U t * S t * (V t)ᵀ - A t‖ ≤ Real.exp (β * (t - a)) *
        (‖U a * S a * (V a)ᵀ - A a‖ + ε * (t - a)) := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := β.toNNReal) fun x y => by
    rw [Real.coe_toNNReal _ hβ, dist_eq_norm, dist_eq_norm]
    exact hg x y).continuous
  have hYc : ContinuousOn (fun t => U t * S t * (V t)ᵀ) (Icc a b) :=
    GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul hU.cont hS.cont)
      (GaugeODE.continuousOn_transpose hV.cont)
  have hAd : ContinuousOn (fun t => -g (U t * S t * (V t)ᵀ)) (Icc a b) :=
    (hgc.comp_continuousOn hYc).neg
  obtain ⟨hCU, hCV⟩ := exists_bound_factor hU.cont hS.cont hV.cont hAd hdet
  obtain ⟨ho, hY⟩ := factorODE_solution_isDLRA_tangentProj hU hS hV
    (fun t ht => hdet t (Ico_subset_Icc_self ht)) hCU hCV hUa hVa
  have hY' : ODESolution (fun t x => tangentProj (U t) (V t) (-g x))
      (fun t => U t * S t * (V t)ᵀ) a b := ⟨hY.cont, hY.deriv⟩
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) β := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  refine ⟨fun t ht => ⟨(ho t ht).1, (ho t ht).2.1⟩, hY', ?_⟩
  exact ODESolution.dlra_norm_sub_le_exp_mul (P := fun t => tangentProj (U t) (V t)) hF hβ hε0 hA
    hY' (fun t ht => by rw [map_neg, norm_neg]; exact hnormal t ht) le_rfl

/-- **Thm 3 of arXiv 2410.18720 (robust error bound).**  Under the hypotheses of `error_bound`
with exact gradients and `A(t₀) = W₀`, and if `W_RF = U S Vᵀ` solves the Riemannian flow (4) with
`W_RF(t₀) = W₀` and normal component at most `ε`, then for `t = t₀ + k λ` with `k λ ≤ T`,
eqs. (13), (14):

`‖W(t) - W_k‖ ≤ c₁ ε + c₂ λ + c₃ ϑ / λ`,  `‖W_RF(t) - W_k‖ ≤ c₄ ε + c₂ λ + c₃ ϑ / λ`,

with `c₁ = c₃ = T e^{βT}`, `c₂ = β B T e^{βT} / 2`, `c₄ = 2 T e^{βT}`.  These constants depend only
on `β`, `B`, `T`, not on the singular values; by `not_uniformErrorBound` the dependence on `T`
cannot be removed, contrary to the statement of the paper.  See also `error_bound` for inexact
gradients and initial data. -/
theorem theorem3 (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hB : ∀ x, ‖g x‖ ≤ B)
    (hlr : 0 < lr) (hε0 : 0 ≤ ε) (hϑ : 0 ≤ ϑ) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A t₀ (t₀ + N * lr))
    {W Wh : ℕ → Matrix m n ℝ} (hA0 : A t₀ = W 0)
    (hstep : ∀ k < N, IsGeoLoRAUpdate (g (W k)) lr (W k) (Wh k))
    (hnormal : ∀ k < N, ‖(1 - tangentAt (W k)) (g (W k))‖ ≤ ε)
    (htr : ∀ k < N, ‖W (k + 1) - Wh k‖ ≤ ϑ) {T : ℝ}
    {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    (hU : ODESolution (fun t X => (1 - X * Xᵀ) * (-g (U t * S t * (V t)ᵀ)) * V t * (S t)⁻¹) U t₀
      (t₀ + N * lr))
    (hS : ODESolution (fun t _ => (U t)ᵀ * (-g (U t * S t * (V t)ᵀ)) * V t) S t₀ (t₀ + N * lr))
    (hV : ODESolution (fun t X => (1 - X * Xᵀ) * (-g (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)
      V t₀ (t₀ + N * lr))
    (hdet : ∀ t ∈ Icc t₀ (t₀ + N * lr), IsUnit (S t).det) (hUa : (U t₀)ᵀ * U t₀ = 1)
    (hVa : (V t₀)ᵀ * V t₀ = 1) (hRF0 : U t₀ * S t₀ * (V t₀)ᵀ = W 0)
    (hnormalRF : ∀ t ∈ Ico t₀ (t₀ + N * lr),
      ‖(1 - tangentProj (U t) (V t)) (g (U t * S t * (V t)ᵀ))‖ ≤ ε) :
    ∀ k ≤ N, (k : ℝ) * lr ≤ T →
      ‖A (t₀ + k * lr) - W k‖ ≤ T * Real.exp (β * T) * ε +
          β * B * T * Real.exp (β * T) / 2 * lr + T * Real.exp (β * T) * (ϑ / lr) ∧
      ‖U (t₀ + k * lr) * S (t₀ + k * lr) * (V (t₀ + k * lr))ᵀ - W k‖ ≤
        2 * T * Real.exp (β * T) * ε + β * B * T * Real.exp (β * T) / 2 * lr +
          T * Real.exp (β * T) * (ϑ / lr) := by
  intro k hk hT
  have hk0 : 0 ≤ (k : ℝ) * lr := by positivity
  have hT0 : 0 ≤ T := hk0.trans hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hexp := Real.exp_pos (β * T)
  have h1 := error_bound (G := fun k => g (W k)) (σ := 0) hg hβ hB hlr hε0 le_rfl hA hstep hnormal
    (fun _ _ => by simp) htr k hk hT
  rw [hA0, sub_self, norm_zero, add_zero, zero_add] at h1
  have hkϑ : (k : ℝ) * ϑ ≤ T * (ϑ / lr) := by
    calc (k : ℝ) * ϑ ≤ T / lr * ϑ :=
          mul_le_mul_of_nonneg_right ((le_div_iff₀ hlr).2 hT) hϑ
      _ = T * (ϑ / lr) := by ring
  have h2 : ‖A (t₀ + k * lr) - W k‖ ≤ T * Real.exp (β * T) * ε +
      β * B * T * Real.exp (β * T) / 2 * lr + T * Real.exp (β * T) * (ϑ / lr) := by
    rw [norm_sub_rev]
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left hkϑ hexp.le
    nlinarith
  refine ⟨h2, ?_⟩
  have hNlr : (k : ℝ) * lr ≤ N * lr :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hk) hlr.le
  obtain ⟨-, -, h3⟩ := riemannian_flow_close hg hβ hε0 hA hU hS hV hdet hUa hVa hnormalRF
  have h4 := h3 (t₀ + k * lr) ⟨by linarith, by linarith⟩
  rw [hRF0, hA0, sub_self, norm_zero, zero_add, add_sub_cancel_left] at h4
  have h5 : ‖U (t₀ + k * lr) * S (t₀ + k * lr) * (V (t₀ + k * lr))ᵀ - A (t₀ + k * lr)‖ ≤
      T * Real.exp (β * T) * ε := by
    refine h4.trans ?_
    have h6 : Real.exp (β * (k * lr)) ≤ Real.exp (β * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hβ)
    calc Real.exp (β * (k * lr)) * (ε * (k * lr)) ≤ Real.exp (β * T) * (ε * T) := by gcongr
      _ = T * Real.exp (β * T) * ε := by ring
  have h7 := norm_sub_le_norm_sub_add_norm_sub
    (U (t₀ + k * lr) * S (t₀ + k * lr) * (V (t₀ + k * lr))ᵀ) (A (t₀ + k * lr)) (W k)
  linarith

end ErrorBound

/-! ### The constants of Theorem 3 must depend on the time horizon -/

section TimeDependence

/-- `e₁` as a column. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- `e₂` as a column. -/
def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The projector `e₁ e₁ᵀ`. -/
def Pe : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

lemma e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₁_mul : e₁ * e₁ᵀ = Pe := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, Pe, Matrix.mul_apply]

lemma hat_orth : (Matrix.fromCols e₁ e₂)ᵀ * Matrix.fromCols e₁ e₂ = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma e₂_mul : e₂ * e₂ᵀ = 1 - Pe := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₂, Pe, Matrix.mul_apply]

lemma Pe_mul : Pe * Pe = Pe := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pe, Matrix.mul_apply, Fin.sum_univ_two]

lemma hat_proj : Matrix.fromCols e₁ e₂ * (Matrix.fromCols e₁ e₂)ᵀ = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, e₁_mul, e₂_mul]
  abel

lemma tangentProj_one : tangentProj e₁ e₁ 1 = Pe := by
  have h1 : e₁ * e₁ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) = Pe := by rw [e₁_mul, Matrix.mul_one]
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) * e₁ * e₁ᵀ = Pe := by rw [Matrix.one_mul, e₁_mul]
  have h3 : e₁ * e₁ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * e₁ * e₁ᵀ = Pe := by
    rw [h1, Matrix.mul_assoc, e₁_mul, Pe_mul]
  rw [tangentProj_apply, h3, h1, h2]
  abel

lemma norm_one_lt : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ < 2 := by
  have h : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Matrix.one_apply]
  nlinarith [norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

/-- The trace `⟪I, W⟫`. -/
noncomputable def tr2 (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ⟪(1 : Matrix (Fin 2) (Fin 2) ℝ), W⟫

lemma tr2_Pe (w : ℝ) : tr2 (w • Pe) = w := by
  simp [tr2, Frobenius.inner_def, Fin.sum_univ_two, Pe, Matrix.one_apply]

lemma tr2_add_smul (w a : ℝ) : tr2 (w • Pe + a • 1) = w + 2 * a := by
  simp [tr2, Frobenius.inner_def, Fin.sum_univ_two, Pe, Matrix.one_apply]
  ring

/-- The bounded loss `ℒ(W) = -arctan(sinh(tr W))`. -/
noncomputable def ceLoss (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  -Real.arctan (Real.sinh (tr2 W))

/-- The gradient of `ceLoss`: `∇ℒ(W) = -sech(tr W) I`. -/
noncomputable def ceGrad (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (-(Real.cosh (tr2 W))⁻¹) • 1

lemma hasDerivAt_ceLoss_aux (x : ℝ) :
    HasDerivAt (fun x => -Real.arctan (Real.sinh x)) (-(Real.cosh x)⁻¹) x := by
  have h1 := (Real.hasDerivAt_arctan (Real.sinh x)).comp x (Real.hasDerivAt_sinh x)
  have e : 1 / (1 + Real.sinh x ^ 2) * Real.cosh x = (Real.cosh x)⁻¹ := by
    have h2 : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by rw [Real.cosh_sq]; ring
    have h3 := (Real.cosh_pos x).ne'
    rw [h2]
    field_simp
  rw [e] at h1
  exact h1.neg

lemma hasFDerivAt_ceLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt ceLoss (innerSL ℝ (ceGrad W)) W := by
  have h1 : HasFDerivAt tr2 (innerSL ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)) W :=
    (innerSL ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)).hasFDerivAt
  have h2 := (hasDerivAt_ceLoss_aux (tr2 W)).comp_hasFDerivAt W h1
  have e : innerSL ℝ (ceGrad W) =
      (-(Real.cosh (tr2 W))⁻¹) • innerSL ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext X
    simp [ceGrad]
  rw [e]
  exact h2

lemma abs_ceLoss_le (W : Matrix (Fin 2) (Fin 2) ℝ) : |ceLoss W| ≤ 2 := by
  have h1 := Real.arctan_lt_pi_div_two (Real.sinh (tr2 W))
  have h2 := Real.neg_pi_div_two_lt_arctan (Real.sinh (tr2 W))
  have h3 := Real.pi_lt_four
  rw [ceLoss, abs_neg]
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma abs_sech_sub_le (a b : ℝ) : |(Real.cosh a)⁻¹ - (Real.cosh b)⁻¹| ≤ |a - b| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => (Real.cosh x)⁻¹)
      (-Real.sinh x / Real.cosh x ^ 2) x := fun x =>
    (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
  have hb : ∀ x : ℝ, ‖-Real.sinh x / Real.cosh x ^ 2‖ ≤ 1 := fun x => by
    have h1 := Real.one_le_cosh x
    have h2 := Real.sinh_lt_cosh x
    have h3 := Real.sinh_lt_cosh (-x)
    rw [Real.sinh_neg, Real.cosh_neg] at h3
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : 0 < Real.cosh x ^ 2),
      div_le_one (by positivity)]
    have h4 : |Real.sinh x| ≤ Real.cosh x := abs_le.2 ⟨by linarith, h2.le⟩
    nlinarith
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x) (mem_univ b) (mem_univ a)
  simpa using h

lemma abs_tr2_sub_le (x y : Matrix (Fin 2) (Fin 2) ℝ) :
    |tr2 x - tr2 y| ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * ‖x - y‖ := by
  rw [tr2, tr2, ← inner_sub_right]
  exact abs_real_inner_le_norm _ _

lemma ceGrad_lipschitz (x y : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖ceGrad x - ceGrad y‖ ≤ 4 * ‖x - y‖ := by
  have h0 := norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have h1 := norm_one_lt
  have e : ceGrad x - ceGrad y =
      (-((Real.cosh (tr2 x))⁻¹ - (Real.cosh (tr2 y))⁻¹)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [ceGrad, ceGrad, ← sub_smul]
    congr 1
    ring
  rw [e, norm_smul, norm_neg, Real.norm_eq_abs]
  have h2 := (abs_sech_sub_le (tr2 x) (tr2 y)).trans (abs_tr2_sub_le x y)
  have h3 := norm_nonneg (x - y)
  nlinarith [abs_nonneg ((Real.cosh (tr2 x))⁻¹ - (Real.cosh (tr2 y))⁻¹), mul_nonneg h0 h3]

lemma norm_ceGrad_lt (W : Matrix (Fin 2) (Fin 2) ℝ) : ‖ceGrad W‖ < 2 := by
  have h1 := Real.one_le_cosh (tr2 W)
  have h2 : (Real.cosh (tr2 W))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have h3 : 0 < (Real.cosh (tr2 W))⁻¹ := inv_pos.2 (Real.cosh_pos _)
  rw [ceGrad, norm_smul, norm_neg, Real.norm_of_nonneg h3.le]
  nlinarith [norm_one_lt, norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

/-- The singular value of the iterate `W_k = w_k e₁ e₁ᵀ`: `w_{k+1} = w_k + sech(w_k)`. -/
noncomputable def ceSeq : ℕ → ℝ
  | 0 => 1
  | k + 1 => ceSeq k + (Real.cosh (ceSeq k))⁻¹

lemma ceSeq_pos (k : ℕ) : 0 < ceSeq k := by
  induction k with
  | zero => simp [ceSeq]
  | succ k ih =>
    have := inv_pos.2 (Real.cosh_pos (ceSeq k))
    simp only [ceSeq]
    linarith

/-- The core of the iterate. -/
noncomputable def coreS (k : ℕ) : Matrix (Fin 1) (Fin 1) ℝ := ceSeq k • 1

lemma coreS_det (k : ℕ) : IsUnit (coreS k).det := by
  simpa [coreS, Matrix.det_fin_one] using (ceSeq_pos k).ne'

/-- The iterates of the counterexample. -/
noncomputable def ceW (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := ceSeq k • Pe

lemma ceW_eq (k : ℕ) : ceW k = e₁ * coreS k * e₁ᵀ := by
  rw [coreS, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e₁_mul, ceW]

lemma ce_step (k : ℕ) : IsGeoLoRAStep (ceGrad (ceW k)) 1 e₁ (coreS k) e₁ e₂ e₂ :=
  ⟨e₁_orth, e₁_orth, coreS_det k, hat_orth, hat_orth, by rw [hat_proj, Matrix.one_mul],
    by rw [hat_proj, Matrix.one_mul]⟩

lemma ce_what (k : ℕ) : geoWhat (ceGrad (ceW k)) 1 e₁ (coreS k) e₁ e₂ e₂ = ceW (k + 1) := by
  rw [geoWhat_eq (ce_step k), ← ceW_eq, ceGrad, map_smul, tangentProj_one]
  simp only [ceW, ceSeq, tr2_Pe, one_smul, add_smul, neg_smul, sub_neg_eq_add]

lemma ce_update (k : ℕ) : IsGeoLoRAUpdate (ceGrad (ceW k)) 1 (ceW k) (ceW (k + 1)) :=
  ⟨1, 1, 1, e₁, coreS k, e₁, e₂, e₂, ce_step k, ceW_eq k, (ce_what k).symm⟩

/-- The growth of the gradient flow: `a(t) = (arsinh(2 t + sinh 1) - 1) / 2`. -/
noncomputable def ceA (t : ℝ) : ℝ := (Real.arsinh (2 * t + Real.sinh 1) - 1) / 2

/-- The gradient flow of the counterexample, `W(t) = e₁ e₁ᵀ + a(t) I`. -/
noncomputable def ceFlow (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (1 : ℝ) • Pe + ceA t • 1

lemma ode_ceFlow (T : ℝ) : ODESolution (fun _ x => -ceGrad x) ceFlow 0 T := by
  have h : ∀ t : ℝ, HasDerivAt ceFlow (-ceGrad (ceFlow t)) t := fun t => by
    have ht : tr2 (ceFlow t) = Real.arsinh (2 * t + Real.sinh 1) := by
      rw [ceFlow, tr2_add_smul, ceA]
      ring
    have h1 : HasDerivAt (fun t : ℝ => 2 * t + Real.sinh 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).add_const (Real.sinh 1)
    have h2 := (Real.hasDerivAt_arsinh (2 * t + Real.sinh 1)).comp t h1
    have h3 : HasDerivAt ceA (√(1 + (2 * t + Real.sinh 1) ^ 2))⁻¹ t := by
      have h4 := (h2.sub_const 1).div_const 2
      rw [show (√(1 + (2 * t + Real.sinh 1) ^ 2))⁻¹ * 2 / 2 =
        (√(1 + (2 * t + Real.sinh 1) ^ 2))⁻¹ by ring] at h4
      exact h4
    have h5 := (h3.smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).const_add ((1 : ℝ) • Pe)
    have e : -ceGrad (ceFlow t) =
        (√(1 + (2 * t + Real.sinh 1) ^ 2))⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [ceGrad, ht, Real.cosh_arsinh, neg_smul, neg_neg]
    rw [e]
    exact h5
  exact ⟨fun t _ => (h t).continuousAt.continuousWithinAt, fun t _ => (h t).hasDerivWithinAt⟩

/-- The statement of Thm 3 of arXiv 2410.18720 with constants `c₁, c₂, c₃` that depend on the
smoothness constant `β` and the bound `B` only, for `2 × 2` matrices.  `B` bounds both the loss
(Sec. 4.2 of the paper) and its gradient (its Assumption 2), and the normal-component assumption
is imposed in its strongest form, for all matrices `Z`. -/
def UniformErrorBound (β B c₁ c₂ c₃ : ℝ) : Prop :=
  ∀ (ℒ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (W Wh : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (lr ε ϑ : ℝ),
    (∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) → (∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) →
    (∀ x, |ℒ x| ≤ B) → (∀ x, ‖g x‖ ≤ B) → 0 < lr →
    (∀ T, ODESolution (fun _ x => -g x) A 0 T) → A 0 = W 0 →
    (∀ k, IsGeoLoRAUpdate (g (W k)) lr (W k) (Wh k)) → (∀ k, ‖W (k + 1) - Wh k‖ ≤ ϑ) →
    (∀ Z, ‖(1 - tangentAt Z) (g Z)‖ < ε) →
    ∀ k : ℕ, ‖A (k * lr) - W k‖ ≤ c₁ * ε + c₂ * lr + c₃ * ϑ / lr

/-- **Thm 3 of arXiv 2410.18720 is false with constants depending only on `L` and `B`**: for all
`β ≥ 4`, `B ≥ 2` and all `c₁, c₂, c₃` the bound fails.  For the bounded loss
`ℒ(W) = -arctan(sinh(tr W))` on `2 × 2` matrices, `W₀ = e₁ e₁ᵀ`, `λ = 1`, the gradient flow is
`W(t) = W₀ + a(t) I` with `a(t) = (arsinh(2 t + sinh 1) - 1) / 2 → ∞`, whereas Algorithm 1 stays in
`span(e₁ e₁ᵀ)`, with no truncation at all (`ϑ = 0`), and `‖(I - P(Z)) ∇ℒ(Z)‖ ≤ ‖∇ℒ‖ < 2 = ε` for
all `Z`.  So the entry `(2, 2)` of the error, `a(k)`, is unbounded.  The correct constants contain
`T e^{βT}`: `theorem3`. -/
theorem not_uniformErrorBound {β B : ℝ} (hβ : 4 ≤ β) (hB : 2 ≤ B) (c₁ c₂ c₃ : ℝ) :
    ¬ UniformErrorBound β B c₁ c₂ c₃ := by
  intro h
  set C := c₁ * 2 + c₂ * 1 with hC
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.sinh (2 * C + 1))
  have key := h ceLoss ceGrad ceFlow ceW (fun k => ceW (k + 1)) 1 2 0
    hasFDerivAt_ceLoss
    (fun x y => (ceGrad_lipschitz x y).trans
      (mul_le_mul_of_nonneg_right hβ (norm_nonneg _)))
    (fun x => (abs_ceLoss_le x).trans hB) (fun x => (norm_ceGrad_lt x).le.trans hB)
    one_pos ode_ceFlow (by simp [ceFlow, ceA, ceW, ceSeq]) ce_update (fun k => by simp)
    (fun Z => ((isOrthProj_tangentAt Z).norm_sub_le (ceGrad Z)).trans_lt (norm_ceGrad_lt Z)) k
  simp only [mul_zero, zero_div, add_zero, mul_one] at key
  have hentry : ceA k ≤ ‖ceFlow k - ceW k‖ := by
    have h1 := Frobenius.abs_apply_le_norm (ceFlow k - ceW k) 1 1
    have h2 : (ceFlow k - ceW k) 1 1 = ceA k := by
      simp [ceFlow, ceW, Pe]
    rw [h2] at h1
    exact (le_abs_self _).trans h1
  have hs1 : 0 ≤ Real.sinh 1 := Real.sinh_nonneg_iff.2 zero_le_one
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlt : Real.sinh (2 * C + 1) < 2 * k + Real.sinh 1 := by linarith
  have h3 := Real.arsinh_strictMono hlt
  rw [Real.arsinh_sinh] at h3
  have h4 : C < ceA k := by
    rw [ceA]
    linarith
  simp only [hC] at h4 ⊢
  linarith

end TimeDependence

/-! ### The multi-layer structure -/

section Blocks

variable {m n ι : Type*} [Fintype m] [Fintype n]

/-- A family of pairwise orthogonal orthogonal projectors `E i` (in the paper: the diagonal
projectors onto the neurons of one layer). -/
structure IsBlockFamily {a : Type*} [Fintype a] (E : ι → Matrix a a ℝ) : Prop where
  symm : ∀ i, (E i)ᵀ = E i
  idem : ∀ i, E i * E i = E i
  orth : ∀ i j, i ≠ j → E i * E j = 0

/-- Left multiplication by a member of a block family is an orthogonal projector. -/
lemma IsBlockFamily.isOrthProj_left {a b : Type*} [Fintype a] [Fintype b]
    {E : ι → Matrix a a ℝ} (hE : IsBlockFamily E) (i : ι) :
    IsOrthProj (Frobenius.leftMulCLM (E i) : Matrix a b ℝ →L[ℝ] Matrix a b ℝ) :=
  ⟨fun X => by simp [← Matrix.mul_assoc, hE.idem], fun X Y => by
    simp only [Frobenius.leftMulCLM_apply]
    rw [Frobenius.inner_mul_left, hE.symm]⟩

/-- Right multiplication by a member of a block family is an orthogonal projector. -/
lemma IsBlockFamily.isOrthProj_right {a b : Type*} [Fintype a] [Fintype b]
    {F : ι → Matrix b b ℝ} (hF : IsBlockFamily F) (i : ι) :
    IsOrthProj (Frobenius.rightMulCLM (F i) : Matrix a b ℝ →L[ℝ] Matrix a b ℝ) :=
  ⟨fun X => by simp [Matrix.mul_assoc, hF.idem], fun X Y => by
    simp only [Frobenius.rightMulCLM_apply]
    rw [Frobenius.inner_mul_right, hF.symm]⟩

lemma IsBlockFamily.norm_mul_left {a b : Type*} [Fintype a] [Fintype b]
    {E : ι → Matrix a a ℝ} (hE : IsBlockFamily E) (i : ι) (X : Matrix a b ℝ) :
    ‖E i * X‖ ≤ ‖X‖ :=
  (hE.isOrthProj_left i).norm_le X

lemma IsBlockFamily.norm_mul_right {a b : Type*} [Fintype a] [Fintype b]
    {F : ι → Matrix b b ℝ} (hF : IsBlockFamily F) (i : ι) (X : Matrix a b ℝ) :
    ‖X * F i‖ ≤ ‖X‖ :=
  (hF.isOrthProj_right i).norm_le X

variable [Fintype ι]

/-- The block mask `Π Z = ∑ᵢ Eᵢ Z Fᵢ` of arXiv 2410.18720, App. I: `Π` keeps the blocks
(rows of layer `i`, columns of layer `i + 1`) of an adjacency matrix. -/
noncomputable def blockMask (E : ι → Matrix m m ℝ) (F : ι → Matrix n n ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  ∑ i, (Frobenius.leftMulCLM (E i)).comp (Frobenius.rightMulCLM (F i))

lemma blockMask_apply (E : ι → Matrix m m ℝ) (F : ι → Matrix n n ℝ) (Z : Matrix m n ℝ) :
    blockMask E F Z = ∑ i, E i * Z * F i := by
  simp [blockMask, Matrix.mul_assoc]

variable {E : ι → Matrix m m ℝ} {F : ι → Matrix n n ℝ}

lemma mul_blockMask (hE : IsBlockFamily E) (i : ι) (Z : Matrix m n ℝ) :
    E i * blockMask E F Z = E i * Z * F i := by
  classical
  rw [blockMask_apply, Matrix.mul_sum, Finset.sum_eq_single i]
  · simp only [← Matrix.mul_assoc, hE.idem]
  · intro j _ hj
    simp only [← Matrix.mul_assoc, hE.orth i j hj.symm, Matrix.zero_mul]
  · simp

lemma blockMask_mul (hF : IsBlockFamily F) (i : ι) (Z : Matrix m n ℝ) :
    blockMask E F Z * F i = E i * Z * F i := by
  classical
  rw [blockMask_apply, Matrix.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.mul_assoc, hF.idem]
  · intro j _ hj
    rw [Matrix.mul_assoc, hF.orth j i hj, Matrix.mul_zero]
  · simp

/-- **`Π` is an orthogonal projector**, as used in arXiv 2410.18720, proof of Prop. 3. -/
theorem isOrthProj_blockMask (hE : IsBlockFamily E) (hF : IsBlockFamily F) :
    IsOrthProj (blockMask E F) := by
  refine ⟨fun Z => ?_, fun X Y => ?_⟩
  · have e : ∀ i, E i * blockMask E F Z * F i = E i * Z * F i := fun i => by
      rw [mul_blockMask hE, Matrix.mul_assoc, hF.idem]
    calc blockMask E F (blockMask E F Z) = ∑ i, E i * blockMask E F Z * F i :=
          blockMask_apply E F _
      _ = ∑ i, E i * Z * F i := Finset.sum_congr rfl fun i _ => e i
      _ = blockMask E F Z := (blockMask_apply E F Z).symm
  · rw [blockMask_apply, blockMask_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, hE.symm, hF.symm,
      Matrix.mul_assoc (E i) Y]

lemma transpose_blockMask (hE : IsBlockFamily E) (hF : IsBlockFamily F) (Z : Matrix m n ℝ) :
    (blockMask E F Z)ᵀ = blockMask F E Zᵀ := by
  rw [blockMask_apply, blockMask_apply, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.transpose_mul, hE.symm, hF.symm, Matrix.mul_assoc]

/-- The commutator of the column projector of `Y = U S Vᵀ` with a layer projector `E` is controlled
by the defect `R = E Y - Y F` of the block structure of `Y`, and by `S⁻¹`: this is what replaces
the block SVD of `Y` in the proof of Prop. 2 of arXiv 2410.18720. -/
lemma norm_commutator_le {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S.det) {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : Aᵀ = A) :
    ‖U * Uᵀ * A - A * (U * Uᵀ)‖ ≤
      2 * (‖A * (U * S * Vᵀ) - U * S * Vᵀ * B‖ * ‖S⁻¹‖) := by
  classical
  set R := A * (U * S * Vᵀ) - U * S * Vᵀ * B with hR
  set a := (1 - U * Uᵀ) * A * U with ha
  have hPU : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hUe : U = U * S * Vᵀ * (V * S⁻¹) := by
    rw [Matrix.mul_assoc (U * S), ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
  have hPY : (1 - U * Uᵀ) * (U * S * Vᵀ * B) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPU]
    simp
  have ha1 : a = (1 - U * Uᵀ) * R * V * S⁻¹ := by
    have e : A * U = R * (V * S⁻¹) + U * S * Vᵀ * B * (V * S⁻¹) := by
      rw [hR, Matrix.sub_mul, sub_add_cancel, Matrix.mul_assoc A, ← hUe]
    rw [ha, Matrix.mul_assoc, e, Matrix.mul_add, ← Matrix.mul_assoc (1 - U * Uᵀ) (U * S * Vᵀ * B),
      hPY]
    simp [Matrix.mul_assoc]
  have ha2 : ‖a‖ ≤ ‖R‖ * ‖S⁻¹‖ := by
    rw [ha1]
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_le_of_orthonormal hV _).trans ?_
    have := (isOrthProj_leftProj (n := n) hU).compl.norm_le R
    rwa [one_sub_leftProj_apply] at this
  have hP : (U * Uᵀ)ᵀ = U * Uᵀ := by simp [Matrix.transpose_mul]
  have e1 : (1 - U * Uᵀ) * A * (U * Uᵀ) = a * Uᵀ := by rw [ha, Matrix.mul_assoc _ U]
  have e2 : U * Uᵀ * A * (1 - U * Uᵀ) = (a * Uᵀ)ᵀ := by
    rw [← e1]
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hP, hA,
      Matrix.mul_assoc]
  have e3 : U * Uᵀ * A - A * (U * Uᵀ) = (a * Uᵀ)ᵀ - a * Uᵀ := by
    rw [← e2, ← e1]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e3]
  refine (norm_sub_le _ _).trans ?_
  rw [Frobenius.norm_transpose, Frobenius.norm_mul_transpose_of_orthonormal hU]
  linarith

/-- The block defect of `P Z` for `Z` in the range of `Π`, by the commutators of `P` with the
`Eᵢ`. -/
lemma norm_compl_mul_le (hF : IsBlockFamily F) {P : Matrix m m ℝ} {c : ℝ}
    (hc : ∀ i, ‖P * E i - E i * P‖ ≤ c) {Z : Matrix m n ℝ} (hZ : blockMask E F Z = Z) :
    ‖(1 - blockMask E F) (P * Z)‖ ≤ Fintype.card ι * c * ‖Z‖ := by
  have e : (1 - blockMask E F) (P * Z) = ∑ i, (P * E i - E i * P) * Z * F i := by
    have h1 : P * Z = ∑ i, P * (E i * Z * F i) := by
      nth_rewrite 1 [← hZ]
      rw [blockMask_apply, Matrix.mul_sum]
    have h2 : (1 - blockMask E F) (P * Z) = P * Z - ∑ i, E i * (P * Z) * F i := by
      rw [sub_apply, one_apply_eq_self, blockMask_apply]
    rw [h2]
    nth_rewrite 1 [h1]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), ‖(P * E i - E i * P) * Z * F i‖ ≤ c * ‖Z‖ :=
    fun i _ => ((hF.norm_mul_right i _).trans (Frobenius.norm_mul_le _ _)).trans
      (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  simp [mul_assoc]

/-- **Key estimate for Prop. 2 of arXiv 2410.18720.**  For `Y = U S Vᵀ` of full rank `r`, and `Z`
in the range of the mask `Π`, the part of `P(Y) Z` outside the range of `Π` is controlled by the
part of `Y` outside the range of `Π`:
`‖(1 - Π) P(Y) Z‖ ≤ 16 k ‖S⁻¹‖ ‖(1 - Π) Y‖ ‖Z‖`, with `k` the number of blocks.  In particular
`P(Y)` maps the range of `Π` into itself if `Y` lies in it (`tangentProj_mem_range`), which is the
key step of the paper; the estimate needs no block decomposition of `Y`. -/
theorem norm_compl_tangentProj_le (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    {Z : Matrix m n ℝ} (hZ : blockMask E F Z = Z) :
    ‖(1 - blockMask E F) (tangentProj U V Z)‖ ≤
      16 * Fintype.card ι * ‖S⁻¹‖ * ‖(1 - blockMask E F) (U * S * Vᵀ)‖ * ‖Z‖ := by
  classical
  set Y := U * S * Vᵀ with hY
  set Pi := blockMask E F with hPi
  have hPio : IsOrthProj Pi := isOrthProj_blockMask hE hF
  set N := (1 - Pi) Y with hN
  have hNe : N = Y - Pi Y := rfl
  set c := 4 * (‖N‖ * ‖S⁻¹‖) with hc
  have hc0 : 0 ≤ c := by positivity
  have hR : ∀ i, ‖E i * Y - Y * F i‖ ≤ 2 * ‖N‖ := fun i => by
    have e1 : E i * Y - Y * F i = E i * N - N * F i := by
      have e2 : E i * Pi Y = Pi Y * F i := by rw [mul_blockMask hE, blockMask_mul hF]
      rw [hNe, Matrix.mul_sub, Matrix.sub_mul, e2]
      abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hE.norm_mul_left i N
    have h2 := hF.norm_mul_right i N
    linarith
  have hcE : ∀ i, ‖U * Uᵀ * E i - E i * (U * Uᵀ)‖ ≤ c := fun i => by
    have h1 := norm_commutator_le hU hV hS (B := F i) (hE.symm i)
    have h2 := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg S⁻¹)
    rw [hc]
    nlinarith
  have hcF : ∀ i, ‖V * Vᵀ * F i - F i * (V * Vᵀ)‖ ≤ c := fun i => by
    have hSt : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
    have h1 := norm_commutator_le hV hU hSt (B := E i) (hF.symm i)
    have e : F i * (V * Sᵀ * Uᵀ) - V * Sᵀ * Uᵀ * E i = -(E i * Y - Y * F i)ᵀ := by
      simp only [hY, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        hE.symm, hF.symm, Matrix.mul_assoc]
      abel
    rw [e, norm_neg, Frobenius.norm_transpose, ← Matrix.transpose_nonsing_inv,
      Frobenius.norm_transpose] at h1
    have h2 := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg S⁻¹)
    rw [hc]
    nlinarith
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  set k : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hkd
  have hQ : (V * Vᵀ)ᵀ = V * Vᵀ := by simp [Matrix.transpose_mul]
  set X := Z * (V * Vᵀ) with hX
  have hXZ : ‖X‖ ≤ ‖Z‖ := by
    have := (isOrthProj_rightProj (m := m) hV).norm_le Z
    rwa [rightProj_apply'] at this
  have hPL : ∀ W : Matrix m n ℝ, ‖U * Uᵀ * W‖ ≤ ‖W‖ := fun W =>
    (isOrthProj_leftProj hU).norm_le W
  have hC : ∀ W : Matrix m n ℝ, ‖(1 - Pi) W‖ ≤ ‖W‖ := fun W => hPio.compl.norm_le W
  have A1 : ‖(1 - Pi) (U * Uᵀ * Z)‖ ≤ k * c * ‖Z‖ := norm_compl_mul_le hF hcE hZ
  have A2 : ‖(1 - Pi) X‖ ≤ k * c * ‖Z‖ := by
    have hZ' : blockMask F E Zᵀ = Zᵀ := by rw [← transpose_blockMask hE hF, hZ]
    have h1 := norm_compl_mul_le hE hcF hZ'
    have e : ((1 - Pi) X)ᵀ = (1 - blockMask F E) (V * Vᵀ * Zᵀ) := by
      have e1 : Xᵀ = V * Vᵀ * Zᵀ := by rw [hX, Matrix.transpose_mul, hQ]
      rw [sub_apply, one_apply_eq_self, Matrix.transpose_sub,
        transpose_blockMask hE hF, e1, sub_apply, one_apply_eq_self]
    rw [← Frobenius.norm_transpose, e]
    rwa [Frobenius.norm_transpose] at h1
  have hX₁ : Pi (Pi X) = Pi X := hPio.idem X
  have A3 : ‖(1 - Pi) (U * Uᵀ * Pi X)‖ ≤ k * c * ‖Z‖ := by
    refine (norm_compl_mul_le hF hcE hX₁).trans ?_
    exact mul_le_mul_of_nonneg_left ((hPio.norm_le X).trans hXZ) (mul_nonneg hk hc0)
  have A4 : ‖(1 - Pi) (U * Uᵀ * (1 - Pi) X)‖ ≤ k * c * ‖Z‖ :=
    ((hC _).trans (hPL _)).trans A2
  have e : (1 - Pi) (tangentProj U V Z) = (1 - Pi) (U * Uᵀ * Z) + (1 - Pi) X -
      (1 - Pi) (U * Uᵀ * Pi X) - (1 - Pi) (U * Uᵀ * (1 - Pi) X) := by
    have e1 : tangentProj U V Z = U * Uᵀ * Z + X - (U * Uᵀ * Pi X + U * Uᵀ * (1 - Pi) X) := by
      rw [tangentProj_apply, ← Matrix.mul_add]
      have e2 : Pi X + (1 - Pi) X = X := by
        rw [sub_apply, one_apply_eq_self]
        abel
      rw [e2, hX]
      simp only [Matrix.mul_assoc]
    rw [e1, map_sub, map_add, map_add]
    abel
  have hfinal : ‖(1 - Pi) (tangentProj U V Z)‖ ≤ 4 * (k * c * ‖Z‖) := by
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h5 := norm_sub_le ((1 - Pi) (U * Uᵀ * Z) + (1 - Pi) X) ((1 - Pi) (U * Uᵀ * Pi X))
    have h6 := norm_add_le ((1 - Pi) (U * Uᵀ * Z)) ((1 - Pi) X)
    linarith
  calc ‖(1 - Pi) (tangentProj U V Z)‖ ≤ 4 * (k * c * ‖Z‖) := hfinal
    _ = 16 * k * ‖S⁻¹‖ * ‖N‖ * ‖Z‖ := by rw [hc]; ring

/-- `P(Y)` maps the range of `Π` into itself if `Y = U S Vᵀ` lies in it (arXiv 2410.18720, proof of
Prop. 2: `Π P(Y) Π = P(Y) Π` on the range of `Π`). -/
theorem tangentProj_mem_range (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hY : blockMask E F (U * S * Vᵀ) = U * S * Vᵀ) {Z : Matrix m n ℝ}
    (hZ : blockMask E F Z = Z) :
    blockMask E F (tangentProj U V Z) = tangentProj U V Z := by
  have h := norm_compl_tangentProj_le hE hF hU hV hS hZ
  have h0 : (1 - blockMask E F) (U * S * Vᵀ) = 0 := by
    rw [sub_apply, one_apply_eq_self, hY, sub_self]
  rw [h0, norm_zero, mul_zero, zero_mul] at h
  have h1 := norm_le_zero_iff.1 h
  rw [sub_apply, one_apply_eq_self, sub_eq_zero] at h1
  exact h1.symm

variable {g : Matrix m n ℝ → Matrix m n ℝ}

lemma flow_bound (hE : IsBlockFamily E) (hF : IsBlockFamily F) {r : Type*} [Fintype r]
    [DecidableEq r] {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hS : IsUnit S.det) {W Z : Matrix m n ℝ} (hW : W = U * S * Vᵀ)
    (hZ : blockMask E F Z = Z) {C G : ℝ} (hC : ‖S⁻¹‖ ≤ C) (hG : ‖Z‖ ≤ G) :
    ‖(1 - blockMask E F) (-tangentAt W Z)‖ ≤
      16 * Fintype.card ι * C * G * ‖(1 - blockMask E F) W‖ := by
  subst hW
  have h1 := norm_compl_tangentProj_le hE hF hU hV hS hZ
  rw [map_neg, norm_neg, tangentAt_eq hU hV hS]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  calc ‖(1 - blockMask E F) (tangentProj U V Z)‖
      ≤ 16 * Fintype.card ι * ‖S⁻¹‖ * ‖(1 - blockMask E F) (U * S * Vᵀ)‖ * ‖Z‖ := h1
    _ ≤ 16 * Fintype.card ι * C * ‖(1 - blockMask E F) (U * S * Vᵀ)‖ * G := by gcongr
    _ = _ := by ring

/-- **Prop. 2 of arXiv 2410.18720 (block structure preservation of the flow).**  Let `Y` solve
`Ẏ = -P(Y) Π ∇ℒ(Y)` on `[a, b]`, where `P(Y)` is the tangent projector at `Y`, `Π` a block mask
and `∇ℒ = g` continuous, and let `Y(a)` lie in the range of `Π`.  If `Y(t)` is a matrix of constant
rank with bounded inverse core, i.e. `Y(t) = U S Vᵀ` with orthonormal `U`, `V` and `‖S⁻¹‖ ≤ C` for
`t ∈ [a, b)`, then `Y(t)` stays in the range of `Π`.  (`r` may even depend on `t`.)

The rank condition is what gives the equation a meaning; the bound `‖S⁻¹‖ ≤ C` on `[a, b)` is an
added hypothesis.  The proof in the paper is circular: it writes a block SVD of `Z ∈ range Π` and
uses `U Uᵀ, V Vᵀ ∈ range Π` for the factors that define `P(Y)`, which are those of `Y(t)`; a
block SVD of `Y(t)` presupposes `Y(t) ∈ range Π`.  Here the Grönwall lemma is
applied to `(1 - Π) Y` through `norm_compl_tangentProj_le`; no uniqueness theorem, no block
decomposition and no structure of the factors is needed.  `Π` is a general block mask; the
mask `M ⊙ ·` of the paper is `blockMask_adjacency`.  The factors can be taken continuous
instead: `mem_range_blockMask_of_continuous`. -/
theorem mem_range_blockMask_of_flow (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    (hg : Continuous g) {Y : ℝ → Matrix m n ℝ} {a b C : ℝ}
    (hY : ODESolution (fun _ y => -tangentAt y (blockMask E F (g y))) Y a b)
    (hfac : ∀ t ∈ Ico a b, ∃ (r : ℕ) (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
      (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S.det ∧ Y t = U * S * Vᵀ ∧
        ‖S⁻¹‖ ≤ C)
    (h0 : blockMask E F (Y a) = Y a) : ∀ t ∈ Icc a b, blockMask E F (Y t) = Y t := by
  have hPio : IsOrthProj (blockMask E F) := isOrthProj_blockMask hE hF
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.comp_continuousOn hY.cont)
  have hf : ContinuousOn (fun t => (1 - blockMask E F) (Y t)) (Icc a b) :=
    (1 - blockMask E F).continuous.comp_continuousOn hY.cont
  have hf' : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => (1 - blockMask E F) (Y t))
      ((1 - blockMask E F) (-tangentAt (Y t) (blockMask E F (g (Y t))))) (Ici t) t := fun t ht =>
    (1 - blockMask E F).hasFDerivAt.comp_hasDerivWithinAt t (hY.deriv t ht)
  have ha : ‖(1 - blockMask E F) (Y a)‖ ≤ 0 := by
    rw [sub_apply, one_apply_eq_self, h0, sub_self, norm_zero]
  have bound : ∀ t ∈ Ico a b, ‖(1 - blockMask E F) (-tangentAt (Y t) (blockMask E F (g (Y t))))‖ ≤
      16 * Fintype.card ι * C * G * ‖(1 - blockMask E F) (Y t)‖ + 0 := fun t ht => by
    obtain ⟨r, U, S, V, hU, hV, hS, hYt, hC⟩ := hfac t ht
    have hGt : ‖blockMask E F (g (Y t))‖ ≤ G :=
      (hPio.norm_le _).trans (hG t (Ico_subset_Icc_self ht))
    rw [add_zero]
    exact flow_bound hE hF hU hV hS hYt (hPio.idem _) hC hGt
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hf hf' ha bound
  intro t ht
  have h1 := key t ht
  rw [gronwallBound_ε0_δ0] at h1
  have h2 := norm_le_zero_iff.1 h1
  rw [sub_apply, one_apply_eq_self, sub_eq_zero] at h2
  exact h2.symm

end Blocks

/-! ### Layer factors -/

section Layers

variable {m n ι : Type*}
variable {r : ι → Type*}

/-- The matrix `[U₁, …, U_L]` obtained by putting the columns of the layer factors side by side.
(In arXiv 2410.18720, App. I, the block `U_i` is written at its place in a `|N| × |N|` matrix;
here `U_i` is a matrix with all rows, supported on the rows of layer `i`.) -/
def stackCols {a : Type*} (U : ∀ i, Matrix a (r i) ℝ) : Matrix a (Σ i, r i) ℝ :=
  Matrix.of fun x c => U c.1 x c.2

lemma stackCols_mul_transpose [Fintype ι] [∀ i, Fintype (r i)] {a b : Type*}
    (A : ∀ i, Matrix a (r i) ℝ) (B : ∀ i, Matrix b (r i) ℝ) :
    stackCols A * (stackCols B)ᵀ = ∑ i, A i * (B i)ᵀ := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.transpose_apply, stackCols, Matrix.of_apply,
    Fintype.sum_sigma]

lemma stackCols_mul_blockDiagonal [Fintype ι] [∀ i, Fintype (r i)] [DecidableEq ι] {a : Type*}
    (U : ∀ i, Matrix a (r i) ℝ) (S : ∀ i, Matrix (r i) (r i) ℝ) :
    stackCols U * Matrix.blockDiagonal' S = stackCols fun i => U i * S i := by
  ext x ⟨k, j⟩
  simp only [Matrix.mul_apply, stackCols, Matrix.of_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.blockDiagonal'_apply_eq]
  · intro i _ hi
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hi, mul_zero]
  · simp

/-- The block factorization of arXiv 2410.18720, App. I: `Y = U S Vᵀ = ∑ᵢ Uᵢ Sᵢ Vᵢᵀ`. -/
lemma stack_factorization [Fintype ι] [∀ i, Fintype (r i)] [DecidableEq ι]
    (U : ∀ i, Matrix m (r i) ℝ) (S : ∀ i, Matrix (r i) (r i) ℝ) (V : ∀ i, Matrix n (r i) ℝ) :
    stackCols U * Matrix.blockDiagonal' S * (stackCols V)ᵀ = ∑ i, U i * S i * (V i)ᵀ := by
  rw [stackCols_mul_blockDiagonal, stackCols_mul_transpose]

/-- The stacked factor of orthonormal layer factors with layer support is orthonormal. -/
lemma stackCols_orth [Fintype m] [DecidableEq ι] [∀ i, DecidableEq (r i)]
    {E : ι → Matrix m m ℝ} (hE : IsBlockFamily E) {U : ∀ i, Matrix m (r i) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) (hEU : ∀ i, E i * U i = U i) :
    (stackCols U)ᵀ * stackCols U = 1 := by
  have hcross : ∀ i j, i ≠ j → (U i)ᵀ * U j = 0 := fun i j hij => by
    have e : (U i)ᵀ * U j = (U i)ᵀ * (E i * E j) * U j := by
      nth_rewrite 1 [← hEU i, ← hEU j]
      rw [Matrix.transpose_mul, hE.symm]
      simp only [Matrix.mul_assoc]
    rw [e, hE.orth i j hij]
    simp
  ext ⟨i, c⟩ ⟨j, d⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, stackCols, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    have h := congrFun (congrFun (hU i) c) d
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [h]
    by_cases hcd : c = d
    · subst hcd; simp
    · have : (⟨i, c⟩ : Σ i, r i) ≠ ⟨i, d⟩ := fun h => hcd (by simpa using h)
      simp [hcd, this]
  · have h := congrFun (congrFun (hcross i j hij) c) d
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    have : (⟨i, c⟩ : Σ i, r i) ≠ ⟨j, d⟩ := fun h => hij (congrArg Sigma.fst h)
    simpa [Matrix.one_apply, this] using h

lemma blockDiagonal_isUnit [Fintype ι] [∀ i, Fintype (r i)] [DecidableEq ι]
    [∀ i, DecidableEq (r i)]
    {S : ∀ i, Matrix (r i) (r i) ℝ} (hS : ∀ i, IsUnit (S i).det) :
    IsUnit (Matrix.blockDiagonal' S).det := by
  have h : Matrix.blockDiagonal' S * Matrix.blockDiagonal' (fun i => (S i)⁻¹) = 1 := by
    rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ (hS i)
  exact Matrix.isUnit_det_of_right_inverse h

variable [Fintype m] [Fintype n] [Fintype ι] [∀ i, Fintype (r i)]
variable {E : ι → Matrix m m ℝ} {F : ι → Matrix n n ℝ}

omit [Fintype m] [Fintype n] [∀ i, Fintype (r i)] in
/-- The product of two sums with vanishing cross terms. -/
lemma sum_mul_sum_diag {a b c : Type*} [Fintype b] (A : ι → Matrix a b ℝ) (B : ι → Matrix b c ℝ)
    (h : ∀ i j, i ≠ j → A i * B j = 0) : (∑ i, A i) * (∑ j, B j) = ∑ i, A i * B i := by
  classical
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum, Finset.sum_eq_single i]
  · exact fun j _ hj => h i j hj.symm
  · simp

omit [Fintype m] [Fintype n] [Fintype ι] [∀ i, Fintype (r i)] in
/-- `P(Y) Z` with the two projectors grouped. -/
lemma tangentProj_apply' [Fintype m] [Fintype n] {k k' : Type*} [Fintype k] [Fintype k']
    (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    tangentProj U V Z = U * Uᵀ * Z + Z * (V * Vᵀ) - U * Uᵀ * Z * (V * Vᵀ) := by
  rw [tangentProj_apply]
  simp only [Matrix.mul_assoc]

/-- **The tangent projector of the block matrix acts block by block** (arXiv 2410.18720, Prop. 3):
for `Y = ∑ᵢ Uᵢ Sᵢ Vᵢᵀ` with factors supported on the layers, `P(Y) Π G = ∑ᵢ P(Yᵢ) (Eᵢ G Fᵢ)`. -/
theorem tangentProj_stack (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {U : ∀ i, Matrix m (r i) ℝ} {V : ∀ i, Matrix n (r i) ℝ} (hEU : ∀ i, E i * U i = U i)
    (hFV : ∀ i, F i * V i = V i) (G : Matrix m n ℝ) :
    tangentProj (stackCols U) (stackCols V) (blockMask E F G) =
      ∑ i, tangentProj (U i) (V i) (E i * G * F i) := by
  have h1 : ∀ i j, i ≠ j → U i * (U i)ᵀ * (E j * G * F j) = 0 := fun i j hij => by
    have e : (U i)ᵀ * E j = 0 := by
      have e0 : (U i)ᵀ = (U i)ᵀ * E i := by
        nth_rewrite 1 [← hEU i]
        rw [Matrix.transpose_mul, hE.symm]
      rw [e0, Matrix.mul_assoc, hE.orth i j hij, Matrix.mul_zero]
    have e' : U i * (U i)ᵀ * (E j * G * F j) = U i * ((U i)ᵀ * E j) * G * F j := by
      simp only [Matrix.mul_assoc]
    rw [e', e]
    simp
  have h2 : ∀ j i, j ≠ i → (E j * G * F j) * (V i * (V i)ᵀ) = 0 := fun j i hji => by
    have e : F j * V i = 0 := by
      rw [← hFV i, ← Matrix.mul_assoc, hF.orth j i hji, Matrix.zero_mul]
    have e' : (E j * G * F j) * (V i * (V i)ᵀ) = E j * G * (F j * V i) * (V i)ᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e', e]
    simp
  have h3 : ∀ i j, i ≠ j →
      (U i * (U i)ᵀ * (E i * G * F i)) * (V j * (V j)ᵀ) = 0 := fun i j hij => by
    rw [Matrix.mul_assoc, h2 i j hij, Matrix.mul_zero]
  rw [tangentProj_apply', stackCols_mul_transpose, stackCols_mul_transpose, blockMask_apply,
    sum_mul_sum_diag _ _ h1, sum_mul_sum_diag _ _ h2, sum_mul_sum_diag _ _ h3,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => (tangentProj_apply' _ _ _).symm

/-- Extraction of one block from a sum of blocks. -/
lemma block_extract (hE : IsBlockFamily E) (hF : IsBlockFamily F) {X : ι → Matrix m n ℝ}
    (hX : ∀ i, E i * X i * F i = X i) (i : ι) : E i * (∑ j, X j) * F i = X i := by
  classical
  rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single i]
  · exact hX i
  · intro j _ hj
    rw [← hX j]
    have e : E i * (E j * X j * F j) * F i = (E i * E j) * X j * (F j * F i) := by
      simp only [Matrix.mul_assoc]
    rw [e, hE.orth i j hj.symm, hF.orth j i hj]
    simp
  · simp

/-- Blocks are orthogonal, so the squared Frobenius norm of a block matrix is additive; this is
why the singular values of all layers can be pooled in the global truncation (10) of
arXiv 2410.18720. -/
theorem norm_sq_sum_blocks (hE : IsBlockFamily E) (hF : IsBlockFamily F) {X : ι → Matrix m n ℝ}
    (hX : ∀ i, E i * X i * F i = X i) : ‖∑ i, X i‖ ^ 2 = ∑ i, ‖X i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hj
    have e : E i * X j * F i = 0 := by
      rw [← hX j]
      have e' : E i * (E j * X j * F j) * F i = (E i * E j) * X j * (F j * F i) := by
        simp only [Matrix.mul_assoc]
      rw [e', hE.orth i j hj.symm, hF.orth j i hj]
      simp
    have e2 : ⟪X i, X j⟫ = ⟪X i, E i * X j * F i⟫ := by
      nth_rewrite 1 [← hX i]
      rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, hE.symm, hF.symm,
        Matrix.mul_assoc]
    rw [e2, e, inner_zero_right]
  · simp

variable {s s' : ι → Type*} [∀ i, Fintype (s i)] [∀ i, Fintype (s' i)]
  [∀ i, DecidableEq (s i)] [∀ i, DecidableEq (s' i)] [∀ i, DecidableEq (r i)]

/-- **Prop. 1 of arXiv 2410.18720 (first part): the multi-layer method integrates one matrix
system.**  Applying Algorithm 1 to each layer `i`, with the block `Eᵢ G Fᵢ` of the gradient and
factors supported on the layer, gives before truncation

`∑ᵢ Ŵᵢ = Y - λ P(Y) Π G`,  `Y = ∑ᵢ Uᵢ Sᵢ Vᵢᵀ`,

one explicit Euler step of `Ẏ = -P(Y) Π ∇ℒ(Y)` for the adjacency matrix `Y` of the network, with
the tangent projector at `Y` (`tangentAt_stack`).  The model assumption of the paper, that
the network output is a fixed point of the adjacency model, plays no role: `G` is any matrix. -/
theorem multilayer_step (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {U : ∀ i, Matrix m (r i) ℝ} {S : ∀ i, Matrix (r i) (r i) ℝ} {V : ∀ i, Matrix n (r i) ℝ}
    {Ut : ∀ i, Matrix m (s i) ℝ} {Vt : ∀ i, Matrix n (s' i) ℝ} {G : Matrix m n ℝ} {lr : ℝ}
    (hEU : ∀ i, E i * U i = U i) (hFV : ∀ i, F i * V i = V i)
    (hstep : ∀ i, IsGeoLoRAStep (E i * G * F i) lr (U i) (S i) (V i) (Ut i) (Vt i)) :
    ∑ i, geoWhat (E i * G * F i) lr (U i) (S i) (V i) (Ut i) (Vt i) =
      ∑ i, U i * S i * (V i)ᵀ -
        lr • tangentProj (stackCols U) (stackCols V) (blockMask E F G) := by
  rw [tangentProj_stack hE hF hEU hFV, Finset.smul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => geoWhat_eq (hstep i)

/-- For layer factors with layer support the tangent projector of `arXiv 2410.18720` at
`Y = ∑ᵢ Uᵢ Sᵢ Vᵢᵀ` is the one of the stacked factors. -/
theorem tangentAt_stack (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {U : ∀ i, Matrix m (r i) ℝ} {S : ∀ i, Matrix (r i) (r i) ℝ} {V : ∀ i, Matrix n (r i) ℝ}
    (hU : ∀ i, (U i)ᵀ * U i = 1) (hV : ∀ i, (V i)ᵀ * V i = 1) (hS : ∀ i, IsUnit (S i).det)
    (hEU : ∀ i, E i * U i = U i) (hFV : ∀ i, F i * V i = V i) :
    tangentAt (∑ i, U i * S i * (V i)ᵀ) = tangentProj (stackCols U) (stackCols V) := by
  classical
  rw [← stack_factorization]
  exact tangentAt_eq (stackCols_orth hE hU hEU) (stackCols_orth hF hV hFV)
    (blockDiagonal_isUnit hS)

omit [Fintype ι] in
/-- The gradient with respect to one block: if `G = ∇ℒ(Y)`, the map
`X ↦ ℒ(Y - Eᵢ Y Fᵢ + Eᵢ X Fᵢ)`, which varies the block `i` of `Y`, has at `X = Y` the gradient
`Eᵢ G Fᵢ`.  This is `∇_{Y_i} ℒ` of arXiv 2410.18720, App. I. -/
theorem hasFDerivAt_block {ℒ : Matrix m n ℝ → ℝ} {Y G : Matrix m n ℝ}
    (hℒ : HasFDerivAt ℒ (innerSL ℝ G) Y) (hE : IsBlockFamily E) (hF : IsBlockFamily F) (i : ι) :
    HasFDerivAt (fun X => ℒ (Y - E i * Y * F i + E i * X * F i))
      (innerSL ℝ (E i * G * F i)) Y := by
  let T : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
    (Frobenius.leftMulCLM (E i)).comp (Frobenius.rightMulCLM (F i))
  have hT : ∀ X, E i * X * F i = T X := fun X => by simp [T, Matrix.mul_assoc]
  have h1 : HasFDerivAt (fun Z => ℒ (Y - T Y + Z)) (innerSL ℝ G) (T Y) := by
    have h2 : HasFDerivAt ℒ (innerSL ℝ G) (Y - T Y + T Y) := by rwa [sub_add_cancel]
    have h3 : HasFDerivAt (fun Z => Y - T Y + Z) (ContinuousLinearMap.id ℝ _) (T Y) :=
      (hasFDerivAt_id _).const_add _
    have h4 := h2.comp (T Y) h3
    rw [ContinuousLinearMap.comp_id] at h4
    exact h4
  simp only [hT]
  refine hasFDerivAt_comp_clm (ℒ := fun Z => ℒ (Y - T Y + Z)) T (fun Z => ?_) h1
  rw [← hT, ← hT, Frobenius.inner_mul_right' G (E i * Z), Frobenius.inner_mul_left', hE.symm,
    hF.symm, Matrix.mul_assoc]

omit [Fintype ι] in
/-- A tangent direction of block `i` lies in block `i`. -/
lemma tangentProj_block (hE : IsBlockFamily E) (hF : IsBlockFamily F) {i : ι} {k : Type*}
    [Fintype k] {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hEU : E i * U = U) (hFV : F i * V = V)
    (G : Matrix m n ℝ) :
    E i * tangentProj U V (E i * G * F i) * F i = tangentProj U V (E i * G * F i) := by
  set Z := E i * G * F i with hZ
  have hEZ : E i * Z = Z := by rw [hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE.idem]
  have hZF : Z * F i = Z := by rw [hZ, Matrix.mul_assoc, hF.idem]
  have hVF : Vᵀ * F i = Vᵀ := by
    have h := congrArg Matrix.transpose hFV
    rwa [Matrix.transpose_mul, hF.symm] at h
  have hEP : E i * (U * Uᵀ) = U * Uᵀ := by rw [← Matrix.mul_assoc, hEU]
  have hQF : V * Vᵀ * F i = V * Vᵀ := by rw [Matrix.mul_assoc, hVF]
  have h1 : E i * tangentProj U V Z = tangentProj U V Z := by
    rw [tangentProj_apply', Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc (E i) (U * Uᵀ),
      ← Matrix.mul_assoc (E i) Z, ← Matrix.mul_assoc (E i) (U * Uᵀ * Z),
      ← Matrix.mul_assoc (E i) (U * Uᵀ), hEP, hEZ]
  have h2 : tangentProj U V Z * F i = tangentProj U V Z := by
    rw [tangentProj_apply', Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc (U * Uᵀ) Z,
      Matrix.mul_assoc Z (V * Vᵀ), Matrix.mul_assoc (U * Uᵀ * Z) (V * Vᵀ), hQF, hZF]
  rw [h1, h2]

/-- **Prop. 3 of arXiv 2410.18720 (block form of the flow).**  At time `t`, let
`Y = ∑ᵢ Uᵢ Sᵢ Vᵢᵀ`, where the layer factors and their velocities are supported on the layers, the
`Uᵢ`, `Vᵢ` are orthonormal, the `Sᵢ` invertible and the gauge conditions `Uᵢᵀ U̇ᵢ = 0`,
`Vᵢᵀ V̇ᵢ = 0` hold.  Then `Y` satisfies the projected flow `Ẏ = -P(Y) Π G` at `t`, with
`G = ∇ℒ(Y)` and `P(Y)` the tangent projector at `Y` (`tangentAt_stack`), **if and only if** the
per-layer equations

`Ṡᵢ = -Uᵢᵀ Gᵢ Vᵢ`, `U̇ᵢ = -(I - Uᵢ Uᵢᵀ) Gᵢ Vᵢ Sᵢ⁻¹`, `V̇ᵢ = -(I - Vᵢ Vᵢᵀ) Gᵢᵀ Uᵢ Sᵢ⁻ᵀ`

hold, where `Gᵢ = Eᵢ G Fᵢ = ∇_{Y_i} ℒ` (`hasFDerivAt_block`).  (The paper asserts the direction
"flow ⇒ block equations"; the extra `I` blocks of its factors, on which its `S` vanishes, are not
needed: here the stacked `S` is invertible.) -/
theorem block_flow_iff [DecidableEq m] [DecidableEq n] (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {U : ∀ i, ℝ → Matrix m (r i) ℝ} {S : ∀ i, ℝ → Matrix (r i) (r i) ℝ}
    {V : ∀ i, ℝ → Matrix n (r i) ℝ} {U' : ∀ i, Matrix m (r i) ℝ}
    {S' : ∀ i, Matrix (r i) (r i) ℝ} {V' : ∀ i, Matrix n (r i) ℝ} {G : Matrix m n ℝ} {u : Set ℝ}
    {t : ℝ} (hu : UniqueDiffWithinAt ℝ u t) (hU : ∀ i, HasDerivWithinAt (U i) (U' i) u t)
    (hS : ∀ i, HasDerivWithinAt (S i) (S' i) u t) (hV : ∀ i, HasDerivWithinAt (V i) (V' i) u t)
    (hUo : ∀ i, (U i t)ᵀ * U i t = 1) (hVo : ∀ i, (V i t)ᵀ * V i t = 1)
    (hdet : ∀ i, IsUnit (S i t).det) (hgU : ∀ i, (U i t)ᵀ * U' i = 0)
    (hgV : ∀ i, (V i t)ᵀ * V' i = 0) (hEU : ∀ i, E i * U i t = U i t)
    (hFV : ∀ i, F i * V i t = V i t) (hEU' : ∀ i, E i * U' i = U' i)
    (hFV' : ∀ i, F i * V' i = V' i) :
    HasDerivWithinAt (fun τ => ∑ i, U i τ * S i τ * (V i τ)ᵀ)
        (-tangentProj (stackCols fun i => U i t) (stackCols fun i => V i t)
          (blockMask E F G)) u t ↔
      ∀ i, U' i = -((1 - U i t * (U i t)ᵀ) * (E i * G * F i) * V i t * (S i t)⁻¹) ∧
        S' i = -((U i t)ᵀ * (E i * G * F i) * V i t) ∧
        V' i = -((1 - V i t * (V i t)ᵀ) * (E i * G * F i)ᵀ * U i t * ((S i t)⁻¹)ᵀ) := by
  have htan := tangentProj_stack hE hF (U := fun i => U i t) (V := fun i => V i t) hEU hFV G
  rw [htan]
  have hneg : ∀ i, tangentProj (U i t) (V i t) (-(E i * G * F i)) =
      -tangentProj (U i t) (V i t) (E i * G * F i) := fun i => map_neg _ _
  have hiff := fun i => hasDerivWithinAt_factorProduct_iff_factorODE
    (Ad := -(E i * G * F i)) hu (hU i) (hS i) (hV i) (hUo i) (hVo i) (hdet i) (hgU i) (hgV i)
  simp only [← tangentProj_apply, hneg] at hiff
  have hrhs : ∀ i, (U' i = (1 - U i t * (U i t)ᵀ) * -(E i * G * F i) * V i t * (S i t)⁻¹ ∧
      S' i = (U i t)ᵀ * -(E i * G * F i) * V i t ∧
      V' i = (1 - V i t * (V i t)ᵀ) * (-(E i * G * F i))ᵀ * U i t * ((S i t)⁻¹)ᵀ) ↔
      (U' i = -((1 - U i t * (U i t)ᵀ) * (E i * G * F i) * V i t * (S i t)⁻¹) ∧
        S' i = -((U i t)ᵀ * (E i * G * F i) * V i t) ∧
        V' i = -((1 - V i t * (V i t)ᵀ) * (E i * G * F i)ᵀ * U i t * ((S i t)⁻¹)ᵀ)) := fun i => by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_neg]
  simp only [hrhs] at hiff
  constructor
  · intro h i
    refine (hiff i).1 ?_
    have hD := fun j => Frobenius.hasDerivWithinAt_mul_mul (hU j) (hS j)
      (Frobenius.hasDerivWithinAt_transpose (hV j))
    have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ => hD j)
    have heq := hu.eq_deriv _ hsum h
    rw [← Finset.sum_neg_distrib] at heq
    have hVT : ∀ j, (V j t)ᵀ * F j = (V j t)ᵀ := fun j => by
      have h1 := congrArg Matrix.transpose (hFV j)
      rwa [Matrix.transpose_mul, hF.symm] at h1
    have hVT' : ∀ j, (V' j)ᵀ * F j = (V' j)ᵀ := fun j => by
      have h1 := congrArg Matrix.transpose (hFV' j)
      rwa [Matrix.transpose_mul, hF.symm] at h1
    have hDs : ∀ j, E j * (U' j * S j t * (V j t)ᵀ + U j t * S' j * (V j t)ᵀ +
        U j t * S j t * (V' j)ᵀ) * F j = U' j * S j t * (V j t)ᵀ + U j t * S' j * (V j t)ᵀ +
        U j t * S j t * (V' j)ᵀ := fun j => by
      have t1 : E j * (U' j * S j t * (V j t)ᵀ) * F j = U' j * S j t * (V j t)ᵀ := by
        rw [← Matrix.mul_assoc (E j), ← Matrix.mul_assoc (E j), hEU', Matrix.mul_assoc _ _ (F j),
          hVT]
      have t2 : E j * (U j t * S' j * (V j t)ᵀ) * F j = U j t * S' j * (V j t)ᵀ := by
        rw [← Matrix.mul_assoc (E j), ← Matrix.mul_assoc (E j), hEU, Matrix.mul_assoc _ _ (F j),
          hVT]
      have t3 : E j * (U j t * S j t * (V' j)ᵀ) * F j = U j t * S j t * (V' j)ᵀ := by
        rw [← Matrix.mul_assoc (E j), ← Matrix.mul_assoc (E j), hEU, Matrix.mul_assoc _ _ (F j),
          hVT']
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, t1, t2, t3]
    have hTs : ∀ j, E j * (-tangentProj (U j t) (V j t) (E j * G * F j)) * F j =
        -tangentProj (U j t) (V j t) (E j * G * F j) := fun j => by
      rw [Matrix.mul_neg, Matrix.neg_mul, tangentProj_block hE hF (hEU j) (hFV j) G]
    have e1 := block_extract hE hF hDs i
    have e2 := block_extract hE hF hTs i
    rw [heq, e2] at e1
    have hi := hD i
    rwa [← e1] at hi
  · intro h
    have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => (hiff i).2 (h i))
    rw [Finset.sum_neg_distrib] at hsum
    exact hsum

/-- A block matrix lies in the range of the mask. -/
lemma blockMask_sum (hE : IsBlockFamily E) (hF : IsBlockFamily F) {X : ι → Matrix m n ℝ}
    (hX : ∀ i, E i * X i * F i = X i) : blockMask E F (∑ i, X i) = ∑ i, X i := by
  rw [blockMask_apply]
  exact Finset.sum_congr rfl fun i _ => block_extract hE hF hX i

/-- **Prop. 1 of arXiv 2410.18720 (second part): the global truncation strategy.**  Let each layer
have orthonormal augmented bases `Ûᵢ`, `V̂ᵢ` supported on the layer and a singular value
decomposition `Ŝᵢ = Pᵢ Σᵢ Qᵢᵀ`.  Truncating each layer to the singular values in `keep i` changes
the single matrix `∑ᵢ Ûᵢ Ŝᵢ V̂ᵢᵀ` in the squared Frobenius norm by the pooled tail
`∑ᵢ ∑_{j ∉ keep i} s_{j,i}²` of all layers, the left side of eq. (10).  See
`truncation_criterion_iff` for the meaning of the criterion. -/
theorem global_truncation {ρ ρ' κ : ι → Type*} [∀ i, Fintype (ρ i)] [∀ i, Fintype (ρ' i)]
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (ρ i)] [∀ i, DecidableEq (ρ' i)]
    [∀ i, DecidableEq (κ i)] (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    {Uh : ∀ i, Matrix m (ρ i) ℝ} {Vh : ∀ i, Matrix n (ρ' i) ℝ}
    (hUh : ∀ i, (Uh i)ᵀ * Uh i = 1) (hVh : ∀ i, (Vh i)ᵀ * Vh i = 1)
    (hEU : ∀ i, E i * Uh i = Uh i) (hFV : ∀ i, F i * Vh i = Vh i)
    {P : ∀ i, Matrix (ρ i) (κ i) ℝ} {Q : ∀ i, Matrix (ρ' i) (κ i) ℝ}
    (hP : ∀ i, (P i)ᵀ * P i = 1) (hQ : ∀ i, (Q i)ᵀ * Q i = 1) (σ : ∀ i, κ i → ℝ)
    (keep : ∀ i, Finset (κ i)) :
    ‖∑ i, Uh i * (P i * Matrix.diagonal (σ i) * (Q i)ᵀ) * (Vh i)ᵀ -
        ∑ i, (Uh i * (P i).submatrix id ((↑) : keep i → κ i)) *
            Matrix.diagonal (fun j : keep i => σ i j) *
          (Vh i * (Q i).submatrix id ((↑) : keep i → κ i))ᵀ‖ ^ 2 =
      ∑ i, ∑ j ∈ (keep i)ᶜ, σ i j ^ 2 := by
  rw [← Finset.sum_sub_distrib, norm_sq_sum_blocks hE hF]
  · exact Finset.sum_congr rfl fun i _ =>
      (truncation_spec (hUh i) (hVh i) (hP i) (hQ i) (σ i) (keep i)).2.2
  · intro i
    have hVF : (Vh i)ᵀ * F i = (Vh i)ᵀ := by
      have h := congrArg Matrix.transpose (hFV i)
      rwa [Matrix.transpose_mul, hF.symm] at h
    have hform : ∀ B : Matrix (ρ i) (ρ' i) ℝ, E i * (Uh i * B * (Vh i)ᵀ) * F i =
        Uh i * B * (Vh i)ᵀ := fun B => by
      rw [← Matrix.mul_assoc (E i), ← Matrix.mul_assoc (E i), hEU, Matrix.mul_assoc _ _ (F i),
        hVF]
    have e : (Uh i * (P i).submatrix id ((↑) : keep i → κ i)) *
          Matrix.diagonal (fun j : keep i => σ i j) *
          (Vh i * (Q i).submatrix id ((↑) : keep i → κ i))ᵀ =
        Uh i * ((P i).submatrix id ((↑) : keep i → κ i) *
          Matrix.diagonal (fun j : keep i => σ i j) *
          ((Q i).submatrix id ((↑) : keep i → κ i))ᵀ) * (Vh i)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, Matrix.mul_sub, Matrix.sub_mul, hform, hform]

/-- The global criterion (10) of arXiv 2410.18720 is a bound on the relative error: with
`tail = ‖Ŵ - W₁‖²` and `tail + kept = ‖Ŵ‖²`, `tail < τ/(1-τ) kept` iff `tail < τ ‖Ŵ‖²`.  (The
criterion in App. I.1 of the paper, `tail/(tail + kept) < τ/(1-τ)`, disagrees with eq. (10); this
is the form consistent with eq. (10).) -/
theorem truncation_criterion_iff {tail kept τ : ℝ} (h1 : τ < 1) :
    tail < τ / (1 - τ) * kept ↔ tail < τ * (tail + kept) := by
  have h : 0 < 1 - τ := by linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ h]
  constructor <;> intro h' <;> nlinarith

end Layers

/-! ### The block structure on the adjacency matrix -/

section Adjacency

variable {N : Type*} [Fintype N] [DecidableEq N] {L : ℕ} (layer : N → Fin (L + 1))

/-- The diagonal projector onto the neurons of layer `l`. -/
def layerProj (l : Fin (L + 1)) : Matrix N N ℝ :=
  Matrix.diagonal fun a => if layer a = l then 1 else 0

omit [Fintype N] in
/-- The mask `M` of arXiv 2410.18720, App. I: `M a b = 1` iff the neuron `b` lies in the layer after
the one of `a`, so that `M` has the blocks `11ᵀ` on the block superdiagonal. -/
def adjacencyMask : Matrix N N ℝ :=
  Matrix.of fun a b => if (layer a : ℕ) + 1 = layer b then 1 else 0

/-- The layer projectors of different layers are a block family. -/
theorem isBlockFamily_layerProj {ι : Type*} {c : ι → Fin (L + 1)} (hc : Function.Injective c) :
    IsBlockFamily fun i => layerProj layer (c i) where
  symm i := by simp [layerProj]
  idem i := by
    simp only [layerProj, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    split_ifs <;> simp
  orth i j hij := by
    simp only [layerProj, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h1 : layer a = c i
    · have h2 : layer a ≠ c j := fun h => hij (hc (h1.symm.trans h))
      simp [h2]
    · simp [h1]

/-- **The mask of arXiv 2410.18720, App. I, is a block mask**:
`Π Z = M ⊙ Z = ∑_{i < L} Eᵢ Z Eᵢ₊₁`, with `Eᵢ` the projector onto layer `i`. -/
theorem blockMask_adjacency (Z : Matrix N N ℝ) :
    blockMask (fun i : Fin L => layerProj layer i.castSucc)
        (fun i : Fin L => layerProj layer i.succ) Z = (adjacencyMask layer).hadamard Z := by
  rw [blockMask_apply]
  ext a b
  simp only [Matrix.sum_apply, layerProj, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.hadamard_apply, adjacencyMask, Matrix.of_apply]
  by_cases h : (layer a : ℕ) + 1 = layer b
  · have hlt : (layer a : ℕ) < L := by
      have := (layer b).2
      omega
    rw [Finset.sum_eq_single (⟨layer a, hlt⟩ : Fin L)]
    · have h1 : layer a = (⟨layer a, hlt⟩ : Fin L).castSucc := Fin.ext rfl
      have h2 : layer b = (⟨layer a, hlt⟩ : Fin L).succ := Fin.ext (by simp [h])
      simp only [← h1, ← h2, h, ite_true]
      ring
    · intro i _ hi
      have h1 : layer a ≠ i.castSucc := fun h' =>
        hi (Fin.ext (by simpa using congrArg Fin.val h'.symm))
      simp [h1]
    · simp
  · simp only [h, ite_false, zero_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : layer a = i.castSucc
    · have h2 : layer b ≠ i.succ := fun h' => h (by simp [h1, h'])
      simp [h2]
    · simp [h1]

end Adjacency

/-! ### Non-vacuity and continuous factors -/

section FlowInstance

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]
variable {E : ι → Matrix m m ℝ} {F : ι → Matrix n n ℝ} {g : Matrix m n ℝ → Matrix m n ℝ}

/-- **Prop. 2 of arXiv 2410.18720 with continuous factors**: if `Y = U S Vᵀ` on the compact
interval `[a, b]` with orthonormal `U`, `V`, and `S` continuous and invertible, then the bound on
`S⁻¹` in `mem_range_blockMask_of_flow` is automatic. -/
theorem mem_range_blockMask_of_continuous (hE : IsBlockFamily E) (hF : IsBlockFamily F)
    (hg : Continuous g) {r : ℕ} {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℝ → Matrix n (Fin r) ℝ} {Y : ℝ → Matrix m n ℝ} {a b : ℝ}
    (hY : ODESolution (fun _ y => -tangentAt y (blockMask E F (g y))) Y a b)
    (hfac : ∀ t ∈ Icc a b, Y t = U t * S t * (V t)ᵀ)
    (hUo : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1) (hVo : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1)
    (hdet : ∀ t ∈ Icc a b, IsUnit (S t).det) (hSc : ContinuousOn S (Icc a b))
    (h0 : blockMask E F (Y a) = Y a) : ∀ t ∈ Icc a b, blockMask E F (Y t) = Y t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_inv hSc hdet)
  refine mem_range_blockMask_of_flow hE hF hg hY (C := C) (fun t ht => ?_) h0
  have ht' := Ico_subset_Icc_self ht
  exact ⟨r, U t, S t, V t, hUo t ht', hVo t ht', hdet t ht', hfac t ht', hC t ht'⟩

/-- **The hypotheses of Prop. 2 can hold** (with `∇ℒ = id`, i.e. `ℒ(Y) = ‖Y‖²/2`): from any
`Y₀ = U S Vᵀ` in the range of `Π`, the curve `Y(t) = e^{-t} Y₀` solves `Ẏ = -P(Y) Π ∇ℒ(Y)` and has
the factorization required in `mem_range_blockMask_of_flow`.  Block matrices `Y₀` are provided by
`stack_factorization` and `blockMask_sum`. -/
theorem exists_flow_instance {r : ℕ} {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det)
    (hY₀ : blockMask E F (U * S * Vᵀ) = U * S * Vᵀ) (a b : ℝ) :
    ODESolution (fun _ y => -tangentAt y (blockMask E F y))
        (fun t => Real.exp (-t) • (U * S * Vᵀ)) a b ∧
      ∀ t ∈ Ico a b, ∃ (S' : Matrix (Fin r) (Fin r) ℝ), IsUnit S'.det ∧
        Real.exp (-t) • (U * S * Vᵀ) = U * S' * Vᵀ ∧ ‖S'⁻¹‖ ≤ Real.exp b * ‖S⁻¹‖ := by
  have hfac : ∀ t : ℝ, Real.exp (-t) • (U * S * Vᵀ) = U * (Real.exp (-t) • S) * Vᵀ := fun t => by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hdet : ∀ t : ℝ, IsUnit (Real.exp (-t) • S).det := fun t => by
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Real.exp_pos _).ne'.isUnit).mul hS
  have hinv : ∀ t : ℝ, (Real.exp (-t) • S)⁻¹ = Real.exp t • S⁻¹ := fun t => by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hS, smul_smul, ← Real.exp_add]
    simp
  have hder : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-t) • (U * S * Vᵀ))
      (-(Real.exp (-t) • (U * S * Vᵀ))) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    simpa using h1.smul_const (U * S * Vᵀ)
  have hfield : ∀ t : ℝ, -tangentAt (Real.exp (-t) • (U * S * Vᵀ))
      (blockMask E F (Real.exp (-t) • (U * S * Vᵀ))) = -(Real.exp (-t) • (U * S * Vᵀ)) := by
    intro t
    rw [map_smul, hY₀, hfac t, tangentAt_eq hU hV (hdet t), ← hfac t, map_smul,
      tangentProj_mul_mul_transpose hU V S]
  refine ⟨⟨fun t _ => (hder t).continuousAt.continuousWithinAt, fun t _ => ?_⟩, fun t ht => ?_⟩
  · have h2 := (hder t).hasDerivWithinAt (s := Ici t)
    rwa [← hfield t] at h2
  · refine ⟨Real.exp (-t) • S, hdet t, hfac t, ?_⟩
    rw [hinv, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht.2.le) (norm_nonneg _)

end FlowInstance

/-! ### The literal conclusion of Theorem 2 is false -/

section NoiseFloor

open ProbabilityTheory

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure coin :=
  ⟨by
    simp only [coin, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact ENNReal.add_halves 1⟩

/-- A sequence of independent fair coins. -/
noncomputable def coins : Measure (ℕ → Bool) := Measure.infinitePi fun _ => coin

instance : IsProbabilityMeasure coins := by
  unfold coins
  infer_instance

/-- The sign of a coin. -/
def toss (b : Bool) : ℝ := if b then 1 else -1

/-- The Rademacher sequence on `coins`. -/
def rad (j : ℕ) (ω : ℕ → Bool) : ℝ := toss (ω j)

lemma measurable_toss : Measurable toss := measurable_from_top

lemma stronglyMeasurable_rad (j : ℕ) : StronglyMeasurable (rad j) :=
  (measurable_toss.comp (measurable_pi_apply j)).stronglyMeasurable

lemma iIndepFun_rad : iIndepFun rad coins :=
  iIndepFun_infinitePi (X := fun _ => toss) fun _ => measurable_toss

lemma integral_rad (j : ℕ) : ∫ ω, rad j ω ∂coins = 0 := by
  have h : coins.map (fun ω => ω j) = coin := Measure.infinitePi_map_eval _ j
  have h1 : ∫ ω, rad j ω ∂coins = ∫ b, toss b ∂(coins.map fun ω => ω j) :=
    (integral_map (measurable_pi_apply j).aemeasurable
      measurable_toss.aestronglyMeasurable).symm
  have h2 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac true) :=
    Measure.smul_finite _ (by simp)
  have h3 : IsFiniteMeasure ((1 / 2 : ENNReal) • Measure.dirac false) :=
    Measure.smul_finite _ (by simp)
  rw [h1, h, coin, integral_add_measure (Integrable.of_finite ..) (Integrable.of_finite ..)]
  simp [toss]

lemma rad_sq (j : ℕ) (ω : ℕ → Bool) : rad j ω ^ 2 = 1 := by
  unfold rad toss
  split_ifs <;> norm_num

/-- The direction `e₁ e₂ᵀ` of the noise. -/
def Eo : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The rank-one matrix `e₁ (e₁ + a e₂)ᵀ`. -/
noncomputable def wOf (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Pe + a • Eo

/-- The core `√(1 + a²)` of `wOf a`. -/
noncomputable def rho (a : ℝ) : ℝ := √(1 + a ^ 2)

lemma rho_pos (a : ℝ) : 0 < rho a := Real.sqrt_pos.2 (by positivity)

lemma rho_inv_sq (a : ℝ) : (rho a)⁻¹ ^ 2 * (1 + a ^ 2) = 1 := by
  have h : rho a ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  rw [← h, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (rho_pos a).ne')]

/-- The unit row factor of `wOf a`. -/
noncomputable def vOf (a : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![(rho a)⁻¹; a * (rho a)⁻¹]

/-- The unit vector orthogonal to `vOf a`. -/
noncomputable def vPerp (a : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![-a * (rho a)⁻¹; (rho a)⁻¹]

/-- The core of `wOf a`. -/
noncomputable def sOf (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := rho a • 1

lemma vOf_orth (a : ℝ) : (vOf a)ᵀ * vOf a = 1 := by
  ext i j
  fin_cases i; fin_cases j
  have h := rho_inv_sq a
  simp [vOf, Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith

lemma vHat_orth (a : ℝ) :
    (Matrix.fromCols (vOf a) (vPerp a))ᵀ * Matrix.fromCols (vOf a) (vPerp a) = 1 := by
  have h := rho_inv_sq a
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [vOf, vPerp, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

lemma vHat_proj (a : ℝ) :
    Matrix.fromCols (vOf a) (vPerp a) * (Matrix.fromCols (vOf a) (vPerp a))ᵀ = 1 := by
  have h := rho_inv_sq a
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [vOf, vPerp] <;> nlinarith

lemma sOf_det (a : ℝ) : IsUnit (sOf a).det := by
  simpa [sOf, Matrix.det_fin_one] using (rho_pos a).ne'

lemma wOf_eq (a : ℝ) : e₁ * sOf a * (vOf a)ᵀ = wOf a := by
  have h : (rho a)⁻¹ * rho a = 1 := inv_mul_cancel₀ (rho_pos a).ne'
  have e1 : e₁ * sOf a = rho a • e₁ := by
    rw [sOf, Matrix.mul_smul, Matrix.mul_one]
  rw [e1, Matrix.smul_mul]
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [e₁, vOf, wOf, Pe, Eo, mul_comm (rho a), mul_assoc, h]

lemma Pe_Eo : Pe * Eo = Eo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pe, Eo, Matrix.mul_apply, Fin.sum_univ_two]

lemma norm_Eo : ‖Eo‖ = 1 := by
  have h : ‖Eo‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Eo, Fin.sum_univ_two]
  nlinarith [norm_nonneg Eo]

lemma tangentProj_Eo (a : ℝ) : tangentProj e₁ (vOf a) Eo = Eo := by
  rw [tangentProj_apply', e₁_mul, Pe_Eo]
  abel

lemma wOf_step (ξ lr a : ℝ) :
    IsGeoLoRAStep (ξ • Eo) lr e₁ (sOf a) (vOf a) e₂ (vPerp a) :=
  ⟨e₁_orth, vOf_orth a, sOf_det a, hat_orth, vHat_orth a, by rw [hat_proj, Matrix.one_mul],
    by rw [vHat_proj, Matrix.one_mul]⟩

lemma tangentAt_wOf (a ξ : ℝ) : tangentAt (wOf a) (ξ • Eo) = ξ • Eo := by
  rw [← wOf_eq, tangentAt_eq e₁_orth (vOf_orth a) (sOf_det a), map_smul, tangentProj_Eo]

lemma wOf_update (ξ lr a : ℝ) : IsGeoLoRAUpdate (ξ • Eo) lr (wOf a) (wOf (a - lr * ξ)) := by
  refine ⟨1, 1, 1, e₁, sOf a, vOf a, e₂, vPerp a, wOf_step ξ lr a, (wOf_eq a).symm, ?_⟩
  rw [geoWhat_eq (wOf_step ξ lr a), wOf_eq, map_smul, tangentProj_Eo, wOf, wOf, sub_smul, mul_smul]
  abel

/-- The noise-driven coefficient of the counterexample. -/
noncomputable def aSeq (lr : ℕ → ℝ) : ℕ → (ℕ → Bool) → ℝ
  | 0, _ => 0
  | k + 1, ω => aSeq lr k ω - lr k * rad (k + 1) ω

/-- The natural filtration of the coins. -/
noncomputable def coinFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  Filtration.natural rad stronglyMeasurable_rad

lemma stronglyMeasurable_aSeq (lr : ℕ → ℝ) (k : ℕ) :
    StronglyMeasurable[coinFiltration k] (aSeq lr k) := by
  induction k with
  | zero => exact stronglyMeasurable_const
  | succ k ih =>
    have h1 : StronglyMeasurable[coinFiltration (k + 1)] (aSeq lr k) :=
      ih.mono (coinFiltration.mono k.le_succ)
    have h2 : StronglyMeasurable[coinFiltration (k + 1)] (rad (k + 1)) :=
      Filtration.stronglyAdapted_natural stronglyMeasurable_rad (k + 1)
    exact h1.sub (h2.const_mul (lr k))

/-- **The conclusion of Thm 2 of arXiv 2410.18720, read literally, is false.**  In the notation of
the paper `f(W_t) = f(W_t, ξ_t)` is the stochastic gradient, and the printed conclusion is
`liminf E ‖P(W_t) f(W_t, ξ_t)‖² = 0`.  Take `ℒ = 0` with the stochastic losses `ξ ⟪e₁ e₂ᵀ, W⟫`,
for fair signs `ξ`, on `2 × 2` matrices at rank `1`.  For **every** sequence of learning rates,
all hypotheses of the theorem and of `convergence` hold, with `∇ℒ = 0`, unit variance and no
truncation at all, but `E ‖P(W_k) G_k‖² = 1` for all `k`: the noise is tangent to the manifold.
(So the hypotheses of `convergence` hold with non-trivial noise; there the conclusion is the
trivial `0 = 0` for this `ℒ`.) -/
theorem stochastic_conclusion_false (lr : ℕ → ℝ) :
    ∃ (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)))
      (W G Wh : ℕ → (ℕ → Bool) → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ k, StronglyMeasurable[ℱ k] (W k)) ∧ (∀ k, StronglyMeasurable (G k)) ∧
      (∀ k, Integrable (fun ω => ‖G k ω‖ ^ 2) coins) ∧
      (∀ k, coins[G k | ℱ k] =ᵐ[coins] fun _ => 0) ∧
      (∀ k, ∫ ω, ‖G k ω‖ ^ 2 ∂coins ≤ 1) ∧
      (∀ k ω, IsGeoLoRAUpdate (G k ω) (lr k) (W k ω) (Wh k ω)) ∧
      (∀ k ω, W (k + 1) ω = Wh k ω) ∧
      liminf (fun k => ∫ ω, ‖tangentAt (W k ω) (G k ω)‖ ^ 2 ∂coins) atTop = 1 := by
  set G : ℕ → (ℕ → Bool) → Matrix (Fin 2) (Fin 2) ℝ := fun k ω => rad (k + 1) ω • Eo with hG
  set W : ℕ → (ℕ → Bool) → Matrix (Fin 2) (Fin 2) ℝ := fun k ω => wOf (aSeq lr k ω) with hW
  have hnorm : ∀ k ω, ‖G k ω‖ ^ 2 = 1 := fun k ω => by
    rw [hG]
    simp only [norm_smul, Real.norm_eq_abs, norm_Eo, mul_one, sq_abs, rad_sq]
  have hGm : ∀ k, StronglyMeasurable (G k) := fun k =>
    (stronglyMeasurable_rad (k + 1)).smul_const Eo
  have hint : ∀ k, Integrable (fun ω => ‖G k ω‖ ^ 2) coins := fun k => by
    simp only [hnorm]
    exact integrable_const _
  have hcond : ∀ k, coins[G k | coinFiltration k] =ᵐ[coins] fun _ => 0 := fun k => by
    have hind := iIndepFun_rad.indep_comap_natural_of_lt stronglyMeasurable_rad k.lt_succ_self
    have hm : StronglyMeasurable[MeasurableSpace.comap (rad (k + 1)) inferInstance] (G k) :=
      (comap_measurable (rad (k + 1))).stronglyMeasurable.smul_const Eo
    have h1 := condExp_indep_eq (stronglyMeasurable_rad (k + 1)).measurable.comap_le
      (coinFiltration.le k) hm hind
    have h2 : ∫ ω, G k ω ∂coins = 0 := by
      rw [hG]
      simp only
      rw [integral_smul_const, integral_rad, zero_smul]
    rwa [h2] at h1
  refine ⟨coinFiltration, W, G, fun k ω => W (k + 1) ω, fun k => ?_, hGm, hint, hcond,
    fun k => ?_, fun k ω => wOf_update _ _ _, fun _ _ => rfl, ?_⟩
  · have h := stronglyMeasurable_aSeq lr k
    exact stronglyMeasurable_const.add (h.smul_const Eo)
  · simp only [hnorm]
    simp
  · have h : ∀ k, ∫ ω, ‖tangentAt (W k ω) (G k ω)‖ ^ 2 ∂coins = 1 := fun k => by
      have e : ∀ ω, ‖tangentAt (W k ω) (G k ω)‖ ^ 2 = 1 := fun ω => by
        rw [hW, hG]
        simp only
        rw [tangentAt_wOf]
        exact hnorm k ω
      simp only [e]
      simp
    simp only [h]
    exact liminf_const 1

end NoiseFloor

end LeanDLRA.Literature.P2410_18720
