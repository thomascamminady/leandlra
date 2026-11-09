import LeanDLRA.Integrators.BUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Curvature

/-!
# Differentiating through a DLRA integrator: discrete adjoints of BUG-type steps

Open problem OP-TR-37 of `docs/survey/open-problems.json` (arXiv 2506.21405 Sec. 6, arXiv
2610.29554 Sec. 7).  The question: when is a BUG step `Y ↦ Y₁`, including QR
and rank truncation, differentiable, what is its exact discrete adjoint, and is that adjoint
robust, i.e. independent of `1 / σ_r`?

The object is the explicit Euler BUG step on real matrices (`bugStep`): with `A = Y + h F(Y)`, Euler
K- and L-steps give `K = A V`, `L = Aᵀ U`, the new projectors are `P₁ = K K⁺`, `Q₁ = L L⁺`, and the
Euler Galerkin S-step gives `Y₁ = P₁ (Y' + h F(Y')) Q₁` with `Y' = P₁ Y Q₁`.

## What is proved

* **QR.**  The step sees QR only through `K K⁺` (`colProj_eq_of_qr`, `bugStep_eq_of_qr`) and depends
  only on the ranges of the bases (`bugStep_gauge`).  `K ↦ K K⁺` is Fréchet differentiable where
  `K` has full column rank (`hasD_colProj`), with `‖δP‖_F ≤ 2 ‖(1 - P) δK‖_F ‖K⁺‖₂`
  (`norm_dProj_le`).
* **Differentiability.**  If `K`, `L` have full column rank and `F` is differentiable at `Y` and
  `Y'`, the step is Fréchet differentiable, with derivative the straight-line program `bugTangent`
  (`HasD.bugStep`).  `barStep` extends the step from rank-`r` matrices to a neighbourhood in matrix
  space (`barStep_eq_bugStep`, `hasD_barStep`).  The condition `h ‖F(Y)‖_F σ_r⁻¹ ≤ 1/2` implies the
  rank conditions (`side_facts`).
* **Exact discrete adjoint.**  `bugAdjoint` is the reverse sweep (`inner_bugTangent`), and
  `barAdjoint` is the resulting gradient on matrix space (`inner_barTangent`).  The basis gradients
  have the residuals `A (1 - Q₁)` and `(1 - P₁) A` as factors (`bugAdjoint_basis_residual`).
* **Not robust, exactly.**  At a rank-`r` matrix with a constant purely normal field `N` the step
  has the fixed point `Y`, with derivative exactly `𝒯 + h 𝒲` for every `h`, where `𝒯` is the
  tangent projector and `𝒲 Z = N Zᵀ Y⁺ᵀ + Y⁺ᵀ Zᵀ N` is the shape operator (`normal_tangent`).  Its
  eigenvalues on `p vᵀ ± u qᵀ` are `1 ± h ν / σ` for singular triples `(σ, u, v)` of `Y` and
  `(ν, p, q)` of `N` (`normal_eigen`).  So the gradient after `k` steps is multiplied by exactly
  `(1 + h ν / σ)ᵏ` (`bug_adjoint_growth`), which is at least `exp (t ν / (σ + h ν))` at `t = k h`
  (`growth_factor_ge`), while the forward error is exactly `t ‖N‖_F` (`bug_adjoint_not_robust`).
* **The sharp rate.**  For tangent `Z`, `‖δY₁‖_F ≤ (1 + h ε / σ_r + 45 b² + 48 h L) ‖Z‖_F` with
  `ε = ‖(1 - P) F(Y) (1 - Q)‖₂` and `b = h ‖F(Y)‖_F / σ_r ≤ 1/2` (`norm_barTangent_le`).  The same
  bound holds for the tangential part of the adjoint (`norm_tanProj_barAdjoint_le`), and along a
  trajectory the growth is at most `exp (T (ε / σ_r + 48 L + O(h / σ_r²)))`
  (`tangent_growth_le`).  So at first order `1 / σ_r` enters only multiplied by the normal size of
  the field, the modelling error `ε` of the robust theory.  Thus `ε T ≲ σ_r` suffices for bounded
  amplification, up to the terms in `L` and `h / σ_r²`, and by `bug_adjoint_growth` this condition
  cannot be relaxed in general.
* **The rank conditions cannot be dropped.**  The step is a dilation by `1 + h / σ` for the identity
  field on `{σ U Uᵀ}` (`bugStep_dilation`), it has no continuous extension to lower rank
  (`bugStep_no_limit_at_zero`), and none to a point where `K` loses rank (`rank_loss_no_limit`).
* **Truncation.**  Only a sharp special case: the rank-one truncation of `[a τ; τ b]` has derivative
  `a / (a - b)` in `τ` at `τ = 0` (`truncOne_deriv`).

## Mechanism

Three identities drive the proofs.  First `(1 - P₁) A Q = 0`, so that a change of the basis `V`
moves `P₁` only through the residual `(1 - P₁) A`, which has the size of the normal part `ε`
(`residual_facts`).  Second, `K⁺ A = Vᵀ + h K⁺ F (1 - Q)` removes the factor `1 / σ_r` from the
change of `P₁` caused by `δY` (`dProj_mul_A_sub_le`).  Third, the frozen-basis part is the
projection of `Z` onto the new tangent space up to a product of two sines (`norm_frozen_le`).

## Pseudoinverse

`K⁺ = (Kᵀ K)⁻¹ Kᵀ` is the core Gram pseudoinverse `Matrix.gramPinv`
(`LinearAlgebra/Factorization/Defs.lean`), the Moore–Penrose inverse of `K` wherever `K` has full
column rank (`Matrix.gramPinv_eq_pinv`), which is where the results here use it.  The local `pinv`
of an earlier version of this file was the same definition (unification batch C1).

## Not covered

Exact (non-Euler) substeps, and differentiability of rank truncation at a general matrix with a
positive gap, are not treated.  The constants `45` and `48` are not claimed to be sharp; the
constant `1` in front of `h ε / σ_r` is sharp by `bug_adjoint_growth`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpTR37

open LeanDLRA LeanDLRA.Frobenius LeanDLRA.Curvature

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {l m n r : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype r]

/-! ### Differentiation calculus -/

section Calculus

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- `f` is Fréchet differentiable at `x` and its derivative acts as `d`. -/
def HasD (f : E → G) (x : E) (d : E → G) : Prop :=
  ∃ D : E →L[ℝ] G, HasFDerivAt f D x ∧ ∀ v, D v = d v

lemma HasD.congr {f : E → G} {x : E} {d d' : E → G} (h : HasD f x d) (hd : ∀ v, d v = d' v) :
    HasD f x d' := by
  obtain ⟨D, hD, hv⟩ := h
  exact ⟨D, hD, fun v => (hv v).trans (hd v)⟩

lemma HasD.add {f g : E → G} {x : E} {d e : E → G} (hf : HasD f x d) (hg : HasD g x e) :
    HasD (fun y => f y + g y) x fun v => d v + e v := by
  obtain ⟨D, hD, hv⟩ := hf
  obtain ⟨D', hD', hv'⟩ := hg
  exact ⟨D + D', hD.add hD', fun v => by simp [hv, hv']⟩

lemma HasD.const_smul {f : E → G} {x : E} {d : E → G} (c : ℝ) (hf : HasD f x d) :
    HasD (fun y => c • f y) x fun v => c • d v := by
  obtain ⟨D, hD, hv⟩ := hf
  exact ⟨c • D, hD.const_smul c, fun v => by simp [hv]⟩

lemma HasD.clm_comp {f : E → G} {x : E} {d : E → G} {G' : Type*} [NormedAddCommGroup G']
    [NormedSpace ℝ G'] {g : G → G'} {J : G →L[ℝ] G'} (hf : HasD f x d)
    (hg : HasFDerivAt g J (f x)) : HasD (fun y => g (f y)) x fun v => J (d v) := by
  obtain ⟨D, hD, hv⟩ := hf
  exact ⟨J.comp D, hg.comp x hD, fun v => by simp [hv]⟩

lemma HasD.mul {f : E → Matrix l m ℝ} {g : E → Matrix m r ℝ} {x : E}
    {d : E → Matrix l m ℝ} {e : E → Matrix m r ℝ} (hf : HasD f x d) (hg : HasD g x e) :
    HasD (fun y => f y * g y) x fun v => d v * g x + f x * e v := by
  obtain ⟨D, hD, hv⟩ := hf
  obtain ⟨D', hD', hv'⟩ := hg
  have h := (mulCLM (m := l) (l := m) (n := r)).hasFDerivAt_of_bilinear hD hD'
  refine ⟨_, h, fun v => ?_⟩
  simp [hv, hv', add_comm]

lemma HasD.transpose {f : E → Matrix l m ℝ} {x : E} {d : E → Matrix l m ℝ} (hf : HasD f x d) :
    HasD (fun y => (f y)ᵀ) x fun v => (d v)ᵀ := by
  simpa using hf.clm_comp (transposeCLM (m := l) (n := m)).hasFDerivAt

lemma hasD_id (x : E) : HasD (fun y : E => y) x fun v => v :=
  ⟨.id ℝ E, hasFDerivAt_id x, fun _ => rfl⟩

lemma hasD_const (x : E) (c : G) : HasD (fun _ : E => c) x fun _ => 0 :=
  ⟨0, hasFDerivAt_const c x, fun _ => rfl⟩

lemma HasD.fst {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] {f : E → G × G'} {x : E}
    {d : E → G × G'} (hf : HasD f x d) : HasD (fun y => (f y).1) x fun v => (d v).1 := by
  simpa using hf.clm_comp (g := Prod.fst) (J := .fst ℝ G G') hasFDerivAt_fst

lemma HasD.snd {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] {f : E → G × G'} {x : E}
    {d : E → G × G'} (hf : HasD f x d) : HasD (fun y => (f y).2) x fun v => (d v).2 := by
  simpa using hf.clm_comp (g := Prod.snd) (J := .snd ℝ G G') hasFDerivAt_snd

/-- The derivative of the matrix inverse: `δ(S⁻¹) = -S⁻¹ δS S⁻¹`. -/
theorem hasFDerivAt_inv [DecidableEq r] (S : Matrix r r ℝ) (hS : IsUnit S) :
    HasFDerivAt (fun T : Matrix r r ℝ => T⁻¹)
      (-((rightMulCLM S⁻¹).comp (leftMulCLM S⁻¹) : Matrix r r ℝ →L[ℝ] Matrix r r ℝ)) S := by
  let _ : NormedRing (Matrix r r ℝ) := Matrix.frobeniusNormedRing
  let _ : NormedAlgebra ℝ (Matrix r r ℝ) := Matrix.frobeniusNormedAlgebra
  obtain ⟨u, rfl⟩ := hS
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hu : (↑u⁻¹ : Matrix r r ℝ) = (↑u : Matrix r r ℝ)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  have hf : (fun T : Matrix r r ℝ => T⁻¹) = Ring.inverse := by
    funext T; rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [hf]
  rw [hu] at h
  refine h.congr_fderiv ?_
  ext Z i j
  simp [ContinuousLinearMap.mulLeftRight_apply]

lemma HasD.inv [DecidableEq r] {f : E → Matrix r r ℝ} {x : E} {d : E → Matrix r r ℝ}
    (hf : HasD f x d) (hu : IsUnit (f x)) :
    HasD (fun y => (f y)⁻¹) x fun v => -((f x)⁻¹ * d v * (f x)⁻¹) := by
  simpa using hf.clm_comp (hasFDerivAt_inv (f x) hu)

end Calculus

/-! ### The orthogonal projector onto a column space -/

section Projector

variable [DecidableEq r]

/-- The orthogonal projector `K K⁺` onto the column space of `K`.  QR factorisation enters a BUG
step only through this matrix, see `colProj_eq_of_qr`. -/
noncomputable def colProj (K : Matrix m r ℝ) : Matrix m m ℝ := K * K.gramPinv

/-- `K⁺ K = 1` for `K` of full column rank (the core `Matrix.gramPinv_mul_self`). -/
lemma pinv_mul_self {K : Matrix m r ℝ} (hK : IsUnit (Kᵀ * K)) : K.gramPinv * K = 1 :=
  Matrix.gramPinv_mul_self ((Matrix.isUnit_iff_isUnit_det _).1 hK)

/-- `(K⁺)ᵀ = K (Kᵀ K)⁻¹` (the core `Matrix.transpose_gramPinv`). -/
lemma pinv_transpose (K : Matrix m r ℝ) : (K.gramPinv)ᵀ = K * (Kᵀ * K)⁻¹ :=
  Matrix.transpose_gramPinv K

lemma colProj_transpose (K : Matrix m r ℝ) : (colProj K)ᵀ = colProj K := by
  rw [colProj, Matrix.transpose_mul, pinv_transpose, Matrix.gramPinv, Matrix.mul_assoc]

lemma colProj_mul_self {K : Matrix m r ℝ} (hK : IsUnit (Kᵀ * K)) : colProj K * K = K := by
  rw [colProj, Matrix.mul_assoc, pinv_mul_self hK, Matrix.mul_one]

lemma pinv_mul_colProj {K : Matrix m r ℝ} (hK : IsUnit (Kᵀ * K)) :
    K.gramPinv * colProj K = K.gramPinv := by
  rw [colProj, ← Matrix.mul_assoc, pinv_mul_self hK, Matrix.one_mul]

lemma isOrthProjMat_colProjK {K : Matrix m r ℝ} (hK : IsUnit (Kᵀ * K)) :
    IsOrthProjMat (colProj K) :=
  ⟨colProj_transpose K, by
    simp only [colProj]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (K.gramPinv), pinv_mul_self hK, Matrix.one_mul]⟩

/-- Replacing a basis by another basis of the same column space does not change the projector. -/
lemma colProj_mul_unit {K : Matrix m r ℝ} {C : Matrix r r ℝ} (hC : IsUnit C) :
    colProj (K * C) = colProj K := by
  have hdC := (Matrix.isUnit_iff_isUnit_det C).1 hC
  have hdCt : IsUnit Cᵀ.det := by rwa [Matrix.det_transpose]
  have hinv : ((K * C)ᵀ * (K * C))⁻¹ = C⁻¹ * (Kᵀ * K)⁻¹ * Cᵀ⁻¹ := by
    have : (K * C)ᵀ * (K * C) = Cᵀ * ((Kᵀ * K) * C) := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [colProj, Matrix.gramPinv, hinv, colProj, Matrix.gramPinv, Matrix.transpose_mul]
  calc K * C * (C⁻¹ * (Kᵀ * K)⁻¹ * Cᵀ⁻¹ * (Cᵀ * Kᵀ))
      = K * (C * C⁻¹) * (Kᵀ * K)⁻¹ * (Cᵀ⁻¹ * Cᵀ) * Kᵀ := by simp only [Matrix.mul_assoc]
    _ = K * ((Kᵀ * K)⁻¹ * Kᵀ) := by
      rw [Matrix.mul_nonsing_inv _ hdC, Matrix.nonsing_inv_mul _ hdCt]
      simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- **QR enters only through the projector.**  If `K = U₁ R` with orthonormal `U₁` and invertible
`R`, then `U₁ U₁ᵀ = K K⁺`, for every QR factorisation of `K`. -/
theorem colProj_eq_of_qr {K U₁ : Matrix m r ℝ} {R : Matrix r r ℝ} (hK : K = U₁ * R)
    (hU : U₁ᵀ * U₁ = 1) (hR : IsUnit R) : colProj K = U₁ * U₁ᵀ := by
  subst hK
  rw [colProj_mul_unit hR, colProj, Matrix.gramPinv, hU, inv_one, Matrix.one_mul]

variable [DecidableEq m]

/-- The derivative `δP = (1 - P) δK K⁺ + K⁺ᵀ δKᵀ (1 - P)` of `P = K K⁺` along `δK`. -/
noncomputable def dProj (K δ : Matrix m r ℝ) : Matrix m m ℝ :=
  (1 - colProj K) * δ * K.gramPinv + (K.gramPinv)ᵀ * δᵀ * (1 - colProj K)

/-- The adjoint of `dProj`: `⟪dProj K δ, X⟫ = ⟪δ, dProjAdj K X⟫`. -/
noncomputable def dProjAdj (K : Matrix m r ℝ) (X : Matrix m m ℝ) : Matrix m r ℝ :=
  (1 - colProj K) * (X + Xᵀ) * (K.gramPinv)ᵀ

theorem inner_dProj (K δ : Matrix m r ℝ) (X : Matrix m m ℝ) :
    ⟪dProj K δ, X⟫ = ⟪δ, dProjAdj K X⟫ := by
  have hc : (1 - colProj K)ᵀ = 1 - colProj K := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, colProj_transpose]
  have h1 : ⟪(1 - colProj K) * δ * K.gramPinv, X⟫ = ⟪δ, (1 - colProj K) * X * (K.gramPinv)ᵀ⟫ := by
    rw [inner_mul_right, inner_mul_left, hc, Matrix.mul_assoc]
  have h2 : ⟪(K.gramPinv)ᵀ * δᵀ * (1 - colProj K), X⟫ =
      ⟪δ, (1 - colProj K) * Xᵀ * (K.gramPinv)ᵀ⟫ := by
    rw [inner_mul_right, inner_mul_left, Matrix.transpose_transpose, hc, ← inner_transpose,
      Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.transpose_mul, hc, Matrix.mul_assoc]
  rw [dProj, dProjAdj, inner_add_left, h1, h2, Matrix.mul_add, Matrix.add_mul, inner_add_right]

/-- **Differentiability of the projector** (QR step).  On the open set of matrices of full column
rank the map `K ↦ K K⁺` is Fréchet differentiable with derivative `dProj`.  This is the QR part of
OP-TR-37: differentiating the projector avoids choosing a differentiable QR factorisation.  With
`norm_dProj_le` it gives the bound by `‖K⁺‖₂` proposed in the proof idea of OP-TR-37, the
infinitesimal form of the projector-difference bounds of `Matrix/Curvature`. -/
theorem hasD_colProj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : E → Matrix m r ℝ}
    {x : E} {d : E → Matrix m r ℝ} (hK : HasD K x d) (hu : IsUnit ((K x)ᵀ * K x)) :
    HasD (fun y => colProj (K y)) x fun v => dProj (K x) (d v) := by
  have hC := (hK.transpose.mul hK).inv hu
  refine (hK.mul (hC.mul hK.transpose)).congr fun v => ?_
  set C := ((K x)ᵀ * K x)⁻¹ with hCdef
  rw [dProj, colProj, pinv_transpose, Matrix.gramPinv, ← hCdef]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

end Projector

/-! ### The explicit Euler BUG step -/

section Step

variable [DecidableEq r]

/-- The full Euler matrix `A = Y + h F(Y)`. -/
noncomputable def eulerMat (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (Y : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Y + h • F Y

/-- The new column projector: `P₁` projects onto the range of the K-step result `A V`. -/
noncomputable def newP (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (V : Matrix n r ℝ)
    (Y : Matrix m n ℝ) : Matrix m m ℝ :=
  colProj (eulerMat F h Y * V)

/-- The new row projector: `Q₁` projects onto the range of the L-step result `Aᵀ U`. -/
noncomputable def newQ (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U : Matrix m r ℝ)
    (Y : Matrix m n ℝ) : Matrix n n ℝ :=
  colProj ((eulerMat F h Y)ᵀ * U)

/-- The initial value `P₁ Y Q₁` of the Galerkin S-step. -/
noncomputable def galStart (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U : Matrix m r ℝ)
    (V : Matrix n r ℝ) (Y : Matrix m n ℝ) : Matrix m n ℝ :=
  newP F h V Y * Y * newQ F h U Y

/-- **The explicit Euler BUG step** from `Y` with column basis `U` and row basis `V`: Euler K- and
L-steps give `K = A V` and `L = Aᵀ U`, and the Euler Galerkin S-step in the new bases gives
`Y₁ = P₁ (Y' + h F(Y')) Q₁` with `Y' = P₁ Y Q₁`. -/
noncomputable def bugStep (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U : Matrix m r ℝ)
    (V : Matrix n r ℝ) (Y : Matrix m n ℝ) : Matrix m n ℝ :=
  newP F h V Y * (galStart F h U V Y + h • F (galStart F h U V Y)) * newQ F h U Y

/-- The definition is the algorithm: with any QR factorisations of the K- and L-step results,
`bugStep` is `U₁ (S₀ + h U₁ᵀ F(U₁ S₀ V₁ᵀ) V₁) V₁ᵀ` with `S₀ = U₁ᵀ Y V₁`. -/
theorem bugStep_eq_of_qr {F : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ} {U U₁ : Matrix m r ℝ}
    {V V₁ : Matrix n r ℝ} {Y : Matrix m n ℝ} {RK RL : Matrix r r ℝ}
    (hK : eulerMat F h Y * V = U₁ * RK) (hL : (eulerMat F h Y)ᵀ * U = V₁ * RL)
    (hU : U₁ᵀ * U₁ = 1) (hV : V₁ᵀ * V₁ = 1) (hRK : IsUnit RK) (hRL : IsUnit RL) :
    bugStep F h U V Y =
      U₁ * ((U₁ᵀ * Y * V₁) + h • (U₁ᵀ * F (U₁ * (U₁ᵀ * Y * V₁) * V₁ᵀ) * V₁)) * V₁ᵀ := by
  have hP : newP F h V Y = U₁ * U₁ᵀ := colProj_eq_of_qr hK hU hRK
  have hQ : newQ F h U Y = V₁ * V₁ᵀ := colProj_eq_of_qr hL hV hRL
  have hG : galStart F h U V Y = U₁ * (U₁ᵀ * Y * V₁) * V₁ᵀ := by
    rw [galStart, hP, hQ]; simp only [Matrix.mul_assoc]
  rw [bugStep, hG, hP, hQ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  simp only [hV, hU, ← Matrix.mul_assoc U₁ᵀ U₁, ← Matrix.mul_assoc V₁ᵀ V₁, Matrix.one_mul]

variable [DecidableEq m] [DecidableEq n]

/-- The **tangent-linear model** of the Euler BUG step, as a straight-line program: the directions
`dU`, `dV`, `dY` of the two bases and of `Y` are pushed through the step. -/
noncomputable def bugTangent (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (Y : Matrix m n ℝ) (dU : Matrix m r ℝ) (dV : Matrix n r ℝ) (dY : Matrix m n ℝ) :
    Matrix m n ℝ :=
  let A := eulerMat F h Y
  let P := newP F h V Y
  let Q := newQ F h U Y
  let Y' := galStart F h U V Y
  let dA := dY + h • J dY
  let dP := dProj (A * V) (dA * V + A * dV)
  let dQ := dProj (Aᵀ * U) (dAᵀ * U + Aᵀ * dU)
  let dY' := dP * Y * Q + P * dY * Q + P * Y * dQ
  dP * (Y' + h • F Y') * Q + P * (dY' + h • J' dY') * Q + P * (Y' + h • F Y') * dQ

/-- **Differentiability of the BUG step.**  If `F` is differentiable at `Y` and at the S-step
start `Y'`, and the K- and L-step results have full column rank, the BUG step is Fréchet
differentiable along any differentiable family of data, with derivative `bugTangent`.  This answers
the first part of OP-TR-37 for Euler substeps; the integrator is that of Ceruti–Lubich
(arXiv 2010.02022), whose robust analysis does not use derivatives of the step. -/
theorem HasD.bugStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ} {J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    {U : E → Matrix m r ℝ} {V : E → Matrix n r ℝ} {Y : E → Matrix m n ℝ} {x : E}
    {dU : E → Matrix m r ℝ} {dV : E → Matrix n r ℝ} {dY : E → Matrix m n ℝ}
    (hU : HasD U x dU) (hV : HasD V x dV) (hY : HasD Y x dY)
    (hJ : HasFDerivAt F J (Y x)) (hJ' : HasFDerivAt F J' (galStart F h (U x) (V x) (Y x)))
    (hK : IsUnit ((eulerMat F h (Y x) * V x)ᵀ * (eulerMat F h (Y x) * V x)))
    (hL : IsUnit (((eulerMat F h (Y x))ᵀ * U x)ᵀ * ((eulerMat F h (Y x))ᵀ * U x))) :
    HasD (fun y => OpTR37.bugStep F h (U y) (V y) (Y y)) x fun v =>
      bugTangent F h J J' (U x) (V x) (Y x) (dU v) (dV v) (dY v) := by
  have hA : HasD (fun y => eulerMat F h (Y y)) x fun v => dY v + h • J (dY v) :=
    hY.add ((hY.clm_comp hJ).const_smul h)
  have hP : HasD (fun y => newP F h (V y) (Y y)) x _ := hasD_colProj (hA.mul hV) hK
  have hQ : HasD (fun y => newQ F h (U y) (Y y)) x _ := hasD_colProj (hA.transpose.mul hU) hL
  have hG : HasD (fun y => galStart F h (U y) (V y) (Y y)) x _ := (hP.mul hY).mul hQ
  have hS := hG.add ((hG.clm_comp hJ').const_smul h)
  refine ((hP.mul hS).mul hQ).congr fun v => ?_
  simp only [bugTangent, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

/-- The **exact discrete adjoint** of the BUG step, as the reverse sweep of `bugTangent`.  `Js`
and `Js'` stand for `J†`, `J'†`.  The components are the gradients with respect to `U`, `V`, `Y`
of `⟪bugStep, Ψ⟫`. -/
noncomputable def bugAdjoint (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (Y Ψ : Matrix m n ℝ) : Matrix m r ℝ × Matrix n r ℝ × Matrix m n ℝ :=
  let A := eulerMat F h Y
  let P := newP F h V Y
  let Q := newQ F h U Y
  let Y' := galStart F h U V Y
  let B := Y' + h • F Y'
  let bS := P * Ψ * Q
  let bY := bS + h • Js' bS
  let bP := Ψ * Q * Bᵀ + bY * Q * Yᵀ
  let bQ := Bᵀ * P * Ψ + Yᵀ * P * bY
  let bK := dProjAdj (A * V) bP
  let bL := dProjAdj (Aᵀ * U) bQ
  let bA := bK * Vᵀ + U * bLᵀ
  (A * bL, Aᵀ * bK, P * bY * Q + (bA + h • Js bA))

/-- **The exact discrete adjoint identity.**  `⟪δY₁, Ψ⟫` of the tangent-linear model equals the
pairing of the directions `(dU, dV, dY)` with the output of the reverse sweep `bugAdjoint`, where
`Js = J†` and `Js' = J'†`.  This is the exact gradient needed for discretize-then-project, unlike
the DLRA approximations of the continuous adjoint in `LeanDLRA/Control/AdjointDLRA.lean`. -/
theorem inner_bugTangent (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    {J J' Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, Js y⟫) (hJs' : ∀ x y, ⟪J' x, y⟫ = ⟪x, Js' y⟫)
    (U : Matrix m r ℝ) (V : Matrix n r ℝ) (Y : Matrix m n ℝ) (dU : Matrix m r ℝ)
    (dV : Matrix n r ℝ) (dY Ψ : Matrix m n ℝ) :
    ⟪bugTangent F h J J' U V Y dU dV dY, Ψ⟫ =
      ⟪dU, (bugAdjoint F h Js Js' U V Y Ψ).1⟫ + ⟪dV, (bugAdjoint F h Js Js' U V Y Ψ).2.1⟫ +
        ⟪dY, (bugAdjoint F h Js Js' U V Y Ψ).2.2⟫ := by
  simp only [bugTangent, bugAdjoint]
  set A := eulerMat F h Y
  set Q := newQ F h U Y with hQ
  set P := newP F h V Y with hP
  set Y' := galStart F h U V Y
  set B := Y' + h • F Y'
  set dA := dY + h • J dY with hdA
  set dK := dA * V + A * dV with hdK
  set dL := dAᵀ * U + Aᵀ * dU with hdL
  set dP := dProj (A * V) dK
  set dQ := dProj (Aᵀ * U) dL
  set bS := P * Ψ * Q
  set bY := bS + h • Js' bS
  set bP := Ψ * Q * Bᵀ + bY * Q * Yᵀ
  set bQ := Bᵀ * P * Ψ + Yᵀ * P * bY
  set bK := dProjAdj (A * V) bP
  set bL := dProjAdj (Aᵀ * U) bQ
  set bA := bK * Vᵀ + U * bLᵀ
  have hPt : Pᵀ = P := colProj_transpose _
  have hQt : Qᵀ = Q := colProj_transpose _
  have e1 : ∀ X : Matrix m n ℝ, ⟪dP * X * Q, Ψ⟫ = ⟪dP, Ψ * Q * Xᵀ⟫ := fun X => by
    rw [Matrix.mul_assoc, inner_mul_right, Matrix.transpose_mul, hQt, Matrix.mul_assoc]
  have e2 : ∀ X : Matrix m n ℝ, ⟪P * X * dQ, Ψ⟫ = ⟪dQ, Xᵀ * P * Ψ⟫ := fun X => by
    rw [Matrix.mul_assoc, inner_mul_left, inner_mul_left, hPt, Matrix.mul_assoc]
  have e3 : ∀ X Z : Matrix m n ℝ, ⟪P * X * Q, Z⟫ = ⟪X, P * Z * Q⟫ := fun X Z => by
    rw [Matrix.mul_assoc, inner_mul_left, inner_mul_right, hPt, hQt]
  have e4 : ⟪dP * Y * Q + P * dY * Q + P * Y * dQ, bY⟫ =
      ⟪dP, bY * Q * Yᵀ⟫ + ⟪dY, P * bY * Q⟫ + ⟪dQ, Yᵀ * P * bY⟫ := by
    rw [inner_add_left, inner_add_left, e3]
    congr 1
    · congr 1
      rw [Matrix.mul_assoc, inner_mul_right, Matrix.transpose_mul, hQt, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, inner_mul_left, inner_mul_left, hPt, Matrix.mul_assoc]
  have e5 : ⟪dP, bP⟫ = ⟪dA, bK * Vᵀ⟫ + ⟪dV, Aᵀ * bK⟫ := by
    rw [inner_dProj, hdK, inner_add_left, inner_mul_right, inner_mul_left]
  have e6 : ⟪dQ, bQ⟫ = ⟪dA, U * bLᵀ⟫ + ⟪dU, A * bL⟫ := by
    rw [inner_dProj, hdL, inner_add_left, inner_mul_right, inner_mul_left,
      Matrix.transpose_transpose, ← inner_transpose dAᵀ, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have e7 : ⟪dA, bA⟫ = ⟪dY, bA + h • Js bA⟫ := by
    rw [hdA, inner_add_left, inner_add_right dY bA (h • Js bA), real_inner_smul_left,
      real_inner_smul_right, hJs]
  have e8 : ∀ X : Matrix m n ℝ, ⟪X + h • J' X, bS⟫ = ⟪X, bY⟫ := fun X => by
    rw [inner_add_left, inner_add_right X bS (h • Js' bS), real_inner_smul_left,
      real_inner_smul_right, hJs']
  rw [inner_add_left, inner_add_left, e1, e2, e3, e8, e4,
    inner_add_right dY (P * bY * Q) (bA + h • Js bA), ← e7]
  have e9 : ⟪dP, Ψ * Q * Bᵀ⟫ + ⟪dP, bY * Q * Yᵀ⟫ = ⟪dP, bP⟫ := (inner_add_right _ _ _).symm
  have e10 : ⟪dQ, Bᵀ * P * Ψ⟫ + ⟪dQ, Yᵀ * P * bY⟫ = ⟪dQ, bQ⟫ := (inner_add_right _ _ _).symm
  have e11 : ⟪dA, bK * Vᵀ⟫ + ⟪dA, U * bLᵀ⟫ = ⟪dA, bA⟫ := (inner_add_right _ _ _).symm
  linarith


/-- Replacing bases by other bases of the same ranges does not change the BUG step. -/
theorem bugStep_gauge (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U : Matrix m r ℝ)
    (V : Matrix n r ℝ) (Y : Matrix m n ℝ) {C D : Matrix r r ℝ} (hC : IsUnit C) (hD : IsUnit D) :
    bugStep F h (U * C) (V * D) Y = bugStep F h U V Y := by
  have hP : newP F h (V * D) Y = newP F h V Y := by
    rw [newP, ← Matrix.mul_assoc, colProj_mul_unit hD, newP]
  have hQ : newQ F h (U * C) Y = newQ F h U Y := by
    rw [newQ, ← Matrix.mul_assoc, colProj_mul_unit hC, newQ]
  simp only [bugStep, galStart, hP, hQ]

/-- The BUG step as a map on matrix space near `Y = U S Vᵀ`: the bases of a nearby matrix `B` are
read off from `B` itself.  On rank-`r` matrices this is the BUG step, see `barStep_eq_bugStep`. -/
noncomputable def barStep (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U : Matrix m r ℝ)
    (S : Matrix r r ℝ) (V : Matrix n r ℝ) (B : Matrix m n ℝ) : Matrix m n ℝ :=
  bugStep F h (B * V * S⁻¹) (Bᵀ * U * Sᵀ⁻¹) B

/-- `barStep` is the BUG step of `B`: if `B = U' S' V'ᵀ` and `B V S⁻¹`, `Bᵀ U S⁻ᵀ` are bases of the
ranges of `U'`, `V'` (which holds for all rank-`r` matrices `B` near `Y`). -/
theorem barStep_eq_bugStep (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) {U U' : Matrix m r ℝ}
    {S : Matrix r r ℝ} {V V' : Matrix n r ℝ} {B : Matrix m n ℝ} {C D : Matrix r r ℝ}
    (hC : B * V * S⁻¹ = U' * C) (hD : Bᵀ * U * Sᵀ⁻¹ = V' * D) (hCu : IsUnit C) (hDu : IsUnit D) :
    barStep F h U S V B = bugStep F h U' V' B := by
  rw [barStep, hC, hD, bugStep_gauge F h U' V' B hCu hDu]

lemma hasD_mul_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l' : Type*}
    [Fintype l'] {f : E → Matrix l m ℝ} {x : E} {d : E → Matrix l m ℝ} (hf : HasD f x d)
    (A : Matrix m l' ℝ) (B : Matrix l' r ℝ) :
    HasD (fun y => f y * A * B) x fun v => d v * A * B := by
  refine ((hf.mul (hasD_const x A)).mul (hasD_const x B)).congr fun v => ?_
  simp

/-- The tangent map of `barStep` at `Y = U S Vᵀ`. -/
noncomputable def barTangent (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  bugTangent F h J J' U V (U * S * Vᵀ) (Z * V * S⁻¹) (Zᵀ * U * Sᵀ⁻¹) Z

section Frame

variable {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ}

lemma frame_mul_V (hV : Vᵀ * V = 1) (hS : IsUnit S) : U * S * Vᵀ * V * S⁻¹ = U := by
  have hd := (Matrix.isUnit_iff_isUnit_det S).1 hS
  rw [Matrix.mul_assoc (U * S), hV, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one]

lemma frame_transpose_mul_U (hU : Uᵀ * U = 1) (hS : IsUnit S) :
    (U * S * Vᵀ)ᵀ * U * Sᵀ⁻¹ = V := by
  have hd : IsUnit Sᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det S).1 hS
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc V * (Sᵀ * Uᵀ) * U * Sᵀ⁻¹ = V * (Sᵀ * (Uᵀ * U) * Sᵀ⁻¹) := by simp only [Matrix.mul_assoc]
    _ = V := by rw [hU, Matrix.mul_one, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

/-- **Differentiability of the BUG step on rank-`r` matrices.** -/
theorem hasD_barStep {F : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ}
    {J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : IsUnit S) (hJ : HasFDerivAt F J (U * S * Vᵀ))
    (hJ' : HasFDerivAt F J' (galStart F h U V (U * S * Vᵀ)))
    (hK : IsUnit ((eulerMat F h (U * S * Vᵀ) * V)ᵀ * (eulerMat F h (U * S * Vᵀ) * V)))
    (hL : IsUnit (((eulerMat F h (U * S * Vᵀ))ᵀ * U)ᵀ * ((eulerMat F h (U * S * Vᵀ))ᵀ * U))) :
    HasD (barStep F h U S V) (U * S * Vᵀ) (barTangent F h J J' U S V) := by
  have e1 := frame_mul_V (U := U) hV hS
  have e2 := frame_transpose_mul_U (V := V) hU hS
  have hU' := hasD_mul_mul (hasD_id (U * S * Vᵀ)) V S⁻¹
  have hV' := hasD_mul_mul (hasD_id (U * S * Vᵀ)).transpose U Sᵀ⁻¹
  have key := HasD.bugStep (F := F) (h := h) (J := J) (J' := J') hU' hV'
    (hasD_id (U * S * Vᵀ)) hJ (by simpa only [e1, e2] using hJ')
    (by simpa only [e1, e2] using hK) (by simpa only [e1, e2] using hL)
  simp only [e1, e2] at key
  exact key

end Frame

/-! ### Normal fixed points: the exact derivative -/

section Normal

variable {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ} {N : Matrix m n ℝ}

omit [DecidableEq m] [DecidableEq n] in
lemma tmul_mul {k : Type*} [Fintype k] (hU : Uᵀ * U = 1) (X : Matrix r k ℝ) :
    Uᵀ * (U * X) = X := by
  rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- `(U S)⁺ = S⁻¹ Uᵀ` for orthonormal `U` and invertible `S` (the core `Matrix.gramPinv_mul`). -/
lemma pinv_mul_unit (hU : Uᵀ * U = 1) (hS : IsUnit S) : (U * S).gramPinv = S⁻¹ * Uᵀ :=
  Matrix.gramPinv_mul hU ((Matrix.isUnit_iff_isUnit_det S).1 hS)

/-- `dProj` for a frame `U S`. -/
lemma dProj_frame {k : Type*} [Fintype k] [DecidableEq k] {U : Matrix k r ℝ} (hU : Uᵀ * U = 1)
    (hS : IsUnit S) (δ : Matrix k r ℝ) :
    dProj (U * S) δ = (1 - U * Uᵀ) * δ * (S⁻¹ * Uᵀ) + (U * Sᵀ⁻¹) * δᵀ * (1 - U * Uᵀ) := by
  have hP : colProj (U * S) = U * Uᵀ := colProj_eq_of_qr rfl hU hS
  rw [dProj, hP, pinv_mul_unit hU hS, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv]

/-- The operator `Z ↦ N Zᵀ Y⁺ᵀ + Y⁺ᵀ Zᵀ N` with `Y⁺ᵀ = U S⁻ᵀ Vᵀ`: the shape operator (Weingarten
map) of the manifold of rank-`r` matrices at `Y = U S Vᵀ` in the normal direction `N`. -/
noncomputable def shapeOp (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ)
    (N Z : Matrix m n ℝ) : Matrix m n ℝ :=
  N * Zᵀ * (U * Sᵀ⁻¹ * Vᵀ) + (U * Sᵀ⁻¹ * Vᵀ) * Zᵀ * N

/-- The orthogonal projector `Z ↦ Z - (1 - P) Z (1 - Q)` onto the tangent space. -/
noncomputable def tanProj (P : Matrix m m ℝ) (Q : Matrix n n ℝ) (Z : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Z - (1 - P) * Z * (1 - Q)

variable (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hNU : Uᵀ * N = 0) (hNV : N * V = 0)
include hU hV hS hNU hNV

/-- At a rank-`r` matrix whose field is purely normal the K- and L-steps change nothing. -/
lemma normal_K (h : ℝ) : eulerMat (fun _ => N) h (U * S * Vᵀ) * V = U * S := by
  rw [eulerMat, Matrix.add_mul, Matrix.smul_mul, hNV, smul_zero, add_zero, Matrix.mul_assoc, hV,
    Matrix.mul_one]

lemma normal_L (h : ℝ) : (eulerMat (fun _ => N) h (U * S * Vᵀ))ᵀ * U = V * Sᵀ := by
  have e : Nᵀ * U = 0 := by rw [← Matrix.transpose_transpose U, ← Matrix.transpose_mul, hNU]; simp
  rw [eulerMat, Matrix.transpose_add, Matrix.add_mul, Matrix.transpose_smul, Matrix.smul_mul, e,
    smul_zero, add_zero]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hU, Matrix.mul_one]

lemma normal_newP (h : ℝ) : newP (fun _ => N) h V (U * S * Vᵀ) = U * Uᵀ :=
  colProj_eq_of_qr (normal_K hU hV hS hNU hNV h) hU hS

lemma normal_newQ (h : ℝ) : newQ (fun _ => N) h U (U * S * Vᵀ) = V * Vᵀ := by
  have hd : IsUnit Sᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det S).1 hS
  exact colProj_eq_of_qr (normal_L hU hV hS hNU hNV h) hV hd

lemma normal_gal (h : ℝ) : galStart (fun _ => N) h U V (U * S * Vᵀ) = U * S * Vᵀ := by
  rw [galStart, normal_newP hU hV hS hNU hNV, normal_newQ hU hV hS hNU hNV]
  simp only [Matrix.mul_assoc, tmul_mul hU, tmul_mul hV]

/-- **Fixed point.**  A rank-`r` matrix with a purely normal constant field is a fixed point of the
BUG step, for every `h`. -/
theorem normal_bugStep (h : ℝ) : bugStep (fun _ => N) h U V (U * S * Vᵀ) = U * S * Vᵀ := by
  have e1 : U * Uᵀ * N = 0 := by rw [Matrix.mul_assoc, hNU, Matrix.mul_zero]
  have e2 : N * (V * Vᵀ) = 0 := by rw [← Matrix.mul_assoc, hNV, Matrix.zero_mul]
  rw [bugStep, normal_gal hU hV hS hNU hNV, normal_newP hU hV hS hNU hNV,
    normal_newQ hU hV hS hNU hNV, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, e1,
    smul_zero, Matrix.zero_mul, add_zero]
  have := normal_gal hU hV hS hNU hNV h
  rwa [galStart, normal_newP hU hV hS hNU hNV, normal_newQ hU hV hS hNU hNV] at this

theorem normal_barStep (h : ℝ) :
    barStep (fun _ => N) h U S V (U * S * Vᵀ) = U * S * Vᵀ := by
  rw [barStep, frame_mul_V hV hS, frame_transpose_mul_U hU hS, normal_bugStep hU hV hS hNU hNV]

/-- **The exact derivative at a normal fixed point**, for every step size `h`: the tangent map of
the BUG step at `Y = U S Vᵀ` with constant purely normal field `N` is `𝒯 + h 𝒲`, with `𝒯` the
orthogonal projector onto the tangent space and `𝒲 = shapeOp` the shape operator in direction `N`.
There is no remainder in `h`.  It identifies the curvature term of the discrete adjoint with the
term of size `1 / σ_r` in the derivative of the tangent projector, Koch–Lubich (2007, Lemma 4.2). -/
theorem normal_tangent (h : ℝ) (Z : Matrix m n ℝ) :
    barTangent (fun _ => N) h 0 0 U S V Z =
      tanProj (U * Uᵀ) (V * Vᵀ) Z + h • shapeOp U S V N Z := by
  have hSu : IsUnit Sᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hNUt : Nᵀ * U = 0 := by
    rw [← Matrix.transpose_transpose U, ← Matrix.transpose_mul, hNU]; simp
  have hPn := normal_newP hU hV hS hNU hNV h
  have hQn := normal_newQ hU hV hS hNU hNV h
  have hGn := normal_gal hU hV hS hNU hNV h
  have hKn := normal_K hU hV hS hNU hNV h
  have hLn := normal_L hU hV hS hNU hNV h
  simp only [barTangent, bugTangent, hPn, hQn, hGn, hKn, hLn, _root_.zero_apply,
    smul_zero, add_zero, dProj_frame hU hS, dProj_frame hV hSu, Matrix.transpose_transpose]
  have hA : eulerMat (fun _ => N) h (U * S * Vᵀ) = U * S * Vᵀ + h • N := rfl
  rw [hA]
  set Y := U * S * Vᵀ with hY
  set A := Y + h • N with hAdef
  set P := U * Uᵀ with hP
  set Q := V * Vᵀ with hQ
  set Sit := Sᵀ⁻¹ with hSit
  have hSd := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hPU : P * U = U := by rw [hP, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hVQ : Vᵀ * Q = Vᵀ := by rw [hQ, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hPY' : P * Y = Y := by rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPU]
  have hYQ' : Y * Q = Y := by rw [hY, Matrix.mul_assoc, hVQ]
  have hPN : P * N = 0 := by rw [hP, Matrix.mul_assoc, hNU, Matrix.mul_zero]
  have hNQ : N * Q = 0 := by rw [hQ, ← Matrix.mul_assoc, hNV, Matrix.zero_mul]
  have hPP : P * P = P := (isOrthProjMat_mul_transpose hU).idem
  have hQQ : Q * Q = Q := (isOrthProjMat_mul_transpose hV).idem
  have hcP : P * (1 - P) = 0 := by rw [Matrix.mul_sub, hPP, Matrix.mul_one, sub_self]
  have hcQ : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, hQQ, Matrix.one_mul, sub_self]
  have hcPY : (1 - P) * Y = 0 := by rw [Matrix.sub_mul, hPY', Matrix.one_mul, sub_self]
  have hcYQ : Y * (1 - Q) = 0 := by rw [Matrix.mul_sub, hYQ', Matrix.mul_one, sub_self]
  have hcPN : (1 - P) * N = N := by rw [Matrix.sub_mul, hPN, Matrix.one_mul, sub_zero]
  have hcNQ : N * (1 - Q) = N := by rw [Matrix.mul_sub, hNQ, Matrix.mul_one, sub_zero]
  have hPA : P * A = Y := by rw [hAdef, Matrix.mul_add, Matrix.mul_smul, hPN, smul_zero, add_zero,
    hPY']
  have hAQ : A * Q = Y := by rw [hAdef, Matrix.add_mul, Matrix.smul_mul, hNQ, smul_zero, add_zero,
    hYQ']
  have hSY : S⁻¹ * Uᵀ * Y = Vᵀ := by
    rw [hY, Matrix.mul_assoc S⁻¹, ← Matrix.mul_assoc Uᵀ, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSd, Matrix.one_mul]
  have hYS : Y * (V * S⁻¹) = U := by
    rw [← Matrix.mul_assoc]; exact frame_mul_V hV hS
  set δ₁ := Z * V + A * (Zᵀ * U * Sit) with hδ₁
  set δ₂ := Zᵀ * U + Aᵀ * (Z * V * S⁻¹) with hδ₂
  have f1 : (1 - P) * δ₁ = (1 - P) * Z * V + h • (N * (Zᵀ * U * Sit)) := by
    rw [hδ₁, Matrix.mul_add, ← Matrix.mul_assoc (1 - P) A, hAdef, Matrix.mul_add (1 - P) Y,
      hcPY, Matrix.mul_smul, hcPN, zero_add, ← Matrix.mul_assoc, Matrix.smul_mul]
  have f2 : δ₂ᵀ * (1 - Q) = Uᵀ * Z * (1 - Q) + h • ((Z * V * S⁻¹)ᵀ * N) := by
    rw [hδ₂, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul Aᵀ,
      Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.add_mul,
      Matrix.mul_assoc _ A, hAdef, Matrix.add_mul Y, hcYQ, Matrix.smul_mul, hcNQ, zero_add,
      Matrix.mul_smul]
  set dP := (1 - P) * δ₁ * (S⁻¹ * Uᵀ) + U * Sit * δ₁ᵀ * (1 - P) with hdP
  set dQ := (1 - Q) * δ₂ * (Sit * Vᵀ) + V * S⁻¹ * δ₂ᵀ * (1 - Q) with hdQ
  have g1 : dP * Y = (1 - P) * δ₁ * Vᵀ := by
    rw [hdP, Matrix.add_mul, Matrix.mul_assoc (U * Sit * δ₁ᵀ), hcPY, Matrix.mul_zero, add_zero,
      Matrix.mul_assoc _ (S⁻¹ * Uᵀ), hSY]
  have g2 : Y * dQ = U * δ₂ᵀ * (1 - Q) := by
    rw [hdQ, Matrix.mul_add]
    have e1 : Y * ((1 - Q) * δ₂ * (Sit * Vᵀ)) = 0 := by
      rw [Matrix.mul_assoc (1 - Q), ← Matrix.mul_assoc Y, hcYQ, Matrix.zero_mul]
    have e2 : Y * (V * S⁻¹ * δ₂ᵀ * (1 - Q)) = U * δ₂ᵀ * (1 - Q) := by
      rw [Matrix.mul_assoc (V * S⁻¹), ← Matrix.mul_assoc Y, hYS, Matrix.mul_assoc]
    rw [e1, e2, zero_add]
  have g3 : dP * A * Q = dP * Y := by rw [Matrix.mul_assoc, hAQ]
  have g4 : P * A * dQ = Y * dQ := by rw [hPA]
  have g5 : P * (dP * Y * Q + P * Z * Q + P * Y * dQ) * Q = P * Z * Q := by
    rw [hPY', g1, g2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
    have e1 : P * ((1 - P) * δ₁ * Vᵀ * Q) * Q = 0 := by
      simp only [← Matrix.mul_assoc, hcP, Matrix.zero_mul]
    have e2 : P * (P * Z * Q) * Q = P * Z * Q := by
      calc P * (P * Z * Q) * Q = (P * P) * Z * (Q * Q) := by simp only [Matrix.mul_assoc]
        _ = P * Z * Q := by rw [hPP, hQQ]
    have e3 : P * (U * δ₂ᵀ * (1 - Q)) * Q = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ (1 - Q) Q, hcQ, Matrix.mul_zero, Matrix.mul_zero]
    rw [e1, e2, e3, zero_add, add_zero]
  rw [g3, g4, g5, g1, g2, f1, Matrix.mul_assoc U δ₂ᵀ, f2]
  have htr : (Z * V * S⁻¹)ᵀ = Sit * Vᵀ * Zᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
  rw [htr, tanProj, shapeOp]
  have hexp : U * (Uᵀ * Z * (1 - Q)) = P * Z * (1 - Q) := by
    simp only [hP, Matrix.mul_assoc]
  rw [Matrix.mul_add U, hexp]
  have hexp2 : (1 - P) * Z * V * Vᵀ = (1 - P) * Z * Q := by simp only [hQ, Matrix.mul_assoc]
  have e1 : ((1 - P) * Z * V + h • (N * (Zᵀ * U * Sit))) * Vᵀ =
      (1 - P) * Z * Q + h • (N * Zᵀ * (U * Sit * Vᵀ)) := by
    rw [Matrix.add_mul, hexp2, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
  have e2 : U * (h • (Sit * Vᵀ * Zᵀ * N)) = h • (U * Sit * Vᵀ * Zᵀ * N) := by
    rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
  rw [e1, e2, smul_add]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  abel

end Normal

/-! ### The spectrum at a normal fixed point and the failure of robustness -/

section Spectrum

variable {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ} {N : Matrix m n ℝ}

/-- A singular triple: `Y v = σ u` and `Yᵀ u = σ v`. -/
structure IsSingularTriple {m n : Type*} [Fintype m] [Fintype n] (Y : Matrix m n ℝ) (σ : ℝ)
    (u : m → ℝ) (v : n → ℝ) : Prop where
  left : Y *ᵥ v = σ • u
  right : Yᵀ *ᵥ u = σ • v

lemma mul_vecMulVec_mul {k k' : Type*} [Fintype k] [Fintype k'] (A : Matrix m k ℝ)
    (B : Matrix k' n ℝ) (x : k → ℝ) (y : k' → ℝ) :
    A * Matrix.vecMulVec x y * B = Matrix.vecMulVec (A *ᵥ x) (Bᵀ *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma vecMulVec_zero' {k k' : Type*} (w : k → ℝ) :
    Matrix.vecMulVec w (0 : k' → ℝ) = 0 := by
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- The iterates of a self-adjoint map are self-adjoint. -/
lemma inner_pow_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : E →L[ℝ] E} (hD : ∀ Z X, ⟪D Z, X⟫ = ⟪Z, D X⟫) (k : ℕ) (Z X : E) :
    ⟪(D ^ k) Z, X⟫ = ⟪Z, (D ^ k) X⟫ := by
  induction k generalizing Z X with
  | zero => simp
  | succ k ih =>
    have e1 : ∀ W, (D ^ (k + 1)) W = (D ^ k) (D W) := fun W => by rw [pow_succ]; rfl
    have e2 : ∀ W, (D ^ (k + 1)) W = D ((D ^ k) W) := fun W => by rw [pow_succ']; rfl
    rw [e1, ih, hD, e2]

/-- The iterates act on an eigenvector by powers of the eigenvalue. -/
lemma pow_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : E →L[ℝ] E} {X : E} {μ : ℝ} (hX : D X = μ • X) (k : ℕ) : (D ^ k) X = μ ^ k • X := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e2 : (D ^ (k + 1)) X = D ((D ^ k) X) := by rw [pow_succ']; rfl
    rw [e2, ih, map_smul, hX, smul_smul, pow_succ]

theorem inner_tanProj_add_shapeOp (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (h : ℝ)
    (Z X : Matrix m n ℝ) :
    ⟪tanProj (U * Uᵀ) (V * Vᵀ) Z + h • shapeOp U S V N Z, X⟫ =
      ⟪Z, tanProj (U * Uᵀ) (V * Vᵀ) X + h • shapeOp U S V N X⟫ := by
  have hP := (isOrthProjMat_mul_transpose hU).compl.symm
  have hQ := (isOrthProjMat_mul_transpose hV).compl.symm
  have e1 : ⟪(1 - U * Uᵀ) * Z * (1 - V * Vᵀ), X⟫ = ⟪Z, (1 - U * Uᵀ) * X * (1 - V * Vᵀ)⟫ := by
    rw [inner_mul_right, inner_mul_left, hP, hQ, Matrix.mul_assoc]
  have e2 : ∀ T : Matrix m n ℝ, ⟪N * Zᵀ * T, X⟫ = ⟪Z, T * Xᵀ * N⟫ := fun T => by
    rw [inner_mul_right, inner_mul_left, ← inner_transpose Zᵀ, Matrix.transpose_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have e3 : ∀ T : Matrix m n ℝ, ⟪T * Zᵀ * N, X⟫ = ⟪Z, N * Xᵀ * T⟫ := fun T => by
    rw [inner_mul_right, inner_mul_left, ← inner_transpose Zᵀ, Matrix.transpose_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [tanProj, shapeOp, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, e1, e2, e3]
  ring

/-- The growth factor `(1 + h ν / σ)ᵏ` of `bug_adjoint_growth` dominates both `1 + k h ν / σ` and
the exponential `exp (k h ν / (σ + h ν))`. -/
theorem growth_factor_ge {σ ν h : ℝ} (hσ : 0 < σ) (hν : 0 < ν) (hh : 0 ≤ h) (k : ℕ) :
    1 + k * (h * ν / σ) ≤ (1 + h * ν / σ) ^ k ∧
      Real.exp (k * h * ν / (σ + h * ν)) ≤ (1 + h * ν / σ) ^ k := by
  have ha : 0 ≤ h * ν / σ := by positivity
  refine ⟨one_add_mul_le_pow (by linarith) k, ?_⟩
  set a := h * ν / σ with hadef
  have hx : h * ν / (σ + h * ν) = a / (1 + a) := by
    rw [hadef]; field_simp
  have h1 : Real.exp (a / (1 + a)) ≤ 1 + a := by
    have h2 := Real.add_one_le_exp (-(a / (1 + a)))
    have h3 : -(a / (1 + a)) + 1 = 1 / (1 + a) := by field_simp; ring
    rw [h3, Real.exp_neg] at h2
    have h4 := Real.exp_pos (a / (1 + a))
    have hp : 0 < 1 + a := by linarith
    rw [div_le_iff₀ hp] at h2
    rw [← inv_mul_le_iff₀ (Real.exp_pos _ |> inv_pos.2)] at h2
    simp only [inv_inv, mul_one] at h2
    nlinarith [h2]
  have e : Real.exp (k * h * ν / (σ + h * ν)) = Real.exp (a / (1 + a)) ^ k := by
    rw [← Real.exp_nat_mul, ← hx]; congr 1; ring
  rw [e]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h1 k

variable (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hNU : Uᵀ * N = 0) (hNV : N * V = 0)
include hU hV hS hNU hNV

/-- The derivative of the BUG step at a normal fixed point. -/
theorem exists_normal_deriv (h : ℝ) :
    ∃ D : Matrix m n ℝ →L[ℝ] Matrix m n ℝ,
      HasFDerivAt (barStep (fun _ => N) h U S V) D (U * S * Vᵀ) ∧
        ∀ Z, D Z = tanProj (U * Uᵀ) (V * Vᵀ) Z + h • shapeOp U S V N Z := by
  have hSt : IsUnit Sᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hK : IsUnit ((eulerMat (fun _ => N) h (U * S * Vᵀ) * V)ᵀ *
      (eulerMat (fun _ => N) h (U * S * Vᵀ) * V)) := by
    rw [normal_K hU hV hS hNU hNV, Matrix.transpose_mul, Matrix.mul_assoc, tmul_mul hU]
    exact hSt.mul hS
  have hL : IsUnit (((eulerMat (fun _ => N) h (U * S * Vᵀ))ᵀ * U)ᵀ *
      ((eulerMat (fun _ => N) h (U * S * Vᵀ))ᵀ * U)) := by
    rw [normal_L hU hV hS hNU hNV, Matrix.transpose_mul, Matrix.mul_assoc, tmul_mul hV,
      Matrix.transpose_transpose]
    exact hS.mul hSt
  obtain ⟨D, hD, hv⟩ := hasD_barStep (F := fun _ => N) (h := h) (J := 0) (J' := 0) hU hV hS
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) hK hL
  exact ⟨D, hD, fun Z => (hv Z).trans (normal_tangent hU hV hS hNU hNV h Z)⟩

variable {σ ν : ℝ} {u p : m → ℝ} {v q : n → ℝ}

/-- `𝒯 + h 𝒲` has the eigenvectors `p vᵀ ± u qᵀ` with eigenvalues `1 ± h ν / σ`. -/
theorem normal_eigen (hσ : σ ≠ 0) (hν : ν ≠ 0)
    (hY : IsSingularTriple (U * S * Vᵀ) σ u v) (hN : IsSingularTriple N ν p q) (h : ℝ)
    {s : ℝ} (hs : s * s = 1) :
    tanProj (U * Uᵀ) (V * Vᵀ) (Matrix.vecMulVec p v + s • Matrix.vecMulVec u q) +
        h • shapeOp U S V N (Matrix.vecMulVec p v + s • Matrix.vecMulVec u q) =
      (1 + s * (h * ν / σ)) • (Matrix.vecMulVec p v + s • Matrix.vecMulVec u q) := by
  have hNUt : Nᵀ * U = 0 := by
    rw [← Matrix.transpose_transpose U, ← Matrix.transpose_mul, hNU]; simp
  have hVNt : Vᵀ * Nᵀ = 0 := by rw [← Matrix.transpose_mul, hNV, Matrix.transpose_zero]
  have hSd := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hSdt : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  set Y := U * S * Vᵀ with hYdef
  have hYt : Yᵀ = V * Sᵀ * Uᵀ := by
    rw [hYdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have hPY : U * Uᵀ * Y = Y := by simp only [hYdef, Matrix.mul_assoc, tmul_mul hU]
  have hQY : V * Vᵀ * Yᵀ = Yᵀ := by simp only [hYt, Matrix.mul_assoc, tmul_mul hV]
  have hNYt : N * Yᵀ = 0 := by
    rw [hYt, Matrix.mul_assoc, ← Matrix.mul_assoc N, hNV, Matrix.zero_mul]
  have hNtY : Nᵀ * Y = 0 := by
    rw [hYdef, Matrix.mul_assoc, ← Matrix.mul_assoc Nᵀ, hNUt, Matrix.zero_mul]
  have hPu : (U * Uᵀ) *ᵥ u = u := by
    have e : (U * Uᵀ) *ᵥ (σ • u) = σ • u := by rw [← hY.left, Matrix.mulVec_mulVec, hPY]
    rw [Matrix.mulVec_smul] at e
    exact smul_right_injective _ hσ e
  have hQv : (V * Vᵀ) *ᵥ v = v := by
    have e : (V * Vᵀ) *ᵥ (σ • v) = σ • v := by rw [← hY.right, Matrix.mulVec_mulVec, hQY]
    rw [Matrix.mulVec_smul] at e
    exact smul_right_injective _ hσ e
  have hNv : N *ᵥ v = 0 := by
    have := congrArg (fun w => N *ᵥ w) hY.right
    simp only [Matrix.mulVec_mulVec, hNYt, Matrix.zero_mulVec, Matrix.mulVec_smul] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hσ
  have hNtu : Nᵀ *ᵥ u = 0 := by
    have := congrArg (fun w => Nᵀ *ᵥ w) hY.left
    simp only [Matrix.mulVec_mulVec, hNtY, Matrix.zero_mulVec, Matrix.mulVec_smul] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hσ
  have hUp : Uᵀ *ᵥ p = 0 := by
    have := congrArg (fun w => Uᵀ *ᵥ w) hN.left
    simp only [Matrix.mulVec_mulVec, hNU, Matrix.zero_mulVec, Matrix.mulVec_smul] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hν
  have hVq : Vᵀ *ᵥ q = 0 := by
    have := congrArg (fun w => Vᵀ *ᵥ w) hN.right
    simp only [Matrix.mulVec_mulVec, hVNt, Matrix.zero_mulVec, Matrix.mulVec_smul] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hν
  set T := U * Sᵀ⁻¹ * Vᵀ with hTdef
  have hTt : Tᵀ = V * S⁻¹ * Uᵀ := by
    rw [hTdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hTYt : T * Yᵀ = U * Uᵀ := by
    calc T * Yᵀ = U * (Sᵀ⁻¹ * (Vᵀ * V) * Sᵀ) * Uᵀ := by
          rw [hTdef, hYt]; simp only [Matrix.mul_assoc]
      _ = U * Uᵀ := by rw [hV, Matrix.mul_one, Matrix.nonsing_inv_mul _ hSdt, Matrix.mul_one]
  have hTtY : Tᵀ * Y = V * Vᵀ := by
    calc Tᵀ * Y = V * (S⁻¹ * (Uᵀ * U) * S) * Vᵀ := by
          rw [hTt, hYdef]; simp only [Matrix.mul_assoc]
      _ = V * Vᵀ := by rw [hU, Matrix.mul_one, Matrix.nonsing_inv_mul _ hSd, Matrix.mul_one]
  have hTv : T *ᵥ v = σ⁻¹ • u := by
    have := congrArg (fun w => T *ᵥ w) hY.right
    simp only [Matrix.mulVec_mulVec, hTYt, hPu, Matrix.mulVec_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ hσ, one_smul]
  have hTtu : Tᵀ *ᵥ u = σ⁻¹ • v := by
    have := congrArg (fun w => Tᵀ *ᵥ w) hY.left
    simp only [Matrix.mulVec_mulVec, hTtY, hQv, Matrix.mulVec_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ hσ, one_smul]
  have hTq : T *ᵥ q = 0 := by
    rw [hTdef, ← Matrix.mulVec_mulVec, hVq, Matrix.mulVec_zero]
  have hTtp : Tᵀ *ᵥ p = 0 := by
    rw [hTt, ← Matrix.mulVec_mulVec, hUp, Matrix.mulVec_zero]
  have sh1 : shapeOp U S V N (Matrix.vecMulVec p v) = (ν / σ) • Matrix.vecMulVec u q := by
    rw [shapeOp, ← hTdef, Matrix.transpose_vecMulVec, mul_vecMulVec_mul, mul_vecMulVec_mul, hNv,
      hTv, hN.right, Matrix.zero_vecMulVec, zero_add, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
      smul_smul]
    congr 1
    field_simp
  have sh2 : shapeOp U S V N (Matrix.vecMulVec u q) = (ν / σ) • Matrix.vecMulVec p v := by
    rw [shapeOp, ← hTdef, Matrix.transpose_vecMulVec, mul_vecMulVec_mul, mul_vecMulVec_mul, hTq,
      hN.left, hTtu, Matrix.zero_vecMulVec, add_zero, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
      smul_smul]
    congr 1
  have hcQv : (1 - V * Vᵀ)ᵀ *ᵥ v = 0 := by
    rw [(isOrthProjMat_mul_transpose hV).compl.symm, Matrix.sub_mulVec, Matrix.one_mulVec, hQv,
      sub_self]
  have hcPu : (1 - U * Uᵀ) *ᵥ u = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPu, sub_self]
  have tp1 : tanProj (U * Uᵀ) (V * Vᵀ) (Matrix.vecMulVec p v) = Matrix.vecMulVec p v := by
    rw [tanProj, mul_vecMulVec_mul, hcQv, vecMulVec_zero', sub_zero]
  have tp2 : tanProj (U * Uᵀ) (V * Vᵀ) (Matrix.vecMulVec u q) = Matrix.vecMulVec u q := by
    rw [tanProj, mul_vecMulVec_mul, hcPu, Matrix.zero_vecMulVec, sub_zero]
  have tl : ∀ A B : Matrix m n ℝ, tanProj (U * Uᵀ) (V * Vᵀ) (A + s • B) =
      tanProj (U * Uᵀ) (V * Vᵀ) A + s • tanProj (U * Uᵀ) (V * Vᵀ) B := fun A B => by
    simp only [tanProj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have sl : ∀ A B : Matrix m n ℝ, shapeOp U S V N (A + s • B) =
      shapeOp U S V N A + s • shapeOp U S V N B := fun A B => by
    simp only [shapeOp, Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  rw [tl, sl, tp1, tp2, sh1, sh2]
  set Z₁ := Matrix.vecMulVec p v
  set Z₂ := Matrix.vecMulVec u q
  have e : (1 + s * (h * ν / σ)) • (Z₁ + s • Z₂) =
      Z₁ + s • Z₂ + (s * (h * ν / σ)) • Z₁ + (s * s * (h * ν / σ)) • Z₂ := by module
  rw [e, hs, one_mul]
  have e2 : h * ν / σ = h * (ν / σ) := by ring
  rw [e2]
  module

/-- **Exact growth of the discrete adjoint at a normal fixed point.**
Let `Y = U S Vᵀ` have a singular triple `(σ, u, v)`, and let the field be a constant `N` with
`Uᵀ N = 0`, `N V = 0` and singular triple `(ν, p, q)`.  Then for the BUG step `Φ`, with any `h` and
`k`, `Y` is fixed and the gradient at `Y` of `B ↦ ⟪Φᵏ B, E⟫`, `E = p vᵀ + u qᵀ`, is exactly
`(1 + h ν / σ)ᵏ E`.  This is what a reverse sweep through `k` BUG steps returns, so the discrete
adjoint carries the factor `1 / σ`, for `σ = σ_r` in particular, in the same way as the derivative
of the tangent projector in Koch–Lubich (2007, Lemma 4.2) does for the continuous projected flow.
`exists_normal_instance` shows the hypotheses are satisfiable. -/
theorem bug_adjoint_growth {σ ν : ℝ} {u p : m → ℝ} {v q : n → ℝ} (hσ : σ ≠ 0) (hν : ν ≠ 0)
    (hY : IsSingularTriple (U * S * Vᵀ) σ u v) (hN : IsSingularTriple N ν p q) (h : ℝ) (k : ℕ) :
    (barStep (fun _ => N) h U S V)^[k] (U * S * Vᵀ) = U * S * Vᵀ ∧
      HasGradientAt
        (fun B => ⟪(barStep (fun _ => N) h U S V)^[k] B,
          Matrix.vecMulVec p v + Matrix.vecMulVec u q⟫)
        ((1 + h * ν / σ) ^ k • (Matrix.vecMulVec p v + Matrix.vecMulVec u q)) (U * S * Vᵀ) := by
  have hfix := normal_barStep hU hV hS hNU hNV h
  refine ⟨Function.iterate_fixed hfix k, ?_⟩
  obtain ⟨D, hD, hDv⟩ := exists_normal_deriv hU hV hS hNU hNV h
  set E := Matrix.vecMulVec p v + Matrix.vecMulVec u q with hE
  have hsa : ∀ Z X, ⟪D Z, X⟫ = ⟪Z, D X⟫ := fun Z X => by
    rw [hDv, hDv]; exact inner_tanProj_add_shapeOp hU hV h Z X
  have hEig : D E = (1 + h * ν / σ) • E := by
    have := normal_eigen hU hV hS hNU hNV hσ hν hY hN h (s := 1) (by norm_num)
    rw [one_smul, one_mul] at this
    rw [hDv]; exact this
  have hk := hD.iterate hfix k
  rw [hasGradientAt_iff_hasFDerivAt]
  have hc := (innerSL ℝ E).hasFDerivAt.comp (U * S * Vᵀ) hk
  have hf : (fun B => ⟪(barStep (fun _ => N) h U S V)^[k] B, E⟫) =
      (innerSL ℝ E) ∘ (barStep (fun _ => N) h U S V)^[k] := by
    funext B
    simp [real_inner_comm]
  rw [hf]
  refine hc.congr_fderiv ?_
  ext W
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply]
  rw [real_inner_comm, inner_pow_apply hsa, pow_apply_of_eigen hEig]
  exact real_inner_comm _ _

/-- **The discrete adjoint of BUG is not robust.**  In the setting of `bug_adjoint_growth`, with
`σ, ν > 0`, `h ≥ 0` and `t = k h`:
* the forward error of `Φᵏ` at `Y` against the exact solution `Y + t N` is exactly `t ‖N‖_F`, which
  does not involve `σ`, in line with the robust error bound of Ceruti–Lubich (arXiv 2010.02022);
* the exact functional `B ↦ ⟪B + t N, E⟫` has gradient `E`;
* the gradient error of the discrete adjoint is exactly `((1 + h ν / σ)ᵏ - 1) ‖E‖_F`, which is at
  least `(t ν / σ) ‖E‖_F`.
So gradients from discretize-then-optimize do not inherit the robust `O(ε + h)` accuracy of the
forward solution: the ratio `t ν / σ_r` enters. -/
theorem bug_adjoint_not_robust {σ ν h : ℝ} {u p : m → ℝ} {v q : n → ℝ} (hσ : 0 < σ) (hν : 0 < ν)
    (hh : 0 ≤ h) (hY : IsSingularTriple (U * S * Vᵀ) σ u v) (hN : IsSingularTriple N ν p q)
    (k : ℕ) :
    ‖(barStep (fun _ => N) h U S V)^[k] (U * S * Vᵀ) - (U * S * Vᵀ + (k * h) • N)‖ =
        k * h * ‖N‖ ∧
      HasGradientAt (fun B => ⟪B + (k * h) • N, Matrix.vecMulVec p v + Matrix.vecMulVec u q⟫)
        (Matrix.vecMulVec p v + Matrix.vecMulVec u q) (U * S * Vᵀ) ∧
      ‖(1 + h * ν / σ) ^ k • (Matrix.vecMulVec p v + Matrix.vecMulVec u q) -
          (Matrix.vecMulVec p v + Matrix.vecMulVec u q)‖ =
        ((1 + h * ν / σ) ^ k - 1) * ‖Matrix.vecMulVec p v + Matrix.vecMulVec u q‖ ∧
      k * (h * ν / σ) * ‖Matrix.vecMulVec p v + Matrix.vecMulVec u q‖ ≤
        ((1 + h * ν / σ) ^ k - 1) * ‖Matrix.vecMulVec p v + Matrix.vecMulVec u q‖ := by
  set E := Matrix.vecMulVec p v + Matrix.vecMulVec u q with hE
  have hgrow := (growth_factor_ge hσ hν hh k).1
  have hnn : 0 ≤ (1 + h * ν / σ) ^ k - 1 := by
    have : 0 ≤ (k : ℝ) * (h * ν / σ) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(bug_adjoint_growth hU hV hS hNU hNV hσ.ne' hν.ne' hY hN h k).1]
    have e : U * S * Vᵀ - (U * S * Vᵀ + ((k : ℝ) * h) • N) = -(((k : ℝ) * h) • N) := by abel
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rw [hasGradientAt_iff_hasFDerivAt]
    have hc := (innerSL ℝ E).hasFDerivAt.comp (U * S * Vᵀ)
      ((hasFDerivAt_id (U * S * Vᵀ)).add_const (((k : ℝ) * h) • N))
    have hf : (fun B => ⟪B + ((k : ℝ) * h) • N, E⟫) =
        (innerSL ℝ E) ∘ fun B => id B + ((k : ℝ) * h) • N := by
      funext B
      simp [real_inner_comm]
    rw [hf]
    refine hc.congr_fderiv ?_
    ext W
    simp [real_inner_comm]
  · have e : (1 + h * ν / σ) ^ k • E - E = ((1 + h * ν / σ) ^ k - 1) • E := by
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    linarith

end Spectrum

/-! ### An upper bound: the only `1 / σ_r` term at first order carries the normal part -/

section Robust

/-- `specNorm` is subadditive. -/
lemma specNorm_add_le {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']
    (A B : Matrix k k' ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B := by
  refine specNorm_le_of (add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) fun x => ?_
  have e : Matrix.toEuclideanLin (A + B) x =
      Matrix.toEuclideanLin A x + Matrix.toEuclideanLin B x := by
    simp [Matrix.toLpLin_apply]
  rw [e, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_toEuclideanLin_le _ _) (norm_toEuclideanLin_le _ _))

lemma specNorm_smul_le {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']
    (c : ℝ) (A : Matrix k k' ℝ) : specNorm (c • A) ≤ |c| * specNorm A := by
  refine specNorm_le_of (mul_nonneg (abs_nonneg _) (specNorm_nonneg _)) fun x => ?_
  have e : Matrix.toEuclideanLin (c • A) x = c • Matrix.toEuclideanLin A x := by
    simp [Matrix.toLpLin_apply]
  rw [e, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le _ _) (abs_nonneg _)

/-- A matrix with a left inverse has full column rank in the sense used here. -/
lemma isUnit_transpose_mul_self {K : Matrix m r ℝ} {C : Matrix r m ℝ} (hC : C * K = 1) :
    IsUnit (Kᵀ * K) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : Kᵀ *ᵥ (K *ᵥ (a - b)) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_sub]; exact sub_eq_zero.2 hab
  have h1 : K *ᵥ (a - b) = 0 := by
    have := congrArg (fun w => (a - b) ⬝ᵥ w) h0
    simp only [dotProduct_zero] at this
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact dotProduct_self_eq_zero.1 this
  have h2 : a - b = 0 := by
    have := congrArg (fun w => C *ᵥ w) h1
    simpa [Matrix.mulVec_mulVec, hC] using this
  exact sub_eq_zero.1 h2

lemma specNorm_transpose_le_one {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {U : Matrix k k' ℝ} (hU : Uᵀ * U = 1) : specNorm Uᵀ ≤ 1 := by
  rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU

lemma specNorm_mul_le_of {k₁ k₂ k₃ : Type*} [Fintype k₁] [Fintype k₂] [Fintype k₃]
    [DecidableEq k₂] [DecidableEq k₃] {A : Matrix k₁ k₂ ℝ} {B : Matrix k₂ k₃ ℝ} {a b : ℝ}
    (hA : specNorm A ≤ a) (hB : specNorm B ≤ b) : specNorm (A * B) ≤ a * b :=
  (specNorm_mul_le A B).trans
    (mul_le_mul hA hB (specNorm_nonneg _) ((specNorm_nonneg _).trans hA))

/-- If `C K = 1 + E` with `‖E‖₂ ≤ 1/2`, then `K` has full column rank and `‖K⁺‖₂ ≤ 2 ‖C‖₂`. -/
lemma left_inverse_bound {K : Matrix m r ℝ} {C : Matrix r m ℝ} {E : Matrix r r ℝ}
    (hCK : C * K = 1 + E) (hE : specNorm E ≤ 1 / 2) :
    IsUnit (Kᵀ * K) ∧ specNorm (K.gramPinv) ≤ 2 * specNorm C := by
  have hlow : ∀ x : EuclideanSpace ℝ r, (1 / 2 : ℝ) * ‖x‖ ≤ ‖Matrix.toEuclideanLin (1 + E) x‖ := by
    intro x
    have e : Matrix.toEuclideanLin (1 + E) x = x + Matrix.toEuclideanLin E x := by
      simp [Matrix.toLpLin_apply]
    have h1 := norm_toEuclideanLin_le E x
    have h2 : ‖x‖ ≤ ‖x + Matrix.toEuclideanLin E x‖ + ‖Matrix.toEuclideanLin E x‖ := by
      simpa using norm_sub_le (x + Matrix.toEuclideanLin E x) (Matrix.toEuclideanLin E x)
    rw [e]
    have h3 : specNorm E * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
    linarith
  have hE1d := isUnit_det_of_bounded_below (by norm_num) hlow
  have hE1i : specNorm (1 + E)⁻¹ ≤ 2 := by
    have := specNorm_inv_le (S := 1 + E) (ρ := 1 / 2) (by norm_num) hlow
    simpa using this
  have hKtK : ((1 + E)⁻¹ * C) * K = 1 := by
    rw [Matrix.mul_assoc, hCK, Matrix.nonsing_inv_mul _ hE1d]
  have hKu : IsUnit (Kᵀ * K) := isUnit_transpose_mul_self hKtK
  have hOP := isOrthProjMat_colProjK hKu
  have hpinv : K.gramPinv = ((1 + E)⁻¹ * C) * colProj K := by
    rw [colProj, ← Matrix.mul_assoc, hKtK, Matrix.one_mul]
  refine ⟨hKu, ?_⟩
  rw [hpinv]
  have := specNorm_mul_le_of (specNorm_mul_le_of hE1i (le_refl (specNorm C))) hOP.specNorm_le_one
  simpa using this

/-- Geometry of one side of the step: if `h ‖G‖ σ_r⁻¹ ≤ 1/2`, then `K = A V` has full column rank,
`‖K⁺‖₂ ≤ 2 σ_r⁻¹`, and the old and new column spaces are close. -/
theorem side_facts {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ} {G A : Matrix m n ℝ}
    {h : ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hA : A = U * S * Vᵀ + h • G)
    (hh : 0 ≤ h) (hb : h * ‖G‖ * specNorm S⁻¹ ≤ 1 / 2) :
    IsUnit ((A * V)ᵀ * (A * V)) ∧ specNorm ((A * V).gramPinv) ≤ 2 * specNorm S⁻¹ ∧
      specNorm ((1 - colProj (A * V)) * U) ≤ h * ‖G‖ * specNorm S⁻¹ ∧
      specNorm ((1 - U * Uᵀ) * colProj (A * V)) ≤ 2 * (h * ‖G‖ * specNorm S⁻¹) := by
  have hSd := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hρ0 : 0 ≤ specNorm S⁻¹ := specNorm_nonneg _
  have hGs : specNorm G ≤ ‖G‖ := specNorm_le_frob G
  have hUt := specNorm_transpose_le_one hU
  have hVn := specNorm_le_one_of_orthonormal hV
  have hK : A * V = U * S + h • (G * V) := by
    rw [hA, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc (U * S), hV, Matrix.mul_one]
  have hGV : specNorm (G * V) ≤ ‖G‖ * 1 := specNorm_mul_le_of hGs hVn
  have hCn : specNorm (S⁻¹ * Uᵀ) ≤ specNorm S⁻¹ * 1 := specNorm_mul_le_of le_rfl hUt
  have hCK : (S⁻¹ * Uᵀ) * (A * V) = 1 + h • (S⁻¹ * Uᵀ * (G * V)) := by
    have e : (S⁻¹ * Uᵀ) * (U * S) = 1 := by
      rw [Matrix.mul_assoc, tmul_mul hU, Matrix.nonsing_inv_mul _ hSd]
    rw [hK, Matrix.mul_add, e, Matrix.mul_smul]
  have hEn : specNorm (h • (S⁻¹ * Uᵀ * (G * V))) ≤ 1 / 2 := by
    refine (specNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg hh]
    have h1 := specNorm_mul_le_of hCn hGV
    have h2 := mul_le_mul_of_nonneg_left h1 hh
    refine h2.trans ?_
    have : h * (specNorm S⁻¹ * 1 * (‖G‖ * 1)) = h * ‖G‖ * specNorm S⁻¹ := by ring
    rw [this]; exact hb
  obtain ⟨hKu, hpn⟩ := left_inverse_bound hCK hEn
  have hpn' : specNorm ((A * V).gramPinv) ≤ 2 * specNorm S⁻¹ := by
    refine hpn.trans ?_
    have := mul_le_mul_of_nonneg_left hCn (zero_le_two (α := ℝ))
    simpa using this
  have hcOP := (isOrthProjMat_colProjK hKu).compl
  have hcPK : (1 - colProj (A * V)) * (A * V) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, colProj_mul_self hKu, sub_self]
  refine ⟨hKu, hpn', ?_, ?_⟩
  · have h1 : (1 - colProj (A * V)) * (U * S) = (-h) • ((1 - colProj (A * V)) * (G * V)) := by
      have e : (1 - colProj (A * V)) * (U * S) + h • ((1 - colProj (A * V)) * (G * V)) = 0 := by
        calc _ = (1 - colProj (A * V)) * (U * S + h • (G * V)) := by
              rw [Matrix.mul_add, Matrix.mul_smul]
          _ = (1 - colProj (A * V)) * (A * V) := by rw [← hK]
          _ = 0 := hcPK
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left e
    have e : (1 - colProj (A * V)) * U = (-h) • ((1 - colProj (A * V)) * (G * V) * S⁻¹) := by
      calc (1 - colProj (A * V)) * U = (1 - colProj (A * V)) * (U * S) * S⁻¹ := by
            rw [Matrix.mul_assoc (1 - colProj (A * V)), Matrix.mul_assoc U,
              Matrix.mul_nonsing_inv _ hSd, Matrix.mul_one]
        _ = (-h) • ((1 - colProj (A * V)) * (G * V) * S⁻¹) := by rw [h1, Matrix.smul_mul]
    rw [e]
    refine (specNorm_smul_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hh]
    have h2 := specNorm_mul_le_of (specNorm_mul_le_of hcOP.specNorm_le_one hGV)
      (le_refl (specNorm S⁻¹))
    have h3 := mul_le_mul_of_nonneg_left h2 hh
    refine h3.trans (le_of_eq ?_)
    ring
  · have hcU : (1 - U * Uᵀ) * U = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
    have h1 : (1 - U * Uᵀ) * (A * V) = h • ((1 - U * Uᵀ) * (G * V)) := by
      rw [hK, Matrix.mul_add, ← Matrix.mul_assoc, hcU, Matrix.zero_mul, zero_add, Matrix.mul_smul]
    have e : (1 - U * Uᵀ) * colProj (A * V) = h • ((1 - U * Uᵀ) * (G * V) * (A * V).gramPinv) := by
      rw [colProj, ← Matrix.mul_assoc, h1, Matrix.smul_mul]
    have hPU := isOrthProjMat_mul_transpose hU
    rw [e]
    refine (specNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg hh]
    have h2 := specNorm_mul_le_of (specNorm_mul_le_of hPU.compl.specNorm_le_one hGV) hpn'
    have h3 := mul_le_mul_of_nonneg_left h2 hh
    refine h3.trans (le_of_eq ?_)
    ring


/-- Orthogonal splitting along a projector. -/
lemma norm_sq_proj_add {k : Type*} [Fintype k] {P : Matrix m m ℝ} (hP : IsOrthProjMat P)
    (X Y : Matrix m k ℝ) : ‖P * X + (1 - P) * Y‖ ^ 2 = ‖P * X‖ ^ 2 + ‖(1 - P) * Y‖ ^ 2 := by
  have h0 : ⟪P * X, (1 - P) * Y⟫ = 0 := by
    rw [inner_mul_left, hP.symm, ← Matrix.mul_assoc, Matrix.mul_sub, hP.idem, Matrix.mul_one,
      sub_self, Matrix.zero_mul, inner_zero_right]
  rw [norm_add_sq_real, h0]
  ring

/-- `‖Z‖² = ‖P Z‖² + ‖(1 - P) Z‖²`. -/
lemma norm_sq_eq_proj {k : Type*} [Fintype k] {P : Matrix m m ℝ} (hP : IsOrthProjMat P)
    (Z : Matrix m k ℝ) : ‖Z‖ ^ 2 = ‖P * Z‖ ^ 2 + ‖(1 - P) * Z‖ ^ 2 := by
  rw [← norm_sq_proj_add hP]
  simp [Matrix.sub_mul]

/-- The tangent projector does not increase the Frobenius norm. -/
lemma norm_tanProj_le {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (Z : Matrix m n ℝ) : ‖tanProj P Q Z‖ ≤ ‖Z‖ := by
  have e : tanProj P Q Z = P * Z + (1 - P) * (Z * Q) := by
    simp only [tanProj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  have h1 : ‖(1 - P) * (Z * Q)‖ ≤ ‖(1 - P) * Z‖ := by
    rw [← Matrix.mul_assoc]; exact hQ.norm_mul_le' _
  have h2 := norm_sq_proj_add hP Z (Z * Q)
  have h3 := norm_sq_eq_proj hP Z
  rw [← e] at h2
  have h4 : ‖tanProj P Q Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
    rw [h2, h3]
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

/-- The two off-diagonal blocks of `Z` have total mass at most `‖Z‖²`. -/
lemma blocks_le {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (Z : Matrix m n ℝ) :
    ‖P * Z * (1 - Q)‖ ^ 2 + ‖(1 - P) * Z * Q‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
  rw [norm_sq_eq_proj hP Z]
  have h1 := hQ.compl.norm_mul_le' (P * Z)
  have h2 := hQ.norm_mul_le' ((1 - P) * Z)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

/-- For tangent `Z` the frozen-basis part of the derivative is the projection of `Z` onto the new
tangent space up to a product of two sines. -/
lemma norm_frozen_le {P P₁ : Matrix m m ℝ} {Q Q₁ : Matrix n n ℝ} (hP₁ : IsOrthProjMat P₁)
    (hQ₁ : IsOrthProjMat Q₁) {Z : Matrix m n ℝ} (hZ : (1 - P) * Z * (1 - Q) = 0) {x₁ x₂ x₃ x₄ : ℝ}
    (h₁ : specNorm ((1 - P₁) * P) ≤ x₁) (h₂ : specNorm ((1 - Q) * Q₁) ≤ x₂)
    (h₃ : specNorm (P₁ * (1 - P)) ≤ x₃) (h₄ : specNorm (Q * (1 - Q₁)) ≤ x₄) :
    ‖P₁ * Z * Q₁ + (1 - P₁) * Z * (Q * Q₁) + P₁ * P * Z * (1 - Q₁)‖ ≤
      (1 + x₁ * x₂ + x₃ * x₄) * ‖Z‖ := by
  have hZ1 : Z * (1 - Q) = P * Z * (1 - Q) := by
    have : Z * (1 - Q) = (1 - P) * Z * (1 - Q) + P * Z * (1 - Q) := by
      simp only [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [this, hZ, zero_add]
  have hZ2 : (1 - P) * Z = (1 - P) * Z * Q := by
    have : (1 - P) * Z = (1 - P) * Z * (1 - Q) + (1 - P) * Z * Q := by
      simp only [Matrix.mul_sub, Matrix.mul_one]; abel
    calc (1 - P) * Z = (1 - P) * Z * (1 - Q) + (1 - P) * Z * Q := this
      _ = (1 - P) * Z * Q := by rw [hZ, zero_add]
  have e1 : (1 - P₁) * Z * (Q * Q₁) =
      (1 - P₁) * Z * Q₁ - ((1 - P₁) * P) * Z * ((1 - Q) * Q₁) := by
    have : (1 - P₁) * Z * ((1 - Q) * Q₁) = ((1 - P₁) * P) * Z * ((1 - Q) * Q₁) := by
      calc (1 - P₁) * Z * ((1 - Q) * Q₁) = (1 - P₁) * (Z * (1 - Q)) * Q₁ := by
            simp only [Matrix.mul_assoc]
        _ = ((1 - P₁) * P) * Z * ((1 - Q) * Q₁) := by rw [hZ1]; simp only [Matrix.mul_assoc]
    rw [← this]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  have e2 : P₁ * P * Z * (1 - Q₁) =
      P₁ * Z * (1 - Q₁) - (P₁ * (1 - P)) * Z * (Q * (1 - Q₁)) := by
    have : P₁ * (1 - P) * Z * (1 - Q₁) = (P₁ * (1 - P)) * Z * (Q * (1 - Q₁)) := by
      calc P₁ * (1 - P) * Z * (1 - Q₁) = P₁ * ((1 - P) * Z) * (1 - Q₁) := by
            simp only [Matrix.mul_assoc]
        _ = (P₁ * (1 - P)) * Z * (Q * (1 - Q₁)) := by rw [hZ2]; simp only [Matrix.mul_assoc]
    rw [← this]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have e3 : P₁ * Z * Q₁ + (1 - P₁) * Z * (Q * Q₁) + P₁ * P * Z * (1 - Q₁) =
      tanProj P₁ Q₁ Z - ((1 - P₁) * P) * Z * ((1 - Q) * Q₁) -
        (P₁ * (1 - P)) * Z * (Q * (1 - Q₁)) := by
    rw [e1, e2, tanProj]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [e3]
  have h5 : ‖((1 - P₁) * P) * Z * ((1 - Q) * Q₁)‖ ≤ x₁ * x₂ * ‖Z‖ := by
    calc ‖((1 - P₁) * P) * Z * ((1 - Q) * Q₁)‖
        ≤ ‖((1 - P₁) * P) * Z‖ * specNorm ((1 - Q) * Q₁) := frob_mul_le' _ _
      _ ≤ (specNorm ((1 - P₁) * P) * ‖Z‖) * specNorm ((1 - Q) * Q₁) :=
        mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _)
      _ ≤ (x₁ * ‖Z‖) * x₂ := by
        have := mul_le_mul_of_nonneg_right h₁ (norm_nonneg Z)
        exact mul_le_mul this h₂ (specNorm_nonneg _) ((mul_nonneg (specNorm_nonneg _)
          (norm_nonneg _)).trans this)
      _ = x₁ * x₂ * ‖Z‖ := by ring
  have h6 : ‖(P₁ * (1 - P)) * Z * (Q * (1 - Q₁))‖ ≤ x₃ * x₄ * ‖Z‖ := by
    calc ‖(P₁ * (1 - P)) * Z * (Q * (1 - Q₁))‖
        ≤ ‖(P₁ * (1 - P)) * Z‖ * specNorm (Q * (1 - Q₁)) := frob_mul_le' _ _
      _ ≤ (specNorm (P₁ * (1 - P)) * ‖Z‖) * specNorm (Q * (1 - Q₁)) :=
        mul_le_mul_of_nonneg_right (frob_mul_le _ _) (specNorm_nonneg _)
      _ ≤ (x₃ * ‖Z‖) * x₄ := by
        have := mul_le_mul_of_nonneg_right h₃ (norm_nonneg Z)
        exact mul_le_mul this h₄ (specNorm_nonneg _) ((mul_nonneg (specNorm_nonneg _)
          (norm_nonneg _)).trans this)
      _ = x₃ * x₄ * ‖Z‖ := by ring
  have h7 := norm_tanProj_le hP₁ hQ₁ Z
  have h8 := norm_sub_le (tanProj P₁ Q₁ Z - ((1 - P₁) * P) * Z * ((1 - Q) * Q₁))
    ((P₁ * (1 - P)) * Z * (Q * (1 - Q₁)))
  have h9 := norm_sub_le (tanProj P₁ Q₁ Z) (((1 - P₁) * P) * Z * ((1 - Q) * Q₁))
  linarith [add_mul (1 + x₁ * x₂) (x₃ * x₄) ‖Z‖, add_mul (1 : ℝ) (x₁ * x₂) ‖Z‖, one_mul ‖Z‖]

lemma dProj_transpose (K δ : Matrix m r ℝ) : (dProj K δ)ᵀ = dProj K δ := by
  have hc : (1 - colProj K)ᵀ = 1 - colProj K := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, colProj_transpose]
  rw [dProj, Matrix.transpose_add]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hc, Matrix.mul_assoc]
  rw [add_comm]

/-- `dProj K δ` is off-diagonal with respect to `P`: `δP P + P δP = δP`. -/
lemma dProj_mul_add {K : Matrix m r ℝ} (hK : IsUnit (Kᵀ * K)) (δ : Matrix m r ℝ) :
    dProj K δ * colProj K + colProj K * dProj K δ = dProj K δ := by
  have hP := isOrthProjMat_colProjK hK
  have h1 : K.gramPinv * colProj K = K.gramPinv := pinv_mul_colProj hK
  have h2 : colProj K * (K.gramPinv)ᵀ = (K.gramPinv)ᵀ := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, hP.symm] at this
  have h3 : (1 - colProj K) * colProj K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP.idem, sub_self]
  have h4 : colProj K * (1 - colProj K) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP.idem, sub_self]
  simp only [dProj, Matrix.add_mul, Matrix.mul_add]
  have e1 : (1 - colProj K) * δ * K.gramPinv * colProj K = (1 - colProj K) * δ * K.gramPinv := by
    rw [Matrix.mul_assoc _ (K.gramPinv), h1]
  have e2 : (K.gramPinv)ᵀ * δᵀ * (1 - colProj K) * colProj K = 0 := by
    rw [Matrix.mul_assoc _ (1 - colProj K), h3, Matrix.mul_zero]
  have e3 : colProj K * ((1 - colProj K) * δ * K.gramPinv) = 0 := by
    simp only [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  have e4 : colProj K * ((K.gramPinv)ᵀ * δᵀ * (1 - colProj K)) =
      (K.gramPinv)ᵀ * δᵀ * (1 - colProj K) := by
    simp only [← Matrix.mul_assoc, h2]
  rw [e1, e2, e3, e4]
  abel

/-- `‖δP‖_F ≤ 2 ‖(1 - P) δK‖_F ‖K⁺‖₂`. -/
lemma norm_dProj_le {K δ : Matrix m r ℝ} {κ : ℝ} (hκ : specNorm (K.gramPinv) ≤ κ) :
    ‖dProj K δ‖ ≤ 2 * ‖(1 - colProj K) * δ‖ * κ := by
  have hc : (1 - colProj K)ᵀ = 1 - colProj K := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, colProj_transpose]
  have e : (K.gramPinv)ᵀ * δᵀ * (1 - colProj K) = ((1 - colProj K) * δ * K.gramPinv)ᵀ := by
    simp only [Matrix.transpose_mul, hc, Matrix.mul_assoc]
  have h1 : ‖(1 - colProj K) * δ * K.gramPinv‖ ≤ ‖(1 - colProj K) * δ‖ * κ :=
    (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left hκ (norm_nonneg _))
  rw [dProj, e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_transpose]
  linarith

/-- **The K-side estimate.**  `δP A Q₁` equals its frozen part `(1 - P₁) δK Vᵀ Q₁` up to a term
quadratic in the sine between the old and the new row spaces. -/
lemma dProj_mul_A_sub_le {K : Matrix m r ℝ} {A G : Matrix m n ℝ} {V : Matrix n r ℝ}
    {Q₁ : Matrix n n ℝ} {h c κ g : ℝ} (hKdef : K = A * V) (hKu : IsUnit (Kᵀ * K))
    (hc : specNorm ((1 - V * Vᵀ) * Q₁) ≤ c)
    (hAQ : A * (1 - V * Vᵀ) = h • (G * (1 - V * Vᵀ))) (hκ : specNorm (K.gramPinv) ≤ κ)
    (hg : specNorm G ≤ g) (hh : 0 ≤ h) (hc' : h * g * κ ≤ c) (δ : Matrix m r ℝ) :
    ‖dProj K δ * A * Q₁ - (1 - colProj K) * δ * (Vᵀ * Q₁)‖ ≤
      2 * c ^ 2 * ‖(1 - colProj K) * δ‖ := by
  have hP := isOrthProjMat_colProjK hKu
  have hc0 : 0 ≤ c := (specNorm_nonneg _).trans hc
  have hκ0 : 0 ≤ κ := (specNorm_nonneg _).trans hκ
  have hg0 : 0 ≤ g := (specNorm_nonneg _).trans hg
  set P₁ := colProj K with hP₁
  set Kp := K.gramPinv with hKp
  set α := (1 - P₁) * δ with hα
  set Q := V * Vᵀ with hQ
  have hct : (1 - P₁)ᵀ = 1 - P₁ := hP.compl.symm
  have hαt : αᵀ = δᵀ * (1 - P₁) := by rw [hα, Matrix.transpose_mul, hct]
  have hαc : αᵀ * (1 - P₁) = αᵀ := by rw [hαt, Matrix.mul_assoc, hP.compl.idem]
  have hdP : dProj K δ = α * Kp + Kpᵀ * αᵀ := by
    rw [dProj, ← hP₁, ← hKp, hαt, Matrix.mul_assoc Kpᵀ]
  have hKV : Kp * (A * V) = 1 := by rw [← hKdef]; exact pinv_mul_self hKu
  have hcK : (1 - P₁) * (A * V) = 0 := by
    rw [← hKdef, Matrix.sub_mul, Matrix.one_mul, hP₁, colProj_mul_self hKu, sub_self]
  have hsplit : A = A * (1 - Q) + A * V * Vᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQ, Matrix.mul_assoc]; abel
  have ha : Kp * A * Q₁ = Vᵀ * Q₁ + h • (Kp * G * ((1 - Q) * Q₁)) := by
    have : Kp * A = h • (Kp * G * (1 - Q)) + Vᵀ := by
      conv_lhs => rw [hsplit]
      rw [Matrix.mul_add, hAQ, Matrix.mul_smul, ← Matrix.mul_assoc Kp G,
        ← Matrix.mul_assoc Kp (A * V), hKV, Matrix.one_mul]
    rw [this, Matrix.add_mul, Matrix.smul_mul, add_comm]
    simp only [Matrix.mul_assoc]
  have hb : αᵀ * A * Q₁ = h • (αᵀ * G * ((1 - Q) * Q₁)) := by
    have : αᵀ * A = h • (αᵀ * G * (1 - Q)) := by
      have e1 : (1 - P₁) * A = h • ((1 - P₁) * G * (1 - Q)) := by
        conv_lhs => rw [hsplit]
        rw [Matrix.mul_add (1 - P₁), hAQ, ← Matrix.mul_assoc (1 - P₁) (A * V), hcK,
          Matrix.zero_mul, add_zero, Matrix.mul_smul, Matrix.mul_assoc]
      calc αᵀ * A = (αᵀ * (1 - P₁)) * A := by rw [hαc]
        _ = αᵀ * ((1 - P₁) * A) := Matrix.mul_assoc _ _ _
        _ = h • ((αᵀ * (1 - P₁)) * G * (1 - Q)) := by
          rw [e1, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
        _ = h • (αᵀ * G * (1 - Q)) := by rw [hαc]
    rw [this, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have e : dProj K δ * A * Q₁ - α * (Vᵀ * Q₁) =
      α * (h • (Kp * G * ((1 - Q) * Q₁))) + Kpᵀ * (h • (αᵀ * G * ((1 - Q) * Q₁))) := by
    rw [hdP, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc α, Matrix.mul_assoc α, ha,
      Matrix.mul_assoc Kpᵀ, Matrix.mul_assoc Kpᵀ, hb, Matrix.mul_add]
    abel
  rw [e]
  have hGR : specNorm (G * ((1 - Q) * Q₁)) ≤ g * c := specNorm_mul_le_of hg hc
  have hsc : h * (κ * (g * c)) ≤ c * c := by
    have := mul_le_mul_of_nonneg_right hc' hc0
    calc h * (κ * (g * c)) = h * g * κ * c := by ring
      _ ≤ c * c := this
  have hX1 : ‖α * (h • (Kp * G * ((1 - Q) * Q₁)))‖ ≤ c ^ 2 * ‖α‖ := by
    refine (frob_mul_le' _ _).trans ?_
    have h1 : specNorm (Kp * G * ((1 - Q) * Q₁)) ≤ κ * (g * c) := by
      rw [Matrix.mul_assoc]; exact specNorm_mul_le_of hκ hGR
    have h2 : specNorm (h • (Kp * G * ((1 - Q) * Q₁))) ≤ c * c := by
      refine (specNorm_smul_le _ _).trans ?_
      rw [abs_of_nonneg hh]
      exact (mul_le_mul_of_nonneg_left h1 hh).trans hsc
    calc ‖α‖ * specNorm (h • (Kp * G * ((1 - Q) * Q₁))) ≤ ‖α‖ * (c * c) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = c ^ 2 * ‖α‖ := by ring
  have hX2 : ‖Kpᵀ * (h • (αᵀ * G * ((1 - Q) * Q₁)))‖ ≤ c ^ 2 * ‖α‖ := by
    refine (frob_mul_le _ _).trans ?_
    rw [specNorm_transpose, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have h1 : ‖αᵀ * G * ((1 - Q) * Q₁)‖ ≤ ‖α‖ * (g * c) := by
      rw [Matrix.mul_assoc]
      refine (frob_mul_le' _ _).trans ?_
      rw [norm_transpose]
      exact mul_le_mul_of_nonneg_left hGR (norm_nonneg _)
    calc specNorm Kp * (h * ‖αᵀ * G * ((1 - Q) * Q₁)‖) ≤ κ * (h * (‖α‖ * (g * c))) := by
          refine mul_le_mul hκ (mul_le_mul_of_nonneg_left h1 hh) ?_ hκ0
          exact mul_nonneg hh (norm_nonneg _)
      _ = (h * (κ * (g * c))) * ‖α‖ := by ring
      _ ≤ (c * c) * ‖α‖ := mul_le_mul_of_nonneg_right hsc (norm_nonneg _)
      _ = c ^ 2 * ‖α‖ := by ring
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The residual `R₁ = (1 - P₁) A`: it lives on the complement of the old row space and its size is
the normal part of the field, up to a term of second order. -/
lemma residual_facts {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ} {G A : Matrix m n ℝ}
    {h x : ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hA : A = U * S * Vᵀ + h • G) (hh : 0 ≤ h)
    (hKu : IsUnit ((A * V)ᵀ * (A * V)))
    (hx : specNorm ((1 - colProj (A * V)) * U) ≤ x) :
    (1 - colProj (A * V)) * A * (1 - V * Vᵀ) = (1 - colProj (A * V)) * A ∧
      (1 - colProj (A * V)) * A = h • ((1 - colProj (A * V)) * G * (1 - V * Vᵀ)) ∧
      specNorm ((1 - colProj (A * V)) * A) ≤
        h * (specNorm ((1 - U * Uᵀ) * G * (1 - V * Vᵀ)) + x * ‖G‖) ∧
      specNorm ((1 - colProj (A * V)) * A) ≤ h * ‖G‖ := by
  have hP := isOrthProjMat_colProjK hKu
  have hQ := isOrthProjMat_mul_transpose hV
  have hPu := isOrthProjMat_mul_transpose hU
  have hGs : specNorm G ≤ ‖G‖ := specNorm_le_frob G
  have hUt := specNorm_transpose_le_one hU
  set P₁ := colProj (A * V) with hP₁
  set Q := V * Vᵀ with hQdef
  set P := U * Uᵀ with hPdef
  have hcK : (1 - P₁) * (A * V) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP₁, colProj_mul_self hKu, sub_self]
  have e1 : (1 - P₁) * A * (1 - Q) = (1 - P₁) * A := by
    have : (1 - P₁) * A * Q = 0 := by
      calc (1 - P₁) * A * Q = (1 - P₁) * (A * V) * Vᵀ := by simp only [hQdef, Matrix.mul_assoc]
        _ = 0 := by rw [hcK, Matrix.zero_mul]
    rw [Matrix.mul_sub, this, Matrix.mul_one, sub_zero]
  have hYQ : U * S * Vᵀ * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQdef, Matrix.mul_assoc (U * S), ← Matrix.mul_assoc Vᵀ, hV,
      Matrix.one_mul, sub_self]
  have hYQ' : U * (S * (Vᵀ * (1 - Q))) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]; exact hYQ
  have e2 : (1 - P₁) * A = h • ((1 - P₁) * G * (1 - Q)) := by
    rw [← e1]
    conv_lhs => rw [hA]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hYQ', Matrix.mul_zero, zero_add,
      Matrix.mul_smul, Matrix.smul_mul]
  have e3 : (1 - P₁) * G * (1 - Q) =
      (1 - P₁) * ((1 - P) * G * (1 - Q)) + ((1 - P₁) * U) * (Uᵀ * G * (1 - Q)) := by
    simp only [hPdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
    abel
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e2]
    refine (specNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    rw [e3]
    refine (specNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · simpa using specNorm_mul_le_of hP.compl.specNorm_le_one
        (le_refl (specNorm ((1 - P) * G * (1 - Q))))
    · have h1 : specNorm (Uᵀ * G * (1 - Q)) ≤ 1 * ‖G‖ * 1 :=
        specNorm_mul_le_of (specNorm_mul_le_of hUt hGs) hQ.compl.specNorm_le_one
      have := specNorm_mul_le_of hx h1
      simpa using this
  · rw [e2]
    refine (specNorm_smul_le _ _).trans ?_
    rw [abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    have := specNorm_mul_le_of (specNorm_mul_le_of hP.compl.specNorm_le_one hGs)
      hQ.compl.specNorm_le_one
    simpa using this


/-- All estimates for one side of the step. -/
lemma side_tangent {A G Y : Matrix m n ℝ} {V : Matrix n r ℝ} {Q₁ : Matrix n n ℝ} {h c ρ g : ℝ}
    (hKu : IsUnit ((A * V)ᵀ * (A * V))) (hV : Vᵀ * V = 1) (hQ₁ : IsOrthProjMat Q₁)
    (hc : specNorm ((1 - V * Vᵀ) * Q₁) ≤ c) (hAY : A = Y + h • G)
    (hYQ : Y * (1 - V * Vᵀ) = 0) (hκ : specNorm ((A * V).gramPinv) ≤ 2 * ρ) (hg : ‖G‖ ≤ g)
    (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hc' : 2 * (h * g * ρ) ≤ c) (hc1 : c ≤ 1)
    (dA : Matrix m n ℝ) (dV : Matrix n r ℝ) :
    ‖dProj (A * V) (dA * V + A * dV) * A * Q₁ -
        ((1 - colProj (A * V)) * dA * (V * Vᵀ * Q₁) +
          (1 - colProj (A * V)) * A * dV * (Vᵀ * Q₁))‖ ≤
        2 * c ^ 2 * ‖(1 - colProj (A * V)) * (dA * V + A * dV)‖ ∧
      ‖dProj (A * V) (dA * V + A * dV) * Y * Q₁‖ ≤
        5 * ‖(1 - colProj (A * V)) * (dA * V + A * dV)‖ ∧
      ‖dProj (A * V) (dA * V + A * dV)‖ ≤
        4 * ρ * ‖(1 - colProj (A * V)) * (dA * V + A * dV)‖ := by
  set K := A * V with hK
  set δ := dA * V + A * dV with hδ
  set a := ‖(1 - colProj K) * δ‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hc0 : 0 ≤ c := (specNorm_nonneg _).trans hc
  have hg0 : 0 ≤ g := (norm_nonneg G).trans hg
  have hgs : specNorm G ≤ g := (specNorm_le_frob G).trans hg
  have hAQ : A * (1 - V * Vᵀ) = h • (G * (1 - V * Vᵀ)) := by
    rw [hAY, Matrix.add_mul, hYQ, zero_add, Matrix.smul_mul]
  have hsc : h * g * (2 * ρ) ≤ c := by nlinarith
  have hmain := dProj_mul_A_sub_le hK hKu hc hAQ hκ hgs hh hsc δ
  have hsplit : (1 - colProj K) * δ * (Vᵀ * Q₁) =
      (1 - colProj K) * dA * (V * Vᵀ * Q₁) + (1 - colProj K) * A * dV * (Vᵀ * Q₁) := by
    rw [hδ, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  have hdP : ‖dProj K δ‖ ≤ 4 * ρ * a := by
    have := norm_dProj_le (δ := δ) hκ
    calc ‖dProj K δ‖ ≤ 2 * a * (2 * ρ) := this
      _ = 4 * ρ * a := by ring
  refine ⟨?_, ?_, hdP⟩
  · rw [← hsplit]; exact hmain
  · have hP1 : ‖(1 - colProj K) * δ * (Vᵀ * Q₁)‖ ≤ a := by
      have hVt : specNorm (Vᵀ * Q₁) ≤ 1 * 1 :=
        specNorm_mul_le_of (specNorm_transpose_le_one hV) hQ₁.specNorm_le_one
      calc ‖(1 - colProj K) * δ * (Vᵀ * Q₁)‖ ≤ a * specNorm (Vᵀ * Q₁) := frob_mul_le' _ _
        _ ≤ a * (1 * 1) := mul_le_mul_of_nonneg_left hVt ha0
        _ = a := by ring
    have hA1 : ‖dProj K δ * A * Q₁‖ ≤ a + 2 * c ^ 2 * a := by
      have := norm_add_le (dProj K δ * A * Q₁ - (1 - colProj K) * δ * (Vᵀ * Q₁))
        ((1 - colProj K) * δ * (Vᵀ * Q₁))
      rw [sub_add_cancel] at this
      linarith
    have hG1 : ‖dProj K δ * G * Q₁‖ ≤ 4 * ρ * a * g := by
      calc ‖dProj K δ * G * Q₁‖ ≤ ‖dProj K δ * G‖ := hQ₁.norm_mul_le' _
        _ ≤ ‖dProj K δ‖ * specNorm G := frob_mul_le' _ _
        _ ≤ 4 * ρ * a * g := mul_le_mul hdP hgs (specNorm_nonneg _) (by positivity)
    have hY : dProj K δ * Y * Q₁ = dProj K δ * A * Q₁ - h • (dProj K δ * G * Q₁) := by
      rw [hAY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]; abel
    rw [hY]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have h1 : h * ‖dProj K δ * G * Q₁‖ ≤ 2 * c * a := by
      calc h * ‖dProj K δ * G * Q₁‖ ≤ h * (4 * ρ * a * g) := mul_le_mul_of_nonneg_left hG1 hh
        _ = 2 * (2 * (h * g * ρ)) * a := by ring
        _ ≤ 2 * c * a := by gcongr
    nlinarith [mul_nonneg hc0 ha0, mul_nonneg (mul_nonneg hc0 hc0) ha0,
      mul_le_mul_of_nonneg_right hc1 ha0,
      mul_le_mul_of_nonneg_right (mul_le_mul hc1 hc1 hc0 zero_le_one) ha0]

/-- The algebraic rearrangement of the tangent-linear model. -/
lemma tangent_rearrange {P₁ dP : Matrix m m ℝ} {Q₁ dQ : Matrix n n ℝ}
    {Y Z G G' dY' Jd A : Matrix m n ℝ} {h : ℝ} (hP : P₁ * P₁ = P₁) (hQ : Q₁ * Q₁ = Q₁)
    (hdP : dP * P₁ + P₁ * dP = dP) (hdQ : dQ * Q₁ + Q₁ * dQ = dQ) (hA : A = Y + h • G)
    (hd : dY' = dP * Y * Q₁ + P₁ * Z * Q₁ + P₁ * Y * dQ) :
    dP * (P₁ * Y * Q₁ + h • G') * Q₁ + P₁ * (dY' + h • Jd) * Q₁ +
        P₁ * (P₁ * Y * Q₁ + h • G') * dQ =
      dP * A * Q₁ + P₁ * A * dQ + P₁ * Z * Q₁ + h • (P₁ * Jd * Q₁) + h • (dP * (G' - G) * Q₁) +
        h • (P₁ * (G' - G) * dQ) := by
  have e1 : dP * (P₁ * Y * Q₁) * Q₁ + P₁ * (dP * Y * Q₁) * Q₁ = dP * Y * Q₁ := by
    calc _ = (dP * P₁ + P₁ * dP) * Y * (Q₁ * Q₁) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = dP * Y * Q₁ := by rw [hdP, hQ]
  have e2 : P₁ * (P₁ * Y * dQ) * Q₁ + P₁ * (P₁ * Y * Q₁) * dQ = P₁ * Y * dQ := by
    calc _ = (P₁ * P₁) * Y * (dQ * Q₁ + Q₁ * dQ) := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = P₁ * Y * dQ := by rw [hdQ, hP]
  have e3 : P₁ * (P₁ * Z * Q₁) * Q₁ = P₁ * Z * Q₁ := by
    calc _ = (P₁ * P₁) * Z * (Q₁ * Q₁) := by simp only [Matrix.mul_assoc]
      _ = P₁ * Z * Q₁ := by rw [hP, hQ]
  have e4 : dP * (P₁ * Y * Q₁ + h • G') * Q₁ + P₁ * (dY' + h • Jd) * Q₁ +
        P₁ * (P₁ * Y * Q₁ + h • G') * dQ =
      (dP * (P₁ * Y * Q₁) * Q₁ + P₁ * (dP * Y * Q₁) * Q₁) + P₁ * (P₁ * Z * Q₁) * Q₁ +
        (P₁ * (P₁ * Y * dQ) * Q₁ + P₁ * (P₁ * Y * Q₁) * dQ) + h • (dP * G' * Q₁) +
        h • (P₁ * Jd * Q₁) + h • (P₁ * G' * dQ) := by
    rw [hd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [e4, e1, e2, e3, hA]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub]
  abel


/-- The off-diagonal blocks of `Z` control the moves of the bases. -/
lemma norm_mul_basis_le {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) {R : Matrix n n ℝ}
    (Z : Matrix m n ℝ) (T : Matrix r r ℝ) :
    ‖R * Zᵀ * U * T‖ ≤ ‖U * Uᵀ * Z * Rᵀ‖ * specNorm T := by
  refine (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (specNorm_nonneg _))
  calc ‖R * Zᵀ * U‖ = ‖(R * Zᵀ * U)ᵀ‖ := (norm_transpose _).symm
    _ = ‖U * (R * Zᵀ * U)ᵀ‖ := (norm_mul_of_orthonormal hU _).symm
    _ = ‖U * Uᵀ * Z * Rᵀ‖ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- `‖(1 - P₁) Y‖_F ≤ h ‖G‖_F`: the old matrix is almost in the new column space. -/
lemma norm_compl_Y_le {A G Y : Matrix m n ℝ} {V : Matrix n r ℝ} {h : ℝ}
    (hKu : IsUnit ((A * V)ᵀ * (A * V))) (hV : Vᵀ * V = 1) (hAY : A = Y + h • G)
    (hYQ : Y * (1 - V * Vᵀ) = 0) (hh : 0 ≤ h) : ‖(1 - colProj (A * V)) * Y‖ ≤ h * ‖G‖ := by
  have hP := isOrthProjMat_colProjK hKu
  have hQ := isOrthProjMat_mul_transpose hV
  have hY : Y = Y * (V * Vᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hYQ
    exact sub_eq_zero.1 hYQ
  have h0 : (1 - colProj (A * V)) * A * (V * Vᵀ) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 - colProj (A * V)), Matrix.sub_mul,
      Matrix.one_mul, colProj_mul_self hKu, sub_self, Matrix.zero_mul]
  have e : (1 - colProj (A * V)) * Y = (-h) • ((1 - colProj (A * V)) * G * (V * Vᵀ)) := by
    have key : ∀ P₁ : Matrix m m ℝ, (1 - P₁) * A * (V * Vᵀ) =
        (1 - P₁) * Y * (V * Vᵀ) + h • ((1 - P₁) * G * (V * Vᵀ)) := fun P₁ => by
      rw [hAY]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have h1 := key (colProj (A * V))
    have h2 : (1 - colProj (A * V)) * Y * (V * Vᵀ) = (1 - colProj (A * V)) * Y := by
      rw [Matrix.mul_assoc, ← hY]
    rw [h2, h0] at h1
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h1.symm
  rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh]
  refine mul_le_mul_of_nonneg_left ?_ hh
  exact (hQ.norm_mul_le' _).trans (hP.compl.norm_mul_le _)

/-- The real-number bookkeeping of `tangent_core`. -/
lemma core_arith {z a₀ b l al be m1 m2 w x1 x2 y1 y2 y3 : ℝ} (hz : 0 ≤ z)
    (hb : b ≤ 1 / 2) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hal0 : 0 ≤ al) (hbe0 : 0 ≤ be)
    (hal : al ≤ (1 + l + b) * z) (hbe : be ≤ (1 + l + b) * z)
    (hm1 : m1 ≤ (1 + b * (2 * b) + 2 * b * b) * z) (hm2 : m2 ≤ 2 * (l * z))
    (hw : w ≤ (a₀ + b ^ 2) * z) (hx1 : x1 ≤ 2 * (2 * b) ^ 2 * al)
    (hx2 : x2 ≤ 2 * (2 * b) ^ 2 * be) (hy1 : y1 ≤ l * (z + 5 * al + 5 * be))
    (hy2 : y2 ≤ 8 * l * b * al) (hy3 : y3 ≤ 8 * l * b * be) :
    m1 + m2 + w + x1 + x2 + y1 + y2 + y3 ≤ (1 + a₀ + 45 * b ^ 2 + 48 * l) * z := by
  have hs : al + be ≤ 5 * z := by nlinarith
  have hs0 : 0 ≤ al + be := by linarith
  have t1 : 8 * b ^ 2 * (al + be) ≤ 8 * b ^ 2 * (5 * z) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have t2 : l * (al + be) ≤ l * (5 * z) := mul_le_mul_of_nonneg_left hs hl0
  have t3 : l * b * (al + be) ≤ l * (1 / 2) * (5 * z) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hb hl0) hs hs0 (by positivity)
  have e1 : 2 * (2 * b) ^ 2 * al + 2 * (2 * b) ^ 2 * be = 8 * b ^ 2 * (al + be) := by ring
  have e2 : l * (z + 5 * al + 5 * be) = l * z + 5 * (l * (al + be)) := by ring
  have e3 : 8 * l * b * al + 8 * l * b * be = 8 * (l * b * (al + be)) := by ring
  have e4 : (1 + b * (2 * b) + 2 * b * b) * z = z + 4 * b ^ 2 * z := by ring
  have e5 : (a₀ + b ^ 2) * z = a₀ * z + b ^ 2 * z := by ring
  have e6 : (1 + a₀ + 45 * b ^ 2 + 48 * l) * z =
      z + a₀ * z + 45 * b ^ 2 * z + 48 * (l * z) := by ring
  have e7 : 8 * b ^ 2 * (5 * z) = 40 * b ^ 2 * z := by ring
  have e8 : l * (1 / 2) * (5 * z) = 5 / 2 * (l * z) := by ring
  have e9 : l * (5 * z) = 5 * (l * z) := by ring
  rw [e6]
  rw [e4] at hm1
  rw [e5] at hw
  rw [e2] at hy1
  rw [e7] at t1
  rw [e8] at t3
  rw [e9] at t2
  linarith

/-- The residual estimates of one side of the step. -/
lemma side_bundle {A dA : Matrix m n ℝ} {V dV : Matrix n r ℝ} {Q₁ : Matrix n n ℝ}
    {x y s t : ℝ} (hV : Vᵀ * V = 1) (hPc : IsOrthProjMat (colProj (A * V)))
    (hQ₁ : IsOrthProjMat Q₁)
    (r1 : (1 - colProj (A * V)) * A * (1 - V * Vᵀ) = (1 - colProj (A * V)) * A)
    (r3 : specNorm ((1 - colProj (A * V)) * A) ≤ x)
    (r4 : specNorm ((1 - colProj (A * V)) * A) ≤ y)
    (hv : ‖(1 - V * Vᵀ) * dV‖ ≤ s) (hdA : ‖dA‖ ≤ t) :
    ‖(1 - colProj (A * V)) * (dA * V + A * dV)‖ ≤ t + y * s ∧
      ‖(1 - colProj (A * V)) * A * dV * (Vᵀ * Q₁)‖ ≤ x * s := by
  have hVn := specNorm_le_one_of_orthonormal hV
  have hVt := specNorm_transpose_le_one hV
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hv
  have hy0 : 0 ≤ y := (specNorm_nonneg _).trans r4
  have hx0 : 0 ≤ x := (specNorm_nonneg _).trans r3
  have hR : (1 - colProj (A * V)) * A * dV =
      ((1 - colProj (A * V)) * A) * ((1 - V * Vᵀ) * dV) := by
    rw [← Matrix.mul_assoc ((1 - colProj (A * V)) * A), r1]
  constructor
  · have e : (1 - colProj (A * V)) * (dA * V + A * dV) =
        (1 - colProj (A * V)) * dA * V + ((1 - colProj (A * V)) * A) * ((1 - V * Vᵀ) * dV) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc (1 - colProj (A * V)) dA,
        ← Matrix.mul_assoc (1 - colProj (A * V)) A, hR]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(1 - colProj (A * V)) * dA * V‖
          ≤ ‖(1 - colProj (A * V)) * dA‖ * specNorm V := frob_mul_le' _ _
        _ ≤ ‖dA‖ * 1 := mul_le_mul (hPc.compl.norm_mul_le _) hVn (specNorm_nonneg _)
          (norm_nonneg _)
        _ ≤ t := by rw [mul_one]; exact hdA
    · exact (frob_mul_le _ _).trans (mul_le_mul r4 hv (norm_nonneg _) hy0)
  · rw [hR]
    have hVQ : specNorm (Vᵀ * Q₁) ≤ 1 * 1 := specNorm_mul_le_of hVt hQ₁.specNorm_le_one
    calc ‖((1 - colProj (A * V)) * A) * ((1 - V * Vᵀ) * dV) * (Vᵀ * Q₁)‖
        ≤ ‖((1 - colProj (A * V)) * A) * ((1 - V * Vᵀ) * dV)‖ * specNorm (Vᵀ * Q₁) :=
          frob_mul_le' _ _
      _ ≤ (x * s) * (1 * 1) := mul_le_mul ((frob_mul_le _ _).trans
          (mul_le_mul r3 hv (norm_nonneg _) hx0)) hVQ (specNorm_nonneg _) (by positivity)
      _ = x * s := by ring

/-- Two pieces living on complementary ranges, with block masses `a₁`, `a₂`. -/
lemma norm_wein_le {P₁ : Matrix m m ℝ} (hP₁ : IsOrthProjMat P₁) {X X' : Matrix m n ℝ}
    {x ρ a₁ a₂ z : ℝ} (hx : 0 ≤ x) (hρ : 0 ≤ ρ) (hz : 0 ≤ z) (h1 : ‖P₁ * X‖ ≤ x * (a₂ * ρ))
    (h2 : ‖(1 - P₁) * X'‖ ≤ x * (a₁ * ρ)) (hbl : a₁ ^ 2 + a₂ ^ 2 ≤ z ^ 2) :
    ‖P₁ * X + (1 - P₁) * X'‖ ≤ x * ρ * z := by
  have hc : 0 ≤ x * ρ := mul_nonneg hx hρ
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_sq_proj_add hP₁]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h5 : (x * (a₂ * ρ)) ^ 2 + (x * (a₁ * ρ)) ^ 2 ≤ (x * ρ * z) ^ 2 := by
    have e : (x * (a₂ * ρ)) ^ 2 + (x * (a₁ * ρ)) ^ 2 = (x * ρ) ^ 2 * (a₁ ^ 2 + a₂ ^ 2) := by ring
    have e2 : (x * ρ * z) ^ 2 = (x * ρ) ^ 2 * z ^ 2 := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hbl (by positivity)
  linarith

lemma norm_add8_le {E : Type*} [NormedAddCommGroup E] (a b c d e f g k : E) :
    ‖a + b + c + d + e + f + g + k‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖k‖ := by
  have h1 := norm_add_le (a + b + c + d + e + f + g) k
  have h2 := norm_add_le (a + b + c + d + e + f) g
  have h3 := norm_add_le (a + b + c + d + e) f
  have h4 := norm_add_le (a + b + c + d) e
  have h5 := norm_add_le (a + b + c) d
  have h6 := norm_add_le (a + b) c
  have h7 := norm_add_le a b
  linarith

/-- The assembly of `tangent_core`, with all projectors abstract. -/
lemma tangent_assembly {P₁ dP : Matrix m m ℝ} {Q₁ dQ : Matrix n n ℝ} {U : Matrix m r ℝ}
    {V : Matrix n r ℝ} {Y G G' A Z E Jd dY' : Matrix m n ℝ} {dU : Matrix m r ℝ}
    {dV : Matrix n r ℝ} {h L ρ g ε a₁ a₂ al be z : ℝ}
    (hP₁ : IsOrthProjMat P₁) (hQ₁ : IsOrthProjMat Q₁) (hA : A = Y + h • G)
    (hdPm : dP * P₁ + P₁ * dP = dP) (hdQm : dQ * Q₁ + Q₁ * dQ = dQ)
    (hdQs : dQᵀ = dQ)
    (hdY : dY' = dP * Y * Q₁ + P₁ * Z * Q₁ + P₁ * Y * dQ) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hhL : h * L ≤ 1) (hρ : 0 ≤ ρ) (hg : 0 ≤ g) (hε : 0 ≤ ε) (hb : h * g * ρ ≤ 1 / 2)
    (hz0 : 0 ≤ z) (hzZ : ‖Z‖ = z)
    (hbl : a₁ ^ 2 + a₂ ^ 2 ≤ z ^ 2) (hE : ‖E‖ ≤ h * L * z)
    (hfro : ‖P₁ * Z * Q₁ + (1 - P₁) * Z * (V * Vᵀ * Q₁) + P₁ * (U * Uᵀ) * Z * (1 - Q₁)‖ ≤
      (1 + h * g * ρ * (2 * (h * g * ρ)) + 2 * (h * g * ρ) * (h * g * ρ)) * z)
    (hal : al = ‖(1 - P₁) * ((Z + E) * V + A * dV)‖)
    (hbe : be = ‖(1 - Q₁) * ((Z + E)ᵀ * U + Aᵀ * dU)‖)
    (hal' : al ≤ (1 + h * L + h * g * ρ) * z) (hbe' : be ≤ (1 + h * L + h * g * ρ) * z)
    (k1 : ‖dP * A * Q₁ - ((1 - P₁) * (Z + E) * (V * Vᵀ * Q₁) +
        (1 - P₁) * A * dV * (Vᵀ * Q₁))‖ ≤ 2 * (2 * (h * g * ρ)) ^ 2 * al)
    (k2 : ‖(1 - P₁) * A * dV * (Vᵀ * Q₁)‖ ≤ h * (ε + h * g * ρ * g) * (a₁ * ρ))
    (k3 : ‖dP * Y * Q₁‖ ≤ 5 * al) (k4 : ‖dP‖ ≤ 4 * ρ * al)
    (l1 : ‖dQ * Aᵀ * P₁ - ((1 - Q₁) * (Z + E)ᵀ * (U * Uᵀ * P₁) +
        (1 - Q₁) * Aᵀ * dU * (Uᵀ * P₁))‖ ≤ 2 * (2 * (h * g * ρ)) ^ 2 * be)
    (l2 : ‖(1 - Q₁) * Aᵀ * dU * (Uᵀ * P₁)‖ ≤ h * (ε + h * g * ρ * g) * (a₂ * ρ))
    (l3 : ‖dQ * Yᵀ * P₁‖ ≤ 5 * be) (l4 : ‖dQ‖ ≤ 4 * ρ * be)
    (hJd : ‖Jd‖ ≤ L * ‖dY'‖) (hG' : ‖G' - G‖ ≤ L * (2 * (h * g)))
    (hV' : specNorm (V * Vᵀ * Q₁) ≤ 1) (hU' : specNorm (P₁ * (U * Uᵀ)) ≤ 1) :
    ‖dP * (P₁ * Y * Q₁ + h • G') * Q₁ + P₁ * (dY' + h • Jd) * Q₁ +
        P₁ * (P₁ * Y * Q₁ + h • G') * dQ‖ ≤
      (1 + h * ε * ρ + 45 * (h * g * ρ) ^ 2 + 48 * (h * L)) * z := by
  have hal0 : 0 ≤ al := by rw [hal]; exact norm_nonneg _
  have hbe0 : 0 ≤ be := by rw [hbe]; exact norm_nonneg _
  rw [tangent_rearrange (Z := Z) (G := G) (G' := G') (Jd := Jd) (dY' := dY') hP₁.idem hQ₁.idem
    hdPm hdQm hA hdY]
  have hc : (1 - Q₁)ᵀ = 1 - Q₁ := hQ₁.compl.symm
  have hPt : P₁ᵀ = P₁ := hP₁.symm
  have e3 : ((1 - Q₁) * Aᵀ * dU * (Uᵀ * P₁))ᵀ = P₁ * (U * (dUᵀ * (A * (1 - Q₁)))) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hc, hPt, Matrix.mul_assoc]
  have hYt : (dQ * Yᵀ * P₁)ᵀ = P₁ * Y * dQ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hdQs, hPt, Matrix.mul_assoc]
  have htr : P₁ * A * dQ =
      (dQ * Aᵀ * P₁ - ((1 - Q₁) * (Z + E)ᵀ * (U * Uᵀ * P₁) +
        (1 - Q₁) * Aᵀ * dU * (Uᵀ * P₁)))ᵀ +
      P₁ * (U * Uᵀ) * (Z + E) * (1 - Q₁) + P₁ * (U * (dUᵀ * (A * (1 - Q₁)))) := by
    have e1 : (dQ * Aᵀ * P₁)ᵀ = P₁ * A * dQ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hdQs, hPt, Matrix.mul_assoc]
    have e2 : ((1 - Q₁) * (Z + E)ᵀ * (U * Uᵀ * P₁))ᵀ = P₁ * (U * Uᵀ) * (Z + E) * (1 - Q₁) := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hc, hPt, Matrix.mul_assoc]
    rw [Matrix.transpose_sub, Matrix.transpose_add, e1, e2, e3]
    abel
  have hE1 : (1 - P₁) * (Z + E) * (V * Vᵀ * Q₁) =
      (1 - P₁) * Z * (V * Vᵀ * Q₁) + (1 - P₁) * E * (V * Vᵀ * Q₁) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have hE2 : P₁ * (U * Uᵀ) * (Z + E) * (1 - Q₁) =
      P₁ * (U * Uᵀ) * Z * (1 - Q₁) + P₁ * (U * Uᵀ) * E * (1 - Q₁) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  set W₁ := (1 - P₁) * A * dV * (Vᵀ * Q₁) with hW₁
  set X₁ := dP * A * Q₁ - ((1 - P₁) * (Z + E) * (V * Vᵀ * Q₁) + W₁) with hX₁
  set X₂ := (dQ * Aᵀ * P₁ - ((1 - Q₁) * (Z + E)ᵀ * (U * Uᵀ * P₁) +
    (1 - Q₁) * Aᵀ * dU * (Uᵀ * P₁)))ᵀ with hX₂
  set W₂ := P₁ * (U * (dUᵀ * (A * (1 - Q₁)))) with hW₂
  set m₁ := P₁ * Z * Q₁ + (1 - P₁) * Z * (V * Vᵀ * Q₁) + P₁ * (U * Uᵀ) * Z * (1 - Q₁) with hm₁
  set m₂ := (1 - P₁) * E * (V * Vᵀ * Q₁) + P₁ * (U * Uᵀ) * E * (1 - Q₁) with hm₂
  set y₁ := h • (P₁ * Jd * Q₁) with hy₁
  set y₂ := h • (dP * (G' - G) * Q₁) with hy₂
  set y₃ := h • (P₁ * (G' - G) * dQ) with hy₃
  have hDsum : dP * A * Q₁ + P₁ * A * dQ + P₁ * Z * Q₁ + y₁ + y₂ + y₃ =
      m₁ + m₂ + (W₂ + W₁) + X₁ + X₂ + y₁ + y₂ + y₃ := by
    rw [htr, hE2, hX₁, hE1, hm₁, hm₂]
    abel
  rw [hDsum]
  set b := h * g * ρ with hbdef
  set l := h * L with hldef
  have hb0 : 0 ≤ b := by positivity
  have hl0 : 0 ≤ l := by positivity
  have hx0 : 0 ≤ h * (ε + b * g) := by positivity
  have hW : ‖W₂ + W₁‖ ≤ (h * ε * ρ + b ^ 2) * z := by
    have h1 : ‖W₂‖ ≤ h * (ε + b * g) * (a₂ * ρ) := by
      rw [← e3, norm_transpose]; exact l2
    have h2 : ‖(1 - P₁) * (A * dV * (Vᵀ * Q₁))‖ ≤ h * (ε + b * g) * (a₁ * ρ) := by
      have e : (1 - P₁) * (A * dV * (Vᵀ * Q₁)) = W₁ := by
        simp only [hW₁, Matrix.mul_assoc]
      rw [e]; exact k2
    have := norm_wein_le hP₁ (X := U * (dUᵀ * (A * (1 - Q₁)))) (X' := A * dV * (Vᵀ * Q₁)) hx0 hρ
      hz0 h1 h2 hbl
    have e : W₂ + W₁ = P₁ * (U * (dUᵀ * (A * (1 - Q₁)))) + (1 - P₁) * (A * dV * (Vᵀ * Q₁)) := by
      simp only [hW₁, hW₂, Matrix.mul_assoc]
    rw [e]
    refine this.trans (le_of_eq ?_)
    rw [hbdef]; ring
  have hX₂n : ‖X₂‖ ≤ 2 * (2 * b) ^ 2 * be := by rw [hX₂, norm_transpose]; exact l1
  have hm₂n : ‖m₂‖ ≤ 2 * (l * z) := by
    have t1 : ‖(1 - P₁) * E * (V * Vᵀ * Q₁)‖ ≤ l * z := by
      refine (frob_mul_le' _ _).trans ?_
      calc ‖(1 - P₁) * E‖ * specNorm (V * Vᵀ * Q₁) ≤ ‖E‖ * 1 :=
            mul_le_mul (hP₁.compl.norm_mul_le _) hV' (specNorm_nonneg _) (norm_nonneg _)
        _ ≤ l * z := by rw [mul_one]; exact hE
    have t2 : ‖P₁ * (U * Uᵀ) * E * (1 - Q₁)‖ ≤ l * z := by
      refine (hQ₁.compl.norm_mul_le' _).trans ((frob_mul_le _ _).trans ?_)
      calc specNorm (P₁ * (U * Uᵀ)) * ‖E‖ ≤ 1 * ‖E‖ :=
            mul_le_mul_of_nonneg_right hU' (norm_nonneg _)
        _ ≤ l * z := by rw [one_mul]; exact hE
    refine (norm_add_le _ _).trans ?_
    linarith
  have hdYn : ‖dY'‖ ≤ z + 5 * al + 5 * be := by
    rw [hdY]
    have t1 : ‖P₁ * Z * Q₁‖ ≤ z := by
      rw [← hzZ]
      exact (hQ₁.norm_mul_le' _).trans (hP₁.norm_mul_le _)
    have t2 : ‖P₁ * Y * dQ‖ ≤ 5 * be := by rw [← hYt, norm_transpose]; exact l3
    have h1 := norm_add_le (dP * Y * Q₁ + P₁ * Z * Q₁) (P₁ * Y * dQ)
    have h2 := norm_add_le (dP * Y * Q₁) (P₁ * Z * Q₁)
    linarith
  have hy₁n : ‖y₁‖ ≤ l * (z + 5 * al + 5 * be) := by
    rw [hy₁, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have t1 : ‖P₁ * Jd * Q₁‖ ≤ L * (z + 5 * al + 5 * be) :=
      ((hQ₁.norm_mul_le' _).trans (hP₁.norm_mul_le _)).trans
        (hJd.trans (mul_le_mul_of_nonneg_left hdYn hL))
    calc h * ‖P₁ * Jd * Q₁‖ ≤ h * (L * (z + 5 * al + 5 * be)) :=
          mul_le_mul_of_nonneg_left t1 hh
      _ = l * (z + 5 * al + 5 * be) := by rw [hldef]; ring
  have hΔs : specNorm (G' - G) ≤ L * (2 * (h * g)) := (specNorm_le_frob _).trans hG'
  have hy₂n : ‖y₂‖ ≤ 8 * l * b * al := by
    rw [hy₂, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have t1 : ‖dP * (G' - G) * Q₁‖ ≤ (4 * ρ * al) * (L * (2 * (h * g))) := by
      refine (hQ₁.norm_mul_le' _).trans ((frob_mul_le' _ _).trans ?_)
      exact mul_le_mul k4 hΔs (specNorm_nonneg _) (by positivity)
    calc h * ‖dP * (G' - G) * Q₁‖ ≤ h * ((4 * ρ * al) * (L * (2 * (h * g)))) :=
          mul_le_mul_of_nonneg_left t1 hh
      _ = 8 * l * b * al := by rw [hldef, hbdef]; ring
  have hy₃n : ‖y₃‖ ≤ 8 * l * b * be := by
    rw [hy₃, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have hQs : specNorm dQ ≤ 4 * ρ * be := (specNorm_le_frob _).trans l4
    have t1 : ‖P₁ * (G' - G) * dQ‖ ≤ (L * (2 * (h * g))) * (4 * ρ * be) := by
      refine (frob_mul_le' _ _).trans ?_
      exact mul_le_mul ((hP₁.norm_mul_le _).trans hG') hQs (specNorm_nonneg _) (by positivity)
    calc h * ‖P₁ * (G' - G) * dQ‖ ≤ h * ((L * (2 * (h * g))) * (4 * ρ * be)) :=
          mul_le_mul_of_nonneg_left t1 hh
      _ = 8 * l * b * be := by rw [hldef, hbdef]; ring
  refine (norm_add8_le _ _ _ _ _ _ _ _).trans ?_
  exact core_arith hz0 hb hl0 hhL hal0 hbe0 hal' hbe' hfro hm₂n hW k1 hX₂n hy₁n hy₂n hy₃n

/-- The bases move by at most `σ_r⁻¹` times the off-diagonal blocks of `Z`. -/
lemma basis_moves {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix r r ℝ) (Z : Matrix m n ℝ) :
    ‖(1 - V * Vᵀ) * (Zᵀ * U * Sᵀ⁻¹)‖ ≤ ‖U * Uᵀ * Z * (1 - V * Vᵀ)‖ * specNorm S⁻¹ ∧
      ‖(1 - U * Uᵀ) * (Z * V * S⁻¹)‖ ≤ ‖(1 - U * Uᵀ) * Z * (V * Vᵀ)‖ * specNorm S⁻¹ := by
  have hP := isOrthProjMat_mul_transpose hU
  have hQ := isOrthProjMat_mul_transpose hV
  have hρt : specNorm Sᵀ⁻¹ = specNorm S⁻¹ := by
    rw [← Matrix.transpose_nonsing_inv, specNorm_transpose]
  constructor
  · have := norm_mul_basis_le hU (R := 1 - V * Vᵀ) Z Sᵀ⁻¹
    rw [hρt, hQ.compl.symm] at this
    have e : (1 - V * Vᵀ) * (Zᵀ * U * Sᵀ⁻¹) = (1 - V * Vᵀ) * Zᵀ * U * Sᵀ⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [e]; exact this
  · have := norm_mul_basis_le hV (R := 1 - U * Uᵀ) Zᵀ S⁻¹
    rw [Matrix.transpose_transpose, hP.compl.symm] at this
    have e2 : V * Vᵀ * Zᵀ * (1 - U * Uᵀ) = ((1 - U * Uᵀ) * Z * (V * Vᵀ))ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hP.compl.symm, Matrix.mul_assoc]
    rw [e2, norm_transpose] at this
    have e : (1 - U * Uᵀ) * (Z * V * S⁻¹) = (1 - U * Uᵀ) * Z * V * S⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [e]; exact this

/-- The S-step starts close to `Y`: `‖P₁ Y Q₁ - Y‖_F ≤ 2 h ‖G‖_F`. -/
lemma galerkin_move {P₁ : Matrix m m ℝ} {Q₁ : Matrix n n ℝ} {Y : Matrix m n ℝ} {x : ℝ}
    (hQ₁ : IsOrthProjMat Q₁) (h1 : ‖(1 - P₁) * Y‖ ≤ x) (h2 : ‖(1 - Q₁) * Yᵀ‖ ≤ x) :
    ‖P₁ * Y * Q₁ - Y‖ ≤ 2 * x := by
  have e : P₁ * Y * Q₁ - Y = -((1 - P₁) * Y * Q₁) - ((1 - Q₁) * Yᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hQ₁.compl.symm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_transpose]
  have := (hQ₁.norm_mul_le' ((1 - P₁) * Y)).trans h1
  linarith

lemma le_of_sq_add_le {a c z : ℝ} (ha : 0 ≤ a) (hz : 0 ≤ z) (h : a ^ 2 + c ^ 2 ≤ z ^ 2) :
    a ≤ z := by
  refine (pow_le_pow_iff_left₀ ha hz two_ne_zero).1 ?_
  nlinarith [sq_nonneg c]

/-- `t + y s ≤ (1 + l + b) z` for the two side bounds. -/
lemma side_arith {l y ρ a z G : ℝ} (hy : 0 ≤ y) (hρ : 0 ≤ ρ) (ha : a ≤ z) (hG : y = G) :
    (1 + l) * z + y * (a * ρ) ≤ (1 + l + G * ρ) * z := by
  subst hG
  have h1 : a * ρ ≤ z * ρ := mul_le_mul_of_nonneg_right ha hρ
  have h2 : y * (a * ρ) ≤ y * (z * ρ) := mul_le_mul_of_nonneg_left h1 hy
  have e : (1 + l + y * ρ) * z = (1 + l) * z + y * (z * ρ) := by ring
  rw [e]; linarith

/-- The core estimate behind `norm_barTangent_le`, with the field eliminated. -/
lemma tangent_core {U : Matrix m r ℝ} {V : Matrix n r ℝ} {S : Matrix r r ℝ}
    {Y G G' A Z E Jd : Matrix m n ℝ} {h L : ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hY : Y = U * S * Vᵀ)
    (hA : A = Y + h • G) (hh : 0 ≤ h) (hL : 0 ≤ L) (hhL : h * L ≤ 1)
    (hb : h * ‖G‖ * specNorm S⁻¹ ≤ 1 / 2)
    (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) (hE : ‖E‖ ≤ h * L * ‖Z‖)
    (hJd : ‖Jd‖ ≤ L * ‖dProj (A * V) ((Z + E) * V + A * (Zᵀ * U * Sᵀ⁻¹)) * Y * colProj (Aᵀ * U) +
      colProj (A * V) * Z * colProj (Aᵀ * U) +
      colProj (A * V) * Y * dProj (Aᵀ * U) ((Z + E)ᵀ * U + Aᵀ * (Z * V * S⁻¹))‖)
    (hG' : ‖G' - G‖ ≤ L * ‖colProj (A * V) * Y * colProj (Aᵀ * U) - Y‖) :
    ‖dProj (A * V) ((Z + E) * V + A * (Zᵀ * U * Sᵀ⁻¹)) *
          (colProj (A * V) * Y * colProj (Aᵀ * U) + h • G') * colProj (Aᵀ * U) +
        colProj (A * V) * ((dProj (A * V) ((Z + E) * V + A * (Zᵀ * U * Sᵀ⁻¹)) * Y *
          colProj (Aᵀ * U) + colProj (A * V) * Z * colProj (Aᵀ * U) +
          colProj (A * V) * Y * dProj (Aᵀ * U) ((Z + E)ᵀ * U + Aᵀ * (Z * V * S⁻¹))) + h • Jd) *
          colProj (Aᵀ * U) +
        colProj (A * V) * (colProj (A * V) * Y * colProj (Aᵀ * U) + h • G') *
          dProj (Aᵀ * U) ((Z + E)ᵀ * U + Aᵀ * (Z * V * S⁻¹))‖ ≤
      (1 + h * specNorm ((1 - U * Uᵀ) * G * (1 - V * Vᵀ)) * specNorm S⁻¹ +
        45 * (h * ‖G‖ * specNorm S⁻¹) ^ 2 + 48 * (h * L)) * ‖Z‖ := by
  have hSd := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hSt : IsUnit Sᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact hSd
  have hρ0 : 0 ≤ specNorm S⁻¹ := specNorm_nonneg _
  have hρt : specNorm Sᵀ⁻¹ = specNorm S⁻¹ := by
    rw [← Matrix.transpose_nonsing_inv, specNorm_transpose]
  have hA1 : A = U * S * Vᵀ + h • G := by rw [hA, hY]
  have hAt : Aᵀ = V * Sᵀ * Uᵀ + h • Gᵀ := by
    rw [hA1, Matrix.transpose_add, Matrix.transpose_smul]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hAt' : Aᵀ = Yᵀ + h • Gᵀ := by rw [hA, Matrix.transpose_add, Matrix.transpose_smul]
  have hb' : h * ‖Gᵀ‖ * specNorm Sᵀ⁻¹ ≤ 1 / 2 := by rw [norm_transpose, hρt]; exact hb
  obtain ⟨hKu, hKp, hx₁, hc₁⟩ := side_facts hU hV hS hA1 hh hb
  obtain ⟨hLu, hLp, hx₂, hc₂⟩ := side_facts hV hU hSt hAt hh hb'
  rw [norm_transpose, hρt] at hx₂ hc₂
  rw [hρt] at hLp
  obtain ⟨r1, -, r3, r4⟩ := residual_facts hU hV hA1 hh hKu hx₁
  obtain ⟨s1, -, s3, s4⟩ := residual_facts hV hU hAt hh hLu hx₂
  rw [norm_transpose] at s3 s4
  have hP := isOrthProjMat_mul_transpose hU
  have hQ := isOrthProjMat_mul_transpose hV
  have hεt : specNorm ((1 - V * Vᵀ) * Gᵀ * (1 - U * Uᵀ)) =
      specNorm ((1 - U * Uᵀ) * G * (1 - V * Vᵀ)) := by
    rw [← specNorm_transpose ((1 - U * Uᵀ) * G * (1 - V * Vᵀ))]
    congr 1
    simp only [Matrix.transpose_mul, hP.compl.symm, hQ.compl.symm, Matrix.mul_assoc]
  rw [hεt] at s3
  have hP₁ := isOrthProjMat_colProjK hKu
  have hQ₁ := isOrthProjMat_colProjK hLu
  have hUt := specNorm_transpose_le_one hU
  have hVt := specNorm_transpose_le_one hV
  have hYQ : Y * (1 - V * Vᵀ) = 0 := by
    rw [hY, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc (U * S), ← Matrix.mul_assoc Vᵀ, hV,
      Matrix.one_mul, sub_self]
  have hYP : Yᵀ * (1 - U * Uᵀ) = 0 := by
    have : Yᵀ = V * Sᵀ * Uᵀ := by
      rw [hY]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [this, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc (V * Sᵀ), ← Matrix.mul_assoc Uᵀ, hU,
      Matrix.one_mul, sub_self]
  have hz0 : 0 ≤ ‖Z‖ := norm_nonneg _
  have h₁ : specNorm ((1 - colProj (A * V)) * (U * Uᵀ)) ≤ h * ‖G‖ * specNorm S⁻¹ := by
    rw [← Matrix.mul_assoc]; simpa using specNorm_mul_le_of hx₁ hUt
  have h₃ : specNorm (colProj (A * V) * (1 - U * Uᵀ)) ≤ 2 * (h * ‖G‖ * specNorm S⁻¹) := by
    have e : colProj (A * V) * (1 - U * Uᵀ) = ((1 - U * Uᵀ) * colProj (A * V))ᵀ := by
      rw [Matrix.transpose_mul, hP₁.symm, hP.compl.symm]
    rw [e, specNorm_transpose]; exact hc₁
  have h₄ : specNorm (V * Vᵀ * (1 - colProj (Aᵀ * U))) ≤ h * ‖G‖ * specNorm S⁻¹ := by
    have e : V * Vᵀ * (1 - colProj (Aᵀ * U)) = ((1 - colProj (Aᵀ * U)) * (V * Vᵀ))ᵀ := by
      rw [Matrix.transpose_mul, hQ.symm, hQ₁.compl.symm]
    rw [e, specNorm_transpose, ← Matrix.mul_assoc]
    simpa using specNorm_mul_le_of hx₂ hVt
  have hfrozen := norm_frozen_le hP₁ hQ₁ hZ h₁ hc₂ h₃ h₄
  have hblocks := blocks_le hP hQ Z
  obtain ⟨hv, hu⟩ := basis_moves hU hV S Z
  have ha₁ : ‖U * Uᵀ * Z * (1 - V * Vᵀ)‖ ≤ ‖Z‖ := le_of_sq_add_le (norm_nonneg _) hz0 hblocks
  have ha₂ : ‖(1 - U * Uᵀ) * Z * (V * Vᵀ)‖ ≤ ‖Z‖ :=
    le_of_sq_add_le (norm_nonneg _) hz0 (by rw [add_comm]; exact hblocks)
  have hdA : ‖Z + E‖ ≤ (1 + h * L) * ‖Z‖ := by
    have := norm_add_le Z E
    have e : (1 + h * L) * ‖Z‖ = ‖Z‖ + h * L * ‖Z‖ := by ring
    rw [e]; linarith
  have hdAt : ‖(Z + E)ᵀ‖ ≤ (1 + h * L) * ‖Z‖ := by rw [norm_transpose]; exact hdA
  obtain ⟨hal, k2⟩ := side_bundle (Q₁ := colProj (Aᵀ * U)) hV hP₁ hQ₁ r1 r3 r4 hv hdA
  obtain ⟨hbe, l2⟩ := side_bundle (Q₁ := colProj (A * V)) hU hQ₁ hP₁ s1 s3 s4 hu hdAt
  have hc1 : 2 * (h * ‖G‖ * specNorm S⁻¹) ≤ 1 := by linarith
  obtain ⟨k1, k3, k4⟩ := side_tangent hKu hV hQ₁ hc₂ hA hYQ hKp (le_refl ‖G‖) hh hρ0 (le_refl _)
    hc1 (Z + E) (Zᵀ * U * Sᵀ⁻¹)
  obtain ⟨l1, l3, l4⟩ := side_tangent hLu hU hP₁ hc₁ hAt' hYP hLp (le_of_eq (norm_transpose G))
    hh hρ0 (le_refl _) hc1 (Z + E)ᵀ (Z * V * S⁻¹)
  have hmove : ‖colProj (A * V) * Y * colProj (Aᵀ * U) - Y‖ ≤ 2 * (h * ‖G‖) := by
    refine galerkin_move hQ₁ (norm_compl_Y_le hKu hV hA hYQ hh) ?_
    have := norm_compl_Y_le hLu hU hAt' hYP hh
    rwa [norm_transpose] at this
  have hhg : 0 ≤ h * ‖G‖ := mul_nonneg hh (norm_nonneg _)
  have hal' : ‖(1 - colProj (A * V)) * ((Z + E) * V + A * (Zᵀ * U * Sᵀ⁻¹))‖ ≤
      (1 + h * L + h * ‖G‖ * specNorm S⁻¹) * ‖Z‖ :=
    hal.trans (side_arith hhg hρ0 ha₁ rfl)
  have hbe' : ‖(1 - colProj (Aᵀ * U)) * ((Z + E)ᵀ * U + Aᵀ * (Z * V * S⁻¹))‖ ≤
      (1 + h * L + h * ‖G‖ * specNorm S⁻¹) * ‖Z‖ :=
    hbe.trans (side_arith hhg hρ0 ha₂ rfl)
  exact tangent_assembly hP₁ hQ₁ hA (dProj_mul_add hKu _) (dProj_mul_add hLu _)
    (dProj_transpose _ _)
    rfl hh hL hhL hρ0 (norm_nonneg _) (specNorm_nonneg _) hb hz0 rfl
    hblocks hE hfrozen rfl rfl hal' hbe' k1 k2 k3 k4 l1 l2 l3 l4 hJd
    (hG'.trans (mul_le_mul_of_nonneg_left hmove hL))
    (by simpa using specNorm_mul_le_of hQ.specNorm_le_one hQ₁.specNorm_le_one)
    (by simpa using specNorm_mul_le_of hP₁.specNorm_le_one hP.specNorm_le_one)

/-- **Upper bound for the tangent map of the BUG step.**  Let `Y = U S Vᵀ` with orthonormal `U`,
`V`, write `ρ = ‖S⁻¹‖₂ = σ_r⁻¹`, `G = F(Y)`, `b = h ‖G‖ ρ ≤ 1/2`, `h L ≤ 1`, and let `J`, `J'` be
the derivatives of `F` at `Y` and at the S-step start, of norm at most `L`.  Then for every tangent
direction `Z` at `Y`,

`‖δY₁‖_F ≤ (1 + h ‖(1 - P) G (1 - Q)‖₂ ρ + 45 b² + 48 h L) ‖Z‖_F`.

The only term of first order in `h` that contains `1 / σ_r` carries the normal part of the field,
with constant `1`; `bug_adjoint_growth` shows that this first-order term cannot be improved.  The
term `45 b²` is of second order in `h` with `1 / σ_r²`, so over `T / h` steps it contributes
`O(h ‖G‖² T / σ_r²)`.  This separates the adjoint from the projected flow bound of Koch–Lubich
(2007, Lemma 4.2), where `1 / σ_r` multiplies the whole field: here it multiplies the modelling
error `ε` of Ceruti–Lubich (arXiv 2010.02022).  The step size restriction `b ≤ 1/2` depends on
`σ_r`; `rank_loss_no_limit` shows that it cannot be removed. -/
theorem norm_barTangent_le {F : Matrix m n ℝ → Matrix m n ℝ} {h L : ℝ}
    {J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    {S : Matrix r r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hh : 0 ≤ h)
    (hL : 0 ≤ L) (hhL : h * L ≤ 1) (hb : h * ‖F (U * S * Vᵀ)‖ * specNorm S⁻¹ ≤ 1 / 2)
    (hJ : ∀ X, ‖J X‖ ≤ L * ‖X‖) (hJ' : ∀ X, ‖J' X‖ ≤ L * ‖X‖)
    (hLip : ‖F (galStart F h U V (U * S * Vᵀ)) - F (U * S * Vᵀ)‖ ≤
      L * ‖galStart F h U V (U * S * Vᵀ) - U * S * Vᵀ‖)
    {Z : Matrix m n ℝ} (hZ : (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) = 0) :
    ‖barTangent F h J J' U S V Z‖ ≤
      (1 + h * specNorm ((1 - U * Uᵀ) * F (U * S * Vᵀ) * (1 - V * Vᵀ)) * specNorm S⁻¹ +
        45 * (h * ‖F (U * S * Vᵀ)‖ * specNorm S⁻¹) ^ 2 + 48 * (h * L)) * ‖Z‖ := by
  refine tangent_core (A := eulerMat F h (U * S * Vᵀ)) (E := h • J Z) hU hV hS rfl rfl hh hL hhL hb
    hZ ?_ (hJ' _) hLip
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hJ Z) hh


lemma tangent_structure {P dP : Matrix m m ℝ} {Q dQ : Matrix n n ℝ} {B C : Matrix m n ℝ}
    (h1 : (1 - P) * P = 0) (h2 : Q * (1 - Q) = 0) :
    (1 - P) * (dP * B * Q + P * C * Q + P * B * dQ) * (1 - Q) = 0 := by
  have e1 : (1 - P) * (dP * B * Q) * (1 - Q) = 0 := by
    simp only [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have e2 : (1 - P) * (P * C * Q) * (1 - Q) = 0 := by
    simp only [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have e3 : (1 - P) * (P * B * dQ) * (1 - Q) = 0 := by
    calc _ = ((1 - P) * P) * B * dQ * (1 - Q) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, e1, e2, e3]
  simp

/-- The output of the tangent-linear model is tangent at the new point. -/
theorem bugTangent_tangent {F : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ}
    {J J' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    {Y : Matrix m n ℝ} (hK : IsUnit ((eulerMat F h Y * V)ᵀ * (eulerMat F h Y * V)))
    (hL : IsUnit (((eulerMat F h Y)ᵀ * U)ᵀ * ((eulerMat F h Y)ᵀ * U))) (dU : Matrix m r ℝ)
    (dV : Matrix n r ℝ) (dY : Matrix m n ℝ) :
    (1 - newP F h V Y) * bugTangent F h J J' U V Y dU dV dY * (1 - newQ F h U Y) = 0 := by
  have hP : IsOrthProjMat (newP F h V Y) := isOrthProjMat_colProjK hK
  have hQ : IsOrthProjMat (newQ F h U Y) := isOrthProjMat_colProjK hL
  have h1 : (1 - newP F h V Y) * newP F h V Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP.idem, sub_self]
  have h2 : newQ F h U Y * (1 - newQ F h U Y) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQ.idem, sub_self]
  exact tangent_structure h1 h2

/-- The gradient of `⟪barStep, Ψ⟫` at `Y = U S Vᵀ` given by the reverse sweep, assembled from the
three components of `bugAdjoint`. -/
noncomputable def barAdjoint (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (Ψ : Matrix m n ℝ) : Matrix m n ℝ :=
  (bugAdjoint F h Js Js' U V (U * S * Vᵀ) Ψ).1 * Sᵀ⁻¹ * Vᵀ +
    U * Sᵀ⁻¹ * ((bugAdjoint F h Js Js' U V (U * S * Vᵀ) Ψ).2.1)ᵀ +
    (bugAdjoint F h Js Js' U V (U * S * Vᵀ) Ψ).2.2

/-- **The exact discrete adjoint on rank-`r` matrices**: `barAdjoint` is the adjoint of
`barTangent` in the Frobenius inner product. -/
theorem inner_barTangent (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    {J J' Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, Js y⟫) (hJs' : ∀ x y, ⟪J' x, y⟫ = ⟪x, Js' y⟫)
    (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Z Ψ : Matrix m n ℝ) :
    ⟪barTangent F h J J' U S V Z, Ψ⟫ = ⟪Z, barAdjoint F h Js Js' U S V Ψ⟫ := by
  rw [barTangent, inner_bugTangent F h hJs hJs', barAdjoint, inner_add_right, inner_add_right]
  set g := bugAdjoint F h Js Js' U V (U * S * Vᵀ) Ψ
  have e1 : ⟪Z * V * S⁻¹, g.1⟫ = ⟪Z, g.1 * Sᵀ⁻¹ * Vᵀ⟫ := by
    rw [inner_mul_right, inner_mul_right, Matrix.transpose_nonsing_inv]
  have e2 : ⟪Zᵀ * U * Sᵀ⁻¹, g.2.1⟫ = ⟪Z, U * Sᵀ⁻¹ * (g.2.1)ᵀ⟫ := by
    rw [inner_mul_right, inner_mul_right, ← inner_transpose Zᵀ, Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      Matrix.mul_assoc]
  rw [e1, e2]

/-- **The basis gradients are residuals.**  In the reverse sweep the gradients with respect to the
two bases have the factors `A (1 - Q₁)` and `(1 - P₁) A`.  So when `A = Y + h F(Y)` has rank `r`
inside the new bases, the basis gradients vanish and the factors `(K⁺)ᵀ`, `(L⁺)ᵀ` of size `1 / σ_r`
disappear from the adjoint. -/
theorem bugAdjoint_basis_residual (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (Y Ψ : Matrix m n ℝ) :
    ∃ (X₁ : Matrix m m ℝ) (X₂ : Matrix n n ℝ),
      (bugAdjoint F h Js Js' U V Y Ψ).1 = (eulerMat F h Y * (1 - newQ F h U Y)) * (X₂ + X₂ᵀ) *
          (((eulerMat F h Y)ᵀ * U).gramPinv)ᵀ ∧
        (bugAdjoint F h Js Js' U V Y Ψ).2.1 = ((1 - newP F h V Y) * eulerMat F h Y)ᵀ * (X₁ + X₁ᵀ) *
          ((eulerMat F h Y * V).gramPinv)ᵀ := by
  have hc : (1 - newP F h V Y)ᵀ = 1 - newP F h V Y := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]; rw [newP, colProj_transpose]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = galStart F h U V Y := ⟨_, rfl⟩
  obtain ⟨bY, hbY⟩ : ∃ bY, bY = newP F h V Y * Ψ * newQ F h U Y +
      h • Js' (newP F h V Y * Ψ * newQ F h U Y) := ⟨_, rfl⟩
  refine ⟨Ψ * newQ F h U Y * (Y' + h • F Y')ᵀ + bY * newQ F h U Y * Yᵀ,
    (Y' + h • F Y')ᵀ * newP F h V Y * Ψ + Yᵀ * newP F h V Y * bY, ?_, ?_⟩
  · subst hY' hbY
    change eulerMat F h Y *
      ((1 - newQ F h U Y) * (_ + _ᵀ) * (((eulerMat F h Y)ᵀ * U).gramPinv)ᵀ) = _
    simp only [Matrix.mul_assoc]
  · subst hY' hbY
    change (eulerMat F h Y)ᵀ *
      ((1 - newP F h V Y) * (_ + _ᵀ) * ((eulerMat F h Y * V).gramPinv)ᵀ) = _
    rw [Matrix.transpose_mul, hc]
    simp only [Matrix.mul_assoc]

section Growth

lemma tanProj_tangent {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (X : Matrix m n ℝ) : (1 - P) * tanProj P Q X * (1 - Q) = 0 := by
  have h1 : (1 - P) * ((1 - P) * X * (1 - Q)) * (1 - Q) = (1 - P) * X * (1 - Q) := by
    calc _ = ((1 - P) * (1 - P)) * X * ((1 - Q) * (1 - Q)) := by simp only [Matrix.mul_assoc]
      _ = (1 - P) * X * (1 - Q) := by rw [hP.compl.idem, hQ.compl.idem]
  rw [tanProj, Matrix.mul_sub (1 - P), Matrix.sub_mul, h1, sub_self]

/-- The adjoint of a map that is bounded on the tangent space is bounded on the tangent space. -/
theorem norm_tanProj_adjoint_le {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) {D Ds : Matrix m n ℝ → Matrix m n ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ Z Ψ, ⟪D Z, Ψ⟫ = ⟪Z, Ds Ψ⟫)
    (hb : ∀ Z, (1 - P) * Z * (1 - Q) = 0 → ‖D Z‖ ≤ C * ‖Z‖) (Ψ : Matrix m n ℝ) :
    ‖tanProj P Q (Ds Ψ)‖ ≤ C * ‖Ψ‖ := by
  set W := tanProj P Q (Ds Ψ) with hW
  have hsym : ⟪W, W⟫ = ⟪W, Ds Ψ⟫ := by
    have h0 : ⟪W, (1 - P) * Ds Ψ * (1 - Q)⟫ = 0 := by
      rw [inner_mul_right', inner_mul_left', hP.compl.symm, hQ.compl.symm, ← Matrix.mul_assoc,
        hW, tanProj_tangent hP hQ, inner_zero_left]
    conv_lhs => rw [hW, ← hW]
    calc ⟪W, tanProj P Q (Ds Ψ)⟫ = ⟪W, Ds Ψ⟫ - ⟪W, (1 - P) * Ds Ψ * (1 - Q)⟫ := by
          rw [tanProj, inner_sub_right]
      _ = ⟪W, Ds Ψ⟫ := by rw [h0, sub_zero]
  have h1 : ‖W‖ ^ 2 ≤ C * ‖Ψ‖ * ‖W‖ := by
    rw [← real_inner_self_eq_norm_sq, hsym, ← hD]
    refine (real_inner_le_norm _ _).trans ?_
    have := hb W (tanProj_tangent hP hQ _)
    nlinarith [norm_nonneg Ψ, norm_nonneg W]
  rcases eq_or_lt_of_le (norm_nonneg W) with h0 | h0
  · rw [← h0]; positivity
  · have : ‖W‖ * ‖W‖ ≤ (C * ‖Ψ‖) * ‖W‖ := by nlinarith
    exact le_of_mul_le_mul_right this h0

/-- A product of per-step factors `1 + h c` is at most `exp (N h c)`. -/
lemma le_exp_of_step {a : ℕ → ℝ} {N : ℕ} {x : ℝ} (hx : 0 ≤ 1 + x)
    (hs : ∀ k < N, a (k + 1) ≤ (1 + x) * a k) (ha : ∀ k, 0 ≤ a k) :
    a N ≤ Real.exp (N * x) * a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := ih fun k hk => hs k (Nat.lt_succ_of_lt hk)
    have h2 := hs N (Nat.lt_succ_self N)
    have h3 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc a (N + 1) ≤ (1 + x) * a N := h2
      _ ≤ (1 + x) * (Real.exp (N * x) * a 0) := mul_le_mul_of_nonneg_left h1 hx
      _ ≤ Real.exp x * (Real.exp (N * x) * a 0) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg (Real.exp_pos _).le (ha 0))
      _ = Real.exp ((N + 1 : ℕ) * x) * a 0 := by
        rw [← mul_assoc, ← Real.exp_add]; push_cast; ring_nf

end Growth

/-- **The adjoint bound.**  Under the hypotheses of `norm_barTangent_le`, the tangential part of
the discrete adjoint `barAdjoint` satisfies the same bound as the tangent map. -/
theorem norm_tanProj_barAdjoint_le {F : Matrix m n ℝ → Matrix m n ℝ} {h L : ℝ}
    {J J' Js Js' : Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    {S : Matrix r r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S) (hh : 0 ≤ h)
    (hL : 0 ≤ L) (hhL : h * L ≤ 1) (hb : h * ‖F (U * S * Vᵀ)‖ * specNorm S⁻¹ ≤ 1 / 2)
    (hJ : ∀ X, ‖J X‖ ≤ L * ‖X‖) (hJ' : ∀ X, ‖J' X‖ ≤ L * ‖X‖)
    (hLip : ‖F (galStart F h U V (U * S * Vᵀ)) - F (U * S * Vᵀ)‖ ≤
      L * ‖galStart F h U V (U * S * Vᵀ) - U * S * Vᵀ‖)
    (hJs : ∀ x y, ⟪J x, y⟫ = ⟪x, Js y⟫) (hJs' : ∀ x y, ⟪J' x, y⟫ = ⟪x, Js' y⟫)
    (Ψ : Matrix m n ℝ) :
    ‖tanProj (U * Uᵀ) (V * Vᵀ) (barAdjoint F h Js Js' U S V Ψ)‖ ≤
      (1 + h * specNorm ((1 - U * Uᵀ) * F (U * S * Vᵀ) * (1 - V * Vᵀ)) * specNorm S⁻¹ +
        45 * (h * ‖F (U * S * Vᵀ)‖ * specNorm S⁻¹) ^ 2 + 48 * (h * L)) * ‖Ψ‖ := by
  have h0 : 0 ≤ h * specNorm ((1 - U * Uᵀ) * F (U * S * Vᵀ) * (1 - V * Vᵀ)) * specNorm S⁻¹ :=
    mul_nonneg (mul_nonneg hh (specNorm_nonneg _)) (specNorm_nonneg _)
  have h1 : 0 ≤ h * L := mul_nonneg hh hL
  exact norm_tanProj_adjoint_le (isOrthProjMat_mul_transpose hU) (isOrthProjMat_mul_transpose hV)
    (by positivity) (inner_barTangent F h hJs hJs' U S V)
    (fun Z hZ => norm_barTangent_le hU hV hS hh hL hhL hb hJ hJ' hLip hZ) Ψ

/-- **Upper bound for the growth along a trajectory**, the counterpart of `bug_adjoint_growth`.
Along a sequence of frames whose projectors are those produced by the BUG steps, with
`σ_r⁻¹ ≤ ρ`, `‖F‖_F ≤ B`, normal part `≤ ε`, the iterated tangent map satisfies

`‖Z_N‖_F ≤ exp (N h (ε ρ + 48 L + 45 h (B ρ)²)) ‖Z_0‖_F`.

At time `T = N h` and for `h → 0` the exponent is `T (ε / σ_r + 48 L)`.  With `bug_adjoint_growth`
this shows that the rate `ε / σ_r` is the correct one. -/
theorem tangent_growth_le {F : Matrix m n ℝ → Matrix m n ℝ} {h L ρ B ε : ℝ} {N : ℕ}
    {U : ℕ → Matrix m r ℝ} {V : ℕ → Matrix n r ℝ} {S : ℕ → Matrix r r ℝ}
    {J J' : ℕ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ} {Z : ℕ → Matrix m n ℝ}
    (hU : ∀ k, (U k)ᵀ * U k = 1) (hV : ∀ k, (V k)ᵀ * V k = 1) (hS : ∀ k, IsUnit (S k))
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hhL : h * L ≤ 1) (hρ : ∀ k, specNorm (S k)⁻¹ ≤ ρ)
    (hB : ∀ k, ‖F (U k * S k * (V k)ᵀ)‖ ≤ B)
    (hε : ∀ k, specNorm ((1 - U k * (U k)ᵀ) * F (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)) ≤ ε)
    (hb : h * B * ρ ≤ 1 / 2) (hJ : ∀ k X, ‖J k X‖ ≤ L * ‖X‖) (hJ' : ∀ k X, ‖J' k X‖ ≤ L * ‖X‖)
    (hLip : ∀ k, ‖F (galStart F h (U k) (V k) (U k * S k * (V k)ᵀ)) - F (U k * S k * (V k)ᵀ)‖ ≤
      L * ‖galStart F h (U k) (V k) (U k * S k * (V k)ᵀ) - U k * S k * (V k)ᵀ‖)
    (hP : ∀ k, newP F h (V k) (U k * S k * (V k)ᵀ) = U (k + 1) * (U (k + 1))ᵀ)
    (hQ : ∀ k, newQ F h (U k) (U k * S k * (V k)ᵀ) = V (k + 1) * (V (k + 1))ᵀ)
    (hZ0 : (1 - U 0 * (U 0)ᵀ) * Z 0 * (1 - V 0 * (V 0)ᵀ) = 0)
    (hZ : ∀ k, Z (k + 1) = barTangent F h (J k) (J' k) (U k) (S k) (V k) (Z k)) :
    ‖Z N‖ ≤ Real.exp (N * (h * (ε * ρ + 48 * L + 45 * h * (B * ρ) ^ 2))) * ‖Z 0‖ := by
  have hρ0 : 0 ≤ ρ := (specNorm_nonneg _).trans (hρ 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hε0 : 0 ≤ ε := (specNorm_nonneg _).trans (hε 0)
  have hbk : ∀ k, h * ‖F (U k * S k * (V k)ᵀ)‖ * specNorm (S k)⁻¹ ≤ h * B * ρ := fun k =>
    mul_le_mul (mul_le_mul_of_nonneg_left (hB k) hh) (hρ k) (specNorm_nonneg _) (by positivity)
  have hbk' := fun k => (hbk k).trans hb
  have htan : ∀ k, (1 - U k * (U k)ᵀ) * Z k * (1 - V k * (V k)ᵀ) = 0 := by
    intro k
    induction k with
    | zero => exact hZ0
    | succ k _ =>
      have hAt : (eulerMat F h (U k * S k * (V k)ᵀ))ᵀ =
          V k * (S k)ᵀ * (U k)ᵀ + h • (F (U k * S k * (V k)ᵀ))ᵀ := by
        rw [eulerMat, Matrix.transpose_add, Matrix.transpose_smul]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      have hSt : IsUnit (S k)ᵀ := by
        rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
        exact (Matrix.isUnit_iff_isUnit_det _).1 (hS k)
      have hb' : h * ‖(F (U k * S k * (V k)ᵀ))ᵀ‖ * specNorm (S k)ᵀ⁻¹ ≤ 1 / 2 := by
        rw [norm_transpose, ← Matrix.transpose_nonsing_inv, specNorm_transpose]
        exact hbk' k
      have hK := (side_facts (hU k) (hV k) (hS k) rfl hh (hbk' k)).1
      have hLu := (side_facts (hV k) (hU k) hSt hAt hh hb').1
      rw [hZ k, ← hP k, ← hQ k]
      exact bugTangent_tangent hK hLu _ _ _
  refine le_exp_of_step (by positivity) (fun k _ => ?_) (fun k => norm_nonneg _)
  rw [hZ k]
  refine (norm_barTangent_le (hU k) (hV k) (hS k) hh hL hhL (hbk' k) (hJ k) (hJ' k) (hLip k)
    (htan k)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have t1 : h * specNorm ((1 - U k * (U k)ᵀ) * F (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)) *
      specNorm (S k)⁻¹ ≤ h * ε * ρ :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hε k) hh) (hρ k) (specNorm_nonneg _) (by positivity)
  have hbk0 : 0 ≤ h * ‖F (U k * S k * (V k)ᵀ)‖ * specNorm (S k)⁻¹ :=
    mul_nonneg (mul_nonneg hh (norm_nonneg _)) (specNorm_nonneg _)
  have t2 : (h * ‖F (U k * S k * (V k)ᵀ)‖ * specNorm (S k)⁻¹) ^ 2 ≤ (h * B * ρ) ^ 2 :=
    pow_le_pow_left₀ hbk0 (hbk k) 2
  have e : 1 + h * (ε * ρ + 48 * L + 45 * h * (B * ρ) ^ 2) =
      1 + h * ε * ρ + 45 * (h * B * ρ) ^ 2 + 48 * (h * L) := by ring
  rw [e]
  linarith

end Robust

/-! ### Examples: the hypotheses are satisfiable, and the rank conditions cannot be dropped -/

section Examples

/-- The hypotheses of `bug_adjoint_growth` and `bug_adjoint_not_robust` are satisfiable for all
`σ > 0` and `ν`: `Y = σ e₁ e₁ᵀ`, `N = ν e₂ e₂ᵀ`, `E = e₂ e₁ᵀ + e₁ e₂ᵀ`. -/
theorem exists_normal_instance {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) :
    ∃ (U V : Matrix (Fin 2) (Fin 1) ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ)
      (N : Matrix (Fin 2) (Fin 2) ℝ) (u v p q : Fin 2 → ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ IsUnit S ∧ Uᵀ * N = 0 ∧ N * V = 0 ∧
        IsSingularTriple (U * S * Vᵀ) σ u v ∧ IsSingularTriple N ν p q ∧
        Matrix.vecMulVec p v + Matrix.vecMulVec u q ≠ 0 := by
  have hY : ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * !![σ] *
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ) = !![σ, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  refine ⟨!![1; 0], !![1; 0], !![σ], !![0, 0; 0, ν], ![1, 0], ![1, 0], ![0, 1], ![0, 1],
    ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · rw [Matrix.isUnit_iff_isUnit_det]; simpa using hσ.ne'
  · ext i j; fin_cases i; fin_cases j <;> simp [Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · rw [hY]; ext i; fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  · rw [hY]; ext i; fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  · intro h0
    have := congrFun (congrFun h0 1) 0
    simp at this

/-- **The BUG step for the identity field is a dilation on the matrices `σ U Uᵀ`**: for orthonormal
`U`, `Φ(σ U Uᵀ) = (σ + h) U Uᵀ`. -/
theorem bugStep_identity_field {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) {σ h : ℝ}
    (hσh : σ + h ≠ 0) :
    bugStep (fun _ => 1) h U U (σ • (U * Uᵀ)) = (σ + h) • (U * Uᵀ) := by
  have hUU : U * Uᵀ * U = U := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have hR : IsUnit ((σ + h) • (1 : Matrix r r ℝ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (IsUnit.mk0 _ hσh).pow _
  have hA : eulerMat (fun _ => 1) h (σ • (U * Uᵀ)) * U = U * ((σ + h) • (1 : Matrix r r ℝ)) := by
    rw [eulerMat, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hUU, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, add_smul]
  have hAt : (eulerMat (fun _ => 1) h (σ • (U * Uᵀ)))ᵀ =
      eulerMat (fun _ => 1) h (σ • (U * Uᵀ)) := by
    simp [eulerMat, Matrix.transpose_smul, Matrix.transpose_mul]
  rw [bugStep_eq_of_qr hA (by rw [hAt, hA]) hU hU hR hR]
  have e1 : Uᵀ * (σ • (U * Uᵀ)) * U = σ • (1 : Matrix r r ℝ) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul, hU]
  have e2 : Uᵀ * (1 : Matrix m m ℝ) * U = 1 := by rw [Matrix.mul_one, hU]
  simp only [e1, e2]
  rw [← add_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **No robust Lipschitz bound.**  For the identity field (Lipschitz constant `0`) the BUG step
dilates distances between the matrices `σ U Uᵀ` by exactly `1 + h / σ`, for any two orthonormal
frames, while the exact flow `Y ↦ Y + h 1` is an isometry.  So on `{σ_r ≥ σ}` the Lipschitz constant
of the step is at least `1 + h / σ`, a finite-distance version of `bug_adjoint_growth`.  It does not
contradict the robust forward bound of Ceruti–Lubich (arXiv 2010.02022, Theorem 4), whose modelling
error `ε` is of size `1` here. -/
theorem bugStep_dilation {U₁ U₂ : Matrix m r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1) {σ h : ℝ}
    (hσ : 0 < σ) (hh : 0 ≤ h) :
    ‖bugStep (fun _ => 1) h U₁ U₁ (σ • (U₁ * U₁ᵀ)) -
        bugStep (fun _ => 1) h U₂ U₂ (σ • (U₂ * U₂ᵀ))‖ =
      (1 + h / σ) * ‖σ • (U₁ * U₁ᵀ) - σ • (U₂ * U₂ᵀ)‖ := by
  have hne : σ + h ≠ 0 := by positivity
  rw [bugStep_identity_field hU₁ hne, bugStep_identity_field hU₂ hne, ← smul_sub, ← smul_sub,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hσ,
    abs_of_pos (by positivity : 0 < σ + h), ← mul_assoc]
  congr 1
  field_simp

/-- **No continuous extension to lower rank.**  For the identity field and two frames with
different ranges, `σ U₁ U₁ᵀ` and `σ U₂ U₂ᵀ` tend to the same matrix `0` as `σ → 0⁺`, but their BUG
steps have different limits.  So the rank-`r` step does not extend continuously to rank-deficient
`Y`, whatever the step size `h > 0`. -/
theorem bugStep_no_limit_at_zero {U₁ U₂ : Matrix m r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1)
    (hne : U₁ * U₁ᵀ ≠ U₂ * U₂ᵀ) {h : ℝ} (hh : 0 < h) (W : Matrix m m ℝ) :
    ¬ (Tendsto (fun σ : ℝ => bugStep (fun _ => 1) h U₁ U₁ (σ • (U₁ * U₁ᵀ))) (𝓝[>] 0) (𝓝 W) ∧
      Tendsto (fun σ : ℝ => bugStep (fun _ => 1) h U₂ U₂ (σ • (U₂ * U₂ᵀ))) (𝓝[>] 0) (𝓝 W)) := by
  have key : ∀ {U : Matrix m r ℝ}, Uᵀ * U = 1 →
      Tendsto (fun σ : ℝ => bugStep (fun _ => 1) h U U (σ • (U * Uᵀ))) (𝓝[>] 0)
        (𝓝 (h • (U * Uᵀ))) := by
    intro U hU
    have h1 : Tendsto (fun σ : ℝ => (σ + h) • (U * Uᵀ)) (𝓝[>] 0) (𝓝 ((0 + h) • (U * Uᵀ))) := by
      have : Continuous fun σ : ℝ => (σ + h) • (U * Uᵀ) := by fun_prop
      exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (bugStep_identity_field hU (by have := Set.mem_Ioi.1 hσ; positivity)).symm
  rintro ⟨h1, h2⟩
  have e₁ := tendsto_nhds_unique h1 (key hU₁)
  have e₂ := tendsto_nhds_unique h2 (key hU₂)
  exact hne (smul_right_injective _ hh.ne' (e₁.symm.trans e₂))

/-- The first basis column of the rank-loss example. -/
def ex : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- The second basis column of the rank-loss example. -/
def ey : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 0 else 1

/-- The rotated column of the rank-loss example. -/
def wt (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else t

/-- The constant field `diag(-1, 1)` of the rank-loss example. -/
def G₀ : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then (if i = 0 then -1 else 1) else 0

/-- A `1 × 1` matrix. -/
def oneBy (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => t

lemma isUnit_oneBy {t : ℝ} (ht : t ≠ 0) : IsUnit (oneBy t) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
  exact IsUnit.mk0 _ ht

lemma ex_orth : exᵀ * ex = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [ex, Matrix.mul_apply]

lemma ey_orth : eyᵀ * ey = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [ey, Matrix.mul_apply, Fin.sum_univ_two]

/-- At `Y₀ = e₁ e₁ᵀ` with field `G₀`, `h = 1`, the K-step result vanishes. -/
theorem rank_loss_base : eulerMat (fun _ => G₀) 1 (ex * exᵀ) * ex = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eulerMat, ex, G₀, Matrix.mul_apply]

theorem rank_loss_family₁ {τ : ℝ} (hτ : τ ≠ 0) :
    bugStep (fun _ => G₀) 1 ex ex ((1 + τ) • (ex * exᵀ)) = τ • (ex * exᵀ) := by
  have hK : eulerMat (fun _ => G₀) 1 ((1 + τ) • (ex * exᵀ)) * ex = ex * oneBy τ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [eulerMat, ex, G₀, oneBy, Matrix.mul_apply]
  have hL : (eulerMat (fun _ => G₀) 1 ((1 + τ) • (ex * exᵀ)))ᵀ * ex = ex * oneBy τ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [eulerMat, ex, G₀, oneBy, Matrix.mul_apply]
  rw [bugStep_eq_of_qr hK hL ex_orth ex_orth (isUnit_oneBy hτ) (isUnit_oneBy hτ)]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ex, G₀, Matrix.mul_apply]

theorem rank_loss_family₂ {t : ℝ} (ht : t ≠ 0) :
    bugStep (fun _ => G₀) 1 (wt t) (wt t) ((1 + t ^ 2)⁻¹ • (wt t * (wt t)ᵀ)) =
      (1 + t ^ 2 * (1 + t ^ 2)⁻¹) • (ey * eyᵀ) := by
  have hp : (1 + t ^ 2) ≠ 0 := by positivity
  obtain ⟨c, hc⟩ : ∃ c, c = (1 + t ^ 2)⁻¹ := ⟨_, rfl⟩
  have hc1 : c * (1 + t ^ 2) = 1 := by rw [hc]; exact inv_mul_cancel₀ hp
  rw [← hc]
  have ht2 : 2 * t ≠ 0 := by positivity
  have hK : eulerMat (fun _ => G₀) 1 (c • (wt t * (wt t)ᵀ)) * wt t = ey * oneBy (2 * t) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [eulerMat, wt, ey, G₀, oneBy, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hc1
    · linear_combination t * hc1
  have hL : (eulerMat (fun _ => G₀) 1 (c • (wt t * (wt t)ᵀ)))ᵀ * wt t = ey * oneBy (2 * t) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [eulerMat, wt, ey, G₀, oneBy, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hc1
    · linear_combination t * hc1
  rw [bugStep_eq_of_qr hK hL ey_orth ey_orth (isUnit_oneBy ht2) (isUnit_oneBy ht2)]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [wt, ey, G₀, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Full column rank of the K-step result cannot be dropped.**  At `Y₀ = e₁ e₁ᵀ`, with constant
field `G₀ = diag(-1, 1)` and `h = 1`, the K-step result is `0` (`rank_loss_base`).  Two families of
rank-one data tend to `Y₀`; along them the BUG steps converge to `0` and to `e₂ e₂ᵀ`.  So the step
has no continuous extension to `Y₀`, which shows that the rank condition in `HasD.bugStep` is not an
artefact of the proof.  Here `h ‖G₀‖₂ = σ_r`, so the condition `h ‖G‖_F σ_r⁻¹ ≤ 1/2` of `side_facts`
cannot be relaxed beyond a constant. -/
theorem rank_loss_no_limit :
    Tendsto (fun τ : ℝ => (1 + τ) • (ex * exᵀ)) (𝓝 0) (𝓝 (ex * exᵀ)) ∧
      Tendsto (fun t : ℝ => (1 + t ^ 2)⁻¹ • (wt t * (wt t)ᵀ)) (𝓝 0) (𝓝 (ex * exᵀ)) ∧
      Tendsto (fun τ : ℝ => bugStep (fun _ => G₀) 1 ex ex ((1 + τ) • (ex * exᵀ))) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun t : ℝ => bugStep (fun _ => G₀) 1 (wt t) (wt t)
        ((1 + t ^ 2)⁻¹ • (wt t * (wt t)ᵀ))) (𝓝[≠] 0) (𝓝 (ey * eyᵀ)) := by
  have hw : ∀ t : ℝ, wt t * (wt t)ᵀ =
      ex * exᵀ + t • (ex * eyᵀ + ey * exᵀ) + t ^ 2 • (ey * eyᵀ) := by
    intro t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [wt, ex, ey, Matrix.mul_apply, sq]
  have hi1 : Continuous fun t : ℝ => 1 + t ^ 2 := by fun_prop
  have hi : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ := hi1.inv₀ fun t => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : Continuous fun τ : ℝ => (1 + τ) • (ex * exᵀ) := by fun_prop
    simpa using this.tendsto 0
  · have hc : Continuous fun t : ℝ => (1 + t ^ 2)⁻¹ • (ex * exᵀ + t • (ex * eyᵀ + ey * exᵀ) +
        t ^ 2 • (ey * eyᵀ)) := hi.smul (by fun_prop)
    have h0 := hc.tendsto 0
    simp only [hw]
    simpa using h0
  · have hc : Continuous fun τ : ℝ => τ • (ex * exᵀ) := by fun_prop
    have h1 : Tendsto (fun τ : ℝ => τ • (ex * exᵀ)) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (rank_loss_family₁ hτ).symm
  · have hc : Continuous fun t : ℝ => (1 + t ^ 2 * (1 + t ^ 2)⁻¹) • (ey * eyᵀ) :=
      (continuous_const.add ((by fun_prop : Continuous fun t : ℝ => t ^ 2).mul hi)).smul
        continuous_const
    have h1 : Tendsto (fun t : ℝ => (1 + t ^ 2 * (1 + t ^ 2)⁻¹) • (ey * eyᵀ)) (𝓝[≠] 0)
        (𝓝 (ey * eyᵀ)) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (rank_loss_family₂ ht).symm

/-- The symmetric matrix `[a τ; τ b]`. -/
def symB (a b τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 0 then (if j = 0 then a else τ) else (if j = 0 then τ else b)

/-- The spectral projector of `symB a b τ` for the eigenvalue `(a + b) / 2 + s`, where
`s² = ((a - b) / 2)² + τ²`. -/
noncomputable def topProj (a b τ s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (2 * s)⁻¹ *
    if i = 0 then (if j = 0 then (a - b) / 2 + s else τ)
    else (if j = 0 then τ else (b - a) / 2 + s)

/-- `topProj` is the orthogonal projector of rank one onto the top eigenvector. -/
theorem topProj_spec {a b τ s : ℝ} (hs0 : s ≠ 0) (hs : s ^ 2 = ((a - b) / 2) ^ 2 + τ ^ 2) :
    topProj a b τ s * topProj a b τ s = topProj a b τ s ∧
      symB a b τ * topProj a b τ s = ((a + b) / 2 + s) • topProj a b τ s ∧
      (topProj a b τ s)ᵀ = topProj a b τ s ∧ (topProj a b τ s).det = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [topProj, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf
    all_goals linear_combination (-4 : ℝ) * hs
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [topProj, symB, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf
    all_goals linear_combination (-4 : ℝ) * hs
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [topProj]
  · rw [Matrix.det_fin_two]
    simp [topProj]
    field_simp
    linear_combination (4 : ℝ) * hs

/-- The rank-one truncation of `symB a b τ`, i.e. top eigenvalue times `topProj`. -/
noncomputable def truncOne (a b τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((a + b) / 2 + √(((a - b) / 2) ^ 2 + τ ^ 2)) • topProj a b τ √(((a - b) / 2) ^ 2 + τ ^ 2)

/-- **Rank truncation amplifies by the relative gap.**  For `a > b`, the entry `(0, 1)` of the
rank-one truncation of `[a τ; τ b]` has derivative `a / (a - b)` at `τ = 0`, where the input entry
has derivative `1`.  So the derivative of truncation is not bounded independently of the gap
`σ_r - σ_{r+1}`.  This is a special case only: differentiability of the truncation at a general
matrix with a positive gap is not treated here. -/
theorem truncOne_deriv {a b : ℝ} (hab : b < a) :
    HasDerivAt (fun τ => truncOne a b τ 0 1) (a / (a - b)) 0 := by
  have hd : 0 < (a - b) / 2 := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ → ℝ, s = fun τ => √(((a - b) / 2) ^ 2 + τ ^ 2) := ⟨_, rfl⟩
  have hs0 : s 0 = (a - b) / 2 := by
    rw [hsdef]; simp [Real.sqrt_sq hd.le]
  have hin : HasDerivAt (fun τ : ℝ => ((a - b) / 2) ^ 2 + τ ^ 2) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).const_add (((a - b) / 2) ^ 2)
  have hsd : HasDerivAt s (0 / (2 * √(((a - b) / 2) ^ 2 + (0 : ℝ) ^ 2))) 0 := by
    rw [hsdef]
    exact hin.sqrt (by positivity)
  have hg : HasDerivAt (fun τ => ((a + b) / 2 + s τ) * (2 * s τ)⁻¹) _ 0 :=
    (hsd.const_add _).mul ((hsd.const_mul 2).inv (by rw [hs0]; positivity))
  have h1 := (hasDerivAt_id (0 : ℝ)).mul hg
  have e : (fun τ => truncOne a b τ 0 1) = (id * fun τ => ((a + b) / 2 + s τ) * (2 * s τ)⁻¹) := by
    funext τ
    simp [truncOne, topProj, hsdef]
    ring
  rw [e]
  convert h1 using 1
  simp [hs0]
  field_simp
  ring

end Examples

end Step
/-- The local left inverse of this file, replaced by the core `Matrix.gramPinv` (same definition,
`(KᵀK)⁻¹Kᵀ`). -/
@[deprecated (since := "2026-11-09")] alias pinv := Matrix.gramPinv

end LeanDLRA.Novel.OpTR37
