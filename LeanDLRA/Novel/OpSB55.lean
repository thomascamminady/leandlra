import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius

/-!
# Robustness of low-rank training to rank over-estimation and ill-conditioned initial spectra

Open problem OP-SB-55 of `docs/survey/open-problems.json` (research-level;).
Target of the entry: discrete error and descent bounds for geometry-aware Tucker/DLRT training
(arXiv 2305.19059) and for CondLR (arXiv 2306.01485) "with constants independent of the smallest
singular values and of the initial conditioning", backing the numerical observations of those
papers (robustness to rank over-estimation / exponentially decaying initial spectra, Sec. 4.2 of
2305.19059 and Fig. 2 of 2306.01485), while "plain low-rank training" deteriorates.

## What is proved

**The positive half is already in the library** and is only instantiated here: the augmented
(TDLRT/DLRT/GeoLoRA) step is a projected gradient step, so `loss_truncated_projGradStep_le`
(`Training/Descent.lean`) gives its descent bound and `matrix_augmentedBug_euler_sub_euler`
(`Integrators/EulerBUG.lean`) its one-step deviation `≤ λ ‖(1 - P₀) ∇ℒ (1 - Q₀)‖` from the full
gradient step, without any singular value.  The result of this module is the **negative half for
the two other algorithms**, by an exact mechanism and an explicit example in which the constants
*cannot* be independent of the smallest singular value, and a comparison that singles out the
BUG K-step as the robust basis update.

### The mechanism (general matrices, `stiefelDir`, `stiefelStep_mul`, `projKStep_eq_kStep_add`)

The CondLR basis update is the Riemannian (Stiefel) step `U₀ - λ (I - U₀U₀ᵀ) ∇_U ℒ (S₀S₀ᵀ)⁻¹`
followed by a QR retraction.  For invertible `S₀` this direction is `(I - U₀U₀ᵀ) ∇ℒ V₀ S₀⁻¹`
(`stiefelDir_eq`), and right-multiplication by `S₀` shows that the retracted basis spans the
range of the *normal-projected* K-step `K̃₁ = U₀ S₀ - λ (I - U₀U₀ᵀ) ∇ℒ V₀`
(`stiefelStep_mul`, `capture_stiefelStep_iff`), which differs from the BUG K-step
`K₁ = U₀ S₀ - λ ∇ℒ V₀` by the tangent coefficient gradient `λ U₀ (U₀ᵀ ∇ℒ V₀)`
(`projKStep_eq_kStep_add`).  For well-conditioned `S₀` this term only re-scales the columns of
`U₀` (a gauge change of relative size `λ ‖S₀⁻¹‖ ‖∇ℒ‖`); for `σ_min(S₀) ≲ λ ‖∇ℒ‖` it changes the
subspace at order one.  Conversely, when `∇ℒ V₀V₀ᵀ = ∇ℒ`, the full gradient step is `K₁ V₀ᵀ`
(`fullStep_eq_kStep_mul`), so any basis capturing `K₁` reproduces it exactly
(`bugEuler_eq_fullStep`).

### The example (`Fin 3`, rank `2`)

`W₀ = U₀ S₀ V₀ᵀ` with `U₀ = V₀ = [e₁, e₂]`, `S₀ = diag(1, σ)` (condition number `1/σ`), target
`A = e₁e₁ᵀ + (e₂ + e₃) e₂ᵀ`, loss `ℒ(X) = ½ ‖X - A‖²` (gradient `hasFDerivAt_loss`),
`G = ∇ℒ(W₀) = W₀ - A`, full step `F = W₀ - λ G`.

* `G` has no doubly normal component (`normal_G`, `ε = 0`) and is tangent (`tangentProj_G`): the
  Riemannian step equals `F`; `F` has rank `≤ 2` (`rank_fullStep_le`); the exact gradient flow
  `W(t) = A + e^{-t}(W₀ - A)` (`hasDerivAt_flow`) has rank `≤ 2` for all `t` (`rank_flow_le`), so
  the modelling error `η` of Thm 1 of 2306.01485 vanishes and no fixed-rank method is forced to
  err.
* `bugEuler_exact`, `augmentedEuler_exact`, `augmentedEuler_sub_le`: the fixed-rank BUG step with
  Euler substeps (any bases capturing `K₁`, `L₁`) and the augmented step reproduce `F` exactly,
  for every `σ > 0`; `loss_fullStep_eq_descent`: `F` attains the DLRT descent guarantee
  `ℒ(W₀) - λ(1 - λ/2) ‖P(W₀) ∇ℒ‖²` with equality (`β = 1`).
* `stiefelStep_eq`: the CondLR Stiefel step is `[e₁, e₂ + (λ/σ) e₃]`, so the retracted basis spans
  `span(e₁, σ e₂ + λ e₃)` (`condLR_rel`, for *every* retraction and every subsequent coefficient
  update `M' = S₁ V₁ᵀ`, hence also with the singular-value clamping of CondLR).  Consequently
  (`condLR_sub_fullStep_sq_ge`, `condLR_loss_ge`)
  `‖W₁ - F‖² ≥ λ⁴ (1 - σ)² / (σ² + λ²)` and `ℒ(W₁) ≥ (λ - σ)² / (2 (σ² + λ²))`,
  both tending to their `σ = 0` values `λ²` and `½ ℒ(W₀)` as `σ → 0`: a first-order error and the
  loss of exactly half of the guaranteed descent.  `condLR_violates_descent`: for `λ = 1` the DLRT
  descent estimate fails for every CondLR-type iterate and every `σ ∈ (0, 1)`.
* `factorStep_eq`, `factor_sub_fullStep_sq_ge`, `factor_loss_ge`: plain simultaneous factor
  gradient descent (`U₀ - λ ∇_U ℒ = U₀ - λ G V₀ S₀ᵀ`) has the mirror-image defect: its basis
  direction is rotated by `O(λσ)` only, `‖W₁ - F‖² ≥ λ² (1 - σ²)² / ((1 + λσ(1 - σ))² + λ²σ²)` and
  `ℒ(W₁) ≥ (1 - λσ²)² / (2 ((1 + λσ(1 - σ))² + λ²σ²))`, again `→ λ²` and `→ ½ ℒ(W₀)`.
* `exists_condLR_basis`, `exists_bug_bases`: the capture hypotheses are satisfiable (explicit QR
  retractions `basisOf a b`).

So the three basis updates differ in the ill-conditioned regime at order one: the Stiefel step
over-rotates (`e₂ ↦ e₃`), the factor step under-rotates (`e₂ ↦ e₂`), the K-step rotates
`e₂ ↦ ((1 - λ)σ + λ) e₂ + λ e₃`, which is exact.  The lower bounds are the squared distances of
the column `(F₂₂, F₃₂) = ((1 - λ)σ + λ, λ)` from the lines through `(σ, λ)` and
`(1 + λσ(1 - σ), λσ)` (`norm_sub_sq_ge_of_rel`).

## Relation to the open problem and to the papers

* For CondLR the target statement is false as posed: the first step from an ill-conditioned
  spectrum is not an `O(λ²)`-accurate step and does not satisfy the projected-gradient descent
  bound, although `ε = η = 0`; Thm 1 of 2306.01485 requires `W̃(t) ∈ Σ_s(ε)` (bounded condition
  number along the exact flow), which fails here, and the paper's claim before Fig. 2 ("CondLR is
  not affected by the steep curvature of the low-rank manifold", citing Thm 1) is not covered by
  that theorem.  What is true is only that *after* the clamping the condition number is
  `≤ 1 + τ` (`div_le_one_add_of_mem_Icc` in `Training/Descent.lean`), so that from the second
  step on the constants depend on the scale `s - ε ∝ ‖W‖_F / √r` rather than on the initial
  conditioning; a positive bound of the form `‖W₁ - F‖ ≲ λ² ‖∇ℒ‖² / σ_min(S₀)` for the Stiefel
  step is suggested by `projKStep_eq_kStep_add` but is not formalised.
* For TDLRT/DLRT the robustness to over-estimated rank and decaying spectra is the robust-BUG
  mechanism: the basis update captures `K₁`, and the Galerkin/coefficient step is a projected
  gradient step.  Nothing new is needed beyond the library; the example shows the contrast with
  the factor step (the comparison of Sec. 4.2 of 2305.19059) in closed form.
* Numerically (throwaway script, not part of the module) the one-step bounds are attained with
  equality by CondLR for both variants of the S-step and with or without clamping, and over many
  steps CondLR recovers (it is still a descent method), while plain factor GD oscillates for
  `λ = 1/2`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpSB55

open LeanDLRA

/-! ### The Stiefel (CondLR) basis update, in general -/

section General

variable {m n k : Type*} [Fintype n] [Fintype k]

/-- `Sᵀ (S Sᵀ)⁻¹ = S⁻¹` for an invertible coefficient matrix `S`. -/
theorem transpose_mul_inv_mul_transpose [DecidableEq k] {S : Matrix k k ℝ} (hS : IsUnit S.det) :
    Sᵀ * (S * Sᵀ)⁻¹ = S⁻¹ := by
  have hSt : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSt, Matrix.one_mul]

/-- The Riemannian (Stiefel) update direction of the left basis used by CondLR
(arXiv 2306.01485, Algorithm 1): `G₁(U) = (I - U Uᵀ) ∇_U ℒ(U S Vᵀ) (S Sᵀ)⁻¹` with
`∇_U ℒ(U S Vᵀ) = ∇ℒ V Sᵀ`, where `G = ∇ℒ(U S Vᵀ)`. -/
noncomputable def stiefelDir [Fintype m] [DecidableEq m] [DecidableEq k] (U : Matrix m k ℝ)
    (S : Matrix k k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) : Matrix m k ℝ :=
  (1 - U * Uᵀ) * (G * V * Sᵀ) * (S * Sᵀ)⁻¹

/-- For invertible `S` the Stiefel direction is `(I - U Uᵀ) ∇ℒ V S⁻¹`, the right-hand side of the
Koch–Lubich factor equation `U̇ = -(I - U Uᵀ) ∇ℒ V S⁻¹`. -/
theorem stiefelDir_eq [Fintype m] [DecidableEq m] [DecidableEq k] {U : Matrix m k ℝ}
    {S : Matrix k k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ} (hS : IsUnit S.det) :
    stiefelDir U S V G = (1 - U * Uᵀ) * G * V * S⁻¹ := by
  unfold stiefelDir
  rw [← transpose_mul_inv_mul_transpose hS]
  simp only [Matrix.mul_assoc]

/-- **The Stiefel step is the normal-projected K-step.**  Right-multiplying the CondLR update
`U - λ G₁(U)` by `S` gives `U S - λ (I - U Uᵀ) ∇ℒ V`: the inverse `S⁻¹` is only a change of
coordinates, so a QR retraction of the Stiefel step spans the same space as the matrix
`K̃₁ = U S - λ (I - U Uᵀ) ∇ℒ V`. -/
theorem stiefelStep_mul [Fintype m] [DecidableEq m] [DecidableEq k] {U : Matrix m k ℝ}
    {S : Matrix k k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ} (hS : IsUnit S.det) (lr : ℝ) :
    (U - lr • stiefelDir U S V G) * S = U * S - lr • ((1 - U * Uᵀ) * G * V) := by
  rw [stiefelDir_eq hS, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ S⁻¹ S,
    Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]

/-- **What the Stiefel step discards.**  The normal-projected K-step `K̃₁` differs from the
BUG K-step `K₁ = U S - λ ∇ℒ V` (explicit Euler) by the tangent coefficient gradient
`λ U (Uᵀ ∇ℒ V)`. -/
theorem projKStep_eq_kStep_add [Fintype m] [DecidableEq m] (U : Matrix m k ℝ) (S : Matrix k k ℝ)
    (V : Matrix n k ℝ) (G : Matrix m n ℝ) (lr : ℝ) :
    U * S - lr • ((1 - U * Uᵀ) * G * V) = (U * S - lr • (G * V)) + lr • (U * (Uᵀ * G * V)) := by
  simp only [Matrix.sub_mul, Matrix.one_mul, smul_sub, Matrix.mul_assoc]
  abel

/-- A projector captures the retracted Stiefel step iff it captures `K̃₁` (for invertible `S`):
the new CondLR basis is an orthonormal basis of the range of `K̃₁`, whatever the retraction. -/
theorem capture_stiefelStep_iff [Fintype m] [DecidableEq m] [DecidableEq k] {P : Matrix m m ℝ}
    {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ}
    (hS : IsUnit S.det) (lr : ℝ) :
    P * (U - lr • stiefelDir U S V G) = U - lr • stiefelDir U S V G ↔
      P * (U * S - lr • ((1 - U * Uᵀ) * G * V)) = U * S - lr • ((1 - U * Uᵀ) * G * V) := by
  rw [← stiefelStep_mul hS]
  constructor
  · intro h; rw [← Matrix.mul_assoc, h]
  · intro h
    have := congrArg (· * S⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS] using this

/-- **The full gradient step is a K-step times `V₀ᵀ`** whenever the gradient has no right-normal
component (`∇ℒ V₀ V₀ᵀ = ∇ℒ`): `W₀ - λ ∇ℒ = (U₀ S₀ - λ ∇ℒ V₀) V₀ᵀ`. -/
theorem fullStep_eq_kStep_mul {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    {G : Matrix m n ℝ} (hG : G * (V * Vᵀ) = G) (lr : ℝ) :
    U * S * Vᵀ - lr • G = (U * S - lr • (G * V)) * Vᵀ := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc G V, hG]

/-- **Exactness of the fixed-rank BUG step with Euler substeps.**  If the gradient has no
right-normal component, any left basis capturing the K-step result `K₁ = U₀ S₀ - λ ∇ℒ V₀` and any
right projector fixing `V₀` reproduce the full gradient step exactly:
`P₁ (W₀ - λ ∇ℒ) Q₁ = W₀ - λ ∇ℒ`.  No singular value of `S₀` enters. -/
theorem bugEuler_eq_fullStep [Fintype m] {P₁ : Matrix m m ℝ} {Q₁ : Matrix n n ℝ} {U : Matrix m k ℝ}
    {S : Matrix k k ℝ} {V : Matrix n k ℝ} {G : Matrix m n ℝ} (hG : G * (V * Vᵀ) = G) (lr : ℝ)
    (hP : P₁ * (U * S - lr • (G * V)) = U * S - lr • (G * V)) (hQ : Vᵀ * Q₁ = Vᵀ) :
    P₁ * (U * S * Vᵀ - lr • G) * Q₁ = U * S * Vᵀ - lr • G := by
  rw [fullStep_eq_kStep_mul hG, ← Matrix.mul_assoc, hP, Matrix.mul_assoc, hQ]

end General

/-! ### An explicit rank-2 example: ill-conditioned initial spectrum, exact flow of rank 2 -/

section Example

/-- Two-dimensional column indices lemma: a matrix of the form `[e₁, (0, a, b)ᵀ] Z` has
`a X₂₁ = b X₁₁` (0-based indices `(2,1)`, `(1,1)`): its columns lie in `span(e₁, a e₂ + b e₃)`. -/
theorem rel_of_eq_mul (a b : ℝ) (Z : Matrix (Fin 2) (Fin 3) ℝ) :
    a * (!![1, 0; 0, a; 0, b] * Z) 2 1 = b * (!![1, 0; 0, a; 0, b] * Z) 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- If an orthonormal (or any) basis `U₁` captures a full-column-rank `3 × 2` matrix `M`
(`U₁ U₁ᵀ M = M`), then every `U₁ M'` is of the form `M Z`: the columns of `U₁ M'` lie in the
column space of `M`. -/
theorem exists_eq_mul_of_capture {M : Matrix (Fin 3) (Fin 2) ℝ} (hdet : (Mᵀ * M).det ≠ 0)
    {U₁ : Matrix (Fin 3) (Fin 2) ℝ} (hcap : U₁ * U₁ᵀ * M = M) (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    ∃ Z : Matrix (Fin 2) (Fin 3) ℝ, U₁ * M' = M * Z := by
  set R := U₁ᵀ * M with hR
  have hUR : U₁ * R = M := by rw [hR, ← Matrix.mul_assoc, hcap]
  have hRR : Rᵀ * R = Mᵀ * M := by
    rw [hR, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U₁, hcap]
  have hdetR : IsUnit R.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    apply hdet
    rw [← hRR, Matrix.det_mul, h, mul_zero]
  refine ⟨R⁻¹ * M', ?_⟩
  rw [← Matrix.mul_assoc, ← hUR, Matrix.mul_assoc U₁ R, Matrix.mul_nonsing_inv _ hdetR,
    Matrix.mul_one]

/-- **Distance from a two-dimensional column space.**  If the entries of `X` satisfy
`a X₂₁ = b X₁₁` (columns in `span(e₁, a e₂ + b e₃)`), then
`‖X - F‖² ≥ (b F₁₁ - a F₂₁)² / (a² + b²)`, the squared distance of the column `(F₁₁, F₂₁)` from
the line through `(a, b)`. -/
theorem norm_sub_sq_ge_of_rel {a b : ℝ} (hab : 0 < a ^ 2 + b ^ 2) {X F : Matrix (Fin 3) (Fin 3) ℝ}
    (hX : a * X 2 1 = b * X 1 1) :
    (b * F 1 1 - a * F 2 1) ^ 2 / (a ^ 2 + b ^ 2) ≤ ‖X - F‖ ^ 2 := by
  rw [div_le_iff₀ hab]
  have h1 : (X 1 1 - F 1 1) ^ 2 + (X 2 1 - F 2 1) ^ 2 ≤ ‖X - F‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_three, Matrix.sub_apply]
    nlinarith [sq_nonneg (X 0 0 - F 0 0), sq_nonneg (X 0 1 - F 0 1), sq_nonneg (X 0 2 - F 0 2),
      sq_nonneg (X 1 0 - F 1 0), sq_nonneg (X 1 2 - F 1 2), sq_nonneg (X 2 0 - F 2 0),
      sq_nonneg (X 2 2 - F 2 2)]
  have e : b * (X 1 1 - F 1 1) - a * (X 2 1 - F 2 1) = -(b * F 1 1 - a * F 2 1) := by
    linear_combination -hX
  have key : (b * (X 1 1 - F 1 1) - a * (X 2 1 - F 2 1)) ^ 2 ≤
      (a ^ 2 + b ^ 2) * ((X 1 1 - F 1 1) ^ 2 + (X 2 1 - F 2 1) ^ 2) := by
    nlinarith [sq_nonneg (a * (X 1 1 - F 1 1) + b * (X 2 1 - F 2 1))]
  rw [e, neg_sq] at key
  exact key.trans ((mul_le_mul_of_nonneg_left h1 hab.le).trans_eq (mul_comm _ _))

/-- The orthonormal basis `[e₁, (a e₂ + b e₃) / ‖(a, b)‖]` of `span(e₁, a e₂ + b e₃)`. -/
noncomputable def basisOf (a b : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, a / √(a ^ 2 + b ^ 2); 0, b / √(a ^ 2 + b ^ 2)]

theorem basisOf_orthonormal {a b : ℝ} (hab : 0 < a ^ 2 + b ^ 2) :
    (basisOf a b)ᵀ * basisOf a b = 1 := by
  have hs : √(a ^ 2 + b ^ 2) * √(a ^ 2 + b ^ 2) = a ^ 2 + b ^ 2 := Real.mul_self_sqrt hab.le
  have hs0 : √(a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 hab).ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [basisOf, Matrix.mul_apply, Fin.sum_univ_three]
  field_simp
  nlinarith [hs]

theorem basisOf_capture {a b : ℝ} (hab : 0 < a ^ 2 + b ^ 2) :
    basisOf a b * (basisOf a b)ᵀ * !![1, 0; 0, a; 0, b] = !![1, 0; 0, a; 0, b] := by
  have hs : √(a ^ 2 + b ^ 2) * √(a ^ 2 + b ^ 2) = a ^ 2 + b ^ 2 := Real.mul_self_sqrt hab.le
  have hs2 : √(a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hab.le
  have hs0 : √(a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 hab).ne'
  have ha : a * √(a ^ 2 + b ^ 2) ^ 2 = a * (a ^ 2 + b ^ 2) := by rw [hs2]
  have hb : b * √(a ^ 2 + b ^ 2) ^ 2 = b * (a ^ 2 + b ^ 2) := by rw [hs2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [basisOf, Matrix.mul_apply, Fin.sum_univ_three,
      Function.swap, Matrix.vecHead,
      Matrix.vecTail] <;>
    field_simp <;> nlinarith [hs, hs2, ha, hb]

/-! #### The data -/

/-- The common initial left and right basis `U₀ = V₀ = [e₁, e₂] ∈ ℝ^{3×2}`. -/
def U₀ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- The initial coefficient matrix `S₀ = diag(1, σ)`: condition number `1/σ`. -/
def S₀ (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, σ]

/-- The initial weight `W₀ = U₀ S₀ U₀ᵀ = e₁e₁ᵀ + σ e₂e₂ᵀ`. -/
def W₀ (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := U₀ * S₀ σ * U₀ᵀ

/-- The target `A = e₁e₁ᵀ + (e₂ + e₃) e₂ᵀ`, of rank `2`. -/
def A : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 1, 0]

/-- The quadratic loss `ℒ(X) = ½ ‖X - A‖²` (Frobenius norm). -/
noncomputable def loss (X : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := (1 / 2) * ‖X - A‖ ^ 2

/-- The gradient of the loss at `W₀`: `G = W₀ - A`. -/
def G (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := W₀ σ - A

/-- The full gradient step `F = W₀ - λ G`. -/
def fullStep (σ lr : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := W₀ σ - lr • G σ

theorem U₀_orthonormal : U₀ᵀ * U₀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U₀, Matrix.mul_apply, Fin.sum_univ_three,
      Function.swap]

theorem W₀_eq (σ : ℝ) : W₀ σ = !![1, 0, 0; 0, σ, 0; 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W₀, U₀, S₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem G_eq (σ : ℝ) : G σ = !![0, 0, 0; 0, σ - 1, 0; 0, -1, 0] := by
  rw [G, W₀_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp [A]

theorem fullStep_eq (σ lr : ℝ) :
    fullStep σ lr = !![1, 0, 0; 0, (1 - lr) * σ + lr, 0; 0, lr, 0] := by
  rw [fullStep, W₀_eq, G_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp
  ring

/-- `G` is the gradient of the loss at `W₀`. -/
theorem hasFDerivAt_loss (X : Matrix (Fin 3) (Fin 3) ℝ) :
    HasFDerivAt loss (innerSL ℝ (X - A)) X := by
  have h : HasFDerivAt (fun Y : Matrix (Fin 3) (Fin 3) ℝ => Y - A) (ContinuousLinearMap.id ℝ _) X :=
    (hasFDerivAt_id X).sub_const A
  have h2 := (h.norm_sq).const_mul (1 / 2 : ℝ)
  refine h2.congr_fderiv ?_
  ext Y
  simp

theorem hasFDerivAt_loss_W₀ (σ : ℝ) : HasFDerivAt loss (innerSL ℝ (G σ)) (W₀ σ) :=
  hasFDerivAt_loss _

/-- The gradient has no right-normal component: `G V₀ V₀ᵀ = G`. -/
theorem G_mul_proj (σ : ℝ) : G σ * (U₀ * U₀ᵀ) = G σ := by
  rw [G_eq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [U₀, Matrix.mul_apply, Fin.sum_univ_three,
      Function.swap, Matrix.vecHead, Matrix.vecTail]

/-- `G` has no doubly normal component: `(1 - U₀U₀ᵀ) G (1 - V₀V₀ᵀ) = 0`; the normal-component
constant `ε` of the robust BUG analysis vanishes. -/
theorem normal_G (σ : ℝ) : (1 - U₀ * U₀ᵀ) * G σ * (1 - U₀ * U₀ᵀ) = 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, G_mul_proj, sub_self, Matrix.mul_zero]

/-- `G` is tangent at `W₀`: the Riemannian gradient step coincides with the full gradient step. -/
theorem tangentProj_G (σ : ℝ) : tangentProj U₀ U₀ (G σ) = G σ := by
  have hG : G σ * U₀ * U₀ᵀ = G σ := by rw [Matrix.mul_assoc]; exact G_mul_proj σ
  rw [tangentProj_apply, hG, Matrix.mul_assoc (U₀ * U₀ᵀ * G σ), Matrix.mul_assoc (U₀ * U₀ᵀ),
    G_mul_proj, add_sub_cancel_left]

/-- The K-step result `K₁ = U₀ S₀ - λ G V₀ = [e₁, c e₂ + λ e₃]`, `c = (1 - λ)σ + λ`. -/
theorem kStep_eq (σ lr : ℝ) :
    U₀ * S₀ σ - lr • (G σ * U₀) = !![1, 0; 0, (1 - lr) * σ + lr; 0, lr] := by
  rw [G_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp [U₀, S₀]
  ring

/-- The L-step result `L₁ = V₀ S₀ᵀ - λ Gᵀ U₀ = V₀ diag(1, c)` lies in the range of `V₀`. -/
theorem lStep_eq (σ lr : ℝ) :
    U₀ * (S₀ σ)ᵀ - lr • ((G σ)ᵀ * U₀) = U₀ * !![1, 0; 0, (1 - lr) * σ + lr] := by
  rw [G_eq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [U₀, S₀, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Function.swap, Matrix.vecHead, Matrix.vecTail]
  ring

/-- The full step is `K₁ V₀ᵀ`, hence of rank `≤ 2`: it stays on the rank-2 manifold. -/
theorem rank_fullStep_le (σ lr : ℝ) : (fullStep σ lr).rank ≤ 2 := by
  rw [fullStep, W₀, fullStep_eq_kStep_mul (G_mul_proj σ)]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 2))

/-- The loss of the full step: `ℒ(F) = ½ (1 - λ)² ‖G‖² = ½ (1 - λ)² ((1 - σ)² + 1)`, which is
exactly the projected-gradient descent guarantee `ℒ(W₀) - λ(1 - λ/2) ‖P(W₀) ∇ℒ(W₀)‖²` (with
smoothness constant `β = 1`) and vanishes for `λ = 1`. -/
theorem loss_fullStep (σ lr : ℝ) :
    loss (fullStep σ lr) = (1 - lr) ^ 2 * ((1 - σ) ^ 2 + 1) / 2 := by
  rw [loss, fullStep_eq, Frobenius.norm_sq_eq_sum]
  simp [A, Fin.sum_univ_three]; ring

theorem loss_W₀ (σ : ℝ) : loss (W₀ σ) = ((1 - σ) ^ 2 + 1) / 2 := by
  rw [loss, W₀_eq, Frobenius.norm_sq_eq_sum]
  simp [A, Fin.sum_univ_three]; ring

theorem norm_sq_G (σ : ℝ) : ‖G σ‖ ^ 2 = (1 - σ) ^ 2 + 1 := by
  rw [G_eq, Frobenius.norm_sq_eq_sum]; simp [Fin.sum_univ_three]; ring

theorem loss_fullStep_eq_descent (σ lr : ℝ) :
    loss (fullStep σ lr) = loss (W₀ σ) - lr * (1 - lr / 2) * ‖tangentProj U₀ U₀ (G σ)‖ ^ 2 := by
  rw [loss_fullStep, loss_W₀, tangentProj_G, norm_sq_G]; ring

/-! #### The exact gradient flow stays on the rank-2 manifold -/

/-- The exact gradient flow `Ẇ = -(W - A)`, `W(0) = W₀`: `W(t) = A + e^{-t} (W₀ - A)`. -/
noncomputable def flow (σ t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := A + Real.exp (-t) • (W₀ σ - A)

theorem flow_zero (σ : ℝ) : flow σ 0 = W₀ σ := by simp [flow]

theorem hasDerivAt_flow (σ t : ℝ) : HasDerivAt (flow σ) (-(flow σ t - A)) t := by
  have h := (hasDerivAt_neg t).exp
  have h2 := (h.smul_const (W₀ σ - A)).const_add A
  have e : -(flow σ t - A) = (Real.exp (-t) * -1) • (W₀ σ - A) := by
    simp [flow, mul_neg, neg_smul]
  rw [e]; exact h2

/-- `W(t) = M(t) V₀ᵀ` with `M(t) = [e₁, (1 - (1 - σ) e^{-t}) e₂ + (1 - e^{-t}) e₃]`. -/
theorem flow_eq_mul (σ t : ℝ) :
    flow σ t =
      !![1, 0; 0, 1 - (1 - σ) * Real.exp (-t); 0, 1 - Real.exp (-t)] * U₀ᵀ := by
  rw [flow, W₀_eq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, U₀, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The exact gradient flow has rank `≤ 2` for all times: the problem is exactly of rank `2`
(the modelling error `η` of arXiv 2306.01485, Thm 1, is zero). -/
theorem rank_flow_le (σ t : ℝ) : (flow σ t).rank ≤ 2 := by
  rw [flow_eq_mul]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin 2))

/-! #### The full gradient step, the fixed-rank BUG step and the augmented step all coincide -/

theorem fullStep_def (σ lr : ℝ) : fullStep σ lr = U₀ * S₀ σ * U₀ᵀ - lr • G σ := rfl

theorem fullStep_mul_proj (σ lr : ℝ) : fullStep σ lr * (U₀ * U₀ᵀ) = fullStep σ lr := by
  rw [fullStep_def, Matrix.sub_mul, Matrix.smul_mul, G_mul_proj, Matrix.mul_assoc,
    ← Matrix.mul_assoc U₀ᵀ, U₀_orthonormal, Matrix.one_mul]

/-- **The fixed-rank BUG step with Euler substeps is exact.**  Any orthonormal `U₁` capturing the
K-step result `K₁ = U₀ S₀ - λ G V₀` and any `V₁` capturing the L-step result
`L₁ = V₀ S₀ᵀ - λ Gᵀ U₀` give `U₁ U₁ᵀ (W₀ - λ G) V₁ V₁ᵀ = W₀ - λ G`, for every `σ > 0`: the
ill-conditioning of `S₀` is invisible to the BUG step. -/
theorem bugEuler_exact {σ lr : ℝ} (hc : (1 - lr) * σ + lr ≠ 0) {U₁ V₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : U₁ * U₁ᵀ * (U₀ * S₀ σ - lr • (G σ * U₀)) = U₀ * S₀ σ - lr • (G σ * U₀))
    (hV : V₁ * V₁ᵀ * (U₀ * (S₀ σ)ᵀ - lr • ((G σ)ᵀ * U₀)) = U₀ * (S₀ σ)ᵀ - lr • ((G σ)ᵀ * U₀)) :
    U₁ * U₁ᵀ * fullStep σ lr * (V₁ * V₁ᵀ) = fullStep σ lr := by
  rw [lStep_eq] at hV
  have hD : IsUnit (!![1, 0; 0, (1 - lr) * σ + lr] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]; simpa using hc
  have hV₀ : V₁ * V₁ᵀ * U₀ = U₀ := by
    have := congrArg (· * (!![1, 0; 0, (1 - lr) * σ + lr] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹) hV
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD] using this
  have hQ : U₀ᵀ * (V₁ * V₁ᵀ) = U₀ᵀ := by
    have := congrArg Matrix.transpose hV₀
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [fullStep_def]
  exact bugEuler_eq_fullStep (G_mul_proj σ) lr hU hQ

/-- The augmented right basis `V̂ = V₀` captures `Gᵀ U₀`. -/
theorem capture_right (σ : ℝ) : U₀ * U₀ᵀ * ((G σ)ᵀ * U₀) = (G σ)ᵀ * U₀ := by
  have := congrArg Matrix.transpose (G_mul_proj σ)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
  rw [← Matrix.mul_assoc, this]

/-- **The augmented BUG step with Euler substeps is exact.**  With `Û = I₃` (an orthonormal basis
of `span[U₀, G V₀] = ℝ³`) and `V̂ = V₀` (which captures `Gᵀ U₀`), the augmented Galerkin step
`Û Ûᵀ (W₀ - λ G) V̂ V̂ᵀ` equals the full gradient step; the library bound
`matrix_augmentedBug_euler_sub_euler` gives the same conclusion as `≤ λ ‖(1 - P₀) G (1 - Q₀)‖ = 0`
(`augmentedEuler_sub_le`). -/
theorem augmentedEuler_exact (σ lr : ℝ) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * fullStep σ lr *
      (U₀ * U₀ᵀ) = fullStep σ lr := by
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.one_mul, fullStep_mul_proj]

theorem augmentedEuler_sub_le {σ lr : ℝ} (hlr : 0 ≤ lr) :
    ‖(1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
        (U₀ * S₀ σ * U₀ᵀ + lr • (-G σ)) * U₀ * U₀ᵀ - (U₀ * S₀ σ * U₀ᵀ + lr • (-G σ))‖ ≤
      lr * 0 := by
  have h := matrix_augmentedBug_euler_sub_euler (Ua := (1 : Matrix (Fin 3) (Fin 3) ℝ))
    (Va := U₀) U₀_orthonormal U₀_orthonormal (by simp) U₀_orthonormal (by simp)
    (by rw [Matrix.mul_assoc, U₀_orthonormal, Matrix.mul_one]) (S₀ σ)
    (-G σ) (by simp) (by rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, capture_right])
    hlr
  have hN : (1 - U₀ * U₀ᵀ) * -G σ * (1 - U₀ * U₀ᵀ) = 0 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, normal_G, neg_zero]
  rwa [hN, norm_zero] at h

/-! #### The CondLR (Stiefel) step loses the tangent coefficient gradient -/

theorem det_S₀ (σ : ℝ) : (S₀ σ).det = σ := by simp [S₀, Matrix.det_fin_two_of]

theorem isUnit_det_S₀ {σ : ℝ} (hσ : σ ≠ 0) : IsUnit (S₀ σ).det := by
  rw [det_S₀, isUnit_iff_ne_zero]; exact hσ

theorem S₀_inv {σ : ℝ} (hσ : σ ≠ 0) : (S₀ σ)⁻¹ = !![1, 0; 0, σ⁻¹] := by
  apply Matrix.inv_eq_left_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [S₀, Matrix.mul_apply, Fin.sum_univ_two, hσ]

/-- **The CondLR Stiefel step from the ill-conditioned spectrum.**  `U₀ - λ G₁(U₀) =
[e₁, e₂ + (λ/σ) e₃]`: the second basis vector is rotated by an angle `arctan(λ/σ)`, which tends
to `π/2` as `σ → 0`; the retracted basis spans `span(e₁, σ e₂ + λ e₃)`. -/
theorem stiefelStep_eq {σ : ℝ} (hσ : σ ≠ 0) (lr : ℝ) :
    U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ) = !![1, 0; 0, 1; 0, lr / σ] := by
  rw [stiefelDir_eq (isUnit_det_S₀ hσ), S₀_inv hσ, G_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U₀, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Function.swap, Matrix.vecHead, Matrix.vecTail]
  field_simp

theorem det_gram_stiefel (σ lr : ℝ) :
    ((!![1, 0; 0, 1; 0, lr / σ] : Matrix (Fin 3) (Fin 2) ℝ)ᵀ *
      !![1, 0; 0, 1; 0, lr / σ]).det ≠ 0 := by
  have : (!![1, 0; 0, 1; 0, lr / σ] : Matrix (Fin 3) (Fin 2) ℝ)ᵀ * !![1, 0; 0, 1; 0, lr / σ] =
      !![1, 0; 0, 1 + (lr / σ) ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]; ring
  rw [this, Matrix.det_fin_two_of]
  simp only [one_mul, mul_zero, sub_zero]
  positivity

/-- **Column relation of every CondLR-type iterate.**  If `U₁` is a (retracted) basis capturing the
Stiefel step, then every `W₁ = U₁ M'` (any coefficient update `M' = S₁ V₁ᵀ`, including the
singular-value clamping of CondLR and any choice of `V₁`) satisfies `σ (W₁)₃₂ = λ (W₁)₂₂`
(1-based indices): its columns lie in `span(e₁, σ e₂ + λ e₃)`. -/
theorem condLR_rel {σ lr : ℝ} (hσ : σ ≠ 0) {U₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) =
      U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    σ * (U₁ * M') 2 1 = lr * (U₁ * M') 1 1 := by
  rw [stiefelStep_eq hσ] at hcap
  obtain ⟨Z, hZ⟩ := exists_eq_mul_of_capture (det_gram_stiefel σ lr) hcap M'
  rw [hZ]
  have h := rel_of_eq_mul 1 (lr / σ) Z
  rw [one_mul] at h
  rw [h]; field_simp

/-- **CondLR is not robust to the ill-conditioned initial spectrum (error).**  For every
retracted Stiefel basis `U₁` and every coefficient update `M'`, the CondLR iterate `W₁ = U₁ M'`
deviates from the full gradient step (= Riemannian step = BUG step = augmented step) by
`‖W₁ - F‖² ≥ λ⁴ (1 - σ)² / (σ² + λ²)`, which tends to `λ²` as `σ → 0` at fixed `λ`: a
first-order error, although `∇ℒ(W₀)` is tangent (`ε = 0`) and the exact flow has rank `2`
(`η = 0`).  The constant cannot be made independent of `σ_min(S₀) = σ`: for `σ ≥ λ`
the bound is `O(λ³/σ)`, for `σ ≪ λ` it is `Θ(λ²)`. -/
theorem condLR_sub_fullStep_sq_ge {σ lr : ℝ} (hσ : 0 < σ) (hlr : 0 < lr)
    {U₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) =
      U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    lr ^ 4 * (1 - σ) ^ 2 / (σ ^ 2 + lr ^ 2) ≤ ‖U₁ * M' - fullStep σ lr‖ ^ 2 := by
  have hab : 0 < σ ^ 2 + lr ^ 2 := by positivity
  have h := norm_sub_sq_ge_of_rel hab (F := fullStep σ lr) (condLR_rel hσ.ne' hcap M')
  have e1 : fullStep σ lr 1 1 = (1 - lr) * σ + lr := by simp [fullStep_eq]
  have e2 : fullStep σ lr 2 1 = lr := by simp [fullStep_eq]
  rw [e1, e2] at h
  convert h using 2; ring

/-- **CondLR is not robust to the ill-conditioned initial spectrum (descent).**  Every
CondLR-type iterate has loss `ℒ(W₁) ≥ (λ - σ)² / (2 (σ² + λ²))`, which tends to `½ = ½ ℒ(W₀)` as
`σ → 0`, whereas the full/Riemannian/BUG/augmented step has `ℒ(F) = ½ (1 - λ)² ((1 - σ)² + 1)`:
the Stiefel step can only fix the normal component of the gradient and loses the tangent
coefficient part, which carries half of `‖∇ℒ(W₀)‖²`. -/
theorem condLR_loss_ge {σ lr : ℝ} (hσ : 0 < σ) (hlr : 0 < lr) {U₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) =
      U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    (lr - σ) ^ 2 / (2 * (σ ^ 2 + lr ^ 2)) ≤ loss (U₁ * M') := by
  have hab : 0 < σ ^ 2 + lr ^ 2 := by positivity
  have h := norm_sub_sq_ge_of_rel hab (F := A) (condLR_rel hσ.ne' hcap M')
  have e1 : A 1 1 = 1 := by simp [A]
  have e2 : A 2 1 = 1 := by simp [A]
  rw [e1, e2] at h
  have h' : (lr - σ) ^ 2 / (σ ^ 2 + lr ^ 2) ≤ ‖U₁ * M' - A‖ ^ 2 := by convert h using 2; ring
  rw [loss]
  calc (lr - σ) ^ 2 / (2 * (σ ^ 2 + lr ^ 2)) = 1 / 2 * ((lr - σ) ^ 2 / (σ ^ 2 + lr ^ 2)) := by
        rw [div_mul_div_comm, one_mul]
    _ ≤ 1 / 2 * ‖U₁ * M' - A‖ ^ 2 := by gcongr

/-- **The DLRT descent guarantee fails for CondLR.**  With `λ = 1` the projected-gradient descent
estimate `ℒ(W₁) ≤ ℒ(W₀) - λ (1 - λ/2) ‖P(W₀) ∇ℒ(W₀)‖²` (smoothness `β = 1`; the right-hand side
is `ℒ(F) = 0`, see `loss_fullStep_eq_descent`) is violated by every CondLR-type iterate, for
every `σ ∈ (0, 1)`. -/
theorem condLR_violates_descent {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U₁ : Matrix (Fin 3) (Fin 2) ℝ}
    (hcap : U₁ * U₁ᵀ * (U₀ - (1 : ℝ) • stiefelDir U₀ (S₀ σ) U₀ (G σ)) =
      U₀ - (1 : ℝ) • stiefelDir U₀ (S₀ σ) U₀ (G σ)) (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    loss (W₀ σ) - 1 * (1 - 1 / 2) * ‖tangentProj U₀ U₀ (G σ)‖ ^ 2 < loss (U₁ * M') := by
  rw [← loss_fullStep_eq_descent, loss_fullStep]
  refine lt_of_lt_of_le ?_ (condLR_loss_ge hσ one_pos hcap M')
  have : 0 < (1 - σ) ^ 2 / (2 * (σ ^ 2 + 1 ^ 2)) := by
    have : 0 < 1 - σ := by linarith
    positivity
  simpa using this

/-- An instance: the hypotheses of the CondLR theorems are satisfiable (the QR retraction of the
Stiefel step is `basisOf 1 (λ/σ)`, an orthonormal basis of `span(e₁, e₂ + (λ/σ) e₃)`). -/
theorem exists_condLR_basis {σ lr : ℝ} (hσ : σ ≠ 0) :
    ∃ U₁ : Matrix (Fin 3) (Fin 2) ℝ, U₁ᵀ * U₁ = 1 ∧
      U₁ * U₁ᵀ * (U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ)) =
        U₀ - lr • stiefelDir U₀ (S₀ σ) U₀ (G σ) := by
  have hab : 0 < (1 : ℝ) ^ 2 + (lr / σ) ^ 2 := by positivity
  refine ⟨basisOf 1 (lr / σ), basisOf_orthonormal hab, ?_⟩
  rw [stiefelStep_eq hσ]
  exact basisOf_capture hab

/-- An instance for the BUG step: `U₁ = basisOf c λ` captures `K₁` and `V₁ = V₀` captures `L₁`. -/
theorem exists_bug_bases {σ lr : ℝ} (hc : (1 - lr) * σ + lr ≠ 0) :
    ∃ U₁ V₁ : Matrix (Fin 3) (Fin 2) ℝ, U₁ᵀ * U₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧
      U₁ * U₁ᵀ * (U₀ * S₀ σ - lr • (G σ * U₀)) = U₀ * S₀ σ - lr • (G σ * U₀) ∧
      V₁ * V₁ᵀ * (U₀ * (S₀ σ)ᵀ - lr • ((G σ)ᵀ * U₀)) = U₀ * (S₀ σ)ᵀ - lr • ((G σ)ᵀ * U₀) := by
  have hab : 0 < ((1 - lr) * σ + lr) ^ 2 + lr ^ 2 := by
    have : 0 < ((1 - lr) * σ + lr) ^ 2 := by positivity
    positivity
  refine ⟨basisOf ((1 - lr) * σ + lr) lr, U₀, basisOf_orthonormal hab, U₀_orthonormal, ?_, ?_⟩
  · rw [kStep_eq]; exact basisOf_capture hab
  · rw [lStep_eq, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, U₀_orthonormal, Matrix.one_mul]

/-! #### Plain factorised gradient descent freezes the ill-conditioned direction -/

/-- **The factor-GD basis update.**  Simultaneous gradient descent on the factors moves `U₀` by
`-λ ∇_U ℒ = -λ G V₀ S₀ᵀ`, giving `[e₁, (1 + λσ(1 - σ)) e₂ + λσ e₃]`: the second direction is
rotated by an angle `O(λσ)` only (the factor gradient is scaled by `σ`). -/
theorem factorStep_eq (σ lr : ℝ) :
    U₀ - lr • (G σ * U₀ * (S₀ σ)ᵀ) = !![1, 0; 0, 1 + lr * σ * (1 - σ); 0, lr * σ] := by
  rw [G_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U₀, S₀,
        Function.swap, Matrix.vecHead, Matrix.vecTail]
  ring

/-- **Plain factor GD is not robust either (error).**  Every iterate
`W₁ = (U₀ - λ ∇_U ℒ) M'` (any `S₁`, `V₁`) satisfies
`‖W₁ - F‖² ≥ λ² (1 - σ²)² / ((1 + λσ(1 - σ))² + λ²σ²)`, which tends to `λ²` as `σ → 0`. -/
theorem factor_sub_fullStep_sq_ge {σ lr : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hlr : 0 ≤ lr)
    (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    lr ^ 2 * (1 - σ ^ 2) ^ 2 / ((1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2) ≤
      ‖(U₀ - lr • (G σ * U₀ * (S₀ σ)ᵀ)) * M' - fullStep σ lr‖ ^ 2 := by
  have ha : 0 < 1 + lr * σ * (1 - σ) := by
    have : 0 ≤ lr * σ * (1 - σ) := by
      have : 0 ≤ 1 - σ := by linarith
      positivity
    linarith
  have hab : 0 < (1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2 := by positivity
  rw [factorStep_eq]
  have h := norm_sub_sq_ge_of_rel hab (F := fullStep σ lr)
    (rel_of_eq_mul (1 + lr * σ * (1 - σ)) (lr * σ) M')
  have e1 : fullStep σ lr 1 1 = (1 - lr) * σ + lr := by simp [fullStep_eq]
  have e2 : fullStep σ lr 2 1 = lr := by simp [fullStep_eq]
  rw [e1, e2] at h
  convert h using 2; ring

/-- **Plain factor GD is not robust either (descent).**  Every factor-GD iterate has
`ℒ(W₁) ≥ (1 - λσ²)² / (2 ((1 + λσ(1 - σ))² + λ²σ²))`, which tends to `½ = ½ ℒ(W₀)` as `σ → 0`:
the frozen basis direction `e₂` cannot acquire the `e₃` component of the target. -/
theorem factor_loss_ge {σ lr : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hlr : 0 ≤ lr)
    (M' : Matrix (Fin 2) (Fin 3) ℝ) :
    (1 - lr * σ ^ 2) ^ 2 / (2 * ((1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2)) ≤
      loss ((U₀ - lr • (G σ * U₀ * (S₀ σ)ᵀ)) * M') := by
  have ha : 0 < 1 + lr * σ * (1 - σ) := by
    have : 0 ≤ lr * σ * (1 - σ) := by
      have : 0 ≤ 1 - σ := by linarith
      positivity
    linarith
  have hab : 0 < (1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2 := by positivity
  rw [factorStep_eq]
  have h := norm_sub_sq_ge_of_rel hab (F := A)
    (rel_of_eq_mul (1 + lr * σ * (1 - σ)) (lr * σ) M')
  have e1 : A 1 1 = 1 := by simp [A]
  have e2 : A 2 1 = 1 := by simp [A]
  rw [e1, e2] at h
  have h' : (1 - lr * σ ^ 2) ^ 2 / ((1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2) ≤
      ‖!![1, 0; 0, 1 + lr * σ * (1 - σ); 0, lr * σ] * M' - A‖ ^ 2 := by
    convert h using 2; ring
  rw [loss]
  calc (1 - lr * σ ^ 2) ^ 2 / (2 * ((1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2)) =
        1 / 2 * ((1 - lr * σ ^ 2) ^ 2 / ((1 + lr * σ * (1 - σ)) ^ 2 + (lr * σ) ^ 2)) := by
        rw [div_mul_div_comm, one_mul]
    _ ≤ 1 / 2 * ‖!![1, 0; 0, 1 + lr * σ * (1 - σ); 0, lr * σ] * M' - A‖ ^ 2 := by gcongr

end Example

end LeanDLRA.Novel.OpSB55
