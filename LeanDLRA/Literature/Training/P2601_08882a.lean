import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Classical.SVD
import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.OneSided

/-!
# DLRT for compressing vision transformers: arXiv 2601.08882, Sec. 2

Snyder, Yang, Schnake, Schotthöfer, *Compressing Vision Transformers in Geospatial Transfer
Learning with Manifold-Constrained Optimization*, recall in their Sec. 2 the method DLRT and its
guarantees, quoted from GeoLoRA (arXiv 2410.18720, Thms 1-3).  This module formalizes that section
on real matrices with the Frobenius inner product, at the level of the factors, and shows that three
of the printed statements are false as they stand and how to correct them.

**The step.**  `IsDLRTStep` is one step for a layer `W = U S Vᵀ`: basis augmentation, the latent
iterations eq. (2) from `Ŝ₀ = Ûᵀ U S Vᵀ V̂`, and a truncated SVD with singular value threshold `ϑ`.
Nothing about the geometry is assumed: `hasFDerivAt_loss_U`, `_V`, `_S` derive `∇_U L`, `∇_V L`,
`∇_Ŝ L`; `IsDLRTStep.start_eq` is the exact start; `IsDLRTStep.What_succ` writes eq. (2) as a
projected gradient step; `IsDLRTStep.capture` proves from the augmentation and `rank S = r` that the
latent space contains the tangent gradient; `norm_next_sub_What` computes the truncation error from
the SVD; `next_valid` shows that the step lands on a manifold `M_{r₁}`.  Steps and trajectories
exist (`exists_step`, `exists_trajectory`, `exists_truncSVD`).

**Loss descent and stationarity, deterministic.**  `loss_dlrtStep_le`, `liminf_tangentGrad_sq`, for
any number `s⋆ ≥ 1` of local iterations.

**Loss descent and stationarity, with mini-batches.**  The paper prints
`E L(W_{t+1}) ≤ L(W_t) - λ (1 - L λ² / 2) E‖P ∇L(W_t, ξ_t)‖² + L E‖W_{t+1} - Û S̃ V̂ᵀ‖` and
`liminf E‖P ∇L(W_t, ξ_t)‖² = 0`.  Three things go wrong.
* `printed_coefficient_false`: the coefficient `L λ² / 2` is a misprint for `L λ / 2`, false even
  without noise.
* `fresh_batch_descent_false`: with `L λ / 2`, the inequality is still false for a batch independent
  of the loss on the left, since `E‖∇L(W, ξ)‖²` contains the variance.  The cited proof applies the
  descent lemma with one symbol for the gradient of `L` and for the batch gradient.  What it proves
  is `sameBatch_loss_descent`, with the loss on the left evaluated on the batch just used.
  The correct statement for the population loss is `IsStochasticDLRT.expected_loss_descent`: the
  norm contains the population gradient and there is a term `β λ² σ² / 2`.
* `not_stationarity_of_batch_gradient`: the printed stationarity is false for i.i.d. batches,
  whereas `IsStochasticDLRT.liminf_expected_tangentGrad_sq` holds with the population gradient: on
  one and the same run (`coin_isStochastic`) the two limits inferior are `0` and `1`.

**Error against the gradient flow.**  `dlrt_error_finite_time` and `dlrt_error_le_constants` are the
printed bound `c₁ ε + c₂ λ + c₃ ϑ / λ`, with constants depending only on `β`, `B`, `T`, not on
singular values, for `s⋆ ≥ 1` local iterations, and `gradientFlow_sub_riemannianFlow_le` compares
the two flows.  The claim that the constants do not depend on time is false:
`not_timeUniform_error`, for a loss satisfying all assumptions, with constants uniform in the
initial value, and `not_timeUniform_error_of_fixed_start`, for a fixed initial value and a loss
unbounded below.  It is true for strongly convex losses: `dlrt_error_time_uniform`,
`dlrt_error_time_uniform_constants`, with `timeUniform_instance`.

**Scope and differences from the paper.**  The stochastic statements have one local iteration per
step, `s⋆ = 1`, as the cited proof; the bases are built from the full gradient, as printed, and
must be known before the batch of the step is drawn.  The expectation is a Bochner integral over an
arbitrary filtered probability space, and measurability of the iterates is a hypothesis
(`IsStochasticDLRT`), satisfied in `coin_isStochastic`; mini-batch expectations over two batches in
the counterexamples are the finite averages `avg`.  The letter `L` of the paper is split into the
Lipschitz constant `β` of the gradient and the bound `G` of the gradient.  Sec. 3 (experiments) and
the regularizer `R` of the paper are not treated.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2601_08882

open Matrix

/-! ### The objects of Sec. 2: low-rank states and the data of one DLRT step -/

/-- A low-rank state: the factors `U`, `S`, `V` of the weight matrix `W = U S Vᵀ`. -/
structure LRState (m n : Type*) where
  /-- The number of columns of the factors. -/
  rank : ℕ
  /-- The left basis. -/
  U : Matrix m (Fin rank) ℝ
  /-- The coefficient matrix. -/
  S : Matrix (Fin rank) (Fin rank) ℝ
  /-- The right basis. -/
  V : Matrix n (Fin rank) ℝ

/-- The internal data of one DLRT step: the augmented bases `Û`, `V̂`, the latent iterates `Ŝ_s` of
eq. (2), and an SVD of `S̃ = Ŝ_{s⋆}` split into the kept part (`k` singular values, factors `P₁`,
`Q₁`) and the discarded part (`d` singular values, factors `P₂`, `Q₂`). -/
structure StepData (m n : Type*) where
  /-- Number of columns of `Û` (`2 r` in the paper). -/
  a : ℕ
  /-- Number of columns of `V̂` (`2 r` in the paper). -/
  b : ℕ
  /-- The new rank `r₁`. -/
  k : ℕ
  /-- The number of discarded singular values. -/
  d : ℕ
  /-- The augmented left basis `Û`. -/
  Uhat : Matrix m (Fin a) ℝ
  /-- The augmented right basis `V̂`. -/
  Vhat : Matrix n (Fin b) ℝ
  /-- The latent coefficient iterates `Ŝ_s`. -/
  Shat : ℕ → Matrix (Fin a) (Fin b) ℝ
  /-- Left singular vectors that are kept. -/
  P₁ : Matrix (Fin a) (Fin k) ℝ
  /-- Right singular vectors that are kept. -/
  Q₁ : Matrix (Fin b) (Fin k) ℝ
  /-- Singular values that are kept. -/
  σ₁ : Fin k → ℝ
  /-- Left singular vectors that are discarded. -/
  P₂ : Matrix (Fin a) (Fin d) ℝ
  /-- Right singular vectors that are discarded. -/
  Q₂ : Matrix (Fin b) (Fin d) ℝ
  /-- Singular values that are discarded. -/
  σ₂ : Fin d → ℝ

variable {m n : Type*} [Fintype m] [Fintype n]

namespace LRState

/-- The weight matrix `W = U S Vᵀ`. -/
def W (X : LRState m n) : Matrix m n ℝ := X.U * X.S * X.Vᵀ

/-- The tangent projector `P_{M_r}` at `W = U S Vᵀ`:
`Z ↦ U Uᵀ Z + Z V Vᵀ - U Uᵀ Z V Vᵀ`. -/
noncomputable def P (X : LRState m n) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  tangentProj X.U X.V

/-- `X` is a point of the manifold `M_r`, `r = X.rank`: orthonormal bases and `rank S = r`. -/
structure IsValid (X : LRState m n) : Prop where
  orthU : X.Uᵀ * X.U = 1
  orthV : X.Vᵀ * X.V = 1
  invS : IsUnit X.S.det

/-- A valid state has rank exactly `r`: it lies on the manifold `M_r` of arXiv 2601.08882, Sec. 2.
-/
theorem IsValid.rank_W {X : LRState m n} (h : X.IsValid) : X.W.rank = X.rank :=
  (SVD.rank_eq_iff_exists_factor X.W).2 ⟨X.U, X.S, X.V, h.orthU, h.orthV, h.invS, rfl⟩

/-- `P_{M_r}` is an orthogonal projector (arXiv 2601.08882, Sec. 2). -/
theorem IsValid.isOrthProj_P {X : LRState m n} (h : X.IsValid) : IsOrthProj X.P :=
  isOrthProj_tangentProj h.orthU h.orthV

end LRState

namespace StepData

/-- The Galerkin projector onto the latent space `S = {Û Z V̂ᵀ}` of eq. (1):
`Z ↦ Û Ûᵀ Z V̂ V̂ᵀ`. -/
noncomputable def gal (D : StepData m n) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  leftProj D.Uhat * rightProj D.Vhat

/-- The latent iterate as a weight matrix: `Û Ŝ_s V̂ᵀ`.  For `s = s⋆` this is `Û S̃ V̂ᵀ`. -/
def What (D : StepData m n) (s : ℕ) : Matrix m n ℝ := D.Uhat * D.Shat s * D.Vhatᵀ

/-- The state after truncation: `U₁ = Û P₁`, `S₁ = diag(σ₁)`, `V₁ = V̂ Q₁`. -/
noncomputable def next (D : StepData m n) : LRState m n :=
  ⟨D.k, D.Uhat * D.P₁, diagonal D.σ₁, D.Vhat * D.Q₁⟩

lemma gal_apply (D : StepData m n) (Z : Matrix m n ℝ) :
    D.gal Z = D.Uhat * (D.Uhatᵀ * Z * D.Vhat) * D.Vhatᵀ := by
  simp [gal, Matrix.mul_assoc]

end StepData

/-- A truncated singular value decomposition of `A`: `A = P₁ diag(σ₁) Q₁ᵀ + P₂ diag(σ₂) Q₂ᵀ`
with `[P₁ | P₂]`, `[Q₁ | Q₂]` orthonormal, the kept singular values positive, the discarded ones
the smallest, and `‖σ₂‖₂ < ϑ`, the singular value threshold of Sec. 2. -/
structure IsTruncSVD {a b k d : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (ϑ : ℝ)
    (P₁ : Matrix (Fin a) (Fin k) ℝ) (Q₁ : Matrix (Fin b) (Fin k) ℝ) (σ₁ : Fin k → ℝ)
    (P₂ : Matrix (Fin a) (Fin d) ℝ) (Q₂ : Matrix (Fin b) (Fin d) ℝ) (σ₂ : Fin d → ℝ) : Prop where
  orthP₁ : P₁ᵀ * P₁ = 1
  orthQ₁ : Q₁ᵀ * Q₁ = 1
  orthP₂ : P₂ᵀ * P₂ = 1
  orthQ₂ : Q₂ᵀ * Q₂ = 1
  crossP : P₁ᵀ * P₂ = 0
  crossQ : Q₁ᵀ * Q₂ = 0
  pos₁ : ∀ i, 0 < σ₁ i
  nonneg₂ : ∀ j, 0 ≤ σ₂ j
  ordered : ∀ i j, σ₂ j ≤ σ₁ i
  svd : A = P₁ * diagonal σ₁ * Q₁ᵀ + P₂ * diagonal σ₂ * Q₂ᵀ
  tail : √(∑ j, σ₂ j ^ 2) < ϑ

/-- **One DLRT step** (arXiv 2601.08882, Sec. 2), from the state `X` with gradient information
`G₀`, S-step field `f`, learning rate `lr`, `s⋆` local iterations and truncation tolerance `ϑ`.

* `X` lies on the manifold (orthonormal bases, `rank S = r`).
* Basis augmentation: `Û`, `V̂` have orthonormal columns and their ranges contain
  `[U | ∇_U L]` and `[V | ∇_V L]`, where `∇_U L = G₀ V Sᵀ` and `∇_V L = G₀ᵀ U S` by the chain rule
  (`hasFDerivAt_loss_U`, `hasFDerivAt_loss_V`).  The paper's `orth([U | ∇_U L])` is the special
  case of equality of ranges; only the inclusion is required here.
* Latent training: `Ŝ₀ = Ûᵀ U S Vᵀ V̂` and eq. (2), `Ŝ_{s+1} = Ŝ_s - lr Ûᵀ f(Û Ŝ_s V̂ᵀ) V̂`, for
  `s < s⋆`, where `Ûᵀ ∇_W L V̂ = ∇_Ŝ L` (`hasFDerivAt_loss_S`).
* Truncation: an SVD of `S̃ = Ŝ_{s⋆}` whose discarded singular values have `ℓ²`-norm `< ϑ`.

The deterministic scheme is `G₀ = ∇L(W)`, `f = ∇L`.  Sec. 2 writes the augmentation with the full
gradient and the S-step with SGD: this is `G₀ = ∇L(W)` and `f` a mini-batch gradient. -/
structure IsDLRTStep (G₀ : Matrix m n ℝ) (f : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (sStar : ℕ)
    (ϑ : ℝ) (X : LRState m n) (D : StepData m n) : Prop where
  valid : X.IsValid
  orthUhat : D.Uhatᵀ * D.Uhat = 1
  orthVhat : D.Vhatᵀ * D.Vhat = 1
  spanU : D.Uhat * D.Uhatᵀ * X.U = X.U
  spanV : D.Vhat * D.Vhatᵀ * X.V = X.V
  spanGU : D.Uhat * D.Uhatᵀ * (G₀ * X.V * X.Sᵀ) = G₀ * X.V * X.Sᵀ
  spanGV : D.Vhat * D.Vhatᵀ * (G₀ᵀ * X.U * X.S) = G₀ᵀ * X.U * X.S
  start : D.Shat 0 = D.Uhatᵀ * X.U * X.S * X.Vᵀ * D.Vhat
  iter : ∀ s < sStar, D.Shat (s + 1) = D.Shat s - lr • (D.Uhatᵀ * f (D.What s) * D.Vhat)
  trunc : IsTruncSVD (D.Shat sStar) ϑ D.P₁ D.Q₁ D.σ₁ D.P₂ D.Q₂ D.σ₂

/-! ### Gradients with respect to the factors -/

section Gradients

variable {ℒ : Matrix m n ℝ → ℝ}

private lemma hasFDerivAt_comp_clm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →L[ℝ] F) {ℓ : F → ℝ} {G : F} {G' : E}
    {x : E} (h : HasFDerivAt ℓ (innerSL ℝ G) (L x)) (hadj : ∀ H, ⟪G, L H⟫ = ⟪G', H⟫) :
    HasFDerivAt (fun y => ℓ (L y)) (innerSL ℝ G') x := by
  refine (h.comp x L.hasFDerivAt).congr_fderiv ?_
  ext H
  simp [hadj]

/-- **`∇_U L = ∇_W L V Sᵀ`** (arXiv 2601.08882, Sec. 2, basis augmentation): the gradient of
`U' ↦ L(U' S Vᵀ)` at `U`, in the Frobenius inner product. -/
theorem hasFDerivAt_loss_U {r : Type*} [Fintype r] {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} {G : Matrix m n ℝ} (h : HasFDerivAt ℒ (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun U' : Matrix m r ℝ => ℒ (U' * S * Vᵀ)) (innerSL ℝ (G * V * Sᵀ)) U := by
  have e : (fun U' : Matrix m r ℝ => ℒ (U' * S * Vᵀ)) =
      fun U' => ℒ (Frobenius.rightMulCLM (S * Vᵀ) U') := by
    funext U'; simp [Matrix.mul_assoc]
  rw [e]
  refine hasFDerivAt_comp_clm _ (by simpa [Matrix.mul_assoc] using h) fun H => ?_
  simp only [Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_right']
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **`∇_V L = (∇_W L)ᵀ U S`** (arXiv 2601.08882, Sec. 2, basis augmentation): the gradient of
`V' ↦ L(U S V'ᵀ)` at `V`, in the Frobenius inner product. -/
theorem hasFDerivAt_loss_V {r : Type*} [Fintype r] {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} {G : Matrix m n ℝ} (h : HasFDerivAt ℒ (innerSL ℝ G) (U * S * Vᵀ)) :
    HasFDerivAt (fun V' : Matrix n r ℝ => ℒ (U * S * V'ᵀ)) (innerSL ℝ (Gᵀ * U * S)) V := by
  have e : (fun V' : Matrix n r ℝ => ℒ (U * S * V'ᵀ)) =
      fun V' => ℒ ((Frobenius.leftMulCLM (U * S)).comp Frobenius.transposeCLM V') := by
    funext V'; simp [Frobenius.transposeCLM]
  rw [e]
  refine hasFDerivAt_comp_clm _ (by simpa [Frobenius.transposeCLM] using h) fun H => ?_
  simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply]
  rw [Frobenius.inner_mul_left', show Frobenius.transposeCLM H = Hᵀ from rfl,
    ← Frobenius.inner_transpose]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- **`∇_Ŝ L = Ûᵀ ∇_W L V̂`** (arXiv 2601.08882, Sec. 2, latent space training): the gradient of
`Z ↦ L(Û Z V̂ᵀ)`, in the Frobenius inner product. -/
theorem hasFDerivAt_loss_S {a b : Type*} [Fintype a] [Fintype b] {Uh : Matrix m a ℝ}
    {Vh : Matrix n b ℝ} {Z : Matrix a b ℝ} {G : Matrix m n ℝ}
    (h : HasFDerivAt ℒ (innerSL ℝ G) (Uh * Z * Vhᵀ)) :
    HasFDerivAt (fun Z' : Matrix a b ℝ => ℒ (Uh * Z' * Vhᵀ)) (innerSL ℝ (Uhᵀ * G * Vh)) Z := by
  have e : (fun Z' : Matrix a b ℝ => ℒ (Uh * Z' * Vhᵀ)) =
      fun Z' => ℒ ((Frobenius.leftMulCLM Uh).comp (Frobenius.rightMulCLM Vhᵀ) Z') := by
    funext Z'; simp [Matrix.mul_assoc]
  rw [e]
  refine hasFDerivAt_comp_clm _ (by simpa [Matrix.mul_assoc] using h) fun H => ?_
  simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
    Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_left', Frobenius.inner_mul_right']
  simp [Matrix.mul_assoc]

end Gradients

/-! ### The step: exact start, Galerkin form, tangent capture, truncation -/

namespace IsDLRTStep

variable {G₀ : Matrix m n ℝ} {f : Matrix m n ℝ → Matrix m n ℝ} {lr ϑ : ℝ} {sStar : ℕ}
  {X : LRState m n} {D : StepData m n}

/-- The Galerkin projector onto the latent space (arXiv 2601.08882, eq. (1)) is an orthogonal
projector. -/
theorem isOrthProj_gal (h : IsDLRTStep G₀ f lr sStar ϑ X D) : IsOrthProj D.gal :=
  isOrthProj_leftProj_mul_rightProj h.orthUhat h.orthVhat

private lemma V_mul (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    X.Vᵀ * (D.Vhat * D.Vhatᵀ) = X.Vᵀ := by
  have := congrArg transpose h.spanV
  simpa [transpose_mul, Matrix.mul_assoc] using this

/-- **Exact start** (arXiv 2601.08882, Sec. 2): `Û Ŝ₀ V̂ᵀ = W`, since the augmented ranges
contain `U` and `V`.  Abstract form: `IsRankAdaptiveBUGStep.start_eq`. -/
theorem start_eq (h : IsDLRTStep G₀ f lr sStar ϑ X D) : D.What 0 = X.W := by
  calc D.What 0 = D.Uhat * (D.Uhatᵀ * X.U * X.S * X.Vᵀ * D.Vhat) * D.Vhatᵀ := by
        rw [StepData.What, h.start]
    _ = (D.Uhat * D.Uhatᵀ * X.U) * X.S * (X.Vᵀ * (D.Vhat * D.Vhatᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = X.W := by rw [h.spanU, h.V_mul]; rfl

/-- **The latent iteration is a projected gradient step on `W`** (arXiv 2601.08882, Sec. 2):
eq. (2) reads `Û Ŝ_{s+1} V̂ᵀ = Û Ŝ_s V̂ᵀ - lr Π f(Û Ŝ_s V̂ᵀ)` with the Galerkin projector
`Π = Û Ûᵀ (·) V̂ V̂ᵀ`. -/
theorem What_succ (h : IsDLRTStep G₀ f lr sStar ϑ X D) {s : ℕ} (hs : s < sStar) :
    D.What (s + 1) = projGradStep D.gal f lr (D.What s) := by
  rw [projGradStep, StepData.gal_apply]
  conv_lhs => rw [StepData.What, h.iter s hs]
  simp [StepData.What, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Basis augmentation captures the matrix `G₀ V`: its columns lie in the range of `Û`.  Uses the
invertibility of `S`. -/
private lemma A_GV (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    D.Uhat * D.Uhatᵀ * (G₀ * X.V) = G₀ * X.V := by
  have hdet : IsUnit X.Sᵀ.det := by rw [det_transpose]; exact h.valid.invS
  have := congrArg (· * X.Sᵀ⁻¹) h.spanGU
  simpa [Matrix.mul_assoc, mul_nonsing_inv _ hdet] using this

/-- Basis augmentation captures `G₀ᵀ U`.  Uses the invertibility of `S`. -/
private lemma B_GU (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    X.Uᵀ * G₀ * (D.Vhat * D.Vhatᵀ) = X.Uᵀ * G₀ := by
  have hdet : IsUnit X.S.det := h.valid.invS
  have h1 := congrArg (· * X.S⁻¹) h.spanGV
  have h2 : D.Vhat * D.Vhatᵀ * (G₀ᵀ * X.U) = G₀ᵀ * X.U := by
    simpa [Matrix.mul_assoc, mul_nonsing_inv _ hdet] using h1
  have := congrArg transpose h2
  simpa [transpose_mul, Matrix.mul_assoc] using this

/-- **Tangent capture** (arXiv 2601.08882, Sec. 2, "careful construction of the tangent space
during the augmentation step"): the latent space contains the tangent gradient,
`Π P_{M_r} G₀ = P_{M_r} G₀`, for `rank S = r`.  The paper describes the latent space as a subspace
of the tangent plane; what the descent analysis uses, and what is proved here, is that the latent
space contains the tangent gradient. -/
theorem capture (h : IsDLRTStep G₀ f lr sStar ϑ X D) : D.gal (X.P G₀) = X.P G₀ := by
  have hU := h.spanU
  have hV := h.V_mul
  have hA := h.A_GV
  have hB := h.B_GU
  set A := D.Uhat * D.Uhatᵀ with hAdef
  set B := D.Vhat * D.Vhatᵀ with hBdef
  have hgal : ∀ Z, D.gal Z = A * Z * B := fun Z => by
    simp [StepData.gal, hAdef, hBdef, Matrix.mul_assoc]
  have h1 : A * (X.U * X.Uᵀ * G₀) * B = X.U * X.Uᵀ * G₀ := by
    calc A * (X.U * X.Uᵀ * G₀) * B = (A * X.U) * (X.Uᵀ * G₀ * B) := by
          simp only [Matrix.mul_assoc]
      _ = X.U * X.Uᵀ * G₀ := by rw [hU, hB, Matrix.mul_assoc]
  have h2 : A * (G₀ * X.V * X.Vᵀ) * B = G₀ * X.V * X.Vᵀ := by
    calc A * (G₀ * X.V * X.Vᵀ) * B = (A * (G₀ * X.V)) * (X.Vᵀ * B) := by
          simp only [Matrix.mul_assoc]
      _ = G₀ * X.V * X.Vᵀ := by rw [hA, hV]
  have h3 : A * (X.U * X.Uᵀ * G₀ * X.V * X.Vᵀ) * B = X.U * X.Uᵀ * G₀ * X.V * X.Vᵀ := by
    calc A * (X.U * X.Uᵀ * G₀ * X.V * X.Vᵀ) * B = (A * X.U) * X.Uᵀ * G₀ * X.V * (X.Vᵀ * B) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV]
  rw [hgal, LRState.P, tangentProj_apply, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
    Matrix.add_mul, h1, h2, h3]

/-- The Galerkin projected gradient dominates the tangent gradient (arXiv 2601.08882, Sec. 2,
Convergence): `‖P G₀‖ ≤ ‖Π G₀‖`. -/
theorem norm_P_le (h : IsDLRTStep G₀ f lr sStar ϑ X D) : ‖X.P G₀‖ ≤ ‖D.gal G₀‖ :=
  norm_apply_le_of_absorbs h.valid.isOrthProj_P h.isOrthProj_gal h.capture

/-- The Galerkin defect is at most the normal component of the gradient (arXiv 2601.08882, Sec. 2,
Error control): `‖G₀ - Π G₀‖ ≤ ‖G₀ - P G₀‖`. -/
theorem norm_sub_gal_le (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    ‖G₀ - D.gal G₀‖ ≤ ‖G₀ - X.P G₀‖ := by
  have := h.isOrthProj_gal.norm_sub_le (G₀ - X.P G₀)
  rwa [map_sub, h.capture, sub_sub_sub_cancel_right] at this

/-- **Retraction** (arXiv 2601.08882, Sec. 2, Truncation): the new bases are orthonormal and `S₁` is
invertible, so that the step returns to a manifold `M_{r₁}`.  With `LRState.IsValid.rank_W`, the new
weight matrix has rank exactly `r₁`. -/
theorem next_valid (h : IsDLRTStep G₀ f lr sStar ϑ X D) : D.next.IsValid where
  orthU := by
    change (D.Uhat * D.P₁)ᵀ * (D.Uhat * D.P₁) = 1
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D.Uhatᵀ, h.orthUhat, Matrix.one_mul,
      h.trunc.orthP₁]
  orthV := by
    change (D.Vhat * D.Q₁)ᵀ * (D.Vhat * D.Q₁) = 1
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D.Vhatᵀ, h.orthVhat, Matrix.one_mul,
      h.trunc.orthQ₁]
  invS := by
    change IsUnit (diagonal D.σ₁).det
    rw [det_diagonal]
    exact (Finset.prod_pos fun i _ => h.trunc.pos₁ i).ne'.isUnit

/-- The truncation error, derived from the SVD (arXiv 2601.08882, Sec. 2):
`‖W₁ - Û S̃ V̂ᵀ‖_F = ‖(discarded singular values)‖₂`. -/
theorem norm_next_sub_What (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    ‖D.next.W - D.What sStar‖ = √(∑ j, D.σ₂ j ^ 2) := by
  have hdec : D.What sStar - D.next.W =
      (D.Uhat * D.P₂) * diagonal D.σ₂ * (D.Vhat * D.Q₂)ᵀ := by
    change D.Uhat * D.Shat sStar * D.Vhatᵀ -
      D.Uhat * D.P₁ * diagonal D.σ₁ * (D.Vhat * D.Q₁)ᵀ = _
    rw [h.trunc.svd]
    simp only [Matrix.mul_add, Matrix.add_mul, transpose_mul, Matrix.mul_assoc, add_sub_cancel_left]
  have hP : (D.Uhat * D.P₂)ᵀ * (D.Uhat * D.P₂) = 1 := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D.Uhatᵀ, h.orthUhat, Matrix.one_mul,
      h.trunc.orthP₂]
  have hQ : (D.Vhat * D.Q₂)ᵀ * (D.Vhat * D.Q₂) = 1 := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D.Vhatᵀ, h.orthVhat, Matrix.one_mul,
      h.trunc.orthQ₂]
  rw [norm_sub_rev, hdec, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hP,
    Frobenius.norm_mul_transpose_of_orthonormal hQ, Frobenius.norm_def]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [diagonal_apply_ne _ hj.symm]
  · simp

/-- The truncation tolerance is met (arXiv 2601.08882, Sec. 2, Truncation):
`‖W₁ - Û S̃ V̂ᵀ‖_F < ϑ`. -/
theorem norm_next_sub_What_lt (h : IsDLRTStep G₀ f lr sStar ϑ X D) :
    ‖D.next.W - D.What sStar‖ < ϑ := by
  rw [h.norm_next_sub_What]
  exact h.trunc.tail

end IsDLRTStep

/-! ### Existence: the hypotheses can always be met -/

/-- **Truncated SVDs exist** (arXiv 2601.08882, Sec. 2, Truncation): a matrix of rank `k + d` has an
SVD with the `k` largest singular values kept and the `d` smallest ones discarded.  What remains of
`IsTruncSVD` is the threshold `‖σ₂‖₂ < ϑ`, which selects `r₁ = k`. -/
theorem exists_truncSVD {a b k d : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (hA : A.rank = k + d) :
    ∃ (P₁ : Matrix (Fin a) (Fin k) ℝ) (Q₁ : Matrix (Fin b) (Fin k) ℝ) (σ₁ : Fin k → ℝ)
      (P₂ : Matrix (Fin a) (Fin d) ℝ) (Q₂ : Matrix (Fin b) (Fin d) ℝ) (σ₂ : Fin d → ℝ),
      ∀ ϑ, √(∑ j, σ₂ j ^ 2) < ϑ → IsTruncSVD A ϑ P₁ Q₁ σ₁ P₂ Q₂ σ₂ := by
  obtain ⟨P, Q, σ, hP, hQ, hanti, hσ, -, hsvd⟩ := SVD.exists_svd A hA
  have key : ∀ {c n₁ n₂ : ℕ} (R : Matrix (Fin c) (Fin (k + d)) ℝ) (f : Fin n₁ → Fin (k + d))
      (g : Fin n₂ → Fin (k + d)),
      (R.submatrix id f)ᵀ * R.submatrix id g = (Rᵀ * R).submatrix f g := by
    intro c n₁ n₂ R f g
    ext i j
    simp [Matrix.mul_apply]
  have hne : ∀ (i : Fin k) (j : Fin d), Fin.castAdd d i ≠ Fin.natAdd k j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨P.submatrix id (Fin.castAdd d), Q.submatrix id (Fin.castAdd d), σ ∘ Fin.castAdd d,
    P.submatrix id (Fin.natAdd k), Q.submatrix id (Fin.natAdd k), σ ∘ Fin.natAdd k,
    fun ϑ hϑ => ?_⟩
  exact
    { orthP₁ := by rw [key, hP, submatrix_one _ (Fin.castAdd_injective _ _)]
      orthQ₁ := by rw [key, hQ, submatrix_one _ (Fin.castAdd_injective _ _)]
      orthP₂ := by rw [key, hP, submatrix_one _ (Fin.natAdd_injective _ _)]
      orthQ₂ := by rw [key, hQ, submatrix_one _ (Fin.natAdd_injective _ _)]
      crossP := by
        rw [key, hP]
        ext i j
        simp [one_apply_ne (hne i j)]
      crossQ := by
        rw [key, hQ]
        ext i j
        simp [one_apply_ne (hne i j)]
      pos₁ := fun _ => hσ _
      nonneg₂ := fun _ => (hσ _).le
      ordered := fun i j => hanti (by
        rw [Fin.le_def]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        omega)
      svd := by
        refine hsvd.trans ?_
        ext x y
        simp [Matrix.mul_apply, Fin.sum_univ_add, diagonal_apply]
      tail := hϑ }

/-- **Non-vacuity of the step of arXiv 2601.08882, Sec. 2.**  From every point of the manifold,
every gradient information `G₀`, S-step field `f`, learning rate, number of local iterations and
tolerance `ϑ > 0`, a DLRT step exists.  (It is the step which truncates nothing; the augmented
bases and the SVD come from `exists_orthonormal_capture_fromCols` and `SVD.exists_svd`.  Genuine
truncations exist by `exists_truncSVD`.) -/
theorem exists_step {X : LRState m n} (hX : X.IsValid) (G₀ : Matrix m n ℝ)
    (f : Matrix m n ℝ → Matrix m n ℝ) (lr : ℝ) (sStar : ℕ) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ D : StepData m n, IsDLRTStep G₀ f lr sStar ϑ X D ∧ ‖D.next.W - D.What sStar‖ = 0 := by
  classical
  obtain ⟨Uh, hUh, hGU, hU⟩ := exists_orthonormal_capture_fromCols (G₀ * X.V * X.Sᵀ) X.U le_rfl
    (by simpa using (fromCols (G₀ * X.V * X.Sᵀ) X.U).rank_le_card_height)
  obtain ⟨Vh, hVh, hGV, hV⟩ := exists_orthonormal_capture_fromCols (G₀ᵀ * X.U * X.S) X.V le_rfl
    (by simpa using (fromCols (G₀ᵀ * X.U * X.S) X.V).rank_le_card_height)
  let Shat : ℕ → Matrix _ _ ℝ := fun s => Nat.rec (Uhᵀ * X.U * X.S * X.Vᵀ * Vh)
    (fun _ Z => Z - lr • (Uhᵀ * f (Uh * Z * Vhᵀ) * Vh)) s
  obtain ⟨P, Q, σ, hP, hQ, -, hσ, -, hsvd⟩ := SVD.exists_svd (Shat sStar) rfl
  have hstep : IsDLRTStep G₀ f lr sStar ϑ X ⟨_, _, _, 0, Uh, Vh, Shat, P, Q, σ, 0, 0, Fin.elim0⟩ :=
    { valid := hX
      orthUhat := hUh
      orthVhat := hVh
      spanU := hU
      spanV := hV
      spanGU := hGU
      spanGV := hGV
      start := rfl
      iter := fun _ _ => rfl
      trunc :=
        { orthP₁ := hP
          orthQ₁ := hQ
          orthP₂ := Subsingleton.elim _ _
          orthQ₂ := Subsingleton.elim _ _
          crossP := Subsingleton.elim _ _
          crossQ := Subsingleton.elim _ _
          pos₁ := hσ
          nonneg₂ := fun j => j.elim0
          ordered := fun _ j => j.elim0
          svd := by
            refine hsvd.trans ?_
            ext i j
            simp [Matrix.mul_apply]
          tail := by simpa using hϑ } }
  refine ⟨_, hstep, ?_⟩
  rw [hstep.norm_next_sub_What]
  simp

/-- **Non-vacuity of trajectories of arXiv 2601.08882, Sec. 2.**  From every point of the manifold
there is an infinite DLRT trajectory without truncation error, for every gradient field, all
learning rates and all positive tolerances. -/
theorem exists_trajectory {X₀ : LRState m n} (hX₀ : X₀.IsValid) (g : Matrix m n ℝ → Matrix m n ℝ)
    (lr : ℕ → ℝ) (sStar : ℕ) {ϑ : ℕ → ℝ} (hϑ : ∀ t, 0 < ϑ t) :
    ∃ (X : ℕ → LRState m n) (D : ℕ → StepData m n), X 0 = X₀ ∧
      (∀ t, IsDLRTStep (g (X t).W) g (lr t) sStar (ϑ t) (X t) (D t)) ∧
      (∀ t, X (t + 1) = (D t).next) ∧ ∀ t, ‖(D t).next.W - (D t).What sStar‖ = 0 := by
  have hex : ∀ (t : ℕ) (Y : {Y : LRState m n // Y.IsValid}),
      ∃ D, IsDLRTStep (g Y.1.W) g (lr t) sStar (ϑ t) Y.1 D ∧ ‖D.next.W - D.What sStar‖ = 0 :=
    fun t Y => exists_step Y.2 _ _ _ _ (hϑ t)
  choose F hF using hex
  let seq : ℕ → {Y : LRState m n // Y.IsValid} := fun t =>
    Nat.rec ⟨X₀, hX₀⟩ (fun t Y => ⟨(F t Y).next, (hF t Y).1.next_valid⟩) t
  exact ⟨fun t => (seq t).1, fun t => F t (seq t), rfl, fun t => (hF t (seq t)).1, fun _ => rfl,
    fun t => (hF t (seq t)).2⟩

/-! ### Deterministic loss descent and stationarity -/

section Descent

variable {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β lr ϑ : ℝ} {sStar : ℕ}
  {X : LRState m n} {D : StepData m n}

/-- All `s⋆ ≥ 1` local iterations together decrease the loss at least as much as the first. -/
private theorem loss_What_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (h : IsDLRTStep (g X.W) g lr sStar ϑ X D)
    (hlr : 0 ≤ lr) (hlr2 : β * lr ≤ 2) (hs : 0 < sStar) :
    ℒ (D.What sStar) ≤ ℒ X.W - lr * (1 - β * lr / 2) * ‖X.P (g X.W)‖ ^ 2 := by
  have hw : 0 ≤ lr * (1 - β * lr / 2) := mul_nonneg hlr (by linarith)
  have key : ∀ i, i + 1 ≤ sStar →
      ℒ (D.What (i + 1)) ≤ ℒ X.W - lr * (1 - β * lr / 2) * ‖D.gal (g X.W)‖ ^ 2 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [h.What_succ hs, h.start_eq]
      exact loss_projGradStep_le hℒ hg h.isOrthProj_gal lr X.W
    | succ i ih =>
      intro hi
      rw [h.What_succ (show i + 1 < sStar by omega)]
      exact (loss_projGradStep_le_self hℒ hg h.isOrthProj_gal hw _).trans (ih (by omega))
  have h1 := key (sStar - 1) (by omega)
  rw [Nat.sub_add_cancel hs] at h1
  have h2 : ‖X.P (g X.W)‖ ^ 2 ≤ ‖D.gal (g X.W)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h.norm_P_le 2
  nlinarith

/-- **Loss descent of DLRT, deterministic form** (arXiv 2601.08882, Sec. 2, Convergence, quoting
GeoLoRA, arXiv 2410.18720, Thm 1): for `L`-smooth loss (`β` here), learning rate
`0 ≤ lr ≤ 2 / β` and any number `s⋆ ≥ 1` of local iterations,
`L(W₁) ≤ L(W) - lr (1 - β lr / 2) ‖P_{M_r} ∇L(W)‖² + G ‖W₁ - Û S̃ V̂ᵀ‖`.

Differences from the paper.  The inequality is printed there with `1 - L λ² / 2`, a misprint which
is false (`printed_coefficient_false`); here it is `1 - β lr / 2`.  The paper uses one letter `L`
for the Lipschitz constant of `∇L` and for a bound of `‖∇L‖` (the proof in 2410.18720 uses both);
they are `β` and `G` here, and `G` is only needed on the segment from `Û S̃ V̂ᵀ` to `W₁`.  The
tangent gradient of the state is captured by the latent space through `IsDLRTStep.capture`, derived
from the augmentation and `rank S = r`, not assumed.  For the expectations over mini-batches see
`expected_loss_descent` and `sameBatch_loss_descent`. -/
theorem loss_dlrtStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (h : IsDLRTStep (g X.W) g lr sStar ϑ X D)
    (hlr : 0 ≤ lr) (hlr2 : β * lr ≤ 2) (hs : 0 < sStar) {G : ℝ}
    (hG : ∀ w ∈ segment ℝ (D.What sStar) D.next.W, ‖g w‖ ≤ G) :
    ℒ D.next.W ≤ ℒ X.W - lr * (1 - β * lr / 2) * ‖X.P (g X.W)‖ ^ 2 +
      G * ‖D.next.W - D.What sStar‖ := by
  have h1 := loss_What_le hℒ hg h hlr hlr2 hs
  have h2 := (abs_le.1 (abs_energy_sub_le hℒ hG)).2
  linarith

end Descent

/-- A sequence bounded below by `v` that comes within every `ε > 0` of `v` infinitely often has
`liminf = v`. -/
private theorem liminf_eq_of_forall_exists_lt {u : ℕ → ℝ} {v : ℝ} (h0 : ∀ t, v ≤ u t)
    (h : ∀ ε, 0 < ε → ∀ N, ∃ t, N ≤ t ∧ u t < v + ε) : liminf u atTop = v := by
  rw [Filter.liminf_eq]
  refine IsGreatest.csSup_eq ⟨Eventually.of_forall h0, fun a ha => ?_⟩
  by_contra hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 ha
  obtain ⟨t, ht, hlt⟩ := h (a - v) (sub_pos.2 (not_le.1 hcon)) N
  have := hN t ht
  linarith

private theorem liminf_eq_zero_of_forall_exists_lt {u : ℕ → ℝ} (h0 : ∀ t, 0 ≤ u t)
    (h : ∀ ε, 0 < ε → ∀ N, ∃ t, N ≤ t ∧ u t < ε) : liminf u atTop = 0 :=
  liminf_eq_of_forall_exists_lt h0 fun ε hε N => by simpa using h ε hε N

section Stationarity

variable {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ} {sStar : ℕ}
  {X : ℕ → LRState m n} {D : ℕ → StepData m n} {lr ϑ : ℕ → ℝ}

/-- **Stationarity of DLRT, deterministic form** (arXiv 2601.08882, Sec. 2, Convergence, quoting
GeoLoRA, arXiv 2410.18720, Thm 2): for Robbins–Monro learning rates with `β lr_t ≤ 2`, a loss
bounded below along the iterates, gradients bounded by `G` between `Û S̃ V̂ᵀ` and `W_{t+1}`, and
bounded accumulated truncation errors, `liminf_t ‖P_{M_r} ∇L(W_t)‖² = 0`, for any `s⋆ ≥ 1`.

The hypothesis on the truncation errors makes precise the paper's "this term vanishes as a suitable
rank and basis is found", as in 2410.18720.  For the expectation see
`liminf_expected_tangentGrad_sq`, and `not_stationarity_of_batch_gradient` for the statement with
`ξ_t` printed inside the expectation, which is false. -/
theorem liminf_tangentGrad_sq (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hstep : ∀ t, IsDLRTStep (g (X t).W) g (lr t) sStar (ϑ t) (X t) (D t))
    (hnext : ∀ t, X (t + 1) = (D t).next) (hs : 0 < sStar) (hlr : ∀ t, 0 ≤ lr t)
    (hlr2 : ∀ t, β * lr t ≤ 2) (hdiv : ¬ Summable lr) (hsq : Summable fun t => lr t ^ 2)
    {ℒinf G C : ℝ} (hinf : ∀ t, ℒinf ≤ ℒ (X t).W)
    (hG : ∀ t, ∀ w ∈ segment ℝ ((D t).What sStar) (D t).next.W, ‖g w‖ ≤ G)
    (hC : ∀ N, ∑ t ∈ range N, ‖(D t).next.W - (D t).What sStar‖ ≤ C) :
    liminf (fun t => ‖(X t).P (g (X t).W)‖ ^ 2) atTop = 0 := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 _ (left_mem_segment ℝ _ _))
  have hw : ∀ t, 0 ≤ lr t * (1 - β * lr t / 2) := fun t =>
    mul_nonneg (hlr t) (by linarith [hlr2 t])
  have hwdiv : ¬ Summable fun t => lr t * (1 - β * lr t / 2) := by
    intro hsum
    apply hdiv
    have e : lr = fun t => lr t * (1 - β * lr t / 2) + β / 2 * lr t ^ 2 := by
      funext t; ring
    rw [e]
    exact hsum.add (hsq.mul_left (β / 2))
  refine liminf_eq_zero_of_forall_exists_lt (fun t => sq_nonneg _) fun ε hε N =>
    exists_lt_of_sum_mul_le hw (fun t => sq_nonneg _) hwdiv
      (C := ℒ (X 0).W - ℒinf + G * C) (fun M => ?_) hε N
  have hstepdesc : ∀ t, lr t * (1 - β * lr t / 2) * ‖(X t).P (g (X t).W)‖ ^ 2 ≤
      ℒ (X t).W - ℒ (X (t + 1)).W + G * ‖(D t).next.W - (D t).What sStar‖ := fun t => by
    have := loss_dlrtStep_le hℒ hg (hstep t) (hlr t) (hlr2 t) hs (hG t)
    rw [hnext t]
    linarith
  have hsum := sum_le_of_le_sub_add (u := fun t => ℒ (X t).W) hstepdesc M
  have h1 := hinf M
  have h2 : ∑ t ∈ range M, G * ‖(D t).next.W - (D t).What sStar‖ ≤ G * C := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hC M) hG0
  linarith

end Stationarity

/-! ### Error against the gradient flow

The analysis is carried out once, for a gradient flow with one-sided Lipschitz constant `ℓ ≠ 0`:
`ℓ = β > 0` gives the bound over finite time and `ℓ = -μ < 0` the time-uniform one. -/

section ErrorBound

variable {g : Matrix m n ℝ → Matrix m n ℝ} {β ℓ ε B lr ϑ : ℝ} {sStar : ℕ} {X : LRState m n}
  {D : StepData m n}

/-- One explicit Euler step compared with the exact flow on `[a, b]`. -/
private lemma norm_flow_sub_line_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {A : ℝ → Matrix m n ℝ} {a b : ℝ} (hab : a ≤ b)
    (hA : ODESolution F A a b) {z d : Matrix m n ℝ} {η δ : ℝ}
    (hd : ∀ t ∈ Ico a b, ‖d - F t (z + (t - a) • d)‖ ≤ η) (h0 : ‖A a - z‖ ≤ δ) :
    ‖A b - (z + (b - a) • d)‖ ≤ gronwallBound δ ℓ η (b - a) := by
  have hzc : ContinuousOn (fun t : ℝ => z + (t - a) • d) (Icc a b) := by fun_prop
  have hzd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t : ℝ => z + (t - a) • d) d (Ici t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t - a) • d) ((1 : ℝ) • d) t :=
      ((hasDerivAt_id t).sub_const a).smul_const d
    simpa using (h1.const_add z).hasDerivWithinAt
  have := norm_sub_le_gronwallBound_of_oneSided hF (ηy := 0) (ηz := η) hA.cont hA.deriv
    (fun t _ => by simp) hzc hzd hd (by simpa using h0) b ⟨hab, le_rfl⟩
  simpa using this

/-- **Local error of one DLRT step** before truncation, against the flow of `-∇L`. -/
private theorem local_error (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β)
    (hℓ : ℓ ≠ 0) (hF : IsOneSidedLipschitzField (fun _ x => -g x) ℓ)
    (h : IsDLRTStep (g X.W) g lr sStar ϑ X D) (hlr : 0 ≤ lr)
    (hB : ∀ i < sStar, ‖g (D.What i)‖ ≤ B) (hε : ‖g X.W - X.P (g X.W)‖ ≤ ε)
    {A : ℝ → Matrix m n ℝ} {a : ℝ}
    (hA : ODESolution (fun _ x => -g x) A a (a + sStar * lr)) :
    ‖A (a + sStar * lr) - D.What sStar‖ ≤
      ‖A a - X.W‖ * Real.exp (ℓ * (sStar * lr)) +
        (ε + β * B * (sStar * lr)) / ℓ * (Real.exp (ℓ * (sStar * lr)) - 1) := by
  set η := ε + β * B * (sStar * lr) with hη
  have hP := h.isOrthProj_gal
  have hdrift : ∀ i ≤ sStar, ‖D.What i - X.W‖ ≤ i * (lr * B) := by
    intro i
    induction i with
    | zero => intro _; simp [h.start_eq]
    | succ i ih =>
      intro hi
      have hi' : i < sStar := by omega
      have h1 : D.What (i + 1) - X.W = (D.What i - X.W) - lr • D.gal (g (D.What i)) := by
        rw [h.What_succ hi', projGradStep]; abel
      have h2 : ‖lr • D.gal (g (D.What i))‖ ≤ lr * B := by
        rw [norm_smul, Real.norm_of_nonneg hlr]
        exact mul_le_mul_of_nonneg_left ((hP.norm_le _).trans (hB i hi')) hlr
      rw [h1]
      push_cast
      calc ‖(D.What i - X.W) - lr • D.gal (g (D.What i))‖
          ≤ ‖D.What i - X.W‖ + ‖lr • D.gal (g (D.What i))‖ := norm_sub_le _ _
        _ ≤ i * (lr * B) + lr * B := add_le_add (ih hi'.le) h2
        _ = (i + 1) * (lr * B) := by ring
  have hB0 : ∀ i < sStar, 0 ≤ B := fun i hi => (norm_nonneg _).trans (hB i hi)
  have hgalε : ∀ i < sStar, ‖g (D.What i) - D.gal (g (D.What i))‖ ≤ ε + β * (i * (lr * B)) := by
    intro i hi
    have h1 : g (D.What i) - D.gal (g (D.What i)) = (g X.W - D.gal (g X.W)) +
        ((g (D.What i) - g X.W) - D.gal (g (D.What i) - g X.W)) := by
      rw [map_sub]; abel
    rw [h1]
    refine (norm_add_le _ _).trans (add_le_add (h.norm_sub_gal_le.trans hε) ?_)
    refine (hP.norm_sub_le _).trans ((hg _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (hdrift i hi.le) hβ
  have hsub : ∀ i ≤ sStar, ‖A (a + i * lr) - D.What i‖ ≤
      ‖A a - X.W‖ * Real.exp (ℓ * (i * lr)) + η / ℓ * (Real.exp (ℓ * (i * lr)) - 1) := by
    intro i
    induction i with
    | zero => intro _; simp [h.start_eq]
    | succ i ih =>
      intro hi
      have hi' : i < sStar := by omega
      have hi1 : ((i : ℝ) + 1) ≤ sStar := by exact_mod_cast hi
      have hB0' := hB0 i hi'
      set c := a + i * lr with hc
      have hc1 : a + ((i + 1 : ℕ) : ℝ) * lr = c + lr := by push_cast; rw [hc]; ring
      have hAsub : ODESolution (fun _ x => -g x) A c (c + lr) :=
        hA.mono (by rw [hc]; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
          (by rw [hc]; nlinarith)
      set d := -D.gal (g (D.What i)) with hd
      have hd_norm : ‖d‖ ≤ B := by
        rw [hd, norm_neg]; exact (hP.norm_le _).trans (hB i hi')
      have hdef : ∀ t ∈ Ico c (c + lr), ‖d - (fun (_ : ℝ) x => -g x) t (D.What i + (t - c) • d)‖
          ≤ η := by
        intro t ht
        have ht0 : 0 ≤ t - c := by linarith [ht.1]
        have ht1 : t - c ≤ lr := by linarith [ht.2]
        have e : d - (fun (_ : ℝ) x => -g x) t (D.What i + (t - c) • d) =
            (g (D.What i + (t - c) • d) - g (D.What i)) +
              (g (D.What i) - D.gal (g (D.What i))) := by
          simp only [hd]; abel
        have h1 : ‖g (D.What i + (t - c) • d) - g (D.What i)‖ ≤ β * (lr * B) := by
          refine (hg _ _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
          exact mul_le_mul ht1 hd_norm (norm_nonneg _) (ht0.trans ht1)
        rw [e]
        refine (norm_add_le _ _).trans ((add_le_add h1 (hgalε i hi')).trans ?_)
        have h2 : β * (lr * B) + β * (i * (lr * B)) ≤ β * B * (sStar * lr) := by
          have : 0 ≤ β * B * lr := mul_nonneg (mul_nonneg hβ hB0') hlr
          nlinarith
        rw [hη]; linarith
      have hstep := norm_flow_sub_line_le hF (show c ≤ c + lr by linarith) hAsub hdef (ih hi'.le)
      have hval : D.What i + (c + lr - c) • d = D.What (i + 1) := by
        rw [h.What_succ hi', projGradStep, hd, add_sub_cancel_left, smul_neg, sub_eq_add_neg]
      rw [hval, add_sub_cancel_left, gronwallBound_of_K_ne_0 hℓ] at hstep
      rw [hc1]
      refine hstep.trans (le_of_eq ?_)
      have hexp : Real.exp (ℓ * ((i + 1 : ℕ) * lr)) =
          Real.exp (ℓ * (i * lr)) * Real.exp (ℓ * lr) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hexp]
      ring
  exact hsub sStar le_rfl

/-- The fan: recursion for the global error over `n` DLRT steps. -/
private theorem global_error_core (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β)
    (hℓ : ℓ ≠ 0) (hF : IsOneSidedLipschitzField (fun _ x => -g x) ℓ) {N : ℕ}
    {X : ℕ → LRState m n} {D : ℕ → StepData m n}
    (hstep : ∀ n < N, IsDLRTStep (g (X n).W) g lr sStar ϑ (X n) (D n))
    (hnext : ∀ n < N, X (n + 1) = (D n).next) (hs : 0 < sStar) (hlr : 0 < lr)
    (hB : ∀ n < N, ∀ i < sStar, ‖g ((D n).What i)‖ ≤ B)
    (hε : ∀ n < N, ‖g (X n).W - (X n).P (g (X n).W)‖ ≤ ε) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A 0 (N * (sStar * lr))) :
    ∀ n ≤ N, ‖A (n * (sStar * lr)) - (X n).W‖ + ((ε + β * B * (sStar * lr)) / ℓ +
        ϑ / (Real.exp (ℓ * (sStar * lr)) - 1)) ≤
      Real.exp (ℓ * (sStar * lr)) ^ n * (‖A (0 * (sStar * lr)) - (X 0).W‖ +
        ((ε + β * B * (sStar * lr)) / ℓ + ϑ / (Real.exp (ℓ * (sStar * lr)) - 1))) := by
  set h : ℝ := sStar * lr with hh
  have hs' : (0 : ℝ) < sStar := by exact_mod_cast hs
  have hpos : 0 < h := mul_pos hs' hlr
  set q := Real.exp (ℓ * h) with hq
  set η := ε + β * B * h with hη
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q - 1 ≠ 0 := by
    rw [sub_ne_zero, hq, Ne, Real.exp_eq_one_iff]
    exact mul_ne_zero hℓ hpos.ne'
  set C := η / ℓ + ϑ / (q - 1) with hC
  have hCq : (q - 1) * C = η / ℓ * (q - 1) + ϑ := by
    rw [hC]; field_simp
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    have hn1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have ih' := ih hn'.le
    have hAsub : ODESolution (fun _ x => -g x) A (n * h) (n * h + h) :=
      hA.mono (by positivity) (by nlinarith)
    have hloc := local_error hg hβ hℓ hF (hstep n hn') hlr.le (hB n hn') (hε n hn') hAsub
    have htr := (hstep n hn').norm_next_sub_What_lt
    rw [← hnext n hn'] at htr
    have htime : ((n + 1 : ℕ) : ℝ) * h = n * h + h := by push_cast; ring
    have htri : ‖A (((n + 1 : ℕ) : ℝ) * h) - (X (n + 1)).W‖ ≤
        ‖A (n * h + h) - (D n).What sStar‖ + ‖(X (n + 1)).W - (D n).What sStar‖ := by
      rw [htime]
      simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub
        (A (n * h + h)) ((D n).What sStar) (X (n + 1)).W
    have hrec : ‖A (((n + 1 : ℕ) : ℝ) * h) - (X (n + 1)).W‖ + C ≤
        q * (‖A (n * h) - (X n).W‖ + C) := by
      have e : q * (‖A (n * h) - (X n).W‖ + C) =
          ‖A (n * h) - (X n).W‖ * q + η / ℓ * (q - 1) + ϑ + C := by
        linear_combination hCq
      rw [e]
      linarith
    rw [pow_succ']
    calc _ ≤ q * (‖A (n * h) - (X n).W‖ + C) := hrec
      _ ≤ q * (q ^ n * (‖A (0 * h) - (X 0).W‖ + C)) := mul_le_mul_of_nonneg_left ih' hq0.le
      _ = _ := by ring

/-- **Error against the gradient flow over finite time** (arXiv 2601.08882, Sec. 2, Error control,
quoting GeoLoRA, arXiv 2410.18720, Thm 3): let `A` solve the gradient flow `Ẇ = -∇L(W)`, let `∇L`
be `β`-Lipschitz, let `‖∇L‖ ≤ B` along the iterates and let the normal component of the gradient
be at most `ε` at the iterates.  With `h = s⋆ lr` the time of one DLRT step and `t = n h`,

  `‖A(t) - W_n‖ ≤ e^{β t} ‖A(0) - W_0‖ + (e^{β t} - 1) / β * (ε + β B h + ϑ / h)`.

The constants depend on `β`, `B` and `t` only, not on singular values or on the curvature of the
manifold, which is the robustness claimed in the paper; `dlrt_error_le_constants` is the printed
form.  They grow with `t`, and this cannot be avoided: `not_timeUniform_error`.  The hypotheses on
the normal component and on `‖∇L‖` are made on the iterates only, weaker than the paper's
"for any `Z` in a neighbourhood of `W(t)`" and the global bound. -/
theorem dlrt_error_finite_time (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {N : ℕ}
    {X : ℕ → LRState m n} {D : ℕ → StepData m n}
    (hstep : ∀ n < N, IsDLRTStep (g (X n).W) g lr sStar ϑ (X n) (D n))
    (hnext : ∀ n < N, X (n + 1) = (D n).next) (hs : 0 < sStar) (hlr : 0 < lr)
    (hB : ∀ n < N, ∀ i < sStar, ‖g ((D n).What i)‖ ≤ B)
    (hε : ∀ n < N, ‖g (X n).W - (X n).P (g (X n).W)‖ ≤ ε) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A 0 (N * (sStar * lr))) :
    ∀ n ≤ N, ‖A (n * (sStar * lr)) - (X n).W‖ ≤
      Real.exp (β * (n * (sStar * lr))) * ‖A 0 - (X 0).W‖ +
        (Real.exp (β * (n * (sStar * lr))) - 1) / β *
          (ε + β * B * (sStar * lr) + ϑ / (sStar * lr)) := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have hN : 0 < N := by omega
  have hF : IsOneSidedLipschitzField (fun _ x => -g x) β :=
    IsLipschitzField.isOneSidedLipschitzField (fun _ x y => by
      rw [neg_sub_neg, norm_sub_rev]; exact hg x y)
  have hcore := global_error_core hg hβ.le hβ.ne' hF hstep hnext hs hlr hB hε hA n hn
  have hϑ : 0 ≤ ϑ := (norm_nonneg _).trans (hstep 0 hN).norm_next_sub_What_lt.le
  set h : ℝ := sStar * lr with hh
  have hs' : (0 : ℝ) < sStar := by exact_mod_cast hs
  have hpos : 0 < h := mul_pos hs' hlr
  set q := Real.exp (β * h) with hq
  set η := ε + β * B * h with hη
  have hqn : q ^ n = Real.exp (β * (n * h)) := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  rw [hqn] at hcore
  simp only [zero_mul] at hcore
  set Q := Real.exp (β * (n * h)) with hQ
  have hQ1 : 0 ≤ Q - 1 := by
    have := Real.add_one_le_exp (β * (n * h))
    have : 0 ≤ β * (n * h) := by positivity
    linarith
  have hqβ : β * h ≤ q - 1 := by linarith [Real.add_one_le_exp (β * h)]
  have hβh : 0 < β * h := mul_pos hβ hpos
  have hdiv : ϑ / (q - 1) ≤ ϑ / (β * h) :=
    div_le_div_of_nonneg_left hϑ hβh hqβ
  have hC : η / β + ϑ / (q - 1) ≤ (η + ϑ / h) / β := by
    have : (η + ϑ / h) / β = η / β + ϑ / (β * h) := by
      field_simp
    rw [this]; linarith
  have hmul := mul_le_mul_of_nonneg_left hC hQ1
  have e : (Q - 1) / β * (η + ϑ / h) = (Q - 1) * ((η + ϑ / h) / β) := by ring
  rw [e]
  nlinarith

/-- **Printed form of the error bound, with the time dependence made explicit** (arXiv 2601.08882,
Sec. 2, Error control): for the same initial value and `n h ≤ T`,
`‖A(t) - W_n‖ ≤ c₁ ε + c₂ lr + c₃ ϑ / lr` with `c₁ = (e^{β T} - 1) / β`,
`c₂ = s⋆ B (e^{β T} - 1)`, `c₃ = (e^{β T} - 1) / (β s⋆)`.  For `s⋆ = 1` this is the printed form
with `t = n lr`.  In contrast to the paper's sentence the constants depend on `T`:
`not_timeUniform_error`. -/
theorem dlrt_error_le_constants (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {N : ℕ}
    {X : ℕ → LRState m n} {D : ℕ → StepData m n}
    (hstep : ∀ n < N, IsDLRTStep (g (X n).W) g lr sStar ϑ (X n) (D n))
    (hnext : ∀ n < N, X (n + 1) = (D n).next) (hs : 0 < sStar) (hlr : 0 < lr)
    (hB : ∀ n < N, ∀ i < sStar, ‖g ((D n).What i)‖ ≤ B)
    (hε : ∀ n < N, ‖g (X n).W - (X n).P (g (X n).W)‖ ≤ ε) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A 0 (N * (sStar * lr))) (hA0 : A 0 = (X 0).W)
    (hε0 : 0 ≤ ε) (hB0 : 0 ≤ B) (hϑ : 0 ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, n * (sStar * lr) ≤ T → ‖A (n * (sStar * lr)) - (X n).W‖ ≤
      (Real.exp (β * T) - 1) / β * ε + sStar * B * (Real.exp (β * T) - 1) * lr +
        (Real.exp (β * T) - 1) / (β * sStar) * ϑ / lr := by
  intro n hn hT
  have h1 := dlrt_error_finite_time hg hβ hstep hnext hs hlr hB hε hA n hn
  rw [hA0, sub_self, norm_zero, mul_zero, zero_add] at h1
  have hs' : (0 : ℝ) < sStar := by exact_mod_cast hs
  have hexp : Real.exp (β * (n * (sStar * lr))) ≤ Real.exp (β * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hβ.le)
  have hdiv : (Real.exp (β * (n * (sStar * lr))) - 1) / β ≤ (Real.exp (β * T) - 1) / β :=
    div_le_div_of_nonneg_right (by linarith) hβ.le
  have hη : 0 ≤ ε + β * B * (sStar * lr) + ϑ / (sStar * lr) := by positivity
  refine h1.trans ((mul_le_mul_of_nonneg_right hdiv hη).trans (le_of_eq ?_))
  field_simp

/-- **Time-uniform error for strongly convex losses** (arXiv 2601.08882, Sec. 2, Error control,
the case in which "the constants do not depend on time" is true): if `∇L` is `μ`-strongly monotone,
`μ > 0`, the error stays bounded uniformly in the number of steps,
`‖A(t) - W_n‖ ≤ e^{-μ t} ‖A(0) - W_0‖ + (ε + β B h + ϑ / h) / μ + ϑ`, `h = s⋆ lr`, `t = n h`.

This is an extra hypothesis compared with the paper, which is necessary:
`not_timeUniform_error`.  `‖∇L‖ ≤ B` is assumed along the iterates only, since a global bound is
impossible for a strongly monotone gradient. -/
theorem dlrt_error_time_uniform (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {μ : ℝ}
    (hμ : 0 < μ) (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) {N : ℕ}
    {X : ℕ → LRState m n} {D : ℕ → StepData m n}
    (hstep : ∀ n < N, IsDLRTStep (g (X n).W) g lr sStar ϑ (X n) (D n))
    (hnext : ∀ n < N, X (n + 1) = (D n).next) (hs : 0 < sStar) (hlr : 0 < lr)
    (hB : ∀ n < N, ∀ i < sStar, ‖g ((D n).What i)‖ ≤ B)
    (hε : ∀ n < N, ‖g (X n).W - (X n).P (g (X n).W)‖ ≤ ε) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A 0 (N * (sStar * lr))) (hε0 : 0 ≤ ε) (hB0 : 0 ≤ B)
    (hϑ : 0 ≤ ϑ) :
    ∀ n ≤ N, ‖A (n * (sStar * lr)) - (X n).W‖ ≤
      Real.exp (-μ * (n * (sStar * lr))) * ‖A 0 - (X 0).W‖ +
        (ε + β * B * (sStar * lr) + ϑ / (sStar * lr)) / μ + ϑ := by
  intro n hn
  have hF : IsOneSidedLipschitzField (fun _ x => -g x) (-μ) :=
    isOneSidedLipschitzField_neg_of_strongMono (G := fun _ x => g x) fun _ x y => hmono x y
  have hcore := global_error_core hg hβ (neg_ne_zero.2 hμ.ne') hF hstep hnext hs hlr hB hε hA n
    hn
  set h : ℝ := sStar * lr with hh
  have hs' : (0 : ℝ) < sStar := by exact_mod_cast hs
  have hpos : 0 < h := mul_pos hs' hlr
  set q := Real.exp (-μ * h) with hq
  set η := ε + β * B * h with hη
  have hη0 : 0 ≤ η := by positivity
  have hqn : q ^ n = Real.exp (-μ * (n * h)) := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  rw [hqn] at hcore
  simp only [zero_mul] at hcore
  set Q := Real.exp (-μ * (n * h)) with hQ
  have hQ0 : 0 < Q := Real.exp_pos _
  have hQ1 : Q ≤ 1 := by
    rw [hQ, ← Real.exp_zero]
    refine Real.exp_le_exp.2 ?_
    have : 0 ≤ μ * (n * h) := by positivity
    nlinarith
  have hμh : 0 < μ * h := mul_pos hμ hpos
  have hq1 : q ≤ 1 / (1 + μ * h) := by
    have h1 := Real.add_one_le_exp (μ * h)
    have h2 : q = (Real.exp (μ * h))⁻¹ := by rw [hq, ← Real.exp_neg]; congr 1; ring
    rw [h2, one_div]
    exact inv_anti₀ (by linarith) (by linarith)
  have hq1' : μ * h / (1 + μ * h) ≤ 1 - q := by
    have : 1 / (1 + μ * h) = 1 - μ * h / (1 + μ * h) := by field_simp; ring
    linarith
  have hq1pos : 0 < 1 - q := lt_of_lt_of_le (by positivity) hq1'
  have hdiv : ϑ / (1 - q) ≤ ϑ / h / μ + ϑ := by
    have h1 : ϑ / (1 - q) ≤ ϑ / (μ * h / (1 + μ * h)) :=
      div_le_div_of_nonneg_left hϑ (by positivity) hq1'
    have h2 : ϑ / (μ * h / (1 + μ * h)) = ϑ / h / μ + ϑ := by
      field_simp
    rw [h2] at h1
    exact h1
  have hC : η / -μ + ϑ / (q - 1) = -(η / μ + ϑ / (1 - q)) := by
    rw [div_neg, show q - 1 = -(1 - q) by ring, div_neg]
    ring
  rw [hC] at hcore
  have hnn : 0 ≤ η / μ + ϑ / (1 - q) := by positivity
  have hcoef : (1 - Q) * (η / μ + ϑ / (1 - q)) ≤ η / μ + ϑ / (1 - q) := by nlinarith
  have e : (η + ϑ / h) / μ = η / μ + ϑ / h / μ := by ring
  rw [e]
  nlinarith

/-- **Time-uniform constants** (arXiv 2601.08882, Sec. 2, Error control, under strong convexity):
for the same initial value and `lr ≤ H`, `‖A(t) - W_n‖ ≤ c₁ ε + c₂ lr + c₃ ϑ / lr` for all `n`, with
`c₁ = 1 / μ`, `c₂ = β B s⋆ / μ` and `c₃ = 1 / (μ s⋆) + H`, which do not depend on `n` or on time. -/
theorem dlrt_error_time_uniform_constants (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β)
    {μ : ℝ} (hμ : 0 < μ) (hmono : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) {N : ℕ}
    {X : ℕ → LRState m n} {D : ℕ → StepData m n}
    (hstep : ∀ n < N, IsDLRTStep (g (X n).W) g lr sStar ϑ (X n) (D n))
    (hnext : ∀ n < N, X (n + 1) = (D n).next) (hs : 0 < sStar) (hlr : 0 < lr)
    (hB : ∀ n < N, ∀ i < sStar, ‖g ((D n).What i)‖ ≤ B)
    (hε : ∀ n < N, ‖g (X n).W - (X n).P (g (X n).W)‖ ≤ ε) {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution (fun _ x => -g x) A 0 (N * (sStar * lr))) (hA0 : A 0 = (X 0).W)
    (hε0 : 0 ≤ ε) (hB0 : 0 ≤ B) (hϑ : 0 ≤ ϑ) {H : ℝ} (hH : lr ≤ H) :
    ∀ n ≤ N, ‖A (n * (sStar * lr)) - (X n).W‖ ≤
      1 / μ * ε + β * B * sStar / μ * lr + (1 / (μ * sStar) + H) * ϑ / lr := by
  intro n hn
  have h1 := dlrt_error_time_uniform hg hβ hμ hmono hstep hnext hs hlr hB hε hA hε0 hB0 hϑ n hn
  rw [hA0, sub_self, norm_zero, mul_zero, zero_add] at h1
  have hs' : (0 : ℝ) < sStar := by exact_mod_cast hs
  refine h1.trans ?_
  have e1 : (ε + β * B * (sStar * lr) + ϑ / (sStar * lr)) / μ + ϑ =
      1 / μ * ε + β * B * sStar / μ * lr + (1 / (μ * sStar) + lr) * ϑ / lr := by
    field_simp
    ring
  rw [e1]
  have h2 : (1 / (μ * sStar) + lr) * ϑ / lr ≤ (1 / (μ * sStar) + H) * ϑ / lr := by
    gcongr
  linarith

/-- **The two flows are close** (arXiv 2601.08882, Sec. 2, Error control, first sentence; GeoLoRA,
arXiv 2410.18720, proof of Thm 3): the gradient flow and the Riemannian flow
`Ẇ_r = -P_{M_r} ∇L(W_r)` with the same initial value, normal component at most `ε` along `W_r`,
satisfy `‖W(t) - W_r(t)‖ ≤ ε (e^{β (t - a)} - 1) / β`. -/
theorem gradientFlow_sub_riemannianFlow_le (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β)
    {a b : ℝ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution (fun _ x => -g x) A a b)
    {Y : ℝ → LRState m n} (hYc : ContinuousOn (fun t => (Y t).W) (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => (Y t).W) (-(Y t).P (g (Y t).W)) (Ici t) t)
    (hε : ∀ t ∈ Ico a b, ‖g (Y t).W - (Y t).P (g (Y t).W)‖ ≤ ε) (h0 : A a = (Y a).W) :
    ∀ t ∈ Icc a b, ‖A t - (Y t).W‖ ≤ ε * (Real.exp (β * (t - a)) - 1) / β := by
  have hF : IsLipschitzField (fun (_ : ℝ) x => -g x) β := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  intro t ht
  have := norm_sub_le_gronwallBound hF hβ.le (ηy := 0) (ηz := ε) (δ := 0) hA.cont hA.deriv
    (fun _ _ => by simp) hYc hY (fun s hs => by
      have e : -(Y s).P (g (Y s).W) - -g (Y s).W = g (Y s).W - (Y s).P (g (Y s).W) := by abel
      simpa [e] using hε s hs) (by simp [h0]) t ht
  rw [gronwallBound_of_K_ne_0 hβ.ne'] at this
  simpa [mul_div_assoc, div_mul_eq_mul_div] using this

end ErrorBound

/-! ### Expectations over mini-batches -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The real inner product as a continuous bilinear map. -/
private noncomputable def innerBilin (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 fun x y => by
    simpa using norm_inner_le_norm (𝕜 := ℝ) x y

private lemma integral_inner_eq_of_condExp {𝓖 : MeasurableSpace Ω} (h𝓖 : 𝓖 ≤ mΩ)
    {f Y h : Ω → E} (hf : StronglyMeasurable[𝓖] f) (hfY : Integrable (fun ω => ⟪f ω, Y ω⟫) μ)
    (hY : Integrable Y μ) (hc : μ[Y | 𝓖] =ᵐ[μ] h) :
    ∫ ω, ⟪f ω, Y ω⟫ ∂μ = ∫ ω, ⟪f ω, h ω⟫ ∂μ := by
  have hpull := condExp_bilin_of_stronglyMeasurable_left (μ := μ) (m := 𝓖) (innerBilin E) hf
    (g := Y) (by simpa [innerBilin] using hfY) hY
  calc ∫ ω, ⟪f ω, Y ω⟫ ∂μ = ∫ ω, (μ[fun ω => innerBilin E (f ω) (Y ω) | 𝓖]) ω ∂μ := by
        rw [integral_condExp h𝓖]; simp [innerBilin]
    _ = ∫ ω, ⟪f ω, (μ[Y | 𝓖]) ω⟫ ∂μ := integral_congr_ae (hpull.mono fun ω hω => by
        simpa [innerBilin] using hω)
    _ = ∫ ω, ⟪f ω, h ω⟫ ∂μ := integral_congr_ae (hc.mono fun ω hω => by simp [hω])

omit [CompleteSpace E] in
/-- Pathwise form of one stochastic projected step: expand the descent lemma around the true
gradient. -/
private lemma step_pathwise {ℒ : E → ℝ} {g : E → E} {β G lr : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) {Q : E →L[ℝ] E} (hQ : IsOrthProj Q) (x x₁ y : E) :
    ℒ x₁ ≤ ℒ x - lr * (1 - β * lr / 2) * ‖Q (g x)‖ ^ 2 + β * lr ^ 2 / 2 * ‖y - g x‖ ^ 2 +
      (β * lr ^ 2 - lr) * ⟪Q (g x), y - g x⟫ + G * ‖x₁ - (x - lr • Q y)‖ := by
  set N := y - g x with hN
  have hy : y = g x + N := by rw [hN]; abel
  have hstep : x - lr • Q y - x = -(lr • Q y) := by abel
  have h1 := descent_lemma hℒ hg x (x - lr • Q y)
  rw [hstep, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_neg_right,
    inner_smul_right, real_inner_comm] at h1
  have h2 : ⟪Q y, g x⟫ = ‖Q (g x)‖ ^ 2 + ⟪Q (g x), N⟫ := by
    rw [hy, map_add, inner_add_left, hQ.inner_self_apply, hQ.symm N, real_inner_comm]
  have h3 : ‖Q y‖ ^ 2 = ‖Q (g x)‖ ^ 2 + 2 * ⟪Q (g x), N⟫ + ‖Q N‖ ^ 2 := by
    rw [hy, map_add, norm_add_sq_real, hQ.inner_comp]
  have h4 : ‖Q N‖ ^ 2 ≤ ‖N‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQ.norm_le N) 2
  have h5 : ℒ x₁ ≤ ℒ (x - lr • Q y) + G * ‖x₁ - (x - lr • Q y)‖ := by
    have := (abs_le.1 (abs_energy_sub_le hℒ (x := x₁) (z := x - lr • Q y)
      (fun w _ => hG w))).2
    linarith
  have h6 : β / 2 * lr ^ 2 * ‖Q N‖ ^ 2 ≤ β / 2 * lr ^ 2 * ‖N‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [h2, h3] at h1
  nlinarith

/-- **One step in expectation, abstract form.**  `x` and the projector `Q` are known at the
beginning of the step (`𝓖`-measurable), `Y` is a conditionally unbiased estimator of `∇L(x)`. -/
private theorem expected_step {ℒ : E → ℝ} {g : E → E} {β G lr : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) {𝓖 : MeasurableSpace Ω} (h𝓖 : 𝓖 ≤ mΩ)
    {x x₁ Y : Ω → E} {Q : Ω → E →L[ℝ] E} (hQ : ∀ ω, IsOrthProj (Q ω))
    (hx : StronglyMeasurable[𝓖] x) (hQm : StronglyMeasurable[𝓖] Q)
    (hYm : StronglyMeasurable[mΩ] Y) (hN : Integrable (fun ω => ‖Y ω - g (x ω)‖ ^ 2) μ)
    (hc : μ[Y | 𝓖] =ᵐ[μ] fun ω => g (x ω)) (hLx : Integrable (fun ω => ℒ (x ω)) μ)
    (hx₁ : AEStronglyMeasurable[mΩ] x₁ μ)
    (hd : Integrable (fun ω => ‖x₁ ω - (x ω - lr • Q ω (Y ω))‖) μ) :
    Integrable (fun ω => ℒ (x₁ ω)) μ ∧ ∫ ω, ℒ (x₁ ω) ∂μ ≤ ∫ ω, ℒ (x ω) ∂μ -
      lr * (1 - β * lr / 2) * ∫ ω, ‖Q ω (g (x ω))‖ ^ 2 ∂μ +
      β * lr ^ 2 / 2 * ∫ ω, ‖Y ω - g (x ω)‖ ^ 2 ∂μ +
      G * ∫ ω, ‖x₁ ω - (x ω - lr • Q ω (Y ω))‖ ∂μ := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hgc : Continuous g :=
    (LipschitzWith.of_dist_le_mul (K := ⟨β, hβ⟩) fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; exact hg a b).continuous
  have hℒc : Continuous ℒ := continuous_iff_continuousAt.2 fun a => (hℒ a).continuousAt
  have hgx : StronglyMeasurable[𝓖] fun ω => g (x ω) := hgc.comp_stronglyMeasurable hx
  have hf : StronglyMeasurable[𝓖] fun ω => Q ω (g (x ω)) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E)).continuous.comp_stronglyMeasurable
      (hQm.prodMk hgx)
  have hfm : AEStronglyMeasurable[mΩ] (fun ω => Q ω (g (x ω))) μ :=
    (hf.mono h𝓖).aestronglyMeasurable
  have hgxm : AEStronglyMeasurable[mΩ] (fun ω => g (x ω)) μ := (hgx.mono h𝓖).aestronglyMeasurable
  set N : Ω → E := fun ω => Y ω - g (x ω) with hNdef
  have hNm : AEStronglyMeasurable[mΩ] N μ := hYm.aestronglyMeasurable.sub hgxm
  have hNnorm : Integrable (fun ω => ‖N ω‖) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hN) hNm.norm (ae_of_all _ fun ω => ?_)
    have : 0 ≤ (‖N ω‖ - 1) ^ 2 := sq_nonneg _
    simp only [Pi.add_apply, norm_norm]
    nlinarith [norm_nonneg (N ω)]
  have hNint : Integrable N μ := (integrable_norm_iff hNm).1 hNnorm
  have hgxint : Integrable (fun ω => g (x ω)) μ :=
    Integrable.of_bound hgxm G (ae_of_all _ fun ω => hG _)
  have hYint : Integrable Y μ := by
    have := hNint.add hgxint
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp [hNdef]
  have hfnorm : ∀ ω, ‖Q ω (g (x ω))‖ ≤ G := fun ω => ((hQ ω).norm_le _).trans (hG _)
  have hinner : ∀ {Z : Ω → E}, Integrable (fun ω => ‖Z ω‖) μ → AEStronglyMeasurable[mΩ] Z μ →
      Integrable (fun ω => ⟪Q ω (g (x ω)), Z ω⟫) μ := fun {Z} hZ hZm => by
    refine Integrable.mono' (hZ.const_mul G) (hfm.inner hZm) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hfnorm ω) (norm_nonneg _))
  have hfN : Integrable (fun ω => ⟪Q ω (g (x ω)), N ω⟫) μ := hinner hNnorm hNm
  have hfY : Integrable (fun ω => ⟪Q ω (g (x ω)), Y ω⟫) μ :=
    hinner hYint.norm hYint.aestronglyMeasurable
  have hfg : Integrable (fun ω => ⟪Q ω (g (x ω)), g (x ω)⟫) μ :=
    hinner hgxint.norm hgxm
  have hzero : ∫ ω, ⟪Q ω (g (x ω)), N ω⟫ ∂μ = 0 := by
    have h1 := integral_inner_eq_of_condExp h𝓖 hf hfY hYint hc
    have h2 : (fun ω => ⟪Q ω (g (x ω)), N ω⟫) =
        fun ω => ⟪Q ω (g (x ω)), Y ω⟫ - ⟪Q ω (g (x ω)), g (x ω)⟫ := by
      funext ω; rw [hNdef]; simp [inner_sub_right]
    rw [h2, integral_sub hfY hfg, h1, sub_self]
  have hf2 : Integrable (fun ω => ‖Q ω (g (x ω))‖ ^ 2) μ := by
    refine Integrable.of_bound (hfm.norm.pow 2) (G ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfnorm ω) 2
  have hint1 : Integrable (fun ω => ℒ (x₁ ω)) μ := by
    have hbound : Integrable (fun ω => |ℒ (x ω)| + G * (‖x₁ ω - (x ω - lr • Q ω (Y ω))‖ +
        |lr| * (‖N ω‖ + G))) μ := by
      refine hLx.abs.add ((hd.add ?_).const_mul G)
      exact (hNnorm.add (integrable_const G)).const_mul _
    refine Integrable.mono' hbound (hℒc.comp_aestronglyMeasurable hx₁)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |ℒ (x₁ ω) - ℒ (x ω)| ≤ G * ‖x₁ ω - x ω‖ :=
      abs_energy_sub_le hℒ fun w _ => hG w
    have h2 : ‖x₁ ω - x ω‖ ≤ ‖x₁ ω - (x ω - lr • Q ω (Y ω))‖ + |lr| * (‖N ω‖ + G) := by
      have e : x₁ ω - x ω = (x₁ ω - (x ω - lr • Q ω (Y ω))) - lr • Q ω (Y ω) := by abel
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine ((hQ ω).norm_le _).trans ?_
      have e2 : Y ω = N ω + g (x ω) := by simp [hNdef]
      rw [e2]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (hG _))
    have h3 := abs_sub_abs_le_abs_sub (ℒ (x₁ ω)) (ℒ (x ω))
    have h4 := mul_le_mul_of_nonneg_left h2 hG0
    linarith
  refine ⟨hint1, ?_⟩
  have hR0 : Integrable (fun ω => ℒ (x ω) - lr * (1 - β * lr / 2) * ‖Q ω (g (x ω))‖ ^ 2) μ :=
    hLx.sub (hf2.const_mul _)
  have hR1 : Integrable (fun ω => ℒ (x ω) - lr * (1 - β * lr / 2) * ‖Q ω (g (x ω))‖ ^ 2 +
      β * lr ^ 2 / 2 * ‖Y ω - g (x ω)‖ ^ 2) μ := hR0.add (hN.const_mul _)
  have hR2 : Integrable (fun ω => ℒ (x ω) - lr * (1 - β * lr / 2) * ‖Q ω (g (x ω))‖ ^ 2 +
      β * lr ^ 2 / 2 * ‖Y ω - g (x ω)‖ ^ 2 + (β * lr ^ 2 - lr) * ⟪Q ω (g (x ω)), N ω⟫) μ :=
    hR1.add (hfN.const_mul _)
  have hR3 : Integrable (fun ω => ℒ (x ω) - lr * (1 - β * lr / 2) * ‖Q ω (g (x ω))‖ ^ 2 +
      β * lr ^ 2 / 2 * ‖Y ω - g (x ω)‖ ^ 2 + (β * lr ^ 2 - lr) * ⟪Q ω (g (x ω)), N ω⟫ +
      G * ‖x₁ ω - (x ω - lr • Q ω (Y ω))‖) μ := hR2.add (hd.const_mul G)
  have hmono := integral_mono hint1 hR3 fun ω =>
    step_pathwise (lr := lr) hℒ hg hβ hG (hQ ω) (x ω) (x₁ ω) (Y ω)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add hR2 (hd.const_mul G), integral_add hR1 (hfN.const_mul _),
    integral_add hR0 (hN.const_mul _), integral_sub hLx (hf2.const_mul _)]
  simp only [integral_const_mul]
  rw [hzero]
  ring

end Abstract

section Trajectory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Stochastic DLRT with fresh mini-batches** (arXiv 2601.08882, Sec. 2; GeoLoRA, arXiv
2410.18720, Alg. 1): one local iteration per step, `𝓕 t` the information before step `t`.

* The bases are built from the *full* gradient at `W_t` (as written in the paper) and from the
  past: `G₀ = ∇L(W_t)` and `Π_t` is `𝓕 t`-measurable.
* The S-step uses the estimator `Ĝ_t`, which is conditionally unbiased and has conditional
  variance at most `σ²` on average: `E[Ĝ_t | 𝓕_t] = ∇L(W_t)`, `E‖Ĝ_t - ∇L(W_t)‖² ≤ σ²`.  For
  mini-batches, `Ĝ_t = ∇L(W_t, ξ_t)`.
* `measP` only says that the quantity in the conclusion is a random variable.  (Lean's integral of a
  non-measurable function is `0`, so without it the conclusion would say nothing.)

The hypothesis that `Π_t` is known before the batch `ξ_t` is drawn is essential: otherwise
`E⟪∇L(W_t), Π_t Ĝ_t⟫ = E‖Π_t ∇L(W_t)‖²` is not available. -/
structure IsStochasticDLRT (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω)
    (g : Matrix m n ℝ → Matrix m n ℝ) (Ghat : ℕ → Ω → Matrix m n ℝ) (lr : ℕ → ℝ)
    (ϑ : ℕ → Ω → ℝ) (σ : ℝ) (X : ℕ → Ω → LRState m n) (D : ℕ → Ω → StepData m n) : Prop where
  step : ∀ t ω, IsDLRTStep (g (X t ω).W) (fun _ => Ghat t ω) (lr t) 1 (ϑ t ω) (X t ω) (D t ω)
  next : ∀ t ω, X (t + 1) ω = (D t ω).next
  adaptedW : ∀ t, StronglyMeasurable[𝓕 t] fun ω => (X t ω).W
  adaptedGal : ∀ t, StronglyMeasurable[𝓕 t] fun ω => (D t ω).gal
  adaptedG : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (Ghat t)
  unbiased : ∀ t, μ[Ghat t | 𝓕 t] =ᵐ[μ] fun ω => g (X t ω).W
  intVar : ∀ t, Integrable (fun ω => ‖Ghat t ω - g (X t ω).W‖ ^ 2) μ
  var : ∀ t, ∫ ω, ‖Ghat t ω - g (X t ω).W‖ ^ 2 ∂μ ≤ σ ^ 2
  intϑ : ∀ t, Integrable (ϑ t) μ
  measP : ∀ t, AEStronglyMeasurable (fun ω => (X t ω).P (g (X t ω).W)) μ

namespace IsStochasticDLRT

variable {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {g : Matrix m n ℝ → Matrix m n ℝ} {Ghat : ℕ → Ω → Matrix m n ℝ} {lr : ℕ → ℝ}
  {ϑ : ℕ → Ω → ℝ} {σ : ℝ} {X : ℕ → Ω → LRState m n} {D : ℕ → Ω → StepData m n}

omit [IsProbabilityMeasure μ] in
private lemma What_one (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D) (t : ℕ) (ω : Ω) :
    (D t ω).What 1 = (X t ω).W - lr t • (D t ω).gal (Ghat t ω) := by
  rw [(h.step t ω).What_succ one_pos, (h.step t ω).start_eq, projGradStep]

omit [IsProbabilityMeasure μ] in
private lemma measurable_err (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D) (t : ℕ) :
    AEStronglyMeasurable[mΩ]
      (fun ω => (X (t + 1) ω).W - ((X t ω).W - lr t • (D t ω).gal (Ghat t ω))) μ := by
  have hx₁ := ((h.adaptedW (t + 1)).mono (𝓕.le _)).aestronglyMeasurable (μ := μ)
  have hx := ((h.adaptedW t).mono (𝓕.le _)).aestronglyMeasurable (μ := μ)
  have hQ : StronglyMeasurable[mΩ] fun ω => (D t ω).gal := (h.adaptedGal t).mono (𝓕.le _)
  have hY : StronglyMeasurable[mΩ] (Ghat t) := (h.adaptedG t).mono (𝓕.le _)
  have hQY : StronglyMeasurable[mΩ] fun ω => (D t ω).gal (Ghat t ω) := by
    have := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Matrix m n ℝ)
      (F := Matrix m n ℝ)).continuous.comp_stronglyMeasurable (hQ.prodMk hY)
    exact this
  exact hx₁.sub (hx.sub (hQY.aestronglyMeasurable.const_smul (lr t)))

omit [IsProbabilityMeasure μ] in
/-- The expected truncation error of arXiv 2601.08882, Sec. 2, Convergence, is finite. -/
theorem integrable_trunc (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D) (t : ℕ) :
    Integrable (fun ω => ‖(D t ω).next.W - (D t ω).What 1‖) μ := by
  have hm : AEStronglyMeasurable[mΩ] (fun ω => ‖(D t ω).next.W - (D t ω).What 1‖) μ := by
    have := (h.measurable_err t).norm
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [h.What_one, h.next]
  refine Integrable.mono' (h.intϑ t) hm (ae_of_all _ fun ω => ?_)
  rw [norm_norm]
  exact (h.step t ω).norm_next_sub_What_lt.le

variable {ℒ : Matrix m n ℝ → ℝ} {β G : ℝ}

private theorem step_bound (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) (t : ℕ) (hL : Integrable (fun ω => ℒ (X t ω).W) μ) :
    Integrable (fun ω => ℒ (X (t + 1) ω).W) μ ∧
      ∫ ω, ℒ (X (t + 1) ω).W ∂μ ≤ ∫ ω, ℒ (X t ω).W ∂μ -
        lr t * (1 - β * lr t / 2) * ∫ ω, ‖(D t ω).gal (g (X t ω).W)‖ ^ 2 ∂μ +
        β * lr t ^ 2 / 2 * σ ^ 2 + G * ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ := by
  have e : (fun ω => ‖(X (t + 1) ω).W - ((X t ω).W - lr t • (D t ω).gal (Ghat t ω))‖) =
      fun ω => ‖(D t ω).next.W - (D t ω).What 1‖ := by
    funext ω
    rw [h.What_one, h.next]
  have hd := h.integrable_trunc t
  rw [← e] at hd
  obtain ⟨hint, hle⟩ := expected_step (lr := lr t) hℒ hg hβ hG (𝓕.le t)
    (x := fun ω => (X t ω).W) (x₁ := fun ω => (X (t + 1) ω).W) (Y := Ghat t)
    (Q := fun ω => (D t ω).gal) (fun ω => (h.step t ω).isOrthProj_gal) (h.adaptedW t)
    (h.adaptedGal t) ((h.adaptedG t).mono (𝓕.le _)) (h.intVar t) (h.unbiased t) hL
    ((h.adaptedW (t + 1)).mono (𝓕.le _)).aestronglyMeasurable hd
  refine ⟨hint, hle.trans ?_⟩
  rw [e]
  have h1 : β * lr t ^ 2 / 2 * ∫ ω, ‖Ghat t ω - g (X t ω).W‖ ^ 2 ∂μ ≤ β * lr t ^ 2 / 2 * σ ^ 2 :=
    mul_le_mul_of_nonneg_left (h.var t) (by positivity)
  linarith

/-- In the setting of arXiv 2601.08882, Sec. 2, Convergence: `L(W_t)` is integrable for all `t` if
it is for `t = 0`. -/
theorem integrable_loss (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) (hL : Integrable (fun ω => ℒ (X 0 ω).W) μ) (t : ℕ) :
    Integrable (fun ω => ℒ (X t ω).W) μ := by
  induction t with
  | zero => exact hL
  | succ t ih => exact (h.step_bound hℒ hg hβ hG t ih).1

private theorem integrable_gal_sq (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D) (hβ : 0 ≤ β)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hG : ∀ x, ‖g x‖ ≤ G) (t : ℕ) :
    Integrable (fun ω => ‖(D t ω).gal (g (X t ω).W)‖ ^ 2) μ := by
  have hgc : Continuous g :=
    (LipschitzWith.of_dist_le_mul (K := ⟨β, hβ⟩) fun a b => by
      rw [dist_eq_norm, dist_eq_norm]; exact hg a b).continuous
  have hgx : StronglyMeasurable[𝓕 t] fun ω => g (X t ω).W :=
    hgc.comp_stronglyMeasurable (h.adaptedW t)
  have hf : StronglyMeasurable[𝓕 t] fun ω => (D t ω).gal (g (X t ω).W) := by
    have h2 := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Matrix m n ℝ)
      (F := Matrix m n ℝ)).continuous.comp_stronglyMeasurable ((h.adaptedGal t).prodMk hgx)
    exact h2
  have hfm : AEStronglyMeasurable[mΩ] (fun ω => (D t ω).gal (g (X t ω).W)) μ :=
    (hf.mono (𝓕.le t)).aestronglyMeasurable
  refine Integrable.of_bound (hfm.norm.pow 2) (G ^ 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (((h.step t ω).isOrthProj_gal.norm_le _).trans (hG _)) 2

private theorem integrable_P_sq (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hG : ∀ x, ‖g x‖ ≤ G) (t : ℕ) :
    Integrable (fun ω => ‖(X t ω).P (g (X t ω).W)‖ ^ 2) μ := by
  refine Integrable.of_bound ((h.measP t).norm.pow 2) (G ^ 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (((h.step t ω).valid.isOrthProj_P.norm_le _).trans (hG _)) 2

/-- **Loss descent in expectation, corrected** (arXiv 2601.08882, Sec. 2, Convergence, and GeoLoRA,
arXiv 2410.18720, Thm 1).  For stochastic DLRT (`IsStochasticDLRT`) with fresh mini-batches,
gradients bounded by `G`, and `0 ≤ lr ≤ 2 / β`,

  `E L(W_{t+1}) ≤ E L(W_t) - lr (1 - β lr / 2) E‖P_{M_r} ∇L(W_t)‖²
      + β lr² σ² / 2 + G E‖W_{t+1} - Û S̃ V̂ᵀ‖`.

Differences from the paper.  The printed inequality has the stochastic gradient `∇L(W_t, ξ_t)`
inside the norm and no variance term: this is false (`fresh_batch_descent_false`).  Here the norm
contains the population gradient, and the price of the noise is the term `β lr² σ² / 2`.  For
`W_0` deterministic and `t = 0` this is the one-step statement `E_ξ`; the expectation is the total
expectation for general `t`.  One local iteration per step (`s⋆ = 1`), as in the cited proof.  The
same-batch reading under which the printed inequality does hold is `sameBatch_loss_descent`. -/
theorem expected_loss_descent (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) (hL : Integrable (fun ω => ℒ (X 0 ω).W) μ) (t : ℕ)
    (hlr : 0 ≤ lr t) (hlr2 : β * lr t ≤ 2) :
    ∫ ω, ℒ (X (t + 1) ω).W ∂μ ≤ ∫ ω, ℒ (X t ω).W ∂μ -
      lr t * (1 - β * lr t / 2) * ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ +
      β * lr t ^ 2 / 2 * σ ^ 2 + G * ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ := by
  have h1 := (h.step_bound hℒ hg hβ hG t (h.integrable_loss hℒ hg hβ hG hL t)).2
  have h2 : ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ ≤ ∫ ω, ‖(D t ω).gal (g (X t ω).W)‖ ^ 2 ∂μ :=
    integral_mono (h.integrable_P_sq hG t) (h.integrable_gal_sq hβ hg hG t) fun ω =>
      pow_le_pow_left₀ (norm_nonneg _) (h.step t ω).norm_P_le 2
  have h3 := mul_le_mul_of_nonneg_left h2
    (mul_nonneg hlr (by linarith : (0 : ℝ) ≤ 1 - β * lr t / 2))
  linarith

/-- Stationarity in expectation (arXiv 2601.08882, Sec. 2, Convergence), explicit form of
`liminf_expected_tangentGrad_sq`. -/
theorem exists_expected_tangentGrad_sq_lt (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) (hL : Integrable (fun ω => ℒ (X 0 ω).W) μ)
    (hlr : ∀ t, 0 ≤ lr t) (hlr2 : ∀ t, β * lr t ≤ 2) (hdiv : ¬ Summable lr)
    (hsq : Summable fun t => lr t ^ 2) {ℒinf C : ℝ} (hinf : ∀ t ω, ℒinf ≤ ℒ (X t ω).W)
    (hC : ∀ N, ∑ t ∈ range N, ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ ≤ C) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) :
    ∃ t, N ≤ t ∧ ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ < ε := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hw : ∀ t, 0 ≤ lr t * (1 - β * lr t / 2) := fun t =>
    mul_nonneg (hlr t) (by linarith [hlr2 t])
  have hwdiv : ¬ Summable fun t => lr t * (1 - β * lr t / 2) := by
    intro hsum
    apply hdiv
    have e : lr = fun t => lr t * (1 - β * lr t / 2) + β / 2 * lr t ^ 2 := by
      funext t; ring
    rw [e]
    exact hsum.add (hsq.mul_left (β / 2))
  have hnn : ∀ t, 0 ≤ ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ := fun t =>
    integral_nonneg fun ω => sq_nonneg _
  refine exists_lt_of_sum_mul_le hw hnn hwdiv
    (C := ∫ ω, ℒ (X 0 ω).W ∂μ - ℒinf + β / 2 * σ ^ 2 * (∑' t, lr t ^ 2) + G * C)
    (fun M => ?_) hε N
  have hstepdesc := fun t => h.expected_loss_descent hℒ hg hβ hG hL t (hlr t) (hlr2 t)
  have hsum := sum_le_of_le_sub_add (u := fun t => ∫ ω, ℒ (X t ω).W ∂μ)
    (a := fun t => lr t * (1 - β * lr t / 2) * ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ)
    (e := fun t => β / 2 * σ ^ 2 * lr t ^ 2 + G * ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ)
    (fun t => by have := hstepdesc t; nlinarith) M
  have h1 : ℒinf ≤ ∫ ω, ℒ (X M ω).W ∂μ := by
    have := integral_mono (integrable_const ℒinf) (h.integrable_loss hℒ hg hβ hG hL M)
      fun ω => hinf M ω
    simpa using this
  have h2 : ∑ t ∈ range M, lr t ^ 2 ≤ ∑' t, lr t ^ 2 :=
    hsq.sum_le_tsum _ fun _ _ => sq_nonneg _
  have h3 : ∑ t ∈ range M, (β / 2 * σ ^ 2 * lr t ^ 2 +
      G * ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ) ≤
      β / 2 * σ ^ 2 * (∑' t, lr t ^ 2) + G * C := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add (mul_le_mul_of_nonneg_left h2 (by positivity))
      (mul_le_mul_of_nonneg_left (hC M) hG0)
  linarith

/-- **Stationarity in expectation** (arXiv 2601.08882, Sec. 2, Convergence; GeoLoRA, arXiv
2410.18720, Thm 2): for stochastic DLRT with Robbins–Monro learning rates, `β lr_t ≤ 2`, a loss
bounded below and bounded accumulated expected truncation errors,

  `liminf_t E‖P_{M_r} ∇L(W_t)‖² = 0`.

The norm contains the population gradient.  The printed statement has `∇L(W_t, ξ_t)` there, and is
false: `not_stationarity_of_batch_gradient`. -/
theorem liminf_expected_tangentGrad_sq (h : IsStochasticDLRT 𝓕 μ g Ghat lr ϑ σ X D)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hβ : 0 ≤ β) (hG : ∀ x, ‖g x‖ ≤ G) (hL : Integrable (fun ω => ℒ (X 0 ω).W) μ)
    (hlr : ∀ t, 0 ≤ lr t) (hlr2 : ∀ t, β * lr t ≤ 2) (hdiv : ¬ Summable lr)
    (hsq : Summable fun t => lr t ^ 2) {ℒinf C : ℝ} (hinf : ∀ t ω, ℒinf ≤ ℒ (X t ω).W)
    (hC : ∀ N, ∑ t ∈ range N, ∫ ω, ‖(D t ω).next.W - (D t ω).What 1‖ ∂μ ≤ C) :
    liminf (fun t => ∫ ω, ‖(X t ω).P (g (X t ω).W)‖ ^ 2 ∂μ) atTop = 0 :=
  liminf_eq_zero_of_forall_exists_lt (fun _ => integral_nonneg fun _ => sq_nonneg _)
    fun _ hε N => h.exists_expected_tangentGrad_sq_lt hℒ hg hβ hG hL hlr hlr2 hdiv hsq hinf hC hε N

end IsStochasticDLRT

/-- **The reading under which the printed descent inequality holds** (arXiv 2601.08882, Sec. 2,
Convergence; this is what the proof of GeoLoRA, arXiv 2410.18720, Thm 1, shows): if the bases and
the S-step use the same batch `ξ`, and the loss after the step is evaluated **on that same batch**,

  `E_ξ[L(W₁^ξ, ξ)] ≤ E_ξ[L(W, ξ)] - lr (1 - β lr / 2) E_ξ‖P_{M_r} ∇L(W, ξ)‖²
      + G E_ξ‖W₁^ξ - Û^ξ S̃^ξ V̂^ξᵀ‖`,

for any `s⋆ ≥ 1`.  This is the deterministic inequality for each batch, integrated.  The left side
is the training loss on the batch just used, not `L(W₁)`, so that this inequality does not
telescope.  Integrability of the truncated iterates is assumed, since measurability of an SVD
selection is not automatic; for mini-batches `Ξ` is finite and it is automatic. -/
theorem sameBatch_loss_descent {Ξ : Type*} {mΞ : MeasurableSpace Ξ} {ν : Measure Ξ}
    {ℒ : Ξ → Matrix m n ℝ → ℝ} {g : Ξ → Matrix m n ℝ → Matrix m n ℝ} {β G lr ϑ : ℝ} {sStar : ℕ}
    {X : LRState m n} {D : Ξ → StepData m n}
    (hℒ : ∀ ξ x, HasFDerivAt (ℒ ξ) (innerSL ℝ (g ξ x)) x)
    (hg : ∀ ξ x y, ‖g ξ x - g ξ y‖ ≤ β * ‖x - y‖)
    (hstep : ∀ ξ, IsDLRTStep (g ξ X.W) (g ξ) lr sStar ϑ X (D ξ)) (hlr : 0 ≤ lr)
    (hlr2 : β * lr ≤ 2) (hs : 0 < sStar)
    (hG : ∀ ξ, ∀ w ∈ segment ℝ ((D ξ).What sStar) (D ξ).next.W, ‖g ξ w‖ ≤ G)
    (h1 : Integrable (fun ξ => ℒ ξ (D ξ).next.W) ν) (h2 : Integrable (fun ξ => ℒ ξ X.W) ν)
    (h3 : Integrable (fun ξ => ‖X.P (g ξ X.W)‖ ^ 2) ν)
    (h4 : Integrable (fun ξ => ‖(D ξ).next.W - (D ξ).What sStar‖) ν) :
    ∫ ξ, ℒ ξ (D ξ).next.W ∂ν ≤ ∫ ξ, ℒ ξ X.W ∂ν -
      lr * (1 - β * lr / 2) * ∫ ξ, ‖X.P (g ξ X.W)‖ ^ 2 ∂ν +
      G * ∫ ξ, ‖(D ξ).next.W - (D ξ).What sStar‖ ∂ν := by
  have hR0 : Integrable (fun ξ => ℒ ξ X.W - lr * (1 - β * lr / 2) * ‖X.P (g ξ X.W)‖ ^ 2) ν :=
    h2.sub (h3.const_mul _)
  have hR1 : Integrable (fun ξ => ℒ ξ X.W - lr * (1 - β * lr / 2) * ‖X.P (g ξ X.W)‖ ^ 2 +
      G * ‖(D ξ).next.W - (D ξ).What sStar‖) ν := hR0.add (h4.const_mul G)
  have hmono := integral_mono h1 hR1 fun ξ =>
    loss_dlrtStep_le (hℒ ξ) (hg ξ) (hstep ξ) hlr hlr2 hs (hG ξ)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add hR0 (h4.const_mul G), integral_sub h2 (h3.const_mul _)]
  simp only [integral_const_mul]

end Trajectory

/-! ### Counterexamples

All counterexamples live on `2 × 2` matrices with rank `r = 1`, at states
`W = [a b; 0 0] = e₀ (a, b)`, so that the low-rank structure is genuine. -/

section Examples

/-- A matrix with a single nonzero row. -/
def row (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 0 then (if j = 0 then a else b) else 0

/-- The first unit vector, as a basis matrix. -/
def e₀ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- The Euclidean length of `(a, b)`. -/
noncomputable def rowLen (a b : ℝ) : ℝ := √(a ^ 2 + b ^ 2)

/-- The normalized row, as the right basis. -/
noncomputable def rowV (a b : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun i _ => if i = 0 then a / rowLen a b else b / rowLen a b

/-- The factorization `[a b; 0 0] = e₀ [ρ] vᵀ`, `ρ = ‖(a, b)‖`, `v = (a, b) / ρ`. -/
noncomputable def rowState (a b : ℝ) : LRState (Fin 2) (Fin 2) :=
  ⟨1, e₀, diagonal fun _ => rowLen a b, rowV a b⟩

/-- A `1 × 2` coefficient matrix. -/
def rowCoef (a b : ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  Matrix.of fun _ j => if j = 0 then a else b

/-- The internal data of the step from `[a b; 0 0]` to `[a' b'; 0 0]`, with `Û = e₀`, `V̂ = I`. -/
noncomputable def rowData (a b a' b' : ℝ) : StepData (Fin 2) (Fin 2) :=
  ⟨1, 2, 1, 0, e₀, 1, fun s => if s = 0 then rowCoef a b else rowCoef a' b', 1, rowV a' b',
    fun _ => rowLen a' b', 0, 0, Fin.elim0⟩

lemma rowLen_pos {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < rowLen a b := by
  refine Real.sqrt_pos.2 ?_
  rcases h with h | h
  · have := sq_pos_of_ne_zero h; positivity
  · have := sq_pos_of_ne_zero h; positivity

lemma rowV_orth {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (rowV a b)ᵀ * rowV a b = 1 := by
  have hρ := rowLen_pos h
  have h2 : rowLen a b ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i; fin_cases j
  simp [rowV, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  nlinarith

lemma e₀_orth : e₀ᵀ * e₀ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [e₀, Matrix.mul_apply]

lemma e₀_mul_row (p q : ℝ) : e₀ * e₀ᵀ * row p q = row p q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₀, row, Matrix.mul_apply]

lemma rowState_W {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (rowState a b).W = row a b := by
  have hρ := rowLen_pos h
  change e₀ * (diagonal fun _ : Fin 1 => rowLen a b) * (rowV a b)ᵀ = row a b
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀, rowV, row, Matrix.mul_apply] <;> field_simp

lemma rowState_valid {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (rowState a b).IsValid where
  orthU := e₀_orth
  orthV := rowV_orth h
  invS := by
    change IsUnit (diagonal fun _ : Fin 1 => rowLen a b).det
    rw [det_diagonal]
    simpa using (rowLen_pos h).ne'

/-- At a state with left basis `e₀`, the tangent projector is the identity on matrices with a
single nonzero row. -/
lemma rowState_P (a b p q : ℝ) : (rowState a b).P (row p q) = row p q := by
  change tangentProj e₀ (rowV a b) (row p q) = row p q
  rw [tangentProj_apply, e₀_mul_row]
  abel

lemma e₀_mul_coef (a b : ℝ) : e₀ * rowCoef a b = row a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀, rowCoef, row, Matrix.mul_apply]

lemma rowData_What_zero (a b a' b' : ℝ) : (rowData a b a' b').What 0 = row a b := by
  change e₀ * rowCoef a b * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = row a b
  rw [transpose_one, Matrix.mul_one, e₀_mul_coef]

lemma rowData_What_one (a b a' b' : ℝ) : (rowData a b a' b').What 1 = row a' b' := by
  change e₀ * rowCoef a' b' * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = row a' b'
  rw [transpose_one, Matrix.mul_one, e₀_mul_coef]

lemma rowData_next (a b a' b' : ℝ) : (rowData a b a' b').next = rowState a' b' := by
  have key : (⟨1, e₀ * (1 : Matrix (Fin 1) (Fin 1) ℝ), diagonal fun _ : Fin 1 => rowLen a' b',
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * rowV a' b'⟩ : LRState (Fin 2) (Fin 2)) = rowState a' b' := by
    rw [Matrix.mul_one, Matrix.one_mul]
    rfl
  exact key

lemma e₀_transpose_mul_row (p q : ℝ) : e₀ᵀ * row p q = rowCoef p q := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [e₀, rowCoef, row, Matrix.mul_apply]

lemma rowCoef_eq {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    (diagonal fun _ : Fin 1 => rowLen a b) * (rowV a b)ᵀ = rowCoef a b := by
  have hρ := rowLen_pos h
  ext i j
  fin_cases i
  fin_cases j <;> simp [rowCoef, rowV, Matrix.mul_apply] <;> field_simp

/-- The step of arXiv 2601.08882, Sec. 2, from `[a b; 0 0]` to `[a - lr p', b - lr q'; 0 0]`.  The
gradient information `G₀` and the value of the S-step field `f` at `W` must lie in the first row.
No singular value is discarded (`W₁ = Û S̃ V̂ᵀ` has rank one). -/
theorem rowData_isStep {a b p q p' q' lr ϑ : ℝ}
    {f : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : a ≠ 0 ∨ b ≠ 0) (hf : f (row a b) = row p' q') (h' : a - lr * p' ≠ 0 ∨ b - lr * q' ≠ 0)
    (hϑ : 0 < ϑ) :
    IsDLRTStep (row p q) f lr 1 ϑ (rowState a b)
      (rowData a b (a - lr * p') (b - lr * q')) where
  valid := rowState_valid h
  orthUhat := e₀_orth
  orthVhat := by
    have key : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp
    exact key
  spanU := by
    change e₀ * e₀ᵀ * e₀ = e₀
    rw [Matrix.mul_assoc, e₀_orth, Matrix.mul_one]
  spanV := by
    have key : (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * rowV a b =
        rowV a b := by simp
    exact key
  spanGU := by
    change e₀ * e₀ᵀ * (row p q * rowV a b * (diagonal fun _ : Fin 1 => rowLen a b)ᵀ) =
      row p q * rowV a b * (diagonal fun _ : Fin 1 => rowLen a b)ᵀ
    rw [Matrix.mul_assoc (row p q), ← Matrix.mul_assoc (e₀ * e₀ᵀ), e₀_mul_row]
  spanGV := by
    have key : (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        ((row p q)ᵀ * e₀ * diagonal fun _ : Fin 1 => rowLen a b) =
        (row p q)ᵀ * e₀ * diagonal fun _ : Fin 1 => rowLen a b := by simp
    exact key
  start := by
    have key : rowCoef a b = e₀ᵀ * e₀ * (diagonal fun _ : Fin 1 => rowLen a b) * (rowV a b)ᵀ *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [e₀_orth, Matrix.one_mul, Matrix.mul_one, rowCoef_eq h]
    exact key
  iter := by
    intro s hs
    obtain rfl : s = 0 := by omega
    rw [rowData_What_zero, hf]
    have key : rowCoef (a - lr * p') (b - lr * q') =
        rowCoef a b - lr • (e₀ᵀ * row p' q' * (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      rw [Matrix.mul_one, e₀_transpose_mul_row]
      ext i j
      fin_cases i
      fin_cases j <;> simp [rowCoef]
    exact key
  trunc :=
    { orthP₁ := by
        have key : (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by simp
        exact key
      orthQ₁ := rowV_orth h'
      orthP₂ := Matrix.ext fun i _ => Fin.elim0 i
      orthQ₂ := Matrix.ext fun i _ => Fin.elim0 i
      crossP := Matrix.ext fun _ j => Fin.elim0 j
      crossQ := Matrix.ext fun _ j => Fin.elim0 j
      pos₁ := fun _ => rowLen_pos h'
      nonneg₂ := fun j => Fin.elim0 j
      ordered := fun _ j => Fin.elim0 j
      svd := by
        have key : rowCoef (a - lr * p') (b - lr * q') =
            (1 : Matrix (Fin 1) (Fin 1) ℝ) *
              (diagonal fun _ : Fin 1 => rowLen (a - lr * p') (b - lr * q')) *
              (rowV (a - lr * p') (b - lr * q'))ᵀ +
            (0 : Matrix (Fin 1) (Fin 0) ℝ) * diagonal (Fin.elim0 : Fin 0 → ℝ) *
              (0 : Matrix (Fin 2) (Fin 0) ℝ)ᵀ := by
          rw [Matrix.one_mul, rowCoef_eq h']
          ext i j
          simp
        exact key
      tail := by
        have key : √(∑ j : Fin 0, (Fin.elim0 j : ℝ) ^ 2) < ϑ := by simpa using hϑ
        exact key }

lemma norm_row_sq (a b : ℝ) : ‖row a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  simp [row, Fin.sum_univ_two]

lemma norm_row_zero (c : ℝ) : ‖row 0 c‖ = |c| := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_row_sq, zero_pow two_ne_zero, zero_add,
    Real.sqrt_sq_eq_abs]

lemma row_sub_row (a b c d : ℝ) : row a b - row c d = row (a - c) (b - d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

@[simp] lemma row_apply_zero_one (a b : ℝ) : row a b 0 1 = b := by simp [row]

lemma inner_row (p q : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    ⟪row p q, W⟫ = p * W 0 0 + q * W 0 1 := by
  rw [Frobenius.inner_def]
  simp [row, Fin.sum_univ_two]

/-- The quadratic loss `‖W‖² / 2`. -/
noncomputable def quadLoss (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ‖W‖ ^ 2 / 2

/-- For use in the counterexample `printed_coefficient_false` to arXiv 2601.08882, Sec. 2:
`∇(‖W‖² / 2) = W`. -/
theorem hasFDerivAt_quadLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt quadLoss (innerSL ℝ (id W)) W := by
  have h := ((hasStrictFDerivAt_norm_sq W).hasFDerivAt).const_mul (1 / 2 : ℝ)
  have e : quadLoss = fun Z => (1 / 2 : ℝ) * ‖Z‖ ^ 2 := by
    funext Z; simp [quadLoss]; ring
  rw [e]
  refine h.congr_fderiv ?_
  ext H
  simp [innerSL_apply_apply]

/-- **The printed coefficient is a misprint** (arXiv 2601.08882, Sec. 2, Convergence, and GeoLoRA,
arXiv 2410.18720, eq. (11), which print `1 - L λ² / 2`).  Deterministically and without truncation
error, for `L(W) = ‖W‖² / 2`, which has `1`-Lipschitz gradient, and every `0 < lr < 1`, the printed
inequality with `L = 1` fails.  The coefficient `1 - L λ / 2` of `loss_dlrtStep_le` is what the
proof in 2410.18720 gives. -/
theorem printed_coefficient_false {lr ϑ : ℝ} (hlr : 0 < lr) (hlr1 : lr < 1) (hϑ : 0 < ϑ) :
    ∃ (X : LRState (Fin 2) (Fin 2)) (D : StepData (Fin 2) (Fin 2)),
      IsDLRTStep (id X.W) id lr 1 ϑ X D ∧
      ¬ quadLoss D.next.W ≤ quadLoss X.W - lr * (1 - 1 * lr ^ 2 / 2) * ‖X.P (id X.W)‖ ^ 2 +
        1 * ‖D.next.W - D.What 1‖ := by
  have h10 : (1 : ℝ) ≠ 0 ∨ (0 : ℝ) ≠ 0 := Or.inl one_ne_zero
  have hne : (1 : ℝ) - lr * 1 ≠ 0 ∨ (0 : ℝ) - lr * 0 ≠ 0 :=
    Or.inl (by rw [mul_one]; exact sub_ne_zero.2 hlr1.ne')
  have hW : (rowState 1 0).W = row 1 0 := rowState_W h10
  refine ⟨rowState 1 0, rowData 1 0 (1 - lr * 1) (0 - lr * 0), ?_, ?_⟩
  · rw [id, hW]
    exact rowData_isStep h10 rfl hne hϑ
  · rw [rowData_next, rowData_What_one, rowState_W hne, sub_self, norm_zero, id, hW, rowState_P,
      quadLoss, quadLoss, norm_row_sq, norm_row_sq]
    intro hle
    have h1 : 0 < lr * lr * (1 - lr) := mul_pos (mul_pos hlr hlr) (sub_pos.2 hlr1)
    nlinarith

/-- The loss `L(W) = 1 + cos W₀₁` of the counterexamples.  It is nonnegative, its gradient is
bounded by `1` and `1`-Lipschitz (`hasFDerivAt_cosLoss`, `cosLoss_nonneg`, `norm_cosGrad_le`,
`cosGrad_lipschitz`), so that it satisfies all the assumptions of GeoLoRA, arXiv 2410.18720, with
`L = B = 1`. -/
noncomputable def cosLoss (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := 1 + Real.cos (W 0 1)

/-- The gradient of `cosLoss`. -/
noncomputable def cosGrad (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  row 0 (-Real.sin (W 0 1))

/-- The loss of the batch with sign `s`: `1 + cos W₀₁ - s W₀₁`. -/
noncomputable def batchLoss (s : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  1 + Real.cos (W 0 1) - s * W 0 1

/-- The gradient of `batchLoss`. -/
noncomputable def batchGrad (s : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  row 0 (-Real.sin (W 0 1) - s)

lemma cosLoss_nonneg (W : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ cosLoss W := by
  have := Real.neg_one_le_cos (W 0 1)
  simp only [cosLoss]; linarith

lemma norm_cosGrad_le (W : Matrix (Fin 2) (Fin 2) ℝ) : ‖cosGrad W‖ ≤ 1 := by
  rw [cosGrad, norm_row_zero, abs_neg]
  exact Real.abs_sin_le_one _

/-- The loss of the counterexamples to arXiv 2601.08882, Sec. 2, has a `1`-Lipschitz gradient. -/
theorem cosGrad_lipschitz (x y : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖cosGrad x - cosGrad y‖ ≤ 1 * ‖x - y‖ := by
  rw [cosGrad, cosGrad, row_sub_row, sub_self, norm_row_zero, one_mul]
  have h1 : |(-Real.sin (x 0 1)) - (-Real.sin (y 0 1))| =
      |Real.sin (x 0 1) - Real.sin (y 0 1)| := by
    rw [neg_sub_neg, abs_sub_comm]
  rw [h1]
  refine (Real.abs_sin_sub_sin_le _ _).trans ?_
  simpa using Frobenius.abs_apply_le_norm (x - y) 0 1

/-- The gradient of the batch losses in the counterexamples to arXiv 2601.08882, Sec. 2. -/
theorem hasFDerivAt_batchLoss (s : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt (batchLoss s) (innerSL ℝ (batchGrad s W)) W := by
  have h1 : HasFDerivAt (fun Z : Matrix (Fin 2) (Fin 2) ℝ => ⟪row 0 1, Z⟫)
      (innerSL ℝ (row 0 1)) W := (innerSL ℝ (row 0 1)).hasFDerivAt
  have h2 := (h1.cos.const_add 1).sub (h1.const_mul s)
  have e : batchLoss s = fun Z => 1 + Real.cos ⟪row 0 1, Z⟫ - s * ⟪row 0 1, Z⟫ := by
    funext Z
    simp [batchLoss, inner_row]
  rw [e]
  refine h2.congr_fderiv ?_
  ext H
  simp [batchGrad, inner_row, innerSL_apply_apply]
  ring

/-- The gradient of the loss in the counterexamples to arXiv 2601.08882, Sec. 2. -/
theorem hasFDerivAt_cosLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt cosLoss (innerSL ℝ (cosGrad W)) W := by
  have h := hasFDerivAt_batchLoss 0 W
  have e : batchLoss 0 = cosLoss := by funext Z; simp [batchLoss, cosLoss]
  have e2 : batchGrad 0 W = cosGrad W := by simp [batchGrad, cosGrad]
  rwa [e, e2] at h

/-- The average over the two batches `s = ±1`. -/
noncomputable def avg (f : ℝ → ℝ) : ℝ := (f 1 + f (-1)) / 2

/-- `cosLoss` is the population loss of the two batches. -/
lemma avg_batchLoss (W : Matrix (Fin 2) (Fin 2) ℝ) :
    avg (fun s => batchLoss s W) = cosLoss W := by
  simp only [avg, batchLoss, cosLoss]; ring

/-- `cosGrad` is the mean of the two batch gradients. -/
lemma avg_batchGrad (W : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 / 2 : ℝ) • (batchGrad 1 W + batchGrad (-1) W) = cosGrad W := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [batchGrad, cosGrad, row]
  ring

lemma cosGrad_row (a b : ℝ) : cosGrad (row a b) = row 0 (-Real.sin b) := by
  simp [cosGrad]

lemma batchGrad_row (s a b : ℝ) : batchGrad s (row a b) = row 0 (-Real.sin b - s) := by
  simp [batchGrad]

/-- **The printed loss descent is false for fresh batches, also with the coefficient corrected**
(arXiv 2601.08882, Sec. 2, Convergence; GeoLoRA, arXiv 2410.18720, Thm 1).  With the coefficient
`1 - L λ / 2` of `loss_dlrtStep_le`, the printed inequality

  `E_ξ L(W₁) ≤ L(W) - λ (1 - L λ / 2) E_ξ‖P_{M_r} ∇L(W, ξ)‖² + L E_ξ‖W₁ - Û S̃ V̂ᵀ‖`

fails, for every `0 < λ < 2`.  Here `L = cosLoss` is the mean of the two batch losses
`batchLoss (±1)` and satisfies the assumptions with `L = 1`, the bases are built from the full
gradient or from the batch (both are `IsDLRTStep`s), and the truncation error is zero.  At the
global minimizer `W = [1 π; 0 0]` the right side is `-λ (1 - λ / 2) < 0 ≤ min L`.  The reason is
that `E‖∇L(W, ξ)‖²` contains the variance of the batch gradient, which does not help the descent;
the proof in 2410.18720 uses the same symbol for the gradient of `L` and for the batch gradient.
`expected_loss_descent` and `sameBatch_loss_descent` are the two correct versions. -/
theorem fresh_batch_descent_false {lr ϑ : ℝ} (hlr : 0 < lr) (hlr2 : lr < 2) (hϑ : 0 < ϑ) :
    ∃ (X : LRState (Fin 2) (Fin 2)) (D : ℝ → StepData (Fin 2) (Fin 2)),
      (∀ s, IsDLRTStep (cosGrad X.W) (batchGrad s) lr 1 ϑ X (D s)) ∧
      (∀ s, IsDLRTStep (batchGrad s X.W) (batchGrad s) lr 1 ϑ X (D s)) ∧
      ¬ avg (fun s => cosLoss (D s).next.W) ≤
        cosLoss X.W - lr * (1 - 1 * lr / 2) * avg (fun s => ‖X.P (batchGrad s X.W)‖ ^ 2) +
          1 * avg (fun s => ‖(D s).next.W - (D s).What 1‖) := by
  have h10 : (1 : ℝ) ≠ 0 ∨ Real.pi ≠ 0 := Or.inl one_ne_zero
  have hW : (rowState 1 Real.pi).W = row 1 Real.pi := rowState_W h10
  set D : ℝ → StepData (Fin 2) (Fin 2) := fun s => rowData 1 Real.pi (1 - lr * 0)
    (Real.pi - lr * (-Real.sin Real.pi - s)) with hD
  have hne : ∀ s : ℝ, (1 : ℝ) - lr * 0 ≠ 0 ∨ Real.pi - lr * (-Real.sin Real.pi - s) ≠ 0 := fun _ =>
    Or.inl (by simp)
  refine ⟨rowState 1 Real.pi, D, fun s => ?_, fun s => ?_, ?_⟩
  · rw [hW, cosGrad_row]
    exact rowData_isStep h10 (batchGrad_row s 1 Real.pi) (hne s) hϑ
  · rw [hW, batchGrad_row]
    exact rowData_isStep h10 (batchGrad_row s 1 Real.pi) (hne s) hϑ
  · have h0 : ∀ s, ‖(D s).next.W - (D s).What 1‖ = 0 := fun s => by
      simp only [hD, rowData_next, rowData_What_one]
      rw [rowState_W (hne s), sub_self, norm_zero]
    have hL : ∀ s, 0 ≤ cosLoss (D s).next.W := fun s => cosLoss_nonneg _
    have hLW : cosLoss (rowState 1 Real.pi).W = 0 := by
      rw [hW]; simp [cosLoss]
    have hP : ∀ s : ℝ,
        ‖(rowState 1 Real.pi).P (batchGrad s (rowState 1 Real.pi).W)‖ ^ 2 = s ^ 2 := by
      intro s
      rw [hW, batchGrad_row, rowState_P, norm_row_sq]
      simp
    intro hle
    simp only [avg, h0, hP, hLW] at hle
    have h3 := hL 1
    have h4 := hL (-1)
    nlinarith

lemma row_eq_add (a b : ℝ) : row a b = row a 0 + b • row 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

lemma row_sub_smul (x s : ℝ) : row 0 (x - s) = row 0 x - s • row 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

lemma continuous_row (a : ℝ) : Continuous fun b : ℝ => row a b := by
  have e : (fun b : ℝ => row a b) = fun b => row a 0 + b • row 0 1 :=
    funext fun b => row_eq_add a b
  rw [e]
  fun_prop

lemma hasDerivAt_row (a : ℝ) {u : ℝ → ℝ} {u' t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun t => row a (u t)) (row 0 u') t := by
  have e : (fun t => row a (u t)) = fun t => row a 0 + u t • row 0 1 :=
    funext fun t => row_eq_add a (u t)
  have h := (hu.smul_const (row 0 1 : Matrix (Fin 2) (Fin 2) ℝ)).const_add (row a 0)
  rw [e]
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

lemma neg_cosGrad_row (a b : ℝ) : -cosGrad (row a b) = row 0 (Real.sin b) := by
  rw [cosGrad_row]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

/-- A curve `[1 u(t); 0 0]` with `u' = sin u` solves the gradient flow of `cosLoss`. -/
lemma odeSolution_row {u : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (Real.sin (u t)) t) (a b : ℝ) :
    ODESolution (fun _ x => -cosGrad x) (fun t => row 1 (u t)) a b where
  cont := fun t _ => (hasDerivAt_row 1 (hu t)).continuousAt.continuousWithinAt
  deriv := fun t _ => by
    rw [neg_cosGrad_row]
    exact (hasDerivAt_row 1 (hu t)).hasDerivWithinAt

/-- Explicit Euler for `b' = sin b`, which is DLRT on `cosLoss` in the second coordinate. -/
noncomputable def eulerSeq (lr b₀ : ℝ) : ℕ → ℝ
  | 0 => b₀
  | n + 1 => eulerSeq lr b₀ n - lr * (-Real.sin (eulerSeq lr b₀ n))

lemma eulerSeq_bound {lr b₀ : ℝ} (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) (hb₀ : 0 ≤ b₀) (n : ℕ) :
    0 ≤ eulerSeq lr b₀ n ∧ eulerSeq lr b₀ n ≤ (1 + lr) ^ n * b₀ := by
  induction n with
  | zero => simpa [eulerSeq] using hb₀
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hs : |Real.sin (eulerSeq lr b₀ n)| ≤ eulerSeq lr b₀ n := by
      simpa [abs_of_nonneg h0] using Real.abs_sin_le_abs (x := eulerSeq lr b₀ n)
    have hs' := abs_le.1 hs
    constructor
    · simp only [eulerSeq]
      nlinarith
    · simp only [eulerSeq]
      rw [pow_succ']
      have h2 : lr * Real.sin (eulerSeq lr b₀ n) ≤ lr * eulerSeq lr b₀ n :=
        mul_le_mul_of_nonneg_left hs'.2 hlr
      have h3 : (1 + lr) * eulerSeq lr b₀ n ≤ (1 + lr) * ((1 + lr) ^ n * b₀) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      nlinarith

/-- The solution `2 arctan(τ eᵗ)` of `b' = sin b`. -/
noncomputable def flowB (τ t : ℝ) : ℝ := 2 * Real.arctan (τ * Real.exp t)

lemma sin_two_arctan (x : ℝ) : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have h : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : √(1 + x ^ 2) * √(1 + x ^ 2) = 1 + x ^ 2 := Real.mul_self_sqrt h.le
  have h3 : √(1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  calc 2 * (x / √(1 + x ^ 2)) * (1 / √(1 + x ^ 2)) = 2 * x / (√(1 + x ^ 2) * √(1 + x ^ 2)) := by
        field_simp
    _ = 2 * x / (1 + x ^ 2) := by rw [h2]

lemma hasDerivAt_flowB (τ t : ℝ) : HasDerivAt (flowB τ) (Real.sin (flowB τ t)) t := by
  have h1 : HasDerivAt (fun t => τ * Real.exp t) (τ * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul τ
  have h2 := h1.arctan.const_mul 2
  have e : 2 * (1 / (1 + (τ * Real.exp t) ^ 2) * (τ * Real.exp t)) =
      Real.sin (flowB τ t) := by
    rw [flowB, sin_two_arctan]
    field_simp
  rw [← e]
  exact h2

/-- **The error is not small uniformly in time** (arXiv 2601.08882, Sec. 2, Error control): for the
fixed loss `cosLoss` (nonnegative, with
gradient bounded by `1` and `1`-Lipschitz), every `0 < lr ≤ 1` and `ϑ > 0` there is a time
`t = N lr` and a DLRT trajectory without any normal component of the gradient and without
truncation, started on the gradient flow, with `‖A(t) - W_N‖ ≥ 1`. -/
theorem exists_large_error {lr ϑ : ℝ} (hlr : 0 < lr) (hlr1 : lr ≤ 1) (hϑ : 0 < ϑ) :
    ∃ (N : ℕ) (X : ℕ → LRState (Fin 2) (Fin 2)) (D : ℕ → StepData (Fin 2) (Fin 2))
      (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ n, IsDLRTStep (cosGrad (X n).W) cosGrad lr 1 ϑ (X n) (D n)) ∧
      (∀ n, X (n + 1) = (D n).next) ∧
      (∀ n, ‖(D n).next.W - (D n).What 1‖ = 0) ∧
      (∀ n, ‖cosGrad (X n).W - (X n).P (cosGrad (X n).W)‖ = 0) ∧
      ODESolution (fun _ x => -cosGrad x) A 0 (N * lr) ∧ A 0 = (X 0).W ∧
      1 ≤ ‖A (N * lr) - (X N).W‖ := by
  have hρ1 : (1 + lr) * Real.exp (-lr) < 1 := by
    have h1 := Real.add_one_lt_exp hlr.ne'
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    linarith
  have hρ0 : 0 ≤ (1 + lr) * Real.exp (-lr) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 4 by norm_num) hρ1
  set τ := Real.exp (-lr) ^ N with hτ
  have hτ0 : 0 < τ := pow_pos (Real.exp_pos _) N
  set b₀ := flowB τ 0 with hb₀
  have hb₀0 : 0 ≤ b₀ := by
    have : 0 ≤ Real.arctan (τ * Real.exp 0) := Real.arctan_nonneg.2 (by positivity)
    rw [hb₀, flowB]; linarith
  have hb₀τ : b₀ ≤ 2 * τ := by
    rw [hb₀, flowB, Real.exp_zero, mul_one]
    have := Real.arctan_le_self hτ0.le
    linarith
  set e := eulerSeq lr b₀ with he
  have hne : ∀ n, (1 : ℝ) - lr * 0 ≠ 0 ∨ e n - lr * (-Real.sin (e n)) ≠ 0 := fun _ =>
    Or.inl (by simp)
  have h1 : ∀ b : ℝ, (1 : ℝ) ≠ 0 ∨ b ≠ 0 := fun _ => Or.inl one_ne_zero
  have hnext : ∀ n, rowState 1 (e (n + 1)) =
      (rowData 1 (e n) (1 - lr * 0) (e n - lr * (-Real.sin (e n)))).next := fun n => by
    rw [rowData_next, mul_zero, sub_zero]
    rfl
  refine ⟨N, fun n => rowState 1 (e n), fun n => rowData 1 (e n) (1 - lr * 0)
    (e n - lr * (-Real.sin (e n))), fun t => row 1 (flowB τ t), fun n => ?_, hnext, fun n => ?_,
    fun n => ?_, odeSolution_row (hasDerivAt_flowB τ) _ _, ?_, ?_⟩
  · simp only [rowState_W (h1 _), cosGrad_row]
    exact rowData_isStep (h1 _) (cosGrad_row 1 (e n)) (hne n) hϑ
  · rw [rowData_next, rowData_What_one, rowState_W (hne n), sub_self, norm_zero]
  · simp only [rowState_W (h1 _), cosGrad_row, rowState_P, sub_self, norm_zero]
  · simp only [rowState_W (h1 _)]
    rfl
  · have hval : flowB τ (N * lr) = Real.pi / 2 := by
      have e1 : τ * Real.exp (N * lr) = 1 := by
        rw [hτ, ← Real.exp_nat_mul, ← Real.exp_add]
        simp
      rw [flowB, e1, Real.arctan_one]
      ring
    have hbound : e N ≤ 1 / 2 := by
      have h2 := (eulerSeq_bound hlr.le hlr1 hb₀0 N).2
      have h3 : (1 + lr) ^ N * b₀ ≤ (1 + lr) ^ N * (2 * τ) :=
        mul_le_mul_of_nonneg_left hb₀τ (by positivity)
      have h4 : (1 + lr) ^ N * (2 * τ) = 2 * ((1 + lr) * Real.exp (-lr)) ^ N := by
        rw [hτ, mul_pow]; ring
      linarith
    have hpi := Real.pi_gt_three
    simp only [rowState_W (h1 _), hval]
    rw [row_sub_row, sub_self, norm_row_zero]
    exact (by linarith : (1 : ℝ) ≤ Real.pi / 2 - e N).trans (le_abs_self _)

/-- **The constants of the error bound cannot be independent of time** (arXiv 2601.08882, Sec. 2,
Error control: "`c_{1,2,3} > 0` do not depend on time").  For the fixed loss `cosLoss`, which is
nonnegative with gradient bounded by `1` and `1`-Lipschitz, and any candidates `c₁`, `c₂`, `c₃`,
there are parameters and a DLRT trajectory started on the gradient flow, whose normal component of
the gradient is at most `ε`, such that `‖A(t) - W_N‖ > c₁ ε + c₂ lr + c₃ ϑ / lr` at `t = N lr`.

So the printed sentence is false.  The constants of `dlrt_error_le_constants` depend on `T`, and
GeoLoRA, arXiv 2410.18720, Thm 3, whose proof uses Lady Windermere's fan, only says that they depend
on `L` and `B`; constants uniform in time do hold under strong convexity,
`dlrt_error_time_uniform_constants`.  The constants here may depend on the loss and on `L` and `B`,
but not on the initial value: the initial values approach the unstable equilibrium as `t → ∞`.
For constants that may depend on the initial value too, see
`not_timeUniform_error_of_fixed_start`. -/
theorem not_timeUniform_error (c₁ c₂ c₃ : ℝ) :
    ∃ (ε lr ϑ : ℝ) (N : ℕ) (X : ℕ → LRState (Fin 2) (Fin 2)) (D : ℕ → StepData (Fin 2) (Fin 2))
      (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ), 0 < ε ∧ 0 < lr ∧ 0 < ϑ ∧
      (∀ n, IsDLRTStep (cosGrad (X n).W) cosGrad lr 1 ϑ (X n) (D n)) ∧
      (∀ n, X (n + 1) = (D n).next) ∧
      (∀ n, ‖cosGrad (X n).W - (X n).P (cosGrad (X n).W)‖ ≤ ε) ∧
      ODESolution (fun _ x => -cosGrad x) A 0 (N * lr) ∧ A 0 = (X 0).W ∧
      c₁ * ε + c₂ * lr + c₃ * ϑ / lr < ‖A (N * lr) - (X N).W‖ := by
  set M := |c₁| + |c₂| + |c₃| + 1 with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg c₁; have := abs_nonneg c₂; have := abs_nonneg c₃
    rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  set δ := 1 / (8 * M) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; linarith
  obtain ⟨N, X, D, A, hstep, hnext, -, hnorm, hA, hA0, hlarge⟩ :=
    exists_large_error hδ0 hδ1 (mul_pos hδ0 hδ0)
  refine ⟨δ, δ, δ * δ, N, X, D, A, hδ0, hδ0, mul_pos hδ0 hδ0, hstep, hnext,
    fun n => (hnorm n).le.trans hδ0.le, hA, hA0, lt_of_lt_of_le ?_ hlarge⟩
  have key : ∀ c : ℝ, |c| ≤ M → c * δ ≤ 1 / 8 := fun c hc => by
    have h1 : c * δ ≤ M * δ := mul_le_mul_of_nonneg_right ((le_abs_self c).trans hc) hδ0.le
    have h2 : M * δ = 1 / 8 := by rw [hδ]; field_simp
    linarith
  have h1 := key c₁ (by have := abs_nonneg c₂; have := abs_nonneg c₃; rw [hM]; linarith)
  have h2 := key c₂ (by have := abs_nonneg c₁; have := abs_nonneg c₃; rw [hM]; linarith)
  have h3 := key c₃ (by have := abs_nonneg c₁; have := abs_nonneg c₂; rw [hM]; linarith)
  have e : c₃ * (δ * δ) / δ = c₃ * δ := by field_simp
  rw [e]
  linarith

lemma neg_row (a b : ℝ) : -row a b = row (-a) (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [row]

lemma norm_row_left (c : ℝ) : ‖row c 0‖ = |c| := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_row_sq, zero_pow two_ne_zero, add_zero,
    Real.sqrt_sq_eq_abs]

/-- **Time-independence fails for a fixed initial value too** (arXiv 2601.08882, Sec. 2, Error
control).  For `L(W) = -‖W‖² / 2`, whose gradient `-W` is `1`-Lipschitz, the fixed initial value
`W₀ = [1 0; 0 0]` and every fixed `lr > 0`, `ϑ > 0`, the error of a DLRT trajectory without normal
component and without truncation is unbounded in time: it exceeds every `C`.  So there are no
constants `c₁, c₂, c₃` independent of time, even if they may depend on the loss, on the initial
value and on `lr`.  This loss is not bounded below and its gradient is not bounded, neither of
which the sentence in the paper excludes; `not_timeUniform_error` is the version with these
properties, with constants uniform in the initial value. -/
theorem not_timeUniform_error_of_fixed_start {lr ϑ : ℝ} (hlr : 0 < lr) (hϑ : 0 < ϑ) :
    ∃ (X : ℕ → LRState (Fin 2) (Fin 2)) (D : ℕ → StepData (Fin 2) (Fin 2))
      (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ n, IsDLRTStep (-(X n).W) (fun W => -W) lr 1 ϑ (X n) (D n)) ∧
      (∀ n, X (n + 1) = (D n).next) ∧
      (∀ n, ‖(-(X n).W) - (X n).P (-(X n).W)‖ = 0) ∧
      (∀ a b, ODESolution (fun _ x => -(-x)) A a b) ∧ A 0 = (X 0).W ∧
      ∀ C : ℝ, ∃ N : ℕ, C < ‖A (N * lr) - (X N).W‖ := by
  set e : ℕ → ℝ := fun n => (1 + lr) ^ n with he
  have hepos : ∀ n, 0 < e n := fun n => pow_pos (by linarith) n
  have hne : ∀ n, e n ≠ 0 ∨ (0 : ℝ) ≠ 0 := fun n => Or.inl (hepos n).ne'
  have hne' : ∀ n, e n - lr * (-e n) ≠ 0 ∨ (0 : ℝ) - lr * 0 ≠ 0 := fun n => Or.inl (by
    have : e n - lr * (-e n) = (1 + lr) * e n := by ring
    rw [this]
    exact (mul_pos (by linarith) (hepos n)).ne')
  have hstep : ∀ n, e (n + 1) = e n - lr * (-e n) := fun n => by
    simp only [he, pow_succ]
    ring
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.exp t • row 1 0)
      (Real.exp t • (row 1 0 : Matrix (Fin 2) (Fin 2) ℝ)) t := fun t =>
    (Real.hasDerivAt_exp t).smul_const _
  have hW : ∀ n, (rowState (e n) 0).W = row (e n) 0 := fun n => rowState_W (hne n)
  have hneg : ∀ a : ℝ, -row a 0 = row (-a) 0 := fun a => by rw [neg_row, neg_zero]
  refine ⟨fun n => rowState (e n) 0, fun n => rowData (e n) 0 (e n - lr * (-e n)) (0 - lr * 0),
    fun t => Real.exp t • row 1 0, fun n => ?_, fun n => ?_, fun n => ?_, fun a b => ?_, ?_,
    fun C => ?_⟩
  · simp only [hW, hneg]
    exact rowData_isStep (hne n) (hneg (e n)) (hne' n) hϑ
  · change rowState (e (n + 1)) 0 = (rowData (e n) 0 (e n - lr * (-e n)) (0 - lr * 0)).next
    rw [rowData_next, hstep n, mul_zero, sub_zero]
  · simp only [hW, hneg, rowState_P, sub_self, norm_zero]
  · exact
      { cont := fun t _ => (hd t).continuousAt.continuousWithinAt
        deriv := fun t _ => by
          simpa using (hd t).hasDerivWithinAt }
  · simp only [hW]
    simp [he]
  · set ρ := (1 + lr) * Real.exp (-lr) with hρ
    have hρ1 : ρ < 1 := by
      have h1 := Real.add_one_lt_exp hlr.ne'
      rw [hρ, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
      linarith
    have hρ0 : 0 ≤ ρ := by positivity
    have hδ : 0 < (1 - ρ) * lr := mul_pos (sub_pos.2 hρ1) hlr
    obtain ⟨N, hN⟩ := exists_nat_gt (|C| / ((1 - ρ) * lr))
    have hN0 : 0 < N := by
      have h1 : 0 ≤ |C| / ((1 - ρ) * lr) := by positivity
      have h2 : (0 : ℝ) < N := lt_of_le_of_lt h1 hN
      exact_mod_cast h2
    have hNC : |C| < N * ((1 - ρ) * lr) := (div_lt_iff₀ hδ).1 hN
    refine ⟨N, ?_⟩
    have hE : (Real.exp (N * lr) • row 1 0 : Matrix (Fin 2) (Fin 2) ℝ) =
        row (Real.exp (N * lr)) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [row]
    have hpow : e N = ρ ^ N * Real.exp (N * lr) := by
      have h1 : Real.exp (-lr) ^ N * Real.exp (N * lr) = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        simp
      simp only [he, hρ, mul_pow]
      rw [mul_assoc, h1, mul_one]
    have hρN : ρ ^ N ≤ ρ := pow_le_of_le_one hρ0 hρ1.le hN0.ne'
    have hexp : (N : ℝ) * lr + 1 ≤ Real.exp (N * lr) := Real.add_one_le_exp _
    have hdiff : Real.exp (N * lr) * (1 - ρ) ≤ Real.exp (N * lr) - e N := by
      rw [hpow]
      nlinarith [Real.exp_pos ((N : ℝ) * lr)]
    have hgt : C < Real.exp (N * lr) - e N := by
      have h1 : ((N : ℝ) * lr + 1) * (1 - ρ) ≤ Real.exp (N * lr) * (1 - ρ) :=
        mul_le_mul_of_nonneg_right hexp (sub_pos.2 hρ1).le
      have h2 := le_abs_self C
      have h3 : 0 < 1 - ρ := sub_pos.2 hρ1
      nlinarith
    simp only [hW]
    rw [hE, row_sub_row, sub_self, norm_row_left]
    exact hgt.trans_le (le_abs_self _)

/-! #### A run with genuine mini-batch noise -/

/-- A fair coin on the two batches. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • Measure.dirac true + (2⁻¹ : ENNReal) • Measure.dirac false

instance : IsProbabilityMeasure coin :=
  ⟨by simp [coin, ENNReal.inv_two_add_inv_two]⟩

/-- The batch sign: `true ↦ 1`, `false ↦ -1`. -/
def sg (ξ : Bool) : ℝ := if ξ then 1 else -1

lemma sg_sq (ξ : Bool) : sg ξ ^ 2 = 1 := by
  cases ξ <;> simp [sg]

lemma abs_sg (ξ : Bool) : |sg ξ| = 1 := by
  cases ξ <;> simp [sg]

lemma measurable_sg : Measurable sg := Measurable.of_discrete

/-- The probability space of i.i.d. fair batches. -/
noncomputable def coinμ : Measure (ℕ → Bool) := Measure.infinitePi fun _ => coin

instance : IsProbabilityMeasure coinμ := by
  unfold coinμ; infer_instance

/-- The batch sign drawn at index `t`.  Step `t` of the algorithm uses index `t + 1`, so that
it is independent of `σ(coinS 0, …, coinS t)`. -/
def coinS (t : ℕ) (ω : ℕ → Bool) : ℝ := sg (ω t)

lemma stronglyMeasurable_coinS (t : ℕ) : StronglyMeasurable (coinS t) :=
  (measurable_sg.comp (measurable_pi_apply t)).stronglyMeasurable

lemma iIndepFun_coinS : ProbabilityTheory.iIndepFun coinS coinμ :=
  ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => sg) fun _ => measurable_sg

lemma integral_coinS (t : ℕ) : ∫ ω, coinS t ω ∂coinμ = 0 := by
  have hmap : coinμ.map (fun ω => ω t) = coin := Measure.infinitePi_map_eval _ t
  have h1 : ∫ ω, coinS t ω ∂coinμ = ∫ ξ, sg ξ ∂(coinμ.map fun ω => ω t) := by
    rw [integral_map (measurable_pi_apply t).aemeasurable
      measurable_sg.stronglyMeasurable.aestronglyMeasurable]
    rfl
  have hi : ∀ b, Integrable sg ((2⁻¹ : ENNReal) • Measure.dirac b) := fun b =>
    (Integrable.of_finite (f := sg) (μ := Measure.dirac b)).smul_measure (by simp)
  rw [h1, hmap, coin, integral_add_measure (hi _) (hi _), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp [sg]

/-- The information before step `t`: the batches with index `≤ t`. -/
noncomputable def coinF : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
  Filtration.natural coinS stronglyMeasurable_coinS

lemma coinS_condExp (t : ℕ) : coinμ[coinS (t + 1) | coinF t] =ᵐ[coinμ] 0 := by
  have h := iIndepFun_coinS.condExp_natural_ae_eq_of_lt stronglyMeasurable_coinS
    (Nat.lt_succ_self t)
  refine h.trans (ae_of_all _ fun ω => ?_)
  simpa using integral_coinS (t + 1)

lemma coinS_adapted (t : ℕ) : StronglyMeasurable[coinF t] (coinS t) :=
  Filtration.stronglyAdapted_natural stronglyMeasurable_coinS t

/-- The second coordinate of the DLRT iterates on `cosLoss` with the batches `coinS (t + 1)`. -/
noncomputable def coinB (lr : ℕ → ℝ) : ℕ → (ℕ → Bool) → ℝ
  | 0, _ => 0
  | t + 1, ω => coinB lr t ω - lr t * (-Real.sin (coinB lr t ω) - coinS (t + 1) ω)

/-- The DLRT states of the run with i.i.d. batches. -/
noncomputable def coinX (lr : ℕ → ℝ) (t : ℕ) (ω : ℕ → Bool) : LRState (Fin 2) (Fin 2) :=
  rowState 1 (coinB lr t ω)

/-- The batch gradient at step `t`. -/
noncomputable def coinG (lr : ℕ → ℝ) (t : ℕ) (ω : ℕ → Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  batchGrad (coinS (t + 1) ω) (coinX lr t ω).W

/-- The internal data of the steps of the run. -/
noncomputable def coinD (lr : ℕ → ℝ) (t : ℕ) (ω : ℕ → Bool) : StepData (Fin 2) (Fin 2) :=
  rowData 1 (coinB lr t ω) (1 - lr t * 0)
    (coinB lr t ω - lr t * (-Real.sin (coinB lr t ω) - coinS (t + 1) ω))

lemma coinX_W (lr : ℕ → ℝ) (t : ℕ) (ω : ℕ → Bool) :
    (coinX lr t ω).W = row 1 (coinB lr t ω) :=
  rowState_W (Or.inl one_ne_zero)

lemma coinG_eq (lr : ℕ → ℝ) (t : ℕ) (ω : ℕ → Bool) :
    coinG lr t ω = row 0 (-Real.sin (coinB lr t ω) - coinS (t + 1) ω) := by
  rw [coinG, coinX_W, batchGrad_row]

lemma coinB_adapted (lr : ℕ → ℝ) (t : ℕ) : StronglyMeasurable[coinF t] (coinB lr t) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    have hb : StronglyMeasurable[coinF (t + 1)] (coinB lr t) :=
      ih.mono (coinF.mono (Nat.le_succ t))
    have hsin : StronglyMeasurable[coinF (t + 1)] fun ω => Real.sin (coinB lr t ω) :=
      Real.continuous_sin.comp_stronglyMeasurable hb
    exact hb.sub (((hsin.neg).sub (coinS_adapted (t + 1))).const_mul (lr t))

/-- **Non-vacuity of `IsStochasticDLRT` with genuine noise** (arXiv 2601.08882, Sec. 2,
Convergence). With i.i.d. fair batches the run on `cosLoss` is a stochastic DLRT in the sense of
`IsStochasticDLRT`, with `σ = 1`.  No singular value is discarded, the iterates stay in `M₁`. -/
theorem coin_isStochastic (lr : ℕ → ℝ) :
    IsStochasticDLRT coinF coinμ cosGrad (coinG lr) lr (fun _ _ => 1) 1 (coinX lr) (coinD lr) := by
  have h1 : ∀ b : ℝ, (1 : ℝ) ≠ 0 ∨ b ≠ 0 := fun _ => Or.inl one_ne_zero
  have hW : ∀ t, StronglyMeasurable[coinF t] fun ω => (coinX lr t ω).W := fun t => by
    simp only [coinX_W]
    exact (continuous_row 1).comp_stronglyMeasurable (coinB_adapted lr t)
  have hgrad : ∀ t, StronglyMeasurable[coinF t] fun ω => row 0 (-Real.sin (coinB lr t ω)) :=
    fun t => (continuous_row 0).comp_stronglyMeasurable
      (Real.continuous_sin.comp_stronglyMeasurable (coinB_adapted lr t)).neg
  have hcg : ∀ t ω, cosGrad (coinX lr t ω).W = row 0 (-Real.sin (coinB lr t ω)) := fun t ω => by
    rw [coinX_W, cosGrad_row]
  have hdiff : ∀ t ω, coinG lr t ω - cosGrad (coinX lr t ω).W = row 0 (-coinS (t + 1) ω) :=
    fun t ω => by
      rw [coinG_eq, hcg, row_sub_row]
      congr 1 <;> ring
  have hvar : ∀ t ω, ‖coinG lr t ω - cosGrad (coinX lr t ω).W‖ ^ 2 = 1 := fun t ω => by
    rw [hdiff, norm_row_sq, coinS]
    simp [sg_sq]
  refine
    { step := fun t ω => ?_
      next := fun t ω => ?_
      adaptedW := hW
      adaptedGal := fun t => ?_
      adaptedG := fun t => ?_
      unbiased := fun t => ?_
      intVar := fun t => ?_
      var := fun t => ?_
      intϑ := fun _ => integrable_const _
      measP := fun t => ?_ }
  · rw [hcg]
    exact rowData_isStep (h1 _) (coinG_eq lr t ω) (Or.inl (by simp)) one_pos
  · rw [coinD, rowData_next, mul_zero, sub_zero]
    rfl
  · have key : StronglyMeasurable[coinF t] fun _ : ℕ → Bool =>
        (leftProj e₀ * rightProj (1 : Matrix (Fin 2) (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := stronglyMeasurable_const
    exact key
  · have hs : StronglyMeasurable[coinF (t + 1)] fun ω => coinG lr t ω := by
      simp only [coinG_eq]
      refine (continuous_row 0).comp_stronglyMeasurable ?_
      have hb : StronglyMeasurable[coinF (t + 1)] (coinB lr t) :=
        (coinB_adapted lr t).mono (coinF.mono (Nat.le_succ t))
      exact (Real.continuous_sin.comp_stronglyMeasurable hb).neg.sub (coinS_adapted (t + 1))
    exact hs
  · set c : Matrix (Fin 2) (Fin 2) ℝ := row 0 1 with hc
    set A : (ℕ → Bool) → Matrix (Fin 2) (Fin 2) ℝ := fun ω => row 0 (-Real.sin (coinB lr t ω))
      with hA
    set B : (ℕ → Bool) → Matrix (Fin 2) (Fin 2) ℝ := fun ω =>
      ContinuousLinearMap.lsmul ℝ ℝ (coinS (t + 1) ω) c with hB
    have hAint : Integrable A coinμ := by
      refine Integrable.of_bound ((hgrad t).mono (coinF.le t)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [hA]
      simp only [norm_row_zero, abs_neg]
      exact Real.abs_sin_le_one _
    have hsint : Integrable (coinS (t + 1)) coinμ := by
      refine Integrable.of_bound (stronglyMeasurable_coinS _).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      simp [coinS, abs_sg]
    have hBint : Integrable B coinμ := hsint.smul_const c
    have hG : coinG lr t = A - B := by
      funext ω
      rw [coinG_eq, row_sub_smul]
      rfl
    have h1 := condExp_sub hAint hBint (coinF t)
    have h2 : coinμ[A | coinF t] = A :=
      condExp_of_stronglyMeasurable (coinF.le t) (hgrad t) hAint
    have h3 := condExp_bilin_of_stronglyMeasurable_right (μ := coinμ) (m := coinF t)
      (ContinuousLinearMap.lsmul ℝ ℝ) (f := coinS (t + 1)) (g := fun _ => c)
      stronglyMeasurable_const hBint hsint
    rw [hG]
    filter_upwards [h1, h3, coinS_condExp t] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, h2]
    change A ω - (coinμ[B | coinF t]) ω = _
    rw [e2, e3, hcg]
    simp [hA]
  · simp only [hvar]
    exact integrable_const _
  · simp [hvar]
  · have e : (fun ω => (coinX lr t ω).P (cosGrad (coinX lr t ω).W)) =
        fun ω => row 0 (-Real.sin (coinB lr t ω)) := funext fun ω => by
      rw [hcg, coinX, rowState_P]
    rw [e]
    exact ((hgrad t).mono (coinF.le t)).aestronglyMeasurable


/-- The quantity printed in arXiv 2601.08882, Sec. 2, Convergence, is the true stationarity measure
plus the noise: in the run with i.i.d. batches,
`E‖P_{M_r} ∇L(W_t, ξ_t)‖² = E‖P_{M_r} ∇L(W_t)‖² + 1`, for all learning rates. -/
theorem coin_printed_eq (lr : ℕ → ℝ) (t : ℕ) :
    ∫ ω, ‖(coinX lr t ω).P (coinG lr t ω)‖ ^ 2 ∂coinμ =
      ∫ ω, ‖(coinX lr t ω).P (cosGrad (coinX lr t ω).W)‖ ^ 2 ∂coinμ + 1 := by
  set u : (ℕ → Bool) → ℝ := fun ω => Real.sin (coinB lr t ω) with hu
  have hP1 : ∀ ω, ‖(coinX lr t ω).P (coinG lr t ω)‖ ^ 2 =
      u ω ^ 2 + 2 * (u * coinS (t + 1)) ω + 1 := fun ω => by
    rw [coinG_eq, coinX, rowState_P, norm_row_sq]
    have h := sg_sq (ω (t + 1))
    simp only [Pi.mul_apply, hu, coinS]
    linear_combination h
  have hP2 : ∀ ω, ‖(coinX lr t ω).P (cosGrad (coinX lr t ω).W)‖ ^ 2 = u ω ^ 2 := fun ω => by
    rw [coinX_W, cosGrad_row, coinX, rowState_P, norm_row_sq]
    simp [hu]
  have hum : StronglyMeasurable[coinF t] u :=
    Real.continuous_sin.comp_stronglyMeasurable (coinB_adapted lr t)
  have hum' : StronglyMeasurable u := hum.mono (coinF.le t)
  have hsm : StronglyMeasurable (coinS (t + 1)) := stronglyMeasurable_coinS _
  have hsint : Integrable (coinS (t + 1)) coinμ := by
    refine Integrable.of_bound hsm.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    simp [coinS, abs_sg]
  have husint : Integrable (u * coinS (t + 1)) coinμ := by
    refine Integrable.of_bound (hum'.mul hsm).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, coinS, abs_sg, mul_one]
    exact Real.abs_sin_le_one _
  have hu2int : Integrable (fun ω => u ω ^ 2) coinμ := by
    refine Integrable.of_bound (hum'.pow 2).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := Real.sin_sq_le_one (coinB lr t ω)
    simpa [hu] using this
  have hzero : ∫ ω, (u * coinS (t + 1)) ω ∂coinμ = 0 := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := coinμ) (m := coinF t) hum husint
      hsint
    calc ∫ ω, (u * coinS (t + 1)) ω ∂coinμ =
          ∫ ω, (coinμ[u * coinS (t + 1) | coinF t]) ω ∂coinμ := by
          rw [integral_condExp (coinF.le t)]
      _ = ∫ _, (0 : ℝ) ∂coinμ := integral_congr_ae (by
          filter_upwards [hpull, coinS_condExp t] with ω e1 e2
          rw [e1, Pi.mul_apply, e2]
          simp)
      _ = 0 := by simp
  simp only [hP1, hP2]
  have h3 : Integrable (fun ω => u ω ^ 2 + 2 * (u * coinS (t + 1)) ω) coinμ :=
    hu2int.add (husint.const_mul 2)
  rw [integral_add h3 (integrable_const 1), integral_add hu2int (husint.const_mul 2),
    integral_const_mul, hzero]
  simp

/-- **The printed stationarity is false** (arXiv 2601.08882, Sec. 2, Convergence, which prints
`liminf E‖P_{M_r} ∇L(W_t, ξ_t)‖² = 0` with the batch `ξ_t` inside the norm).  In the run with i.i.d.
fair batches on `cosLoss`, for all Robbins–Monro learning rates with `lr_t ≤ 2`,

  `liminf E‖P_{M_r} ∇L(W_t)‖² = 0`, but `liminf E‖P_{M_r} ∇L(W_t, ξ_t)‖² = 1`.

The first statement is `IsStochasticDLRT.liminf_expected_tangentGrad_sq`, so the corrected theorem
applies to this very run.  By `coin_printed_eq` the second quantity is the first plus the tangential
noise variance `1`, which does not vanish.  All other hypotheses of the paper hold: there is no
truncation error, and the loss is nonnegative with `1`-Lipschitz gradient bounded by `1`.  GeoLoRA,
arXiv 2410.18720, Thm 2, writes `f(W_t)`, which its appendix declares to be shorthand for
`f(W_t, ξ_t)`; read as the population gradient, it is the first statement. -/
theorem not_stationarity_of_batch_gradient {lr : ℕ → ℝ} (hlr : ∀ t, 0 ≤ lr t)
    (hlr2 : ∀ t, lr t ≤ 2) (hdiv : ¬ Summable lr) (hsq : Summable fun t => lr t ^ 2) :
    liminf (fun t => ∫ ω, ‖(coinX lr t ω).P (cosGrad (coinX lr t ω).W)‖ ^ 2 ∂coinμ) atTop = 0 ∧
      liminf (fun t => ∫ ω, ‖(coinX lr t ω).P (coinG lr t ω)‖ ^ 2 ∂coinμ) atTop = 1 := by
  have hS := coin_isStochastic lr
  have hL : Integrable (fun ω => cosLoss (coinX lr 0 ω).W) coinμ := by
    have e : (fun ω => cosLoss (coinX lr 0 ω).W) = fun _ => cosLoss (row 1 0) := by
      funext ω
      rw [coinX_W]
      rfl
    rw [e]
    exact integrable_const _
  have hzero : ∀ t ω, ‖(coinD lr t ω).next.W - (coinD lr t ω).What 1‖ = 0 := fun t ω => by
    rw [coinD, rowData_next, rowData_What_one, rowState_W (Or.inl (by simp)), sub_self, norm_zero]
  have hC : ∀ N, ∑ t ∈ range N, ∫ ω, ‖(coinD lr t ω).next.W - (coinD lr t ω).What 1‖ ∂coinμ ≤ 0 :=
    fun N => by simp [hzero]
  have hex := fun (ε : ℝ) (hε : 0 < ε) (N : ℕ) =>
    hS.exists_expected_tangentGrad_sq_lt (ℒ := cosLoss) (β := 1) (G := 1) (ℒinf := 0)
      hasFDerivAt_cosLoss cosGrad_lipschitz zero_le_one norm_cosGrad_le hL hlr
      (fun t => by simpa using hlr2 t) hdiv hsq (fun _ _ => cosLoss_nonneg _) hC hε N
  refine ⟨hS.liminf_expected_tangentGrad_sq (ℒ := cosLoss) (β := 1) (G := 1) (ℒinf := 0)
    hasFDerivAt_cosLoss cosGrad_lipschitz zero_le_one norm_cosGrad_le hL hlr
    (fun t => by simpa using hlr2 t) hdiv hsq (fun _ _ => cosLoss_nonneg _) hC, ?_⟩
  refine liminf_eq_of_forall_exists_lt (fun t => ?_) fun ε hε N => ?_
  · rw [coin_printed_eq]
    have : 0 ≤ ∫ ω, ‖(coinX lr t ω).P (cosGrad (coinX lr t ω).W)‖ ^ 2 ∂coinμ :=
      integral_nonneg fun ω => sq_nonneg _
    linarith
  · obtain ⟨t, ht, hlt⟩ := hex ε hε N
    refine ⟨t, ht, ?_⟩
    rw [coin_printed_eq]
    linarith

/-- For every choice of learning rates, the stationarity measure printed in arXiv 2601.08882, Sec.
2, Convergence, stays at least `1` along the run with i.i.d. batches. -/
theorem one_le_printed_stationarity (lr : ℕ → ℝ) (t : ℕ) :
    1 ≤ ∫ ω, ‖(coinX lr t ω).P (coinG lr t ω)‖ ^ 2 ∂coinμ := by
  rw [coin_printed_eq]
  have : 0 ≤ ∫ ω, ‖(coinX lr t ω).P (cosGrad (coinX lr t ω).W)‖ ^ 2 ∂coinμ :=
    integral_nonneg fun ω => sq_nonneg _
  linarith

/-- The hypotheses on the learning rates of `not_stationarity_of_batch_gradient` (arXiv 2601.08882,
Sec. 2, Convergence) can be met: `lr_t = 1 / (t + 1)`. -/
theorem exists_robbinsMonro : ∃ lr : ℕ → ℝ, (∀ t, 0 ≤ lr t) ∧ (∀ t, lr t ≤ 2) ∧ ¬ Summable lr ∧
    Summable fun t => lr t ^ 2 := by
  refine ⟨fun t => 1 / ((t : ℝ) + 1), fun t => by positivity, fun t => ?_, ?_, ?_⟩
  · have h : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have h2 : 1 / ((t : ℝ) + 1) ≤ 1 := (div_le_one (by linarith)).2 h
    linarith
  · intro hs
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 (by
      simpa using hs)
    exact Real.not_summable_one_div_natCast h
  · have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.2 one_lt_two)
    refine h.congr fun t => ?_
    simp [one_div]

/-- **Non-vacuity of `dlrt_error_time_uniform`** (arXiv 2601.08882, Sec. 2, Error control): for
`L(W) = ‖W‖² / 2`, which has `∇L = id`, with `β = μ = 1`, and `0 < lr < 1`, all hypotheses hold
along the DLRT iterates, with `ε = 0`, `B = 1`, and the gradient flow `A(t) = e^{-t} W₀`. -/
theorem timeUniform_instance {lr ϑ : ℝ} (hlr : 0 < lr) (hlr1 : lr < 1) (hϑ : 0 < ϑ) (N : ℕ) :
    ∃ (X : ℕ → LRState (Fin 2) (Fin 2)) (D : ℕ → StepData (Fin 2) (Fin 2))
      (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ n < N, IsDLRTStep (id (X n).W) id lr 1 ϑ (X n) (D n)) ∧
      (∀ n < N, X (n + 1) = (D n).next) ∧
      (∀ n < N, ∀ i < 1, ‖id ((D n).What i)‖ ≤ 1) ∧
      (∀ n < N, ‖id (X n).W - (X n).P (id (X n).W)‖ ≤ 0) ∧
      ODESolution (fun _ x => -id x) A 0 (N * (((1 : ℕ) : ℝ) * lr)) ∧ A 0 = (X 0).W := by
  have h0 : 0 < 1 - lr := sub_pos.2 hlr1
  set e : ℕ → ℝ := fun n => (1 - lr) ^ n with he
  have hepos : ∀ n, 0 < e n := fun n => pow_pos h0 n
  have hele : ∀ n, e n ≤ 1 := fun n => pow_le_one₀ h0.le (by linarith)
  have hne : ∀ n, e n ≠ 0 ∨ (0 : ℝ) ≠ 0 := fun n => Or.inl (hepos n).ne'
  have hne' : ∀ n, e n - lr * e n ≠ 0 ∨ (0 : ℝ) - lr * 0 ≠ 0 := fun n => Or.inl (by
    have : e n - lr * e n = (1 - lr) * e n := by ring
    rw [this]
    exact (mul_pos h0 (hepos n)).ne')
  have hstep : ∀ n, e (n + 1) = e n - lr * e n := fun n => by
    simp only [he, pow_succ]
    ring
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-t) • row 1 0)
      (-(Real.exp (-t) • (row 1 0 : Matrix (Fin 2) (Fin 2) ℝ))) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    simpa using h1.smul_const (row 1 0 : Matrix (Fin 2) (Fin 2) ℝ)
  refine ⟨fun n => rowState (e n) 0, fun n => rowData (e n) 0 (e n - lr * e n) (0 - lr * 0),
    fun t => Real.exp (-t) • row 1 0, fun n _ => ?_, fun n _ => ?_, fun n _ i hi => ?_,
    fun n _ => ?_, ?_, ?_⟩
  · rw [id, rowState_W (hne n)]
    exact rowData_isStep (hne n) rfl (hne' n) hϑ
  · change rowState (e (n + 1)) 0 = (rowData (e n) 0 (e n - lr * e n) (0 - lr * 0)).next
    rw [rowData_next, hstep n, mul_zero, sub_zero]
  · obtain rfl : i = 0 := by omega
    rw [id, rowData_What_zero]
    have h1 := norm_row_sq (e n) 0
    have h2 : (e n) ^ 2 ≤ 1 := pow_le_one₀ (hepos n).le (hele n)
    have h3 : ‖row (e n) 0‖ ^ 2 ≤ 1 := by rw [h1]; simpa using h2
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  · simp only [id, rowState_W (hne n), rowState_P, sub_self, norm_zero, le_refl]
  · exact
      { cont := fun t _ => (hd t).continuousAt.continuousWithinAt
        deriv := fun t _ => (hd t).hasDerivWithinAt }
  · rw [rowState_W (hne 0)]
    simp [he]

end Examples

end LeanDLRA.Literature.P2601_08882
