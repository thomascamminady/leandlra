import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Localization
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.KStep
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Literature.Training.P2209_13569a
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2205.13571: Low-rank lottery tickets (DLRT)

Schotthöfer, Zangrando, Kusch, Ceruti, Tudisco, *Low-rank lottery tickets: finding efficient
low-rank neural networks via matrix differential equations*.  This module formalizes dynamical
low-rank training for real weight matrices with the Frobenius norm and a differentiable loss `ℒ`.
The chain rule of Sec. 4.2 (`hasGradientAt_kLoss`, `hasGradientAt_lLoss`, `hasGradientAt_sLoss`,
`kFlow_eq`, `lFlow_eq`, `sFlow_eq`) turns the factor gradient flows of eqs. (7), (8) and Algorithm 1
(`IsDLRTStep`, `IsAdaptiveDLRTStep`) into the BUG and rank-adaptive BUG steps for `F = -∇ℒ`
(`IsDLRTStep.isStep`, `IsAdaptiveDLRTStep.isRankAdaptiveStep`).  Rank adaptation is the actual
algorithm: bases augmented by `U₀`, `V₀`, so that the S-step starts at `Y₀`
(`IsAdaptiveDLRTStep.start_eq`), an SVD of the core, the smallest rank with discarded singular
values `≤ ϑ`, and truncated factors, whose error is exactly that tail
(`IsAdaptiveDLRTStep.norm_sub_eq`) and which is optimal
(`IsAdaptiveDLRTStep.norm_sub_le_of_rank_le`); such steps exist (`exists_isAdaptiveDLRTStep`).
Under the assumptions `IsP1`, `IsP2` this gives the appendix lemmas with the paper's constant
(`dlrt_lemma_1`, `dlrt_lemma_2`, `dlrt_lemma_3`), **Theorem 1** (`dlrt_approximation`,
`dlrt_approximation_fixedRank`) and **Theorem 2** (`dlrt_sStep_dissipation`, `dlrt_descent`,
`dlrt_descent_of_P1`, `dlrt_descent_explicit`, and for all layers `dlrt_descent_sweep`).

Two claims of the main-text theorems (p. 5) are false as printed, and this is proved.  In
Theorem 1 the constants cannot depend only on `C₁`, `C₂`, they must grow with the final time
(`dlrt_constants_depend_on_time`).  In Theorem 2 no positive `α` independent of `t`, `η`, `ϑ`
exists (`dlrt_no_uniform_descent`, `dlrt_no_uniform_descent_of_bddBelow`); the paper's proof gives
the step-dependent `α²` of `dlrt_descent`.  A scope remark: the main-text Theorem 2 refers to
Algorithm 1 without excluding `adaptive = False`, but the appendix proves it only for the
rank-adaptive algorithm, and the proof needs the augmentation.  For `adaptive = False` even the
step-dependent form fails: one exact step from a start that scales with `η` raises the loss by
`3 η`, for every `η > 0` (`fixedRank_loss_increases`).

Differences from the paper.  The substeps are integrated exactly, as in Theorem 1.  Theorem 1 and
the appendix treat one layer with the others frozen, as the paper does; `dlrt_descent_sweep` updates
the layers one after the other.  The network (forward pass, activations) enters only through `ℒ`,
and the bias update is not modelled.  P1 is global, as displayed in the appendix.  P2 is required
on a ball of explicit radius, and it is extended to rank-deficient iterates (`IsP2.normal_le`).
Orthonormal bases are required to span the K- and L-factors (and `U₀`, `V₀`), not to equal the
range, which allows the padded bases of a QR factorization.  Sec. 3.1 is not repeated: the Galerkin
condition is `IsOrthProj.diracFrenkel_tfae`, and the factor system (6) is
`hasDerivAt_factorProduct_iff_factorODE` and `factorODE_solution_isDLRA` of `Matrix/GaugeODE.lean`.
The experiments and the cost estimates of Sec. 4.3 are not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius Gradient

namespace LeanDLRA.Literature.P2205_13571

open LeanDLRA.MatrixBUG LeanDLRA.Literature.P2209_13569

/-! ### Factor gradients -/

section FactorGradients

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']

/-- Chain rule for a gradient along a continuous linear map: if `⟪G, Φ v⟫ = ⟪G', v⟫` for all `v`
and `G = ∇ℒ(Φ x)`, then `G' = ∇(ℒ ∘ Φ)(x)`. -/
private lemma hasGradientAt_comp_clm {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
    {ℒ : E' → ℝ} (Φ : E →L[ℝ] E') {x : E} {G : E'} {G' : E} (hadj : ∀ v, ⟪G, Φ v⟫ = ⟪G', v⟫)
    (h : HasGradientAt ℒ G (Φ x)) : HasGradientAt (fun y => ℒ (Φ y)) G' x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have hEq : InnerProductSpace.toDual ℝ E G' = (InnerProductSpace.toDual ℝ E' G).comp Φ := by
    ext v
    simpa using (hadj v).symm
  rw [hEq]
  exact h.comp x Φ.hasFDerivAt

/-- **The K-step chain rule** (arXiv 2205.13571, Sec. 4.2): `∇_K ℒ(K Vᵀ) = ∇ℒ(K Vᵀ) V`. -/
theorem hasGradientAt_kLoss {ℒ : Matrix m n ℝ → ℝ} (V : Matrix n k ℝ) {K : Matrix m k ℝ}
    {G : Matrix m n ℝ} (h : HasGradientAt ℒ G (K * Vᵀ)) :
    HasGradientAt (fun K' => ℒ (K' * Vᵀ)) (G * V) K := by
  refine hasGradientAt_comp_clm (Frobenius.rightMulCLM Vᵀ) (fun v => ?_) h
  simp only [Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_right', Matrix.transpose_transpose]

/-- **The L-step chain rule** (arXiv 2205.13571, Sec. 4.2): `∇_L ℒ(U Lᵀ) = ∇ℒ(U Lᵀ)ᵀ U`. -/
theorem hasGradientAt_lLoss {ℒ : Matrix m n ℝ → ℝ} (U : Matrix m k ℝ) {Lf : Matrix n k ℝ}
    {G : Matrix m n ℝ} (h : HasGradientAt ℒ G (U * Lfᵀ)) :
    HasGradientAt (fun L' => ℒ (U * L'ᵀ)) (Gᵀ * U) Lf := by
  refine hasGradientAt_comp_clm
    ((Frobenius.leftMulCLM U).comp Frobenius.transposeCLM) (fun v => ?_) h
  simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
    Frobenius.transposeCLM_apply]
  rw [Frobenius.inner_mul_left', ← Frobenius.inner_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose]

/-- **The S-step chain rule** (arXiv 2205.13571, Sec. 4.2): `∇_S ℒ(U S Vᵀ) = Uᵀ ∇ℒ(U S Vᵀ) V`. -/
theorem hasGradientAt_sLoss {ℒ : Matrix m n ℝ → ℝ} (U : Matrix m k ℝ) (V : Matrix n k' ℝ)
    {S : Matrix k k' ℝ} {G : Matrix m n ℝ} (h : HasGradientAt ℒ G (U * S * Vᵀ)) :
    HasGradientAt (fun S' => ℒ (U * S' * Vᵀ)) (Uᵀ * G * V) S := by
  refine hasGradientAt_comp_clm
    ((Frobenius.rightMulCLM Vᵀ).comp (Frobenius.leftMulCLM U)) (fun v => ?_) h
  simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
    Frobenius.rightMulCLM_apply]
  rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, Frobenius.inner_mul_left',
    Matrix.mul_assoc]

/-- The full gradient flow `F(Z) = -∇ℒ(Z)` of eq. (2) of arXiv 2205.13571, an autonomous field. -/
noncomputable def gradField (ℒ : Matrix m n ℝ → ℝ) : ℝ → Matrix m n ℝ → Matrix m n ℝ :=
  fun _ Z => -∇ ℒ Z

/-- The K-step flow `K̇ = -∇_K ℒ(K V₀ᵀ)` (Algorithm 1 of arXiv 2205.13571, line 5). -/
noncomputable def kFlow (ℒ : Matrix m n ℝ → ℝ) (V₀ : Matrix n k ℝ) :
    ℝ → Matrix m k ℝ → Matrix m k ℝ :=
  fun _ K => -∇ (fun K' => ℒ (K' * V₀ᵀ)) K

/-- The L-step flow `L̇ = -∇_L ℒ(U₀ Lᵀ)` (Algorithm 1 of arXiv 2205.13571, line 7). -/
noncomputable def lFlow (ℒ : Matrix m n ℝ → ℝ) (U₀ : Matrix m k ℝ) :
    ℝ → Matrix n k ℝ → Matrix n k ℝ :=
  fun _ L => -∇ (fun L' => ℒ (U₀ * L'ᵀ)) L

/-- The S-step flow `Ṡ = -∇_S ℒ(U₁ S V₁ᵀ)` (Algorithm 1 of arXiv 2205.13571, line 16). -/
noncomputable def sFlow (ℒ : Matrix m n ℝ → ℝ) (U₁ : Matrix m k ℝ) (V₁ : Matrix n k' ℝ) :
    ℝ → Matrix k k' ℝ → Matrix k k' ℝ :=
  fun _ S => -∇ (fun S' => ℒ (U₁ * S' * V₁ᵀ)) S

variable {ℒ : Matrix m n ℝ → ℝ}

/-- The K-step flow is the K-field of the BUG integrator for `F = -∇ℒ`: eq. (7) of
arXiv 2205.13571, `K̇ = -∇ℒ(K V₀ᵀ) V₀`. -/
theorem kFlow_eq (hℒ : Differentiable ℝ ℒ) (V₀ : Matrix n k ℝ) :
    kFlow ℒ V₀ = kField V₀ (gradField ℒ) := by
  funext t K
  have h := (hasGradientAt_kLoss V₀ (hℒ (K * V₀ᵀ)).hasGradientAt).gradient
  simp [kFlow, kField, gradField, h, Matrix.neg_mul]

/-- The L-step flow is the L-field of the BUG integrator for `F = -∇ℒ`: eq. (7) of
arXiv 2205.13571, `L̇ = -∇ℒ(U₀ Lᵀ)ᵀ U₀`. -/
theorem lFlow_eq (hℒ : Differentiable ℝ ℒ) (U₀ : Matrix m k ℝ) :
    lFlow ℒ U₀ = lField U₀ (gradField ℒ) := by
  funext t L
  have h := (hasGradientAt_lLoss U₀ (hℒ (U₀ * Lᵀ)).hasGradientAt).gradient
  simp [lFlow, lField, gradField, h, Matrix.neg_mul, Matrix.transpose_neg]

/-- The S-step flow is the S-field of the BUG integrator for `F = -∇ℒ`: eq. (8) of
arXiv 2205.13571, `Ṡ = -U₁ᵀ ∇ℒ(U₁ S V₁ᵀ) V₁`. -/
theorem sFlow_eq (hℒ : Differentiable ℝ ℒ) (U₁ : Matrix m k ℝ) (V₁ : Matrix n k' ℝ) :
    sFlow ℒ U₁ V₁ = sField U₁ V₁ (gradField ℒ) := by
  funext t S
  have h := (hasGradientAt_sLoss U₁ V₁ (hℒ (U₁ * S * V₁ᵀ)).hasGradientAt).gradient
  simp [sFlow, sField, gradField, h, Matrix.neg_mul, Matrix.mul_neg]

end FactorGradients

/-! ### Algorithm 1: one step -/

section Steps

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r p r₁ : ℕ}

/-- The Frobenius norm of the discarded singular values `(∑_{i ≥ s} σᵢ²)^{1/2}`, zero-indexed: the
truncation rule of Sec. 4.3 of arXiv 2205.13571 keeps the indices `i < s`. -/
noncomputable def svdTail (σ : Fin p → ℝ) (s : ℕ) : ℝ :=
  √(∑ i : Fin p, if (i : ℕ) < s then 0 else σ i ^ 2)

/-- **Bridge.** `svdTail` is the square root of the core discarded weight `tailSqSum`. -/
theorem svdTail_eq_sqrt_tailSqSum (σ : Fin p → ℝ) (s : ℕ) : svdTail σ s = √(tailSqSum σ s) := by
  rw [svdTail, tailSqSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < s
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-- One step of the **fixed-rank** Algorithm 1 of arXiv 2205.13571 (`adaptive = False`, integrated
exactly as in Theorem 1, bias not modelled), from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`: the K-, L- and
S-steps are gradient flows of `ℒ` with respect to the factors (lines 5, 7, 16), and `U₁`, `V₁` have
orthonormal columns and capture `K(t₁)`, `L(t₁)` (lines 11, 13).  The new weight is
`Y₁ = U₁ S(t₁) V₁ᵀ`. -/
structure IsDLRTStep (ℒ : Matrix m n ℝ → ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
    (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (S : ℝ → Matrix (Fin r) (Fin r) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K̇ = -∇_K ℒ(K V₀ᵀ)`. -/
  kSol : ODESolution (kFlow ℒ V₀) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L̇ = -∇_L ℒ(U₀ Lᵀ)`. -/
  lSol : ODESolution (lFlow ℒ U₀) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- `U₁` spans `K(t₁)`. -/
  kCap : U₁ * U₁ᵀ * K t₁ = K t₁
  orthV₁ : V₁ᵀ * V₁ = 1
  /-- `V₁` spans `L(t₁)`. -/
  lCap : V₁ * V₁ᵀ * Lf t₁ = Lf t₁
  /-- S-step `Ṡ = -∇_S ℒ(U₁ S V₁ᵀ)`. -/
  sSol : ODESolution (sFlow ℒ U₁ V₁) S t₀ t₁
  /-- `S(t₀) = M S₀ Nᵀ` with `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`. -/
  sStart : S t₀ = U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)

/-- One step of the **rank-adaptive** Algorithm 1 of arXiv 2205.13571 (`adaptive = True`, integrated
exactly as in Theorem 1, bias not modelled), from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`.  As
`IsDLRTStep`, with bases `Û = Uh`, `V̂ = Vh` augmented by `U₀`, `V₀` (lines 8–13).  Lines 17–21 are
an SVD `Ŝ(t₁) = P diag(σ) Qᵀ` and the rule of Sec. 4.3: `r₁` is the smallest number with
`(∑_{i ≥ r₁} σᵢ²)^{1/2} ≤ ϑ`, and `U₁ = Û P̃`, `S₁ = diag(σ₀, …, σ_{r₁-1})`, `V₁ = V̂ Q̃` for the
leading `r₁` columns `P̃`, `Q̃`.  The new weight is `Y₁ = U₁ S₁ V₁ᵀ`.  `exists_isAdaptiveDLRTStep`
shows that such steps exist. -/
structure IsAdaptiveDLRTStep (ℒ : Matrix m n ℝ → ℝ) (ϑ t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (Uh : Matrix m k ℝ)
    (Vh : Matrix n k' ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (Sh : ℝ → Matrix k k' ℝ) (P : Matrix k (Fin p) ℝ) (σ : Fin p → ℝ) (Q : Matrix k' (Fin p) ℝ)
    (U₁ : Matrix m (Fin r₁) ℝ) (S₁ : Matrix (Fin r₁) (Fin r₁) ℝ) (V₁ : Matrix n (Fin r₁) ℝ) :
    Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K̇ = -∇_K ℒ(K V₀ᵀ)`. -/
  kSol : ODESolution (kFlow ℒ V₀) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L̇ = -∇_L ℒ(U₀ Lᵀ)`. -/
  lSol : ODESolution (lFlow ℒ U₀) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthUh : Uhᵀ * Uh = 1
  /-- `Û` spans `K(t₁)`. -/
  kCap : Uh * Uhᵀ * K t₁ = K t₁
  /-- `Û` spans `U₀` (augmentation). -/
  augU : Uh * Uhᵀ * U₀ = U₀
  orthVh : Vhᵀ * Vh = 1
  /-- `V̂` spans `L(t₁)`. -/
  lCap : Vh * Vhᵀ * Lf t₁ = Lf t₁
  /-- `V̂` spans `V₀` (augmentation). -/
  augV : Vh * Vhᵀ * V₀ = V₀
  /-- S-step `Ŝ' = -∇_S ℒ(Û S V̂ᵀ)`. -/
  sSol : ODESolution (sFlow ℒ Uh Vh) Sh t₀ t₁
  /-- `Ŝ(t₀) = M S₀ Nᵀ` with `M = Ûᵀ U₀`, `N = V̂ᵀ V₀`. -/
  sStart : Sh t₀ = Uhᵀ * U₀ * S₀ * (V₀ᵀ * Vh)
  /-- `P, Σ, Q ← SVD(Ŝ(t₁))`. -/
  svd : Matrix.IsSVD (Sh t₁) P σ Q
  rankLe : r₁ ≤ p
  /-- The discarded singular values are below the threshold. -/
  tail : svdTail σ r₁ ≤ ϑ
  /-- `r₁` is the smallest such number. -/
  minimal : ∀ s < r₁, ϑ < svdTail σ s
  eqU : U₁ = Uh * leadCols rankLe P
  eqS : S₁ = Matrix.diagonal (leadVals rankLe σ)
  eqV : V₁ = Vh * leadCols rankLe Q

omit [DecidableEq k] [DecidableEq k'] in
/-- `‖P diag(d) Qᵀ‖_F² = ∑ᵢ dᵢ²` for orthonormal columns. -/
private theorem sq_norm_mul_diagonal_mul' {P : Matrix k (Fin p) ℝ} {Q : Matrix k' (Fin p) ℝ}
    (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) (d : Fin p → ℝ) :
    ‖P * Matrix.diagonal d * Qᵀ‖ ^ 2 = ∑ i, d i ^ 2 := by
  rw [Frobenius.norm_mul_transpose_of_orthonormal hQ, Frobenius.norm_mul_of_orthonormal hP,
    Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]

/-- The leading columns of a matrix with orthonormal columns are orthonormal. -/
theorem transpose_leadCols_mul_self {ι : Type*} [Fintype ι] {X : Matrix ι (Fin p) ℝ}
    (hX : Xᵀ * X = 1) (hr : r₁ ≤ p) : (leadCols hr X)ᵀ * leadCols hr X = 1 := by
  have h := congrArg (fun M => M.submatrix (Fin.castLE hr) (Fin.castLE hr)) hX
  simp only [Matrix.submatrix_one _ (Fin.castLE_injective hr)] at h
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id] at h
  exact h

omit [DecidableEq k] [DecidableEq k'] in
/-- The truncation error of an SVD is exactly the Frobenius norm of the discarded singular
values. -/
theorem norm_sub_svdTrunc_eq {A : Matrix k k' ℝ} {P : Matrix k (Fin p) ℝ} {σ : Fin p → ℝ}
    {Q : Matrix k' (Fin p) ℝ} (hs : Matrix.IsSVD A P σ Q) (r₁ : ℕ) :
    ‖A - Matrix.svdTrunc P σ Q r₁‖ = svdTail σ r₁ := by
  have h := sq_norm_mul_diagonal_mul' hs.orthU hs.orthV
    (fun i : Fin p => if (i : ℕ) < r₁ then 0 else σ i)
  rw [← IsSVD.sub_svdTrunc hs r₁] at h
  rw [svdTail, ← Real.sqrt_sq (norm_nonneg (A - Matrix.svdTrunc P σ Q r₁)), h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

namespace IsAdaptiveDLRTStep

variable {ℒ : Matrix m n ℝ → ℝ} {ϑ t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m k ℝ}
  {Vh : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sh : ℝ → Matrix k k' ℝ} {P : Matrix k (Fin p) ℝ} {σ : Fin p → ℝ} {Q : Matrix k' (Fin p) ℝ}
  {U₁ : Matrix m (Fin r₁) ℝ} {S₁ : Matrix (Fin r₁) (Fin r₁) ℝ} {V₁ : Matrix n (Fin r₁) ℝ}

/-- The truncated left basis of Algorithm 1 of arXiv 2205.13571 has orthonormal columns. -/
theorem orthU₁ (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    U₁ᵀ * U₁ = 1 := by
  have h := transpose_leadCols_mul_self hs.svd.orthU hs.rankLe
  have h' : U₁ᵀ * U₁ = (Uh * leadCols hs.rankLe P)ᵀ * (Uh * leadCols hs.rankLe P) := by
    rw [← hs.eqU]
  rw [h', Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uhᵀ, hs.orthUh,
    Matrix.one_mul, h]

/-- The truncated right basis of Algorithm 1 of arXiv 2205.13571 has orthonormal columns. -/
theorem orthV₁ (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    V₁ᵀ * V₁ = 1 := by
  have h := transpose_leadCols_mul_self hs.svd.orthV hs.rankLe
  have h' : V₁ᵀ * V₁ = (Vh * leadCols hs.rankLe Q)ᵀ * (Vh * leadCols hs.rankLe Q) := by
    rw [← hs.eqV]
  rw [h', Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vhᵀ, hs.orthVh,
    Matrix.one_mul, h]

/-- The new weight of Algorithm 1 of arXiv 2205.13571 is the truncated SVD of `Ŝ(t₁)` in the
augmented bases. -/
theorem eq_svdTrunc (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    U₁ * S₁ * V₁ᵀ = Uh * Matrix.svdTrunc P σ Q r₁ * Vhᵀ := by
  have h : U₁ * S₁ * V₁ᵀ = Uh * leadCols hs.rankLe P * Matrix.diagonal (leadVals hs.rankLe σ) *
      (Vh * leadCols hs.rankLe Q)ᵀ := by rw [← hs.eqU, ← hs.eqS, ← hs.eqV]
  rw [h, svdTrunc_eq_leadCols hs.rankLe, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Eckart–Young for the truncation step** (arXiv 2205.13571, proof of Theorem 2,
`‖Y₁ - Ŷ₁‖ ≤ ϑ`): the error of the truncation is exactly the Frobenius norm of the discarded
singular values. -/
theorem norm_sub_eq (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    ‖U₁ * S₁ * V₁ᵀ - Uh * Sh t₁ * Vhᵀ‖ = svdTail σ r₁ := by
  rw [hs.eq_svdTrunc, ← Matrix.sub_mul, ← Matrix.mul_sub,
    Frobenius.norm_mul_transpose_of_orthonormal hs.orthVh,
    Frobenius.norm_mul_of_orthonormal hs.orthUh, norm_sub_rev,
    norm_sub_svdTrunc_eq hs.svd r₁]

/-- **Eckart–Young for the truncation step** (arXiv 2205.13571, Sec. 4, "Automatic rank
adaptation"): `Y₁ = U₁ S₁ V₁ᵀ` is a best approximation of `Ŷ₁ = Û Ŝ(t₁) V̂ᵀ` among all matrices of
rank at most `r₁`. -/
theorem norm_sub_le_of_rank_le
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) {Y : Matrix m n ℝ}
    (hY : Y.rank ≤ r₁) : ‖U₁ * S₁ * V₁ᵀ - Uh * Sh t₁ * Vhᵀ‖ ≤ ‖Y - Uh * Sh t₁ * Vhᵀ‖ := by
  rw [hs.norm_sub_eq, ← norm_sub_svdTrunc_eq hs.svd r₁, norm_sub_rev Y]
  have hrank : (Uhᵀ * Y * Vh).rank ≤ r₁ :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hY)
  exact (IsSVD.norm_sub_svdTrunc_le hs.svd hrank).trans
    (norm_coeff_sub_le hs.orthUh hs.orthVh _ _)

/-- The new weight has rank at most `r₁`, and `r₁` is at most the size `p` of the SVD (`p = 2 r` in
the augmented algorithm of arXiv 2205.13571). -/
theorem rank_le (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    (U₁ * S₁ * V₁ᵀ).rank ≤ r₁ ∧ r₁ ≤ p :=
  ⟨(Matrix.rank_mul_le_right _ _).trans (by simpa using V₁ᵀ.rank_le_card_height), hs.rankLe⟩

/-- The threshold of a step is nonnegative. -/
theorem tol_nonneg (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁) :
    0 ≤ ϑ :=
  (Real.sqrt_nonneg _).trans hs.tail

/-- **The rank-adaptive DLRT step is the rank-adaptive BUG step for `F = -∇ℒ`**: the factor flows
of Algorithm 1 of arXiv 2205.13571 are the K-, L- and S-steps of arXiv 2104.05247 by the chain
rule, and the truncated SVD is a truncation to the tolerance `ϑ`. -/
theorem isRankAdaptiveStep
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hℒ : Differentiable ℝ ℒ) :
    IsRankAdaptiveStep (gradField ℒ) ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh (U₁ * S₁ * V₁ᵀ) where
  orthU₀ := hs.orthU₀
  orthV₀ := hs.orthV₀
  kSol := kFlow_eq hℒ V₀ ▸ hs.kSol
  kStart := hs.kStart
  lSol := lFlow_eq hℒ U₀ ▸ hs.lSol
  lStart := hs.lStart
  orthUa := hs.orthUh
  kCap := hs.kCap
  augU := hs.augU
  orthVa := hs.orthVh
  lCap := hs.lCap
  augV := hs.augV
  sSol := sFlow_eq hℒ Uh Vh ▸ hs.sSol
  sStart := hs.sStart
  trunc := by rw [hs.norm_sub_eq]; exact hs.tail

/-- **The augmentation fixes the starting value** (arXiv 2205.13571, proof of Theorem 2, quoting
Lemma 1 of arXiv 2104.05247): the S-step starts at `Ŷ(t₀) = Û Ŝ(t₀) V̂ᵀ = Y₀`, because the ranges of
`Û`, `V̂` contain those of `U₀`, `V₀`. -/
theorem start_eq (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hℒ : Differentiable ℝ ℒ) : Uh * Sh t₀ * Vhᵀ = U₀ * S₀ * V₀ᵀ :=
  (hs.isRankAdaptiveStep hℒ).start_eq

end IsAdaptiveDLRTStep

/-- **The fixed-rank DLRT step is the BUG step for `F = -∇ℒ`** (arXiv 2205.13571, eqs. (7), (8)
and Sec. 4.2). -/
theorem IsDLRTStep.isStep {ℒ : Matrix m n ℝ → ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hℒ : Differentiable ℝ ℒ) :
    IsStep (gradField ℒ) t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S where
  orthU₀ := hs.orthU₀
  orthV₀ := hs.orthV₀
  kSol := kFlow_eq hℒ V₀ ▸ hs.kSol
  kStart := hs.kStart
  lSol := lFlow_eq hℒ U₀ ▸ hs.lSol
  lStart := hs.lStart
  orthU₁ := hs.orthU₁
  kCap := hs.kCap
  orthV₁ := hs.orthV₁
  lCap := hs.lCap
  sSol := sFlow_eq hℒ U₁ V₁ ▸ hs.sSol
  sStart := hs.sStart

end Steps

/-! ### The assumptions P1 and P2 -/

section Assumptions

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Assumption P1** of arXiv 2205.13571 (Appendix 6.1): `F = -∇ℒ` exists and satisfies
`‖F(Z)‖ ≤ C₁`, `‖F(Z) - F(Z̃)‖ ≤ C₂ ‖Z - Z̃‖` for all `Z`, `Z̃`, as displayed in the appendix (the
surrounding text says "locally"). -/
structure IsP1 (ℒ : Matrix m n ℝ → ℝ) (C₁ C₂ : ℝ) : Prop where
  differentiable : Differentiable ℝ ℒ
  bounded : ∀ Z, ‖∇ ℒ Z‖ ≤ C₁
  lipschitz : ∀ Z Z', ‖∇ ℒ Z - ∇ ℒ Z'‖ ≤ C₂ * ‖Z - Z'‖

/-- **Assumption P2** of arXiv 2205.13571 (Appendix 6.1), near a matrix `W`: for all
`Z = U S Vᵀ ∈ M_r` (orthonormal `U`, `V`, invertible `S`) closer to `W` than `ρ`, the part of
`F(Z) = -∇ℒ(Z)` normal to `T_Z M_r` is small, `‖(I - P(Z)) F(Z)‖ ≤ ε`.  The paper says "arbitrary
close"; here the radius `ρ` is explicit. -/
def IsP2 (ℒ : Matrix m n ℝ → ℝ) (W : Matrix m n ℝ) (r : ℕ) (ρ ε : ℝ) : Prop :=
  ∀ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S → ‖U * S * Vᵀ - W‖ < ρ →
      ‖(1 - tangentProj U V) (-∇ ℒ (U * S * Vᵀ))‖ ≤ ε

variable {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ : ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- Under P1 the field `F = -∇ℒ` is `C₂`-Lipschitz. -/
theorem IsP1.isLipschitzField (h : IsP1 ℒ C₁ C₂) : IsLipschitzField (gradField ℒ) C₂ :=
  fun _ x y => by
    change ‖-∇ ℒ x - -∇ ℒ y‖ ≤ _
    rw [neg_sub_neg, norm_sub_rev]
    exact h.lipschitz x y

omit [DecidableEq m] [DecidableEq n] in
/-- Under P1 the field `F = -∇ℒ` is bounded by `C₁`. -/
theorem IsP1.isBoundedField (h : IsP1 ℒ C₁ C₂) : IsBoundedField (gradField ℒ) C₁ :=
  fun _ x => by simpa [gradField] using h.bounded x

omit [DecidableEq m] [DecidableEq n] in
/-- The bound of P1 is nonnegative. -/
theorem IsP1.nonneg (h : IsP1 ℒ C₁ C₂) : 0 ≤ C₁ := (norm_nonneg _).trans (h.bounded 0)

omit [DecidableEq m] [DecidableEq n] in
/-- Under P1 the gradient is continuous. -/
theorem IsP1.continuous_gradient (h : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) : Continuous (∇ ℒ) := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C₂, hC₂⟩) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact h.lipschitz x y

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The invertible matrices `S + δ I` are dense in `δ`. -/
theorem dense_isUnit_add_smul {r : ℕ} (S : Matrix (Fin r) (Fin r) ℝ) :
    Dense {δ : ℝ | IsUnit (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ))} := by
  have hfin : {δ : ℝ | (Matrix.charpoly (-S)).IsRoot δ}.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  refine (hfin.countable.dense_compl ℝ).mono fun δ hδ => ?_
  have hdet : (Matrix.charpoly (-S)).eval δ = (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ)).det := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, add_comm]
  simp only [mem_ofPred_eq]
  rw [Matrix.isUnit_iff_isUnit_det, ← hdet, isUnit_iff_ne_zero]
  exact hδ

/-- The normal part of the tangent projector: `(I - P) Z = (I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem one_sub_tangentProj_apply {k k' : Type*} [Fintype k] [Fintype k'] (U : Matrix m k ℝ)
    (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    (1 - tangentProj U V) Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  have h := tangentProj_add_normal U V Z
  rw [sub_apply, one_apply_eq_self]
  nth_rewrite 1 [← h]
  abel

/-- **P2 of arXiv 2205.13571 extends to rank-deficient points.**  The K- and L-step iterates
`K(t₁) V₀ᵀ`, `U₀ L(t₁)ᵀ`
need not have rank exactly `r`.  Since `F` is continuous and `S + δ I` is invertible for almost all
`δ`, the bound of P2 extends from `M_r` to all `U S Vᵀ` with orthonormal `U`, `V`. -/
theorem IsP2.normal_le {W : Matrix m n ℝ} {r : ℕ} {ρ ε : ℝ} (h : IsP2 ℒ W r ρ ε)
    (hc : Continuous (∇ ℒ)) {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (S : Matrix (Fin r) (Fin r) ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hlt : ‖U * S * Vᵀ - W‖ < ρ) (t : ℝ) :
    ‖(1 - U * Uᵀ) * gradField ℒ t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
  set f : ℝ → Matrix m n ℝ := fun δ => U * S * Vᵀ + δ • (U * Vᵀ) with hf_def
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hfeq : ∀ δ, f δ = U * (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ)) * Vᵀ := fun δ => by
    simp [hf_def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hopen : IsOpen {δ : ℝ | ‖f δ - W‖ < ρ} :=
    isOpen_lt ((hf.sub continuous_const).norm) continuous_const
  have h0 : (0 : ℝ) ∈ {δ : ℝ | ‖f δ - W‖ < ρ} := by simpa [hf_def] using hlt
  have hcl := (dense_isUnit_add_smul S).open_subset_closure_inter hopen h0
  let G : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
    (Frobenius.rightMulCLM (1 - V * Vᵀ)).comp (Frobenius.leftMulCLM (1 - U * Uᵀ))
  have hGc : Continuous fun δ => ‖G (∇ ℒ (f δ))‖ := (G.continuous.comp (hc.comp hf)).norm
  have hclosed : IsClosed {δ : ℝ | ‖G (∇ ℒ (f δ))‖ ≤ ε} := isClosed_le hGc continuous_const
  have hsub : {δ : ℝ | ‖f δ - W‖ < ρ} ∩ {δ | IsUnit (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ))} ⊆
      {δ : ℝ | ‖G (∇ ℒ (f δ))‖ ≤ ε} := by
    rintro δ ⟨hδ1, hδ2⟩
    have h1 := h U V _ hU hV hδ2 (by simpa only [mem_ofPred_eq, hfeq] using hδ1)
    rw [one_sub_tangentProj_apply, ← hfeq, Matrix.mul_neg, Matrix.neg_mul, norm_neg] at h1
    exact h1
  have h2 := hclosed.closure_subset_iff.2 hsub hcl
  simp only [mem_ofPred_eq] at h2
  have h3 : f 0 = U * S * Vᵀ := by simp [hf_def]
  rw [h3] at h2
  have h4 : (1 - U * Uᵀ) * gradField ℒ t (U * S * Vᵀ) * (1 - V * Vᵀ)
      = -G (∇ ℒ (U * S * Vᵀ)) := by
    simp [G, gradField, Matrix.mul_neg, Matrix.neg_mul]
  rw [h4, norm_neg]
  exact h2

end Assumptions

/-! ### From P2 to the abstract step -/

section Near

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ} {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ : ℝ}

omit [Fintype k'] [DecidableEq k'] in
/-- The K-step iterate stays near the exact solution: `‖K(t₁) V₀ᵀ - W(t₁)‖ ≤ e + 2 B h` if
`‖Y₀ - W(t₀)‖ ≤ e`. -/
theorem norm_kIterate_sub_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {B e h t₀ t₁ : ℝ}
    {U₀ : Matrix m k ℝ} {S₀ : Matrix k k ℝ} {V₀ : Matrix n k ℝ} {K : ℝ → Matrix m k ℝ}
    {W : ℝ → Matrix m n ℝ} (hV₀ : V₀ᵀ * V₀ = 1) (hF : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hK : ODESolution (kField V₀ F) K t₀ t₁) (hK₀ : K t₀ = U₀ * S₀)
    (hW : ODESolution F W t₀ t₁) (he : ‖U₀ * S₀ * V₀ᵀ - W t₀‖ ≤ e) :
    ‖K t₁ * V₀ᵀ - W t₁‖ ≤ e + 2 * B * h := by
  have hmem : t₁ ∈ Icc t₀ t₁ := ⟨by linarith, le_rfl⟩
  have h1 := (odeSolution_kField hK).norm_sub_start_le_of_proj hF (isOrthProj_rightProj hV₀) ht₁
    t₁ hmem
  simp only [hK₀] at h1
  have h2 := hW.norm_sub_le_of_bounded hF t₁ hmem
  have h3 : K t₁ * V₀ᵀ - W t₁ =
      (K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - W t₀) - (W t₁ - W t₀) := by abel
  rw [h3]
  have h4 : t₁ - t₀ = h := by linarith
  rw [h4] at h2
  calc _ ≤ ‖K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ + ‖U₀ * S₀ * V₀ᵀ - W t₀‖ + ‖W t₁ - W t₀‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e + 2 * B * h := by linarith

omit [Fintype k'] [DecidableEq k'] in
/-- The L-step iterate stays near the exact solution: `‖U₀ L(t₁)ᵀ - W(t₁)‖ ≤ e + 2 B h` if
`‖Y₀ - W(t₀)‖ ≤ e`. -/
theorem norm_lIterate_sub_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {B e h t₀ t₁ : ℝ}
    {U₀ : Matrix m k ℝ} {S₀ : Matrix k k ℝ} {V₀ : Matrix n k ℝ} {Lf : ℝ → Matrix n k ℝ}
    {W : ℝ → Matrix m n ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hF : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hL : ODESolution (lField U₀ F) Lf t₀ t₁) (hL₀ : Lf t₀ = V₀ * S₀ᵀ)
    (hW : ODESolution F W t₀ t₁) (he : ‖U₀ * S₀ * V₀ᵀ - W t₀‖ ≤ e) :
    ‖U₀ * (Lf t₁)ᵀ - W t₁‖ ≤ e + 2 * B * h := by
  have hmem : t₁ ∈ Icc t₀ t₁ := ⟨by linarith, le_rfl⟩
  have h1 := (odeSolution_lField hL).norm_sub_start_le_of_proj hF (isOrthProj_leftProj hU₀) ht₁
    t₁ hmem
  have h0 : U₀ * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
    rw [hL₀, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [h0] at h1
  have h2 := hW.norm_sub_le_of_bounded hF t₁ hmem
  have h3 : U₀ * (Lf t₁)ᵀ - W t₁ =
      (U₀ * (Lf t₁)ᵀ - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - W t₀) - (W t₁ - W t₀) := by abel
  rw [h3]
  have h4 : t₁ - t₀ = h := by linarith
  rw [h4] at h2
  calc _ ≤ ‖U₀ * (Lf t₁)ᵀ - U₀ * S₀ * V₀ᵀ‖ + ‖U₀ * S₀ * V₀ᵀ - W t₀‖ + ‖W t₁ - W t₀‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e + 2 * B * h := by linarith

/-- A matrix rank-adaptive step for `F = -∇ℒ` is an abstract `IsRankAdaptiveBUGStep`, using P2 of
arXiv 2205.13571 only at the two iterates `K(t₁) V₀ᵀ` and `U₀ L(t₁)ᵀ`. -/
theorem isRankAdaptiveBUGStep_of_near {ϑ t₀ t₁ ρ ε : ℝ} {U₀ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ}
    {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {Sa : ℝ → Matrix k k' ℝ} {Y₁ W : Matrix m n ℝ}
    (hs : IsRankAdaptiveStep (gradField ℒ) ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hc : Continuous (∇ ℒ)) (hP2 : IsP2 ℒ W r ρ ε) (hK : ‖K t₁ * V₀ᵀ - W‖ < ρ)
    (hL : ‖U₀ * (Lf t₁)ᵀ - W‖ < ρ) :
    IsRankAdaptiveBUGStep (gradField ℒ) ε ϑ (leftProj U₀) (rightProj V₀) (leftProj Ua)
      (rightProj Va) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => Ua * Sa t * Vaᵀ) Y₁ := by
  classical
  exact
    { projP₀ := isOrthProj_leftProj hs.orthU₀
      projQ₀ := isOrthProj_rightProj hs.orthV₀
      projP₁ := isOrthProj_leftProj hs.orthUa
      projQ₁ := isOrthProj_rightProj hs.orthVa
      comm₁ := leftProj_rightProj_comm Ua Va
      kSol := odeSolution_kField hs.kSol
      kStart := by rw [hs.kStart]
      kCap := by rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
      kNormal t _ := by
        obtain ⟨U', hU', hcap, hin⟩ := hs.exists_kBasis
        rw [one_sub_leftProj_one_sub_rightProj_apply]
        have hK' : K t₁ * V₀ᵀ = U' * (U'ᵀ * K t₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hcap]
        rw [hK'] at hK ⊢
        exact (norm_normal_le_of_left hs.orthUa hin V₀ _).trans
          (hP2.normal_le hc _ hU' hs.orthV₀ hK t)
      lSol := odeSolution_lField hs.lSol
      lStart := by
        rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      lCap := by
        have hT : (Lf t₁)ᵀ * Va * Vaᵀ = (Lf t₁)ᵀ := by
          simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
        rw [rightProj_apply, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hT]
      lNormal t _ := by
        obtain ⟨V', hV', hcap, hin⟩ := hs.exists_lBasis
        rw [one_sub_rightProj_one_sub_leftProj_apply]
        have hT : (Lf t₁)ᵀ * V' * V'ᵀ = (Lf t₁)ᵀ := by
          simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hcap
        have hL' : U₀ * (Lf t₁)ᵀ = U₀ * ((Lf t₁)ᵀ * V') * V'ᵀ := by
          rw [Matrix.mul_assoc U₀, hT]
        rw [hL'] at hL ⊢
        exact (norm_normal_le_of_right hs.orthVa hin U₀ _).trans
          (hP2.normal_le hc _ hs.orthU₀ hV' hL t)
      sSol := odeSolution_sField hs.sSol
      sStart := hs.ys_start
      augP := hs.aug_left
      augQ := hs.aug_right
      trunc := hs.trunc }

/-- A fixed-rank DLRT step of arXiv 2205.13571 is an abstract `IsBUGStep`, using P2 only at the two
iterates
`K(t₁) V₀ᵀ` and `U₀ L(t₁)ᵀ`. -/
theorem IsDLRTStep.isBUGStep_of_near {t₀ t₁ ρ ε : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {W : Matrix m n ℝ}
    (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hd : Differentiable ℝ ℒ)
    (hc : Continuous (∇ ℒ)) (hP2 : IsP2 ℒ W r ρ ε) (hK : ‖K t₁ * V₀ᵀ - W‖ < ρ)
    (hL : ‖U₀ * (Lf t₁)ᵀ - W‖ < ρ) :
    IsBUGStep (gradField ℒ) ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ) (fun t => U₁ * S t * V₁ᵀ) := by
  classical
  refine (hs.isStep hd).isBUGStep_of_normal (fun t _ => ?_) (fun t _ => ?_)
  · have hK' : K t₁ * V₀ᵀ = U₁ * (U₁ᵀ * K t₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hs.kCap]
    rw [hK'] at hK ⊢
    exact hP2.normal_le hc _ hs.orthU₁ hs.orthV₀ hK t
  · have hT : (Lf t₁)ᵀ * V₁ * V₁ᵀ = (Lf t₁)ᵀ := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
    have hL' : U₀ * (Lf t₁)ᵀ = U₀ * ((Lf t₁)ᵀ * V₁) * V₁ᵀ := by
      rw [Matrix.mul_assoc U₀, hT]
    rw [hL'] at hL ⊢
    exact hP2.normal_le hc _ hs.orthU₀ hs.orthV₁ hL t

end Near

/-! ### The local lemmas of the appendix -/

section Local

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ : ℝ}
  {t₀ t₁ η ρ ε : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ}
  {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {W : ℝ → Matrix m n ℝ}

/-- The constant `θ = C₁ C₂ (4 e^{C₂ η} + 9) η² + (3 e^{C₂ η} + 4) ε η` of Lemma 1 of
arXiv 2205.13571. -/
noncomputable def lemmaTheta (C₁ C₂ ε η : ℝ) : ℝ :=
  C₁ * C₂ * (4 * Real.exp (C₂ * η) + 9) * η ^ 2 + (3 * Real.exp (C₂ * η) + 4) * ε * η

/-- The library's capture bound is at most the `θ` of the paper. -/
theorem capture_le_lemmaTheta (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    η * (4 * C₂ * C₁ * η + ε) ≤ lemmaTheta C₁ C₂ ε η := by
  have he : 0 < Real.exp (C₂ * η) := Real.exp_pos _
  have h : lemmaTheta C₁ C₂ ε η = η * (4 * C₂ * C₁ * η + ε)
      + (C₁ * C₂ * (4 * Real.exp (C₂ * η) + 5) * η ^ 2
        + (3 * Real.exp (C₂ * η) + 3) * ε * η) := by
    unfold lemmaTheta; ring
  have h2 : 0 ≤ C₁ * C₂ * (4 * Real.exp (C₂ * η) + 5) * η ^ 2
      + (3 * Real.exp (C₂ * η) + 3) * ε * η := by positivity
  linarith

/-- One fixed-rank step of arXiv 2205.13571 started on the exact solution is an abstract BUG step
under P1 and P2. -/
theorem IsDLRTStep.isBUGStep_of_P2 (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) (ht₁ : t₁ = t₀ + η) (hη : 0 ≤ η)
    (hW : ODESolution (gradField ℒ) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ)
    (hP2 : IsP2 ℒ (W t₁) r ρ ε) (hρ : 2 * C₁ * η < ρ) :
    IsBUGStep (gradField ℒ) ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ) (fun t => U₁ * S t * V₁ᵀ) := by
  have hst := hs.isStep hP1.differentiable
  have h0 : ‖U₀ * S₀ * V₀ᵀ - W t₀‖ ≤ 0 := by simp [hW₀]
  have hK := norm_kIterate_sub_le hs.orthV₀ hP1.isBoundedField ht₁ hη hst.kSol hs.kStart hW h0
  have hL := norm_lIterate_sub_le hs.orthU₀ hP1.isBoundedField ht₁ hη hst.lSol hs.lStart hW h0
  exact hs.isBUGStep_of_near hP1.differentiable (hP1.continuous_gradient hC₂) hP2 (by linarith)
    (by linarith)

/-- **Lemma 1 of arXiv 2205.13571** (K-step subspace error, Appendix 6.1, quoted there from
Ceruti–Lubich): under P1 and P2, `‖U¹ U¹ᵀ W¹ - W¹‖ ≤ θ` with the constant of the paper.  P2 is
required at `W¹ = W(t₁)` with a radius `ρ > 2 C₁ η`, and `ε ≥ 0`.  The library's `kstep_capture`
gives the sharper `η (4 C₁ C₂ η + ε)`. -/
theorem dlrt_lemma_1 (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hP1 : IsP1 ℒ C₁ C₂)
    (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε) (ht₁ : t₁ = t₀ + η) (hη : 0 ≤ η)
    (hW : ODESolution (gradField ℒ) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ)
    (hP2 : IsP2 ℒ (W t₁) r ρ ε) (hρ : 2 * C₁ * η < ρ) :
    ‖U₁ * U₁ᵀ * W t₁ - W t₁‖ ≤ lemmaTheta C₁ C₂ ε η := by
  classical
  have hb := hs.isBUGStep_of_P2 hP1 hC₂ ht₁ hη hW hW₀ hP2 hρ
  have h1 := kstep_capture hP1.isLipschitzField hC₂ hP1.isBoundedField hb.projP₁ hb.projQ₀ ht₁ hη
    hW hb.kSol (hb.kStart.trans hW₀.symm) hb.kCap hb.kNormal
  have h2 : U₁ * U₁ᵀ * W t₁ - W t₁ = -((1 - leftProj U₁) (W t₁)) := by
    rw [sub_apply, one_apply_eq_self, leftProj_apply]
    abel
  rw [h2, norm_neg]
  exact h1.trans (capture_le_lemmaTheta hP1.nonneg hC₂ hε hη)

/-- **Lemma 2 of arXiv 2205.13571** (L-step subspace error, Appendix 6.1):
`‖U¹ U¹ᵀ W¹ V¹ V¹ᵀ - W¹‖ ≤ 2 θ`, under the hypotheses of `dlrt_lemma_1`. -/
theorem dlrt_lemma_2 (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hP1 : IsP1 ℒ C₁ C₂)
    (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε) (ht₁ : t₁ = t₀ + η) (hη : 0 ≤ η)
    (hW : ODESolution (gradField ℒ) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ)
    (hP2 : IsP2 ℒ (W t₁) r ρ ε) (hρ : 2 * C₁ * η < ρ) :
    ‖U₁ * U₁ᵀ * W t₁ * V₁ * V₁ᵀ - W t₁‖ ≤ 2 * lemmaTheta C₁ C₂ ε η := by
  have hb := hs.isBUGStep_of_P2 hP1 hC₂ ht₁ hη hW hW₀ hP2 hρ
  have h1 := bug_capture hP1.isLipschitzField hC₂ hP1.isBoundedField hb.projP₀ hb.projQ₀ hb.projP₁
    hb.projQ₁ ht₁ hη hW hb.kSol (hb.kStart.trans hW₀.symm) hb.kCap hb.kNormal hb.lSol
    (hb.lStart.trans hW₀.symm) hb.lCap hb.lNormal
  have h2 := capture_le_lemmaTheta hP1.nonneg hC₂ hε hη
  rw [norm_sub_rev]
  have h3 : ‖W t₁ - leftProj U₁ (rightProj V₁ (W t₁))‖ ≤ 2 * lemmaTheta C₁ C₂ ε η := by linarith
  simpa [Matrix.mul_assoc] using h3

/-- **Lemma 3 of arXiv 2205.13571** (local error of the fixed-rank integrator, Appendix 6.1):
`‖U¹ S¹ V¹ᵀ - W¹‖ ≤ η (ĉ₁ ε + ĉ₂ η)` for `0 ≤ η ≤ H`, with the library's explicit constants
`ĉ₁ = bugC₁ C₂ H`, `ĉ₂ = bugC₂ C₂ C₁ H`, which depend only on `C₁`, `C₂`, `H`, not on singular
values.  P2 is required as in `dlrt_lemma_1`. -/
theorem dlrt_lemma_3 (hs : IsDLRTStep ℒ t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) (hP1 : IsP1 ℒ C₁ C₂)
    (hC₂ : 0 ≤ C₂) (ht₁ : t₁ = t₀ + η) (hη : 0 ≤ η) {H : ℝ} (hηH : η ≤ H)
    (hW : ODESolution (gradField ℒ) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ)
    (hP2 : IsP2 ℒ (W t₁) r ρ ε) (hρ : 2 * C₁ * η < ρ) :
    ‖U₁ * S t₁ * V₁ᵀ - W t₁‖ ≤ η * (bugC₁ C₂ H * ε + bugC₂ C₂ C₁ H * η) :=
  (hs.isBUGStep_of_P2 hP1 hC₂ ht₁ hη hW hW₀ hP2 hρ).local_error_le hP1.isLipschitzField hC₂
    hP1.isBoundedField ht₁ hη hηH hW hW₀

end Local

/-! ### Theorem 1 -/

section Approximation

variable {m n : Type*} [Fintype m] [Fintype n] {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ : ℝ}

/-- The constant `c₁ = T e^{C₂ T} ĉ₁` of Theorem 1 of arXiv 2205.13571, step sizes `η ≤ H`. -/
noncomputable def dlrtC₁ (C₂ H T : ℝ) : ℝ := T * Real.exp (C₂ * T) * bugC₁ C₂ H

/-- The constant `c₂ = T e^{C₂ T} ĉ₂` of Theorem 1 of arXiv 2205.13571, step sizes `η ≤ H`. -/
noncomputable def dlrtC₂ (C₁ C₂ H T : ℝ) : ℝ := T * Real.exp (C₂ * T) * bugC₂ C₂ C₁ H

/-- The constant `c₃ = T e^{C₂ T}` of Theorem 1 of arXiv 2205.13571. -/
noncomputable def dlrtC₃ (C₂ T : ℝ) : ℝ := T * Real.exp (C₂ * T)

/-- **Theorem 1 of arXiv 2205.13571** (approximation error of rank-adaptive DLRT): under P1, if
`W` solves the gradient flow `Ẇ = -∇ℒ(W)` from `W(t₀) = U⁰ S⁰ V⁰ᵀ`, the steps `j < N` of
Algorithm 1 are given (K-, L-, S-flows integrated exactly on the grid `t₀ + j η`, ranks `r j` and
thresholds `ϑs j ≤ ϑ` that may change from step to step), and P2 holds near `W(t₀ + (j+1) η)` at
rank `r j`, then

    ‖U^j S^j V^jᵀ - W(t₀ + j η)‖ ≤ c₁ ε + c₂ η + c₃ ϑ / η      (j ≤ N, N η ≤ T, 0 < η ≤ H).

The bound does not involve singular values.  Differences from the paper:

* one layer, the others frozen, as in Sec. 3.1 and the appendix of the paper;
* the constants `dlrtC₁`, `dlrtC₂`, `dlrtC₃` depend on `C₁`, `C₂`, on the final time `T` and on the
  bound `H` for `η`; the paper's "depend only on `C₁` and `C₂`" is false, see
  `dlrt_constants_depend_on_time`;
* "`Z` sufficiently close to `W(tη)`" in P2 is the ball of radius `ρ`, with the only requirement
  `c₁ ε + c₂ η + c₃ ϑ / η + 2 C₁ η < ρ`: that the iterates stay in the ball is derived by a
  bootstrap, not assumed;
* rank-deficient iterates, which the paper does not discuss, are covered by `IsP2.normal_le`;
* the varying thresholds cover the relative rule `ϑ = τ ‖Σ‖` of Sec. 5, with `ϑ = τ max_j ‖Σ_j‖`. -/
theorem dlrt_approximation {ε ϑ t₀ η H T ρ : ℝ} (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε)
    (hϑ : 0 ≤ ϑ) (hη : 0 < η) (hηH : η ≤ H) {N : ℕ} (hNT : (N : ℝ) * η ≤ T)
    {W : ℝ → Matrix m n ℝ} (hW : ODESolution (gradField ℒ) W t₀ (t₀ + N * η))
    {r ka kb p : ℕ → ℕ} {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ}
    {S : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ} {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ}
    {Uh : (j : ℕ) → Matrix m (Fin (ka j)) ℝ} {Vh : (j : ℕ) → Matrix n (Fin (kb j)) ℝ}
    {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ} {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sh : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ}
    {P : (j : ℕ) → Matrix (Fin (ka j)) (Fin (p j)) ℝ} {σ : (j : ℕ) → Fin (p j) → ℝ}
    {Q : (j : ℕ) → Matrix (Fin (kb j)) (Fin (p j)) ℝ} {ϑs : ℕ → ℝ} (hϑs : ∀ j < N, ϑs j ≤ ϑ)
    (hstep : ∀ j < N, IsAdaptiveDLRTStep ℒ (ϑs j) (t₀ + j * η) (t₀ + (j + 1) * η) (U j) (S j) (V j)
      (Uh j) (Vh j) (K j) (Lf j) (Sh j) (P j) (σ j) (Q j) (U (j + 1)) (S (j + 1)) (V (j + 1)))
    (hW₀ : W t₀ = U 0 * S 0 * (V 0)ᵀ)
    (hρ : dlrtC₁ C₂ H T * ε + dlrtC₂ C₁ C₂ H T * η + dlrtC₃ C₂ T * ϑ / η + 2 * C₁ * η < ρ)
    (hP2 : ∀ j < N, IsP2 ℒ (W (t₀ + (j + 1) * η)) (r j) ρ ε) :
    ∀ j ≤ N, ‖U j * S j * (V j)ᵀ - W (t₀ + j * η)‖ ≤
      dlrtC₁ C₂ H T * ε + dlrtC₂ C₁ C₂ H T * η + dlrtC₃ C₂ T * ϑ / η := by
  have hF := hP1.isLipschitzField
  have hB := hP1.isBoundedField
  have hc := hP1.continuous_gradient hC₂
  have hgrid : ∀ a b : ℝ, a ≤ b → t₀ + a * η ≤ t₀ + b * η := fun a b hab => by
    nlinarith [mul_le_mul_of_nonneg_right hab hη.le]
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily hF hB (fun _ => continuous_const) (t₀ := t₀) hη.le
    (fun j => U j * S j * (V j)ᵀ)
  refine bootstrap_of_global (e := fun j => ‖U j * S j * (V j)ᵀ - W (t₀ + j * η)‖)
    fun m' hm' hprev => ?_
  have hm'R : (m' : ℝ) ≤ N := by exact_mod_cast hm'
  have hsteps : ∀ j < m', IsRankAdaptiveBUGStep (gradField ℒ) ε ϑ (leftProj (U j)) (rightProj (V j))
      (leftProj (Uh j)) (rightProj (Vh j)) (t₀ + j * η) (t₀ + (j + 1) * η)
      (U j * S j * (V j)ᵀ) (fun t => K j t * (V j)ᵀ) (fun t => U j * (Lf j t)ᵀ)
      (fun t => Uh j * Sh j t * (Vh j)ᵀ) (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ) := by
    intro j hj
    have hjN : j < N := hj.trans_le hm'
    have hs₀ := (hstep j hjN).isRankAdaptiveStep hP1.differentiable
    have hs : IsRankAdaptiveStep (gradField ℒ) ϑ (t₀ + j * η) (t₀ + (j + 1) * η) (U j) (S j) (V j)
        (Uh j) (Vh j) (K j) (Lf j) (Sh j) (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ) :=
      { hs₀ with trunc := hs₀.trunc.trans (hϑs j hjN) }
    have ht : t₀ + ((j : ℝ) + 1) * η = t₀ + j * η + η := by ring
    have hjR : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
    have hWj : ODESolution (gradField ℒ) W (t₀ + j * η) (t₀ + (j + 1) * η) := by
      refine hW.mono ?_ (hgrid _ _ hjR)
      simpa using hgrid 0 j (by positivity)
    have hK := norm_kIterate_sub_le hs.orthV₀ hB ht hη.le hs.kSol hs.kStart hWj (hprev j hj)
    have hL := norm_lIterate_sub_le hs.orthU₀ hB ht hη.le hs.lSol hs.lStart hWj (hprev j hj)
    exact isRankAdaptiveBUGStep_of_near hs hc (hP2 j hjN) (by linarith) (by linarith)
  have hWm : ODESolution (gradField ℒ) W t₀ (t₀ + m' * η) := hW.mono le_rfl (hgrid _ _ hm'R)
  have hmT : (m' : ℝ) * η ≤ T := (mul_le_mul_of_nonneg_right hm'R hη.le).trans hNT
  have h := rankAdaptiveBUG_global_error_le hF hC₂ hB hε hη.le hηH hWm
    (P := fun j => leftProj (U j)) (Q := fun j => rightProj (V j))
    (Pa := fun j => leftProj (Uh j)) (Qa := fun j => rightProj (Vh j))
    (Y := fun j => U j * S j * (V j)ᵀ) (YK := fun j t => K j t * (V j)ᵀ)
    (YL := fun j t => U j * (Lf j t)ᵀ) (YS := fun j t => Uh j * Sh j t * (Vh j)ᵀ)
    hsteps (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) (δ := 0) (T := T) (by simp [hW₀]) m' le_rfl
    hmT
  have hm'le : (m' : ℝ) ≤ T / η := by rwa [le_div_iff₀ hη]
  have hlast : Real.exp (C₂ * T) * m' * ϑ ≤ dlrtC₃ C₂ T * ϑ / η := by
    have he := Real.exp_pos (C₂ * T)
    have h1 : Real.exp (C₂ * T) * m' * ϑ ≤ Real.exp (C₂ * T) * (T / η) * ϑ := by gcongr
    have h2 : Real.exp (C₂ * T) * (T / η) * ϑ = dlrtC₃ C₂ T * ϑ / η := by
      unfold dlrtC₃; ring
    linarith
  simp only [mul_zero, zero_add] at h
  unfold dlrtC₁ dlrtC₂
  linarith

/-- **Theorem 1 of arXiv 2205.13571 for `adaptive = False`** (fixed rank `r`, no truncation): with
the notation of `dlrt_approximation`,

    ‖U^j S^j V^jᵀ - W(t₀ + j η)‖ ≤ c₁ ε + c₂ η      (j ≤ N, N η ≤ T, 0 < η ≤ H).

The differences from the paper are those of `dlrt_approximation`. -/
theorem dlrt_approximation_fixedRank {ε t₀ η H T ρ : ℝ} (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂)
    (hε : 0 ≤ ε) (hη : 0 < η) (hηH : η ≤ H) {N : ℕ} (hNT : (N : ℝ) * η ≤ T)
    {W : ℝ → Matrix m n ℝ} (hW : ODESolution (gradField ℒ) W t₀ (t₀ + N * η)) {r : ℕ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {Sh : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    (hstep : ∀ j < N, IsDLRTStep ℒ (t₀ + j * η) (t₀ + (j + 1) * η) (U j) (S j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (Sh j))
    (hS : ∀ j < N, S (j + 1) = Sh j (t₀ + (j + 1) * η))
    (hW₀ : W t₀ = U 0 * S 0 * (V 0)ᵀ)
    (hρ : dlrtC₁ C₂ H T * ε + dlrtC₂ C₁ C₂ H T * η + 2 * C₁ * η < ρ)
    (hP2 : ∀ j < N, IsP2 ℒ (W (t₀ + (j + 1) * η)) r ρ ε) :
    ∀ j ≤ N, ‖U j * S j * (V j)ᵀ - W (t₀ + j * η)‖ ≤
      dlrtC₁ C₂ H T * ε + dlrtC₂ C₁ C₂ H T * η := by
  have hF := hP1.isLipschitzField
  have hB := hP1.isBoundedField
  have hc := hP1.continuous_gradient hC₂
  have hgrid : ∀ a b : ℝ, a ≤ b → t₀ + a * η ≤ t₀ + b * η := fun a b hab => by
    nlinarith [mul_le_mul_of_nonneg_right hab hη.le]
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily hF hB (fun _ => continuous_const) (t₀ := t₀) hη.le
    (fun j => U j * S j * (V j)ᵀ)
  refine bootstrap_of_global (e := fun j => ‖U j * S j * (V j)ᵀ - W (t₀ + j * η)‖)
    fun m' hm' hprev => ?_
  have hm'R : (m' : ℝ) ≤ N := by exact_mod_cast hm'
  have hsteps : ∀ j < m', IsBUGStep (gradField ℒ) ε (leftProj (U j)) (rightProj (V j))
      (leftProj (U (j + 1))) (rightProj (V (j + 1))) (t₀ + j * η) (t₀ + (j + 1) * η)
      (U j * S j * (V j)ᵀ) (fun t => K j t * (V j)ᵀ) (fun t => U j * (Lf j t)ᵀ)
      (fun t => U (j + 1) * Sh j t * (V (j + 1))ᵀ) := by
    intro j hj
    have hjN : j < N := hj.trans_le hm'
    have hs := hstep j hjN
    have hst := hs.isStep hP1.differentiable
    have ht : t₀ + ((j : ℝ) + 1) * η = t₀ + j * η + η := by ring
    have hjR : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
    have hWj : ODESolution (gradField ℒ) W (t₀ + j * η) (t₀ + (j + 1) * η) := by
      refine hW.mono ?_ (hgrid _ _ hjR)
      simpa using hgrid 0 j (by positivity)
    have hK := norm_kIterate_sub_le hs.orthV₀ hB ht hη.le hst.kSol hs.kStart hWj (hprev j hj)
    have hL := norm_lIterate_sub_le hs.orthU₀ hB ht hη.le hst.lSol hs.lStart hWj (hprev j hj)
    exact hs.isBUGStep_of_near hP1.differentiable hc (hP2 j hjN) (by linarith) (by linarith)
  have hWm : ODESolution (gradField ℒ) W t₀ (t₀ + m' * η) := hW.mono le_rfl (hgrid _ _ hm'R)
  have hmT : (m' : ℝ) * η ≤ T := (mul_le_mul_of_nonneg_right hm'R hη.le).trans hNT
  have h := bug_global_error_le hF hC₂ hB hε hη.le hηH hWm
    (P := fun j => leftProj (U j)) (Q := fun j => rightProj (V j))
    (Y := fun j => U j * S j * (V j)ᵀ) (YK := fun j t => K j t * (V j)ᵀ)
    (YL := fun j t => U j * (Lf j t)ᵀ) (YS := fun j t => U (j + 1) * Sh j t * (V (j + 1))ᵀ)
    hsteps (fun j hj => by simp only [hS j (hj.trans_le hm' |>.trans_le le_rfl)])
    (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) (δ := 0) (T := T) (by simp [hW₀]) m' le_rfl hmT
  simp only [mul_zero, zero_add] at h
  unfold dlrtC₁ dlrtC₂
  linarith

end Approximation

/-! ### Theorem 2 -/

section Descent

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r p r₁ : ℕ} {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ ϑ t₀ t₁ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {Uh : Matrix m k ℝ} {Vh : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {Sh : ℝ → Matrix k k' ℝ} {P : Matrix k (Fin p) ℝ}
  {σ : Fin p → ℝ} {Q : Matrix k' (Fin p) ℝ} {U₁ : Matrix m (Fin r₁) ℝ}
  {S₁ : Matrix (Fin r₁) (Fin r₁) ℝ} {V₁ : Matrix n (Fin r₁) ℝ}

/-- The rate of the proof of Theorem 2 of arXiv 2205.13571 (eq. (12)):
`α = min_{t₀ ≤ t ≤ t₁} ‖Ûᵀ ∇ℒ(Ŷ(t)) V̂‖` with `Ŷ(t) = Û Ŝ(t) V̂ᵀ`. -/
noncomputable def dlrtAlpha (ℒ : Matrix m n ℝ → ℝ) (Uh : Matrix m k ℝ) (Vh : Matrix n k' ℝ)
    (Sh : ℝ → Matrix k k' ℝ) (t₀ t₁ : ℝ) : ℝ :=
  sInf ((fun t => ‖Uhᵀ * ∇ ℒ (Uh * Sh t * Vhᵀ) * Vh‖) '' Icc t₀ t₁)

/-- The constant of the proof of Theorem 2 of arXiv 2205.13571:
`β = max_{0 ≤ τ ≤ 1} ‖∇ℒ(τ Y + (1 - τ) Y')‖`. -/
noncomputable def dlrtBeta (ℒ : Matrix m n ℝ → ℝ) (Y Y' : Matrix m n ℝ) : ℝ :=
  sSup ((fun τ : ℝ => ‖∇ ℒ (τ • Y + (1 - τ) • Y')‖) '' Icc 0 1)

/-- A rank-adaptive DLRT step of arXiv 2205.13571 under P1 is an abstract rank-adaptive BUG step
with the trivial normal bound `ε = C₁`: P2 is not used, as the paper says for Theorem 2. -/
theorem IsAdaptiveDLRTStep.isRankAdaptiveBUGStep
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) :
    IsRankAdaptiveBUGStep (gradField ℒ) C₁ ϑ (leftProj U₀) (rightProj V₀) (leftProj Uh)
      (rightProj Vh) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => Uh * Sh t * Vhᵀ) (U₁ * S₁ * V₁ᵀ) := by
  classical
  exact (hs.isRankAdaptiveStep hP1.differentiable).isRankAdaptiveBUGStep
    fun t U V S hU hV => (norm_normal_le hU hV _).trans (hP1.isBoundedField t _)

/-- `‖Û Ûᵀ X V̂ V̂ᵀ‖ = ‖Ûᵀ X V̂‖` for orthonormal `Û`, `V̂`. -/
private theorem norm_galerkin_eq (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1)
    (X : Matrix m n ℝ) : ‖leftProj Uh (rightProj Vh X)‖ = ‖Uhᵀ * X * Vh‖ := by
  rw [leftProj_rightProj_apply, Frobenius.norm_mul_transpose_of_orthonormal hVh,
    Frobenius.norm_mul_of_orthonormal hUh]

/-- A differentiable loss has the Fréchet derivative `⟪∇ℒ(x), ·⟫`. -/
private theorem hasFDerivAt_loss (hd : Differentiable ℝ ℒ) (x : Matrix m n ℝ) :
    HasFDerivAt ℒ (innerSL ℝ (∇ ℒ x)) x :=
  hasFDerivAt_of_hasGradientAt (fun z => (hd z).hasGradientAt) x

/-- **The dissipation identity** of the proof of Theorem 2 of arXiv 2205.13571:
`d/dt ℒ(Ŷ(t)) = -‖Ûᵀ ∇ℒ(Ŷ(t)) V̂‖²` along the S-step (right derivative on `[t₀, t₁)`). -/
theorem dlrt_sStep_dissipation
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) {t : ℝ} (ht : t ∈ Ico t₀ t₁) :
    HasDerivWithinAt (fun s => ℒ (Uh * Sh s * Vhᵀ))
      (-‖Uhᵀ * ∇ ℒ (Uh * Sh t * Vhᵀ) * Vh‖ ^ 2) (Ici t) t := by
  have hb := hs.isRankAdaptiveBUGStep hP1
  have h := (hb.sSol_gradFlow (g := ∇ ℒ) fun _ _ => rfl).hasDerivWithinAt_energy_gradFlow
    hb.galerkinProj (hasFDerivAt_loss hP1.differentiable) ht
  rw [← norm_galerkin_eq hs.orthUh hs.orthVh]
  exact h

/-- **Theorem 2 of arXiv 2205.13571, in the form of its proof** (one layer, other weights frozen):
under P1 alone, one step of rank-adaptive Algorithm 1 satisfies

    ℒ(Y₁) ≤ ℒ(Y₀) - α² η + β ϑ,    η = t₁ - t₀,

with `α = dlrtAlpha` and `β = dlrtBeta` as in the paper's proof (`dlrtAlpha_isLeast` and
`dlrtBeta_isGreatest`: they are a minimum and a maximum).  Differences from the paper: the printed
statement has `-α η` with `α > 0` independent of `t`, `η`, `ϑ`, which is false, see
`dlrt_no_uniform_descent` and `dlrt_no_uniform_descent_of_bddBelow`; its proof gives this `α²`,
which depends on the step and may vanish.  No smallness of `η` is needed.  The statement does not
cover fixed-rank steps, for which it fails: `fixedRank_loss_increases`.  For all layers see
`dlrt_descent_sweep`, and for a rate in terms of `Y₀` see `dlrt_descent_explicit`. -/
theorem dlrt_descent (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) (h01 : t₀ ≤ t₁) :
    ℒ (U₁ * S₁ * V₁ᵀ) ≤ ℒ (U₀ * S₀ * V₀ᵀ) - dlrtAlpha ℒ Uh Vh Sh t₀ t₁ ^ 2 * (t₁ - t₀)
      + dlrtBeta ℒ (U₁ * S₁ * V₁ᵀ) (Uh * Sh t₁ * Vhᵀ) * ϑ := by
  have hb := hs.isRankAdaptiveBUGStep hP1
  refine hb.energy_le h01 (hasFDerivAt_loss hP1.differentiable) (g := ∇ ℒ) (fun _ _ => rfl)
    (fun t ht => ?_) fun w hw => ?_
  · rw [norm_galerkin_eq hs.orthUh hs.orthVh]
    have hα0 : 0 ≤ dlrtAlpha ℒ Uh Vh Sh t₀ t₁ := Real.sInf_nonneg (by
      rintro _ ⟨s, -, rfl⟩
      exact norm_nonneg _)
    refine pow_le_pow_left₀ hα0 (csInf_le ⟨0, ?_⟩ ⟨t, Ico_subset_Icc_self ht, rfl⟩) 2
    rintro _ ⟨s, -, rfl⟩
    exact norm_nonneg _
  · rw [segment_eq_image] at hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    refine le_csSup ⟨C₁, ?_⟩ ⟨τ, hτ, ?_⟩
    · rintro _ ⟨τ', -, rfl⟩
      exact hP1.bounded _
    · simp only [add_comm]

/-- The `α` of Theorem 2 of arXiv 2205.13571 is a minimum over the step, as in the paper. -/
theorem dlrtAlpha_isLeast (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) (h01 : t₀ ≤ t₁) :
    IsLeast ((fun t => ‖Uhᵀ * ∇ ℒ (Uh * Sh t * Vhᵀ) * Vh‖) '' Icc t₀ t₁)
      (dlrtAlpha ℒ Uh Vh Sh t₀ t₁) := by
  have hY : ContinuousOn (fun t => Uh * Sh t * Vhᵀ) (Icc t₀ t₁) :=
    (odeSolution_sField (hs.isRankAdaptiveStep hP1.differentiable).sSol).cont
  let G : Matrix m n ℝ →L[ℝ] Matrix k k' ℝ :=
    (Frobenius.rightMulCLM Vh).comp (Frobenius.leftMulCLM Uhᵀ)
  have hc : ContinuousOn (fun t => ‖G (∇ ℒ (Uh * Sh t * Vhᵀ))‖) (Icc t₀ t₁) :=
    (G.continuous.comp_continuousOn
      ((hP1.continuous_gradient hC₂).comp_continuousOn hY)).norm
  have hcomp := isCompact_Icc.image_of_continuousOn hc
  exact ⟨hcomp.sInf_mem ((Set.nonempty_Icc.2 h01).image _),
    fun x hx => csInf_le hcomp.bddBelow hx⟩

/-- The `β` of Theorem 2 of arXiv 2205.13571 is a maximum over the segment, as in the paper. -/
theorem dlrtBeta_isGreatest (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) (Y Y' : Matrix m n ℝ) :
    IsGreatest ((fun τ : ℝ => ‖∇ ℒ (τ • Y + (1 - τ) • Y')‖) '' Icc 0 1) (dlrtBeta ℒ Y Y') := by
  have hc : Continuous fun τ : ℝ => ‖∇ ℒ (τ • Y + (1 - τ) • Y')‖ := by
    have h1 : Continuous fun τ : ℝ => τ • Y + (1 - τ) • Y' :=
      (continuous_id.smul continuous_const).add
        ((continuous_const.sub continuous_id).smul continuous_const)
    exact ((hP1.continuous_gradient hC₂).comp h1).norm
  have hcomp := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).image_of_continuousOn hc.continuousOn
  exact ⟨hcomp.sSup_mem ((Set.nonempty_Icc.2 zero_le_one).image _),
    fun x hx => le_csSup hcomp.bddAbove hx⟩

/-- The `β` of Theorem 2 is at most `C₁`, a constant independent of `t`, `η` and `ϑ`, as claimed in
arXiv 2205.13571. -/
theorem dlrtBeta_le (hP1 : IsP1 ℒ C₁ C₂) (Y Y' : Matrix m n ℝ) : dlrtBeta ℒ Y Y' ≤ C₁ := by
  refine csSup_le ((Set.nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨τ, -, rfl⟩
  exact hP1.bounded _

/-- **Theorem 2 of arXiv 2205.13571 with `β = C₁`**: `ℒ(Y₁) ≤ ℒ(Y₀) - α² η + C₁ ϑ`, where
`α = dlrtAlpha` depends on the step; see `dlrt_descent`. -/
theorem dlrt_descent_of_P1
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) (h01 : t₀ ≤ t₁) :
    ℒ (U₁ * S₁ * V₁ᵀ) ≤ ℒ (U₀ * S₀ * V₀ᵀ) - dlrtAlpha ℒ Uh Vh Sh t₀ t₁ ^ 2 * (t₁ - t₀)
      + C₁ * ϑ := by
  have h := dlrt_descent hs hP1 h01
  have h2 := mul_le_mul_of_nonneg_right (dlrtBeta_le hP1 (U₁ * S₁ * V₁ᵀ) (Uh * Sh t₁ * Vhᵀ))
    hs.tol_nonneg
  linarith

/-- **Theorem 2 of arXiv 2205.13571 with a rate at the start of the step**: if `Y₀` is not
stationary in the augmented bases, the loss really decreases for small `η` and `ϑ`:

    ℒ(Y₁) ≤ ℒ(Y₀) - max(0, ‖Ûᵀ ∇ℒ(Y₀) V̂‖ - C₁ C₂ η)² η + (‖∇ℒ(Y₁)‖ + C₂ ϑ) ϑ.

This makes precise why the paper's `α` cannot be uniform: it is `‖Ûᵀ ∇ℒ(Y₀) V̂‖² + O(η)`. -/
theorem dlrt_descent_explicit
    (hs : IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁)
    (hP1 : IsP1 ℒ C₁ C₂) (hC₂ : 0 ≤ C₂) {η : ℝ} (ht₁ : t₁ = t₀ + η) (hη : 0 ≤ η) :
    ℒ (U₁ * S₁ * V₁ᵀ) ≤ ℒ (U₀ * S₀ * V₀ᵀ)
      - max 0 (‖Uhᵀ * ∇ ℒ (U₀ * S₀ * V₀ᵀ) * Vh‖ - C₂ * C₁ * η) ^ 2 * η
      + (‖∇ ℒ (U₁ * S₁ * V₁ᵀ)‖ + C₂ * ϑ) * ϑ := by
  have h := (hs.isRankAdaptiveBUGStep hP1).energy_le_of_lipschitz_grad ht₁ hη
    (hasFDerivAt_loss hP1.differentiable) (g := ∇ ℒ) (fun _ _ => rfl) hC₂ hP1.lipschitz hP1.bounded
  rwa [norm_galerkin_eq hs.orthUh hs.orthVh] at h

end Descent

/-! ### All layers -/

section Layers

variable {M : ℕ} {a b : Fin M → ℕ}

/-- The weights `(W₁, …, W_M)` of a network with layer shapes `a k × b k`. -/
abbrev Weights (a b : Fin M → ℕ) := ∀ k : Fin M, Matrix (Fin (a k)) (Fin (b k)) ℝ

/-- The loss as a function of layer `k`, all other weights frozen:
`Z ↦ ℒ(W₁, …, Z, …, W_M)` (arXiv 2205.13571, Sec. 3.1). -/
noncomputable def layerLoss (ℒ : Weights a b → ℝ) (W : Weights a b) (k : Fin M)
    (Z : Matrix (Fin (a k)) (Fin (b k)) ℝ) : ℝ :=
  ℒ (Function.update W k Z)

/-- Layer `k` of the inner loop of Algorithm 1 of arXiv 2205.13571: one rank-adaptive step for the
loss of layer `k` with the other weights frozen at their current values replaces `W k` by the new
weight, with rate `α` of Theorem 2. -/
def IsLayerUpdate (ℒ : Weights a b → ℝ) (ϑ t₀ t₁ α : ℝ) (W W' : Weights a b) (k : Fin M) : Prop :=
  ∃ (r ka kb p r₁ : ℕ) (U₀ : Matrix (Fin (a k)) (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix (Fin (b k)) (Fin r) ℝ) (Uh : Matrix (Fin (a k)) (Fin ka) ℝ)
    (Vh : Matrix (Fin (b k)) (Fin kb) ℝ) (K : ℝ → Matrix (Fin (a k)) (Fin r) ℝ)
    (Lf : ℝ → Matrix (Fin (b k)) (Fin r) ℝ) (Sh : ℝ → Matrix (Fin ka) (Fin kb) ℝ)
    (P : Matrix (Fin ka) (Fin p) ℝ) (σ : Fin p → ℝ) (Q : Matrix (Fin kb) (Fin p) ℝ)
    (U₁ : Matrix (Fin (a k)) (Fin r₁) ℝ) (S₁ : Matrix (Fin r₁) (Fin r₁) ℝ)
    (V₁ : Matrix (Fin (b k)) (Fin r₁) ℝ),
    IsAdaptiveDLRTStep (layerLoss ℒ W k) ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁ ∧
      W k = U₀ * S₀ * V₀ᵀ ∧ W' = Function.update W k (U₁ * S₁ * V₁ᵀ) ∧
      α = dlrtAlpha (layerLoss ℒ W k) Uh Vh Sh t₀ t₁

/-- **Theorem 2 of arXiv 2205.13571 for all layers**: for `ℒ(t) = ℒ(W₁ᵗ, …, W_Mᵗ)`, one sweep over
the layers `0, …, M - 1` (`W i` the weights before layer `i`), each layer satisfying P1 with
constants independent of the layer, gives

    ℒ(t + 1) ≤ ℒ(t) - (∑ₖ αₖ²) η + M C₁ ϑ,

with `αₖ = dlrtAlpha` of layer `k`.  Differences from the paper: as in `dlrt_descent`, the rates
depend on the step and are not a uniform positive constant.  Layers are updated one after the other
(the paper's single-layer proof only covers this reading), and bias updates are not modelled. -/
theorem dlrt_descent_sweep {ℒ : Weights a b → ℝ} {W : ℕ → Weights a b} {α : ℕ → ℝ}
    {C₁ C₂ ϑ t₀ t₁ : ℝ} (hP1 : ∀ k : Fin M, IsP1 (layerLoss ℒ (W k) k) C₁ C₂) (h01 : t₀ ≤ t₁)
    (hup : ∀ k : Fin M, IsLayerUpdate ℒ ϑ t₀ t₁ (α k) (W k) (W (k + 1)) k) :
    ℒ (W M) ≤ ℒ (W 0) - (∑ k ∈ Finset.range M, α k ^ 2) * (t₁ - t₀) + M * (C₁ * ϑ) := by
  have hstep : ∀ k : Fin M, ℒ (W (k + 1)) ≤ ℒ (W k) - α k ^ 2 * (t₁ - t₀) + C₁ * ϑ := by
    intro k
    obtain ⟨r, ka, kb, p, r₁, U₀, S₀, V₀, Uh, Vh, K, Lf, Sh, P, σ, Q, U₁, S₁, V₁, hs, h0, h1, hα⟩ :=
      hup k
    have h := dlrt_descent_of_P1 hs (hP1 k) h01
    rw [← hα, ← h0] at h
    have hl0 : layerLoss ℒ (W k) k (W k k) = ℒ (W k) := by
      rw [layerLoss, Function.update_eq_self]
    rw [hl0] at h
    have hl1 : layerLoss ℒ (W k) k (U₁ * S₁ * V₁ᵀ) = ℒ (W (k + 1)) := by rw [h1, layerLoss]
    rwa [hl1] at h
  have hind : ∀ i ≤ M, ℒ (W i) ≤ ℒ (W 0) - (∑ k ∈ Finset.range i, α k ^ 2) * (t₁ - t₀)
      + i * (C₁ * ϑ) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have h1 := ih (Nat.le_of_succ_le hi)
      have h2 := hstep ⟨i, hi⟩
      simp only at h2
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  exact hind M le_rfl

end Layers

/-! ### Existence of steps -/

section Existence

variable {m n : Type*} [Fintype m] [Fintype n] {r p : ℕ} {ℒ : Matrix m n ℝ → ℝ} {C₁ C₂ : ℝ}

omit [Fintype m] [Fintype n] in
/-- Nothing is discarded at the full rank. -/
theorem svdTail_self (σ : Fin p → ℝ) : svdTail σ p = 0 := by
  simp [svdTail]

/-- **Non-vacuity: one rank-adaptive step of Algorithm 1 exists** (arXiv 2205.13571, Algorithm 1,
`adaptive = True`).  Under P1, for `2 r ≤ m`, `2 r ≤ n`, orthonormal `U₀`, `V₀`, every `S₀` and
every `ϑ ≥ 0`, the flows have solutions, the augmented bases and the SVD exist, and the smallest
rank `r₁` of the truncation rule exists. -/
theorem exists_isAdaptiveDLRTStep (hP1 : IsP1 ℒ C₁ C₂) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hrm : 2 * r ≤ Fintype.card m)
    (hrn : 2 * r ≤ Fintype.card n) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    ∃ (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (P : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ)
      (σ : Fin (2 * r) → ℝ) (Q : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (r₁ : ℕ)
      (U₁ : Matrix m (Fin r₁) ℝ) (S₁ : Matrix (Fin r₁) (Fin r₁) ℝ) (V₁ : Matrix n (Fin r₁) ℝ),
      IsAdaptiveDLRTStep ℒ ϑ t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sh P σ Q U₁ S₁ V₁ := by
  classical
  obtain ⟨Uh, Vh, K, Lf, Sh, hs⟩ := exists_isRankAdaptiveStep hP1.isLipschitzField
    hP1.isBoundedField (fun _ => continuous_const) h01 S₀ hU₀ hV₀ hrm hrn hϑ
  obtain ⟨P, σ, Q, hsvd⟩ := exists_isSVD_of_le (Sh t₁) (p := 2 * r) (Matrix.rank_le_width _)
    (by simp) (by simp)
  have hex : ∃ s, svdTail σ s ≤ ϑ := ⟨2 * r, by rw [svdTail_self]; exact hϑ⟩
  have hr₁ : Nat.find hex ≤ 2 * r := Nat.find_min' hex (by rw [svdTail_self]; exact hϑ)
  have hd := hP1.differentiable
  exact ⟨Uh, Vh, K, Lf, Sh, P, σ, Q, Nat.find hex, Uh * leadCols hr₁ P,
    Matrix.diagonal (leadVals hr₁ σ), Vh * leadCols hr₁ Q,
    { orthU₀ := hU₀
      orthV₀ := hV₀
      kSol := (kFlow_eq hd V₀).symm ▸ hs.kSol
      kStart := hs.kStart
      lSol := (lFlow_eq hd U₀).symm ▸ hs.lSol
      lStart := hs.lStart
      orthUh := hs.orthUa
      kCap := hs.kCap
      augU := hs.augU
      orthVh := hs.orthVa
      lCap := hs.lCap
      augV := hs.augV
      sSol := (sFlow_eq hd Uh Vh).symm ▸ hs.sSol
      sStart := hs.sStart
      svd := hsvd
      rankLe := hr₁
      tail := Nat.find_spec hex
      minimal := fun s hs' => not_le.1 (Nat.find_min hex hs')
      eqU := rfl
      eqS := rfl
      eqV := rfl }⟩

end Existence

/-! ### Linear losses -/

section LinearLoss

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The linear loss `ℒ(Z) = -⟪C, Z⟫`, with `F = -∇ℒ ≡ C`. -/
noncomputable def linLoss (C Z : Matrix m n ℝ) : ℝ := -⟪C, Z⟫

/-- The gradient of a linear loss is constant. -/
theorem hasGradientAt_linLoss (C Z : Matrix m n ℝ) : HasGradientAt (linLoss C) (-C) Z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (linLoss C) (-(innerSL ℝ C)) Z := (innerSL ℝ C).hasFDerivAt.neg
  have hEq : InnerProductSpace.toDual ℝ _ (-C) = -(innerSL ℝ C) := by
    ext v
    simp
  rw [hEq]
  exact h

/-- The gradient of `ℒ(Z) = -⟪C, Z⟫` is `-C`. -/
theorem gradient_linLoss (C : Matrix m n ℝ) : ∇ (linLoss C) = fun _ => -C :=
  funext fun Z => (hasGradientAt_linLoss C Z).gradient

/-- A linear loss satisfies P1 with `C₁ = ‖C‖` and every `C₂ ≥ 0`. -/
theorem isP1_linLoss (C : Matrix m n ℝ) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) : IsP1 (linLoss C) ‖C‖ C₂ where
  differentiable Z := (hasGradientAt_linLoss C Z).differentiableAt
  bounded Z := by simp [gradient_linLoss]
  lipschitz Z Z' := by simpa [gradient_linLoss] using mul_nonneg hC₂ (norm_nonneg _)

/-- The full flow of a linear loss is `F ≡ C`. -/
theorem gradField_linLoss (C : Matrix m n ℝ) (t : ℝ) (Z : Matrix m n ℝ) :
    gradField (linLoss C) t Z = C := by
  simp [gradField, gradient_linLoss]

/-- The K-step flow of a linear loss is the constant `C V`. -/
theorem kFlow_linLoss {k : Type*} [Fintype k] (C : Matrix m n ℝ) (V : Matrix n k ℝ) (t : ℝ)
    (X : Matrix m k ℝ) : kFlow (linLoss C) V t X = C * V := by
  rw [kFlow_eq (isP1_linLoss C le_rfl).differentiable, kField, gradField_linLoss]

/-- The L-step flow of a linear loss is the constant `Cᵀ U`. -/
theorem lFlow_linLoss {k : Type*} [Fintype k] (C : Matrix m n ℝ) (U : Matrix m k ℝ) (t : ℝ)
    (X : Matrix n k ℝ) : lFlow (linLoss C) U t X = Cᵀ * U := by
  rw [lFlow_eq (isP1_linLoss C le_rfl).differentiable, lField, gradField_linLoss]

/-- The S-step flow of a linear loss is the constant `Uᵀ C V`. -/
theorem sFlow_linLoss {k k' : Type*} [Fintype k] [Fintype k'] (C : Matrix m n ℝ)
    (U : Matrix m k ℝ) (V : Matrix n k' ℝ) (t : ℝ) (X : Matrix k k' ℝ) :
    sFlow (linLoss C) U V t X = Uᵀ * C * V := by
  rw [sFlow_eq (isP1_linLoss C le_rfl).differentiable, sField, gradField_linLoss]

/-- A linear loss satisfies P2 with `ε = ‖C‖` at every rank, near every matrix. -/
theorem isP2_linLoss (C W : Matrix m n ℝ) (r : ℕ) (ρ : ℝ) : IsP2 (linLoss C) W r ρ ‖C‖ := by
  classical
  intro U V S hU hV _ _
  rw [gradient_linLoss, one_sub_tangentProj_apply, neg_neg]
  exact norm_normal_le hU hV C

end LinearLoss

/-! ### The constants of Theorem 1 depend on the final time -/

section TimeDependence

/-- A solution `t ↦ (1 + t) c` of the constant field `c`. -/
private theorem odeSolution_one_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {c : E} (hf : ∀ t x, f t x = c) (a b : ℝ) :
    ODESolution f (fun t => (1 + t) • c) a b := by
  have h := odeSolution_of_const hf ((1 + a) • c) a b
  have he : (fun t => (1 + a) • c + (t - a) • c) = fun t : ℝ => (1 + t) • c := by
    funext t
    rw [← add_smul]
    congr 1
    ring
  rwa [he] at h

/-- The loss of the run: `ℒ(Z) = -tr Z`, so `F ≡ I`. -/
noncomputable def traceLoss : Matrix (Fin 2) (Fin 2) ℝ → ℝ := linLoss 1

/-- The K- and L-step of the run: `K(t) = (1 + t) e₁`. -/
noncomputable def runK (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := (1 + t) • unitCol

/-- The S-step of the run: `S(t) = 1 + t`. -/
noncomputable def runS (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := (1 + t) • 1

/-- The exact solution: `W(t) = e₁ e₁ᵀ + t I`. -/
noncomputable def runW (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := unitCol * unitColᵀ + t • 1

/-- One step of rank-adaptive Algorithm 1 of arXiv 2205.13571 for `ℒ(Z) = -tr Z` from
`Y₀ = (1 + a) e₁ e₁ᵀ`:
`[K(b) | U₀]` and `[L(b) | V₀]` both have range `span e₁`, so the rank stays `1` already for
`ϑ = 0`, although the exact solution has rank `2`. -/
theorem traceLoss_step {a b : ℝ} (hb : 0 ≤ b) :
    IsAdaptiveDLRTStep traceLoss 0 a b unitCol (runS a) unitCol unitCol unitCol runK runK runS 1
      (fun _ : Fin 1 => 1 + b) 1 unitCol (runS b) unitCol where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_one_add_smul (fun t x => by simp [traceLoss, kFlow_linLoss]) a b
  kStart := by simp [runK, runS, Matrix.mul_smul]
  lSol := odeSolution_one_add_smul (fun t x => by simp [traceLoss, lFlow_linLoss]) a b
  lStart := by simp [runK, runS, Matrix.mul_smul]
  orthUh := unitCol_orth
  kCap := kCap_of_qr unitCol_orth (R₁ := runS b) (by simp [runK, runS, Matrix.mul_smul])
  augU := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  orthVh := unitCol_orth
  lCap := kCap_of_qr unitCol_orth (R₁ := runS b) (by simp [runK, runS, Matrix.mul_smul])
  augV := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  sSol := odeSolution_one_add_smul
    (fun t x => by simp [traceLoss, sFlow_linLoss, unitCol_orth]) a b
  sStart := by simp [runS, unitCol_orth]
  svd :=
    { orthU := by simp
      orthV := by simp
      antitone := fun _ _ _ => le_rfl
      nonneg := fun _ => by positivity
      eq := by
        ext i j
        fin_cases i
        fin_cases j
        simp [runS] }
  rankLe := le_rfl
  tail := by simp [svdTail]
  minimal := fun s hs => by
    obtain rfl : s = 0 := by omega
    have h1 : (0 : ℝ) < 1 + b := by positivity
    simp [svdTail, Real.sqrt_sq h1.le, h1]
  eqU := by
    ext i j
    fin_cases j
    simp [leadCols, Matrix.mul_apply]
  eqS := by
    ext i j
    fin_cases i
    fin_cases j
    simp [runS, leadVals]
  eqV := by
    ext i j
    fin_cases j
    simp [leadCols, Matrix.mul_apply]

/-- The grid steps of the run of `traceLoss_step`, in the indexing of `dlrt_approximation`. -/
theorem traceLoss_grid_step {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    IsAdaptiveDLRTStep traceLoss 0 (0 + j * η) (0 + (j + 1) * η) unitCol (runS (j * η)) unitCol
      unitCol unitCol runK runK runS 1 (fun _ : Fin 1 => 1 + ((j + 1 : ℕ) : ℝ) * η) 1 unitCol
      (runS (((j + 1 : ℕ) : ℝ) * η)) unitCol := by
  have h := traceLoss_step (a := j * η) (b := ((j + 1 : ℕ) : ℝ) * η) (by positivity)
  have h1 : (0 : ℝ) + j * η = j * η := by ring
  have h2 : (0 : ℝ) + (j + 1) * η = ((j + 1 : ℕ) : ℝ) * η := by push_cast; ring
  rw [h1, h2]
  exact h

/-- `W(t) = e₁ e₁ᵀ + t I` solves the gradient flow of `ℒ(Z) = -tr Z`. -/
theorem runW_sol (T : ℝ) : ODESolution (gradField traceLoss) runW 0 T := by
  have h := odeSolution_of_const (f := gradField traceLoss) (c := 1)
    (fun t x => gradField_linLoss 1 t x) (unitCol * unitColᵀ) 0 T
  have he : (fun t : ℝ => unitCol * unitColᵀ + (t - 0) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      runW := by
    funext t
    simp [runW]
  rwa [he] at h

/-- The run starts on the exact solution. -/
theorem runW_zero : runW 0 = unitCol * runS 0 * unitColᵀ := by
  simp [runW, runS]

/-- The hypotheses of `dlrt_approximation` hold on the run of `traceLoss_step`, so Theorem 1 of
arXiv 2205.13571 is not vacuous.  Its bound holds on this run because the constants grow with the
final time `T`, see `dlrt_constants_depend_on_time`. -/
example {N : ℕ} {η T : ℝ} (hη : 0 < η) (hN : (N : ℝ) * η ≤ T) :
    ∀ j ≤ N, ‖unitCol * runS (j * η) * unitColᵀ - runW (0 + j * η)‖ ≤
      dlrtC₁ 0 η T * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
        + dlrtC₂ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 0 η T * η + dlrtC₃ 0 T * 0 / η :=
  dlrt_approximation (ℒ := traceLoss) (r := fun _ => 1) (ka := fun _ => 1)
    (kb := fun _ => 1) (p := fun _ => 1) (U := fun _ => unitCol) (S := fun j => runS (j * η))
    (V := fun _ => unitCol) (Uh := fun _ => unitCol) (Vh := fun _ => unitCol) (K := fun _ => runK)
    (Lf := fun _ => runK) (Sh := fun _ => runS) (P := fun _ => 1)
    (σ := fun j _ => 1 + (((j + 1 : ℕ) : ℝ)) * η) (Q := fun _ => 1) (ϑs := fun _ => 0)
    (ρ := 1 + (dlrtC₁ 0 η T * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      + dlrtC₂ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 0 η T * η + dlrtC₃ 0 T * 0 / η
        + 2 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ * η))
    (isP1_linLoss 1 le_rfl) le_rfl (norm_nonneg _) le_rfl hη le_rfl hN
    (W := runW) (runW_sol _) (fun _ _ => le_rfl) (fun j _ => traceLoss_grid_step hη.le j)
    (by simpa using runW_zero) (by linarith) fun _ _ => isP2_linLoss _ _ _ _

/-- The error of the run grows linearly in time: `N η ≤ ‖Y_N - W(N η)‖`. -/
theorem le_norm_run_error {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    (N : ℝ) * η ≤ ‖unitCol * runS (N * η) * unitColᵀ - runW (0 + N * η)‖ := by
  have h := Frobenius.abs_apply_le_norm
    (unitCol * runS (N * η) * unitColᵀ - runW (0 + N * η)) 1 1
  have he : (unitCol * runS (N * η) * unitColᵀ - runW (0 + N * η)) 1 1 = -((N : ℝ) * η) := by
    simp [runS, runW, Matrix.mul_apply, Matrix.smul_apply]
  rw [he, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) hη)] at h
  exact h

/-- **The claim of Theorem 1 of arXiv 2205.13571 that `c₁, c₂, c₃` depend only on `C₁`, `C₂` is
false.**  For every step size `η > 0` there is one infinite run of rank-adaptive Algorithm 1, with
`ℒ(Z) = -tr Z` on `2 × 2` matrices, fixed `C₁ = ε = ‖I‖`, `C₂ = 1`, `ϑ = 0`, which satisfies P1 and
P2, starts on the exact solution, and has unbounded error: for all `c₁, c₂, c₃` the bound of
Theorem 1 fails after finitely many steps.  The constants must depend on the final time, as in
`dlrt_approximation`.  The bases `[K(η) | U₀]`, `[L(η) | V₀]` do not see the second direction, so
even `ϑ = 0` keeps rank `1`, while `W(t)` has rank `2` for `t > 0`. -/
theorem dlrt_constants_depend_on_time {η : ℝ} (hη : 0 < η) :
    IsP1 traceLoss ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 ∧
    (∀ (X : Matrix (Fin 2) (Fin 2) ℝ) (ρ : ℝ),
      IsP2 traceLoss X 1 ρ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖) ∧
    (∀ T, ODESolution (gradField traceLoss) runW 0 T) ∧
    runW 0 = unitCol * runS 0 * unitColᵀ ∧
    (∀ j : ℕ, IsAdaptiveDLRTStep traceLoss 0 (0 + j * η) (0 + (j + 1) * η) unitCol (runS (j * η))
      unitCol unitCol unitCol runK runK runS 1 (fun _ : Fin 1 => 1 + ((j + 1 : ℕ) : ℝ) * η) 1
      unitCol (runS (((j + 1 : ℕ) : ℝ) * η)) unitCol) ∧
    ∀ c₁ c₂ c₃ : ℝ, ∃ N : ℕ, c₁ * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + c₂ * η + c₃ * 0 / η <
      ‖unitCol * runS (N * η) * unitColᵀ - runW (0 + N * η)‖ := by
  refine ⟨isP1_linLoss 1 zero_le_one, fun X ρ => isP2_linLoss 1 X 1 ρ, runW_sol, runW_zero,
    traceLoss_grid_step hη.le, fun c₁ c₂ c₃ => ?_⟩
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((c₁ * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ + c₂ * η + c₃ * 0 / η) / η)
  rw [div_lt_iff₀ hη] at hN
  exact ⟨N, hN.trans_le (le_norm_run_error hη.le N)⟩

end TimeDependence

/-! ### There is no uniform rate in Theorem 2 -/

section NoUniformRate

/-- **The rate in Theorem 2 of arXiv 2205.13571 cannot be a constant.**  For a loss bounded below,
such as a nonnegative training loss, no infinite sequence of weights satisfies
`ℒ(t + 1) ≤ ℒ(t) - α η + β ϑ` with constants such that `β ϑ < α η`: the loss would tend to
`-∞`.  So the printed statement, with `α > 0` independent of `t` and `ϑ = O(η²)`, fails for every
such loss on every infinite run with `η` small. -/
theorem dlrt_no_uniform_descent_of_bddBelow {E : Type*} {ℒ : E → ℝ} (hℒ : BddBelow (range ℒ))
    {α β η ϑ : ℝ} (hlt : β * ϑ < α * η) (Y : ℕ → E) :
    ¬ ∀ j, ℒ (Y (j + 1)) ≤ ℒ (Y j) - α * η + β * ϑ := by
  intro h
  obtain ⟨b, hb⟩ := hℒ
  have hd : 0 < α * η - β * ϑ := by linarith
  have hind : ∀ j : ℕ, ℒ (Y j) ≤ ℒ (Y 0) - j * (α * η - β * ϑ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := h j
      push_cast
      linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((ℒ (Y 0) - b) / (α * η - β * ϑ))
  have h1 := hind N
  have h2 : b ≤ ℒ (Y N) := hb ⟨Y N, rfl⟩
  rw [div_lt_iff₀ hd] at hN
  linarith

/-- A constant trajectory solves the zero field. -/
private theorem odeSolution_const_of_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} (hf : ∀ t x, f t x = 0) (c : E) (a b : ℝ) :
    ODESolution f (fun _ => c) a b := by
  simpa using odeSolution_of_const hf c a b

/-- The constant loss `ℒ ≡ 0` on `2 × 2` matrices. -/
noncomputable def zeroLoss : Matrix (Fin 2) (Fin 2) ℝ → ℝ := linLoss 0

/-- `zeroLoss` vanishes. -/
theorem zeroLoss_apply (Z : Matrix (Fin 2) (Fin 2) ℝ) : zeroLoss Z = 0 := by
  simp [zeroLoss, linLoss]

/-- A step of rank-adaptive Algorithm 1 of arXiv 2205.13571 for `ℒ ≡ 0`: nothing moves. -/
theorem zeroLoss_step (a b : ℝ) :
    IsAdaptiveDLRTStep zeroLoss 0 a b unitCol 1 unitCol unitCol unitCol (fun _ => unitCol)
      (fun _ => unitCol) (fun _ => 1) 1 (fun _ : Fin 1 => 1) 1 unitCol 1 unitCol where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_const_of_zero (fun t x => by simp [zeroLoss, kFlow_linLoss]) _ a b
  kStart := by simp
  lSol := odeSolution_const_of_zero (fun t x => by simp [zeroLoss, lFlow_linLoss]) _ a b
  lStart := by simp
  orthUh := unitCol_orth
  kCap := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  augU := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  orthVh := unitCol_orth
  lCap := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  augV := by rw [Matrix.mul_assoc, unitCol_orth, Matrix.mul_one]
  sSol := odeSolution_const_of_zero (fun t x => by simp [zeroLoss, sFlow_linLoss]) _ a b
  sStart := by simp [unitCol_orth]
  svd :=
    { orthU := by simp
      orthV := by simp
      antitone := fun _ _ _ => le_rfl
      nonneg := fun _ => zero_le_one
      eq := by
        ext i j
        fin_cases i
        fin_cases j
        simp }
  rankLe := le_rfl
  tail := by simp [svdTail]
  minimal := fun s hs => by
    obtain rfl : s = 0 := by omega
    simp [svdTail]
  eqU := by
    ext i j
    fin_cases j
    simp [leadCols, Matrix.mul_apply]
  eqS := by
    ext i j
    fin_cases i
    fin_cases j
    simp [leadVals]
  eqV := by
    ext i j
    fin_cases j
    simp [leadCols, Matrix.mul_apply]

/-- **Theorem 2 of arXiv 2205.13571 as printed is false**: it claims positive constants `α`, `β`
independent of `t`, `η`, `ϑ` with `ℒ(t + 1) ≤ ℒ(t) - α η + β ϑ`.  For the loss `ℒ ≡ 0`, which
satisfies P1, and `ϑ = 0`, this fails for all `α > 0`, `β` and every step size `η > 0`, on a genuine
step of Algorithm 1.  The correct rate is the step-dependent `α²` of `dlrt_descent`. -/
theorem dlrt_no_uniform_descent {α β η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    IsP1 zeroLoss 1 1 ∧
    IsAdaptiveDLRTStep zeroLoss 0 0 η unitCol 1 unitCol unitCol unitCol (fun _ => unitCol)
      (fun _ => unitCol) (fun _ => 1) 1 (fun _ : Fin 1 => 1) 1 unitCol 1 unitCol ∧
    ¬ zeroLoss (unitCol * (1 : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ) ≤
      zeroLoss (unitCol * (1 : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ) - α * η + β * 0 := by
  have hP1 : IsP1 zeroLoss ‖(0 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 := isP1_linLoss 0 zero_le_one
  refine ⟨⟨hP1.differentiable, fun Z => (hP1.bounded Z).trans (by simp), hP1.lipschitz⟩,
    zeroLoss_step 0 η, ?_⟩
  have h := mul_pos hα hη
  simp only [zeroLoss_apply]
  linarith

end NoUniformRate

/-! ### Theorem 2 fails without augmentation -/

section FixedRank

/-- The gradient flow of the fixed-rank example, `F ≡ C`. -/
noncomputable def ceC : Matrix (Fin 2) (Fin 2) ℝ := !![3, 3; 3, -40 / 3]

/-- The new basis of the fixed-rank example, `u = (4, 3)ᵀ / 5`. -/
noncomputable def ceU : Matrix (Fin 2) (Fin 1) ℝ := !![4 / 5; 3 / 5]

/-- The K- and L-step of the fixed-rank example, `K(t) = η e₁ + t C e₁`. -/
noncomputable def ceK (η t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  unitCol * (η • (1 : Matrix (Fin 1) (Fin 1) ℝ)) + (t - 0) • (ceC * unitCol)

/-- The S-step of the fixed-rank example: `S(t) = 16 η / 25`, since `uᵀ C u = 0`. -/
noncomputable def ceS (η t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  ((16 / 25 * η) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) + (t - 0) • (ceUᵀ * ceC * ceU)

/-- `u` is a unit vector. -/
theorem ceU_orth : ceUᵀ * ceU = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [ceU, Matrix.mul_apply]
  norm_num

/-- The S-step of the fixed-rank example does not move: `uᵀ C u = 0`. -/
theorem ceU_C_ceU : ceUᵀ * ceC * ceU = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [ceU, ceC, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- `C` is symmetric, so the K- and L-step of the fixed-rank example coincide. -/
theorem ceC_transpose : ceCᵀ = ceC := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ceC]

/-- The K-step ends in the span of `u`: `K(η) = 5 η u`. -/
theorem ceK_end (η : ℝ) : ceK η η = ceU * ((5 * η) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  ext i j
  fin_cases j
  fin_cases i <;> simp [ceK, ceU, ceC, Matrix.mul_apply, Matrix.vecMul, dotProduct] <;> ring

/-- One exact step of the fixed-rank Algorithm 1 of arXiv 2205.13571 for the linear loss
`ℒ(Z) = -⟪C, Z⟫`, from
`Y₀ = η e₁ e₁ᵀ`, with bases `U₁ = V₁ = u`. -/
theorem ceStep (η : ℝ) :
    IsDLRTStep (linLoss ceC) 0 η unitCol (η • 1) unitCol ceU ceU (ceK η) (ceK η) (ceS η) where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_of_const (fun t x => kFlow_linLoss ceC unitCol t x) _ 0 η
  kStart := by simp [ceK]
  lSol := odeSolution_of_const
    (fun t x => (lFlow_linLoss ceC unitCol t x).trans (by rw [ceC_transpose])) _ 0 η
  lStart := by simp [ceK, Matrix.transpose_smul]
  orthU₁ := ceU_orth
  kCap := kCap_of_qr ceU_orth (ceK_end η)
  orthV₁ := ceU_orth
  lCap := kCap_of_qr ceU_orth (ceK_end η)
  sSol := by
    have h := odeSolution_of_const (f := sFlow (linLoss ceC) ceU ceU) (c := ceUᵀ * ceC * ceU)
      (fun t x => sFlow_linLoss ceC ceU ceU t x) ((16 / 25 * η) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      0 η
    exact h
  sStart := by
    ext i j
    fin_cases i
    fin_cases j
    simp [ceS, ceU, Matrix.mul_apply]
    ring

/-- The loss after the fixed-rank step of `ceStep`: `ℒ(Y₁) = ℒ(Y₀) + 3 η`. -/
theorem ceStep_loss (η : ℝ) :
    linLoss ceC (ceU * ceS η η * ceUᵀ) =
      linLoss ceC (unitCol * (η • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ) + 3 * η := by
  simp [linLoss, Frobenius.inner_def, ceS, ceC, ceU, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]
  ring

/-- **Theorem 2 of arXiv 2205.13571 fails for `adaptive = False`.**  The main-text statement
refers to Algorithm 1 without excluding `adaptive = False`; the appendix proves it only for the
rank-adaptive algorithm, and the proof uses `Ŷ₀ = Y₀`, which needs the augmentation of the bases.
For the fixed linear loss `ℒ(Z) = -⟪C, Z⟫`, which satisfies P1 with constants independent of `η`,
and every step size `η > 0`, one exact fixed-rank step from `Y₀ = η e₁ e₁ᵀ` strictly increases the
loss, by `3 η` (`ceStep_loss`), so no threshold for `η` depending only on `C₁`, `C₂` helps.  The
reason is the Galerkin start `U₁ U₁ᵀ Y₀ V₁ V₁ᵀ ≠ Y₀`. -/
theorem fixedRank_loss_increases {η : ℝ} (hη : 0 < η) :
    IsP1 (linLoss ceC) ‖ceC‖ 1 ∧
    IsDLRTStep (linLoss ceC) 0 η unitCol (η • 1) unitCol ceU ceU (ceK η) (ceK η) (ceS η) ∧
    linLoss ceC (unitCol * (η • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ) <
      linLoss ceC (ceU * ceS η η * ceUᵀ) := by
  refine ⟨isP1_linLoss ceC zero_le_one, ceStep η, ?_⟩
  rw [ceStep_loss]
  linarith

end FixedRank

end LeanDLRA.Literature.P2205_13571
