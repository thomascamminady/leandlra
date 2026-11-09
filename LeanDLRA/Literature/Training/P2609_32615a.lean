import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.KyFan
import LeanDLRA.Classical.SVD
import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Results of arXiv 2609.32615: Stabilizing the Dynamic Low-Rank Training (SDLRT)

This module formalizes the algorithm and the three theorems of the paper for real `m × n` matrices
with the Frobenius norm and an arbitrary Lipschitz field `F` (`F = -∇L` for training); nothing of
them is left out, except that the paper's strict gain `γ < 1` is refuted instead of proved.
**Algorithm** (§3.3): `State`, `next`, `IsSDLRTData`, `IsSDLRTStep` model the K- and L-steps, the QR
bases of the compensated matrices `(K₁, U, U_neg)`, `(L₁, V, V_neg)` (extra orthonormal columns
allowed), the Galerkin S-step, the thin SVD, the rank selection with `ϑ = τ ‖Ŝ‖_F`, the buffer of
the next `r₁` directions (`next_orthUn`, `next_cross`) and the negative feedback on `τ`
(`next_tau_mem`); `IsSDLRTData.toRankAdaptive` shows that a step is a rank-adaptive BUG step, and
`exists_isSDLRTStep`, `exists_sdlrt_run` that steps and runs exist. **Thm 3.2** (exactness) is
`IsSDLRTData.exact`, `IsSDLRTData.exact_of_isUnit` for one step, truncation included, and
`sdlrt_exact_run` for a training period, with instance `exact_example`; the invertibility of `U(t₁)ᵀ
U₀` must be assumed besides that of `V(t₁)ᵀ V₀` (the paper's "identical argument"). **Thm 3.3 /
C.1** (error bound) is `sdlrt_error_bound` with `γ = 1` and constants depending only on `L`, `B`,
`T`, and `sdlrt_error_bound_feedback`, where the tolerances of the feedback rule are bounded rather
than assumed; (A2) is `FactoredNormalBound` at the ranks of the iterates, on all matrices instead of
an unspecified neighbourhood. **False claim**: the contraction (26) with `γ ∈ (0, 1)` and the gain
`E_DLRT - E_SDLRT = (1 - γ) c₁ ε > 0` fail. `compensation_no_contraction` shows that (26) fails for
every `γ < 1` on a concrete step, and `sdlrt_worse_than_dlrt` that on the same step, under (A1)–(A3)
and for every tolerance factor `τ ≤ 1/2`, the buffer raises the actual error from `1` to `√2`; the
displayed inequality with a free constant holds only because `c₁ / γ` can replace `c₁`, so `γ`
carries no information. **Thm 3.1** (flow of the best rank-`r` approximation) is `bestApprox_flow`,
`hasDerivAt_truncation`, the uniqueness statement `flow_of_constraints` and the coefficient form
`flowU_eq_of_complete`, for a partitioned SVD with `τⱼ < σᵢ` (`IsPartitionedSVD`), which exists
under any singular value gap (`exists_partitionedSVD`). The paper assumes differentiable factors;
here they are constructed: the implicit function theorem applied to a Riccati system gives invariant
frames (`exists_riccati_branch`), `exists_orth_factor` orthonormalizes them without changing their
derivative, and `isBestApprox_of_bounds`, `eq_of_isBestApprox` show that the block of the large
singular values is the unique best approximation near `t₀`. The paper's gauge with `S = Σ_r` holds
only at the single time `t₀`, and its expansion `U̇ = U⊥ C` needs `U Uᵀ + U⊥ U⊥ᵀ = I` although (18)
does not. The stabilizing effect of the feedback rule on the rank is not a theorem of the paper and
is not addressed.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace LeanDLRA.Literature.P2609_32615

open LeanDLRA LeanDLRA.MatrixBUG Matrix

/-! ### The SDLRT algorithm -/

section Algorithm

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The state of SDLRT (arXiv 2609.32615, §3.3) between two steps: the current rank `r`, the
factors `U`, `S`, `V`, the compensation buffer `(Un, Vn) = (U_neg, V_neg)` with `b` columns, and
the tolerance factor `τ`. -/
structure State (m n : Type*) where
  /-- The current rank. -/
  r : ℕ
  /-- The number of buffer columns. -/
  b : ℕ
  /-- The left factor. -/
  U : Matrix m (Fin r) ℝ
  /-- The small factor. -/
  S : Matrix (Fin r) (Fin r) ℝ
  /-- The right factor. -/
  V : Matrix n (Fin r) ℝ
  /-- The left compensation buffer `U_neg`. -/
  Un : Matrix m (Fin b) ℝ
  /-- The right compensation buffer `V_neg`. -/
  Vn : Matrix n (Fin b) ℝ
  /-- The tolerance factor `τ`. -/
  τ : ℝ

/-- The low-rank weight `W = U S Vᵀ` represented by a state. -/
def State.Y (x : State m n) : Matrix m n ℝ := x.U * x.S * x.Vᵀ

/-! The squared Frobenius mass `∑_{i ≥ r} sᵢ²` of the singular values beyond rank `r` is the core
`tailSqSum s r` (the local `tailSq` of an earlier version of this file was the same definition,
unification batch C3). -/

/-- Step 5 of SDLRT, rank selection: `r₁` is the smallest rank whose discarded tail is at most
the tolerance `ϑ` in Frobenius norm (the rule of Ceruti–Kusch–Lubich, arXiv 2104.05247, eq. (6),
which arXiv 2609.32615, proof of Thm C.1, step 5, uses). -/
structure IsTruncRank {q : ℕ} (s : Fin q → ℝ) (ϑ : ℝ) (r₁ : ℕ) : Prop where
  le : r₁ ≤ q
  tail : √(tailSqSum s r₁) ≤ ϑ
  min : ∀ r' < r₁, ϑ < √(tailSqSum s r')

/-- The number `min(2 r₁, r_max) - r₁` of buffer columns kept by step 5. -/
def bufSize (r₁ q : ℕ) : ℕ := min (2 * r₁) q - r₁

/-- The indices `r₁ ≤ i < min(2 r₁, r_max)` of the next `r₁` singular directions. -/
def bufIdx {r₁ q : ℕ} (i : Fin (bufSize r₁ q)) : Fin q :=
  ⟨r₁ + i, by have := i.2; unfold bufSize at this; omega⟩

/-- Steps 5 and 6 of SDLRT: from the augmented bases `Û`, `V̂` and the thin SVD `P diag(s) Qᵀ` of
the Galerkin result, keep the first `r₁` singular triplets, store the next `r₁` (at most) in the
buffer, and apply the negative feedback `τ ↦ ω τ` if `r₁ < r₀`. -/
noncomputable def next (ω : ℝ) (r₀ : ℕ) (τ : ℝ) {k k' q : ℕ} (Ua : Matrix m (Fin k) ℝ)
    (Va : Matrix n (Fin k') ℝ) (P : Matrix (Fin k) (Fin q) ℝ) (s : Fin q → ℝ)
    (Q : Matrix (Fin k') (Fin q) ℝ) {r₁ : ℕ} (h : r₁ ≤ q) : State m n where
  r := r₁
  b := bufSize r₁ q
  U := Ua * P.submatrix id (Fin.castLE h)
  S := diagonal fun i => s (Fin.castLE h i)
  V := Va * Q.submatrix id (Fin.castLE h)
  Un := Ua * P.submatrix id bufIdx
  Vn := Va * Q.submatrix id bufIdx
  τ := if r₁ < r₀ then ω * τ else τ

/-- Steps 1–5 of one SDLRT step (arXiv 2609.32615, §3.3) from `(t₀, x)` to `t₁`, with the field
`F(t, Y)` (`F = -∇L` for training):

1. K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`,
   `L(t₀) = V₀ S₀ᵀ`;
2.–3. `Û`, `V̂` have orthonormal columns whose range contains the compensated matrices
   `(K(t₁), U₀, U_neg)`, `(L(t₁), V₀, V_neg)` (a QR factorization; extra orthonormal columns are
   allowed, as a QR factor of a rank-deficient matrix has them);
4. Galerkin S-step `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂`, `Ŝ(t₀) = Ûᵀ W_prev V̂`, `W_prev = U₀ S₀ V₀ᵀ`;
5. thin SVD `Ŝ(t₁) = P diag(s) Qᵀ` with `s₀ ≥ s₁ ≥ ⋯ > 0` (so `q = r_max` is the rank of
   `Ŝ(t₁)`), and `r₁` selected by the tolerance `ϑ = τ ‖Ŝ(t₁)‖_F`. -/
structure IsSDLRTData (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (x : State m n)
    {k k' q : ℕ} (Ua : Matrix m (Fin k) ℝ) (Va : Matrix n (Fin k') ℝ)
    (K : ℝ → Matrix m (Fin x.r) ℝ) (Lf : ℝ → Matrix n (Fin x.r) ℝ)
    (Sa : ℝ → Matrix (Fin k) (Fin k') ℝ) (P : Matrix (Fin k) (Fin q) ℝ) (s : Fin q → ℝ)
    (Q : Matrix (Fin k') (Fin q) ℝ) (r₁ : ℕ) : Prop where
  orthU₀ : x.Uᵀ * x.U = 1
  orthV₀ : x.Vᵀ * x.V = 1
  kSol : ODESolution (kField x.V F) K t₀ t₁
  kStart : K t₀ = x.U * x.S
  lSol : ODESolution (lField x.U F) Lf t₀ t₁
  lStart : Lf t₀ = x.V * x.Sᵀ
  orthUa : Uaᵀ * Ua = 1
  capU : Ua * Uaᵀ * fromCols (fromCols (K t₁) x.U) x.Un = fromCols (fromCols (K t₁) x.U) x.Un
  orthVa : Vaᵀ * Va = 1
  capV : Va * Vaᵀ * fromCols (fromCols (Lf t₁) x.V) x.Vn = fromCols (fromCols (Lf t₁) x.V) x.Vn
  sSol : ODESolution (sField Ua Va F) Sa t₀ t₁
  sStart : Sa t₀ = Uaᵀ * x.Y * Va
  orthP : Pᵀ * P = 1
  orthQ : Qᵀ * Q = 1
  anti : Antitone s
  pos : ∀ i, 0 < s i
  svd : Sa t₁ = P * diagonal s * Qᵀ
  rank : IsTruncRank s (x.τ * ‖Sa t₁‖) r₁

/-- One step of SDLRT from `(t₀, x)` to `(t₁, y)`, whose truncation tolerance `τ ‖Ŝ(t₁)‖_F` is at
most `ϑ`. -/
def IsSDLRTStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (ω : ℝ) (r₀ : ℕ) (ϑ t₀ t₁ : ℝ)
    (x y : State m n) : Prop :=
  ∃ (k k' q r₁ : ℕ) (Ua : Matrix m (Fin k) ℝ) (Va : Matrix n (Fin k') ℝ)
    (K : ℝ → Matrix m (Fin x.r) ℝ) (Lf : ℝ → Matrix n (Fin x.r) ℝ)
    (Sa : ℝ → Matrix (Fin k) (Fin k') ℝ) (P : Matrix (Fin k) (Fin q) ℝ) (s : Fin q → ℝ)
    (Q : Matrix (Fin k') (Fin q) ℝ) (h : r₁ ≤ q),
    IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁ ∧ x.τ * ‖Sa t₁‖ ≤ ϑ ∧
      y = next ω r₀ x.τ Ua Va P s Q h

end Algorithm

section Truncation

variable {k k' : Type*} [Fintype k] [Fintype k'] {q : ℕ}

omit [Fintype k] [Fintype k'] in
/-- The squared Frobenius norm of a diagonal matrix. -/
lemma sq_norm_diagonal (d : Fin q → ℝ) : ‖(diagonal d : Matrix (Fin q) (Fin q) ℝ)‖ ^ 2 =
    ∑ i, d i ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [diagonal_apply_ne _ (Ne.symm hj)]
  · simp

omit [Fintype k] [Fintype k'] in
/-- The discarded part of a thin SVD. -/
lemma svd_sub_truncated (P : Matrix k (Fin q) ℝ) (s : Fin q → ℝ) (Q : Matrix k' (Fin q) ℝ)
    {r₁ : ℕ} (h : r₁ ≤ q) :
    P * diagonal s * Qᵀ - P.submatrix id (Fin.castLE h) *
        diagonal (fun i => s (Fin.castLE h i)) * (Q.submatrix id (Fin.castLE h))ᵀ =
      P * diagonal (fun i : Fin q => if r₁ ≤ (i : ℕ) then s i else 0) * Qᵀ := by
  ext a b
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [KyFan.sum_castLE_eq_sum_filter h (fun i => P a i * s i * Q b i),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin q => (i : ℕ) < r₁)
      (fun i => P a i * s i * Q b i),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin q => (i : ℕ) < r₁)
      (fun i => P a i * (if r₁ ≤ (i : ℕ) then s i else 0) * Q b i)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin q => (i : ℕ) < r₁),
      P a i * (if r₁ ≤ (i : ℕ) then s i else 0) * Q b i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have := (Finset.mem_filter.mp hi).2
    simp [not_le.mpr this]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin q => ¬ (i : ℕ) < r₁),
      P a i * (if r₁ ≤ (i : ℕ) then s i else 0) * Q b i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin q => ¬ (i : ℕ) < r₁), P a i * s i * Q b i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (Finset.mem_filter.mp hi).2
    simp [not_lt.mp this]
  rw [h1, h2]
  ring

/-- The truncation error of a thin SVD is the singular-value tail. -/
lemma norm_truncated_sub_svd {P : Matrix k (Fin q) ℝ} {Q : Matrix k' (Fin q) ℝ} (hP : Pᵀ * P = 1)
    (hQ : Qᵀ * Q = 1) (s : Fin q → ℝ) {r₁ : ℕ} (h : r₁ ≤ q) :
    ‖P.submatrix id (Fin.castLE h) * diagonal (fun i => s (Fin.castLE h i)) *
        (Q.submatrix id (Fin.castLE h))ᵀ - P * diagonal s * Qᵀ‖ = √(tailSqSum s r₁) := by
  rw [norm_sub_rev, svd_sub_truncated, Frobenius.norm_mul_transpose_of_orthonormal hQ,
    Frobenius.norm_mul_of_orthonormal hP, ← Real.sqrt_sq (norm_nonneg _), sq_norm_diagonal]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- The tail beyond the full length vanishes. -/
lemma tailSq_self (s : Fin q → ℝ) : tailSqSum s q = 0 :=
  tailSqSum_of_le s le_rfl

/-- The kept singular values carry no more energy than all of them. -/
lemma sum_castLE_sq_le (s : Fin q → ℝ) {r₁ : ℕ} (h : r₁ ≤ q) :
    ∑ i : Fin r₁, s (Fin.castLE h i) ^ 2 ≤ ∑ i, s i ^ 2 := by
  rw [KyFan.sum_castLE_eq_sum_filter h (fun i => s i ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun i _ _ => sq_nonneg (s i)

omit [Fintype k] [Fintype k'] in
/-- `(P_f)ᵀ P_g = (Pᵀ P)_{f g}` for column selections. -/
lemma transpose_submatrix_mul_submatrix [Fintype k] {a b : Type*} (P : Matrix k (Fin q) ℝ)
    (f : a → Fin q) (g : b → Fin q) :
    (P.submatrix id f)ᵀ * P.submatrix id g = (Pᵀ * P).submatrix f g := by
  ext i j
  simp [Matrix.mul_apply]

end Truncation

section Step

variable {m n : Type*} [Fintype m] [Fintype n] {ω : ℝ} {r₀ : ℕ} {τ : ℝ} {k k' q r₁ : ℕ}
  {Ua : Matrix m (Fin k) ℝ} {Va : Matrix n (Fin k') ℝ} {P : Matrix (Fin k) (Fin q) ℝ}
  {s : Fin q → ℝ} {Q : Matrix (Fin k') (Fin q) ℝ}

/-- The low-rank weight of the new state: `U₁ S₁ V₁ᵀ = Û P_{r₁} Σ_{r₁} Q_{r₁}ᵀ V̂ᵀ`. -/
lemma next_Y (h : r₁ ≤ q) : (next ω r₀ τ Ua Va P s Q h).Y =
    Ua * (P.submatrix id (Fin.castLE h) * diagonal (fun i => s (Fin.castLE h i)) *
      (Q.submatrix id (Fin.castLE h))ᵀ) * Vaᵀ := by
  change (Ua * P.submatrix id (Fin.castLE h)) * diagonal (fun i => s (Fin.castLE h i)) *
    (Va * Q.submatrix id (Fin.castLE h))ᵀ = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- `(Û P_f)ᵀ (Û P_g) = (Pᵀ P)_{f g}`. -/
lemma transpose_mul_mul_submatrix {a b : Type*} (hUa : Uaᵀ * Ua = 1) (f : a → Fin q)
    (g : b → Fin q) :
    (Ua * P.submatrix id f)ᵀ * (Ua * P.submatrix id g) = (Pᵀ * P).submatrix f g := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uaᵀ, hUa, Matrix.one_mul,
    transpose_submatrix_mul_submatrix]

/-- The new left factor has orthonormal columns.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem next_orthU (hUa : Uaᵀ * Ua = 1) (hP : Pᵀ * P = 1) (h : r₁ ≤ q) :
    (next ω r₀ τ Ua Va P s Q h).Uᵀ * (next ω r₀ τ Ua Va P s Q h).U = 1 := by
  change (Ua * P.submatrix id (Fin.castLE h))ᵀ * (Ua * P.submatrix id (Fin.castLE h)) = 1
  rw [transpose_mul_mul_submatrix hUa, hP]
  exact Matrix.submatrix_one _ (Fin.castLE_injective h)

/-- The new right factor has orthonormal columns.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem next_orthV (hVa : Vaᵀ * Va = 1) (hQ : Qᵀ * Q = 1) (h : r₁ ≤ q) :
    (next ω r₀ τ Ua Va P s Q h).Vᵀ * (next ω r₀ τ Ua Va P s Q h).V = 1 := by
  change (Va * Q.submatrix id (Fin.castLE h))ᵀ * (Va * Q.submatrix id (Fin.castLE h)) = 1
  rw [transpose_mul_mul_submatrix hVa, hQ]
  exact Matrix.submatrix_one _ (Fin.castLE_injective h)

/-- The left buffer has orthonormal columns.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem next_orthUn (hUa : Uaᵀ * Ua = 1) (hP : Pᵀ * P = 1) (h : r₁ ≤ q) :
    (next ω r₀ τ Ua Va P s Q h).Unᵀ * (next ω r₀ τ Ua Va P s Q h).Un = 1 := by
  change (Ua * P.submatrix id bufIdx)ᵀ * (Ua * P.submatrix id bufIdx) = 1
  rw [transpose_mul_mul_submatrix hUa, hP]
  refine Matrix.submatrix_one _ fun i j hij => ?_
  have : (i : ℕ) = j := by simpa [bufIdx, Fin.ext_iff] using hij
  exact Fin.ext this

/-- The left buffer is orthogonal to the new left factor: it stores discarded directions.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem next_cross (hUa : Uaᵀ * Ua = 1) (hP : Pᵀ * P = 1) (h : r₁ ≤ q) :
    (next ω r₀ τ Ua Va P s Q h).Uᵀ * (next ω r₀ τ Ua Va P s Q h).Un = 0 := by
  change (Ua * P.submatrix id (Fin.castLE h))ᵀ * (Ua * P.submatrix id bufIdx) = 0
  rw [transpose_mul_mul_submatrix hUa, hP]
  ext i j
  have hij : Fin.castLE h i ≠ bufIdx j := by
    intro he
    have : (i : ℕ) = r₁ + j := by simpa [bufIdx, Fin.ext_iff] using he
    have := i.2
    omega
  simp [Matrix.one_apply_ne hij]

/-- The negative feedback never increases `τ` and keeps it nonnegative.
(arXiv 2609.32615, §3.3, step 6.) -/
theorem next_tau_mem (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1) (hτ : 0 ≤ τ) (h : r₁ ≤ q) :
    0 ≤ (next ω r₀ τ Ua Va P s Q h).τ ∧ (next ω r₀ τ Ua Va P s Q h).τ ≤ τ := by
  simp only [next]
  split_ifs
  · exact ⟨mul_nonneg hω₀ hτ, mul_le_of_le_one_left hτ hω₁⟩
  · exact ⟨hτ, le_rfl⟩

/-- The energy of the new low-rank weight is at most that of the Galerkin result.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem norm_next_Y_le (hUa : Uaᵀ * Ua = 1) (hVa : Vaᵀ * Va = 1) (hP : Pᵀ * P = 1)
    (hQ : Qᵀ * Q = 1) (h : r₁ ≤ q) :
    ‖(next ω r₀ τ Ua Va P s Q h).Y‖ ≤ ‖Ua * (P * diagonal s * Qᵀ) * Vaᵀ‖ := by
  have hk : (P.submatrix id (Fin.castLE h))ᵀ * P.submatrix id (Fin.castLE h) = 1 := by
    rw [transpose_submatrix_mul_submatrix, hP]
    exact Matrix.submatrix_one _ (Fin.castLE_injective h)
  have hl : (Q.submatrix id (Fin.castLE h))ᵀ * Q.submatrix id (Fin.castLE h) = 1 := by
    rw [transpose_submatrix_mul_submatrix, hQ]
    exact Matrix.submatrix_one _ (Fin.castLE_injective h)
  rw [next_Y, Frobenius.norm_mul_transpose_of_orthonormal hVa,
    Frobenius.norm_mul_of_orthonormal hUa, Frobenius.norm_mul_transpose_of_orthonormal hVa,
    Frobenius.norm_mul_of_orthonormal hUa, Frobenius.norm_mul_transpose_of_orthonormal hl,
    Frobenius.norm_mul_of_orthonormal hk, Frobenius.norm_mul_transpose_of_orthonormal hQ,
    Frobenius.norm_mul_of_orthonormal hP]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [sq_norm_diagonal, sq_norm_diagonal]
  exact sum_castLE_sq_le s h

namespace IsSDLRTData

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {x : State m n}
  {K : ℝ → Matrix m (Fin x.r) ℝ} {Lf : ℝ → Matrix n (Fin x.r) ℝ}
  {Sa : ℝ → Matrix (Fin k) (Fin k') ℝ}

/-- `Û` captures `K(t₁)`. -/
lemma capK (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Ua * Uaᵀ * K t₁ = K t₁ :=
  (Exactness.capture_fromCols.mp (Exactness.capture_fromCols.mp hs.capU).1).1

/-- `Û` captures `U₀`. -/
lemma augU (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Ua * Uaᵀ * x.U = x.U :=
  (Exactness.capture_fromCols.mp (Exactness.capture_fromCols.mp hs.capU).1).2

/-- `Û` captures the buffer `U_neg`. -/
lemma capUn (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Ua * Uaᵀ * x.Un = x.Un :=
  (Exactness.capture_fromCols.mp hs.capU).2

/-- `V̂` captures `L(t₁)`. -/
lemma capL (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Va * Vaᵀ * Lf t₁ = Lf t₁ :=
  (Exactness.capture_fromCols.mp (Exactness.capture_fromCols.mp hs.capV).1).1

/-- `V̂` captures `V₀`. -/
lemma augV (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Va * Vaᵀ * x.V = x.V :=
  (Exactness.capture_fromCols.mp (Exactness.capture_fromCols.mp hs.capV).1).2

/-- `V̂` captures the buffer `V_neg`. -/
lemma capVn (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) : Va * Vaᵀ * x.Vn = x.Vn :=
  (Exactness.capture_fromCols.mp hs.capV).2

/-- The truncation error of step 5 is at most the tolerance `τ ‖Ŝ(t₁)‖_F`. -/
lemma trunc_le (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) (h : r₁ ≤ q) :
    ‖(next ω r₀ x.τ Ua Va P s Q h).Y - Ua * Sa t₁ * Vaᵀ‖ ≤ x.τ * ‖Sa t₁‖ := by
  rw [next_Y]
  have h1 := norm_truncated_sub_svd hs.orthP hs.orthQ s h
  rw [← hs.svd] at h1
  exact trunc_of_coeff hs.orthUa hs.orthVa (h1.le.trans hs.rank.tail)

/-- **SDLRT is a rank-adaptive BUG step** (arXiv 2609.32615, §3.3): the K- and L-steps, the
augmented bases (which the buffer enlarges), the Galerkin S-step and the truncation to
`τ ‖Ŝ(t₁)‖_F` form a step `IsRankAdaptiveStep` of the matrix rank-adaptive BUG integrator, so
that its whole error analysis applies verbatim. -/
theorem toRankAdaptive (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) (h : r₁ ≤ q) :
    IsRankAdaptiveStep F (x.τ * ‖Sa t₁‖) t₀ t₁ x.U x.S x.V Ua Va K Lf Sa
      (next ω r₀ x.τ Ua Va P s Q h).Y where
  orthU₀ := hs.orthU₀
  orthV₀ := hs.orthV₀
  kSol := hs.kSol
  kStart := hs.kStart
  lSol := hs.lSol
  lStart := hs.lStart
  orthUa := hs.orthUa
  kCap := hs.capK
  augU := hs.augU
  orthVa := hs.orthVa
  lCap := hs.capL
  augV := hs.augV
  sSol := hs.sSol
  sStart := by rw [hs.sStart, State.Y]; simp only [Matrix.mul_assoc]
  trunc := hs.trunc_le h

/-- The Galerkin step adds at most `(t₁ - t₀) B` of energy.
(arXiv 2609.32615, §3.3, step 4.) -/
theorem norm_Sa_le (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) {B : ℝ}
    (hB : IsBoundedField F B) (ht : t₀ ≤ t₁) : ‖Sa t₁‖ ≤ ‖x.Y‖ + (t₁ - t₀) * B := by
  have hbd : ∀ t ∈ Ico t₀ t₁, ‖sField Ua Va F t (Sa t)‖ ≤ B := fun t _ => by
    refine ((norm_mul_le_of_orthonormal hs.orthVa _).trans
      (norm_transpose_mul_le hs.orthUa _)).trans (hB t _)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hs.sSol.cont hs.sSol.deriv hbd t₁
    ⟨ht, le_rfl⟩
  have h0 : ‖Sa t₀‖ ≤ ‖x.Y‖ := by
    rw [hs.sStart]
    exact (norm_mul_le_of_orthonormal hs.orthVa _).trans (norm_transpose_mul_le hs.orthUa _)
  have h1 := norm_le_norm_add_norm_sub' (Sa t₁) (Sa t₀)
  linarith [mul_comm (t₁ - t₀) B]

/-- The energy of the iterates grows by at most `(t₁ - t₀) B` per step.
(arXiv 2609.32615, §3.3, steps 4–5.) -/
theorem norm_next_Y_le' (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) {B : ℝ}
    (hB : IsBoundedField F B) (ht : t₀ ≤ t₁) (h : r₁ ≤ q) :
    ‖(next ω r₀ x.τ Ua Va P s Q h).Y‖ ≤ ‖x.Y‖ + (t₁ - t₀) * B := by
  refine (norm_next_Y_le hs.orthUa hs.orthVa hs.orthP hs.orthQ h).trans ?_
  rw [← hs.svd, Frobenius.norm_mul_transpose_of_orthonormal hs.orthVa,
    Frobenius.norm_mul_of_orthonormal hs.orthUa]
  exact hs.norm_Sa_le hB ht

end IsSDLRTData

end Step

/-! ### Theorem 3.2 (exactness) -/

section Exact

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- If `B` has rank `≤ r₁ < r ≤ card n`, then `σ_{r-1}(A) ≤ ‖A - B‖_F` (Eckart–Young). -/
lemma singularValues_le_norm_sub (A B : Matrix m n ℝ) {r₁ r : ℕ} (hB : B.rank ≤ r₁) (h : r₁ < r)
    (hr : r ≤ Fintype.card n) : (toEuclideanLin A).singularValues (r - 1) ≤ ‖A - B‖ := by
  refine le_trans ?_ (EckartYoung.sqrt_sum_sq_singularValues_le_norm_sub A B hB)
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => (toEuclideanLin A).singularValues i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

variable {ω : ℝ} {r₀ : ℕ} {k k' q r₁ : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
  {x : State m n} {Ua : Matrix m (Fin k) ℝ} {Va : Matrix n (Fin k') ℝ}
  {K : ℝ → Matrix m (Fin x.r) ℝ} {Lf : ℝ → Matrix n (Fin x.r) ℝ}
  {Sa : ℝ → Matrix (Fin k) (Fin k') ℝ} {P : Matrix (Fin k) (Fin q) ℝ} {s : Fin q → ℝ}
  {Q : Matrix (Fin k') (Fin q) ℝ}

/-- **Thm 3.2 (exactness), one step** (arXiv 2609.32615, Thm 3.2 and its proof in App. B).
Let `F(t, Y) = W'(t)` on `[t₀, t₁]` not depend on `Y`, and start from `Y₀ = U₀ S₀ V₀ᵀ = W(t₀)`.
If `W(t₁) = U₁ S₁ V₁ᵀ` with orthonormal `U₁`, `V₁`, invertible `S₁` (so `rank W(t₁) = r`),
`U₁ᵀ U₀` and `V₁ᵀ V₀` right invertible (invertible when `U₀`, `V₀` have `r` columns too), and the
tolerance is below the smallest singular value, `τ ‖W(t₁)‖_F < σ_r(W(t₁))` (`0`-based index
`r - 1` in the code), then whatever the buffer, the step keeps `r₁ = r` and
`U' S' V'ᵀ = W(t₁)` for the new factors.  Differences from the paper: the paper states only
invertibility of `V₁ᵀ V₀`, but its "identical argument" for `V̂` needs that of `U₁ᵀ U₀`; the
truncation is modelled with the actual rule (tail in Frobenius norm below `ϑ = τ ‖Ŝ‖_F`), and
`‖Ŝ(t₁)‖_F = ‖W(t₁)‖_F` is derived. -/
theorem IsSDLRTData.exact (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁) (ht : t₀ ≤ t₁)
    {W : ℝ → Matrix m n ℝ} (hW : IsDerivRHS F W t₀ t₁) (hY : x.Y = W t₀) {r : ℕ}
    {U₁ : Matrix m (Fin r) ℝ} {S₁ : Matrix (Fin r) (Fin r) ℝ} {V₁ : Matrix n (Fin r) ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hS₁ : IsUnit S₁.det)
    (hfac : W t₁ = U₁ * S₁ * V₁ᵀ)
    (hU : ∃ C : Matrix (Fin x.r) (Fin r) ℝ, U₁ᵀ * x.U * C = 1)
    (hV : ∃ C : Matrix (Fin x.r) (Fin r) ℝ, V₁ᵀ * x.V * C = 1)
    (hϑ : x.τ * ‖W t₁‖ < (toEuclideanLin (W t₁)).singularValues (r - 1)) (h : r₁ ≤ q) :
    r₁ = r ∧ (next ω r₀ x.τ Ua Va P s Q h).Y = W t₁ := by
  obtain ⟨CU, hCU⟩ := hU
  obtain ⟨CV, hCV⟩ := hV
  have hmem : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hU₀ := hs.orthU₀
  have hV₀ := hs.orthV₀
  have hA₀V : W t₀ * x.V = x.U * x.S := by
    rw [← hY, State.Y, Matrix.mul_assoc, hV₀, Matrix.mul_one]
  have hUA₀ : (W t₀)ᵀ * x.U = x.V * x.Sᵀ := by
    rw [← hY, State.Y, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc, hU₀, Matrix.mul_one]
  have eK : K t₁ = W t₁ * x.V := by
    rw [Exactness.kStepODE_eq_add hW hs.kSol t₁ hmem, hs.kStart, Matrix.sub_mul, hA₀V]
    abel
  have eL : Lf t₁ = (W t₁)ᵀ * x.U := by
    rw [Exactness.lStepODE_eq_add hW hs.lSol t₁ hmem, hs.lStart, Matrix.transpose_sub,
      Matrix.sub_mul, hUA₀]
    abel
  have eS : Sa t₁ = Uaᵀ * W t₁ * Va := by
    rw [Exactness.factorODE_eq_add hW Uaᵀ Va (fun S => Ua * S * Vaᵀ) (fun _ _ => rfl) hs.sSol t₁
      hmem, hs.sStart, hY, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hcapL : Ua * Uaᵀ * W t₁ = W t₁ := by
    have h1 : W t₁ = K t₁ * CV * V₁ᵀ := by
      rw [eK, hfac]
      calc U₁ * S₁ * V₁ᵀ = U₁ * S₁ * (V₁ᵀ * x.V * CV) * V₁ᵀ := by rw [hCV, Matrix.mul_one]
        _ = U₁ * S₁ * V₁ᵀ * x.V * CV * V₁ᵀ := by simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [← Matrix.mul_assoc]
    rw [hs.capK]
  have hcapR : W t₁ * Va * Vaᵀ = W t₁ := by
    have h1 : (W t₁)ᵀ = Lf t₁ * CU * U₁ᵀ := by
      rw [eL, hfac]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc V₁ * (S₁ᵀ * U₁ᵀ) = V₁ * S₁ᵀ * (U₁ᵀ * x.U * CU) * U₁ᵀ := by
            rw [hCU, Matrix.mul_one, Matrix.mul_assoc]
        _ = V₁ * (S₁ᵀ * U₁ᵀ) * x.U * CU * U₁ᵀ := by simp only [Matrix.mul_assoc]
    have h2 : Va * Vaᵀ * (W t₁)ᵀ = (W t₁)ᵀ := by
      rw [h1]
      simp only [← Matrix.mul_assoc]
      rw [hs.capL]
    have h3 := congrArg Matrix.transpose h2
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h3
  have hYh : Ua * Sa t₁ * Vaᵀ = W t₁ := by
    rw [eS]
    calc Ua * (Uaᵀ * W t₁ * Va) * Vaᵀ = Ua * Uaᵀ * W t₁ * Va * Vaᵀ := by
          simp only [Matrix.mul_assoc]
      _ = W t₁ := by rw [hcapL, hcapR]
  have hnorm : ‖Sa t₁‖ = ‖W t₁‖ := by
    rw [← hYh, Frobenius.norm_mul_transpose_of_orthonormal hs.orthVa,
      Frobenius.norm_mul_of_orthonormal hs.orthUa]
  have hrW : (W t₁).rank = r :=
    (SVD.rank_eq_iff_exists_factor _).mpr ⟨U₁, S₁, V₁, hU₁, hV₁, hS₁, hfac⟩
  have hrq : (W t₁).rank = q := by
    refine (SVD.rank_eq_iff_exists_factor _).mpr ⟨Ua * P, diagonal s, Va * Q, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uaᵀ, hs.orthUa,
        Matrix.one_mul, hs.orthP]
    · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vaᵀ, hs.orthVa,
        Matrix.one_mul, hs.orthQ]
    · rw [det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (hs.pos i).ne'
    · rw [← hYh, hs.svd, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
  have hqr : q = r := hrq.symm.trans hrW
  have hle : r ≤ r₁ := by
    by_contra hlt
    have hlt' : r₁ < r := not_le.mp hlt
    have hB : (next ω r₀ x.τ Ua Va P s Q h).Y.rank ≤ r₁ :=
      rank_mul_mul_transpose_le (next ω r₀ x.τ Ua Va P s Q h).U _ _
    have hcard : r ≤ Fintype.card n := by
      rw [← hrW]
      exact (W t₁).rank_le_card_width
    have h1 := singularValues_le_norm_sub (W t₁) _ hB hlt' hcard
    have h2 := hs.trunc_le (ω := ω) (r₀ := r₀) h
    rw [hYh, norm_sub_rev, hnorm] at h2
    linarith
  have hr₁q : r₁ = q := le_antisymm h (hqr ▸ hle)
  refine ⟨hr₁q.trans hqr, ?_⟩
  have h0 := norm_truncated_sub_svd hs.orthP hs.orthQ s h
  have ht0 : tailSqSum s r₁ = 0 := by rw [hr₁q]; exact tailSq_self s
  rw [ht0, Real.sqrt_zero, norm_eq_zero, sub_eq_zero] at h0
  rw [next_Y, h0, ← hs.svd, hYh]

/-- **Thm 3.2 (exactness), one step, square form** (arXiv 2609.32615, Thm 3.2): as
`IsSDLRTData.exact` with `U₁`, `V₁` of the same size as `U₀`, `V₀` and `U₁ᵀ U₀`, `V₁ᵀ V₀`
invertible. -/
theorem IsSDLRTData.exact_of_isUnit (hs : IsSDLRTData F t₀ t₁ x Ua Va K Lf Sa P s Q r₁)
    (ht : t₀ ≤ t₁) {W : ℝ → Matrix m n ℝ} (hW : IsDerivRHS F W t₀ t₁) (hY : x.Y = W t₀)
    {U₁ : Matrix m (Fin x.r) ℝ} {S₁ : Matrix (Fin x.r) (Fin x.r) ℝ}
    {V₁ : Matrix n (Fin x.r) ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (hS₁ : IsUnit S₁.det)
    (hfac : W t₁ = U₁ * S₁ * V₁ᵀ) (hU : IsUnit (U₁ᵀ * x.U)) (hV : IsUnit (V₁ᵀ * x.V))
    (hϑ : x.τ * ‖W t₁‖ < (toEuclideanLin (W t₁)).singularValues (x.r - 1)) (h : r₁ ≤ q) :
    r₁ = x.r ∧ (next ω r₀ x.τ Ua Va P s Q h).Y = W t₁ :=
  hs.exact ht hW hY hU₁ hV₁ hS₁ hfac ⟨↑hU.unit⁻¹, hU.mul_val_inv⟩ ⟨↑hV.unit⁻¹, hV.mul_val_inv⟩ hϑ h

/-- **Thm 3.2 (exactness) over a training period** (arXiv 2609.32615, Thm 3.2: "after a certain
training period `T`, `U(t) S(t) V(t)ᵀ = W(t)`").  Let `F(t, Y) = W'(t)` on `[t₀, t₀ + N h]`, start
from `U(t₀) S(t₀) V(t₀)ᵀ = W(t₀)` of rank `r`, and let `W(tⱼ) = Uⱼ Sⱼ Vⱼᵀ` at the grid points
(`Uⱼ`, `Vⱼ` orthonormal, `Sⱼ` invertible) with the non-degeneracy of `IsSDLRTData.exact` at every
step and with the initial tolerance factor `τ₀` below the relative smallest singular value,
`τ₀ ‖W(tⱼ)‖_F < σ_r(W(tⱼ))`.  Then all iterates are exact and keep rank `r`, whatever the buffers
and whatever `ω ∈ [0, 1]`. -/
theorem sdlrt_exact_run {ϑ h : ℝ} {N : ℕ} (hh : 0 ≤ h) {X : ℕ → State m n}
    (hrun : ∀ j < N, IsSDLRTStep F ω r₀ ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (X j) (X (j + 1)))
    {W : ℝ → Matrix m n ℝ} (hW : IsDerivRHS F W t₀ (t₀ + N * h)) (hY : (X 0).Y = W t₀) {r : ℕ}
    (hr₀ : (X 0).r = r) {Ub : ℕ → Matrix m (Fin r) ℝ} {Sb : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {Vb : ℕ → Matrix n (Fin r) ℝ} (hUb : ∀ j, (Ub j)ᵀ * Ub j = 1) (hVb : ∀ j, (Vb j)ᵀ * Vb j = 1)
    (hSb : ∀ j, IsUnit (Sb j).det)
    (hfac : ∀ j ≤ N, W (t₀ + j * h) = Ub j * Sb j * (Vb j)ᵀ)
    (hU : ∀ j < N, ∃ C : Matrix (Fin (X j).r) (Fin r) ℝ, (Ub (j + 1))ᵀ * (X j).U * C = 1)
    (hV : ∀ j < N, ∃ C : Matrix (Fin (X j).r) (Fin r) ℝ, (Vb (j + 1))ᵀ * (X j).V * C = 1)
    (hτ : ∀ j ≤ N, (X 0).τ * ‖W (t₀ + j * h)‖ <
      (toEuclideanLin (W (t₀ + j * h))).singularValues (r - 1))
    (hτ₀ : 0 ≤ (X 0).τ) (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1) :
    ∀ j ≤ N, (X j).r = r ∧ (X j).Y = W (t₀ + j * h) := by
  have key : ∀ j ≤ N, (X j).r = r ∧ (X j).Y = W (t₀ + j * h) ∧ 0 ≤ (X j).τ ∧
      (X j).τ ≤ (X 0).τ := by
    intro j
    induction j with
    | zero => intro _; simp [hr₀, hY, hτ₀]
    | succ j ih =>
      intro hj
      have hjN : j < N := hj
      obtain ⟨-, hYj, hτ1, hτ2⟩ := ih hjN.le
      obtain ⟨_, _, q', _, Ua', Va', K', Lf', Sa', P', s', Q', hr', hs, -, hy⟩ := hrun j hjN
      have hjcast : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hle : t₀ + j * h ≤ t₀ + (j + 1) * h := by nlinarith
      have hW' : IsDerivRHS F W (t₀ + j * h) (t₀ + (j + 1) * h) :=
        ⟨hW.cont.mono (Icc_subset_Icc (by nlinarith) (by nlinarith)),
          fun t ht Y => hW.deriv t ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ Y⟩
      have ec : t₀ + ((j + 1 : ℕ) : ℝ) * h = t₀ + (j + 1) * h := by push_cast; ring
      have hfac' := hfac (j + 1) hj
      have hτ' := hτ (j + 1) hj
      rw [ec] at hfac' hτ'
      have hτ'' : (X j).τ * ‖W (t₀ + (j + 1) * h)‖ <
          (toEuclideanLin (W (t₀ + (j + 1) * h))).singularValues (r - 1) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hτ2 (norm_nonneg _)) hτ'
      obtain ⟨h1, h2⟩ := hs.exact (ω := ω) (r₀ := r₀) hle hW' hYj (hUb _) (hVb _) (hSb _) hfac'
        (hU j hjN) (hV j hjN) hτ'' hr'
      have hτn := next_tau_mem (ω := ω) (r₀ := r₀) (Ua := Ua') (Va := Va') (P := P') (s := s')
        (Q := Q') hω₀ hω₁ hτ1 hr'
      rw [hy, ec]
      exact ⟨h1, h2, hτn.1, hτn.2.trans hτ2⟩
  exact fun j hj => ⟨(key j hj).1, (key j hj).2.1⟩

end Exact

/-! ### Theorem 3.3 (error bound) -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {ω : ℝ} {r₀ : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε ϑ t₀ t₁ h H : ℝ} {x y : State m n}
  {A : ℝ → Matrix m n ℝ}

/-- **Local error of SDLRT** (arXiv 2609.32615, proof of Thm C.1, eq. (33), with `γ = 1`): under
(A1) (`F` `L`-Lipschitz, bounded by `B`) and (A2) (the normal component of `F` at rank `r` is at
most `ε`), one step of size `h ≤ H` with truncation tolerance at most `ϑ` satisfies
`‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h) + ϑ` for the exact solution `A` from `Y₀`. -/
theorem IsSDLRTStep.local_error_le (hs : IsSDLRTStep F ω r₀ ϑ t₀ t₁ x y)
    (hε : FactoredNormalBound F x.r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = x.Y) :
    ‖y.Y - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := by
  obtain ⟨_, _, _, _, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, hϑ, rfl⟩ := hs
  have := (hd.toRankAdaptive (ω := ω) (r₀ := r₀) hr).local_error_le hε hF hL hB ht₁ hh hhH hA hA₀
  linarith

/-- **Global error of SDLRT, intermediate form** (arXiv 2609.32615, proof of Thm C.1, eq. (34),
with `γ = 1`): under (A1), (A2) and (A3), for `j ≤ N` with `j h ≤ T`,
`‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ j ϑ`, `c₀ = c₃ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L H`,
`c₂ = T e^{L T} bugC₂ L B H`, for step sizes `h ≤ H`. -/
theorem sdlrt_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε₀ : 0 ≤ ε) (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {X : ℕ → State m n}
    (hε : ∀ j < N, FactoredNormalBound F (X j).r ε)
    (hstep : ∀ j < N, IsSDLRTStep F ω r₀ ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (X j) (X (j + 1)))
    {δ T : ℝ} (hδ : ‖(X 0).Y - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖(X j).Y - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * j * ϑ := by
  intro j hj hT
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily (t₀ := t₀) hF hB hc hh (fun j => (X j).Y)
  have hloc : ∀ j < N, ‖(X (j + 1)).Y - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := fun j hj =>
    (hstep j hj).local_error_le (hε j hj) hF hL hB (by ring) hh hhH (hΦ j).1 (hΦ j).2
  have h1 := lady_windermere (Y := fun j => (X j).Y) hF hL hh hA (fun j _ => (hΦ j).1)
    (fun j _ => (hΦ j).2) hloc j hj
  set g := bugC₁ L H * ε + bugC₂ L B H * h with hg_def
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ g :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε₀)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  set Z := ‖(X 0).Y - A t₀‖ + j * (h * g + ϑ) with hZ_def
  have he := Real.exp_pos (L * (j * h))
  have hZ : 0 ≤ Z := by
    by_contra hcon
    have : Real.exp (L * (j * h)) * Z < 0 := mul_neg_of_pos_of_neg he (lt_of_not_ge hcon)
    linarith [norm_nonneg ((X j).Y - A (t₀ + j * h))]
  have hexp : Real.exp (L * (j * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hZle : Z ≤ δ + T * g + j * ϑ := by
    have : (j : ℝ) * h * g ≤ T * g := mul_le_mul_of_nonneg_right hT hg
    rw [hZ_def]
    nlinarith
  calc ‖(X j).Y - A (t₀ + j * h)‖ ≤ Real.exp (L * (j * h)) * Z := h1
    _ ≤ Real.exp (L * T) * Z := mul_le_mul_of_nonneg_right hexp hZ
    _ ≤ Real.exp (L * T) * (δ + T * g + j * ϑ) :=
        mul_le_mul_of_nonneg_left hZle (Real.exp_pos _).le
    _ = _ := by rw [hg_def]; ring

/-- **Thm 3.3 / Thm C.1 (error bound), case `γ = 1`** (arXiv 2609.32615).  Let `Ẇ_f = F(t, W_f)`
on `[t₀, t₀ + T]`, `T = N η`, `η > 0`, `N ≥ 1`, under (A1) `F` `L`-Lipschitz, bounded by `B`,
(A2) normal component of `F` at most `ε` at the ranks of the iterates, (A3)
`‖U₀ S₀ V₀ᵀ - W_f(t₀)‖ ≤ δ`.  After `N` SDLRT steps of size `η` with truncation tolerances at
most `ϑ`:

    ‖U S Vᵀ - W_f(t₀ + T)‖_F ≤ c₀ δ + c₁ ε + c₂ η + c₃ ϑ / η,

`c₀ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L T`, `c₂ = T e^{L T} bugC₂ L B T`, `c₃ = T e^{L T}`, which
depend only on `L`, `B`, `T`, not on singular values.  Differences from the paper: the paper has
`c₁ γ ε` with `γ ∈ (0, 1)`.  For any fixed `γ` that form follows from this one with `c₁ / γ`
in place of `c₁`, so as an inequality with free constants it says nothing about `γ`; its
justification (26) and the claimed gain `E_DLRT - E_SDLRT = (1 - γ) c₁ ε > 0` are false, see
`compensation_no_contraction` and `sdlrt_worse_than_dlrt`.  (A2) is the library's
`FactoredNormalBound`, imposed at the ranks of the iterates on all of `ℝ^{m×n}` rather than on
an unspecified neighbourhood. -/
theorem sdlrt_error_bound (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε₀ : 0 ≤ ε) {η : ℝ} (hη : 0 < η) {N : ℕ}
    (hN : 0 < N) {T : ℝ} (hT : T = N * η) (hA : ODESolution F A t₀ (t₀ + T))
    {X : ℕ → State m n} (hε : ∀ j < N, FactoredNormalBound F (X j).r ε)
    (hstep : ∀ j < N, IsSDLRTStep F ω r₀ ϑ (t₀ + j * η) (t₀ + (j + 1) * η) (X j) (X (j + 1)))
    {δ : ℝ} (hδ : ‖(X 0).Y - A t₀‖ ≤ δ) :
    ‖(X N).Y - A (t₀ + T)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L T * ε
      + T * Real.exp (L * T) * bugC₂ L B T * η + T * Real.exp (L * T) * ϑ / η := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hηT : η ≤ T := by rw [hT]; nlinarith
  have hA' : ODESolution F A t₀ (t₀ + N * η) := hT ▸ hA
  have h1 := sdlrt_global_error_le hF hL hB hc hε₀ hη.le hηT hA' hε hstep hδ N le_rfl hT.symm.le
  rw [← hT] at h1
  have e : T * Real.exp (L * T) * ϑ / η = Real.exp (L * T) * N * ϑ := by
    rw [hT]
    field_simp
  rw [e]
  exact h1

/-- **Thm 3.3 with the negative-feedback tolerance** (arXiv 2609.32615, Thm 3.3 for the tolerance
`ϑⱼ = τⱼ ‖Ŝⱼ‖_F` of §3.3, step 5).  For `ω ∈ [0, 1]` and `τ₀ ≥ 0` the tolerances of an SDLRT run
need no assumption: `τⱼ ≤ τ₀`, `‖Yⱼ‖_F ≤ ‖Y₀‖_F + tⱼ B`, so that `ϑⱼ ≤ ϑ := τ₀ (‖Y₀‖_F + T B)`
and `sdlrt_error_bound` holds with this `ϑ`. -/
theorem sdlrt_error_bound_feedback (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y) (hε₀ : 0 ≤ ε) {η : ℝ}
    (hη : 0 < η) {N : ℕ}
    (hN : 0 < N) {T : ℝ} (hT : T = N * η) (hA : ODESolution F A t₀ (t₀ + T))
    {X : ℕ → State m n} (hε : ∀ j < N, FactoredNormalBound F (X j).r ε)
    (hstep : ∀ j < N, ∃ ϑ', IsSDLRTStep F ω r₀ ϑ' (t₀ + j * η) (t₀ + (j + 1) * η) (X j) (X (j + 1)))
    (hτ₀ : 0 ≤ (X 0).τ) (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1) {δ : ℝ} (hδ : ‖(X 0).Y - A t₀‖ ≤ δ) :
    ‖(X N).Y - A (t₀ + T)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * bugC₁ L T * ε
      + T * Real.exp (L * T) * bugC₂ L B T * η
      + T * Real.exp (L * T) * ((X 0).τ * (‖(X 0).Y‖ + T * B)) / η := by
  have hB₀ : 0 ≤ B := hB.nonneg
  have key : ∀ j ≤ N, 0 ≤ (X j).τ ∧ (X j).τ ≤ (X 0).τ ∧ ‖(X j).Y‖ ≤ ‖(X 0).Y‖ + j * η * B := by
    intro j
    induction j with
    | zero => intro _; simp [hτ₀]
    | succ j ih =>
      intro hj
      have hjN : j < N := hj
      obtain ⟨hτ1, hτ2, hY⟩ := ih hjN.le
      obtain ⟨ϑ', _, _, _, _, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, -, hy⟩ := hstep j hjN
      have hle : t₀ + j * η ≤ t₀ + (j + 1) * η := by nlinarith
      have h1 := hd.norm_next_Y_le' (ω := ω) (r₀ := r₀) hB hle hr
      have h2 := next_tau_mem (ω := ω) (r₀ := r₀) (Ua := Ua) (Va := Va) (P := P) (s := s)
        (Q := Q) hω₀ hω₁ hτ1 hr
      rw [hy]
      refine ⟨h2.1, h2.2.trans hτ2, h1.trans ?_⟩
      push_cast
      nlinarith
  refine sdlrt_error_bound (ω := ω) (r₀ := r₀) hF hL hB hc hε₀ hη hN hT hA hε (fun j hj => ?_) hδ
  obtain ⟨hτ1, hτ2, hY⟩ := key j hj.le
  obtain ⟨ϑ', k, k', q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, -, hy⟩ := hstep j hj
  have hle : t₀ + j * η ≤ t₀ + (j + 1) * η := by nlinarith
  refine ⟨k, k', q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, ?_, hy⟩
  have h1 := hd.norm_Sa_le hB hle
  have hjr : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  have h2 : ‖Sa (t₀ + (j + 1) * η)‖ ≤ ‖(X 0).Y‖ + T * B := by
    have : ((j : ℝ) + 1) * η ≤ T := by rw [hT]; exact mul_le_mul_of_nonneg_right hjr hη.le
    nlinarith
  calc (X j).τ * ‖Sa (t₀ + (j + 1) * η)‖ ≤ (X 0).τ * ‖Sa (t₀ + (j + 1) * η)‖ :=
        mul_le_mul_of_nonneg_right hτ2 (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hτ₀

end Error

/-! ### Well-posedness of the algorithm -/

section WellPosed

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The rank selection of step 5 exists for every tolerance `ϑ ≥ 0`.
(arXiv 2609.32615, §3.3, step 5.) -/
theorem exists_isTruncRank {q : ℕ} (s : Fin q → ℝ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    ∃ r₁, IsTruncRank s ϑ r₁ := by
  classical
  have hex : ∃ r, r ≤ q ∧ √(tailSqSum s r) ≤ ϑ :=
    ⟨q, le_rfl, by rw [tailSq_self, Real.sqrt_zero]; exact hϑ⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun r' hr' => ?_⟩
  have h1 := Nat.find_min hex hr'
  have h2 : r' ≤ q := hr'.le.trans (Nat.find_spec hex).1
  exact not_le.mp fun h3 => h1 ⟨h2, h3⟩

/-- **Well-posedness of one SDLRT step** (arXiv 2609.32615, §3.3).  For `F` Lipschitz, bounded and
continuous in time, every state with orthonormal `U`, `V` and `τ ≥ 0` admits a complete SDLRT step
on `[t₀, t₁]`: the substep solutions, QR bases, thin SVD and rank selection exist. -/
theorem exists_isSDLRTStep {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B : ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (ω : ℝ) (r₀ : ℕ) (x : State m n) (hU : x.Uᵀ * x.U = 1) (hV : x.Vᵀ * x.V = 1)
    (hτ : 0 ≤ x.τ) : ∃ ϑ y, IsSDLRTStep F ω r₀ ϑ t₀ t₁ x y := by
  obtain ⟨K, hK, hK₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t Z => kField_eq x.V t Z) h01
    (x.U * x.S)
  obtain ⟨Lf, hLf, hLf₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t Z => lField_eq x.U t Z)
    h01 (x.V * x.Sᵀ)
  obtain ⟨Ua, hUa, hcapU⟩ := exists_orthonormal_capture
    (fromCols (fromCols (K t₁) x.U) x.Un) le_rfl (Matrix.rank_le_card_height _)
  obtain ⟨Va, hVa, hcapV⟩ := exists_orthonormal_capture
    (fromCols (fromCols (Lf t₁) x.V) x.Vn) le_rfl (Matrix.rank_le_card_height _)
  obtain ⟨Sa, hSa, hSa₀⟩ := exists_odeSolution_conj hF hB hc _ _
    (fun t Z => sField_eq Ua Va t Z) h01 (Uaᵀ * x.Y * Va)
  obtain ⟨P, Q, s, hP, hQ, hs, hpos, -, hsvd⟩ := SVD.exists_svd (Sa t₁) rfl
  obtain ⟨r₁, hr₁⟩ := exists_isTruncRank s (mul_nonneg hτ (norm_nonneg (Sa t₁)))
  exact ⟨_, _, _, _, _, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr₁.le,
    ⟨hU, hV, hK, hK₀, hLf, hLf₀, hUa, hcapU, hVa, hcapV, hSa, hSa₀, hP, hQ, hs, hpos, hsvd, hr₁⟩,
    le_rfl, rfl⟩

/-- **Well-posedness of an SDLRT run** (arXiv 2609.32615, §3.3).  Under the assumptions of
`exists_isSDLRTStep` and `ω ≥ 0`, a run of arbitrary length exists from every state with orthonormal
`U`, `V` and `τ ≥ 0`, so that the hypotheses of `sdlrt_error_bound_feedback` can hold. -/
theorem exists_sdlrt_run {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B : ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    {ω : ℝ} (hω : 0 ≤ ω) (r₀ : ℕ) {t₀ h : ℝ} (hh : 0 ≤ h) (x₀ : State m n)
    (hU : x₀.Uᵀ * x₀.U = 1) (hV : x₀.Vᵀ * x₀.V = 1) (hτ : 0 ≤ x₀.τ) :
    ∃ X : ℕ → State m n, X 0 = x₀ ∧ ∀ j : ℕ, ∃ ϑ,
      IsSDLRTStep F ω r₀ ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (X j) (X (j + 1)) := by
  have hstep : ∀ (j : ℕ) (x : {x : State m n // x.Uᵀ * x.U = 1 ∧ x.Vᵀ * x.V = 1 ∧ 0 ≤ x.τ}),
      ∃ y : {x : State m n // x.Uᵀ * x.U = 1 ∧ x.Vᵀ * x.V = 1 ∧ 0 ≤ x.τ}, ∃ ϑ,
        IsSDLRTStep F ω r₀ ϑ (t₀ + j * h) (t₀ + (j + 1) * h) x.1 y.1 := by
    rintro j ⟨x, hx₁, hx₂, hx₃⟩
    have hle : t₀ + j * h ≤ t₀ + (j + 1) * h := by nlinarith
    obtain ⟨ϑ, y, k, k', q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, hϑ, rfl⟩ :=
      exists_isSDLRTStep hF hB hc hle ω r₀ x hx₁ hx₂ hx₃
    refine ⟨⟨_, next_orthU hd.orthUa hd.orthP hr, next_orthV hd.orthVa hd.orthQ hr, ?_⟩, ϑ, k, k',
      q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, hϑ, rfl⟩
    simp only [next]
    split_ifs
    · exact mul_nonneg hω hx₃
    · exact hx₃
  choose f hf using hstep
  let Y : ℕ → {x : State m n // x.Uᵀ * x.U = 1 ∧ x.Vᵀ * x.V = 1 ∧ 0 ≤ x.τ} :=
    fun j => Nat.rec ⟨x₀, hU, hV, hτ⟩ (fun j y => f j y) j
  exact ⟨fun j => (Y j).1, rfl, fun j => hf j (Y j)⟩

end WellPosed

/-! ### The claimed gain of the buffer is false -/

section Counterexample

/-- The `i`-th unit vector of `ℝ³` as a `3 × 1` matrix. -/
noncomputable def ec (i : Fin 3) : Matrix (Fin 3) (Fin 1) ℝ :=
  Matrix.of fun a _ => if a = i then 1 else 0

/-- The diagonal unit `eᵢ eᵢᵀ` of `ℝ^{3×3}`. -/
noncomputable def ed (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun a => if a = i then 1 else 0

/-- The augmented basis `[e₀, e₂]` of the SDLRT step. -/
noncomputable def cxUa : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]

/-- The bounded, Lipschitz field `F(Y) = e₁ e₁ᵀ + cos(π Y₁₁) e₂ e₂ᵀ` of the counterexample: the
direction `e₂` that the buffer sees is driven by the direction `e₁` that no basis sees. -/
noncomputable def cxF (_ : ℝ) (Y : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ed 1 + Real.cos (Real.pi * Y 1 1) • ed 2

/-- The exact solution `A(t) = e₀ e₀ᵀ + t e₁ e₁ᵀ + (sin(π t) / π) e₂ e₂ᵀ`. -/
noncomputable def cxA (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ed 0 + t • ed 1 + (Real.sin (Real.pi * t) / Real.pi) • ed 2

/-- The SDLRT state: `U₀ = V₀ = e₀`, `S₀ = 1`, buffer `U_neg = V_neg = e₂`, tolerance factor `τ`.
It is what steps 5–6 leave after truncating `diag(1, s)` with `0 < s ≤ τ < 1`, `r₀ = 1`. -/
noncomputable def cxX (τ : ℝ) : State (Fin 3) (Fin 3) :=
  ⟨1, 1, ec 0, 1, ec 0, ec 2, ec 2, τ⟩

/-- The DLRT state: the same factors without a buffer. -/
noncomputable def cxZ (τ : ℝ) : State (Fin 3) (Fin 3) :=
  ⟨1, 0, ec 0, 1, ec 0, 0, 0, τ⟩

/-- `eᵢᵀ eᵢ = 1`. -/
lemma ec_orth (i : Fin 3) : (ec i)ᵀ * ec i = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  fin_cases i <;> simp [ec, Matrix.mul_apply]

/-- `Û = [e₀, e₂]` has orthonormal columns. -/
lemma cxUa_orth : cxUaᵀ * cxUa = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cxUa, Matrix.mul_apply, Fin.sum_univ_three]

/-- `eᵢ eᵢᵀ` is the diagonal unit `ed i`. -/
lemma ec_mul_transpose (i : Fin 3) : ec i * (ec i)ᵀ = ed i := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [ec, ed, Matrix.mul_apply]

/-- The projector of `Û = [e₀, e₂]`. -/
lemma cxUa_mul_transpose : cxUa * cxUaᵀ = ed 0 + ed 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cxUa, ed, Matrix.mul_apply, Fin.sum_univ_two]

/-- `eᵢ eᵢᵀ eⱼ = 0` for `i ≠ j`. -/
lemma ed_mul_ec (i j : Fin 3) (h : i ≠ j) : ed i * ec j = 0 := by
  ext a b
  rw [ed, Matrix.diagonal_mul]
  by_cases ha : a = i
  · subst ha
    simp [ec, h]
  · simp [ha]

/-- The field never moves the direction `e₀`: `F(Y) e₀ = 0`. -/
lemma cxF_mul_ec (t : ℝ) (Y : Matrix (Fin 3) (Fin 3) ℝ) : cxF t Y * ec 0 = 0 := by
  rw [cxF, Matrix.add_mul, Matrix.smul_mul, ed_mul_ec 1 0 (by decide), ed_mul_ec 2 0 (by decide),
    smul_zero, add_zero]

/-- The field of the counterexample is symmetric. -/
lemma cxF_transpose (t : ℝ) (Y : Matrix (Fin 3) (Fin 3) ℝ) : (cxF t Y)ᵀ = cxF t Y := by
  simp [cxF, ed, Matrix.transpose_add, Matrix.transpose_smul]

/-- `‖e_i e_iᵀ‖_F = 1`. -/
lemma norm_ed (i : Fin 3) : ‖ed i‖ = 1 := by
  have h : ‖ed i‖ ^ 2 = 1 := by
    rw [ed, sq_norm_diagonal]
    fin_cases i <;> simp
  nlinarith [norm_nonneg (ed i)]

/-- (A1): the field of the counterexample is Lipschitz.
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxF_lipschitz : IsLipschitzField cxF Real.pi := fun t Y Z => by
  have h1 : cxF t Y - cxF t Z =
      (Real.cos (Real.pi * Y 1 1) - Real.cos (Real.pi * Z 1 1)) • ed 2 := by
    simp only [cxF, sub_smul]
    abel
  rw [h1, norm_smul, norm_ed, mul_one, Real.norm_eq_abs]
  calc |Real.cos (Real.pi * Y 1 1) - Real.cos (Real.pi * Z 1 1)|
      ≤ |Real.pi * Y 1 1 - Real.pi * Z 1 1| := Real.abs_cos_sub_cos_le _ _
    _ = Real.pi * |(Y - Z) 1 1| := by
        rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos, Matrix.sub_apply]
    _ ≤ Real.pi * ‖Y - Z‖ :=
        mul_le_mul_of_nonneg_left (Frobenius.abs_apply_le_norm _ _ _) Real.pi_pos.le

/-- (A1): the field of the counterexample is bounded.
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxF_bounded : IsBoundedField cxF 2 := fun t Y => by
  calc ‖cxF t Y‖ ≤ ‖ed 1‖ + ‖Real.cos (Real.pi * Y 1 1) • ed 2‖ := norm_add_le _ _
    _ = 1 + |Real.cos (Real.pi * Y 1 1)| := by
        rw [norm_smul, norm_ed, norm_ed, mul_one, Real.norm_eq_abs]
    _ ≤ 2 := by linarith [Real.abs_cos_le_one (Real.pi * Y 1 1)]

/-- (A2): the normal component is at most `2`.
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxF_normal : FactoredNormalBound cxF 1 2 := fun t _ _ _ hU hV =>
  (norm_normal_le hU hV _).trans (cxF_bounded t _)

/-- The entry `A(t)₁₁ = t` of the exact solution. -/
lemma cxA_apply (t : ℝ) : cxA t 1 1 = t := by
  simp [cxA, ed]

/-- The exact flow of the counterexample.
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxA_sol : ODESolution cxF cxA 0 1 := by
  have hd : ∀ t, HasDerivAt cxA (ed 1 + Real.cos (Real.pi * t) • ed 2) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s • ed 1) (ed 1) t := by
      simpa using (hasDerivAt_id t).smul_const (ed 1)
    have h2 : HasDerivAt (fun s : ℝ => Real.sin (Real.pi * s) / Real.pi)
        (Real.cos (Real.pi * t)) t := by
      have h3 := ((hasDerivAt_id t).const_mul Real.pi).sin.div_const Real.pi
      simpa [Real.pi_ne_zero, mul_comm] using h3
    have h4 := (h1.const_add (ed 0)).add (h2.smul_const (ed 2))
    exact h4
  refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => ?_⟩
  have h := (hd t).hasDerivWithinAt (s := Ici t)
  rwa [show ed 1 + Real.cos (Real.pi * t) • ed 2 = cxF t (cxA t) by rw [cxF, cxA_apply]] at h

/-- The SDLRT state represents `e₀ e₀ᵀ`. -/
lemma cxX_Y (τ : ℝ) : (cxX τ).Y = ed 0 := by
  change ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (ec 0)ᵀ = ed 0
  rw [Matrix.mul_one, ec_mul_transpose]

/-- The DLRT state represents `e₀ e₀ᵀ`. -/
lemma cxZ_Y (τ : ℝ) : (cxZ τ).Y = ed 0 := cxX_Y τ

/-- The exact solution starts at the SDLRT iterate. -/
lemma cxA_zero (τ : ℝ) : cxA 0 = (cxX τ).Y := by
  rw [cxX_Y]
  simp [cxA]

/-- The new state of the full-rank truncation of step 5. -/
lemma next_Y_full {m n : Type*} [Fintype m] [Fintype n] {ω : ℝ} {r₀ : ℕ} {τ : ℝ} {k k' q : ℕ}
    {Ua : Matrix m (Fin k) ℝ} {Va : Matrix n (Fin k') ℝ} {P : Matrix (Fin k) (Fin q) ℝ}
    {s : Fin q → ℝ} {Q : Matrix (Fin k') (Fin q) ℝ} (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) :
    (next ω r₀ τ Ua Va P s Q (le_refl q)).Y = Ua * (P * diagonal s * Qᵀ) * Vaᵀ := by
  have h0 := norm_truncated_sub_svd hP hQ s (le_refl q)
  rw [tailSq_self, Real.sqrt_zero, norm_eq_zero, sub_eq_zero] at h0
  rw [next_Y, h0]

/-- The Galerkin solution of the SDLRT step: `Ŝ(t) = diag(1, t)`. -/
noncomputable def cxSa (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0] + (t - 0) • !![0, 0; 0, 1]

/-- The K- and L-step solution of both steps: `K(t) = e₀`. -/
noncomputable def cxK (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := ec 0 + (t - 0) • 0

/-- The S-step solution of the DLRT step: `S(t) = 1`. -/
noncomputable def cxS (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := 1 + (t - 0) • 0

/-- The S-step field is constant, since `e₁` is orthogonal to `Û`. -/
lemma cxUa_field (t : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) :
    sField cxUa cxUa cxF t S = !![0, 0; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sField, cxF, cxUa, ed, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

/-- With a tolerance below `1` all unit singular values are kept. -/
lemma isTruncRank_one (q : ℕ) {ϑ : ℝ} (h0 : 0 ≤ ϑ) (h1 : ϑ < 1) :
    IsTruncRank (fun _ : Fin q => (1 : ℝ)) ϑ q where
  le := le_rfl
  tail := by
    rw [tailSq_self, Real.sqrt_zero]
    exact h0
  min r' hr' := by
    refine lt_of_lt_of_le h1 (Real.one_le_sqrt.mpr ?_)
    have h := Finset.single_le_sum (f := fun i : Fin q => if r' ≤ (i : ℕ) then (1 : ℝ) ^ 2 else 0)
      (fun i _ => by split_ifs <;> positivity) (Finset.mem_univ ⟨r', hr'⟩)
    simpa [tailSqSum] using h

/-- `‖I_q‖_F = √q`. -/
lemma norm_one_fin (q : ℕ) : ‖(1 : Matrix (Fin q) (Fin q) ℝ)‖ = √q := by
  rw [← Real.sqrt_sq (norm_nonneg (1 : Matrix (Fin q) (Fin q) ℝ)), ← Matrix.diagonal_one,
    sq_norm_diagonal]
  simp

/-- The Galerkin result of the SDLRT step is `Ŝ(1) = I`. -/
lemma cxSa_one : cxSa 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cxSa]

/-- The Galerkin result of the DLRT step is `S(1) = 1`. -/
lemma cxS_one : cxS 1 = 1 := by
  simp [cxS]

/-- `eᵢ eᵢᵀ eᵢ = eᵢ`. -/
lemma ed_mul_ec_self (i : Fin 3) : ed i * ec i = ec i := by
  ext a b
  rw [ed, Matrix.diagonal_mul]
  by_cases ha : a = i
  · simp [ha]
  · simp [ha, ec]

/-- `Û = [e₀, e₂]` captures `e₀`. -/
lemma cxUa_cap_zero : cxUa * cxUaᵀ * ec 0 = ec 0 := by
  rw [cxUa_mul_transpose, Matrix.add_mul, ed_mul_ec_self, ed_mul_ec 2 0 (by decide), add_zero]

/-- `Û = [e₀, e₂]` captures `e₂`. -/
lemma cxUa_cap_two : cxUa * cxUaᵀ * ec 2 = ec 2 := by
  rw [cxUa_mul_transpose, Matrix.add_mul, ed_mul_ec_self, ed_mul_ec 0 2 (by decide), zero_add]

/-- The SDLRT step of the counterexample: a complete step with the non-empty buffer `e₂`, which
keeps both Galerkin directions (`Ŝ(1) = I`, `r₁ = 2`).
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxX_data {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) :
    IsSDLRTData cxF 0 1 (cxX τ) cxUa cxUa cxK cxK cxSa (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (fun _ => 1) (1 : Matrix (Fin 2) (Fin 2) ℝ) 2 where
  orthU₀ := ec_orth 0
  orthV₀ := ec_orth 0
  kSol := odeSolution_of_const (c := 0) (fun t _ => cxF_mul_ec t _) (ec 0) 0 1
  kStart := by
    change cxK 0 = ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ)
    simp [cxK]
  lSol := odeSolution_of_const (c := 0) (fun t _ => by
    change (cxF t _)ᵀ * ec 0 = 0
    rw [cxF_transpose]
    exact cxF_mul_ec t _) (ec 0) 0 1
  lStart := by
    change cxK 0 = ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
    simp [cxK]
  orthUa := cxUa_orth
  capU := by
    refine Exactness.capture_fromCols.mpr ⟨Exactness.capture_fromCols.mpr ⟨?_, cxUa_cap_zero⟩,
      cxUa_cap_two⟩
    change cxUa * cxUaᵀ * cxK 1 = cxK 1
    simpa [cxK] using cxUa_cap_zero
  orthVa := cxUa_orth
  capV := by
    refine Exactness.capture_fromCols.mpr ⟨Exactness.capture_fromCols.mpr ⟨?_, cxUa_cap_zero⟩,
      cxUa_cap_two⟩
    change cxUa * cxUaᵀ * cxK 1 = cxK 1
    simpa [cxK] using cxUa_cap_zero
  sSol := odeSolution_of_const (fun t Z => cxUa_field t Z) _ _ _
  sStart := by
    rw [cxX_Y]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [cxSa, cxUa, ed, Matrix.mul_apply, Fin.sum_univ_three]
  orthP := by simp
  orthQ := by simp
  anti := fun _ _ _ => le_rfl
  pos := fun _ => one_pos
  svd := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [cxSa]
  rank := by
    refine isTruncRank_one 2 (mul_nonneg h0 (norm_nonneg _)) ?_
    have hn : ‖cxSa 1‖ ≤ 3 / 2 := by
      rw [cxSa_one, norm_one_fin]
      exact Real.sqrt_le_iff.mpr (by norm_num)
    change τ * ‖cxSa 1‖ < 1
    nlinarith [norm_nonneg (cxSa 1)]

/-- The DLRT step of the counterexample: the same factors, no buffer.
(arXiv 2609.32615, counterexample to the gain in Thm 3.3.) -/
theorem cxZ_data {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) :
    IsSDLRTData cxF 0 1 (cxZ τ) (ec 0) (ec 0) cxK cxK cxS
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 where
  orthU₀ := ec_orth 0
  orthV₀ := ec_orth 0
  kSol := odeSolution_of_const (c := 0) (fun t _ => cxF_mul_ec t _) (ec 0) 0 1
  kStart := by
    change cxK 0 = ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ)
    simp [cxK]
  lSol := odeSolution_of_const (c := 0) (fun t _ => by
    change (cxF t _)ᵀ * ec 0 = 0
    rw [cxF_transpose]
    exact cxF_mul_ec t _) (ec 0) 0 1
  lStart := by
    change cxK 0 = ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ
    simp [cxK]
  orthUa := ec_orth 0
  capU := by
    have h0 : ec 0 * (ec 0)ᵀ * ec 0 = ec 0 := by
      rw [Matrix.mul_assoc, ec_orth, Matrix.mul_one]
    refine Exactness.capture_fromCols.mpr ⟨Exactness.capture_fromCols.mpr ⟨?_, h0⟩, ?_⟩
    · change ec 0 * (ec 0)ᵀ * cxK 1 = cxK 1
      simpa [cxK] using h0
    · exact Matrix.mul_zero _
  orthVa := ec_orth 0
  capV := by
    have h0 : ec 0 * (ec 0)ᵀ * ec 0 = ec 0 := by
      rw [Matrix.mul_assoc, ec_orth, Matrix.mul_one]
    refine Exactness.capture_fromCols.mpr ⟨Exactness.capture_fromCols.mpr ⟨?_, h0⟩, ?_⟩
    · change ec 0 * (ec 0)ᵀ * cxK 1 = cxK 1
      simpa [cxK] using h0
    · exact Matrix.mul_zero _
  sSol := odeSolution_of_const (c := 0) (fun t _ => by
    rw [sField, Matrix.mul_assoc, cxF_mul_ec, Matrix.mul_zero]) 1 0 1
  sStart := by
    rw [cxZ_Y, ← ec_mul_transpose]
    have h : (ec 0)ᵀ * (ec 0 * (ec 0)ᵀ) * ec 0 = 1 := by
      rw [← Matrix.mul_assoc, ec_orth, Matrix.one_mul, ec_orth]
    rw [h]
    simp [cxS]
  orthP := by simp
  orthQ := by simp
  anti := fun _ _ _ => le_rfl
  pos := fun _ => one_pos
  svd := by simp [cxS]
  rank := by
    refine isTruncRank_one 1 (mul_nonneg h0 (norm_nonneg _)) ?_
    change τ * ‖cxS 1‖ < 1
    rw [cxS_one, norm_one_fin]
    norm_num
    linarith

/-- The exact value `A(1) = e₀ e₀ᵀ + e₁ e₁ᵀ`. -/
lemma cxA_one : cxA 1 = ed 0 + ed 1 := by
  simp [cxA]

/-- **The contraction (26) of arXiv 2609.32615 is false.**  For the data of `cxX_data` and
`cxZ_data`, the compensated basis `Û = [e₀, e₂]` and the DLRT basis `Ũ = e₀` have the same
residual at the exact value `A(1) = e₀ e₀ᵀ + e₁ e₁ᵀ`, namely `e₁ e₁ᵀ ≠ 0`, because the buffer is
orthogonal to `A(1)`.  So `‖(I - Û Ûᵀ) A₁‖ ≤ γ ‖(I - Ũ Ũᵀ) A₁‖` fails for every `γ < 1`:
monotonicity of projections only gives `γ = 1`. -/
theorem compensation_no_contraction {γ : ℝ} (hγ : γ < 1) :
    ¬ ‖(1 - cxUa * cxUaᵀ) * cxA 1‖ ≤ γ * ‖(1 - ec 0 * (ec 0)ᵀ) * cxA 1‖ := by
  have h1 : (1 - cxUa * cxUaᵀ) * cxA 1 = ed 1 := by
    rw [cxUa_mul_transpose, cxA_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [ed, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  have h2 : (1 - ec 0 * (ec 0)ᵀ) * cxA 1 = ed 1 := by
    rw [ec_mul_transpose, cxA_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [ed, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  rw [h1, h2, norm_ed]
  linarith

/-- **The buffer can make the error larger: the claimed gain is false** (arXiv 2609.32615, Thm 3.3,
"`E_DLRT - E_SDLRT = (1 - γ) c₁ ε > 0`").  For the field `cxF`, which satisfies (A1) and (A2)
(`cxF_lipschitz`, `cxF_bounded`, `cxF_normal`), the exact solution `cxA` from
`e₀ e₀ᵀ = (cxX τ).Y = (cxZ τ).Y` (so (A3) holds with `δ = 0`, `cxA_zero`) and every tolerance
factor `τ ∈ [0, 1/2]`, one step of size `1` from the same factors gives the error `1` without
buffer and the error `√2` with the buffer `e₂`.  The Galerkin step in the larger space follows
`e₂` with the wrong drive, since `e₁`, which drives it, stays outside the basis.  In particular no
bound of SDLRT can be a strict improvement of a sharp bound of DLRT.  (A DLRT step is an SDLRT
step with an empty buffer, so every bound valid for all SDLRT steps is also valid for DLRT.) -/
theorem sdlrt_worse_than_dlrt {ω : ℝ} {r₀ : ℕ} {τ ϑ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 1 / 2)
    (hϑ : τ * √2 ≤ ϑ) :
    ∃ x' z' : State (Fin 3) (Fin 3), IsSDLRTStep cxF ω r₀ ϑ 0 1 (cxX τ) x' ∧
      IsSDLRTStep cxF ω r₀ ϑ 0 1 (cxZ τ) z' ∧ ‖z'.Y - cxA 1‖ = 1 ∧ ‖x'.Y - cxA 1‖ = √2 := by
  have hX := cxX_data hτ₀ hτ₁
  have hZ := cxZ_data hτ₀ hτ₁
  refine ⟨_, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, le_refl 2, hX, ?_, rfl⟩,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, le_refl 1, hZ, ?_, rfl⟩, ?_, ?_⟩
  · change τ * ‖cxSa 1‖ ≤ ϑ
    rw [cxSa_one, norm_one_fin]
    simpa using hϑ
  · change τ * ‖cxS 1‖ ≤ ϑ
    rw [cxS_one, norm_one_fin]
    have h2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    have h3 : τ * 1 ≤ τ * √2 := mul_le_mul_of_nonneg_left h2 hτ₀
    simpa using h3.trans hϑ
  · rw [next_Y_full (by simp) (by simp), cxA_one]
    have e : ec 0 * ((1 : Matrix (Fin 1) (Fin 1) ℝ) * diagonal (fun _ => 1) * 1ᵀ) * (ec 0)ᵀ -
        (ed 0 + ed 1) = -ed 1 := by
      simp [ec_mul_transpose]
    rw [e, norm_neg, norm_ed]
  · rw [next_Y_full (by simp) (by simp), cxA_one]
    have e : cxUa * ((1 : Matrix (Fin 2) (Fin 2) ℝ) * diagonal (fun _ => 1) * 1ᵀ) * cxUaᵀ -
        (ed 0 + ed 1) = diagonal ![0, -1, 1] := by
      simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.diagonal_one]
      rw [cxUa_mul_transpose]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [ed]
    rw [e, ← Real.sqrt_sq (norm_nonneg _), sq_norm_diagonal]
    norm_num [Fin.sum_univ_three]

/-- **Non-vacuity of Thm 3.2** (arXiv 2609.32615, Thm 3.2).  For `F ≡ e₀ e₀ᵀ`,
`W(t) = (1 + t) e₀ e₀ᵀ` and the state `cxX 0` with its buffer `e₂`, every step on `[0, 1]` satisfies
the hypotheses of `IsSDLRTData.exact`, and it gives `Y₁ = W(1)` with rank `1`. -/
theorem exact_example : ∃ ϑ y, IsSDLRTStep (fun _ _ => ed 0) 1 1 ϑ 0 1 (cxX 0) y ∧ y.r = 1 ∧
    y.Y = ed 0 + (1 : ℝ) • ed 0 := by
  have hF : IsLipschitzField
      (fun _ _ => ed 0 : ℝ → Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ) 0 :=
    fun _ _ _ => by simp
  have hB : IsBoundedField
      (fun _ _ => ed 0 : ℝ → Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ) 1 :=
    fun _ _ => (norm_ed 0).le
  obtain ⟨ϑ, y, k, k', q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, hϑ, rfl⟩ :=
    exists_isSDLRTStep hF hB (fun _ => continuous_const) zero_le_one 1 1 (cxX 0) (ec_orth 0)
      (ec_orth 0) le_rfl
  have hW : IsDerivRHS (fun _ _ => ed 0) (fun t : ℝ => ed 0 + t • ed 0) 0 1 :=
    Exactness.isDerivRHS_add_smul _ _ _ _
  have hfac : ed 0 + (1 : ℝ) • ed 0 =
      ec 0 * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (ec 0)ᵀ := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ec_mul_transpose, one_smul, two_smul]
  have hS : IsUnit ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det := by simp
  have hrk : (ed 0 + (1 : ℝ) • ed 0).rank = 1 :=
    (SVD.rank_eq_iff_exists_factor _).mpr ⟨ec 0, _, ec 0, ec_orth 0, ec_orth 0, hS, hfac⟩
  have hsv := SVD.singularValues_pred_rank_pos hrk one_pos
  have hC : ∃ C : Matrix (Fin (cxX 0).r) (Fin 1) ℝ, (ec 0)ᵀ * (cxX 0).U * C = 1 :=
    ⟨(1 : Matrix (Fin 1) (Fin 1) ℝ), by
      change (ec 0)ᵀ * ec 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1
      rw [Matrix.mul_one, ec_orth]⟩
  obtain ⟨h1, h2⟩ := hd.exact (ω := 1) (r₀ := 1) zero_le_one hW (by rw [cxX_Y]; simp)
    (ec_orth 0) (ec_orth 0) hS hfac hC hC (by
      have h0 : (cxX 0).τ = 0 := rfl
      rw [h0, zero_mul]
      exact hsv) hr
  exact ⟨ϑ, _, ⟨k, k', q, r₁, Ua, Va, K, Lf, Sa, P, s, Q, hr, hd, hϑ, rfl⟩, h1, h2⟩

end Counterexample

/-! ### Theorem 3.1 (flow of the best rank-`r` approximation) -/

section BestFlow

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k : ℕ}

/-- The partitioned SVD (5)–(6) of arXiv 2609.32615: `W = U Σ_r Vᵀ + U⊥ Σ⊥ V⊥ᵀ` with `U = [uᵢ]`,
`U⊥ = [u_{r+j}]`, `V = [vᵢ]`, `V⊥ = [v_{r+j}]` having orthonormal columns, `Σ_r = diag(σᵢ)`,
`Σ⊥ = diag(τⱼ)` (`τⱼ = σ_{r+j}`), and no singular value crossing the truncation: `τⱼ < σᵢ`.
The columns need not be sorted, and `r + k` may be smaller than `m` and `n`. -/
structure IsPartitionedSVD (W : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (σ : Fin r → ℝ)
    (V : Matrix n (Fin r) ℝ) (Uc : Matrix m (Fin k) ℝ) (τ : Fin k → ℝ)
    (Vc : Matrix n (Fin k) ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthV : Vᵀ * V = 1
  orthUc : Ucᵀ * Uc = 1
  orthVc : Vcᵀ * Vc = 1
  crossU : Ucᵀ * U = 0
  crossV : Vcᵀ * V = 0
  pos : ∀ i, 0 < σ i
  nonneg : ∀ j, 0 ≤ τ j
  gap : ∀ i j, τ j < σ i
  eq : W = U * diagonal σ * Vᵀ + Uc * diagonal τ * Vcᵀ

/-- The coupling `P_{ij} = σ_{r+j}² / (σᵢ² - σ_{r+j}²)` of Thm 3.1 of arXiv 2609.32615. -/
noncomputable def coupleP (σ : Fin r → ℝ) (τ : Fin k → ℝ) (i : Fin r) (j : Fin k) : ℝ :=
  τ j ^ 2 / (σ i ^ 2 - τ j ^ 2)

/-- The coupling `Q_{ij} = σᵢ σ_{r+j} / (σᵢ² - σ_{r+j}²)` of Thm 3.1 of arXiv 2609.32615. -/
noncomputable def coupleQ (σ : Fin r → ℝ) (τ : Fin k → ℝ) (i : Fin r) (j : Fin k) : ℝ :=
  σ i * τ j / (σ i ^ 2 - τ j ^ 2)

/-- The right-hand side of the `U̇` equation in (18) of arXiv 2609.32615:

    -P_U^⊥ G V S⁻¹ - [∑_{i,j} (P_{ij} u_{r+j}ᵀ G vᵢ + Q_{ij} uᵢᵀ G v_{r+j}) u_{r+j} vᵢᵀ] V S⁻¹,

with `S = diag(σ)`.  The `V̇` equation of (18) is `flowU Gᵀ V U Vc Uc σ τ`, because `Sᵀ = S`,
`(Vcᵀ Gᵀ U) j i = v_{r+j}ᵀ Gᵀ uᵢ` and `(Vᵀ Gᵀ Uc) i j = vᵢᵀ Gᵀ u_{r+j}`. -/
noncomputable def flowU (G : Matrix m n ℝ) (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (Uc : Matrix m (Fin k) ℝ) (Vc : Matrix n (Fin k) ℝ) (σ : Fin r → ℝ) (τ : Fin k → ℝ) :
    Matrix m (Fin r) ℝ :=
  -((1 - U * Uᵀ) * G * V * (diagonal σ)⁻¹) -
    (∑ i, ∑ j, (coupleP σ τ i j * (Ucᵀ * G * V) j i + coupleQ σ τ i j * (Uᵀ * G * Vc) i j) •
      vecMulVec (Ucᵀ j) (Vᵀ i)) * V * (diagonal σ)⁻¹

/-- The rank-one sum of (18) as a matrix product. -/
lemma sum_vecMulVec_eq (Uc : Matrix m (Fin k) ℝ) (V : Matrix n (Fin r) ℝ)
    (M : Matrix (Fin k) (Fin r) ℝ) :
    (∑ i, ∑ j, M j i • vecMulVec (Ucᵀ j) (Vᵀ i)) = Uc * M * Vᵀ := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.transpose_apply,
    smul_eq_mul, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

namespace IsPartitionedSVD

variable {W : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ} {V : Matrix n (Fin r) ℝ}
  {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ} {Vc : Matrix n (Fin k) ℝ}

/-- The partitioned SVD of the transpose.
(arXiv 2609.32615, (5).) -/
theorem swap (h : IsPartitionedSVD W U σ V Uc τ Vc) : IsPartitionedSVD Wᵀ V σ U Vc τ Uc where
  orthU := h.orthV
  orthV := h.orthU
  orthUc := h.orthVc
  orthVc := h.orthUc
  crossU := h.crossV
  crossV := h.crossU
  pos := h.pos
  nonneg := h.nonneg
  gap := h.gap
  eq := by
    rw [h.eq]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- `Uᵀ U⊥ = 0`. -/
lemma crossU' (h : IsPartitionedSVD W U σ V Uc τ Vc) : Uᵀ * Uc = 0 := by
  simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h.crossU

/-- `Vᵀ V⊥ = 0`. -/
lemma crossV' (h : IsPartitionedSVD W U σ V Uc τ Vc) : Vᵀ * Vc = 0 := h.swap.crossU'

/-- `W V = U Σ_r` (from (6)). -/
lemma mul_V (h : IsPartitionedSVD W U σ V Uc τ Vc) : W * V = U * diagonal σ := by
  rw [h.eq, Matrix.add_mul, Matrix.mul_assoc _ Vᵀ, Matrix.mul_assoc _ Vcᵀ, h.orthV, h.crossV,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

/-- `Uᵀ W = Σ_r Vᵀ` (from (6)). -/
lemma transpose_mul (h : IsPartitionedSVD W U σ V Uc τ Vc) : Uᵀ * W = diagonal σ * Vᵀ := by
  rw [h.eq, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᵀ, h.orthU, h.crossU', Matrix.one_mul, Matrix.zero_mul, Matrix.zero_mul,
    add_zero]

/-- `W V⊥ = U⊥ Σ⊥`. -/
lemma mul_Vc (h : IsPartitionedSVD W U σ V Uc τ Vc) : W * Vc = Uc * diagonal τ := by
  rw [h.eq, Matrix.add_mul, Matrix.mul_assoc _ Vᵀ, Matrix.mul_assoc _ Vcᵀ, h.orthVc, h.crossV',
    Matrix.mul_one, Matrix.mul_zero, zero_add]

/-- `(I - U Uᵀ) W (I - V Vᵀ) = U⊥ Σ⊥ V⊥ᵀ`. -/
lemma normal_part (h : IsPartitionedSVD W U σ V Uc τ Vc) :
    (1 - U * Uᵀ) * W * (1 - V * Vᵀ) = Uc * diagonal τ * Vcᵀ := by
  have h1 : W * (1 - V * Vᵀ) = Uc * diagonal τ * Vcᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.mul_V, h.eq, add_sub_cancel_left]
  have h2 : Uᵀ * (Uc * diagonal τ * Vcᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.crossU', Matrix.zero_mul, Matrix.zero_mul]
  rw [Matrix.mul_assoc, h1, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U, h2,
    Matrix.mul_zero, sub_zero]

end IsPartitionedSVD

/-- Scalar elimination between (13) and (14). -/
lemma coupled_scalar {s t a b c d : ℝ} (hst : s ^ 2 - t ^ 2 ≠ 0)
    (h1 : c * s = -a + t * d) (h2 : d * s = -b + t * c) :
    t * d = -(t ^ 2 / (s ^ 2 - t ^ 2) * a + s * t / (s ^ 2 - t ^ 2) * b) := by
  have hd : d * (s ^ 2 - t ^ 2) = -(t * a + s * b) := by
    linear_combination s * h2 + t * h1
  have e : d = -(t * a + s * b) / (s ^ 2 - t ^ 2) := by
    field_simp
    linarith
  rw [e]
  field_simp

/-- **The coupled system (8)–(9) determines `U̇`** (arXiv 2609.32615, (10)–(15)): if the gauge
conditions hold and `U̇ Σ_r = -P_U^⊥ G V + U⊥ Σ⊥ V⊥ᵀ V̇`, `V̇ Σ_r = -P_V^⊥ Gᵀ U + V⊥ Σ⊥ U⊥ᵀ U̇`,
then `U̇` is the right-hand side of (18).  Unlike the paper's derivation this does not expand
`U̇ = U⊥ C`, which is false when `r + k < m`, but works with `C = U⊥ᵀ U̇`, `D = V⊥ᵀ V̇`. -/
theorem flowU_of_coupled {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {Uc : Matrix m (Fin k) ℝ} {Vc : Matrix n (Fin k) ℝ} {σ : Fin r → ℝ} {τ : Fin k → ℝ}
    {G : Matrix m n ℝ} {U' : Matrix m (Fin r) ℝ} {V' : Matrix n (Fin r) ℝ}
    (hUc : Ucᵀ * Uc = 1) (hVc : Vcᵀ * Vc = 1) (hcU : Ucᵀ * U = 0) (hcV : Vcᵀ * V = 0)
    (hV : Vᵀ * V = 1) (hσ : ∀ i, σ i ≠ 0) (hne : ∀ i j, σ i ^ 2 - τ j ^ 2 ≠ 0)
    (h8 : U' * diagonal σ = -((1 - U * Uᵀ) * G * V) + Uc * diagonal τ * (Vcᵀ * V'))
    (h9 : V' * diagonal σ = -((1 - V * Vᵀ) * Gᵀ * U) + Vc * diagonal τ * (Ucᵀ * U')) :
    U' = flowU G U V Uc Vc σ τ := by
  have hunit : IsUnit (diagonal σ).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hσ i
  have hUc1 : Ucᵀ * (1 - U * Uᵀ) = Ucᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcU, Matrix.zero_mul, sub_zero]
  have hVc1 : Vcᵀ * (1 - V * Vᵀ) = Vcᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcV, Matrix.zero_mul, sub_zero]
  -- (10), (11)
  have h10 : (Ucᵀ * U') * diagonal σ = -(Ucᵀ * G * V) + diagonal τ * (Vcᵀ * V') := by
    rw [Matrix.mul_assoc, h8, Matrix.mul_add, Matrix.mul_neg]
    simp only [← Matrix.mul_assoc]
    rw [hUc1, hUc, Matrix.one_mul]
  have h11 : (Vcᵀ * V') * diagonal σ = -(Vcᵀ * Gᵀ * U) + diagonal τ * (Ucᵀ * U') := by
    rw [Matrix.mul_assoc, h9, Matrix.mul_add, Matrix.mul_neg]
    simp only [← Matrix.mul_assoc]
    rw [hVc1, hVc, Matrix.one_mul]
  set M : Matrix (Fin k) (Fin r) ℝ := fun j i =>
    coupleP σ τ i j * (Ucᵀ * G * V) j i + coupleQ σ τ i j * (Uᵀ * G * Vc) i j with hM
  have hτD : diagonal τ * (Vcᵀ * V') = -M := by
    ext j i
    have e1 := congrFun (congrFun h10 j) i
    have e2 := congrFun (congrFun h11 j) i
    simp only [Matrix.mul_diagonal, Matrix.add_apply, Matrix.neg_apply, Matrix.diagonal_mul]
      at e1 e2
    have e3 : (Vcᵀ * Gᵀ * U) j i = (Uᵀ * G * Vc) i j := by
      have : Vcᵀ * Gᵀ * U = (Uᵀ * G * Vc)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [this, Matrix.transpose_apply]
    rw [e3] at e2
    simp only [Matrix.diagonal_mul, hM]
    exact coupled_scalar (hne i j) e1 e2
  have hsum := sum_vecMulVec_eq Uc V M
  have hflow : flowU G U V Uc Vc σ τ =
      (-((1 - U * Uᵀ) * G * V) - Uc * M) * (diagonal σ)⁻¹ := by
    have : (∑ i, ∑ j, (coupleP σ τ i j * (Ucᵀ * G * V) j i +
        coupleQ σ τ i j * (Uᵀ * G * Vc) i j) • vecMulVec (Ucᵀ j) (Vᵀ i)) = Uc * M * Vᵀ := hsum
    rw [flowU, this, Matrix.mul_assoc (Uc * M), hV, Matrix.mul_one,
      Matrix.sub_mul (-((1 - U * Uᵀ) * G * V)), Matrix.neg_mul]
  have h8' : U' * diagonal σ = -((1 - U * Uᵀ) * G * V) - Uc * M := by
    rw [h8, Matrix.mul_assoc Uc, hτD, Matrix.mul_neg]
    exact (sub_eq_add_neg _ _).symm
  rw [hflow, ← h8', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]

/-- The first constraint of §3.2 differentiated: (7)–(8) of arXiv 2609.32615. -/
theorem eq8 {W : ℝ → Matrix m n ℝ} {G : Matrix m n ℝ} {t₀ : ℝ} {U : ℝ → Matrix m (Fin r) ℝ}
    {V : ℝ → Matrix n (Fin r) ℝ} {U' : Matrix m (Fin r) ℝ} {V' : Matrix n (Fin r) ℝ}
    {σ : Fin r → ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ} {Vc : Matrix n (Fin k) ℝ}
    (hW : HasDerivAt W (-G) t₀) (hU : HasDerivAt U U' t₀) (hV : HasDerivAt V V' t₀)
    (hs : IsPartitionedSVD (W t₀) (U t₀) σ (V t₀) Uc τ Vc) (hgU : (U t₀)ᵀ * U' = 0)
    (hgV : (V t₀)ᵀ * V' = 0)
    (hc : ∀ᶠ t in 𝓝 t₀, (1 - U t * (U t)ᵀ) * W t * V t = 0) :
    U' * diagonal σ = -((1 - U t₀ * (U t₀)ᵀ) * G * V t₀) + Uc * diagonal τ * (Vcᵀ * V') := by
  have hP : HasDerivAt (fun t => 1 - U t * (U t)ᵀ) (-(U' * (U t₀)ᵀ + U t₀ * U'ᵀ)) t₀ := by
    simpa using (Frobenius.hasDerivAt_mul hU (Frobenius.hasDerivAt_transpose hU)).const_sub 1
  have hE := Frobenius.hasDerivAt_mul_mul hP hW hV
  have h0 : HasDerivAt (fun t => (1 - U t * (U t)ᵀ) * W t * V t) 0 t₀ :=
    (hasDerivAt_const t₀ (0 : Matrix m (Fin r) ℝ)).congr_of_eventuallyEq hc
  have e := hE.unique h0
  set U₀ := U t₀
  set V₀ := V t₀
  set W₀ := W t₀
  have h1 : U₀ᵀ * W₀ * V₀ = diagonal σ := by
    rw [hs.transpose_mul, Matrix.mul_assoc, hs.orthV, Matrix.mul_one]
  have h2 : U'ᵀ * W₀ * V₀ = 0 := by
    have : U'ᵀ * U₀ = 0 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hgU
    rw [Matrix.mul_assoc, hs.mul_V, ← Matrix.mul_assoc, this, Matrix.zero_mul]
  have h3 : (1 - U₀ * U₀ᵀ) * W₀ * V' = Uc * diagonal τ * (Vcᵀ * V') := by
    have h4 : U₀ᵀ * W₀ * V' = 0 := by
      rw [hs.transpose_mul, Matrix.mul_assoc, hgV, Matrix.mul_zero]
    have h5 : W₀ * V' = Uc * diagonal τ * (Vcᵀ * V') := by
      rw [hs.eq, Matrix.add_mul, Matrix.mul_assoc _ (V₀ᵀ), hgV, Matrix.mul_zero, zero_add,
        Matrix.mul_assoc _ Vcᵀ]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, h5, Matrix.mul_assoc U₀,
      Matrix.mul_assoc U₀, h4, Matrix.mul_zero, sub_zero]
  have h6 : -(U' * U₀ᵀ + U₀ * U'ᵀ) * W₀ * V₀ = -(U' * diagonal σ) := by
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc U',
      Matrix.mul_assoc U', h1, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, h2, Matrix.mul_zero,
      add_zero]
  have h7 : (1 - U₀ * U₀ᵀ) * -G * V₀ = -((1 - U₀ * U₀ᵀ) * G * V₀) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h6, h7, h3, add_assoc] at e
  exact neg_add_eq_zero.mp e

/-- **Thm 3.1 of arXiv 2609.32615, algebraic part.**  If `U`, `V` are differentiable at `t₀` and
satisfy the optimality constraints `(I - U Uᵀ) W V = 0`, `(I - V Vᵀ) Wᵀ U = 0` near `t₀`, the
gauge conditions `Uᵀ U̇ = 0`, `Vᵀ V̇ = 0` at `t₀`, and `U(t₀)`, `V(t₀)` are the singular vectors of
a partitioned SVD of `W(t₀)`, then `U̇`, `V̇` are given by (18). -/
theorem flow_of_constraints {W : ℝ → Matrix m n ℝ} {G : Matrix m n ℝ} {t₀ : ℝ}
    {U : ℝ → Matrix m (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ} {U' : Matrix m (Fin r) ℝ}
    {V' : Matrix n (Fin r) ℝ} {σ : Fin r → ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hW : HasDerivAt W (-G) t₀) (hU : HasDerivAt U U' t₀)
    (hV : HasDerivAt V V' t₀) (hs : IsPartitionedSVD (W t₀) (U t₀) σ (V t₀) Uc τ Vc)
    (hgU : (U t₀)ᵀ * U' = 0) (hgV : (V t₀)ᵀ * V' = 0)
    (hc₁ : ∀ᶠ t in 𝓝 t₀, (1 - U t * (U t)ᵀ) * W t * V t = 0)
    (hc₂ : ∀ᶠ t in 𝓝 t₀, (1 - V t * (V t)ᵀ) * (W t)ᵀ * U t = 0) :
    U' = flowU G (U t₀) (V t₀) Uc Vc σ τ ∧ V' = flowU Gᵀ (V t₀) (U t₀) Vc Uc σ τ := by
  have hWT : HasDerivAt (fun t => (W t)ᵀ) (-Gᵀ) t₀ := by
    simpa using Frobenius.hasDerivAt_transpose hW
  have h8 := eq8 hW hU hV hs hgU hgV hc₁
  have h9 := eq8 hWT hV hU hs.swap hgV hgU hc₂
  have hσ : ∀ i, σ i ≠ 0 := fun i => (hs.pos i).ne'
  have hne : ∀ i j, σ i ^ 2 - τ j ^ 2 ≠ 0 := fun i j => by
    have h1 := hs.gap i j
    have h2 := hs.nonneg j
    nlinarith
  constructor
  · exact flowU_of_coupled hs.orthUc hs.orthVc hs.crossU hs.crossV hs.orthV hσ hne h8 h9
  · refine flowU_of_coupled hs.orthVc hs.orthUc hs.crossV hs.crossU hs.orthU hσ hne h9 ?_
    simpa using h8

/-- The derivative of `S = Uᵀ W V` at `t₀`: `Ṡ = -Uᵀ G V`, (17) of arXiv 2609.32615. -/
theorem hasDerivAt_core {W : ℝ → Matrix m n ℝ} {G : Matrix m n ℝ} {t₀ : ℝ}
    {U : ℝ → Matrix m (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ} {U' : Matrix m (Fin r) ℝ}
    {V' : Matrix n (Fin r) ℝ} {σ : Fin r → ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hW : HasDerivAt W (-G) t₀) (hU : HasDerivAt U U' t₀)
    (hV : HasDerivAt V V' t₀) (hs : IsPartitionedSVD (W t₀) (U t₀) σ (V t₀) Uc τ Vc)
    (hgU : (U t₀)ᵀ * U' = 0) (hgV : (V t₀)ᵀ * V' = 0) :
    HasDerivAt (fun t => (U t)ᵀ * W t * V t) (-((U t₀)ᵀ * G * V t₀)) t₀ := by
  have h := Frobenius.hasDerivAt_mul_mul (Frobenius.hasDerivAt_transpose hU) hW hV
  have h1 : U'ᵀ * W t₀ * V t₀ = 0 := by
    have : U'ᵀ * U t₀ = 0 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hgU
    rw [Matrix.mul_assoc, hs.mul_V, ← Matrix.mul_assoc, this, Matrix.zero_mul]
  have h2 : (U t₀)ᵀ * W t₀ * V' = 0 := by
    rw [hs.transpose_mul, Matrix.mul_assoc, hgV, Matrix.mul_zero]
  rw [h1, h2, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero] at h
  exact h

/-! #### Best approximation under a gap -/

/-- `B` is a best approximation of `A` among the matrices of rank `≤ r` in Frobenius norm. -/
def IsBestApprox (r : ℕ) (A B : Matrix m n ℝ) : Prop :=
  B.rank ≤ r ∧ ∀ C : Matrix m n ℝ, C.rank ≤ r → ‖A - B‖ ≤ ‖A - C‖

/-- A matrix with orthonormal columns has squared Frobenius norm the number of columns. -/
lemma sq_norm_of_orthonormal {I : Type*} [Fintype I] [DecidableEq I] {T : Matrix n I ℝ}
    (hT : Tᵀ * T = 1) : ‖T‖ ^ 2 = Fintype.card I := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hT, Matrix.trace_one]

/-- Pythagoras for the frame `T` against the projector `V Vᵀ`. -/
lemma sq_norm_one_sub_mul_frame {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1) {I : Type*} [Fintype I]
    [DecidableEq I] {T : Matrix n I ℝ} (hT : Tᵀ * T = 1) :
    ‖(1 - V * Vᵀ) * T‖ ^ 2 = Fintype.card I - ‖Vᵀ * T‖ ^ 2 := by
  have h4 := KyFan.sq_norm_mul_one_sub Tᵀ hV
  have h5 : ‖Tᵀ * (1 - V * Vᵀ)‖ = ‖(1 - V * Vᵀ) * T‖ := by
    rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have h6 : ‖Tᵀ * V‖ = ‖Vᵀ * T‖ := by
    rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  have h7 : ‖Tᵀ‖ ^ 2 = Fintype.card I := by
    rw [Frobenius.norm_transpose]
    exact sq_norm_of_orthonormal hT
  rw [← h5, h4, h6, h7]

/-- **Ky Fan maximum principle at a block-diagonal splitting.**  Let `W` be split by `U`, `V`
(`(I - U Uᵀ) W V = 0`, `(I - V Vᵀ) Wᵀ U = 0`) into `S = Uᵀ W V` and
`N = (I - U Uᵀ) W (I - V Vᵀ)`, with `S` bounded below by `ρ₂` and `N` bounded above by `ρ₁ ≤ ρ₂`.
Then no orthonormal frame `T` with at most `r` columns captures more of `W` than `V` does, with a
quantitative defect `(ρ₂² - ρ₁²) (r - ‖Vᵀ T‖²)`.
(arXiv 2609.32615, §3.2.) -/
theorem sq_norm_mul_frame_le {W : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (h₁ : (1 - U * Uᵀ) * W * V = 0)
    (h₂ : (1 - V * Vᵀ) * Wᵀ * U = 0) {ρ₁ ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (hlow : ∀ M : Matrix (Fin r) n ℝ, ρ₂ * ‖M‖ ≤ ‖Uᵀ * W * V * M‖) {I : Type*} [Fintype I]
    [DecidableEq I] {T : Matrix n I ℝ} (hT : Tᵀ * T = 1) (hc : Fintype.card I ≤ r)
    (hup : ∀ M : Matrix n I ℝ, ‖(1 - U * Uᵀ) * W * (1 - V * Vᵀ) * M‖ ≤ ρ₁ * ‖M‖) :
    ‖W * T‖ ^ 2 + (ρ₂ ^ 2 - ρ₁ ^ 2) * (r - ‖Vᵀ * T‖ ^ 2) ≤ ‖W * V‖ ^ 2 := by
  set S := Uᵀ * W * V with hS
  set N := (1 - U * Uᵀ) * W * (1 - V * Vᵀ) with hN
  have hWV : W * V = U * S := by
    have h := h₁
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, hS]
    simp only [Matrix.mul_assoc]
  have hUW : Uᵀ * W * (1 - V * Vᵀ) = 0 := by
    have h := congrArg Matrix.transpose h₂
    simpa [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.mul_assoc] using h
  have hNeq : N = W - U * S * Vᵀ := by
    have h3 : W * (1 - V * Vᵀ) = W - U * S * Vᵀ := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hWV]
    rw [hN, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_assoc U, Matrix.mul_assoc U,
      hUW, Matrix.mul_zero, sub_zero, h3]
  have hUN : Uᵀ * N = 0 := by
    have : Uᵀ * (1 - U * Uᵀ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul, sub_self]
    rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.zero_mul, Matrix.zero_mul]
  have hNV : N * V = 0 := by
    have : (1 - V * Vᵀ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
    rw [hN, Matrix.mul_assoc, this, Matrix.mul_zero]
  have hWT : W * T = U * (S * (Vᵀ * T)) + N * T := by
    have : W = U * S * Vᵀ + N := by rw [hNeq]; abel
    conv_lhs => rw [this]
    rw [Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  have hP : ‖W * T‖ ^ 2 = ‖S * (Vᵀ * T)‖ ^ 2 + ‖N * T‖ ^ 2 := by
    have hin : ⟪U * (S * (Vᵀ * T)), N * T⟫ = 0 := by
      have h0 : Uᵀ * (N * T) = 0 := by rw [← Matrix.mul_assoc, hUN, Matrix.zero_mul]
      rw [Frobenius.inner_mul_left, h0, inner_zero_right]
    rw [hWT, norm_add_sq_real, hin, Frobenius.norm_mul_of_orthonormal hU]
    ring
  set A := ‖Vᵀ * T‖ ^ 2 with hA
  have hNT : N * T = N * ((1 - V * Vᵀ) * T) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hNV,
      Matrix.zero_mul, sub_zero]
  have h3 : ‖(1 - V * Vᵀ) * T‖ ^ 2 = Fintype.card I - A := sq_norm_one_sub_mul_frame hV hT
  have h4 : ρ₂ ^ 2 * (r - A) ≤ ‖S‖ ^ 2 - ‖S * (Vᵀ * T)‖ ^ 2 := by
    have h5 := KyFan.sq_norm_mul_one_sub (S * Vᵀ) hT
    have h6 := KyFan.sq_norm_mul_one_sub Vᵀ hT
    have h7 := hlow (Vᵀ * (1 - T * Tᵀ))
    have h8 : ‖Vᵀ‖ ^ 2 = r := by
      rw [Frobenius.norm_transpose, sq_norm_of_orthonormal hV, Fintype.card_fin]
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV] at h5
    rw [h8] at h6
    rw [← Matrix.mul_assoc S] at h7
    have h9 : (ρ₂ * ‖Vᵀ * (1 - T * Tᵀ)‖) ^ 2 ≤ ‖S * Vᵀ * (1 - T * Tᵀ)‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hρ₂ (norm_nonneg _)) h7 2
    rw [mul_pow, h6, h5, Matrix.mul_assoc S] at h9
    exact h9
  have h5 : ‖N * T‖ ^ 2 ≤ ρ₁ ^ 2 * (Fintype.card I - A) := by
    have h6 := hup ((1 - V * Vᵀ) * T)
    rw [← hNT] at h6
    have h7 := pow_le_pow_left₀ (norm_nonneg _) h6 2
    rwa [mul_pow, h3] at h7
  have hcr : (Fintype.card I : ℝ) ≤ r := by exact_mod_cast hc
  have h6 : ‖W * V‖ = ‖S‖ := by rw [hWV, Frobenius.norm_mul_of_orthonormal hU]
  have h7 : 0 ≤ ρ₁ ^ 2 * (r - Fintype.card I) := mul_nonneg (sq_nonneg ρ₁) (sub_nonneg.mpr hcr)
  have h8 : (ρ₂ ^ 2 - ρ₁ ^ 2) * (r - A) + ρ₁ ^ 2 * (Fintype.card I - A) =
      ρ₂ ^ 2 * (r - A) - ρ₁ ^ 2 * (r - Fintype.card I) := by ring
  rw [hP, h6]
  linarith

/-- `‖Vᵀ T‖² ≤ r`. -/
lemma sq_norm_transpose_mul_frame_le {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1) {I : Type*}
    [Fintype I] [DecidableEq I] {T : Matrix n I ℝ} (hT : Tᵀ * T = 1) :
    ‖Vᵀ * T‖ ^ 2 ≤ r := by
  have h1 : ‖Vᵀ * T‖ ≤ ‖Vᵀ‖ := norm_mul_le_of_orthonormal hT Vᵀ
  have h2 : ‖Vᵀ‖ ^ 2 = r := by
    rw [Frobenius.norm_transpose, sq_norm_of_orthonormal hV, Fintype.card_fin]
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- `W - U (Uᵀ W V) Vᵀ = W (I - V Vᵀ)` under the first constraint. -/
lemma sub_block_eq {W : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (h₁ : (1 - U * Uᵀ) * W * V = 0) : W - U * (Uᵀ * W * V) * Vᵀ = W * (1 - V * Vᵀ) := by
  have h := h₁
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc W, h]
  simp only [Matrix.mul_assoc]

/-- **The block of the large singular values is a best approximation** (Eckart–Young, with a
frame-free gap condition): under the hypotheses of `sq_norm_mul_frame_le`, `U S Vᵀ` with
`S = Uᵀ W V` is a best approximation of `W` of rank `≤ r`.
(arXiv 2609.32615, §3.2.) -/
theorem isBestApprox_of_bounds {W : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ}
    {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (h₁ : (1 - U * Uᵀ) * W * V = 0) (h₂ : (1 - V * Vᵀ) * Wᵀ * U = 0) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁)
    (hρ : ρ₁ ≤ ρ₂) (hlow : ∀ M : Matrix (Fin r) n ℝ, ρ₂ * ‖M‖ ≤ ‖Uᵀ * W * V * M‖)
    (hup : ∀ {I : Type} [Fintype I] (M : Matrix n I ℝ),
      ‖(1 - U * Uᵀ) * W * (1 - V * Vᵀ) * M‖ ≤ ρ₁ * ‖M‖) :
    IsBestApprox r W (U * (Uᵀ * W * V) * Vᵀ) := by
  refine ⟨rank_mul_mul_transpose_le U _ V, fun C hC => ?_⟩
  refine le_trans ?_ (EckartYoung.norm_sub_truncation_le W hC)
  set T := EckartYoung.topRightSingularVectors W r with hTdef
  have hT : Tᵀ * T = 1 := EckartYoung.transpose_mul_topRightSingularVectors W r
  have hc : Fintype.card {i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) // (i : ℕ) < r} ≤ r := by
    refine (Fintype.card_le_of_injective (fun i => (⟨i.1, i.2⟩ : Fin r)) fun a b h => ?_).trans
      (Fintype.card_fin r).le
    exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))
  have hkey := sq_norm_mul_frame_le hU hV h₁ h₂ (hρ₁.trans hρ) hlow hT hc hup
  have hA := sq_norm_transpose_mul_frame_le hV hT
  have hg : 0 ≤ ρ₂ ^ 2 - ρ₁ ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hρ₁ hρ 2)
  have hd := mul_nonneg hg (sub_nonneg.mpr hA)
  have e2 : W - EckartYoung.truncation W r = W * (1 - T * Tᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
    rfl
  rw [sub_block_eq h₁, e2]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [KyFan.sq_norm_mul_one_sub W hV, KyFan.sq_norm_mul_one_sub W hT]
  linarith

/-- **Uniqueness of the best approximation under a strict gap**: under the hypotheses of
`isBestApprox_of_bounds` with `ρ₁ < ρ₂`, every best approximation of `W` of rank `≤ r` equals
`U (Uᵀ W V) Vᵀ`.  This justifies "the" best rank-`r` approximation of arXiv 2609.32615, §3.2. -/
theorem eq_of_isBestApprox {W : Matrix m n ℝ} {U : Matrix m (Fin r) ℝ}
    {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (h₁ : (1 - U * Uᵀ) * W * V = 0) (h₂ : (1 - V * Vᵀ) * Wᵀ * U = 0) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁)
    (hρ : ρ₁ < ρ₂) (hlow : ∀ M : Matrix (Fin r) n ℝ, ρ₂ * ‖M‖ ≤ ‖Uᵀ * W * V * M‖)
    (hup : ∀ {I : Type} [Fintype I] (M : Matrix n I ℝ),
      ‖(1 - U * Uᵀ) * W * (1 - V * Vᵀ) * M‖ ≤ ρ₁ * ‖M‖) {C : Matrix m n ℝ}
    (hC : IsBestApprox r W C) : C = U * (Uᵀ * W * V) * Vᵀ := by
  have hrn : r ≤ Fintype.card n := by
    have := rank_eq_card_of_transpose_mul_eq_one hV
    rw [Fintype.card_fin] at this
    rw [← this]
    exact V.rank_le_card_height
  obtain ⟨T, hT, hcap⟩ := exists_orthonormal_capture Cᵀ
    (by rw [Matrix.rank_transpose]; exact hC.1) hrn
  have hCT : C * T * Tᵀ = C := by
    have h := congrArg Matrix.transpose hcap
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
  have hkey := sq_norm_mul_frame_le hU hV h₁ h₂ (hρ₁.trans hρ.le) hlow hT (by simp) hup
  have hbest := hC.2 _ (rank_mul_mul_transpose_le U (Uᵀ * W * V) V)
  have h3 : ‖W - C‖ ^ 2 = ‖W‖ ^ 2 - ‖W * T‖ ^ 2 + ‖(W - C) * T‖ ^ 2 := by
    have h4 := KyFan.sq_norm_mul_one_sub (W - C) hT
    have h5 : (W - C) * (1 - T * Tᵀ) = W * (1 - T * Tᵀ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub C, Matrix.mul_one, ← Matrix.mul_assoc C, hCT, sub_self,
        sub_zero]
    rw [h5, KyFan.sq_norm_mul_one_sub W hT] at h4
    linarith
  have h6 : ‖W - U * (Uᵀ * W * V) * Vᵀ‖ ^ 2 = ‖W‖ ^ 2 - ‖W * V‖ ^ 2 := by
    rw [sub_block_eq h₁, KyFan.sq_norm_mul_one_sub W hV]
  have h7 := pow_le_pow_left₀ (norm_nonneg _) hbest 2
  rw [h3, h6] at h7
  have hg : 0 < ρ₂ ^ 2 - ρ₁ ^ 2 := sub_pos.mpr (pow_lt_pow_left₀ hρ hρ₁ two_ne_zero)
  have hA := sq_norm_transpose_mul_frame_le hV hT
  have hd := mul_nonneg hg.le (sub_nonneg.mpr hA)
  have h8 : ‖(W - C) * T‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  have h9 : (ρ₂ ^ 2 - ρ₁ ^ 2) * (r - ‖Vᵀ * T‖ ^ 2) = 0 :=
    le_antisymm (by linarith [sq_nonneg ‖(W - C) * T‖]) hd
  have h10 : (r : ℝ) - ‖Vᵀ * T‖ ^ 2 = 0 := (mul_eq_zero.mp h9).resolve_left hg.ne'
  have h11 : (W - C) * T = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h8
    exact norm_eq_zero.mp this
  have h12 : W * T = C * T := by
    rw [Matrix.sub_mul] at h11
    exact sub_eq_zero.mp h11
  have h13 : (1 - V * Vᵀ) * T = 0 := by
    have h14 := sq_norm_one_sub_mul_frame hV hT
    rw [Fintype.card_fin, h10] at h14
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h14)
  have h15 : V * Vᵀ * T = T := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h13
    exact h13.symm
  have hpr : T * Tᵀ = V * Vᵀ := mul_transpose_eq_of_capture_fin hT h15
  have h16 : W * V * Vᵀ = U * (Uᵀ * W * V) * Vᵀ := by
    have h := h₁
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h]
    simp only [Matrix.mul_assoc]
  rw [← hCT, ← h12, Matrix.mul_assoc, hpr, ← Matrix.mul_assoc]
  exact h16

/-! #### Norm bounds for diagonal factors -/

/-- A lower bound `b ≤ σ` passes to right multiplication by `diag(σ)`. -/
lemma mul_norm_le_norm_mul_diagonal {l : Type*} [Fintype l] (M : Matrix l (Fin r) ℝ)
    {σ : Fin r → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, b ≤ σ i) :
    b * ‖M‖ ≤ ‖M * diagonal σ‖ := by
  refine (sq_le_sq₀ (mul_nonneg hb (norm_nonneg _)) (norm_nonneg _)).mp ?_
  rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.mul_diagonal, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb (h j) 2) (sq_nonneg _)

/-- An upper bound `τ ≤ a` passes to left multiplication by `diag(τ)`. -/
lemma norm_diagonal_mul_le {l : Type*} [Fintype l] (M : Matrix (Fin k) l ℝ) {τ : Fin k → ℝ}
    {a : ℝ} (ha : 0 ≤ a) (h0 : ∀ j, 0 ≤ τ j) (h : ∀ j, τ j ≤ a) :
    ‖diagonal τ * M‖ ≤ a * ‖M‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp ?_
  rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.diagonal_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h0 i) (h i) 2) (sq_nonneg _)

/-- A lower bound `b ≤ σ` passes to left multiplication by `diag(σ)`. -/
lemma mul_norm_le_norm_diagonal_mul {l : Type*} [Fintype l] (M : Matrix (Fin r) l ℝ)
    {σ : Fin r → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, b ≤ σ i) :
    b * ‖M‖ ≤ ‖diagonal σ * M‖ := by
  have h1 := mul_norm_le_norm_mul_diagonal Mᵀ hb h
  have h2 : Mᵀ * diagonal σ = (diagonal σ * M)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  rwa [h2, Frobenius.norm_transpose, Frobenius.norm_transpose] at h1

/-- The numbers separating the retained from the discarded singular values. -/
lemma exists_gap_bounds {σ : Fin r → ℝ} {τ : Fin k → ℝ} (hσ : ∀ i, 0 < σ i)
    (hgap : ∀ i j, τ j < σ i) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ (∀ j, τ j ≤ a) ∧ ∀ i, b ≤ σ i := by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := Finset.exists_between' (insert 0 (Finset.univ.image τ))
    (Finset.univ.image σ) (by
      intro x hx y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hσ i
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        exact hgap i j)
  obtain ⟨a, ha₁, ha₂⟩ := Finset.exists_between' (insert 0 (Finset.univ.image τ)) {b} (by
    intro x hx y hy
    rw [Finset.mem_singleton.mp hy]
    exact hb₁ x hx)
  refine ⟨a, b, (ha₁ 0 (Finset.mem_insert_self _ _)).le, ha₂ b (Finset.mem_singleton_self b),
    fun j => (ha₁ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))).le,
    fun i => (hb₂ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).le⟩

/-! #### Smooth orthonormal frames near a gapped SVD -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Products of `C¹` matrix-valued maps are `C¹`. -/
lemma contDiff_matMul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] {f : E → Matrix a b ℝ}
    {g : E → Matrix b c ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun x => f x * g x :=
  ((Frobenius.mulCLM (m := a) (l := b) (n := c)).contDiff.comp hf).clm_apply hg

/-- The Riccati defect: `riccati U₀ V₀ W X Y = 0` says that `U₀ᵀ X = 0` and
`W (V₀ + Y) = (U₀ + X) (U₀ᵀ W (V₀ + Y))`, i.e. the range of `U₀ + X` contains the image under
`W` of the range of `V₀ + Y`. -/
noncomputable def riccati (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (W : Matrix m n ℝ)
    (X : Matrix m (Fin r) ℝ) (Y : Matrix n (Fin r) ℝ) : Matrix m (Fin r) ℝ :=
  (1 - U₀ * U₀ᵀ) * (W * (V₀ + Y) - (U₀ + X) * (U₀ᵀ * W * (V₀ + Y))) + U₀ * U₀ᵀ * X

/-- `riccati` is a `C¹` function of its matrix arguments. -/
lemma contDiff_riccati (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    {W : E → Matrix m n ℝ} {X : E → Matrix m (Fin r) ℝ} {Y : E → Matrix n (Fin r) ℝ}
    (hW : ContDiff ℝ 1 W) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) :
    ContDiff ℝ 1 fun p => riccati U₀ V₀ (W p) (X p) (Y p) := by
  unfold riccati
  have hV : ContDiff ℝ 1 fun p => V₀ + Y p := contDiff_const.add hY
  have hU : ContDiff ℝ 1 fun p => U₀ + X p := contDiff_const.add hX
  exact (contDiff_matMul contDiff_const ((contDiff_matMul hW hV).sub (contDiff_matMul hU
    (contDiff_matMul (contDiff_matMul contDiff_const hW) hV)))).add
    (contDiff_matMul contDiff_const hX)

end Smooth

/-- The linearization of `riccati` at `(X, Y) = (0, 0)`. -/
noncomputable def ricD (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (W : Matrix m n ℝ)
    (X : Matrix m (Fin r) ℝ) (Y : Matrix n (Fin r) ℝ) : Matrix m (Fin r) ℝ :=
  (1 - U₀ * U₀ᵀ) * (W * Y - (X * (U₀ᵀ * W * V₀) + U₀ * (U₀ᵀ * W * Y))) + U₀ * U₀ᵀ * X

/-- The directional derivative of `riccati` at `(X, Y) = (0, 0)`. -/
lemma hasDerivAt_riccati_line (U₀ : Matrix m (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (W : Matrix m n ℝ) (X : Matrix m (Fin r) ℝ) (Y : Matrix n (Fin r) ℝ) :
    HasDerivAt (fun s : ℝ => riccati U₀ V₀ W (s • X) (s • Y)) (ricD U₀ V₀ W X Y) 0 := by
  have hx : HasDerivAt (fun s : ℝ => s • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hy : HasDerivAt (fun s : ℝ => s • Y) Y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y
  have hu : HasDerivAt (fun s : ℝ => U₀ + s • X) X 0 := hx.const_add U₀
  have hv : HasDerivAt (fun s : ℝ => V₀ + s • Y) Y 0 := hy.const_add V₀
  have h1 := Frobenius.hasDerivAt_const_mul W hv
  have h2 := Frobenius.hasDerivAt_const_mul (U₀ᵀ * W) hv
  have h3 := Frobenius.hasDerivAt_mul hu h2
  have h4 := Frobenius.hasDerivAt_const_mul (1 - U₀ * U₀ᵀ) (h1.sub h3)
  have h5 := Frobenius.hasDerivAt_const_mul (U₀ * U₀ᵀ) hx
  have h6 := h4.fun_add h5
  have h7 : HasDerivAt (fun s : ℝ => riccati U₀ V₀ W (s • X) (s • Y)) _ 0 := h6
  exact h7.congr_deriv (by simp [ricD])

/-- A zero of `riccati` gives the invariance relation of the frames.
(arXiv 2609.32615, Thm 3.1.) -/
theorem of_riccati {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {W : Matrix m n ℝ}
    {X : Matrix m (Fin r) ℝ} {Y : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (h : riccati U₀ V₀ W X Y = 0) :
    U₀ᵀ * X = 0 ∧ W * (V₀ + Y) = (U₀ + X) * (U₀ᵀ * W * (V₀ + Y)) := by
  set Z := W * (V₀ + Y) - (U₀ + X) * (U₀ᵀ * W * (V₀ + Y)) with hZ
  have h1 : U₀ᵀ * (1 - U₀ * U₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU₀, Matrix.one_mul, sub_self]
  have hX : U₀ᵀ * X = 0 := by
    have h2 := congrArg (fun A => U₀ᵀ * A) h
    simp only [riccati, Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc] at h2
    rw [h1, hU₀, Matrix.zero_mul, zero_add, Matrix.one_mul] at h2
    exact h2
  refine ⟨hX, ?_⟩
  have h3 : (1 - U₀ * U₀ᵀ) * Z = 0 := by
    have h4 : riccati U₀ V₀ W X Y = (1 - U₀ * U₀ᵀ) * Z := by
      rw [riccati, Matrix.mul_assoc U₀, hX, Matrix.mul_zero, add_zero]
    rwa [h4] at h
  have h5 : U₀ᵀ * Z = 0 := by
    have e : U₀ᵀ * (U₀ + X) = 1 := by rw [Matrix.mul_add, hU₀, hX, add_zero]
    rw [hZ, Matrix.mul_sub, ← Matrix.mul_assoc U₀ᵀ (U₀ + X), e, Matrix.one_mul,
      ← Matrix.mul_assoc U₀ᵀ W, sub_self]
  have h6 : Z = 0 := by
    have : Z = (1 - U₀ * U₀ᵀ) * Z + U₀ * (U₀ᵀ * Z) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [this, h3, h5, Matrix.mul_zero, add_zero]
  exact sub_eq_zero.mp h6

/-- The projection `I - U₀ U₀ᵀ` fixes what is orthogonal to `U₀`. -/
lemma one_sub_mul_of_perp {l : Type*} [Fintype l] {U₀ : Matrix m (Fin r) ℝ} {B : Matrix m l ℝ}
    (h : U₀ᵀ * B = 0) : (1 - U₀ * U₀ᵀ) * B = B := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_zero, sub_zero]

/-- `U₀ᵀ` sees only the normalization term of the linearization. -/
lemma transpose_mul_ricD {U₀ : Matrix m (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (V₀ : Matrix n (Fin r) ℝ) (W : Matrix m n ℝ) (X : Matrix m (Fin r) ℝ)
    (Y : Matrix n (Fin r) ℝ) : U₀ᵀ * ricD U₀ V₀ W X Y = U₀ᵀ * X := by
  have h1 : U₀ᵀ * (1 - U₀ * U₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU₀, Matrix.one_mul, sub_self]
  simp only [ricD, Matrix.mul_add, ← Matrix.mul_assoc]
  rw [h1, hU₀, Matrix.zero_mul, zero_add, Matrix.one_mul]

/-- The linearization on the orthogonal complements. -/
lemma ricD_eq {W : Matrix m n ℝ} {U₀ : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hs : IsPartitionedSVD W U₀ σ V₀ Uc τ Vc)
    {X : Matrix m (Fin r) ℝ} {Y : Matrix n (Fin r) ℝ} (hX : U₀ᵀ * X = 0) (hY : V₀ᵀ * Y = 0) :
    ricD U₀ V₀ W X Y = Uc * diagonal τ * (Vcᵀ * Y) - X * diagonal σ := by
  have h1 : U₀ᵀ * W * V₀ = diagonal σ := by
    rw [hs.transpose_mul, Matrix.mul_assoc, hs.orthV, Matrix.mul_one]
  have h2 : W * Y = Uc * diagonal τ * (Vcᵀ * Y) := by
    rw [hs.eq, Matrix.add_mul, Matrix.mul_assoc _ V₀ᵀ, hY, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc _ Vcᵀ]
  have h3 : U₀ᵀ * W * Y = 0 := by
    rw [hs.transpose_mul, Matrix.mul_assoc, hY, Matrix.mul_zero]
  have h4 : U₀ᵀ * (Uc * diagonal τ * (Vcᵀ * Y) - X * diagonal σ) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc U₀ᵀ, ← Matrix.mul_assoc U₀ᵀ, ← Matrix.mul_assoc U₀ᵀ,
      hs.crossU', hX, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
  rw [ricD, h1, h2, h3, Matrix.mul_zero, add_zero, Matrix.mul_assoc U₀, hX, Matrix.mul_zero,
    add_zero, one_sub_mul_of_perp h4]

/-- The discarded block is bounded by `a` on the right. -/
lemma norm_normal_mul_le {l : Type*} [Fintype l] {Uc : Matrix m (Fin k) ℝ}
    {Vc : Matrix n (Fin k) ℝ} {τ : Fin k → ℝ} (hUc : Ucᵀ * Uc = 1) (hVc : Vcᵀ * Vc = 1) {a : ℝ}
    (ha : 0 ≤ a) (h0 : ∀ j, 0 ≤ τ j) (hτ : ∀ j, τ j ≤ a) (M : Matrix n l ℝ) :
    ‖Uc * diagonal τ * (Vcᵀ * M)‖ ≤ a * ‖M‖ := by
  rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hUc]
  exact (norm_diagonal_mul_le _ ha h0 hτ).trans
    (mul_le_mul_of_nonneg_left (norm_transpose_mul_le hVc M) ha)

/-- **The linearized Riccati system is injective under the gap** (the Sylvester operator
`(X, Y) ↦ (W Y - X Σ_r, Wᵀ X - Y Σ_r)` on the orthogonal complements has no kernel).
(arXiv 2609.32615, Thm 3.1.) -/
theorem ricD_injective {W : Matrix m n ℝ} {U₀ : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hs : IsPartitionedSVD W U₀ σ V₀ Uc τ Vc)
    {X : Matrix m (Fin r) ℝ} {Y : Matrix n (Fin r) ℝ} (h₁ : ricD U₀ V₀ W X Y = 0)
    (h₂ : ricD V₀ U₀ Wᵀ Y X = 0) : X = 0 ∧ Y = 0 := by
  have hX : U₀ᵀ * X = 0 := by
    rw [← transpose_mul_ricD hs.orthU V₀ W X Y, h₁, Matrix.mul_zero]
  have hY : V₀ᵀ * Y = 0 := by
    rw [← transpose_mul_ricD hs.orthV U₀ Wᵀ Y X, h₂, Matrix.mul_zero]
  have e₁ := ricD_eq hs hX hY
  have e₂ := ricD_eq hs.swap hY hX
  rw [h₁] at e₁
  rw [h₂] at e₂
  obtain ⟨a, b, ha, hab, hτ, hσ⟩ := exists_gap_bounds hs.pos hs.gap
  have hb : 0 ≤ b := ha.trans hab.le
  have n₁ : b * ‖X‖ ≤ a * ‖Y‖ := by
    refine (mul_norm_le_norm_mul_diagonal X hb hσ).trans ?_
    rw [(sub_eq_zero.mp e₁.symm).symm]
    exact norm_normal_mul_le hs.orthUc hs.orthVc ha hs.nonneg hτ Y
  have n₂ : b * ‖Y‖ ≤ a * ‖X‖ := by
    refine (mul_norm_le_norm_mul_diagonal Y hb hσ).trans ?_
    rw [(sub_eq_zero.mp e₂.symm).symm]
    exact norm_normal_mul_le hs.orthVc hs.orthUc ha hs.nonneg hτ X
  have h3 : (b - a) * (‖X‖ + ‖Y‖) ≤ (b - a) * 0 := by
    have : (b - a) * (‖X‖ + ‖Y‖) = b * ‖X‖ + b * ‖Y‖ - a * ‖X‖ - a * ‖Y‖ := by ring
    rw [this, mul_zero]
    linarith
  have h4 := le_of_mul_le_mul_left h3 (sub_pos.mpr hab)
  have h5 := norm_nonneg X
  have h6 := norm_nonneg Y
  exact ⟨norm_eq_zero.mp (by linarith), norm_eq_zero.mp (by linarith)⟩

/-- **Existence of a differentiable branch of invariant frames** (implicit function theorem).
Near a gapped partitioned SVD of `W₀` there are `X(W)`, `Y(W)`, differentiable at `W₀` and
vanishing there, with `riccati U₀ V₀ W X Y = 0 = riccati V₀ U₀ Wᵀ Y X`.  This is the perturbation
theory of the singular subspaces that arXiv 2609.32615 takes for granted. -/
theorem exists_riccati_branch {W₀ : Matrix m n ℝ} {U₀ : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hs : IsPartitionedSVD W₀ U₀ σ V₀ Uc τ Vc) :
    ∃ (ψ : Matrix m n ℝ → Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ)
      (ψ' : Matrix m n ℝ →L[ℝ] Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ),
      ψ W₀ = 0 ∧ HasFDerivAt ψ ψ' W₀ ∧
      ∀ᶠ W in 𝓝 W₀, riccati U₀ V₀ W (ψ W).1 (ψ W).2 = 0 ∧
        riccati V₀ U₀ Wᵀ (ψ W).2 (ψ W).1 = 0 := by
  set f : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) →
      Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ :=
    fun p => (riccati U₀ V₀ p.1 p.2.1 p.2.2, riccati V₀ U₀ p.1ᵀ p.2.2 p.2.1) with hf
  have hfc : ContDiff ℝ 1 f := by
    have h1 : ContDiff ℝ 1 fun p : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
      p.1 := contDiff_fst
    have h2 : ContDiff ℝ 1 fun p : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
      p.2.1 := contDiff_fst.comp contDiff_snd
    have h3 : ContDiff ℝ 1 fun p : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
      p.2.2 := contDiff_snd.comp contDiff_snd
    have h4 : ContDiff ℝ 1 fun p : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
      p.1ᵀ := (Frobenius.transposeCLM (m := m) (n := n)).contDiff.comp h1
    exact (contDiff_riccati U₀ V₀ h1 h2 h3).prodMk (contDiff_riccati V₀ U₀ h4 h3 h2)
  set u : Matrix m n ℝ × (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) := (W₀, 0) with hu
  have hfu : f u = 0 := by
    have h1 : U₀ᵀ * W₀ * V₀ = diagonal σ := by
      rw [hs.transpose_mul, Matrix.mul_assoc, hs.orthV, Matrix.mul_one]
    have h2 : V₀ᵀ * W₀ᵀ * U₀ = diagonal σ := by
      rw [hs.swap.transpose_mul, Matrix.mul_assoc, hs.orthU, Matrix.mul_one]
    refine Prod.ext ?_ ?_
    · change riccati U₀ V₀ W₀ 0 0 = 0
      simp only [riccati, add_zero, Matrix.mul_zero]
      rw [hs.mul_V, h1, sub_self, Matrix.mul_zero]
    · change riccati V₀ U₀ W₀ᵀ 0 0 = 0
      simp only [riccati, add_zero, Matrix.mul_zero]
      rw [hs.swap.mul_V, h2, sub_self, Matrix.mul_zero]
  have dfu : HasStrictFDerivAt f (fderiv ℝ f u) u :=
    hfc.contDiffAt.hasStrictFDerivAt (by norm_num)
  have hfd : HasFDerivAt f (fderiv ℝ f u) u := dfu.hasFDerivAt
  set T : (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) →L[ℝ]
      (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) :=
    (fderiv ℝ f u) ∘L ContinuousLinearMap.inr ℝ _ _ with hTdef
  have hT : ∀ Z : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ,
      T Z = (ricD U₀ V₀ W₀ Z.1 Z.2, ricD V₀ U₀ W₀ᵀ Z.2 Z.1) := by
    intro Z
    have hg : HasFDerivAt (fun Z' => f (W₀, Z')) T 0 :=
      hfd.comp (0 : Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) (hasFDerivAt_prodMk_right W₀ 0)
    set Lz : ℝ →L[ℝ] (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) :=
      ContinuousLinearMap.toSpanSingleton ℝ Z with hLz
    have hL : HasFDerivAt (fun s : ℝ => s • Z) Lz 0 := Lz.hasFDerivAt
    have hg' : HasFDerivAt (fun Z' => f (W₀, Z')) T ((0 : ℝ) • Z) := by
      rw [zero_smul]
      exact hg
    have hc : HasFDerivAt (fun s : ℝ => f (W₀, s • Z)) (T ∘L Lz) 0 := hg'.comp (0 : ℝ) hL
    have h1 := ((ContinuousLinearMap.fst ℝ (Matrix m (Fin r) ℝ)
      (Matrix n (Fin r) ℝ)).hasFDerivAt.comp (0 : ℝ) hc).hasDerivAt
    have h2 := ((ContinuousLinearMap.snd ℝ (Matrix m (Fin r) ℝ)
      (Matrix n (Fin r) ℝ)).hasFDerivAt.comp (0 : ℝ) hc).hasDerivAt
    have e1 := h1.unique (hasDerivAt_riccati_line U₀ V₀ W₀ Z.1 Z.2)
    have e2 := h2.unique (hasDerivAt_riccati_line V₀ U₀ W₀ᵀ Z.2 Z.1)
    have hLz1 : T (Lz 1) = T Z := by simp [hLz]
    refine Prod.ext ?_ ?_
    · have : (T (Lz 1)).1 = ricD U₀ V₀ W₀ Z.1 Z.2 := e1
      rw [← this, hLz1]
    · have : (T (Lz 1)).2 = ricD V₀ U₀ W₀ᵀ Z.2 Z.1 := e2
      rw [← this, hLz1]
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun Z hZ => ?_
    rw [hT] at hZ
    obtain ⟨h1, h2⟩ := ricD_injective hs (congrArg Prod.fst hZ) (congrArg Prod.snd hZ)
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hinj
  have hinv : T.IsInvertible := by
    have hbij : Function.Bijective (T : (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ) →ₗ[ℝ]
        (Matrix m (Fin r) ℝ × Matrix n (Fin r) ℝ)) := ⟨hinj, hsurj⟩
    exact ⟨(LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv, by ext x <;> rfl⟩
  refine ⟨dfu.implicitFunctionOfProdDomain hinv, _, ?_,
    (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt, ?_⟩
  · have := (dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    exact this.mp rfl
  · have := dfu.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [this] with W hW
    rw [hfu] at hW
    exact ⟨congrArg Prod.fst hW, congrArg Prod.snd hW⟩

/-- **Orthonormalization close to the identity.**  `(I + Xᵀ X)^{-1/2}` differs from `I` by at
most `‖X‖²`.
(arXiv 2609.32615, Thm 3.1.) -/
theorem exists_orth_factor (X : Matrix m (Fin r) ℝ) :
    ∃ R : Matrix (Fin r) (Fin r) ℝ, Rᵀ * (1 + Xᵀ * X) * R = 1 ∧ ‖R - 1‖ ≤ ‖X‖ ^ 2 := by
  have hA : (Xᵀ * X).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hH := hA.isHermitian
  have hspec := hH.spectral_theorem
  have hUm : (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) ∈
      Matrix.unitaryGroup (Fin r) ℝ := (hH.eigenvectorUnitary).2
  have hd0 : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have hE : Xᵀ * X = (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) *
      diagonal hH.eigenvalues * (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)ᵀ := by
    have h2 : Xᵀ * X = (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) *
        diagonal hH.eigenvalues * star (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) := by
      simpa using hspec
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hQ1 : (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)ᵀ *
      (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hUm
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hQ2 : (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) *
      (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)ᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hUm
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  generalize (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) = Q at hE hQ1 hQ2
  generalize hH.eigenvalues = d at hE hd0
  have hy : ∀ i, 1 ≤ √(1 + d i) := fun i => by
    rw [Real.le_sqrt' one_pos]
    linarith [hd0 i]
  set c : Fin r → ℝ := fun i => (√(1 + d i))⁻¹ with hc
  have hc2 : ∀ i, c i * (1 + d i) * c i = 1 := fun i => by
    have hne : √(1 + d i) ≠ 0 := (lt_of_lt_of_le one_pos (hy i)).ne'
    have hs : √(1 + d i) * √(1 + d i) = 1 + d i := Real.mul_self_sqrt (by linarith [hd0 i])
    have hci : c i * √(1 + d i) = 1 := inv_mul_cancel₀ hne
    calc c i * (1 + d i) * c i = c i * (√(1 + d i) * √(1 + d i)) * c i := by rw [hs]
      _ = (c i * √(1 + d i)) * (c i * √(1 + d i)) := by ring
      _ = 1 := by rw [hci, one_mul]
  have hc3 : ∀ i, (c i - 1) ^ 2 ≤ d i ^ 2 := fun i => by
    have hyi := hy i
    have hs : √(1 + d i) * √(1 + d i) = 1 + d i := Real.mul_self_sqrt (by linarith [hd0 i])
    have hci : c i * √(1 + d i) = 1 := inv_mul_cancel₀ (lt_of_lt_of_le one_pos hyi).ne'
    have hc0 : 0 ≤ c i := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hc1 : c i ≤ 1 := inv_le_one_of_one_le₀ hyi
    have h1 : 1 - c i ≤ d i := by nlinarith
    have h2 : (1 - c i) ^ 2 ≤ d i ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  refine ⟨Q * diagonal c * Qᵀ, ?_, ?_⟩
  · have h1 : (1 : Matrix (Fin r) (Fin r) ℝ) + Xᵀ * X = Q * diagonal (fun i => 1 + d i) * Qᵀ := by
      have e : diagonal (fun i => 1 + d i) = (1 : Matrix (Fin r) (Fin r) ℝ) + diagonal d := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_add]
      rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQ2, hE]
    have h2 : (Q * diagonal c * Qᵀ)ᵀ = Q * diagonal c * Qᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
        Matrix.mul_assoc]
    rw [h2, h1]
    calc Q * diagonal c * Qᵀ * (Q * diagonal (fun i => 1 + d i) * Qᵀ) * (Q * diagonal c * Qᵀ)
        = Q * (diagonal c * (Qᵀ * Q) * diagonal (fun i => 1 + d i) * (Qᵀ * Q) * diagonal c) *
            Qᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hQ1, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
            Matrix.diagonal_mul_diagonal]
          have : (fun i => c i * (1 + d i) * c i) = fun _ => (1 : ℝ) := funext hc2
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hQ2]
  · have e : Q * diagonal c * Qᵀ - 1 = Q * diagonal (fun i => c i - 1) * Qᵀ := by
      have e' : diagonal (fun i => c i - 1) = diagonal c - (1 : Matrix (Fin r) (Fin r) ℝ) := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
      rw [e', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQ2]
    have h3 : ‖diagonal (fun i => c i - 1)‖ ≤ ‖diagonal d‖ := by
      refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
      rw [sq_norm_diagonal, sq_norm_diagonal]
      exact Finset.sum_le_sum fun i _ => hc3 i
    have h4 : ‖diagonal d‖ = ‖Xᵀ * X‖ := by
      rw [hE, Frobenius.norm_mul_transpose_of_orthonormal hQ1,
        Frobenius.norm_mul_of_orthonormal hQ1]
    have h5 : ‖Xᵀ * X‖ ≤ ‖X‖ ^ 2 := by
      have := Frobenius.norm_mul_le Xᵀ X
      rwa [Frobenius.norm_transpose, ← sq] at this
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hQ1, Frobenius.norm_mul_of_orthonormal hQ1]
    exact h3.trans (h4.le.trans h5)

/-- A function within `‖x(t)‖²` of a constant, with `x(t₀) = 0` differentiable at `t₀`, has
derivative `0` at `t₀`. -/
lemma hasDerivAt_of_sq_bound {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : ℝ → F} {x : ℝ → G} {x' : G} {t₀ : ℝ}
    (hx : HasDerivAt x x' t₀) (hx₀ : x t₀ = 0) {c : F} (hg : ∀ t, ‖g t - c‖ ≤ ‖x t‖ ^ 2) :
    HasDerivAt g 0 t₀ := by
  have hgc : g t₀ = c := by
    have h := hg t₀
    rw [hx₀, norm_zero] at h
    have h0 : ‖g t₀ - c‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  rw [hasDerivAt_iff_isLittleO]
  simp only [smul_zero, sub_zero, hgc]
  have h1 : x =O[𝓝 t₀] fun t => t - t₀ := by
    simpa [hx₀] using hx.isBigO_sub
  have h2 : x =o[𝓝 t₀] fun _ => (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff]
    simpa [hx₀] using hx.continuousAt.tendsto
  have h4 : (fun t => ‖x t‖ * ‖x t‖) =o[𝓝 t₀] fun t => t - t₀ := by
    simpa using h2.norm_left.mul_isBigO h1.norm_left
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun t => ?_)).trans_isLittleO
    h4
  have := hg t
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), ← sq]
  exact this

/-- A normalized frame is orthonormal and has the same range as the unnormalized one. -/
lemma frame_props {U₀ X : Matrix m (Fin r) ℝ} {R : Matrix (Fin r) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hX : U₀ᵀ * X = 0) (hR : Rᵀ * (1 + Xᵀ * X) * R = 1) :
    ((U₀ + X) * R)ᵀ * ((U₀ + X) * R) = 1 ∧
      (1 - ((U₀ + X) * R) * ((U₀ + X) * R)ᵀ) * (U₀ + X) = 0 := by
  have hX' : Xᵀ * U₀ = 0 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hX
  have hG : (U₀ + X)ᵀ * (U₀ + X) = 1 + Xᵀ * X := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hU₀, hX, hX',
      add_zero, zero_add]
  have hRA : R * (Rᵀ * (1 + Xᵀ * X)) = 1 := mul_eq_one_comm.mp hR
  constructor
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (U₀ + X), hG,
      ← Matrix.mul_assoc]
    exact hR
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_mul]
    have : (U₀ + X) * R * (Rᵀ * (U₀ + X)ᵀ) * (U₀ + X) =
        (U₀ + X) * (R * (Rᵀ * ((U₀ + X)ᵀ * (U₀ + X)))) := by
      simp only [Matrix.mul_assoc]
    rw [this, hG, hRA, Matrix.mul_one, sub_self]

/-- `(I - U Uᵀ) W V = 0` for normalized frames of a `riccati` zero. -/
lemma constraint_of_frames {U₀ X : Matrix m (Fin r) ℝ} {V₀ Y : Matrix n (Fin r) ℝ}
    {W : Matrix m n ℝ} {RU RV : Matrix (Fin r) (Fin r) ℝ}
    (hA : W * (V₀ + Y) = (U₀ + X) * (U₀ᵀ * W * (V₀ + Y)))
    (hU : (1 - ((U₀ + X) * RU) * ((U₀ + X) * RU)ᵀ) * (U₀ + X) = 0) :
    (1 - ((U₀ + X) * RU) * ((U₀ + X) * RU)ᵀ) * W * ((V₀ + Y) * RV) = 0 := by
  have h : (1 - ((U₀ + X) * RU) * ((U₀ + X) * RU)ᵀ) * W * ((V₀ + Y) * RV) =
      (1 - ((U₀ + X) * RU) * ((U₀ + X) * RU)ᵀ) * (W * (V₀ + Y)) * RV := by
    simp only [Matrix.mul_assoc]
  rw [h, hA, ← Matrix.mul_assoc _ (U₀ + X), hU, Matrix.zero_mul, Matrix.zero_mul]

/-- **Thm 3.1 (flow of the best rank-`r` approximation)** (arXiv 2609.32615, Thm 3.1 and (5)–(18)).
Let `W` be differentiable at `t₀` with `Ẇ(t₀) = -G` (`W = W_f`, `G = ∇L(W_f(t₀))`), and let
`W(t₀) = U₀ Σ_r V₀ᵀ + U⊥ Σ⊥ V⊥ᵀ` be a partitioned SVD without singular value crossing the
truncation.  Then near `t₀` the best rank-`r` approximation factors differentiably: there are
`U(t)`, `S(t)`, `V(t)` with `U(t₀) = U₀`, `S(t₀) = Σ_r`, `V(t₀) = V₀`, with orthonormal `U(t)`,
`V(t)` and `U(t) S(t) V(t)ᵀ` a best approximation of `W(t)` of rank `≤ r` near `t₀`, satisfying
the gauge conditions `U₀ᵀ U̇ = 0`, `V₀ᵀ V̇ = 0` at `t₀` and the coupled system (18):

    U̇ = flowU G U₀ V₀ U⊥ V⊥ σ τ,   V̇ = flowU Gᵀ V₀ U₀ V⊥ U⊥ σ τ,   Ṡ = -U₀ᵀ G V₀.

By `flow_of_constraints` every other differentiable factorization with these properties has the
same derivatives.  Differences from the paper: the paper assumes the differentiability of
`U`, `V`, which is proved here with the implicit function theorem (`exists_riccati_branch`); and
it adopts the gauge with `S = Σ_r` along the flow, which is possible only at the one time `t₀`:
`S(t)` is not diagonal in general since `Ṡ = -Uᵀ G V` is not.  The statement is at an arbitrary
`t₀`, with singular vectors at that time, which is the content of (18). -/
theorem bestApprox_flow {W : ℝ → Matrix m n ℝ} {G : Matrix m n ℝ} {t₀ : ℝ}
    (hW : HasDerivAt W (-G) t₀) {U₀ : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hs : IsPartitionedSVD (W t₀) U₀ σ V₀ Uc τ Vc) :
    ∃ (U : ℝ → Matrix m (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ)
      (V : ℝ → Matrix n (Fin r) ℝ),
      U t₀ = U₀ ∧ S t₀ = diagonal σ ∧ V t₀ = V₀ ∧
      (∀ᶠ t in 𝓝 t₀, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧
        IsBestApprox r (W t) (U t * S t * (V t)ᵀ) ∧
        ∀ C, IsBestApprox r (W t) C → C = U t * S t * (V t)ᵀ) ∧
      U₀ᵀ * flowU G U₀ V₀ Uc Vc σ τ = 0 ∧ V₀ᵀ * flowU Gᵀ V₀ U₀ Vc Uc σ τ = 0 ∧
      HasDerivAt U (flowU G U₀ V₀ Uc Vc σ τ) t₀ ∧
      HasDerivAt V (flowU Gᵀ V₀ U₀ Vc Uc σ τ) t₀ ∧
      HasDerivAt S (-(U₀ᵀ * G * V₀)) t₀ := by
  obtain ⟨ψ, ψ', hψ0, hψd, hψz⟩ := exists_riccati_branch hs
  have hZ : HasDerivAt (fun t => ψ (W t)) (ψ' (-G)) t₀ := hψd.comp_hasDerivAt t₀ hW
  have hX : HasDerivAt (fun t => (ψ (W t)).1) (ψ' (-G)).1 t₀ :=
    (ContinuousLinearMap.fst ℝ (Matrix m (Fin r) ℝ)
      (Matrix n (Fin r) ℝ)).hasFDerivAt.comp_hasDerivAt t₀ hZ
  have hY : HasDerivAt (fun t => (ψ (W t)).2) (ψ' (-G)).2 t₀ :=
    (ContinuousLinearMap.snd ℝ (Matrix m (Fin r) ℝ)
      (Matrix n (Fin r) ℝ)).hasFDerivAt.comp_hasDerivAt t₀ hZ
  generalize hXdef : (fun t => (ψ (W t)).1) = X at hX
  generalize hYdef : (fun t => (ψ (W t)).2) = Y at hY
  generalize (ψ' (-G)).1 = X' at hX
  generalize (ψ' (-G)).2 = Y' at hY
  have hX₀ : X t₀ = 0 := by rw [← hXdef]; simp [hψ0]
  have hY₀ : Y t₀ = 0 := by rw [← hYdef]; simp [hψ0]
  have hz : ∀ᶠ t in 𝓝 t₀, riccati U₀ V₀ (W t) (X t) (Y t) = 0 ∧
      riccati V₀ U₀ (W t)ᵀ (Y t) (X t) = 0 := by
    rw [← hXdef, ← hYdef]
    exact hW.continuousAt.tendsto.eventually hψz
  choose RU hRU₁ hRU₂ using exists_orth_factor (m := m) (r := r)
  choose RV hRV₁ hRV₂ using exists_orth_factor (m := n) (r := r)
  have hRUd : HasDerivAt (fun t => RU (X t)) 0 t₀ :=
    hasDerivAt_of_sq_bound hX hX₀ (c := 1) fun t => hRU₂ (X t)
  have hRVd : HasDerivAt (fun t => RV (Y t)) 0 t₀ :=
    hasDerivAt_of_sq_bound hY hY₀ (c := 1) fun t => hRV₂ (Y t)
  have hRU₀ : RU (X t₀) = 1 := by
    have h := hRU₂ (X t₀)
    rw [hX₀] at h ⊢
    rw [norm_zero] at h
    have h0 : ‖RU 0 - 1‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hRV₀ : RV (Y t₀) = 1 := by
    have h := hRV₂ (Y t₀)
    rw [hY₀] at h ⊢
    rw [norm_zero] at h
    have h0 : ‖RV 0 - 1‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  set U : ℝ → Matrix m (Fin r) ℝ := fun t => (U₀ + X t) * RU (X t) with hUdef
  set V : ℝ → Matrix n (Fin r) ℝ := fun t => (V₀ + Y t) * RV (Y t) with hVdef
  have hU : HasDerivAt U X' t₀ := by
    have h := Frobenius.hasDerivAt_mul (hX.const_add U₀) hRUd
    rwa [hRU₀, Matrix.mul_one, Matrix.mul_zero, add_zero] at h
  have hV : HasDerivAt V Y' t₀ := by
    have h := Frobenius.hasDerivAt_mul (hY.const_add V₀) hRVd
    rwa [hRV₀, Matrix.mul_one, Matrix.mul_zero, add_zero] at h
  have hUt : U t₀ = U₀ := by
    change (U₀ + X t₀) * RU (X t₀) = U₀
    rw [hRU₀, hX₀, add_zero, Matrix.mul_one]
  have hVt : V t₀ = V₀ := by
    change (V₀ + Y t₀) * RV (Y t₀) = V₀
    rw [hRV₀, hY₀, add_zero, Matrix.mul_one]
  have hs' : IsPartitionedSVD (W t₀) (U t₀) σ (V t₀) Uc τ Vc := by rw [hUt, hVt]; exact hs
  have hgU : U₀ᵀ * X' = 0 := by
    have h1 := Frobenius.hasDerivAt_const_mul U₀ᵀ hX
    have h2 : (fun t => U₀ᵀ * X t) =ᶠ[𝓝 t₀] fun _ => 0 :=
      hz.mono fun t ht => (of_riccati hs.orthU ht.1).1
    exact h1.unique ((hasDerivAt_const t₀ (0 : Matrix (Fin r) (Fin r) ℝ)).congr_of_eventuallyEq h2)
  have hgV : V₀ᵀ * Y' = 0 := by
    have h1 := Frobenius.hasDerivAt_const_mul V₀ᵀ hY
    have h2 : (fun t => V₀ᵀ * Y t) =ᶠ[𝓝 t₀] fun _ => 0 :=
      hz.mono fun t ht => (of_riccati hs.orthV ht.2).1
    exact h1.unique ((hasDerivAt_const t₀ (0 : Matrix (Fin r) (Fin r) ℝ)).congr_of_eventuallyEq h2)
  have hfr : ∀ᶠ t in 𝓝 t₀, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧
      (1 - U t * (U t)ᵀ) * W t * V t = 0 ∧ (1 - V t * (V t)ᵀ) * (W t)ᵀ * U t = 0 := by
    filter_upwards [hz] with t ht
    obtain ⟨hx1, hx2⟩ := of_riccati hs.orthU ht.1
    obtain ⟨hy1, hy2⟩ := of_riccati hs.orthV ht.2
    obtain ⟨hu1, hu2⟩ := frame_props hs.orthU hx1 (hRU₁ (X t))
    obtain ⟨hv1, hv2⟩ := frame_props hs.orthV hy1 (hRV₁ (Y t))
    exact ⟨hu1, hv1, constraint_of_frames hx2 hu2, constraint_of_frames hy2 hv2⟩
  obtain ⟨hf₁, hf₂⟩ := flow_of_constraints hW hU hV hs' (by rw [hUt]; exact hgU)
    (by rw [hVt]; exact hgV) (hfr.mono fun t ht => ht.2.2.1) (hfr.mono fun t ht => ht.2.2.2)
  rw [hUt, hVt] at hf₁ hf₂
  have hSd := hasDerivAt_core hW hU hV hs' (by rw [hUt]; exact hgU) (by rw [hVt]; exact hgV)
  have hPU : HasDerivAt (fun t => 1 - U t * (U t)ᵀ) (-(X' * (U t₀)ᵀ + U t₀ * X'ᵀ)) t₀ := by
    simpa using (Frobenius.hasDerivAt_mul hU (Frobenius.hasDerivAt_transpose hU)).const_sub 1
  have hPV : HasDerivAt (fun t => 1 - V t * (V t)ᵀ) (-(Y' * (V t₀)ᵀ + V t₀ * Y'ᵀ)) t₀ := by
    simpa using (Frobenius.hasDerivAt_mul hV (Frobenius.hasDerivAt_transpose hV)).const_sub 1
  have hNd := Frobenius.hasDerivAt_mul_mul hPU hW hPV
  obtain ⟨a, b, ha, hab, hτ, hσ⟩ := exists_gap_bounds hs.pos hs.gap
  have hb : 0 ≤ b := ha.trans hab.le
  have hδ : 0 < (b - a) / 4 := by linarith
  have hS₀ : (U t₀)ᵀ * W t₀ * V t₀ = diagonal σ := by
    rw [hs'.transpose_mul, Matrix.mul_assoc, hs'.orthV, Matrix.mul_one]
  have hclose₁ : ∀ᶠ t in 𝓝 t₀, ‖(U t)ᵀ * W t * V t - diagonal σ‖ < (b - a) / 4 := by
    have := Metric.tendsto_nhds.mp hSd.continuousAt.tendsto _ hδ
    simpa only [hS₀, dist_eq_norm] using this
  have hclose₂ : ∀ᶠ t in 𝓝 t₀, ‖(1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ) -
      Uc * diagonal τ * Vcᵀ‖ < (b - a) / 4 := by
    have := Metric.tendsto_nhds.mp hNd.continuousAt.tendsto _ hδ
    simpa only [hs'.normal_part, dist_eq_norm] using this
  refine ⟨U, fun t => (U t)ᵀ * W t * V t, V, hUt, hS₀, hVt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hfr, hclose₁, hclose₂] with t ⟨h1, h2, h3, h4⟩ h5 h6
    have hlow : ∀ M : Matrix (Fin r) n ℝ,
        (b - (b - a) / 4) * ‖M‖ ≤ ‖(U t)ᵀ * W t * V t * M‖ := by
      intro M
      have h7 := mul_norm_le_norm_diagonal_mul M hb hσ
      have h8 : ‖((U t)ᵀ * W t * V t - diagonal σ) * M‖ ≤ (b - a) / 4 * ‖M‖ :=
        (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h5.le (norm_nonneg _))
      have h9 : ‖diagonal σ * M‖ ≤ ‖(U t)ᵀ * W t * V t * M‖ +
          ‖((U t)ᵀ * W t * V t - diagonal σ) * M‖ := by
        have : diagonal σ * M = (U t)ᵀ * W t * V t * M -
            ((U t)ᵀ * W t * V t - diagonal σ) * M := by
          rw [Matrix.sub_mul]
          abel
        rw [this]
        exact norm_sub_le _ _
      linarith
    have hup : ∀ {I : Type} [Fintype I] (M : Matrix n I ℝ),
        ‖(1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ) * M‖ ≤ (a + (b - a) / 4) * ‖M‖ := by
      intro I _ M
      have h7 := norm_normal_mul_le hs.orthUc hs.orthVc ha hs.nonneg hτ M
      have h8 : ‖((1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ) - Uc * diagonal τ * Vcᵀ) * M‖ ≤
          (b - a) / 4 * ‖M‖ :=
        (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h6.le (norm_nonneg _))
      have h9 : (1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ) * M =
          ((1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ) - Uc * diagonal τ * Vcᵀ) * M +
            Uc * diagonal τ * (Vcᵀ * M) := by
        rw [Matrix.sub_mul ((1 - U t * (U t)ᵀ) * W t * (1 - V t * (V t)ᵀ)),
          Matrix.mul_assoc (Uc * diagonal τ)]
        abel
      rw [h9]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hρ₁ : 0 ≤ a + (b - a) / 4 := by linarith
    have hρ : a + (b - a) / 4 < b - (b - a) / 4 := by linarith
    exact ⟨h1, h2, isBestApprox_of_bounds h1 h2 h3 h4 hρ₁ hρ.le hlow hup,
      fun C hC => eq_of_isBestApprox h1 h2 h3 h4 hρ₁ hρ hlow hup hC⟩
  · rw [← hf₁]
    exact hgU
  · rw [← hf₂]
    exact hgV
  · rw [← hf₁]
    exact hU
  · rw [← hf₂]
    exact hV
  · rw [hUt, hVt] at hSd
    exact hSd

/-- **The best rank-`r` approximation is differentiable** (arXiv 2609.32615, Thm 3.1, "its
derivative is given by"): under the hypotheses of `bestApprox_flow`, the truncated SVD `W_r(t)`
(the library's `EckartYoung.truncation`, the unique best approximation of rank `≤ r` near `t₀`)
has at `t₀` the derivative `U̇ Σ_r V₀ᵀ + U₀ Ṡ V₀ᵀ + U₀ Σ_r V̇ᵀ` with `U̇`, `Ṡ`, `V̇` from (18).  The
same holds for any other choice of best approximations, by uniqueness. -/
theorem hasDerivAt_truncation {W : ℝ → Matrix m n ℝ} {G : Matrix m n ℝ} {t₀ : ℝ}
    (hW : HasDerivAt W (-G) t₀) {U₀ : Matrix m (Fin r) ℝ} {σ : Fin r → ℝ}
    {V₀ : Matrix n (Fin r) ℝ} {Uc : Matrix m (Fin k) ℝ} {τ : Fin k → ℝ}
    {Vc : Matrix n (Fin k) ℝ} (hs : IsPartitionedSVD (W t₀) U₀ σ V₀ Uc τ Vc) :
    HasDerivAt (fun t => EckartYoung.truncation (W t) r)
      (flowU G U₀ V₀ Uc Vc σ τ * diagonal σ * V₀ᵀ + U₀ * -(U₀ᵀ * G * V₀) * V₀ᵀ +
        U₀ * diagonal σ * (flowU Gᵀ V₀ U₀ Vc Uc σ τ)ᵀ) t₀ := by
  obtain ⟨U, S, V, hU₀, hS₀, hV₀, hev, -, -, hU, hV, hS⟩ := bestApprox_flow hW hs
  have h := Frobenius.hasDerivAt_mul_mul hU hS (Frobenius.hasDerivAt_transpose hV)
  rw [hU₀, hS₀, hV₀] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact ht.2.2.2 _ ⟨EckartYoung.rank_truncation_le _ _,
    fun C hC => EckartYoung.norm_sub_truncation_le _ hC⟩

/-- The splitting (16) of the coefficient `C_{ji}` into the DLRA part and the curvature
correction. -/
lemma coupled_coeff {s t a b : ℝ} (hst : s ^ 2 - t ^ 2 ≠ 0) :
    -(s * a + t * b) / (s ^ 2 - t ^ 2) * s =
      -a - (t ^ 2 / (s ^ 2 - t ^ 2) * a + s * t / (s ^ 2 - t ^ 2) * b) := by
  field_simp
  ring

/-- **Thm 3.1 of arXiv 2609.32615 for a complete SVD: the coefficient form (14).**  If `U⊥`
completes `U` (`U Uᵀ + U⊥ U⊥ᵀ = I`), then `U̇ = U⊥ C` with
`C_{ji} = -(σᵢ a_{ji} + σ_{r+j} b_{ji}) / (σᵢ² - σ_{r+j}²)`, `a_{ji} = u_{r+j}ᵀ G vᵢ`,
`b_{ji} = uᵢᵀ G v_{r+j}`.  Without completeness (for instance `r + k < m`, a rectangular `W`)
the expansion `U̇ = U⊥ C` of the paper fails, whereas (18) stays true. -/
theorem flowU_eq_of_complete {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {Uc : Matrix m (Fin k) ℝ} {Vc : Matrix n (Fin k) ℝ} {σ : Fin r → ℝ} {τ : Fin k → ℝ}
    (G : Matrix m n ℝ) (hV : Vᵀ * V = 1) (hσ : ∀ i, σ i ≠ 0)
    (hne : ∀ i j, σ i ^ 2 - τ j ^ 2 ≠ 0) (hcomp : U * Uᵀ + Uc * Ucᵀ = 1) :
    flowU G U V Uc Vc σ τ = Uc * Matrix.of fun j i =>
      -(σ i * (Ucᵀ * G * V) j i + τ j * (Uᵀ * G * Vc) i j) / (σ i ^ 2 - τ j ^ 2) := by
  have hunit : IsUnit (diagonal σ).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hσ i
  set M : Matrix (Fin k) (Fin r) ℝ := fun j i =>
    coupleP σ τ i j * (Ucᵀ * G * V) j i + coupleQ σ τ i j * (Uᵀ * G * Vc) i j with hM
  set C : Matrix (Fin k) (Fin r) ℝ := Matrix.of fun j i =>
    -(σ i * (Ucᵀ * G * V) j i + τ j * (Uᵀ * G * Vc) i j) / (σ i ^ 2 - τ j ^ 2) with hC
  have hsum : (∑ i, ∑ j, (coupleP σ τ i j * (Ucᵀ * G * V) j i +
      coupleQ σ τ i j * (Uᵀ * G * Vc) i j) • vecMulVec (Ucᵀ j) (Vᵀ i)) = Uc * M * Vᵀ :=
    sum_vecMulVec_eq Uc V M
  have hCS : C * diagonal σ = -(Ucᵀ * G * V) - M := by
    ext j i
    rw [Matrix.mul_diagonal, Matrix.sub_apply, Matrix.neg_apply]
    exact coupled_coeff (hne i j)
  have hP : (1 - U * Uᵀ) = Uc * Ucᵀ := by
    rw [← hcomp]
    abel
  have h1 : Uc * C = (-((1 - U * Uᵀ) * G * V) - Uc * M) * (diagonal σ)⁻¹ := by
    calc Uc * C = Uc * C * (diagonal σ * (diagonal σ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
      _ = Uc * (C * diagonal σ) * (diagonal σ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hCS, hP, Matrix.mul_sub, Matrix.mul_neg]
          simp only [Matrix.mul_assoc]
  rw [h1, flowU, hsum, Matrix.mul_assoc (Uc * M), hV, Matrix.mul_one,
    Matrix.sub_mul (-((1 - U * Uᵀ) * G * V)), Matrix.neg_mul]

/-- Two disjoint column blocks of a matrix with orthonormal columns are orthogonal. -/
lemma cross_submatrix {l : Type*} [Fintype l] {P : Matrix l (Fin (r + k)) ℝ} (hP : Pᵀ * P = 1) :
    (P.submatrix id (Fin.natAdd r))ᵀ * P.submatrix id (Fin.castAdd k) = 0 := by
  ext j i
  have hne : Fin.natAdd r j ≠ Fin.castAdd k i := fun h => by
    have h1 := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
    have := i.2
    omega
  rw [transpose_submatrix_mul_submatrix, hP]
  simp [Matrix.one_apply_ne hne]

/-- **Non-vacuity of Thm 3.1: every gap comes with a partitioned SVD.**  If
`σ_{r+1}(A) < σ_r(A)` (`1`-based indices as in the paper; `singularValues r < singularValues
(r - 1)` here), the thin SVD of `A` splits into the partitioned SVD (5) with `k = rank A - r`.
(arXiv 2609.32615, Thm 3.1.) -/
theorem exists_partitionedSVD (A : Matrix m n ℝ) {r : ℕ} (hr : 0 < r)
    (hgap : (toEuclideanLin A).singularValues r < (toEuclideanLin A).singularValues (r - 1)) :
    ∃ (k : ℕ) (U : Matrix m (Fin r) ℝ) (σ : Fin r → ℝ) (V : Matrix n (Fin r) ℝ)
      (Uc : Matrix m (Fin k) ℝ) (τ : Fin k → ℝ) (Vc : Matrix n (Fin k) ℝ),
      IsPartitionedSVD A U σ V Uc τ Vc ∧ (∀ i, σ i = (toEuclideanLin A).singularValues i) ∧
        ∀ j, τ j = (toEuclideanLin A).singularValues (r + j) := by
  have hpos : 0 < (toEuclideanLin A).singularValues (r - 1) :=
    lt_of_le_of_lt ((toEuclideanLin A).singularValues_nonneg r) hgap
  have hrk : r ≤ A.rank := by
    have h1 := (toEuclideanLin A).singularValues_pos_iff_lt_finrank_range.mp hpos
    rw [← SVD.rank_eq_finrank_range] at h1
    omega
  obtain ⟨k, hk⟩ : ∃ k, A.rank = r + k := ⟨A.rank - r, by omega⟩
  obtain ⟨U, V, σ, hU, hV, -, hσpos, hσ, hA⟩ := SVD.exists_svd A hk
  have hanti := (toEuclideanLin A).singularValues_antitone
  refine ⟨k, U.submatrix id (Fin.castAdd k), fun i => σ (Fin.castAdd k i),
    V.submatrix id (Fin.castAdd k), U.submatrix id (Fin.natAdd r), fun j => σ (Fin.natAdd r j),
    V.submatrix id (Fin.natAdd r), ⟨?_, ?_, ?_, ?_, cross_submatrix hU, cross_submatrix hV,
      fun _ => hσpos _, fun _ => (hσpos _).le, ?_, ?_⟩, fun i => hσ _, fun j => hσ _⟩
  · rw [transpose_submatrix_mul_submatrix, hU]
    exact Matrix.submatrix_one _ (Fin.castAdd_injective _ _)
  · rw [transpose_submatrix_mul_submatrix, hV]
    exact Matrix.submatrix_one _ (Fin.castAdd_injective _ _)
  · rw [transpose_submatrix_mul_submatrix, hU]
    exact Matrix.submatrix_one _ (Fin.natAdd_injective _ _)
  · rw [transpose_submatrix_mul_submatrix, hV]
    exact Matrix.submatrix_one _ (Fin.natAdd_injective _ _)
  · intro i j
    rw [hσ, hσ]
    have h1 : (toEuclideanLin A).singularValues (Fin.natAdd r j : ℕ) ≤
        (toEuclideanLin A).singularValues r := hanti (by simp)
    have h2 : (toEuclideanLin A).singularValues (r - 1) ≤
        (toEuclideanLin A).singularValues (Fin.castAdd k i : ℕ) :=
      hanti (by have := i.2; simp; omega)
    linarith
  · conv_lhs => rw [hA]
    ext a b
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
    rw [Fin.sum_univ_add]

end BestFlow

/-- The local singular-value tail of this file, replaced by the core `LeanDLRA.tailSqSum` (same
definition). -/
@[deprecated (since := "2026-11-09")] alias tailSq := LeanDLRA.tailSqSum

end LeanDLRA.Literature.P2609_32615
