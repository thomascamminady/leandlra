import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Integrators.ParallelBUG

/-!
# The parallel BUG integrator for matrices

This file instantiates the abstract robust error analysis of the *parallel* basis-update &
Galerkin integrator (`LeanDLRA/Integrators/ParallelBUG.lean`) for real `m × n` matrices with
the Frobenius norm, **at the level of the factors** computed by the algorithm of

* G. Ceruti, J. Kusch, Ch. Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, [CerutiKuschLubich2024] (SIAM J. Sci. Comput. 2024), §3.1 (algorithm), (3.4)
  (augmented coefficient matrix), (4.1) (local error) and **Theorem 4.1** (global error).

## The algorithm ([CerutiKuschLubich2024, §3.1])

From `Y₀ = U₀ S₀ V₀ᵀ` (`U₀ᵀ U₀ = I`, `V₀ᵀ V₀ = I`), a step `t₀ → t₁` computes in parallel

* K-step (3.1): `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`; new directions `Ũ₁` with
  `Ũ₁ᵀ U₀ = 0` whose range contains `(I - U₀U₀ᵀ) K(t₁)`, so that the range of `Û = (U₀, Ũ₁)`
  contains the range of `(U₀, K(t₁))`;
* L-step (3.2): `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ`; likewise `Ṽ₁` with `Ṽ₁ᵀ V₀ = 0`
  capturing `(I - V₀V₀ᵀ) L(t₁)`;
* S-step (3.3): `S̄' = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`, `S̄(t₀) = S₀` (Galerkin step in the old basis);

and forms the augmented coefficient matrix (3.4)
`Ŝ₁ = [[S̄(t₁), L(t₁)ᵀ Ṽ₁], [Ũ₁ᵀ K(t₁), 0]]` (`augCoeff`) and `Ŷ₁ = Û Ŝ₁ V̂ᵀ` (`augmented`),
which is then truncated to `Y₁` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`.

## Main results

* `augmented_eq_sum`: `Û Ŝ₁ V̂ᵀ = U₀ S̄ V₀ᵀ + U₀ L(t₁)ᵀ Ṽ₁Ṽ₁ᵀ + Ũ₁Ũ₁ᵀ K(t₁) V₀ᵀ`;
  `augmented_eq_parallelBUG`: with the capture properties this is the abstract update
  `Ŷ₁ = YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁)` (`parallelBUG`), where
  `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`, `YK = K V₀ᵀ`, `YL = U₀ Lᵀ`, `YS = U₀ S̄ V₀ᵀ`.
* `normal_augmented_eq_zero`, `tangent_augmented_eq`: the zero block of `Ŝ₁` means
  `(I - U₀U₀ᵀ) Ŷ₁ (I - V₀V₀ᵀ) = 0`, i.e. `Ŷ₁` lies in the tangent space at `Y₀` (purely
  algebraic: only `U₀ᵀ U₀ = I` and `V₀ᵀ V₀ = I` are used).
* `IsStep.isParallelBUGStep`: the factor trajectories satisfy all hypotheses of the abstract
  step `IsParallelBUGStep`.
* `IsStep.local_error` ([CerutiKuschLubich2024], (4.1) before truncation, explicit constants): if
  the normal component at the starting value satisfies `‖(I - U₀U₀ᵀ) F(t, Y₀) (I - V₀V₀ᵀ)‖ ≤ ε` on
  `[t₀, t₁)`, then `‖Û Ŝ₁ V̂ᵀ - A(t₁)‖ ≤ h (7 L B h + ε)`; `IsStep.local_error_truncated` adds the
  truncation error `ϑ`; `IsStep.local_error_of_timeLipschitz` needs the bound only at `(t₀, Y₀)`.
* `IsStep.orthonormal_capture`: with orthonormal `Ũ₁`, the augmented basis `Û` is orthonormal
  and spans `K(t₁)` and `U₀` (as in the paper); `exists_compl_capture`: such `Ũ₁` with `r`
  columns exist if `2 r ≤ m`; `compl_capture_proj`: for every `m`, `Ũ₁ = I - U₀U₀ᵀ` is an
  admissible choice of new directions.
* `global_error_paper` (**Theorem 4.1** of [CerutiKuschLubich2024], verbatim form): for the
  rank-adaptive parallel integrator with ranks `rₖ` changing from step to step, truncation
  tolerance `ϑ` and Assumption 2 of the paper exactly as stated,
  `‖(I - UₖUₖᵀ) F(tₖ, Yₖ) (I - VₖVₖᵀ)‖ ≤ ε` at the grid points,
  `‖Yₖ - A(tₖ)‖ ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h` with `C₀ = e^{LT}`,
  `C₁ = (7 L B + Lₜ) T e^{LT}`, `C₂ = C₃ = T e^{LT}` (`Lₜ`: Lipschitz constant of `F` in time);
  `global_error_of_timeLipschitz` is the underlying `e^{LT}(δ + …)` form, and `global_error`,
  `global_error_constants` are the variants with the normal-component bound on each
  `[tₖ, tₖ₊₁)` at the iterates `Yₖ` and no time regularity.
* Satisfiability: a bounded, Lipschitz, non-constant field `F(t, Y) = φ(Y₁₁) C` (`φ` the clamp
  to `[-1, 1]`, `C = [[0, 1], [1, 1]]`, so `L = B = ‖C‖ > 0`) on `2 × 2` matrices; from
  `Y₀ = e₁ e₁ᵀ` the normal component of `F(t, Y₀)` is the nonzero `e₂ e₂ᵀ`, and `ε` is taken
  to be exactly its norm.  `example`s instantiate `IsStep.local_error` and a two-step run of
  `global_error_paper` and `global_error` in which the rank grows from `1` to `2`.

## Implementation notes

`Ṽ` is not a valid Lean identifier, so in the code the new directions `Ũ₁`, `Ṽ₁` are called
`U₁`, `V₁` (and `W k`, `Z k` for step `k` in the global theorems).

## Deviations from the paper

* The new directions `Ũ₁`, `Ṽ₁` may have any number of columns (the paper uses `r` columns,
  possibly zero columns in the rank-deficient case), and their orthonormality is not needed for
  the identity `Û Ŝ₁ V̂ᵀ = Ŷ₁` nor for the error bounds: only `Ũ₁ᵀ U₀ = 0` and the capture of
  `(I - U₀U₀ᵀ) K(t₁)` are used.  This covers the zero-filled `Ũ₁` of the paper.
* The paper's Assumption 2 (`‖P⊥_{rₙ}(Yₙ) F(tₙ, Yₙ)‖ ≤ ε`) is imposed only at the iterates
  `Yₖ = Uₖ Sₖ Vₖᵀ` themselves, in the factored form `(I - UₖUₖᵀ) Z (I - VₖVₖᵀ)`, which is
  `P⊥_{rₖ}(Yₖ) Z` when `Sₖ` is invertible.  In `global_error_paper` it is imposed at the grid
  points `(tₖ, Yₖ)` only, as in the paper; this requires `F` to be Lipschitz in time as well
  (our reading of the paper's Assumption 1, "F is bounded and Lipschitz continuous"), with the
  time-Lipschitz constant `Lₜ` entering `C₁`.  `global_error` and `global_error_constants`
  instead impose it for `t ∈ [tₖ, tₖ₊₁)` (still only at `Yₖ`) and need no time regularity.
* The truncation (SVD) is abstracted to `‖Yₖ₊₁ - Ŷₖ₊₁‖ ≤ ϑ`; the substep solutions and exact
  flows are hypotheses (`ODESolution`), as in the abstract file.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixParallelBUG

open MatrixKSL (kField lField odeSolution_kField odeSolution_lField odeSolution_comp_clm
  odeSolution_affine)

/-! ### The S-step field -/

section Fields

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- The Galerkin S-step field `S̄ ↦ U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀` ([CerutiKuschLubich2024], (3.3)). -/
def sField (U₀ : Matrix m r ℝ) (V₀ : Matrix n r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (S : Matrix r r ℝ) : Matrix r r ℝ :=
  U₀ᵀ * F t (U₀ * S * V₀ᵀ) * V₀

/-- **S-step lift.**  If `S̄' = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`, then `YS = U₀ S̄ V₀ᵀ` solves
`YS' = P₀ Q₀ F(t, YS)` with `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`. -/
theorem odeSolution_sField {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {U₀ : Matrix m r ℝ}
    {V₀ : Matrix n r ℝ} {S : ℝ → Matrix r r ℝ} {t₀ t₁ : ℝ}
    (hS : ODESolution (sField U₀ V₀ F) S t₀ t₁) :
    ODESolution (fun t x => leftProj U₀ (rightProj V₀ (F t x))) (fun t => U₀ * S t * V₀ᵀ)
      t₀ t₁ :=
  odeSolution_comp_clm hS ((Frobenius.rightMulCLM V₀ᵀ).comp (Frobenius.leftMulCLM U₀))
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftProj_rightProj_apply, sField]

end Fields

/-! ### The augmented coefficient matrix -/

section Blocks

variable {m n r s s' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s] [Fintype s']

/-- **The augmented coefficient matrix** ([CerutiKuschLubich2024], (3.4)):
`Ŝ₁ = [[S̄(t₁), L(t₁)ᵀ Ṽ₁], [Ũ₁ᵀ K(t₁), 0]]`, given `S̄ = S̄(t₁)`, `K₁ = K(t₁)`,
`L₁ = L(t₁)` and the new directions `Ũ₁`, `Ṽ₁`. -/
def augCoeff (Sbar : Matrix r r ℝ) (U₁ : Matrix m s ℝ) (V₁ : Matrix n s' ℝ) (K₁ : Matrix m r ℝ)
    (L₁ : Matrix n r ℝ) : Matrix (r ⊕ s) (r ⊕ s') ℝ :=
  Matrix.fromBlocks Sbar (L₁ᵀ * V₁) (U₁ᵀ * K₁) 0

/-- **The untruncated parallel BUG result** `Ŷ₁ = Û Ŝ₁ V̂ᵀ` with the augmented bases
`Û = (U₀, Ũ₁)`, `V̂ = (V₀, Ṽ₁)` ([CerutiKuschLubich2024, §3.1], step 2). -/
def augmented (U₀ : Matrix m r ℝ) (U₁ : Matrix m s ℝ) (V₀ : Matrix n r ℝ) (V₁ : Matrix n s' ℝ)
    (Sbar : Matrix r r ℝ) (K₁ : Matrix m r ℝ) (L₁ : Matrix n r ℝ) : Matrix m n ℝ :=
  Matrix.fromCols U₀ U₁ * augCoeff Sbar U₁ V₁ K₁ L₁ * (Matrix.fromCols V₀ V₁)ᵀ

/-- **Block expansion of `Û Ŝ₁ V̂ᵀ`**:
`Û Ŝ₁ V̂ᵀ = U₀ S̄ V₀ᵀ + U₀ L(t₁)ᵀ Ṽ₁Ṽ₁ᵀ + Ũ₁Ũ₁ᵀ K(t₁) V₀ᵀ`. -/
theorem augmented_eq_sum (U₀ : Matrix m r ℝ) (U₁ : Matrix m s ℝ) (V₀ : Matrix n r ℝ)
    (V₁ : Matrix n s' ℝ) (Sbar : Matrix r r ℝ) (K₁ : Matrix m r ℝ) (L₁ : Matrix n r ℝ) :
    augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁ =
      U₀ * Sbar * V₀ᵀ + U₀ * L₁ᵀ * (V₁ * V₁ᵀ) + U₁ * U₁ᵀ * K₁ * V₀ᵀ := by
  rw [augmented, augCoeff, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, Matrix.add_mul, Matrix.mul_assoc]
  abel

variable [DecidableEq m] [DecidableEq n]

/-- **The zero block of `Ŝ₁`** ([CerutiKuschLubich2024], (3.4)): if `U₀ᵀ U₀ = I` and `V₀ᵀ V₀ = I`,
the doubly normal component of `Ŷ₁ = Û Ŝ₁ V̂ᵀ` vanishes, `(I - U₀U₀ᵀ) Ŷ₁ (I - V₀V₀ᵀ) = 0`,
for any new directions `Ũ₁`, `Ṽ₁` and any `S̄`, `K₁`, `L₁` (a purely algebraic fact). -/
theorem normal_augmented_eq_zero [DecidableEq r] {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (U₁ : Matrix m s ℝ) (V₁ : Matrix n s' ℝ)
    (Sbar : Matrix r r ℝ) (K₁ : Matrix m r ℝ) (L₁ : Matrix n r ℝ) :
    (1 - U₀ * U₀ᵀ) * augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁ * (1 - V₀ * V₀ᵀ) = 0 := by
  have hU : ∀ X : Matrix r n ℝ, (1 - U₀ * U₀ᵀ) * (U₀ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU₀,
      Matrix.mul_one, sub_self, Matrix.zero_mul]
  have hV : V₀ᵀ * (1 - V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV₀, Matrix.one_mul, sub_self]
  rw [augmented_eq_sum]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hV, Matrix.mul_zero, hU,
    Matrix.zero_mul, add_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- **`Ŷ₁` lies in the tangent space at `Y₀`**: `P(Y₀) Ŷ₁ = Ŷ₁` for the tangent projector
`P(Y₀) Z = U₀U₀ᵀ Z + Z V₀V₀ᵀ - U₀U₀ᵀ Z V₀V₀ᵀ` (only `U₀ᵀ U₀ = I`, `V₀ᵀ V₀ = I` are used). -/
theorem tangent_augmented_eq [DecidableEq r] {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (U₁ : Matrix m s ℝ) (V₁ : Matrix n s' ℝ)
    (Sbar : Matrix r r ℝ) (K₁ : Matrix m r ℝ) (L₁ : Matrix n r ℝ) :
    tangentProj U₀ V₀ (augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁) = augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁ := by
  classical
  have h := tangentProj_add_normal U₀ V₀ (augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁)
  rwa [normal_augmented_eq_zero hU₀ hV₀, add_zero] at h

omit [Fintype n] [DecidableEq n] in
/-- If `Ũᵀ U₀ = 0` and `Ũ Ũᵀ` fixes `(I - U₀U₀ᵀ) K`, then `Ũ Ũᵀ K = (I - U₀U₀ᵀ) K`. -/
theorem capture_compl {U₀ : Matrix m r ℝ} {U₁ : Matrix m s ℝ} {K₁ : Matrix m r ℝ}
    (hperp : U₁ᵀ * U₀ = 0) (hcap : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K₁) = (1 - U₀ * U₀ᵀ) * K₁) :
    U₁ * U₁ᵀ * K₁ = (1 - U₀ * U₀ᵀ) * K₁ := by
  have h : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K₁) = U₁ * U₁ᵀ * K₁ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      show U₁ * U₁ᵀ * (U₀ * U₀ᵀ * K₁) = U₁ * (U₁ᵀ * U₀) * U₀ᵀ * K₁ by simp only [Matrix.mul_assoc],
      hperp, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
  rw [← h, hcap]

omit [Fintype m] [DecidableEq m] in
/-- The right-hand version of `capture_compl`, transposed:
`L₁ᵀ Ṽ Ṽᵀ = L₁ᵀ (I - V₀V₀ᵀ)`. -/
theorem capture_compl_right {V₀ : Matrix n r ℝ} {V₁ : Matrix n s' ℝ} {L₁ : Matrix n r ℝ}
    (hperp : V₁ᵀ * V₀ = 0) (hcap : V₁ * V₁ᵀ * ((1 - V₀ * V₀ᵀ) * L₁) = (1 - V₀ * V₀ᵀ) * L₁) :
    L₁ᵀ * (V₁ * V₁ᵀ) = L₁ᵀ * (1 - V₀ * V₀ᵀ) := by
  have h := congrArg Matrix.transpose (capture_compl hperp hcap)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.mul_assoc] using h

/-- **The paper's `Û Ŝ₁ V̂ᵀ` is the abstract parallel BUG update** (follows from
[CerutiKuschLubich2024, §3.1] and (3.4); the paper does not state this identity explicitly, §3.2
only compares the blocks of (3.4) with the BUG coefficients up to `O(h²)`). If the new directions
satisfy `Ũᵀ U₀ = 0`, `Ṽᵀ V₀ = 0` and capture `(I - U₀U₀ᵀ) K₁` and `(I - V₀V₀ᵀ) L₁`, then
`Û Ŝ₁ V̂ᵀ = YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁)` with `P₀ = leftProj U₀`,
`Q₀ = rightProj V₀`, `YK(t₁) = K₁ V₀ᵀ`, `YL(t₁) = U₀ L₁ᵀ`, `YS(t₁) = U₀ S̄ V₀ᵀ`. No orthonormality
is needed for this identity. -/
theorem augmented_eq_parallelBUG {U₀ : Matrix m r ℝ} {U₁ : Matrix m s ℝ} {V₀ : Matrix n r ℝ}
    {V₁ : Matrix n s' ℝ} (Sbar : Matrix r r ℝ) {K₁ : Matrix m r ℝ} {L₁ : Matrix n r ℝ}
    (hpU : U₁ᵀ * U₀ = 0) (hcU : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K₁) = (1 - U₀ * U₀ᵀ) * K₁)
    (hpV : V₁ᵀ * V₀ = 0) (hcV : V₁ * V₁ᵀ * ((1 - V₀ * V₀ᵀ) * L₁) = (1 - V₀ * V₀ᵀ) * L₁) :
    augmented U₀ U₁ V₀ V₁ Sbar K₁ L₁ =
      parallelBUG (leftProj U₀) (rightProj V₀) (K₁ * V₀ᵀ) (U₀ * L₁ᵀ) (U₀ * Sbar * V₀ᵀ) := by
  rw [augmented_eq_sum, parallelBUG, one_sub_leftProj_apply, one_sub_rightProj_apply,
    Matrix.mul_assoc U₀ L₁ᵀ, capture_compl_right hpV hcV, capture_compl hpU hcU,
    Matrix.mul_assoc (1 - U₀ * U₀ᵀ) K₁, ← Matrix.mul_assoc U₀ L₁ᵀ]
  abel

end Blocks

/-! ### One step of the matrix parallel BUG integrator -/

section Step

variable {m n r s s' : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s] [Fintype s']
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- **One step of the matrix parallel BUG integrator** from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`
([CerutiKuschLubich2024, §3.1], step 1), at the factor level: the K-, L- and S-steps (3.1)–(3.3) and
the new directions `Ũ₁` (`Ũ₁ᵀ U₀ = 0`, capturing `(I - U₀U₀ᵀ) K(t₁)`) and `Ṽ₁` (`Ṽ₁ᵀ V₀ = 0`,
capturing `(I - V₀V₀ᵀ) L(t₁)`).  The untruncated result is
`augmented U₀ Ũ₁ V₀ Ṽ₁ (S̄ t₁) (K t₁) (L t₁) = Û Ŝ₁ V̂ᵀ`. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m s ℝ) (V₁ : Matrix n s' ℝ)
    (K : ℝ → Matrix m r ℝ) (Lf : ℝ → Matrix n r ℝ) (Sb : ℝ → Matrix r r ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step (3.1): `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step (3.2): `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  /-- S-step (3.3): `S̄' = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`. -/
  sSol : ODESolution (sField U₀ V₀ F) Sb t₀ t₁
  sStart : Sb t₀ = S₀
  /-- The new left directions are orthogonal to `U₀`. -/
  perpU : U₁ᵀ * U₀ = 0
  /-- `Û = (U₀, Ũ₁)` captures `(U₀, K(t₁))`: its range contains the range of `(U₀, K(t₁))`
  (`Ũ₁` may contain further directions and need not be orthonormal). -/
  capU : U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K t₁) = (1 - U₀ * U₀ᵀ) * K t₁
  /-- The new right directions are orthogonal to `V₀`. -/
  perpV : V₁ᵀ * V₀ = 0
  /-- `V̂ = (V₀, Ṽ₁)` captures `(V₀, L(t₁))`: its range contains the range of `(V₀, L(t₁))`
  (`Ṽ₁` may contain further directions and need not be orthonormal). -/
  capV : V₁ * V₁ᵀ * ((1 - V₀ * V₀ᵀ) * Lf t₁) = (1 - V₀ * V₀ᵀ) * Lf t₁

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m s ℝ} {V₁ : Matrix n s' ℝ}
  {K : ℝ → Matrix m r ℝ} {Lf : ℝ → Matrix n r ℝ} {Sb : ℝ → Matrix r r ℝ}

namespace IsStep

/-- **The factor trajectories satisfy the abstract hypotheses.**  One step of the matrix
parallel BUG integrator gives an abstract step `IsParallelBUGStep` with `P₀ = leftProj U₀`,
`Q₀ = rightProj V₀`, `Y₀ = U₀ S₀ V₀ᵀ` and full-space trajectories `YK = K V₀ᵀ`,
`YL = U₀ Lᵀ`, `YS = U₀ S̄ V₀ᵀ`. -/
theorem isParallelBUGStep (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    IsParallelBUGStep F (leftProj U₀) (rightProj V₀) t₀ t₁ (U₀ * S₀ * V₀ᵀ)
      (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ) (fun t => U₀ * Sb t * V₀ᵀ) where
  orthP := isOrthProj_leftProj hs.orthU₀
  orthQ := isOrthProj_rightProj hs.orthV₀
  comm := leftProj_rightProj_comm U₀ V₀
  fixP := by
    rw [Matrix.mul_assoc]
    exact leftProj_mul_left hs.orthU₀ _
  fixQ := rightProj_mul_transpose hs.orthV₀ _
  solK := odeSolution_kField hs.kSol
  initK := by simp only [hs.kStart]
  solL := odeSolution_lField hs.lSol
  initL := by
    simp only [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  solS := odeSolution_sField hs.sSol
  initS := by simp only [hs.sStart]

/-- Along a step, `Û Ŝ₁ V̂ᵀ` is the abstract update
`Ŷ₁ = YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁)`. -/
theorem augmented_eq (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) =
      parallelBUG (leftProj U₀) (rightProj V₀) (K t₁ * V₀ᵀ) (U₀ * (Lf t₁)ᵀ)
        (U₀ * Sb t₁ * V₀ᵀ) :=
  augmented_eq_parallelBUG _ hs.perpU hs.capU hs.perpV hs.capV

/-- **The zero block of `Ŝ₁`** ([CerutiKuschLubich2024], (3.4)) along a step:
`(I - U₀U₀ᵀ) Ŷ₁ (I - V₀V₀ᵀ) = 0` (see `normal_augmented_eq_zero`; no ODE property is used). -/
theorem normal_eq_zero (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    (1 - U₀ * U₀ᵀ) * augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) * (1 - V₀ * V₀ᵀ) = 0 :=
  normal_augmented_eq_zero hs.orthU₀ hs.orthV₀ _ _ _ _ _

/-- **`Ŷ₁` lies in the tangent space at `Y₀`** along a step: `P(Y₀) Ŷ₁ = Ŷ₁` for the tangent
projector `P(Y₀) Z = U₀U₀ᵀ Z + Z V₀V₀ᵀ - U₀U₀ᵀ Z V₀V₀ᵀ` (see `tangent_augmented_eq`). -/
theorem tangent_eq (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) :
    tangentProj U₀ V₀ (augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)) =
      augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) :=
  tangent_augmented_eq hs.orthU₀ hs.orthV₀ _ _ _ _ _

/-- With orthonormal new directions `Ũ₁ᵀ Ũ₁ = I`, the augmented basis `Û = (U₀, Ũ₁)` has
orthonormal columns and spans both `K(t₁)` and `U₀`, as required in [CerutiKuschLubich2024, §3.1] -/
theorem orthonormal_capture [DecidableEq s] (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hU₁ : U₁ᵀ * U₁ = 1) :
    (Matrix.fromCols U₀ U₁)ᵀ * Matrix.fromCols U₀ U₁ = 1 ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * K t₁ = K t₁ ∧
      Matrix.fromCols U₀ U₁ * (Matrix.fromCols U₀ U₁)ᵀ * U₀ = U₀ :=
  fromCols_orthonormal_capture hs.orthU₀ hU₁ hs.perpU hs.capU

variable {L B : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Robust local error of the matrix parallel BUG integrator** ([CerutiKuschLubich2024], (4.1)
before truncation, with explicit constants `c₁ = 7 L B`, `c₂ = 1`). Let `F` be `L`-Lipschitz
(`L ≥ 0`) and bounded by `B` in the Frobenius norm, and let the normal component of `F` at the
starting value `Y₀ = U₀ S₀ V₀ᵀ` satisfy `‖(I - U₀U₀ᵀ) F(t, Y₀) (I - V₀V₀ᵀ)‖ ≤ ε` for
`t ∈ [t₀, t₁)`.  If `A' = F(t, A)`, `A(t₀) = Y₀`, then for one parallel BUG step (`IsStep`) on
`[t₀, t₁]`

    ‖Û Ŝ₁ V̂ᵀ - A(t₁)‖ ≤ h (7 L B h + ε),   h = t₁ - t₀,

independently of singular values. -/
theorem local_error (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (ht : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) - A t₁‖ ≤
      (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) := by
  rw [hs.augmented_eq]
  exact hs.isParallelBUGStep.local_error hF hL hB ht hA hA₀ fun t ht' => by
    rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact hε t ht'

/-- **Robust local error after truncation** ([CerutiKuschLubich2024], (4.1)): if the truncated
approximation satisfies `‖Y₁ - Û Ŝ₁ V̂ᵀ‖ ≤ ϑ`, then `‖Y₁ - A(t₁)‖ ≤ h (7 L B h + ε) + ϑ`
(under the hypotheses of `local_error`). -/
theorem local_error_truncated (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (ht : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {Y₁ : Matrix m n ℝ} {ϑ : ℝ}
    (htr : ‖Y₁ - augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)‖ ≤ ϑ) :
    ‖Y₁ - A t₁‖ ≤ (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) + ϑ := by
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁)‖
        + ‖augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) :=
        add_le_add htr (hs.local_error hF hL hB hε ht hA hA₀)
    _ = _ := add_comm _ _

/-- **Local error with the normal-component bound only at `(t₀, Y₀)`** ([CerutiKuschLubich2024],
(3.10)): if `‖(I - U₀U₀ᵀ) F(t₀, Y₀) (I - V₀V₀ᵀ)‖ ≤ ε` and `F(·, Y₀)` is `Lₜ`-Lipschitz in time
on the step, then `‖Û Ŝ₁ V̂ᵀ - A(t₁)‖ ≤ h ((7 L B + Lₜ) h + ε)`, `h = t₁ - t₀`. -/
theorem local_error_of_timeLipschitz (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε Lt : ℝ}
    (hLt : 0 ≤ Lt)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t (U₀ * S₀ * V₀ᵀ) - F t₀ (U₀ * S₀ * V₀ᵀ)‖ ≤ Lt * |t - t₀|)
    (ht : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖augmented U₀ U₁ V₀ V₁ (Sb t₁) (K t₁) (Lf t₁) - A t₁‖ ≤
      (t₁ - t₀) * ((7 * L * B + Lt) * (t₁ - t₀) + ε) := by
  rw [hs.augmented_eq]
  have h := hs.isParallelBUGStep
  have hε' : ‖(1 - leftProj U₀) ((1 - rightProj V₀) (F t₀ (U₀ * S₀ * V₀ᵀ)))‖ ≤ ε := by
    rw [one_sub_leftProj_one_sub_rightProj_apply]; exact hε
  exact parallelBUG_local_error_of_timeLipschitz (YK := fun t => K t * V₀ᵀ)
    (YL := fun t => U₀ * (Lf t)ᵀ) (YS := fun t => U₀ * Sb t * V₀ᵀ) hF hL hB hLt h.orthP h.orthQ
    h.comm ht h.fixP h.fixQ hA hA₀ h.solK h.initK h.solL h.initL h.solS h.initS hε' hFt

end IsStep

end Step

/-! ### Existence of the new directions -/

/-- **Existence of orthonormal new directions** ([CerutiKuschLubich2024, §3.1], "orthonormal basis
of the range of `(U₀, K(t₁))`"): for `U₀ ∈ ℝ^{m×r}` with orthonormal columns, `K₁ ∈ ℝ^{m×r}` and
`2 r ≤ m`, there is `Ũ₁ ∈ ℝ^{m×r}` with orthonormal columns, `Ũ₁ᵀ U₀ = 0`, capturing
`(I - U₀U₀ᵀ) K₁`. (The same lemma applied to `V₀`, `L(t₁)` gives `Ṽ₁`.) Without `2 r ≤ m`, see
`compl_capture_proj`. -/
theorem exists_compl_capture {m : Type*} [Fintype m] [DecidableEq m] {r : ℕ}
    (U₀ : Matrix m (Fin r) ℝ) (hU₀ : U₀ᵀ * U₀ = 1) (K₁ : Matrix m (Fin r) ℝ)
    (hr : r + r ≤ Fintype.card m) :
    ∃ U₁ : Matrix m (Fin r) ℝ, U₁ᵀ * U₁ = 1 ∧ U₁ᵀ * U₀ = 0 ∧
      U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * K₁) = (1 - U₀ * U₀ᵀ) * K₁ :=
  exists_orthonormal_capture_compl_fin U₀ hU₀ K₁ hr

/-- **Admissible new directions in every dimension.**  For any `U₀` with orthonormal columns
(no condition on `m`), `Ũ₁ = I - U₀U₀ᵀ` (with `m` columns) satisfies `Ũ₁ᵀ U₀ = 0`, captures
`(I - U₀U₀ᵀ) K₁` for every `K₁`, and `Ũ₁ Ũ₁ᵀ = Ũ₁` is the orthogonal projector onto the
complement of the range of `U₀`.  So the hypotheses `perpU`, `capU` (and `perpV`, `capV`) of
`IsStep` can always be met. -/
theorem compl_capture_proj {m r k : Type*} [Fintype m] [DecidableEq m] [Fintype r]
    [DecidableEq r] {U₀ : Matrix m r ℝ} (hU₀ : U₀ᵀ * U₀ = 1) :
    (1 - U₀ * U₀ᵀ)ᵀ * U₀ = 0 ∧
      (1 - U₀ * U₀ᵀ) * (1 - U₀ * U₀ᵀ)ᵀ = 1 - U₀ * U₀ᵀ ∧
      ∀ K₁ : Matrix m k ℝ, (1 - U₀ * U₀ᵀ) * (1 - U₀ * U₀ᵀ)ᵀ * ((1 - U₀ * U₀ᵀ) * K₁) =
        (1 - U₀ * U₀ᵀ) * K₁ := by
  have hsym : (1 - U₀ * U₀ᵀ)ᵀ = 1 - U₀ * U₀ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hidem : (1 - U₀ * U₀ᵀ) * (1 - U₀ * U₀ᵀ) = 1 - U₀ * U₀ᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      show U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * (U₀ᵀ * U₀) * U₀ᵀ by simp only [Matrix.mul_assoc], hU₀,
      Matrix.mul_one, sub_self, sub_zero]
  refine ⟨?_, by rw [hsym, hidem], fun K₁ => by rw [hsym, hidem, ← Matrix.mul_assoc, hidem]⟩
  rw [hsym, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU₀, Matrix.mul_one, sub_self]

/-! ### Global error of the rank-adaptive parallel integrator -/

section Global

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Global error of the matrix parallel rank-adaptive BUG integrator** ([CerutiKuschLubich2024],
**Theorem 4.1**, in the form of [Kusch2025, Thm. 2.2], with explicit constants).  Let
`F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B` in the Frobenius norm, and let `A' = F(t, A)`
on `[t₀, t₀ + N h]`, `h ≥ 0`.  For `k < N` let step `k` start from `Yₖ = Uₖ Sₖ Vₖᵀ` of rank
`rₖ = rk k` at `tₖ = t₀ + k h` (`IsStep`, with new directions `W k`, `Z k` and factor
trajectories `K k`, `Lf k`, `Sb k`), let the normal component at the iterate satisfy
`‖(I - UₖUₖᵀ) F(t, Yₖ) (I - VₖVₖᵀ)‖ ≤ ε` for `t ∈ [tₖ, tₖ₊₁)` (`ε ≥ 0`), let
`Yₖ₊₁ = Uₖ₊₁ Sₖ₊₁ Vₖ₊₁ᵀ` be a truncation of `Ŷₖ₊₁ = Ûₖ Ŝₖ V̂ₖᵀ` with `‖Yₖ₊₁ - Ŷₖ₊₁‖ ≤ ϑ`, and
let `Φ k` be the exact flow from `(tₖ, Yₖ)`.  Then for `k ≤ N` with `k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ e^{L T} (‖Y₀ - A(t₀)‖ + T (7 L B h + ε) + k ϑ).

The ranks `rₖ` may change from step to step (rank adaptivity).  For the normal-component
assumption at the grid points only, see `global_error_of_timeLipschitz`. -/
theorem global_error {rk sU sV : ℕ → ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε0 : 0 ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {W : (k : ℕ) → Matrix m (Fin (sU k)) ℝ} {Z : (k : ℕ) → Matrix n (Fin (sV k)) ℝ}
    {K : (k : ℕ) → ℝ → Matrix m (Fin (rk k)) ℝ} {Lf : (k : ℕ) → ℝ → Matrix n (Fin (rk k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (rk k)) (Fin (rk k)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (W k) (Z k)
      (K k) (Lf k) (Sb k))
    (hε : ∀ k < N, ∀ t ∈ Ico (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - U k * (U k)ᵀ) * F t (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augmented (U k) (W k) (V k) (Z k)
      (Sb k (t₀ + (k + 1) * h)) (K k (t₀ + (k + 1) * h)) (Lf k (t₀ + (k + 1) * h))‖ ≤ ϑ)
    {T : ℝ} :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * (‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ + T * (7 * L * B * h + ε) + k * ϑ) :=
  parallelBUG_global_error (Y := fun k => U k * S k * (V k)ᵀ) (P := fun k => leftProj (U k))
    (Q := fun k => rightProj (V k)) (YK := fun k t => K k t * (V k)ᵀ)
    (YL := fun k t => U k * (Lf k t)ᵀ) (YS := fun k t => U k * Sb k t * (V k)ᵀ)
    hF hL hB hε0 hh hA (fun k hk => (hstep k hk).isParallelBUGStep)
    (fun k hk t ht => by
      rw [one_sub_leftProj_one_sub_rightProj_apply]
      exact hε k hk t ht)
    hΦ hΦ₀ hϑ (fun k hk => by rw [← (hstep k hk).augmented_eq]; exact htr k hk)

/-- **Global error with the normal-component assumption at the grid points only**
([CerutiKuschLubich2024, Thm. 4.1] with Assumption 2 as stated: `‖P⊥_{rₖ}(Yₖ) F(tₖ, Yₖ)‖ ≤ ε`).
Under the hypotheses of `global_error`, but with the normal-component bound
`‖(I - UₖUₖᵀ) F(tₖ, Yₖ) (I - VₖVₖᵀ)‖ ≤ ε` required only at `(tₖ, Yₖ)`, and with `F`
additionally `Lₜ`-Lipschitz in time, for `k ≤ N` with `k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ e^{L T} (‖Y₀ - A(t₀)‖ + T ((7 L B + Lₜ) h + ε) + k ϑ). -/
theorem global_error_of_timeLipschitz {rk sU sV : ℕ → ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε Lt : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε) (hLt : 0 ≤ Lt) (hFt : ∀ t s x, ‖F t x - F s x‖ ≤ Lt * |t - s|)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {W : (k : ℕ) → Matrix m (Fin (sU k)) ℝ} {Z : (k : ℕ) → Matrix n (Fin (sV k)) ℝ}
    {K : (k : ℕ) → ℝ → Matrix m (Fin (rk k)) ℝ} {Lf : (k : ℕ) → ℝ → Matrix n (Fin (rk k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (rk k)) (Fin (rk k)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (W k) (Z k)
      (K k) (Lf k) (Sb k))
    (hε : ∀ k < N,
      ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augmented (U k) (W k) (V k) (Z k)
      (Sb k (t₀ + (k + 1) * h)) (K k (t₀ + (k + 1) * h)) (Lf k (t₀ + (k + 1) * h))‖ ≤ ϑ)
    {T : ℝ} :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * (‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ + T * ((7 * L * B + Lt) * h + ε)
        + k * ϑ) :=
  parallelBUG_global_error_of_timeLipschitz (Y := fun k => U k * S k * (V k)ᵀ)
    (P := fun k => leftProj (U k)) (Q := fun k => rightProj (V k))
    (YK := fun k t => K k t * (V k)ᵀ) (YL := fun k t => U k * (Lf k t)ᵀ)
    (YS := fun k t => U k * Sb k t * (V k)ᵀ) hF hL hB hε0 hLt hFt hh hA
    (fun k hk => (hstep k hk).isParallelBUGStep)
    (fun k hk => by
      rw [one_sub_leftProj_one_sub_rightProj_apply]
      exact hε k hk)
    hΦ hΦ₀ hϑ (fun k hk => by rw [← (hstep k hk).augmented_eq]; exact htr k hk)

/-- **Theorem 4.1 of [CerutiKuschLubich2024], verbatim form** (matrix parallel rank-adaptive BUG
integrator).  Assumptions as in the paper: (1) `F` is bounded by `B` and Lipschitz, with
constant `L` in the state and `Lₜ` in time; (2) the normal component at the iterates is
`ε`-small at the grid points, `‖(I - UₖUₖᵀ) F(tₖ, Yₖ) (I - VₖVₖᵀ)‖ ≤ ε` for the rank `rₖ`
used in step `k`; (3) `‖Y₀ - A(t₀)‖ ≤ δ`.  With step size `h > 0`, rank-truncation tolerance
`ϑ` and ranks `rₖ` changing from step to step, for `0 ≤ k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h

with `C₀ = e^{LT}`, `C₁ = (7 L B + Lₜ) T e^{LT}`, `C₂ = C₃ = T e^{LT}`. -/
theorem global_error_paper {rk sU sV : ℕ → ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε Lt : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε) (hLt : 0 ≤ Lt) (hFt : ∀ t s x, ‖F t x - F s x‖ ≤ Lt * |t - s|)
    {t₀ h : ℝ} (hh : 0 < h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {W : (k : ℕ) → Matrix m (Fin (sU k)) ℝ} {Z : (k : ℕ) → Matrix n (Fin (sV k)) ℝ}
    {K : (k : ℕ) → ℝ → Matrix m (Fin (rk k)) ℝ} {Lf : (k : ℕ) → ℝ → Matrix n (Fin (rk k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (rk k)) (Fin (rk k)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (W k) (Z k)
      (K k) (Lf k) (Sb k))
    (hε : ∀ k < N,
      ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augmented (U k) (W k) (V k) (Z k)
      (Sb k (t₀ + (k + 1) * h)) (K k (t₀ + (k + 1) * h)) (Lf k (t₀ + (k + 1) * h))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * δ + (7 * L * B + Lt) * T * Real.exp (L * T) * h
        + T * Real.exp (L * T) * ε + T * Real.exp (L * T) * (ϑ / h) := by
  intro k hk hT
  have h1 := global_error_of_timeLipschitz hF hL hB hε0 hLt hFt hh.le hA hstep hε hΦ hΦ₀ hϑ
    htr k hk hT
  have hnϑ : (k : ℝ) * ϑ ≤ T * (ϑ / h) := by
    calc (k : ℝ) * ϑ ≤ T / h * ϑ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hh).2 hT) hϑ
      _ = T * (ϑ / h) := by ring
  calc ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖
      ≤ Real.exp (L * T) * (‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ + T * ((7 * L * B + Lt) * h + ε)
          + k * ϑ) := h1
    _ ≤ Real.exp (L * T) * (δ + T * ((7 * L * B + Lt) * h + ε) + T * (ϑ / h)) := by gcongr
    _ = _ := by ring

/-- **Theorem 4.1 of [CerutiKuschLubich2024] with the normal-component bound on each step
interval.** Under the hypotheses of `global_error` (normal-component bound for
`t ∈ [tₖ, tₖ₊₁)` at the iterates `Yₖ`, no time regularity of `F`) with `h > 0` and
`‖Y₀ - A(t₀)‖ ≤ δ`, for `0 ≤ k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h

with `C₀ = e^{LT}`, `C₁ = 7 L B T e^{LT}`, `C₂ = C₃ = T e^{LT}`. -/
theorem global_error_constants {rk sU sV : ℕ → ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε) {t₀ h : ℝ} (hh : 0 < h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {W : (k : ℕ) → Matrix m (Fin (sU k)) ℝ} {Z : (k : ℕ) → Matrix n (Fin (sV k)) ℝ}
    {K : (k : ℕ) → ℝ → Matrix m (Fin (rk k)) ℝ} {Lf : (k : ℕ) → ℝ → Matrix n (Fin (rk k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (rk k)) (Fin (rk k)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (W k) (Z k)
      (K k) (Lf k) (Sb k))
    (hε : ∀ k < N, ∀ t ∈ Ico (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - U k * (U k)ᵀ) * F t (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augmented (U k) (W k) (V k) (Z k)
      (Sb k (t₀ + (k + 1) * h)) (K k (t₀ + (k + 1) * h)) (Lf k (t₀ + (k + 1) * h))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * δ + 7 * L * B * T * Real.exp (L * T) * h
        + T * Real.exp (L * T) * ε + T * Real.exp (L * T) * (ϑ / h) := by
  intro k hk hT
  have h1 := parallelBUG_global_error_paper (Y := fun k => U k * S k * (V k)ᵀ)
    (P := fun k => leftProj (U k)) (Q := fun k => rightProj (V k))
    (YK := fun k t => K k t * (V k)ᵀ) (YL := fun k t => U k * (Lf k t)ᵀ)
    (YS := fun k t => U k * Sb k t * (V k)ᵀ) hF hL hB hε0 hh hA
    (fun k hk => (hstep k hk).isParallelBUGStep)
    (fun k hk t ht => by
      rw [one_sub_leftProj_one_sub_rightProj_apply]
      exact hε k hk t ht)
    hΦ hΦ₀ hϑ (fun k hk => by rw [← (hstep k hk).augmented_eq]; exact htr k hk) k hk hT
  have h2 : Real.exp (L * T) * ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ Real.exp (L * T) * δ :=
    mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
  linarith

end Global

/-! ### Satisfiability examples -/

section Examples

/-- `e₁ = (1, 0)ᵀ`, the starting basis `U₀ = V₀` of the examples. -/
private noncomputable def exE₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- `e₂ = (0, 1)ᵀ`, the new direction `Ũ₁ = Ṽ₁` of the first step of the examples. -/
private noncomputable def exE₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The matrix `C = [[0, 1], [1, 1]]` of the example field. -/
private noncomputable def exC : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- The clamp `φ(x) = max (-1) (min 1 x)` to `[-1, 1]`: bounded by `1` and `1`-Lipschitz. -/
private noncomputable def exφ (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- The example field `F(t, Y) = φ(Y₁₁) C`: bounded by `‖C‖`, `‖C‖`-Lipschitz, not constant. -/
private noncomputable def exG (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  exφ (Y 0 0) • exC

private lemma exφ_lip (x y : ℝ) : |exφ x - exφ y| ≤ |x - y| := by
  unfold exφ
  rw [max_comm (-1) (min 1 x), max_comm (-1) (min 1 y)]
  calc |max (min 1 x) (-1) - max (min 1 y) (-1)| ≤ |min 1 x - min 1 y| :=
        abs_max_sub_max_le_abs _ _ _
    _ ≤ max |1 - 1| |x - y| := abs_min_sub_min_le_max _ _ _ _
    _ = |x - y| := by simp

private lemma exφ_abs (x : ℝ) : |exφ x| ≤ 1 := by
  unfold exφ
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private lemma exG_lip : IsLipschitzField exG ‖exC‖ := fun _ Y Z => by
  simp only [exG, ← sub_smul, norm_smul, Real.norm_eq_abs]
  calc |exφ (Y 0 0) - exφ (Z 0 0)| * ‖exC‖ ≤ ‖Y - Z‖ * ‖exC‖ := by
        gcongr
        exact (exφ_lip _ _).trans (Frobenius.abs_apply_le_norm (Y - Z) 0 0)
    _ = ‖exC‖ * ‖Y - Z‖ := mul_comm _ _

private lemma exG_bdd : IsBoundedField exG ‖exC‖ := fun _ Y => by
  simp only [exG, norm_smul, Real.norm_eq_abs]
  calc |exφ (Y 0 0)| * ‖exC‖ ≤ 1 * ‖exC‖ := by gcongr; exact exφ_abs _
    _ = ‖exC‖ := one_mul _

private lemma exG_time (t s : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖exG t Y - exG s Y‖ ≤ 0 * |t - s| := by
  simp [exG]

private lemma exG_eq {Y : Matrix (Fin 2) (Fin 2) ℝ} (h : Y 0 0 = 1) (t : ℝ) : exG t Y = exC := by
  simp [exG, exφ, h]

/-- An ODE solution for `f` solves `g` if `f` and `g` agree along the trajectory. -/
private lemma odeSolution_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E → E} {y : ℝ → E} {a b : ℝ} (hy : ODESolution f y a b)
    (h : ∀ t, g t (y t) = f t (y t)) : ODESolution g y a b :=
  ⟨hy.cont, fun t ht => by rw [h]; exact hy.deriv t ht⟩

/-- A parallel BUG step for the example field `exG`, from any `Y₀ = U₀ S₀ V₀ᵀ` with
`(Y₀)₁₁ = 1` and bases for which the `(1,1)` entries of `C V₀V₀ᵀ`, `U₀U₀ᵀ C` and
`U₀U₀ᵀ C V₀V₀ᵀ` vanish: along all substeps `(Y)₁₁ = 1`, so `F = C` there and the substeps are
affine. -/
private lemma exIsStep {r s s' : Type*} [Fintype r] [Fintype s] [Fintype s'] [DecidableEq r]
    {U₀ : Matrix (Fin 2) r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix (Fin 2) r ℝ}
    {U₁ : Matrix (Fin 2) s ℝ} {V₁ : Matrix (Fin 2) s' ℝ} {a b : ℝ}
    (hU : U₀ᵀ * U₀ = 1) (hV : V₀ᵀ * V₀ = 1) (hpU : U₁ᵀ * U₀ = 0) (hpV : V₁ᵀ * V₀ = 0)
    (hcU : ∀ X : Matrix (Fin 2) r ℝ, U₁ * U₁ᵀ * ((1 - U₀ * U₀ᵀ) * X) = (1 - U₀ * U₀ᵀ) * X)
    (hcV : ∀ X : Matrix (Fin 2) r ℝ, V₁ * V₁ᵀ * ((1 - V₀ * V₀ᵀ) * X) = (1 - V₀ * V₀ᵀ) * X)
    (h₀ : (U₀ * S₀ * V₀ᵀ) 0 0 = 1) (hK : (exC * V₀ * V₀ᵀ) 0 0 = 0)
    (hL : (U₀ * U₀ᵀ * exC) 0 0 = 0) (hS : (U₀ * U₀ᵀ * exC * V₀ * V₀ᵀ) 0 0 = 0) :
    IsStep exG a b U₀ S₀ V₀ U₁ V₁ (fun t => U₀ * S₀ + (t - a) • (exC * V₀))
      (fun t => V₀ * S₀ᵀ + (t - a) • (exCᵀ * U₀))
      (fun t => S₀ + (t - a) • (U₀ᵀ * exC * V₀)) where
  orthU₀ := hU
  orthV₀ := hV
  kSol := odeSolution_of_eq (odeSolution_affine _ _ a b) fun t => by
    have e : (U₀ * S₀ + (t - a) • (exC * V₀)) * V₀ᵀ =
        U₀ * S₀ * V₀ᵀ + (t - a) • (exC * V₀ * V₀ᵀ) := by
      rw [Matrix.add_mul, Matrix.smul_mul]
    simp only [kField]
    rw [exG_eq (by rw [e, Matrix.add_apply, Matrix.smul_apply, h₀, hK]; simp)]
  kStart := by simp
  lSol := odeSolution_of_eq (odeSolution_affine _ _ a b) fun t => by
    have e : U₀ * (V₀ * S₀ᵀ + (t - a) • (exCᵀ * U₀))ᵀ =
        U₀ * S₀ * V₀ᵀ + (t - a) • (U₀ * U₀ᵀ * exC) := by
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
    simp only [lField]
    rw [exG_eq (by rw [e, Matrix.add_apply, Matrix.smul_apply, h₀, hL]; simp)]
  lStart := by simp
  sSol := odeSolution_of_eq (odeSolution_affine _ _ a b) fun t => by
    have e : U₀ * (S₀ + (t - a) • (U₀ᵀ * exC * V₀)) * V₀ᵀ =
        U₀ * S₀ * V₀ᵀ + (t - a) • (U₀ * U₀ᵀ * exC * V₀ * V₀ᵀ) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc]
    simp only [sField]
    rw [exG_eq (by rw [e, Matrix.add_apply, Matrix.smul_apply, h₀, hS]; simp)]
  sStart := by simp
  perpU := hpU
  capU := hcU _
  perpV := hpV
  capV := hcV _

private lemma exE₁_orth : exE₁ᵀ * exE₁ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exE₁, Matrix.mul_apply]

private lemma exE₂_perp : exE₂ᵀ * exE₁ = 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exE₁, exE₂, Matrix.mul_apply]

private lemma exE₂_orth : exE₂ᵀ * exE₂ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exE₂, Matrix.mul_apply]

private lemma exE₂_proj : 1 - exE₁ * exE₁ᵀ = exE₂ * exE₂ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exE₁, exE₂, Matrix.mul_apply, Matrix.vecMul, dotProduct]

private lemma exE₂_cap (X : Matrix (Fin 2) (Fin 1) ℝ) :
    exE₂ * exE₂ᵀ * ((1 - exE₁ * exE₁ᵀ) * X) = (1 - exE₁ * exE₁ᵀ) * X := by
  rw [exE₂_proj, show exE₂ * exE₂ᵀ * (exE₂ * exE₂ᵀ * X) = exE₂ * (exE₂ᵀ * exE₂) * exE₂ᵀ * X by
    simp only [Matrix.mul_assoc], exE₂_orth, Matrix.mul_one]

/-- The normal-component bound of the examples: the norm of the normal component
`(I - e₁e₁ᵀ) C (I - e₁e₁ᵀ) = e₂ e₂ᵀ` of `F(t, Y₀) = C` at `Y₀ = e₁ e₁ᵀ`. -/
private noncomputable def exε : ℝ := ‖(1 - exE₁ * exE₁ᵀ) * exC * (1 - exE₁ * exE₁ᵀ)‖

/-- The normal component at `Y₀ = e₁ e₁ᵀ` is nonzero, so `ε = exε > 0` in the examples. -/
private lemma exNormal_ne_zero : (1 - exE₁ * exE₁ᵀ) * exC * (1 - exE₁ * exE₁ᵀ) ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [exE₁, exC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecMul,
    dotProduct] at h11

/-- `e₁ e₁ᵀ = [[1, 0], [0, 0]]`. -/
private lemma exE₁E₁ : exE₁ * exE₁ᵀ = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exE₁, Matrix.mul_apply]

private lemma exY₀_entry : (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exE₁ᵀ) 0 0 = 1 := by
  rw [Matrix.mul_one, exE₁E₁]
  simp

/-- The first step of the examples: from `Y₀ = e₁ e₁ᵀ` (rank `1`) on `[a, b]`, with new
directions `Ũ₁ = Ṽ₁ = e₂`. -/
private lemma exStep₀ (a b : ℝ) :
    IsStep exG a b exE₁ (1 : Matrix (Fin 1) (Fin 1) ℝ) exE₁ exE₂ exE₂
      (fun t => exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - a) • (exC * exE₁))
      (fun t => exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + (t - a) • (exCᵀ * exE₁))
      (fun t => (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - a) • (exE₁ᵀ * exC * exE₁)) :=
  exIsStep exE₁_orth exE₁_orth exE₂_perp exE₂_perp exE₂_cap exE₂_cap exY₀_entry
    (by rw [Matrix.mul_assoc, exE₁E₁]; simp [exC, Matrix.mul_apply, Fin.sum_univ_two])
    (by rw [exE₁E₁]; simp [exC, Matrix.mul_apply, Fin.sum_univ_two])
    (by
      rw [Matrix.mul_assoc (exE₁ * exE₁ᵀ * exC), exE₁E₁]
      simp [exC, Matrix.mul_apply, Fin.sum_univ_two])

/-- **The hypotheses of `IsStep.local_error` are jointly satisfiable**, with `L = B = ‖C‖ > 0`
(Lipschitz, bounded, non-constant field `exG`) and `ε = exε > 0` the exact normal component at
`Y₀ = e₁ e₁ᵀ`: one parallel BUG step on `[0, 1]` with `Û = V̂ = (e₁, e₂)` and exact solution
`A(t) = e₁ e₁ᵀ + t C`.  (Here `Ŷ₁ = [[1, 1], [1, 0]]` and `A(1) = [[1, 1], [1, 1]]`.) -/
example :
    ‖augmented exE₁ exE₂ exE₁ exE₂
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 : ℝ) - 0) • (exE₁ᵀ * exC * exE₁))
        (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 : ℝ) - 0) • (exC * exE₁))
        (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + ((1 : ℝ) - 0) • (exCᵀ * exE₁))
      - (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exE₁ᵀ + ((1 : ℝ) - 0) • exC)‖ ≤
      (1 - 0) * (7 * ‖exC‖ * ‖exC‖ * (1 - 0) + exε) :=
  (exStep₀ 0 1).local_error
    (A := fun t => exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exE₁ᵀ + (t - 0) • exC) exG_lip
    (norm_nonneg _) exG_bdd (fun t _ => by rw [exG_eq exY₀_entry]; rfl)
    zero_le_one
    (odeSolution_of_eq (odeSolution_affine _ exC 0 1) fun t =>
      exG_eq (by simp [exE₁E₁, exC]) t)
    (by simp)

/-- The second step of the examples: from `Y₁ = [[1, 1], [1, 0]]` (rank `2`, `U₁ = V₁ = I`)
on `[a, b]`, with no new directions. -/
private lemma exStep₁ (a b : ℝ) :
    IsStep exG a b (1 : Matrix (Fin 2) (Fin 2) ℝ) !![1, 1; 1, 0] (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 0) ℝ) (0 : Matrix (Fin 2) (Fin 0) ℝ)
      (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 0] + (t - a) • (exC * 1))
      (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 0]ᵀ + (t - a) • (exCᵀ * 1))
      (fun t => !![1, 1; 1, 0] + (t - a) • ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * exC * 1)) :=
  exIsStep (by simp) (by simp) (by simp) (by simp) (fun _ => by simp) (fun _ => by simp)
    (by simp) (by simp [exC]) (by simp [exC]) (by simp [exC])

/-! A two-step run in which the rank grows from `1` to `2`. -/

/-- Ranks `r₀ = 1`, `rₖ = 2` (`k ≥ 1`). -/
private def exRk : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 2

/-- Numbers of new directions: `1` in the first step, `0` afterwards (full rank). -/
private def exSU : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

/-- The bases `U₀ = e₁`, `Uₖ = I` (`k ≥ 1`). -/
private noncomputable def exU : (k : ℕ) → Matrix (Fin 2) (Fin (exRk k)) ℝ
  | 0 => exE₁
  | _ + 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The coefficients `S₀ = 1`, `S₁ = [[1, 1], [1, 0]] = Ŷ₁`, `S₂ = [[1, 2], [2, 1]] = Ŷ₂`. -/
private noncomputable def exS : (k : ℕ) → Matrix (Fin (exRk k)) (Fin (exRk k)) ℝ
  | 0 => (1 : Matrix (Fin 1) (Fin 1) ℝ)
  | 1 => !![1, 1; 1, 0]
  | _ + 2 => !![1, 2; 2, 1]

/-- The new directions `W₀ = e₂` and (empty) `Wₖ` for `k ≥ 1`. -/
private noncomputable def exW : (k : ℕ) → Matrix (Fin 2) (Fin (exSU k)) ℝ
  | 0 => exE₂
  | _ + 1 => (0 : Matrix (Fin 2) (Fin 0) ℝ)

/-- The K-step solutions `Kₖ(t) = Uₖ Sₖ + (t - tₖ) C Uₖ`. -/
private noncomputable def exK (k : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin (exRk k)) ℝ :=
  exU k * exS k + (t - (0 + (k : ℝ) * 1)) • (exC * exU k)

/-- The L-step solutions `Lₖ(t) = Uₖ Sₖᵀ + (t - tₖ) Cᵀ Uₖ`. -/
private noncomputable def exL (k : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin (exRk k)) ℝ :=
  exU k * (exS k)ᵀ + (t - (0 + (k : ℝ) * 1)) • (exCᵀ * exU k)

/-- The S-step solutions `S̄ₖ(t) = Sₖ + (t - tₖ) Uₖᵀ C Uₖ`. -/
private noncomputable def exSb (k : ℕ) (t : ℝ) : Matrix (Fin (exRk k)) (Fin (exRk k)) ℝ :=
  exS k + (t - (0 + (k : ℝ) * 1)) • ((exU k)ᵀ * exC * exU k)

/-- The exact flows `Φₖ(t) = Yₖ + (t - tₖ) C` from `(tₖ, Yₖ)`; `Φ₀ = A` is the exact
solution. -/
private noncomputable def exΦ (k : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  exU k * exS k * (exU k)ᵀ + (t - (0 + (k : ℝ) * 1)) • exC

private lemma exY₁_entry :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
  simp

private lemma exY₀₀ : ∀ k : ℕ, k < 2 → (exU k * exS k * (exU k)ᵀ) 0 0 = 1 := by
  intro k hk
  interval_cases k
  · exact exY₀_entry
  · exact exY₁_entry

private lemma exStepAll : ∀ k : ℕ, k < 2 → IsStep exG (0 + (k : ℝ) * 1) (0 + ((k : ℝ) + 1) * 1)
    (exU k) (exS k) (exU k) (exW k) (exW k) (exK k) (exL k) (exSb k) := by
  intro k hk
  interval_cases k
  · exact exStep₀ _ _
  · exact exStep₁ _ _

private lemma exNormalAll : ∀ k : ℕ, k < 2 → ∀ t, ‖(1 - exU k * (exU k)ᵀ) *
    exG t (exU k * exS k * (exU k)ᵀ) * (1 - exU k * (exU k)ᵀ)‖ ≤ exε := by
  intro k hk t
  rw [exG_eq (exY₀₀ k hk)]
  interval_cases k
  · exact le_rfl
  · change ‖(1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) * exC *
      (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)‖ ≤ exε
    simp only [Matrix.transpose_one, Matrix.mul_one, sub_self, Matrix.mul_zero, norm_zero]
    exact norm_nonneg _

private lemma exΦAll : ∀ k : ℕ, k < 2 →
    ODESolution exG (exΦ k) (0 + (k : ℝ) * 1) (0 + ((k : ℝ) + 1) * 1) := by
  intro k hk
  have e : ∀ t, exΦ k t 0 0 = 1 := fun t => by
    simp [exΦ, Matrix.add_apply, exY₀₀ k hk, exC]
  exact odeSolution_of_eq (odeSolution_affine _ exC _ _) fun t => exG_eq (e t) t

/-- The exact solution `A(t) = Y₀ + t C` of the two-step run. -/
private noncomputable def exA (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  exU 0 * exS 0 * (exU 0)ᵀ + (t - 0) • exC

private lemma exA_sol : ODESolution exG exA 0 (0 + ((2 : ℕ) : ℝ) * 1) := by
  have e : ∀ t, exA t 0 0 = 1 := fun t => by
    simp [exA, Matrix.add_apply, exY₀₀ 0 two_pos, exC]
  exact odeSolution_of_eq (odeSolution_affine _ exC _ _) fun t => exG_eq (e t) t

private lemma exTr₀ (c : ℝ) (hc : c = 1) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 0] * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ -
      augmented exE₁ exE₂ exE₁ exE₂ ((1 : Matrix (Fin 1) (Fin 1) ℝ) + c • (exE₁ᵀ * exC * exE₁))
        (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) + c • (exC * exE₁))
        (exE₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ + c • (exCᵀ * exE₁))‖ ≤ 0 := by
  refine norm_le_zero_iff.2 (sub_eq_zero.2 ?_)
  subst hc
  rw [augmented_eq_sum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exE₁, exE₂, exC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private lemma exTr₁ (c : ℝ) (hc : c = 1) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 2; 2, 1] * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ -
      augmented (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 0) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 0) ℝ)
        (!![1, 1; 1, 0] + c • ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * exC * 1))
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 0] + c • (exC * 1))
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 1, 0]ᵀ + c • (exCᵀ * 1))‖ ≤ 0 := by
  refine norm_le_zero_iff.2 (sub_eq_zero.2 ?_)
  subst hc
  rw [augmented_eq_sum]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exC] <;> norm_num

private lemma exTrAll : ∀ k : ℕ, k < 2 → ‖exU (k + 1) * exS (k + 1) * (exU (k + 1))ᵀ -
    augmented (exU k) (exW k) (exU k) (exW k) (exSb k (0 + ((k : ℝ) + 1) * 1))
      (exK k (0 + ((k : ℝ) + 1) * 1)) (exL k (0 + ((k : ℝ) + 1) * 1))‖ ≤ 0 := by
  intro k hk
  interval_cases k
  · exact exTr₀ _ (by norm_num)
  · exact exTr₁ _ (by norm_num)

/-- **The hypotheses of `global_error_paper` (Theorem 4.1, verbatim) are jointly satisfiable**,
non-trivially: two steps (`N = 2`, `h = 1`, `T = 2`) for the bounded, Lipschitz, non-constant,
autonomous field `exG` (`L = B = ‖C‖ > 0`, `Lₜ = 0`), starting from `Y₀ = e₁ e₁ᵀ = A(0)`
(`δ = 0`), with `ε = exε > 0` the exact normal component at `(t₀, Y₀)` (at `Y₁` it vanishes).
The rank grows from `r₀ = 1` to `r₁ = 2` (rank adaptivity), the truncations are exact
(`ϑ = 0`), and the Grönwall propagation is used through the exact flows `Φₖ`. -/
example : ∀ k : ℕ, k ≤ 2 → (k : ℝ) * 1 ≤ 2 →
    ‖exU k * exS k * (exU k)ᵀ - exA (0 + k * 1)‖ ≤
      Real.exp (‖exC‖ * 2) * 0 + (7 * ‖exC‖ * ‖exC‖ + 0) * 2 * Real.exp (‖exC‖ * 2) * 1
        + 2 * Real.exp (‖exC‖ * 2) * exε + 2 * Real.exp (‖exC‖ * 2) * (0 / 1) :=
  global_error_paper (rk := exRk) (sU := exSU) (sV := exSU) (F := exG) (L := ‖exC‖)
    (B := ‖exC‖) (ε := exε) (Lt := 0) (t₀ := 0) (h := 1) (N := 2) (A := exA) (U := exU)
    (V := exU) (S := exS) (W := exW) (Z := exW) (K := exK) (Lf := exL) (Sb := exSb) (Φ := exΦ)
    (ϑ := 0) (δ := 0) (T := 2) exG_lip (norm_nonneg _) exG_bdd (norm_nonneg _) le_rfl exG_time
    one_pos exA_sol exStepAll (fun k hk => exNormalAll k hk _) exΦAll
    (fun _ _ => by simp [exΦ]) le_rfl exTrAll (by simp [exA])

/-- **The hypotheses of `global_error` are jointly satisfiable** on the same two-step run, with
the normal-component bound on each step interval at the iterates. -/
example : ∀ k : ℕ, k ≤ 2 → (k : ℝ) * 1 ≤ 2 →
    ‖exU k * exS k * (exU k)ᵀ - exA (0 + k * 1)‖ ≤
      Real.exp (‖exC‖ * 2) * (‖exU 0 * exS 0 * (exU 0)ᵀ - exA 0‖
        + 2 * (7 * ‖exC‖ * ‖exC‖ * 1 + exε) + k * 0) :=
  global_error (rk := exRk) (sU := exSU) (sV := exSU) (F := exG) (L := ‖exC‖) (B := ‖exC‖)
    (ε := exε) (t₀ := 0) (h := 1) (N := 2) (A := exA) (U := exU) (V := exU) (S := exS)
    (W := exW) (Z := exW) (K := exK) (Lf := exL) (Sb := exSb) (Φ := exΦ) (ϑ := 0) (T := 2)
    exG_lip (norm_nonneg _) exG_bdd (norm_nonneg _) zero_le_one exA_sol exStepAll
    (fun k hk t _ => exNormalAll k hk t) exΦAll (fun _ _ => by simp [exΦ]) le_rfl exTrAll

end Examples

end MatrixParallelBUG

end LeanDLRA
