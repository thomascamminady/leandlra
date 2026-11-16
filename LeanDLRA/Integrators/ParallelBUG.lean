import LeanDLRA.Foundations.Gronwall

/-!
# The parallel rank-adaptive BUG integrator: robust local and global error bounds

This file formalizes the robust error analysis of the *parallel* basis-update & Galerkin (BUG)
integrator of

* G. Ceruti, J. Kusch, Ch. Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, [CerutiKuschLubich2024] (SIAM J. Sci. Comput. 2024), §3.1 (algorithm), §3.2 (block
  structure of the augmented coefficient matrix), (4.1) (local error) and **Theorem 4.1**
  (global error);

see also J. Kusch, *Second-order robust parallel integrators for dynamical low-rank
approximation*, [Kusch2025, Thm. 2.2] (restatement of Theorem 4.1 above with the
truncation term written as `C₃ k ϑ`).

## The algorithm (matrix form, [CerutiKuschLubich2024] §3.1)

Starting from `Y₀ = U₀ S₀ V₀ᵀ` (`U₀ᵀU₀ = I`, `V₀ᵀV₀ = I`), a step `t₀ → t₁ = t₀ + h` solves
**in parallel**

* K-step: `K̇ = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`; `Û = [U₀, Ũ₁] = orth([U₀, K(t₁)])`,
  `S̃ᴷ = Ũ₁ᵀ K(t₁)`;
* L-step: `L̇ = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ`; `V̂ = [V₀, Ṽ₁] = orth([V₀, L(t₁)])`,
  `S̃ᴸ = L(t₁)ᵀ Ṽ₁`;
* S-step: `S̄̇ = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`, `S̄(t₀) = S₀`;

then forms the augmented coefficient matrix `Ŝ₁ = [[S̄(t₁), S̃ᴸ], [S̃ᴷ, 0]]`, the rank-`2r` matrix
`Ŷ₁ = Û Ŝ₁ V̂ᵀ`, and truncates it to `Y₁` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`.

## Abstract formulation

As everywhere in LeanDLRA, the substeps are written as full-space trajectories on a real inner
product space `E`, with `P₀ = (X ↦ U₀U₀ᵀX)` and `Q₀ = (X ↦ XV₀V₀ᵀ)` commuting orthogonal
projectors:

* `YK = K V₀ᵀ` solves `YK' = Q₀ F(t, YK)`, `YK t₀ = Y₀`;
* `YL = U₀ Lᵀ` solves `YL' = P₀ F(t, YL)`, `YL t₀ = Y₀`;
* `YS = U₀ S̄ V₀ᵀ` solves `YS' = P₀ Q₀ F(t, YS)`, `YS t₀ = Y₀`;

and `Y₀ = P₀ Y₀ = Q₀ Y₀`.  The untruncated result is (`parallelBUG`)

    Ŷ₁ = YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁).

**Why this is `Û Ŝ₁ V̂ᵀ`.**  Expanding the block product,
`Û Ŝ₁ V̂ᵀ = U₀ S̄(t₁) V₀ᵀ + Ũ₁ S̃ᴷ V₀ᵀ + U₀ S̃ᴸ Ṽ₁ᵀ` (`matrix_parallelBUG_blocks`).  The first
term is `YS(t₁)`.  Since `Û = [U₀, Ũ₁]` is an orthonormal basis of the range of `[U₀, K(t₁)]`
whose first block is `U₀`, the second block `Ũ₁` is an orthonormal basis of the range of
`(I - U₀U₀ᵀ) K(t₁)` (Gram–Schmidt: `Ũ₁ = orth((I - U₀U₀ᵀ) K(t₁))`, `U₀ᵀŨ₁ = 0`), and likewise
`Ṽ₁ = orth((I - V₀V₀ᵀ) L(t₁))`.  The projector `ÛÛᵀ = U₀U₀ᵀ + Ũ₁Ũ₁ᵀ` (`matrix_augmented_proj`)
fixes `K(t₁)`, hence
`Ũ₁ S̃ᴷ V₀ᵀ = Ũ₁Ũ₁ᵀ K(t₁) V₀ᵀ = (I - U₀U₀ᵀ) K(t₁) V₀ᵀ = (1 - P₀) YK(t₁)`; symmetrically
`U₀ S̃ᴸ Ṽ₁ᵀ = U₀ L(t₁)ᵀ Ṽ₁Ṽ₁ᵀ = (1 - Q₀) YL(t₁)`.  Abstractly this is
`parallelBUG_eq_augmented` (with `P₁ = Ũ₁Ũ₁ᵀ`, `Q₁ = Ṽ₁Ṽ₁ᵀ`), and at the level of matrices
`matrix_parallelBUG_eq`.  The zero `(1,1)` block of `Ŝ₁` is the statement
`(1 - P₀)(1 - Q₀) Ŷ₁ = 0` of `parallelBUG_blocks`.

## Main results

* `four_block_decomp`, `ContinuousLinearMap.four_block_decomp_apply`: the identity
  `1 = P₀Q₀ + (1-P₀)Q₀ + P₀(1-Q₀) + (1-P₀)(1-Q₀)` (valid in every ring).
* `parallelBUG_blocks`: the four blocks of `Ŷ₁` are `YS(t₁)`, `(1-P₀)YK(t₁)`, `(1-Q₀)YL(t₁)`
  and `0`.
* `parallelBUG_local_error`: if `F` is `L`-Lipschitz and bounded by `B`, `P₀`, `Q₀` are
  commuting orthogonal projectors and `‖(1-P₀)(1-Q₀) F(t, Y₀)‖ ≤ ε` on the step, then

      ‖Ŷ₁ - A(t₁)‖ ≤ h (7 L B h + ε),

  where `A` is the exact solution with `A(t₀) = Y₀`.  `parallelBUG_local_error_of_timeLipschitz`
  only assumes the normal-component bound at `t₀` (as in the paper) and `Lₜ`-Lipschitz time
  dependence, giving `h ((7 L B + Lₜ) h + ε)`.
* `parallelBUG_global_error_sum`, `parallelBUG_global_error`, `parallelBUG_global_error_paper`:
  with truncation `‖Yₙ₊₁ - Ŷₙ₊₁‖ ≤ ϑ`, Lady Windermere's fan gives, for `n h ≤ T`,

      ‖Yₙ - A(tₙ)‖ ≤ exp(L T) (δ + T (7 L B h + ε) + n ϑ)
                   ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h,

  with `C₀ = e^{LT}`, `C₁ = 7 L B T e^{LT}`, `C₂ = C₃ = T e^{LT}`.  This is **Theorem 4.1** of
  [CerutiKuschLubich2024].  `parallelBUG_global_error_of_timeLipschitz` assumes the normal-component
  bound only at the grid points `(tₙ, Yₙ)`, exactly as Assumption 2 of the paper.
* `IsParallelBUGStep.local_error_truncated`: the truncated local error (4.1),
  `‖Y₁ - A(t₁)‖ ≤ h (7 L B h + ε) + ϑ`.
* `IsParallelBUGStep.blocks`, `IsParallelBUGStep.tangent_eq`: along an actual step the substeps
  stay in their Galerkin spaces, so the four blocks of `Ŷ₁` are as in (3.4); in particular the
  doubly normal block vanishes, `normal P₀ Q₀ Ŷ₁ = 0`, i.e. `Ŷ₁` lies in the range of the
  tangent projector `tangent P₀ Q₀ = P₀ + Q₀ - P₀Q₀` at `Y₀`.
* `normal_augmented_eq`, `norm_augmented_le_normal`, `matrix_normal_augmented_eq`: the identity
  (3.11) behind the step-rejection strategy (§3.3),
  `P⊥(Y₀)[ÛÛᵀ F₀ V̂V̂ᵀ] = Ũ₁Ũ₁ᵀ F₀ Ṽ₁Ṽ₁ᵀ` (abstractly: `normal P₀ Q₀ ((P₀+P₁)(Q₀+Q₁) x) = P₁ Q₁ x`),
  and the bound `η = ‖P₁ Q₁ F₀‖ ≤ ‖P⊥(Y₀) F₀‖` of the computable indicator by the normal
  component.
* `parallelBUG_euler`, `parallelBUG_euler_norm_le`, `parallelBUG_euler_stable`: with explicit
  Euler substeps the parallel BUG step is the tangent-space projected Euler step,
  `Ŷ₁ = P(Y₀)(Y₀ + h F(t₀, Y₀))`; hence it inherits the CFL condition of the full explicit Euler
  scheme, `‖Ŷ₁‖ ≤ ‖Y₀ + h F(t₀, Y₀)‖ ≤ ‖Y₀‖` (§5.1 of [CerutiKuschLubich2024]), and with
  norm-nonincreasing truncation `‖Yₙ‖ ≤ ‖Y₀‖` for all `n`.

## Statement of Theorem 4.1 of [CerutiKuschLubich2024]

Assumptions: (1) `F` is bounded and Lipschitz continuous; (2) the normal component of
`F(tₙ, Yₙ)` is `ε`-small, `‖P⊥_{rₙ}(Yₙ) F(tₙ, Yₙ)‖ ≤ ε` for `0 ≤ nh ≤ T`, where
`P⊥_r(Y) Z = (I - UUᵀ) Z (I - VVᵀ)` for `Y = USVᵀ`; (3) `‖Y₀ - A(0)‖ ≤ δ`.  Then the parallel
rank-adaptive integrator with step size `h` and truncation tolerance `ϑ` satisfies
`‖Yₙ - A(tₙ)‖ ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ/h` for `0 ≤ nh ≤ T`, where the `Cᵢ` depend only on
the bound and Lipschitz constant of `F` and on `T`.  The local error bound (4.1) reads
`‖Y₁ - A(t₁)‖ ≤ c₁ h² + c₂ h ε + ϑ`.

## Deviations from the paper

* The paper proves the local error by comparison with the rank-adaptive BUG integrator
  (`‖Ŷ₁ - Ŷ₁^BUG‖ ≤ ĉ₁h² + ĉ₂hε`, §3.2/§4.1, constants left implicit).  We instead bound
  `Ŷ₁ - A(t₁)` directly through the four-block decomposition of `A(t₁) - Ŷ₁`: three Galerkin
  defects of size `≤ 2 L B h²` each (the `P₀Q₀`, `(1-P₀)Q₀`, `P₀(1-Q₀)` blocks) and the doubly
  normal block of size `≤ h (L B h + ε)`.  This yields fully explicit constants `c₁ = 7 L B`,
  `c₂ = 1`.
* The normal-component bound is used in the form `‖(1-P₀)(1-Q₀) F(t, Y₀)‖ ≤ ε` for
  `t ∈ [t₀, t₁)` (the "near the solution" assumption of the robust BUG literature).  The
  variant `…_of_timeLipschitz` uses it only at `t₀`, as in Assumption 2 of the paper, at the
  price of a time-Lipschitz constant `Lₜ` of `F` (implicit in the paper's "bounded derivatives").
* The substep solutions and the exact flows on each step are hypotheses (`ODESolution`), as in
  `lady_windermere`; their existence for Lipschitz fields is `Foundations/Existence.lean`.
* The truncation is abstracted to `‖Yₙ₊₁ - Ŷₙ₊₁‖ ≤ ϑ` (the SVD truncation of the paper
  satisfies this by construction); the step-rejection strategy (§3.3) is not formalized.
* The second-order parallel integrators of [Kusch2025] (whose analysis needs bounds on third
  derivatives of the exact solution) are not formalized here.
* For the CFL statement of §5.1 the paper projects onto the span of
  `[U₀ ⊗ V₀, Ũ₁ ⊗ V₀, U₀ ⊗ Ṽ₁]`; we use the (equivalent on `Y₀ + h F₀`, and basis-free) tangent
  projector `P(Y₀) = P₀ + Q₀ - P₀Q₀`.
-/

open Set Finset

namespace LeanDLRA

/-! ### The four-block decomposition -/

section Blocks

/-- **Four-block decomposition of the identity.**  For any two elements `p`, `q` of a ring,
`1 = p q + (1 - p) q + p (1 - q) + (1 - p)(1 - q)`.  For the left and right projectors
`P₀ = U₀U₀ᵀ·`, `Q₀ = ·V₀V₀ᵀ` this is the splitting of a matrix into the four blocks with respect
to `[U₀, U₀^⊥]` and `[V₀, V₀^⊥]` ([CerutiKuschLubich2024], (3.6)). -/
theorem four_block_decomp {R : Type*} [Ring R] (p q : R) :
    p * q + (1 - p) * q + p * (1 - q) + (1 - p) * (1 - q) = 1 := by
  noncomm_ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The four-block decomposition, applied to a vector. -/
theorem ContinuousLinearMap.four_block_decomp_apply (P Q : E →L[ℝ] E) (x : E) :
    P (Q x) + (1 - P) (Q x) + P ((1 - Q) x) + (1 - P) ((1 - Q) x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) (four_block_decomp P Q)
  simpa only [add_apply, mul_apply_eq_comp,
    one_apply_eq_self] using h

/-- **The parallel BUG update** ([CerutiKuschLubich2024, §3.1], before truncation):
`Ŷ₁ = YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁)`, given the end values `yK = YK(t₁)`,
`yL = YL(t₁)`, `yS = YS(t₁)` of the K-, L- and S-steps.  In matrix form this is `Û Ŝ₁ V̂ᵀ`, see
`parallelBUG_eq_augmented` and `matrix_parallelBUG_eq`. -/
def parallelBUG (P₀ Q₀ : E →L[ℝ] E) (yK yL yS : E) : E :=
  yS + (1 - P₀) yK + (1 - Q₀) yL

/-- **Ŷ₁ is the paper's `Û Ŝ₁ V̂ᵀ`** (abstract form).  Let `P₁` and `Q₁` be maps (in the paper
`Ũ₁Ũ₁ᵀ·` and `·Ṽ₁Ṽ₁ᵀ`) such that the augmented projectors `P₀ + P₁` (`= ÛÛᵀ·`) and `Q₀ + Q₁`
(`= ·V̂V̂ᵀ`) fix `yK = K(t₁)V₀ᵀ` resp. `yL = U₀L(t₁)ᵀ` (i.e. `Û` spans `K(t₁)` and `V̂` spans
`L(t₁)`).  Then `yS + P₁ yK + Q₁ yL`, which is `U₀S̄(t₁)V₀ᵀ + Ũ₁S̃ᴷV₀ᵀ + U₀S̃ᴸṼ₁ᵀ`, equals
`parallelBUG P₀ Q₀ yK yL yS`. -/
theorem parallelBUG_eq_augmented (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E) (yK yL yS : E)
    (hK : P₀ yK + P₁ yK = yK) (hL : Q₀ yL + Q₁ yL = yL) :
    yS + P₁ yK + Q₁ yL = parallelBUG P₀ Q₀ yK yL yS := by
  have hK' : P₁ yK = yK - P₀ yK := eq_sub_of_add_eq' hK
  have hL' : Q₁ yL = yL - Q₀ yL := eq_sub_of_add_eq' hL
  simp only [parallelBUG, sub_apply, one_apply_eq_self, hK', hL']

/-- **Block structure of `Ŷ₁`** ([CerutiKuschLubich2024], (3.4)).  If `P₀`, `Q₀` are commuting
idempotents, `yK` lies in the range of `Q₀`, `yL` in the range of `P₀`, and `yS` in the range
of `P₀Q₀`, then the four blocks of `Ŷ₁ = parallelBUG P₀ Q₀ yK yL yS` are `yS`, `(1-P₀) yK`,
`(1-Q₀) yL` and `0` — the zero `(1,1)` block of `Ŝ₁`. -/
theorem parallelBUG_blocks {P₀ Q₀ : E →L[ℝ] E} (hP : ∀ x, P₀ (P₀ x) = P₀ x)
    (hQ : ∀ x, Q₀ (Q₀ x) = Q₀ x) (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {yK yL yS : E}
    (hK : Q₀ yK = yK) (hL : P₀ yL = yL) (hSP : P₀ yS = yS) (hSQ : Q₀ yS = yS) :
    P₀ (Q₀ (parallelBUG P₀ Q₀ yK yL yS)) = yS ∧
      (1 - P₀) (Q₀ (parallelBUG P₀ Q₀ yK yL yS)) = (1 - P₀) yK ∧
      P₀ ((1 - Q₀) (parallelBUG P₀ Q₀ yK yL yS)) = (1 - Q₀) yL ∧
      (1 - P₀) ((1 - Q₀) (parallelBUG P₀ Q₀ yK yL yS)) = 0 := by
  have hQK : Q₀ (P₀ yK) = P₀ yK := by rw [← hc, hK]
  have hPQL : P₀ (Q₀ yL) = Q₀ yL := by rw [hc, hL]
  have hQ' : Q₀ (parallelBUG P₀ Q₀ yK yL yS) = yS + (yK - P₀ yK) := by
    simp only [parallelBUG, sub_apply, one_apply_eq_self,
      map_add, map_sub, hSQ, hK, hQK, hQ]
    abel
  have hN : (1 - Q₀) (parallelBUG P₀ Q₀ yK yL yS) = yL - Q₀ yL := by
    rw [sub_apply, one_apply_eq_self, hQ']
    simp only [parallelBUG, sub_apply, one_apply_eq_self]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQ']; simp only [map_add, map_sub, hSP, hP]; abel
  · rw [hQ']
    simp only [sub_apply, one_apply_eq_self, map_add, map_sub,
      hSP, hP]
    abel
  · rw [hN]; simp only [map_sub, hL, hPQL, sub_apply,
      one_apply_eq_self]
  · rw [hN]; simp only [map_sub, hL, hPQL, sub_apply,
      one_apply_eq_self, sub_self]

/-- The error decomposition behind the local error bound: for commuting `P₀`, `Q₀`,
`A₁ - Ŷ₁ = (P₀Q₀A₁ - yS) + (1-P₀)(Q₀A₁ - yK) + (1-Q₀)(P₀A₁ - yL) + (1-P₀)(1-Q₀)A₁`. -/
theorem sub_parallelBUG_eq {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    (a yK yL yS : E) :
    a - parallelBUG P₀ Q₀ yK yL yS =
      (P₀ (Q₀ a) - yS) + (1 - P₀) (Q₀ a - yK) + (1 - Q₀) (P₀ a - yL)
        + (1 - P₀) ((1 - Q₀) a) := by
  simp only [parallelBUG, sub_apply, one_apply_eq_self, map_sub,
    hc]
  abel

/-- **The step-rejection indicator** ([CerutiKuschLubich2024], (3.11), abstract form). Let `P₁`,
`Q₁` be the projectors onto the new basis directions (`Ũ₁Ũ₁ᵀ·`, `·Ṽ₁Ṽ₁ᵀ`), orthogonal to the old
ones (`P₀P₁ = 0`, `Q₀Q₁ = 0`), so that `P₀ + P₁ = ÛÛᵀ·` and `Q₀ + Q₁ = ·V̂V̂ᵀ`. Then the normal
component at `Y₀` of the projection of `x` onto the augmented space is
`normal P₀ Q₀ ((P₀ + P₁)((Q₀ + Q₁) x)) = P₁ (Q₁ x)`, i.e. `P⊥(Y₀)[ÛÛᵀ F₀ V̂V̂ᵀ] = Ũ₁Ũ₁ᵀ F₀ Ṽ₁Ṽ₁ᵀ`,
whose norm is the computable `η = ‖Ũ₁ᵀ F₀ Ṽ₁‖`. Only idempotence of `P₀`, `Q₀` and commutation of
`Q₀` with `P₀`, `P₁` are needed. -/
theorem normal_augmented_eq {P₀ P₁ Q₀ Q₁ : E →L[ℝ] E} (hP₀ : ∀ x, P₀ (P₀ x) = P₀ x)
    (hQ₀ : ∀ x, Q₀ (Q₀ x) = Q₀ x) (hP₀₁ : ∀ x, P₀ (P₁ x) = 0) (hQ₀₁ : ∀ x, Q₀ (Q₁ x) = 0)
    (hc₀ : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) (hc₁ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (x : E) :
    normal P₀ Q₀ ((P₀ + P₁) ((Q₀ + Q₁) x)) = P₁ (Q₁ x) := by
  simp only [normal_apply, add_apply, map_add, map_sub, ← hc₀, ← hc₁, hQ₀,
    hQ₀₁, map_zero, hP₀, hP₀₁]
  abel

/-- **The step-rejection indicator is bounded by the normal component** ([CerutiKuschLubich2024],
§3.3).  For orthogonal projectors `P₀ ⟂ P₁`, `Q₀ ⟂ Q₁` with `Q₁` commuting with `P₀`,
`‖P₁ (Q₁ x)‖ ≤ ‖normal P₀ Q₀ x‖`.  With `x = F₀ = F(t₀, Y₀)` this is
`η = ‖Ũ₁ᵀ F₀ Ṽ₁‖ ≤ ‖P⊥(Y₀) F₀‖`: the computable quantity used in the step-rejection criterion
`h η > c ϑ` never exceeds the (inaccessible) normal component `ε` of Assumption 2. -/
theorem norm_augmented_le_normal {P₀ P₁ Q₀ Q₁ : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hP₁ : IsOrthProj P₁) (hQ₁ : IsOrthProj Q₁)
    (hP₀₁ : ∀ x, P₀ (P₁ x) = 0) (hQ₀₁ : ∀ x, Q₀ (Q₁ x) = 0)
    (hc : ∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) (x : E) :
    ‖P₁ (Q₁ x)‖ ≤ ‖normal P₀ Q₀ x‖ := by
  have hP₁₀ : ∀ x, P₁ (P₀ x) = 0 := fun x => by
    refine ext_inner_right ℝ fun y => ?_
    rw [hP₁.symm, hP₀.symm, hP₀₁, inner_zero_right, inner_zero_left]
  have hQ₁₀ : ∀ x, Q₁ (Q₀ x) = 0 := fun x => by
    refine ext_inner_right ℝ fun y => ?_
    rw [hQ₁.symm, hQ₀.symm, hQ₀₁, inner_zero_right, inner_zero_left]
  have heq : P₁ (Q₁ (normal P₀ Q₀ x)) = P₁ (Q₁ x) := by
    simp only [normal_apply, map_sub, hc, hQ₁₀, hP₁₀, sub_zero]
  calc ‖P₁ (Q₁ x)‖ = ‖P₁ (Q₁ (normal P₀ Q₀ x))‖ := by rw [heq]
    _ ≤ ‖normal P₀ Q₀ x‖ := (hP₁.norm_le _).trans (hQ₁.norm_le _)

end Blocks

/-! ### Analytic lemmas: Galerkin defects and the doubly normal block -/

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivative of a trajectory composed with a fixed continuous linear map. -/
private lemma hasDerivWithinAt_clm_comp (R : E →L[ℝ] E) {y : ℝ → E} {v : E} {s : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt y v s t) : HasDerivWithinAt (fun t => R (y t)) (R v) s t :=
  R.hasFDerivAt.comp_hasDerivWithinAt t h

/-- **Range invariance of a projected flow.**  If `R` is idempotent, `y' = R f(t, y)` on
`[a, b]` and `R (y a) = y a`, then `R (y t) = y t` on `[a, b]`. -/
theorem ODESolution.map_eq_of_idem {f : ℝ → E → E} {R : E →L[ℝ] E} (hR : ∀ x, R (R x) = R x)
    {y : ℝ → E} {a b : ℝ} (hy : ODESolution (fun t x => R (f t x)) y a b) (h0 : R (y a) = y a) :
    ∀ t ∈ Icc a b, R (y t) = y t := by
  intro t ht
  have hg := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => y t - R (y t))
    (f' := fun _ => 0) (C := 0) (hy.cont.sub (R.continuous.comp_continuousOn hy.cont))
    (fun s hs => by
      have h1 := (hy.deriv s hs).sub (hasDerivWithinAt_clm_comp R (hy.deriv s hs))
      exact h1.congr_deriv (by simp [hR]))
    (fun _ _ => by simp) t ht
  rw [zero_mul, h0, sub_self, sub_zero, norm_le_zero_iff, sub_eq_zero] at hg
  exact hg.symm

/-- **Galerkin defect bound.**  Let `F` be `L`-Lipschitz and bounded by `B`, let `A' = F(t, A)`
and `Y' = R F(t, Y)` on `[t₀, t₁]` with a contraction `R`, and `Y t₀ = A t₀ = R (A t₀)`.  Then
`‖R A(t₁) - Y(t₁)‖ ≤ 2 L B (t₁ - t₀)²`.  (Both trajectories move at speed `≤ B`, so
`‖A - Y‖ ≤ 2B(t - t₀)` and the defect has speed `≤ 2 L B (t₁ - t₀)`.)  Used for the K-step
(`R = Q₀`), L-step (`R = P₀`) and S-step (`R = P₀Q₀`). -/
theorem norm_map_sub_galerkin_le {F : ℝ → E → E} {L B : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (R : E →L[ℝ] E) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {A Y : ℝ → E} (hA : ODESolution F A t₀ t₁)
    (hY : ODESolution (fun t y => R (F t y)) Y t₀ t₁) (h0 : Y t₀ = A t₀)
    (hR0 : R (A t₀) = A t₀) :
    ‖R (A t₁) - Y t₁‖ ≤ 2 * L * B * (t₁ - t₀) * (t₁ - t₀) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ (A t₀))
  have hAm := hA.norm_sub_le_of_bounded hB
  have hYm := hY.norm_sub_le_of_bounded (hB.comp_contraction R hR)
  have hg := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => R (A t) - Y t)
    (f' := fun t => R (F t (A t)) - R (F t (Y t))) (C := 2 * L * B * (t₁ - t₀))
    ((R.continuous.comp_continuousOn hA.cont).sub hY.cont)
    (fun t ht => (hasDerivWithinAt_clm_comp R (hA.deriv t ht)).sub (hY.deriv t ht))
    (fun t ht => by
      have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
      have hdist : ‖A t - Y t‖ ≤ B * (t - t₀) + B * (t - t₀) := by
        have : A t - Y t = (A t - A t₀) - (Y t - Y t₀) := by rw [h0]; abel
        rw [this]
        exact (norm_sub_le _ _).trans (add_le_add (hAm t htI) (hYm t htI))
      calc ‖R (F t (A t)) - R (F t (Y t))‖ = ‖R (F t (A t) - F t (Y t))‖ := by rw [map_sub]
        _ ≤ ‖F t (A t) - F t (Y t)‖ := hR _
        _ ≤ L * ‖A t - Y t‖ := hF t _ _
        _ ≤ L * (B * (t - t₀) + B * (t - t₀)) := mul_le_mul_of_nonneg_left hdist hL
        _ ≤ 2 * L * B * (t₁ - t₀) := by
          nlinarith [mul_nonneg (mul_nonneg hL hB0) (sub_nonneg.2 ht.2.le)])
    t₁ ⟨ht, le_rfl⟩
  simpa only [h0, hR0, sub_self, sub_zero] using hg

/-- **Doubly normal block.**  Let `F` be `L`-Lipschitz and bounded by `B`, `A' = F(t, A)` on
`[t₀, t₁]`, and `N` a contraction with `N (A t₀) = 0` and `‖N F(t, A t₀)‖ ≤ ε` for
`t ∈ [t₀, t₁)`.  Then `‖N A(t₁)‖ ≤ (L B (t₁ - t₀) + ε) (t₁ - t₀)`.  Used with
`N = (1 - P₀)(1 - Q₀)`, the normal projector at `Y₀`. -/
theorem norm_map_le_of_normal {F : ℝ → E → E} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (N : E →L[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : ODESolution F A t₀ t₁) (hN0 : N (A t₀) = 0)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖N (F t (A t₀))‖ ≤ ε) :
    ‖N (A t₁)‖ ≤ (L * B * (t₁ - t₀) + ε) * (t₁ - t₀) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ (A t₀))
  have hAm := hA.norm_sub_le_of_bounded hB
  have hg := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => N (A t))
    (f' := fun t => N (F t (A t))) (C := L * B * (t₁ - t₀) + ε)
    (N.continuous.comp_continuousOn hA.cont)
    (fun t ht => hasDerivWithinAt_clm_comp N (hA.deriv t ht))
    (fun t ht => by
      have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
      have hsplit : N (F t (A t)) = N (F t (A t) - F t (A t₀)) + N (F t (A t₀)) := by
        rw [map_sub]; abel
      calc ‖N (F t (A t))‖ ≤ ‖N (F t (A t) - F t (A t₀))‖ + ‖N (F t (A t₀))‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ L * ‖A t - A t₀‖ + ε := add_le_add ((hN _).trans (hF t _ _)) (hε t ht)
        _ ≤ L * (B * (t - t₀)) + ε := by
          gcongr; exact hAm t htI
        _ ≤ L * B * (t₁ - t₀) + ε := by
          nlinarith [mul_nonneg (mul_nonneg hL hB0) (sub_nonneg.2 ht.2.le)])
    t₁ ⟨ht, le_rfl⟩
  simpa only [hN0, sub_zero] using hg

end Analytic

/-! ### Local error of the parallel BUG step -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Robust local error of the parallel BUG integrator** ([CerutiKuschLubich2024, §4.1], bound
(4.1) before truncation, with explicit constants). Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by
`B`; let `P₀`, `Q₀` be commuting orthogonal projectors with `P₀ Y₀ = Y₀ = Q₀ Y₀`; let the K-, L- and
S-steps `YK' = Q₀ F(t, YK)`, `YL' = P₀ F(t, YL)`, `YS' = P₀Q₀ F(t, YS)` all start at `Y₀` at time
`t₀`, and let `A' = F(t, A)`, `A(t₀) = Y₀` be the exact solution, all on `[t₀, t₁]`. If the normal
component `‖(1-P₀)(1-Q₀) F(t, Y₀)‖ ≤ ε` for `t ∈ [t₀, t₁)`, then with `h = t₁ - t₀`

    ‖Ŷ₁ - A(t₁)‖ ≤ h (7 L B h + ε),   Ŷ₁ = YS(t₁) + (1-P₀) YK(t₁) + (1-Q₀) YL(t₁).

No assumption on singular values (or on the ranks of `P₀`, `Q₀`) is made: the bound is robust. -/
theorem parallelBUG_local_error {F : ℝ → E → E} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {P₀ Q₀ : E →L[ℝ] E} (hP : IsOrthProj P₀)
    (hQ : IsOrthProj Q₀) (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    {Y₀ : E} (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) {A YK YL YS : ℝ → E}
    (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hYK : ODESolution (fun t y => Q₀ (F t y)) YK t₀ t₁) (hK0 : YK t₀ = Y₀)
    (hYL : ODESolution (fun t y => P₀ (F t y)) YL t₀ t₁) (hL0 : YL t₀ = Y₀)
    (hYS : ODESolution (fun t y => P₀ (Q₀ (F t y))) YS t₀ t₁) (hS0 : YS t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - A t₁‖ ≤
      (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) := by
  have hcP : ∀ x, ‖(1 - P₀) x‖ ≤ ‖x‖ := hP.compl.norm_le
  have hcQ : ∀ x, ‖(1 - Q₀) x‖ ≤ ‖x‖ := hQ.compl.norm_le
  -- S-step defect
  have e1 : ‖P₀ (Q₀ (A t₁)) - YS t₁‖ ≤ 2 * L * B * (t₁ - t₀) * (t₁ - t₀) :=
    norm_map_sub_galerkin_le hF hL hB (P₀ * Q₀) (fun x => (hP.norm_le _).trans (hQ.norm_le x))
      ht hA hYS (by rw [hS0, hA0]) (by
        change P₀ (Q₀ (A t₀)) = A t₀
        rw [hA0, hQY, hPY])
  -- K-step defect
  have e2 : ‖(1 - P₀) (Q₀ (A t₁) - YK t₁)‖ ≤ 2 * L * B * (t₁ - t₀) * (t₁ - t₀) :=
    (hcP _).trans (norm_map_sub_galerkin_le hF hL hB Q₀ hQ.norm_le ht hA hYK
      (by rw [hK0, hA0]) (by rw [hA0, hQY]))
  -- L-step defect
  have e3 : ‖(1 - Q₀) (P₀ (A t₁) - YL t₁)‖ ≤ 2 * L * B * (t₁ - t₀) * (t₁ - t₀) :=
    (hcQ _).trans (norm_map_sub_galerkin_le hF hL hB P₀ hP.norm_le ht hA hYL
      (by rw [hL0, hA0]) (by rw [hA0, hPY]))
  -- doubly normal block
  have e4 : ‖(1 - P₀) ((1 - Q₀) (A t₁))‖ ≤ (L * B * (t₁ - t₀) + ε) * (t₁ - t₀) :=
    norm_map_le_of_normal (N := (1 - P₀) * (1 - Q₀)) hF hL hB
      (fun x => (hcP _).trans (hcQ x)) ht hA
      (by
        change (1 - P₀) ((1 - Q₀) (A t₀)) = 0
        simp only [hA0, sub_apply, one_apply_eq_self, hQY,
          sub_self, map_zero])
      (by rw [hA0]; exact hε)
  rw [norm_sub_rev, sub_parallelBUG_eq hc]
  calc ‖P₀ (Q₀ (A t₁)) - YS t₁ + (1 - P₀) (Q₀ (A t₁) - YK t₁) + (1 - Q₀) (P₀ (A t₁) - YL t₁)
        + (1 - P₀) ((1 - Q₀) (A t₁))‖
      ≤ ‖P₀ (Q₀ (A t₁)) - YS t₁‖ + ‖(1 - P₀) (Q₀ (A t₁) - YK t₁)‖
        + ‖(1 - Q₀) (P₀ (A t₁) - YL t₁)‖ + ‖(1 - P₀) ((1 - Q₀) (A t₁))‖ :=
        norm_add₄_le
    _ ≤ 2 * L * B * (t₁ - t₀) * (t₁ - t₀) + 2 * L * B * (t₁ - t₀) * (t₁ - t₀)
        + 2 * L * B * (t₁ - t₀) * (t₁ - t₀) + (L * B * (t₁ - t₀) + ε) * (t₁ - t₀) := by
        gcongr
    _ = (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) := by ring

/-- A normal-component bound at time `s` propagates to nearby times when `F` is Lipschitz in
time: `‖N F(t, y)‖ ≤ ε + Lₜ h` whenever `‖N F(s, y)‖ ≤ ε`, `‖F(t,y) - F(s,y)‖ ≤ Lₜ |t - s|` and
`|t - s| ≤ h`, for any contraction `N`. -/
theorem norm_map_le_of_timeLipschitz {F : ℝ → E → E} (N : E →L[ℝ] E) (hN : ∀ x, ‖N x‖ ≤ ‖x‖)
    {s t h ε Lt : ℝ} (hLt : 0 ≤ Lt) {y : E} (hε : ‖N (F s y)‖ ≤ ε)
    (hFt : ‖F t y - F s y‖ ≤ Lt * |t - s|) (hts : |t - s| ≤ h) :
    ‖N (F t y)‖ ≤ ε + Lt * h := by
  have hsplit : N (F t y) = N (F t y - F s y) + N (F s y) := by rw [map_sub]; abel
  rw [hsplit]
  calc ‖N (F t y - F s y) + N (F s y)‖ ≤ ‖N (F t y - F s y)‖ + ‖N (F s y)‖ := norm_add_le _ _
    _ ≤ Lt * h + ε := add_le_add ((hN _).trans (hFt.trans (by gcongr))) hε
    _ = ε + Lt * h := add_comm _ _

/-- **Local error with the normal-component bound only at the initial time** (Assumption 2 of
[CerutiKuschLubich2024, Thm. 4.1], is imposed at the grid points `(tₙ, Yₙ)` only).  If
`‖(1-P₀)(1-Q₀) F(t₀, Y₀)‖ ≤ ε` and `‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)` on the step, then
`‖Ŷ₁ - A(t₁)‖ ≤ h ((7 L B + Lₜ) h + ε)` with `h = t₁ - t₀`. -/
theorem parallelBUG_local_error_of_timeLipschitz {F : ℝ → E → E} {L B ε Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt)
    {P₀ Q₀ : E →L[ℝ] E} (hP : IsOrthProj P₀) (hQ : IsOrthProj Q₀)
    (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {Y₀ : E} (hPY : P₀ Y₀ = Y₀)
    (hQY : Q₀ Y₀ = Y₀) {A YK YL YS : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hYK : ODESolution (fun t y => Q₀ (F t y)) YK t₀ t₁) (hK0 : YK t₀ = Y₀)
    (hYL : ODESolution (fun t y => P₀ (F t y)) YL t₀ t₁) (hL0 : YL t₀ = Y₀)
    (hYS : ODESolution (fun t y => P₀ (Q₀ (F t y))) YS t₀ t₁) (hS0 : YS t₀ = Y₀)
    (hε : ‖(1 - P₀) ((1 - Q₀) (F t₀ Y₀))‖ ≤ ε)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * |t - t₀|) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - A t₁‖ ≤
      (t₁ - t₀) * ((7 * L * B + Lt) * (t₁ - t₀) + ε) := by
  have h := parallelBUG_local_error (ε := ε + Lt * (t₁ - t₀)) hF hL hB hP hQ hc ht hPY hQY hA
    hA0 hYK hK0 hYL hL0 hYS hS0 (fun t ht' =>
      norm_map_le_of_timeLipschitz ((1 - P₀) * (1 - Q₀))
        (fun x => (hP.compl.norm_le _).trans (hQ.compl.norm_le x)) hLt hε (hFt t ht')
        (by rw [abs_of_nonneg (sub_nonneg.2 ht'.1)]; linarith [ht'.2]))
  calc _ ≤ (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + (ε + Lt * (t₁ - t₀))) := h
    _ = (t₁ - t₀) * ((7 * L * B + Lt) * (t₁ - t₀) + ε) := by ring

/-- The hypotheses of `parallelBUG_local_error` are jointly satisfiable, and the `h ε` term is
sharp: on `E = ℝ` with `P₀ = Q₀ = 0` (rank zero), `Y₀ = 0`, `F ≡ 1` (`L = 0`, `B = 1`,
normal component `ε = 1`), all substeps stay at `0`, so `Ŷ₁ = 0`, while `A(t) = t`; the error
`‖Ŷ₁ - A(1)‖ = 1` equals the bound `h (7 L B h + ε) = 1`. -/
example : ‖parallelBUG (0 : ℝ →L[ℝ] ℝ) 0 0 0 0 - 1‖ ≤ (1 - 0) * (7 * 0 * 1 * (1 - 0) + 1) :=
  parallelBUG_local_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) IsOrthProj.zero IsOrthProj.zero
    (fun _ => rfl) zero_le_one (Y₀ := 0) (by simp) (by simp)
    (A := fun t => t) (YK := fun _ => 0) (YL := fun _ => 0) (YS := fun _ => 0)
    ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩ rfl
    ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩ rfl
    ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩ rfl
    ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩ rfl
    (fun _ _ => by simp)

end Local

/-! ### Global error: Lady Windermere's fan -/

section Global

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **One step of the parallel BUG integrator** from `(t₀, Y₀)` to `t₁` ([CerutiKuschLubich2024],
§3.1, abstract form): `P₀`, `Q₀` are commuting orthogonal projectors (`U₀U₀ᵀ·`, `·V₀V₀ᵀ`)
fixing `Y₀`, and `YK`, `YL`, `YS` are the K-, L- and S-step trajectories
`YK' = Q₀ F(t, YK)`, `YL' = P₀ F(t, YL)`, `YS' = P₀Q₀ F(t, YS)` on `[t₀, t₁]`, all started at
`Y₀`.  The untruncated result is `parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)`. -/
structure IsParallelBUGStep (F : ℝ → E → E) (P₀ Q₀ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK YL YS : ℝ → E) : Prop where
  orthP : IsOrthProj P₀
  orthQ : IsOrthProj Q₀
  comm : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)
  fixP : P₀ Y₀ = Y₀
  fixQ : Q₀ Y₀ = Y₀
  solK : ODESolution (fun t y => Q₀ (F t y)) YK t₀ t₁
  initK : YK t₀ = Y₀
  solL : ODESolution (fun t y => P₀ (F t y)) YL t₀ t₁
  initL : YL t₀ = Y₀
  solS : ODESolution (fun t y => P₀ (Q₀ (F t y))) YS t₀ t₁
  initS : YS t₀ = Y₀

/-- Local error of a parallel BUG step, in terms of `IsParallelBUGStep`
(see `parallelBUG_local_error`). -/
theorem IsParallelBUGStep.local_error {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) {L B ε : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht : t₀ ≤ t₁)
    {A : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε) :
    ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - A t₁‖ ≤
      (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) :=
  parallelBUG_local_error hF hL hB hs.orthP hs.orthQ hs.comm ht hs.fixP hs.fixQ hA hA0
    hs.solK hs.initK hs.solL hs.initL hs.solS hs.initS hε

/-- **Block structure along a parallel BUG step** ([CerutiKuschLubich2024], (3.4)).  The K-, L- and
S-steps stay in their Galerkin spaces (`Q₀ YK = YK`, `P₀ YL = YL`, `P₀Q₀ YS = YS`), so the four
blocks of `Ŷ₁` are `YS(t₁)`, `(1-P₀) YK(t₁)`, `(1-Q₀) YL(t₁)` and — the zero block of `Ŝ₁` —
`normal P₀ Q₀ Ŷ₁ = (1-P₀)(1-Q₀) Ŷ₁ = 0`. -/
theorem IsParallelBUGStep.blocks {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) (ht : t₀ ≤ t₁) :
    P₀ (Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁))) = YS t₁ ∧
      (1 - P₀) (Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁))) = (1 - P₀) (YK t₁) ∧
      P₀ ((1 - Q₀) (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁))) = (1 - Q₀) (YL t₁) ∧
      normal P₀ Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)) = 0 := by
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hK := hs.solK.map_eq_of_idem hs.orthQ.idem (by rw [hs.initK, hs.fixQ]) t₁ ht₁
  have hL := hs.solL.map_eq_of_idem hs.orthP.idem (by rw [hs.initL, hs.fixP]) t₁ ht₁
  have hPQ : IsOrthProj (P₀ * Q₀) := hs.orthP.mul hs.orthQ hs.comm
  have hS := ODESolution.map_eq_of_idem (R := P₀ * Q₀) hPQ.idem hs.solS
    (by rw [hs.initS]; change P₀ (Q₀ Y₀) = Y₀; rw [hs.fixQ, hs.fixP]) t₁ ht₁
  change P₀ (Q₀ (YS t₁)) = YS t₁ at hS
  have hSQ : Q₀ (YS t₁) = YS t₁ := by rw [← hS, ← hs.comm, hs.orthQ.idem]
  have hSP : P₀ (YS t₁) = YS t₁ := by rw [← hS, hs.orthP.idem]
  exact parallelBUG_blocks hs.orthP.idem hs.orthQ.idem hs.comm hK hL hSP hSQ

/-- **`Ŷ₁` lies in the tangent space at `Y₀`.**  Along a parallel BUG step,
`tangent P₀ Q₀ Ŷ₁ = Ŷ₁`, where `tangent P₀ Q₀ = P₀ + Q₀ - P₀Q₀` abstracts the orthogonal
projector `P(Y₀)` onto the tangent space of the rank-`r` manifold at `Y₀ = U₀S₀V₀ᵀ`. -/
theorem IsParallelBUGStep.tangent_eq {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
    {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS) (ht : t₀ ≤ t₁) :
    tangent P₀ Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)) =
      parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) := by
  have h := tangent_apply_add_normal_apply P₀ Q₀ (parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁))
  rwa [(hs.blocks ht).2.2.2, add_zero] at h

/-- **Robust local error after truncation** ([CerutiKuschLubich2024], (4.1), with explicit constants
`c₁ = 7 L B`, `c₂ = 1`): if the truncated value satisfies `‖Y₁ - Ŷ₁‖ ≤ ϑ`, then
`‖Y₁ - A(t₁)‖ ≤ h (7 L B h + ε) + ϑ` with `h = t₁ - t₀`. -/
theorem IsParallelBUGStep.local_error_truncated {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : ODESolution F A t₀ t₁) (hA0 : A t₀ = Y₀)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₀) ((1 - Q₀) (F t Y₀))‖ ≤ ε) {Y₁ : E} {ϑ : ℝ}
    (htr : ‖Y₁ - parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖ ≤ ϑ) :
    ‖Y₁ - A t₁‖ ≤ (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) + ϑ := by
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁)‖
        + ‖parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ϑ + (t₁ - t₀) * (7 * L * B * (t₁ - t₀) + ε) :=
        add_le_add htr (hs.local_error hF hL hB ht hA hA0 hε)
    _ = _ := add_comm _ _

/-- **Global error of the parallel rank-adaptive BUG integrator** (per-step truncation errors).
Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `tₙ = t₀ + n h` with `h ≥ 0`, and let
`A' = F(t, A)` on `[t₀, t₀ + N h]`.  For `n < N` let step `n` be a parallel BUG step from
`(tₙ, Yₙ)` (`IsParallelBUGStep` with projectors `Pₙ`, `Qₙ`) whose normal component satisfies
`‖(1-Pₙ)(1-Qₙ) F(t, Yₙ)‖ ≤ ε` on `[tₙ, tₙ₊₁)`, let `Yₙ₊₁` be its truncation with
`‖Yₙ₊₁ - Ŷₙ₊₁‖ ≤ ϑₙ`, and let `Φₙ` be the exact flow from `(tₙ, Yₙ)`.  Then for `n ≤ N`

    ‖Yₙ - A(tₙ)‖ ≤ exp(L n h) (‖Y₀ - A(t₀)‖ + n h (7 L B h + ε) + ∑_{k<n} ϑₖ).

([CerutiKuschLubich2024, §4.2], via Lady Windermere's fan.) -/
theorem parallelBUG_global_error_sum {F : ℝ → E → E} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {P Q : ℕ → E →L[ℝ] E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YL n) (YS n))
    (hε : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - P n) ((1 - Q n) (F t (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {ϑ : ℕ → ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
      (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖ ≤ ϑ n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * (h * (7 * L * B * h + ε))
        + ∑ k ∈ range n, ϑ k) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (7 * L * B * h + ε) + ϑ n := by
    intro n hn
    have hlt : t₀ + n * h ≤ t₀ + (n + 1) * h := by nlinarith
    have h1 := (hstep n hn).local_error hF hL hB hlt (hΦ n hn) (hΦ₀ n hn) (hε n hn)
    rw [show t₀ + (n + 1) * h - (t₀ + n * h) = h by ring] at h1
    calc ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖
        ≤ ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
            (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖
          + ‖parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
            (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))
              - Φ n (t₀ + (n + 1) * h)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ϑ n + h * (7 * L * B * h + ε) := add_le_add (htr n hn) h1
      _ = h * (7 * L * B * h + ε) + ϑ n := add_comm _ _
  intro n hn
  have key := lady_windermere_sum hF hL hh hA hΦ hΦ₀
    (ℓ := fun k => h * (7 * L * B * h + ε) + ϑ k) hloc n hn
  rwa [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← add_assoc] at key

/-- **Global error of the parallel rank-adaptive BUG integrator** ([CerutiKuschLubich2024],
**Theorem 4.1**, in the form of [Kusch2025, Thm. 2.2]).  Under the hypotheses of
`parallelBUG_global_error_sum` with a uniform truncation tolerance `ϑ ≥ 0` and `ε ≥ 0`, for
`n ≤ N` with `n h ≤ T`

    ‖Yₙ - A(tₙ)‖ ≤ exp(L T) (δ + T (7 L B h + ε) + n ϑ),   δ = ‖Y₀ - A(t₀)‖,

i.e. `C₀ δ + C₁ h + C₂ ε + C₃ n ϑ` with `C₀ = C₃ = e^{LT}`, `C₁ = 7 L B T e^{LT}`,
`C₂ = T e^{LT}`, independent of singular values. -/
theorem parallelBUG_global_error {F : ℝ → E → E} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {P Q : ℕ → E →L[ℝ] E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YL n) (YS n))
    (hε : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - P n) ((1 - Q n) (F t (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
      (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖ ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (7 * L * B * h + ε) + n * ϑ) := by
  intro n hn hT
  have h1 := parallelBUG_global_error_sum hF hL hB hh hA hstep hε hΦ hΦ₀ (ϑ := fun _ => ϑ) htr
    n hn
  rw [sum_const, card_range, nsmul_eq_mul] at h1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ (A t₀))
  have hc : 0 ≤ 7 * L * B * h + ε := by positivity
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hin : ‖Y 0 - A t₀‖ + n * (h * (7 * L * B * h + ε)) + n * ϑ ≤
      ‖Y 0 - A t₀‖ + T * (7 * L * B * h + ε) + n * ϑ := by
    rw [← mul_assoc]; gcongr
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * (7 * L * B * h + ε)) + n * ϑ := by positivity
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

/-- **Theorem 4.1 of [CerutiKuschLubich2024], verbatim form.**  Under the hypotheses of
`parallelBUG_global_error` with `h > 0`, for `0 ≤ n h ≤ T`

    ‖Yₙ - A(tₙ)‖ ≤ C₀ δ + C₁ h + C₂ ε + C₃ ϑ / h

with `C₀ = e^{LT}`, `C₁ = 7 L B T e^{LT}`, `C₂ = C₃ = T e^{LT}`, which depend only on the
bound `B` and Lipschitz constant `L` of `F` and on `T`. -/
theorem parallelBUG_global_error_paper {F : ℝ → E → E} {L B ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) {t₀ h : ℝ} (hh : 0 < h) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {P Q : ℕ → E →L[ℝ] E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YL n) (YS n))
    (hε : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - P n) ((1 - Q n) (F t (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
      (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖ ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * ‖Y 0 - A t₀‖ + 7 * L * B * T * Real.exp (L * T) * h
        + T * Real.exp (L * T) * ε + T * Real.exp (L * T) * (ϑ / h) := by
  intro n hn hT
  have h1 := parallelBUG_global_error hF hL hB hε0 hh.le hA hstep hε hΦ hΦ₀ hϑ htr n hn hT
  have hn' : (n : ℝ) ≤ T / h := (le_div_iff₀ hh).2 hT
  have hnϑ : (n : ℝ) * ϑ ≤ T * (ϑ / h) := by
    calc (n : ℝ) * ϑ ≤ T / h * ϑ := mul_le_mul_of_nonneg_right hn' hϑ
      _ = T * (ϑ / h) := by ring
  calc ‖Y n - A (t₀ + n * h)‖
      ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (7 * L * B * h + ε) + n * ϑ) := h1
    _ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (7 * L * B * h + ε) + T * (ϑ / h)) := by
        gcongr
    _ = _ := by ring

/-- **Global error with the normal-component assumption at the grid points only**
(Assumption 2 of [CerutiKuschLubich2024, Thm. 4.1], verbatim:
`‖(1-Pₙ)(1-Qₙ) F(tₙ, Yₙ)‖ ≤ ε`), for `F` additionally `Lₜ`-Lipschitz in time.  Then for
`n ≤ N` with `n h ≤ T`: `‖Yₙ - A(tₙ)‖ ≤ exp(L T) (δ + T ((7 L B + Lₜ) h + ε) + n ϑ)`. -/
theorem parallelBUG_global_error_of_timeLipschitz {F : ℝ → E → E} {L B ε Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε0 : 0 ≤ ε)
    (hLt : 0 ≤ Lt) (hFt : ∀ t s x, ‖F t x - F s x‖ ≤ Lt * |t - s|) {t₀ h : ℝ} (hh : 0 ≤ h)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E}
    {P Q : ℕ → E →L[ℝ] E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParallelBUGStep F (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YL n) (YS n))
    (hε : ∀ n < N, ‖(1 - P n) ((1 - Q n) (F (t₀ + n * h) (Y n)))‖ ≤ ε)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (htr : ∀ n < N, ‖Y (n + 1) - parallelBUG (P n) (Q n) (YK n (t₀ + (n + 1) * h))
      (YL n (t₀ + (n + 1) * h)) (YS n (t₀ + (n + 1) * h))‖ ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T → ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * ((7 * L * B + Lt) * h + ε) + n * ϑ) := by
  intro n hn hT
  have hε' : ∀ n < N, ∀ t ∈ Ico (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖(1 - P n) ((1 - Q n) (F t (Y n)))‖ ≤ ε + Lt * h := fun k hk t ht =>
    norm_map_le_of_timeLipschitz ((1 - P k) * (1 - Q k))
      (fun x => ((hstep k hk).orthP.compl.norm_le _).trans
        ((hstep k hk).orthQ.compl.norm_le x)) hLt (hε k hk) (hFt _ _ _)
      (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
  have h1 := parallelBUG_global_error hF hL hB (by positivity) hh hA hstep hε' hΦ hΦ₀ hϑ htr
    n hn hT
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- The hypotheses of the global theorems are jointly satisfiable, with a sharp bound: on
`E = ℝ` with `Pₙ = Qₙ = 0`, `F ≡ 1` (`L = 0`, `B = 1`, `ε = 1`), `h = 1`, all numerical values
`Yₙ = 0` (no truncation, `ϑ = 0`), exact flows `Φₙ(t) = t - n` and exact solution `A(t) = t`,
the error at `tₙ = n` is `n`, which equals the bound `T (7 L B h + ε)` for `T = n`. -/
example : ∀ n : ℕ, n ≤ 3 → (n : ℝ) * 1 ≤ n → ‖(0 : ℝ) - (0 + n * 1)‖ ≤
    Real.exp (0 * n) * (‖(0 : ℝ) - 0‖ + n * (7 * 0 * 1 * 1 + 1) + n * 0) := fun n hn hT =>
  parallelBUG_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) zero_le_one (t₀ := 0) (h := 1)
    zero_le_one (N := 3) (A := fun t => t) ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩
    (Y := fun _ => 0) (P := fun _ => 0) (Q := fun _ => 0) (YK := fun _ _ => 0)
    (YL := fun _ _ => 0) (YS := fun _ _ => 0) (Φ := fun k t => t - k)
    (fun _ _ =>
      { orthP := IsOrthProj.zero
        orthQ := IsOrthProj.zero
        comm := fun _ => rfl
        fixP := by simp
        fixQ := by simp
        solK := ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩
        initK := rfl
        solL := ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩
        initL := rfl
        solS := ⟨continuousOn_const, fun _ _ => by simpa using hasDerivWithinAt_const _ _ (0 : ℝ)⟩
        initS := rfl })
    (fun _ _ _ _ => by simp)
    (fun _ _ => ⟨continuousOn_id.sub continuousOn_const,
      fun t _ => (hasDerivWithinAt_id t _).sub_const _⟩)
    (fun _ _ => by simp) le_rfl (fun _ _ => by simp [parallelBUG]) (T := (n : ℝ)) n hn hT

end Global

/-! ### Explicit Euler substeps: the tangent-projected Euler step and CFL inheritance -/

section Euler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Parallel BUG with explicit Euler substeps is the tangent-projected Euler step**
([CerutiKuschLubich2024, §5.1]). If the K-, L- and S-steps are each solved by one explicit Euler
step with the frozen field `f = F(t₀, Y₀)` — `YK(t₁) = Y₀ + h Q₀ f`, `YL(t₁) = Y₀ + h P₀ f`,
`YS(t₁) = Y₀ + h P₀Q₀ f` (matrix form: `K₁ = U₀S₀ + h F₀V₀`, `L₁ = V₀S₀ᵀ + h F₀ᵀU₀`,
`S̄₁ = S₀ + h U₀ᵀF₀V₀`) — then `Ŷ₁ = P(Y₀)(Y₀ + h f) = Y₀ + h P(Y₀) f` with the tangent projector
`P(Y₀) = tangent P₀ Q₀`. -/
theorem parallelBUG_euler {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {Y₀ : E}
    (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) (h : ℝ) (f : E) :
    parallelBUG P₀ Q₀ (Y₀ + h • Q₀ f) (Y₀ + h • P₀ f) (Y₀ + h • P₀ (Q₀ f)) =
      tangent P₀ Q₀ (Y₀ + h • f) := by
  simp only [parallelBUG, tangent_apply, sub_apply, one_apply_eq_self, map_add, map_smul,
    hPY, hQY, hc]
  module

/-- **CFL inheritance, one step** ([CerutiKuschLubich2024, §5.1]).  With explicit Euler substeps and
commuting orthogonal projectors `P₀`, `Q₀` fixing `Y₀`, `‖Ŷ₁‖ ≤ ‖Y₀ + h f‖`: the parallel BUG step
is never larger than the full explicit Euler step. -/
theorem parallelBUG_euler_norm_le {P₀ Q₀ : E →L[ℝ] E} (hP : IsOrthProj P₀) (hQ : IsOrthProj Q₀)
    (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) {Y₀ : E} (hPY : P₀ Y₀ = Y₀) (hQY : Q₀ Y₀ = Y₀) (h : ℝ)
    (f : E) :
    ‖parallelBUG P₀ Q₀ (Y₀ + h • Q₀ f) (Y₀ + h • P₀ f) (Y₀ + h • P₀ (Q₀ f))‖ ≤
      ‖Y₀ + h • f‖ := by
  rw [parallelBUG_euler hc hPY hQY]
  exact (hP.tangent hQ hc).norm_le _

/-- **CFL inheritance** ([CerutiKuschLubich2024, §5.1]). Run the parallel BUG integrator with
explicit Euler substeps on the grid `tₙ = t₀ + n h`: step `n` uses commuting orthogonal projectors
`Pₙ`, `Qₙ` fixing `Yₙ` and the field `fₙ = F(tₙ, Yₙ)`, and the truncation does not increase the
norm, `‖Yₙ₊₁‖ ≤ ‖Ŷₙ₊₁‖` (true for SVD truncation). If the full explicit Euler step is stable at the
iterates, `‖Yₙ + h F(tₙ, Yₙ)‖ ≤ ‖Yₙ‖` (e.g. under the CFL condition of the full problem), then
`‖Yₙ‖ ≤ ‖Y₀‖` for all `n ≤ N`. -/
theorem parallelBUG_euler_stable {F : ℝ → E → E} {t₀ h : ℝ} {N : ℕ} {Y : ℕ → E}
    {P Q : ℕ → E →L[ℝ] E} (hP : ∀ n < N, IsOrthProj (P n)) (hQ : ∀ n < N, IsOrthProj (Q n))
    (hc : ∀ n < N, ∀ x, P n (Q n x) = Q n (P n x)) (hPY : ∀ n < N, P n (Y n) = Y n)
    (hQY : ∀ n < N, Q n (Y n) = Y n)
    (hCFL : ∀ n < N, ‖Y n + h • F (t₀ + n * h) (Y n)‖ ≤ ‖Y n‖)
    (htr : ∀ n < N, ‖Y (n + 1)‖ ≤ ‖parallelBUG (P n) (Q n)
      (Y n + h • Q n (F (t₀ + n * h) (Y n))) (Y n + h • P n (F (t₀ + n * h) (Y n)))
      (Y n + h • P n (Q n (F (t₀ + n * h) (Y n))))‖) :
    ∀ n ≤ N, ‖Y n‖ ≤ ‖Y 0‖ := by
  intro n
  induction n with
  | zero => intro _; exact le_rfl
  | succ k ih =>
    intro hk
    have hk' : k < N := hk
    calc ‖Y (k + 1)‖ ≤ _ := htr k hk'
      _ ≤ ‖Y k + h • F (t₀ + k * h) (Y k)‖ :=
        parallelBUG_euler_norm_le (hP k hk') (hQ k hk') (hc k hk') (hPY k hk') (hQY k hk') _ _
      _ ≤ ‖Y k‖ := hCFL k hk'
      _ ≤ ‖Y 0‖ := ih hk'.le

/-- The hypotheses of `parallelBUG_euler_stable` are jointly satisfiable non-trivially: on
`E = ℝ` with `Pₙ = Qₙ = 1`, `F(t, x) = -x`, `h = 1/2`, the iterates `Yₙ = 2⁻ⁿ` are produced
exactly (no truncation) and the full Euler step `x ↦ x/2` is stable. -/
example : ∀ n ≤ 5, ‖((1 : ℝ) / 2) ^ n‖ ≤ ‖((1 : ℝ) / 2) ^ 0‖ :=
  parallelBUG_euler_stable (E := ℝ) (F := fun _ x => -x) (t₀ := 0) (h := 1 / 2) (N := 5)
    (Y := fun n => ((1 : ℝ) / 2) ^ n) (P := fun _ => 1) (Q := fun _ => 1)
    (fun _ _ => IsOrthProj.one) (fun _ _ => IsOrthProj.one) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun n _ => by
      have h0 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      simp only [smul_eq_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
      linarith)
    (fun n _ => by
      simp only [parallelBUG, smul_eq_mul, one_apply_eq_self, sub_self,
        zero_apply, add_zero, pow_succ]
      apply le_of_eq
      congr 1
      ring)

end Euler

/-! ### Matrix form of the augmented coefficient matrix -/

section MatrixBlocks

open Matrix

variable {m n r : Type*} [Fintype r] {R : Type*} [CommRing R]

/-- **Block expansion of `Û Ŝ₁ V̂ᵀ`** ([CerutiKuschLubich2024], (3.4)).  With `Û = [U₀, Ũ₁]`,
`V̂ = [V₀, Ṽ₁]` and `Ŝ₁ = [[S̄, S̃ᴸ], [S̃ᴷ, 0]]`,
`Û Ŝ₁ V̂ᵀ = U₀ S̄ V₀ᵀ + Ũ₁ S̃ᴷ V₀ᵀ + U₀ S̃ᴸ Ṽ₁ᵀ`. -/
theorem matrix_parallelBUG_blocks (U₀ U₁ : Matrix m r R) (V₀ V₁ : Matrix n r R)
    (Sbar SK SL : Matrix r r R) :
    fromCols U₀ U₁ * fromBlocks Sbar SL SK 0 * (fromCols V₀ V₁)ᵀ =
      U₀ * Sbar * V₀ᵀ + U₁ * SK * V₀ᵀ + U₀ * SL * V₁ᵀ := by
  rw [fromCols_mul_fromBlocks, transpose_fromCols, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, Matrix.add_mul]

/-- **The paper's `Û Ŝ₁ V̂ᵀ` is the abstract `parallelBUG`** (matrix form).  Let
`Û = [U₀, Ũ₁]` and `V̂ = [V₀, Ṽ₁]` capture `K₁ = K(t₁)` and `L₁ = L(t₁)`
(`Û Ûᵀ K₁ = K₁`, `V̂ V̂ᵀ L₁ = L₁`, as for orthonormal bases of the ranges of `[U₀, K₁]` and
`[V₀, L₁]`), and `Ŝ₁ = [[S̄, L₁ᵀṼ₁], [Ũ₁ᵀK₁, 0]]` as in (3.4).  Then

    Û Ŝ₁ V̂ᵀ = U₀ S̄ V₀ᵀ + (I - U₀U₀ᵀ)(K₁ V₀ᵀ) + (U₀ L₁ᵀ)(I - V₀V₀ᵀ),

which is `YS(t₁) + (1 - P₀) YK(t₁) + (1 - Q₀) YL(t₁)` for `P₀ X = U₀U₀ᵀX`, `Q₀ X = XV₀V₀ᵀ`,
`YK = K V₀ᵀ`, `YL = U₀ Lᵀ`, `YS = U₀ S̄ V₀ᵀ`.  (Orthonormality of `Û`, `V̂` is not needed for
this identity.) -/
theorem matrix_parallelBUG_eq [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (U₀ U₁ : Matrix m r R) (V₀ V₁ : Matrix n r R) (Sbar : Matrix r r R) (K₁ : Matrix m r R)
    (L₁ : Matrix n r R) (hU : fromCols U₀ U₁ * (fromCols U₀ U₁)ᵀ * K₁ = K₁)
    (hV : fromCols V₀ V₁ * (fromCols V₀ V₁)ᵀ * L₁ = L₁) :
    fromCols U₀ U₁ * fromBlocks Sbar (L₁ᵀ * V₁) (U₁ᵀ * K₁) 0 * (fromCols V₀ V₁)ᵀ =
      U₀ * Sbar * V₀ᵀ + (1 - U₀ * U₀ᵀ) * (K₁ * V₀ᵀ) + U₀ * L₁ᵀ * (1 - V₀ * V₀ᵀ) := by
  rw [matrix_parallelBUG_blocks]
  rw [transpose_fromCols, fromCols_mul_fromRows, Matrix.add_mul] at hU hV
  have hU' : U₁ * U₁ᵀ * K₁ = K₁ - U₀ * U₀ᵀ * K₁ := eq_sub_of_add_eq' hU
  have hV' : L₁ᵀ * V₁ * V₁ᵀ = L₁ᵀ - L₁ᵀ * V₀ * V₀ᵀ := by
    have h := congrArg transpose hV
    simp only [transpose_add, transpose_mul, transpose_transpose, Matrix.mul_assoc] at h
    simp only [Matrix.mul_assoc]
    exact eq_sub_of_add_eq' h
  have e1 : U₁ * (U₁ᵀ * K₁) * V₀ᵀ = (1 - U₀ * U₀ᵀ) * (K₁ * V₀ᵀ) := by
    rw [← Matrix.mul_assoc U₁, hU', Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc (U₀ * U₀ᵀ)]
  have e2 : U₀ * (L₁ᵀ * V₁) * V₁ᵀ = U₀ * L₁ᵀ * (1 - V₀ * V₀ᵀ) := by
    rw [Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hV']
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1, e2]

end MatrixBlocks

section MatrixRejection

open Matrix

variable {m n r s : Type*} [Fintype r] [Fintype s] {R : Type*} [CommRing R]

/-- The augmented projector splits: `ÛÛᵀ = U₀U₀ᵀ + Ũ₁Ũ₁ᵀ` for `Û = [U₀, Ũ₁]`. -/
theorem matrix_augmented_proj (U₀ : Matrix m r R) (U₁ : Matrix m s R) :
    fromCols U₀ U₁ * (fromCols U₀ U₁)ᵀ = U₀ * U₀ᵀ + U₁ * U₁ᵀ := by
  rw [transpose_fromCols, fromCols_mul_fromRows]

/-- **Identity (3.11) of [CerutiKuschLubich2024]** (matrix form).  Let `U₀`, `V₀` have orthonormal
columns and let the new directions be orthogonal to them, `U₀ᵀŨ₁ = 0`, `V₀ᵀṼ₁ = 0`.  Then for
every `F₀`
`(I - U₀U₀ᵀ) [ÛÛᵀ F₀ V̂V̂ᵀ] (I - V₀V₀ᵀ) = Ũ₁Ũ₁ᵀ F₀ Ṽ₁Ṽ₁ᵀ`, i.e. the normal component at
`Y₀ = U₀S₀V₀ᵀ` (`P⊥(Y₀) Z = (I - U₀U₀ᵀ) Z (I - V₀V₀ᵀ)`) of the projection of `F₀` onto the augmented
space.  When `Ũ₁`, `Ṽ₁` also have orthonormal columns its Frobenius norm is
`η = ‖Ũ₁ᵀ F₀ Ṽ₁‖`, the step-rejection indicator of §3.3. -/
theorem matrix_normal_augmented_eq [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [DecidableEq r] (U₀ : Matrix m r R) (U₁ : Matrix m s R) (V₀ : Matrix n r R)
    (V₁ : Matrix n s R) (F₀ : Matrix m n R) (hU₀ : U₀ᵀ * U₀ = 1) (hU₀₁ : U₀ᵀ * U₁ = 0)
    (hV₀ : V₀ᵀ * V₀ = 1) (hV₀₁ : V₀ᵀ * V₁ = 0) :
    (1 - U₀ * U₀ᵀ) * (fromCols U₀ U₁ * (fromCols U₀ U₁)ᵀ * F₀ *
        (fromCols V₀ V₁ * (fromCols V₀ V₁)ᵀ)) * (1 - V₀ * V₀ᵀ) =
      U₁ * U₁ᵀ * F₀ * (V₁ * V₁ᵀ) := by
  have hV₁₀ : V₁ᵀ * V₀ = 0 := by
    rw [← transpose_transpose (V₁ᵀ * V₀), transpose_mul, transpose_transpose, hV₀₁,
      transpose_zero]
  have hl : (1 - U₀ * U₀ᵀ) * (U₀ * U₀ᵀ + U₁ * U₁ᵀ) = U₁ * U₁ᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_assoc U₀ U₀ᵀ (U₀ * U₀ᵀ),
      ← Matrix.mul_assoc U₀ᵀ, hU₀, Matrix.one_mul, Matrix.mul_assoc U₀ U₀ᵀ (U₁ * U₁ᵀ),
      ← Matrix.mul_assoc U₀ᵀ, hU₀₁, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    abel
  have hr : (V₀ * V₀ᵀ + V₁ * V₁ᵀ) * (1 - V₀ * V₀ᵀ) = V₁ * V₁ᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc V₀ V₀ᵀ (V₀ * V₀ᵀ),
      ← Matrix.mul_assoc V₀ᵀ, hV₀, Matrix.one_mul, Matrix.mul_assoc V₁ V₁ᵀ (V₀ * V₀ᵀ),
      ← Matrix.mul_assoc V₁ᵀ, hV₁₀, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    abel
  rw [matrix_augmented_proj, matrix_augmented_proj]
  calc (1 - U₀ * U₀ᵀ) * ((U₀ * U₀ᵀ + U₁ * U₁ᵀ) * F₀ * (V₀ * V₀ᵀ + V₁ * V₁ᵀ)) * (1 - V₀ * V₀ᵀ)
      = (1 - U₀ * U₀ᵀ) * (U₀ * U₀ᵀ + U₁ * U₁ᵀ) * F₀ *
          ((V₀ * V₀ᵀ + V₁ * V₁ᵀ) * (1 - V₀ * V₀ᵀ)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hl, hr]

end MatrixRejection

end LeanDLRA
