import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Training.Descent

/-!
# Results of arXiv 2506.17475: Geometric momentum for low-rank training

Schotthöfer, Klein, Kusch, *A geometric framework for momentum-based optimizers for low-rank
training*.  This module works on real matrices with the Frobenius inner product, and where
nothing matrix-specific is needed on a real inner product space.  It proves Theorem 2, the
factorised momentum flow (`momentumFactorFlow`, with the orthonormality of the factors derived);
the derivation of the bases of Algorithms 1 and 2 (`hasDerivWithinAt_KFlow`,
`hasDerivWithinAt_LFlow`, `colSpan_sup_KStep`, `colSpan_sup_LStep`, `hasFDerivAt_coeff`); the
energy identity of Theorem 1 (`hasDerivWithinAt_heavyBall_energy`, sharpening the inequality
`LeanDLRA.heavyBall_energy_le`) and a corrected Theorem 1 (`heavyBall_tendsto`,
`heavyBall_limit_stationary`, `heavyBall_tendsto_tangentProj`, a Barbalat argument without
integrals); a corrected Theorem 3 for Algorithm 1 in factorised form with free rank changes
(`IsLRHeavyBallStep`, `lowRankHeavyBall_error`, `lowRankHeavyBall_error_le`,
`lowRankHeavyBall_error_fullFlow`); and Theorem 4 with a genuine trajectory (`naiveFlow_failure`,
using the identities `IsNaiveFlow.hasDerivAt_weight`, `IsNaiveFlow.hasDerivAt_momentum`, and
extending the algebraic core `LeanDLRA.naiveMomentum_apply_eq_zero_of_left`).

**Claims of the paper that are false, with proved counterexamples.**
(1) Theorem 1: `W(t)` need not converge when `ℒ` is only bounded below
(`heavyBall_not_convergent`, even with a Lipschitz gradient); what survives is
`𝒱 → 0`, `P ∇ℒ(W) → 0` and stationarity of limits, under a Lipschitz gradient and `σ_min ≥ ρ`.
(2) Theorem 3 with Algorithm 1 as printed, damping `1 - γ` with the `γ` of Eq. (7):
`lowRankHeavyBall_printedDamping_false`.  (If the `γ` of Algorithm 1 is read as `λ γ`, this is the
damping `1 - λ γ` of Eqs. (3a)-(3c) and of `lowRankHeavyBall_error`.)
(3) Theorem 3 with damping `1 - λ γ` but without a bound on `(I - P(W)) 𝒱` along the flow:
`lowRankHeavyBall_needs_normalMomentum`.  The paper's proof uses `Ẇ = 𝒱` in place of
`Ẇ = P(W) 𝒱`; the bound does hold against the full-rank flow.  Caveat: the gradient of that
counterexample is Lipschitz and bounded along both trajectories but not on all of `ℝ^{2×2}`,
whereas Theorem 3 assumes a bounded gradient; so it refutes the damping-corrected statement with
boundedness required only along the trajectories (the setting of `lowRankHeavyBall_error`).  A
cutoff of `ℒ` away from the trajectories would remove this gap, but it is not formalized.
(4) The proof of Theorem 4: the configuration `U_𝒱 = -U`, `S_𝒱 = 0`, `V_𝒱 = V` is not stationary
for `S ≠ 0` (`naiveFlow_not_stationary`); it stalls for `S = 0` (`naiveFlow_stall_of_singular`).
The statement of Theorem 4 is true: `naiveFlow_failure`, with `S(t)` invertible for all `t`, a limit
of lower rank and tuned initial data (a stable manifold of a saddle).
(5) A slip: the displayed `K̇_𝒱 = -∇ℒ V⁰` drops `-γ K_𝒱`; this does not affect the spans.

**Other differences.**  Theorem 3 has constants growing like `e^{(1 + β) T}`, and uses
`‖∇ℒ‖ ≤ B` along the two trajectories only.  The spans in terms of `∇_U ℒ` need invertible `S⁰`.

**Not treated.**  Algorithm 2 (low-rank Adam) beyond its shared bases; convergence of bounded
trajectories to a single point (which needs a Łojasiewicz inequality; the failure of convergence
here is by escape to infinity); trajectories of Eq. (7) that leave `ℳ_r`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2506_17475

/-! ### Theorem 2: the factorised momentum flow -/

section FactorFlow

open scoped LeanDLRA.Frobenius
open LeanDLRA LeanDLRA.GaugeODE

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- Pointwise algebra behind Theorem 2 of arXiv 2506.17475 (Eq. (12)). -/
theorem factorFlow_sum_eq [DecidableEq m] [DecidableEq n] [DecidableEq r] (U : Matrix m r ℝ)
    (S : Matrix r r ℝ) (V : Matrix n r ℝ) (G : Matrix m n ℝ) (γ : ℝ) (hS : IsUnit S.det) :
    (-((1 - U * Uᵀ) * G * V * S⁻¹)) * S * Vᵀ + U * (-(γ • S) - Uᵀ * G * V) * Vᵀ
        + U * S * (-((1 - V * Vᵀ) * Gᵀ * U * (S⁻¹)ᵀ))ᵀ
      = -(γ • (U * S * Vᵀ)) - tangentProj U V G := by
  have h := factorODE_sum_eq_tangent U S V G hS
  rw [tangentProj_apply, ← h]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.transpose_neg, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  abel

/-- Continuity of the inverse along a curve of invertible matrices. -/
theorem continuousOn_matrix_inv [DecidableEq r] {X : ℝ → Matrix r r ℝ} {s : Set ℝ}
    (hX : ContinuousOn X s) (hdet : ∀ t ∈ s, IsUnit (X t).det) :
    ContinuousOn (fun t => (X t)⁻¹) s := by
  have h1 : ContinuousOn (fun t => (X t).det) s := by
    have : Continuous (fun A : Matrix r r ℝ => A.det) := continuous_id.matrix_det
    exact this.comp_continuousOn hX
  have h2 : ContinuousOn (fun t => (X t).adjugate) s := by
    have : Continuous (fun A : Matrix r r ℝ => A.adjugate) := continuous_id.matrix_adjugate
    exact this.comp_continuousOn hX
  have h3 : ContinuousOn (fun t => ((X t).det)⁻¹) s :=
    h1.inv₀ fun t ht => (hdet t ht).ne_zero
  have h4 : ContinuousOn (fun t => ((X t).det)⁻¹ • (X t).adjugate) s := h3.smul h2
  refine h4.congr fun t _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

/-- A curve continuous on `[a, b)` is bounded on `[a, b')` for every `b' < b`. -/
theorem exists_bound_Ico {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Ico a b)) (b' : ℝ) (hb' : b' < b) :
    ∃ C, ∀ t ∈ Ico a b', ‖f t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.mono fun t ht => ⟨ht.1, ht.2.trans_lt hb'⟩ : ContinuousOn f (Icc a b'))
  exact ⟨C, fun t ht => hC t ⟨ht.1, ht.2.le⟩⟩

variable {Uv : ℝ → Matrix m r ℝ} {Sv : ℝ → Matrix r r ℝ} {Vv : ℝ → Matrix n r ℝ}
  {G : ℝ → Matrix m n ℝ} {γ a b : ℝ}

/-- Orthonormality of one factor along `U̇ = -(I - U Uᵀ) G V S⁻¹`. -/
theorem orthonormal_of_factorFlow [DecidableEq m] [DecidableEq r] {X H : ℝ → Matrix m r ℝ}
    (hX : ODESolution (fun t Y => -((1 - Y * Yᵀ) * H t)) X a b)
    (hH : ContinuousOn H (Ico a b)) (ha : (X a)ᵀ * X a = 1) :
    ∀ t ∈ Icc a b, (X t)ᵀ * X t = 1 := by
  have hX' : ODESolution (fun t Y => (1 - Y * Yᵀ) * (-H t)) X a b := by
    refine ⟨hX.cont, fun t ht => ?_⟩
    have := hX.deriv t ht
    simpa only [Matrix.mul_neg] using this
  refine transpose_mul_self_eq_one_of_odeSolution hX' (fun b' hb' => ?_) ha
  have hc : ContinuousOn (fun t => (X t)ᵀ * (-H t)) (Ico a b) :=
    GaugeODE.continuousOn_mul
      (GaugeODE.continuousOn_transpose (hX.cont.mono Ico_subset_Icc_self)) hH.neg
  exact exists_bound_Ico hc b' hb'

/-- **Theorem 2 of arXiv 2506.17475 (factorised momentum flow).**  Let `G(t)` be a curve of
matrices, continuous on `[a, b)` (in the paper `G(t) = ∇_W ℒ(W(t))`), and let `U_𝒱`, `S_𝒱`, `V_𝒱`
solve on `[a, b]` the factor system (Eqs. (9), (11))
`U̇_𝒱 = -(I - U_𝒱 U_𝒱ᵀ) G V_𝒱 S_𝒱⁻¹`, `V̇_𝒱 = -(I - V_𝒱 V_𝒱ᵀ) Gᵀ U_𝒱 S_𝒱⁻ᵀ`,
`Ṡ_𝒱 = -γ S_𝒱 - U_𝒱ᵀ G V_𝒱`, with `S_𝒱(t)` invertible on `[a, b)`.

If the factors are orthonormal at the initial time, then they stay orthonormal on `[a, b]`, which
the paper takes for granted, and `𝒱 = U_𝒱 S_𝒱 V_𝒱ᵀ` solves `𝒱̇ = -γ 𝒱 - P(𝒱) G`, with
`P(𝒱) = tangentProj U_𝒱 V_𝒱` the orthogonal tangent projector (it depends on `𝒱` only, see
`LeanDLRA.tangentProj_eq_of_factorization`).  The solution notion is `ODESolution`: continuity on
`[a, b]` and right derivatives on `[a, b)`. -/
theorem momentumFactorFlow [DecidableEq m] [DecidableEq n] [DecidableEq r]
    (hU : ODESolution (fun t X => -((1 - X * Xᵀ) * G t * Vv t * (Sv t)⁻¹)) Uv a b)
    (hV : ODESolution (fun t X => -((1 - X * Xᵀ) * (G t)ᵀ * Uv t * ((Sv t)⁻¹)ᵀ)) Vv a b)
    (hS : ODESolution (fun t X => -(γ • X) - (Uv t)ᵀ * G t * Vv t) Sv a b)
    (hdet : ∀ t ∈ Ico a b, IsUnit (Sv t).det) (hG : ContinuousOn G (Ico a b))
    (hUa : (Uv a)ᵀ * Uv a = 1) (hVa : (Vv a)ᵀ * Vv a = 1) :
    (∀ t ∈ Icc a b, (Uv t)ᵀ * Uv t = 1 ∧ (Vv t)ᵀ * Vv t = 1 ∧
        IsOrthProj (tangentProj (Uv t) (Vv t) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)) ∧
      ODESolution (fun t Y => -(γ • Y) - tangentProj (Uv t) (Vv t) (G t))
        (fun t => Uv t * Sv t * (Vv t)ᵀ) a b := by
  have hUc : ContinuousOn Uv (Ico a b) := hU.cont.mono Ico_subset_Icc_self
  have hVc : ContinuousOn Vv (Ico a b) := hV.cont.mono Ico_subset_Icc_self
  have hSc : ContinuousOn Sv (Ico a b) := hS.cont.mono Ico_subset_Icc_self
  have hSi := continuousOn_matrix_inv hSc hdet
  have hH1 : ContinuousOn (fun t => G t * Vv t * (Sv t)⁻¹) (Ico a b) :=
    GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul hG hVc) hSi
  have hH2 : ContinuousOn (fun t => (G t)ᵀ * Uv t * ((Sv t)⁻¹)ᵀ) (Ico a b) :=
    GaugeODE.continuousOn_mul
      (GaugeODE.continuousOn_mul (GaugeODE.continuousOn_transpose hG) hUc)
      (GaugeODE.continuousOn_transpose hSi)
  have hUo := orthonormal_of_factorFlow (H := fun t => G t * Vv t * (Sv t)⁻¹)
    ⟨hU.cont, fun t ht => by simpa only [Matrix.mul_assoc] using hU.deriv t ht⟩ hH1 hUa
  have hVo := orthonormal_of_factorFlow (H := fun t => (G t)ᵀ * Uv t * ((Sv t)⁻¹)ᵀ)
    ⟨hV.cont, fun t ht => by simpa only [Matrix.mul_assoc] using hV.deriv t ht⟩ hH2 hVa
  refine ⟨fun t ht => ⟨hUo t ht, hVo t ht, isOrthProj_tangentProj (hUo t ht) (hVo t ht)⟩, ?_, ?_⟩
  · exact GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul hU.cont hS.cont)
      (GaugeODE.continuousOn_transpose hV.cont)
  · intro t ht
    have h := hasDerivWithinAt_factorProduct (hU.deriv t ht) (hS.deriv t ht) (hV.deriv t ht)
    rwa [factorFlow_sum_eq _ _ _ _ _ (hdet t ht)] at h

/-- **Derivation of Algorithms 1 and 2 of arXiv 2506.17475: the `K`-equation.**  Along the factor
flow of Theorem 2, `K_𝒱 = U_𝒱 S_𝒱` satisfies `K̇_𝒱 = -G V_𝒱 - γ K_𝒱`: the inverse `S_𝒱⁻¹` has
disappeared.  **Difference from the paper:** the paper displays `K̇_𝒱 = -G V⁰` and thereby drops
the damping term `-γ K_𝒱`, which the product rule produces; the term does not affect the
span statement `colSpan_sup_KStep`, whose scalar `c` covers both versions. -/
theorem hasDerivWithinAt_KFlow [DecidableEq m] [DecidableEq r] {s : Set ℝ} {t : ℝ}
    (hdet : IsUnit (Sv t).det)
    (hU : HasDerivWithinAt Uv (-((1 - Uv t * (Uv t)ᵀ) * G t * Vv t * (Sv t)⁻¹)) s t)
    (hS : HasDerivWithinAt Sv (-(γ • Sv t) - (Uv t)ᵀ * G t * Vv t) s t) :
    HasDerivWithinAt (fun t => Uv t * Sv t) (-(G t * Vv t) - γ • (Uv t * Sv t)) s t := by
  refine (GaugeODE.hasDerivWithinAt_mul hU hS).congr_deriv ?_
  rw [Matrix.neg_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hdet]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  abel

/-- **Derivation of Algorithms 1 and 2 of arXiv 2506.17475: the `L`-equation.**  Along the factor
flow of Theorem 2, `L_𝒱 = V_𝒱 S_𝒱ᵀ` satisfies `L̇_𝒱 = -Gᵀ U_𝒱 - γ L_𝒱`.  The paper drops `-γ L_𝒱`
as in `hasDerivWithinAt_KFlow`. -/
theorem hasDerivWithinAt_LFlow [DecidableEq n] [DecidableEq r] {s : Set ℝ} {t : ℝ}
    (hdet : IsUnit (Sv t).det)
    (hV : HasDerivWithinAt Vv (-((1 - Vv t * (Vv t)ᵀ) * (G t)ᵀ * Uv t * ((Sv t)⁻¹)ᵀ)) s t)
    (hS : HasDerivWithinAt Sv (-(γ • Sv t) - (Uv t)ᵀ * G t * Vv t) s t) :
    HasDerivWithinAt (fun t => Vv t * (Sv t)ᵀ) (-((G t)ᵀ * Uv t) - γ • (Vv t * (Sv t)ᵀ)) s t := by
  refine (GaugeODE.hasDerivWithinAt_mul hV
    (GaugeODE.hasDerivWithinAt_transpose hS)).congr_deriv ?_
  have e : ((Sv t)⁻¹)ᵀ * (Sv t)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one]
  rw [Matrix.neg_mul, Matrix.mul_assoc _ (((Sv t)⁻¹)ᵀ), e, Matrix.mul_one]
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_neg, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_assoc]
  abel

/-- `momentumFactorFlow` is not vacuous: for `G = 0`, constant orthonormal factors and
`S_𝒱 = e^{-γ t} S₀`, `S₀` invertible, the hypotheses hold. -/
theorem momentumFactorFlow_instance [DecidableEq m] [DecidableEq n] [DecidableEq r]
    {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : IsUnit S₀.det) (γ a b : ℝ) :
    ODESolution (fun t X => -((1 - X * Xᵀ) * (0 : Matrix m n ℝ) * V₀ *
      ((Real.exp (-γ * t) • S₀)⁻¹))) (fun _ => U₀) a b ∧
    ODESolution (fun t X => -((1 - X * Xᵀ) * (0 : Matrix m n ℝ)ᵀ * U₀ *
      ((Real.exp (-γ * t) • S₀)⁻¹)ᵀ)) (fun _ => V₀) a b ∧
    ODESolution (fun _ X => -(γ • X) - U₀ᵀ * (0 : Matrix m n ℝ) * V₀)
      (fun t => Real.exp (-γ * t) • S₀) a b ∧
    ∀ t, IsUnit (Real.exp (-γ * t) • S₀).det := by
  have hE : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-γ * t)) (-γ * Real.exp (-γ * t)) t := by
    intro t
    have h : HasDerivAt (fun t => -γ * t) (-γ) t := by
      simpa using (hasDerivAt_id t).const_mul (-γ)
    exact h.exp.congr_deriv (by ring)
  have hS : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-γ * t) • S₀)
      ((-γ * Real.exp (-γ * t)) • S₀) t := fun t => (hE t).smul_const S₀
  refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, ⟨continuousOn_const, fun t _ => ?_⟩,
    ⟨fun t _ => (hS t).continuousAt.continuousWithinAt, fun t _ => ?_⟩, fun t => ?_⟩
  · simpa using hasDerivWithinAt_const t (Ici t) U₀
  · simpa using hasDerivWithinAt_const t (Ici t) V₀
  · refine (hS t).hasDerivWithinAt.congr_deriv ?_
    simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero, smul_smul]
    rw [← neg_smul]
    congr 1
    ring
  · rw [Matrix.det_smul]
    exact (IsUnit.mk0 _ (pow_ne_zero _ (Real.exp_pos _).ne')).mul hS₀

/-- The column span of a matrix. -/
def colSpan {M k : Type*} [Fintype k] (A : Matrix M k ℝ) : Submodule ℝ (M → ℝ) :=
  LinearMap.range A.mulVecLin

/-- Auxiliary for Sec. 3 of arXiv 2506.17475: `span(A B) ⊆ span A`. -/
theorem colSpan_mul_le {M k l : Type*} [Fintype k] [Fintype l] (A : Matrix M k ℝ)
    (B : Matrix k l ℝ) : colSpan (A * B) ≤ colSpan A := by
  rintro _ ⟨x, rfl⟩
  exact ⟨B.mulVecLin x, by simp [Matrix.mulVec_mulVec]⟩

/-- Auxiliary for Sec. 3 of arXiv 2506.17475: an invertible right factor does not change the column
span. -/
theorem colSpan_mul_of_isUnit {M k : Type*} [Fintype k] [DecidableEq k] (A : Matrix M k ℝ)
    {T : Matrix k k ℝ} (hT : IsUnit T.det) : colSpan (A * T) = colSpan A := by
  refine le_antisymm (colSpan_mul_le _ _) ?_
  have := colSpan_mul_le (A * T) T⁻¹
  rwa [Matrix.mul_nonsing_inv_cancel_right _ _ hT] at this

/-- Auxiliary for Sec. 3 of arXiv 2506.17475: `span(A + c B) ⊆ span[A, B]`. -/
theorem colSpan_smul_add_le {M k : Type*} [Fintype k] (A B : Matrix M k ℝ) (c : ℝ) :
    colSpan (A + c • B) ≤ colSpan A ⊔ colSpan B := by
  rintro _ ⟨x, rfl⟩
  refine Submodule.mem_sup.2 ⟨A.mulVecLin x, ⟨x, rfl⟩, B.mulVecLin (c • x), ⟨_, rfl⟩, ?_⟩
  simp

/-- Replacing `Z` by `U M + c Z` with `c ≠ 0` does not change `span[U, Z]`. -/
theorem colSpan_sup_add_smul {M k l : Type*} [Fintype k] [Fintype l] (U : Matrix M k ℝ)
    (B : Matrix k l ℝ) (Z : Matrix M l ℝ) {c : ℝ} (hc : c ≠ 0) :
    colSpan U ⊔ colSpan (U * B + c • Z) = colSpan U ⊔ colSpan Z := by
  apply le_antisymm
  · exact sup_le le_sup_left ((colSpan_smul_add_le _ _ c).trans
      (sup_le_sup_right (colSpan_mul_le _ _) _))
  · refine sup_le le_sup_left ?_
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_sup.2 ⟨U.mulVecLin (-(c⁻¹ • B.mulVec y)), ⟨_, rfl⟩,
      (U * B + c • Z).mulVecLin (c⁻¹ • y), ⟨_, rfl⟩, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_neg, ← Matrix.mulVec_mulVec]
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
    abel

omit [Fintype m] in
/-- **Derivation of Algorithms 1 and 2 of arXiv 2506.17475: the bases.**  One Euler step for the
`K`-equation from `K⁰ = U⁰ S⁰_𝒱`, namely `K¹ = c K⁰ - λ G V⁰`, spans the same space together with
`U⁰` as `∇_U ℒ = G V⁰ S⁰ᵀ`:  `span[U⁰, K¹] = span[U⁰, ∇_U ℒ(W⁰)]`.  This holds for `λ ≠ 0` and for
every `c`; the paper has `c = 1`, the exact Euler step of `hasDerivWithinAt_KFlow` has
`c = 1 - λ γ`.  The paper leaves implicit that the last equality needs the coefficient `S⁰` of
`W⁰ = U⁰ S⁰ V⁰ᵀ` to be invertible; it is a hypothesis here. -/
theorem colSpan_sup_KStep [DecidableEq r] {U : Matrix m r ℝ}
    {S Sv₀ : Matrix r r ℝ} {V : Matrix n r ℝ} {G₀ : Matrix m n ℝ} {lr c : ℝ}
    (hlr : lr ≠ 0) (hS : IsUnit S.det) :
    colSpan U ⊔ colSpan (c • (U * Sv₀) - lr • (G₀ * V)) = colSpan U ⊔ colSpan (G₀ * V * Sᵀ) := by
  have h1 : colSpan (G₀ * V * Sᵀ) = colSpan (G₀ * V) :=
    colSpan_mul_of_isUnit _ (by rwa [Matrix.det_transpose])
  have h2 : c • (U * Sv₀) - lr • (G₀ * V) = U * (c • Sv₀) + (-lr) • (G₀ * V) := by
    rw [Matrix.mul_smul, neg_smul, sub_eq_add_neg]
  rw [h1, h2, colSpan_sup_add_smul _ _ _ (neg_ne_zero.2 hlr)]

omit [Fintype n] in
/-- The `L`-counterpart of `colSpan_sup_KStep`: with `L¹ = c L⁰ - λ Gᵀ U⁰`, `L⁰ = V⁰ S⁰_𝒱ᵀ`,
we have `span[V⁰, L¹] = span[V⁰, ∇_V ℒ(W⁰)]`, `∇_V ℒ = Gᵀ U⁰ S⁰` (arXiv 2506.17475, Sec. 3). -/
theorem colSpan_sup_LStep [DecidableEq r] {U : Matrix m r ℝ}
    {S Sv₀ : Matrix r r ℝ} {V : Matrix n r ℝ} {G₀ : Matrix m n ℝ} {lr c : ℝ}
    (hlr : lr ≠ 0) (hS : IsUnit S.det) :
    colSpan V ⊔ colSpan (c • (V * Sv₀ᵀ) - lr • (G₀ᵀ * U)) = colSpan V ⊔ colSpan (G₀ᵀ * U * S) := by
  have h := colSpan_sup_KStep (m := n) (n := m) (U := V) (S := Sᵀ) (Sv₀ := Sv₀ᵀ) (V := U)
    (G₀ := G₀ᵀ) (c := c) hlr (by rwa [Matrix.det_transpose])
  rwa [Matrix.transpose_transpose] at h

/-- **Coefficient gradient in the augmented bases** (arXiv 2506.17475, Sec. 3):
if `ℒ` has gradient `g`, then `S̄ ↦ ℒ(Û S̄ V̂ᵀ)` has gradient `Ûᵀ g(Û S̄ V̂ᵀ) V̂`.  This is
the `G_S` of Algorithm 1. -/
theorem hasFDerivAt_coeff {k l : Type*} [Fintype k] [Fintype l] {ℒ : Matrix m n ℝ → ℝ}
    {g : Matrix m n ℝ → Matrix m n ℝ} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (Uh : Matrix m k ℝ) (Vh : Matrix n l ℝ) (Sb : Matrix k l ℝ) :
    HasFDerivAt (fun X => ℒ (Uh * X * Vhᵀ))
      (innerSL ℝ (Uhᵀ * g (Uh * Sb * Vhᵀ) * Vh)) Sb := by
  set φ : Matrix k l ℝ →L[ℝ] Matrix m n ℝ :=
    (Frobenius.rightMulCLM Vhᵀ).comp (Frobenius.leftMulCLM Uh) with hφ
  have h : HasFDerivAt (fun X => ℒ (φ X)) ((innerSL ℝ (g (φ Sb))).comp φ) Sb :=
    (hℒ (φ Sb)).comp Sb φ.hasFDerivAt
  refine h.congr_fderiv ?_
  ext1 X
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hφ, Frobenius.rightMulCLM_apply,
    Frobenius.leftMulCLM_apply]
  rw [Frobenius.inner_mul_right, Frobenius.inner_mul_left, Matrix.transpose_transpose]
  simp [Matrix.mul_assoc]

end FactorFlow
/-! ### Theorem 4: the naive factor-wise momentum flow -/

section NaiveFlow

open scoped LeanDLRA.Frobenius
open LeanDLRA LeanDLRA.GaugeODE

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- The operator `P̂(W, 𝒱)` of Eq. (5b) of arXiv 2506.17475. -/
def naiveProj (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (Uv : Matrix m r ℝ)
    (Sv : Matrix r r ℝ) (Vv : Matrix n r ℝ) (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  Z * V * Sᵀ * Sv * Vvᵀ + Uv * Uᵀ * Z * V * Vvᵀ + Uv * Sv * Sᵀ * Uᵀ * Z

/-- The conventional momentum flow on the factors, Eqs. (4a)-(4c) of arXiv 2506.17475,
on a set `I` of times: `U̇ = U_𝒱`, `U̇_𝒱 + γ U_𝒱 + ∇_U ℒ = 0` with `∇_U ℒ = G V Sᵀ`, and similarly
for `V` and `S`, where `G = g(U S Vᵀ)`.  The factors are free: this flow does not keep `U`, `V`
orthonormal. -/
structure IsNaiveFlow (g : Matrix m n ℝ → Matrix m n ℝ) (γ : ℝ) (U : ℝ → Matrix m r ℝ)
    (S : ℝ → Matrix r r ℝ) (V : ℝ → Matrix n r ℝ) (Uv : ℝ → Matrix m r ℝ)
    (Sv : ℝ → Matrix r r ℝ) (Vv : ℝ → Matrix n r ℝ) (I : Set ℝ) : Prop where
  dU : ∀ t ∈ I, HasDerivAt U (Uv t) t
  dS : ∀ t ∈ I, HasDerivAt S (Sv t) t
  dV : ∀ t ∈ I, HasDerivAt V (Vv t) t
  dUv : ∀ t ∈ I, HasDerivAt Uv (-(γ • Uv t) - g (U t * S t * (V t)ᵀ) * V t * (S t)ᵀ) t
  dSv : ∀ t ∈ I, HasDerivAt Sv (-(γ • Sv t) - (U t)ᵀ * g (U t * S t * (V t)ᵀ) * V t) t
  dVv : ∀ t ∈ I, HasDerivAt Vv (-(γ • Vv t) - (g (U t * S t * (V t)ᵀ))ᵀ * U t * S t) t

variable {g : Matrix m n ℝ → Matrix m n ℝ} {γ : ℝ} {U Uv : ℝ → Matrix m r ℝ}
  {S Sv : ℝ → Matrix r r ℝ} {V Vv : ℝ → Matrix n r ℝ} {I : Set ℝ}

/-- Eq. (5a) of arXiv 2506.17475: along the naive flow
`Ẇ = U_𝒱 S Vᵀ + U S_𝒱 Vᵀ + U S V_𝒱ᵀ`. -/
theorem IsNaiveFlow.hasDerivAt_weight
    (h : IsNaiveFlow g γ U S V Uv Sv Vv I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun t => U t * S t * (V t)ᵀ)
      (Uv t * S t * (V t)ᵀ + U t * Sv t * (V t)ᵀ + U t * S t * (Vv t)ᵀ) t :=
  hasDerivAt_factorProduct (h.dU t ht) (h.dS t ht) (h.dV t ht)

/-- Eq. (5b) of arXiv 2506.17475: along the naive flow, the momentum
`𝒱 = U_𝒱 S_𝒱 V_𝒱ᵀ` satisfies `𝒱̇ + 3 γ 𝒱 = -P̂(W, 𝒱) G`. -/
theorem IsNaiveFlow.hasDerivAt_momentum
    (h : IsNaiveFlow g γ U S V Uv Sv Vv I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun t => Uv t * Sv t * (Vv t)ᵀ)
      (-((3 * γ) • (Uv t * Sv t * (Vv t)ᵀ)) -
        naiveProj (U t) (S t) (V t) (Uv t) (Sv t) (Vv t) (g (U t * S t * (V t)ᵀ))) t := by
  refine (hasDerivAt_factorProduct (h.dUv t ht) (h.dSv t ht) (h.dVv t ht)).congr_deriv ?_
  simp only [naiveProj, Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    show (3 * γ) = γ + γ + γ by ring, add_smul]
  abel

/-- **The configuration of the proof of Theorem 4 of arXiv 2506.17475.**  For
`U_𝒱 = -U`, `S_𝒱 = 0`, `V_𝒱 = V` the right-hand side of `Ẇ` and the momentum `𝒱` vanish and
`P̂(W, 𝒱) Z = -U Uᵀ Z V Vᵀ`.  The paper's remark has `+U Uᵀ Z V Vᵀ`, a sign slip without
consequence. -/
theorem naive_configuration (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ)
    (Z : Matrix m n ℝ) :
    (-U) * S * Vᵀ + U * (0 : Matrix r r ℝ) * Vᵀ + U * S * Vᵀ = 0 ∧
      (-U) * (0 : Matrix r r ℝ) * Vᵀ = 0 ∧
      naiveProj U S V (-U) 0 V Z = -(U * Uᵀ * Z * V * Vᵀ) := by
  refine ⟨?_, by simp, ?_⟩
  · simp
  · simp [naiveProj, Matrix.mul_assoc]

/-- **The algebra of Theorem 4 of arXiv 2506.17475 (the paper's remark).**  If `Uᵀ Z = 0` for
`Z = ∇ℒ(W)`, `W = U S Vᵀ`, then at the configuration `U_𝒱 = -U`, `S_𝒱 = 0`, `V_𝒱 = V` we have
`P̂(W, 𝒱) Z = 0`, while `P(W) Z = Z V Vᵀ`, which does not vanish if `Z V ≠ 0`. -/
theorem naive_configuration_stall [DecidableEq r] {U₀ : Matrix m r ℝ} (S₀ : Matrix r r ℝ)
    {V₀ : Matrix n r ℝ} (hV : V₀ᵀ * V₀ = 1) {Z : Matrix m n ℝ} (hZ : U₀ᵀ * Z = 0) :
    naiveProj U₀ S₀ V₀ (-U₀) 0 V₀ Z = 0 ∧ tangentProj U₀ V₀ Z = Z * V₀ * V₀ᵀ ∧
      (Z * V₀ ≠ 0 → tangentProj U₀ V₀ Z ≠ 0) := by
  have h1 : U₀ * U₀ᵀ * Z = 0 := by rw [Matrix.mul_assoc, hZ, Matrix.mul_zero]
  have h2 : tangentProj U₀ V₀ Z = Z * V₀ * V₀ᵀ := by
    rw [tangentProj_apply, h1]
    simp
  refine ⟨?_, h2, fun hne h0 => hne ?_⟩
  · rw [(naive_configuration U₀ S₀ V₀ Z).2.2, h1]
    simp
  · have := congrArg (· * V₀) h0
    simpa [h2, Matrix.mul_assoc, hV] using this

/-- Algebra of `naiveFlow_not_stationary`: the mixed component of the second derivative of `W` at
the configuration of Theorem 4 of arXiv 2506.17475. -/
theorem naive_second_deriv [DecidableEq r] {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} (G : Matrix m n ℝ) (c : ℝ) (hU : U₀ᵀ * U₀ = 1) (hV : V₀ᵀ * V₀ = 1)
    (h0 : U₀ᵀ * G * V₀ = 0) :
    U₀ᵀ * (((-(c • (-U₀)) - G * V₀ * S₀ᵀ) * S₀ * V₀ᵀ + (-U₀) * (0 : Matrix r r ℝ) * V₀ᵀ
          + (-U₀) * S₀ * V₀ᵀ)
        + ((-U₀) * (0 : Matrix r r ℝ) * V₀ᵀ
          + U₀ * (-(c • (0 : Matrix r r ℝ)) - U₀ᵀ * G * V₀) * V₀ᵀ
          + U₀ * (0 : Matrix r r ℝ) * V₀ᵀ)
        + ((-U₀) * S₀ * V₀ᵀ + U₀ * (0 : Matrix r r ℝ) * V₀ᵀ
          + U₀ * S₀ * (-(c • V₀) - Gᵀ * U₀ * S₀)ᵀ)) * V₀
      = (-2 : ℝ) • S₀ := by
  have hU' : ∀ X : Matrix r r ℝ, U₀ᵀ * (U₀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have h0' : U₀ᵀ * (G * V₀) = 0 := by rw [← Matrix.mul_assoc, h0]
  have h0'' : ∀ X : Matrix r r ℝ, U₀ᵀ * (G * (V₀ * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, h0, Matrix.zero_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_sub,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    smul_zero, neg_zero, zero_sub, Matrix.mul_assoc, hV, hU', h0', h0'', Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul]
  module

/-- **The point of the proof of Theorem 4 of arXiv 2506.17475 is not stationary.**  The paper argues
that at `U_𝒱 = -U`, `S_𝒱 = 0`, `V_𝒱 = V`, with `P̂(W, 𝒱) ∇ℒ(W) = 0` (equivalently `Uᵀ ∇ℒ(W) V = 0`
for orthonormal `U`, `V`), the naive flow "identifies `(W, 𝒱)` as a stationary point".  This is
true at `t₀` for the right-hand sides of `Ẇ` and `𝒱̇`, but the naive flow is a system for the
factors: if `W` stays constant on `[t₀, t₀ + δ)`, then necessarily `S(t₀) = 0`.  So for `S ≠ 0`
the weight leaves the configuration immediately (in fact `Uᵀ Ẅ(t₀) V = -2 S`). -/
theorem naiveFlow_not_stationary [DecidableEq r] {t₀ δ : ℝ} (hδ : 0 < δ)
    (h : IsNaiveFlow g γ U S V Uv Sv Vv (Ico t₀ (t₀ + δ)))
    (hUv : Uv t₀ = -U t₀) (hSv : Sv t₀ = 0) (hVv : Vv t₀ = V t₀)
    (hU : (U t₀)ᵀ * U t₀ = 1) (hV : (V t₀)ᵀ * V t₀ = 1)
    (h0 : (U t₀)ᵀ * g (U t₀ * S t₀ * (V t₀)ᵀ) * V t₀ = 0)
    (hW : ∀ t ∈ Ico t₀ (t₀ + δ), U t * S t * (V t)ᵀ = U t₀ * S t₀ * (V t₀)ᵀ) :
    S t₀ = 0 := by
  have ht₀ : t₀ ∈ Ico t₀ (t₀ + δ) := ⟨le_rfl, by linarith⟩
  set D : ℝ → Matrix m n ℝ :=
    fun t => Uv t * S t * (V t)ᵀ + U t * Sv t * (V t)ᵀ + U t * S t * (Vv t)ᵀ with hDdef
  have hD0 : ∀ t ∈ Ico t₀ (t₀ + δ), D t = 0 := by
    intro t ht
    have h1 := (h.hasDerivAt_weight ht).hasDerivWithinAt (s := Ici t)
    have h2 : HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ) (0 : Matrix m n ℝ) (Ici t) t := by
      refine (hasDerivWithinAt_const t (Ici t) (U t₀ * S t₀ * (V t₀)ᵀ)).congr_of_eventuallyEq ?_
        (hW t ht)
      filter_upwards [Ico_mem_nhdsGE ht.2] with x hx using hW x ⟨ht.1.trans hx.1, hx.2⟩
    exact (uniqueDiffWithinAt_Ici t).eq_deriv _ h1 h2
  have d1 := hasDerivAt_factorProduct (h.dUv t₀ ht₀) (h.dS t₀ ht₀) (h.dV t₀ ht₀)
  have d2 := hasDerivAt_factorProduct (h.dU t₀ ht₀) (h.dSv t₀ ht₀) (h.dV t₀ ht₀)
  have d3 := hasDerivAt_factorProduct (h.dU t₀ ht₀) (h.dS t₀ ht₀) (h.dVv t₀ ht₀)
  have d := ((d1.add d2).add d3).hasDerivWithinAt (s := Ici t₀)
  have h3 : HasDerivWithinAt D (0 : Matrix m n ℝ) (Ici t₀) t₀ := by
    refine (hasDerivWithinAt_const t₀ (Ici t₀) (0 : Matrix m n ℝ)).congr_of_eventuallyEq ?_
      (hD0 t₀ ht₀)
    filter_upwards [Ico_mem_nhdsGE (show t₀ < t₀ + δ by linarith)] with x hx using hD0 x hx
  have hz := (uniqueDiffWithinAt_Ici t₀).eq_deriv _ d h3
  rw [hUv, hSv, hVv] at hz
  have key := naive_second_deriv (S₀ := S t₀) (g (U t₀ * S t₀ * (V t₀)ᵀ)) γ hU hV h0
  rw [hz] at key
  simp only [Matrix.mul_zero, Matrix.zero_mul] at key
  have := (smul_eq_zero.1 key.symm).resolve_left (by norm_num)
  exact this

/-- **Theorem 4 of arXiv 2506.17475 with singular `S`: an exact stalling solution from the paper's
configuration.**  Let `U₀ᵀ ∇ℒ(0) V₀ = 0`, `γ > 0`, `e(t) = (1 - e^{-γ t})/γ`.  Then
`U = (1 - e) U₀`, `S = 0`, `V = (1 + e) V₀`, `U_𝒱 = -e^{-γ t} U₀`, `S_𝒱 = 0`, `V_𝒱 = e^{-γ t} V₀` is
a solution of the naive flow which at `t = 0` is the configuration `U_𝒱 = -U`, `S_𝒱 = 0`,
`V_𝒱 = V` of the paper, and along which `W ≡ 0` and `𝒱 ≡ 0`.  If moreover `U₀ᵀ ∇ℒ(0) = 0` and
`∇ℒ(0) V₀ ≠ 0`, then `P ∇ℒ(0) ≠ 0` for `P = tangentProj U₀ V₀`, by `naive_configuration_stall`.
So the weight stalls at a point which is not stationary.  **Difference from the paper:** `S = 0`
is forced by `naiveFlow_not_stationary`, and the factors do not stay orthonormal. -/
theorem naiveFlow_stall_of_singular {γ : ℝ} (hγ : 0 < γ) {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ}
    (h0 : U₀ᵀ * g 0 * V₀ = 0) :
    IsNaiveFlow g γ (fun t => (1 - (1 - Real.exp (-γ * t)) / γ) • U₀) (fun _ => 0)
      (fun t => (1 + (1 - Real.exp (-γ * t)) / γ) • V₀) (fun t => (-Real.exp (-γ * t)) • U₀)
      (fun _ => 0) (fun t => Real.exp (-γ * t) • V₀) univ := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-γ * t)) (-γ * Real.exp (-γ * t)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-γ)).exp
    simpa [mul_comm] using this
  have he : ∀ t : ℝ, HasDerivAt (fun t => (1 - Real.exp (-γ * t)) / γ) (Real.exp (-γ * t)) t := by
    intro t
    have := ((hexp t).const_sub 1).div_const γ
    refine this.congr_deriv ?_
    field_simp
  refine ⟨fun t _ => ?_, fun t _ => hasDerivAt_const _ _, fun t _ => ?_, fun t _ => ?_,
    fun t _ => ?_, fun t _ => ?_⟩
  · have := ((he t).const_sub 1).smul_const U₀
    simpa using this
  · have := ((he t).const_add 1).smul_const V₀
    simpa using this
  · have := ((hexp t).neg).smul_const U₀
    refine this.congr_deriv ?_
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_zero, sub_zero, smul_smul]
    rw [← neg_smul]
    congr 1
    ring
  · have e : ((1 - (1 - Real.exp (-γ * t)) / γ) • U₀)ᵀ * g ((1 - (1 - Real.exp (-γ * t)) / γ) • U₀
        * (0 : Matrix r r ℝ) * ((1 + (1 - Real.exp (-γ * t)) / γ) • V₀)ᵀ)
        * ((1 + (1 - Real.exp (-γ * t)) / γ) • V₀) = 0 := by
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.transpose_smul, Matrix.smul_mul,
        Matrix.mul_smul, h0, smul_zero]
    rw [e]
    simpa using hasDerivAt_const t (0 : Matrix r r ℝ)
  · have := (hexp t).smul_const V₀
    refine this.congr_deriv ?_
    simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero, smul_smul]
    rw [← neg_smul]
    congr 1
    ring

end NaiveFlow
/-! ### Theorem 4: a nondegenerate failing trajectory -/

section NaiveExample

open scoped LeanDLRA.Frobenius
open LeanDLRA LeanDLRA.GaugeODE

/-- `y ↦ max(y, 0)² / 2`. -/
noncomputable def posSq (y : ℝ) : ℝ := (max y 0) ^ 2 / 2

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `posSq` is differentiable with derivative `max(y,
0)`. -/
theorem hasDerivAt_posSq (y : ℝ) : HasDerivAt posSq (max y 0) y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · have e : posSq =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp [posSq, max_eq_right (mem_Iio.1 hx).le]
    rw [max_eq_right h.le]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq e
  · rw [max_self, hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hc] with x hx
    have hx' : |x| < c := by simpa using hx
    have h1 : (max x 0) ^ 2 ≤ x ^ 2 := by
      rcases le_total x 0 with h | h
      · simpa [max_eq_right h] using sq_nonneg x
      · rw [max_eq_left h]
    have h2 : 0 ≤ (max x 0) ^ 2 := by positivity
    have h3 : x ^ 2 = |x| * |x| := by rw [← sq_abs, sq]
    have h4 := abs_nonneg x
    simp only [posSq, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, smul_zero, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · have e : posSq =ᶠ[𝓝 y] fun x => x ^ 2 / 2 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp [posSq, max_eq_left (mem_Ioi.1 hx).le]
    rw [max_eq_left h.le]
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) y y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    exact h2.congr_of_eventuallyEq e

/-- A `C^{1,1}` function, decreasing with slope `-c` on `(-∞, 1]`, constant on `[1 + c, ∞)`. -/
noncomputable def huber (c y : ℝ) : ℝ := -c * y + posSq (y - 1) - posSq (y - (1 + c))

/-- The derivative of `huber`. -/
noncomputable def dhuber (c y : ℝ) : ℝ := -c + max (y - 1) 0 - max (y - (1 + c)) 0

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the derivative of `huber`. -/
theorem hasDerivAt_huber (c y : ℝ) : HasDerivAt (huber c) (dhuber c y) y := by
  have h1 : HasDerivAt (fun y => -c * y) (-c) y := by
    simpa using (hasDerivAt_id y).const_mul (-c)
  have h2 := (hasDerivAt_posSq (y - 1)).comp_sub_const y 1
  have h3 := (hasDerivAt_posSq (y - (1 + c))).comp_sub_const y (1 + c)
  exact (h1.add h2).sub h3

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `huber` is bounded below. -/
theorem huber_ge {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : -c - c ^ 2 / 2 ≤ huber c y := by
  unfold huber posSq
  rcases le_total (y - 1) 0 with a | a <;> rcases le_total (y - (1 + c)) 0 with b | b <;>
    simp only [max_eq_left, max_eq_right, a, b] <;> nlinarith [sq_nonneg (y - 1 - c)]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `huber` has slope `-c` on `(-∞, 1]`. -/
theorem dhuber_of_le {c y : ℝ} (hc : 0 ≤ c) (hy : y ≤ 1) : dhuber c y = -c := by
  unfold dhuber
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `dhuber` is `1`-Lipschitz. -/
theorem abs_dhuber_sub_le {c : ℝ} (hc : 0 ≤ c) (y y' : ℝ) :
    |dhuber c y - dhuber c y'| ≤ |y - y'| := by
  unfold dhuber
  have h1 := le_abs_self (y - y')
  have h2 := neg_abs_le (y - y')
  rw [abs_le]
  rcases le_total (y - 1) 0 with a | a <;> rcases le_total (y - (1 + c)) 0 with b | b <;>
    rcases le_total (y' - 1) 0 with a' | a' <;> rcases le_total (y' - (1 + c)) 0 with b' | b' <;>
    simp only [max_eq_left, max_eq_right, a, b, a', b'] <;> constructor <;> linarith

/-- Matrix units of `ℝ^{2×2}`. -/
noncomputable def E₂ (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single i j 1

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the inner product with a matrix unit is an entry.
-/
theorem inner_E₂ (i j : Fin 2) (X : Matrix (Fin 2) (Fin 2) ℝ) : ⟪E₂ i j, X⟫ = X i j := by
  rw [Frobenius.inner_def]
  fin_cases i <;> fin_cases j <;> simp [E₂, Matrix.single_apply, Fin.sum_univ_two]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: an entry of a matrix has gradient the matrix unit.
-/
theorem hasFDerivAt_entry (i j : Fin 2) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt (fun X : Matrix (Fin 2) (Fin 2) ℝ => X i j) (innerSL ℝ (E₂ i j)) W := by
  refine ((innerSL ℝ (E₂ i j)).hasFDerivAt (x := W)).congr_of_eventuallyEq
    (Eventually.of_forall fun X => ?_)
  simp [innerSL_apply_apply, inner_E₂]

/-- The loss of `naiveFlow_failure`: `ℒ(W) = c W₀₀² / 2 + h(W₀₁) + h(W₁₀)` with `h = huber c`. -/
noncomputable def naiveLoss (c : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  c / 2 * (W 0 0) ^ 2 + huber c (W 0 1) + huber c (W 1 0)

/-- The gradient of `naiveLoss`. -/
noncomputable def naiveGrad (c : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (c * W 0 0) • E₂ 0 0 + dhuber c (W 0 1) • E₂ 0 1 + dhuber c (W 1 0) • E₂ 1 0

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `naiveGrad` is the gradient of `naiveLoss`. -/
theorem hasFDerivAt_naiveLoss (c : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt (naiveLoss c) (innerSL ℝ (naiveGrad c W)) W := by
  have h1 : HasDerivAt (fun y : ℝ => c / 2 * y ^ 2) (c * W 0 0) (W 0 0) := by
    have := (hasDerivAt_pow 2 (W 0 0)).const_mul (c / 2)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h := ((h1.comp_hasFDerivAt W (hasFDerivAt_entry 0 0 W)).add
    ((hasDerivAt_huber c (W 0 1)).comp_hasFDerivAt W (hasFDerivAt_entry 0 1 W))).add
    ((hasDerivAt_huber c (W 1 0)).comp_hasFDerivAt W (hasFDerivAt_entry 1 0 W))
  refine h.congr_fderiv ?_
  ext1 X
  simp [naiveGrad, innerSL_apply_apply, inner_E₂]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `naiveLoss` is bounded below. -/
theorem naiveLoss_ge {c : ℝ} (hc : 0 ≤ c) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    2 * (-c - c ^ 2 / 2) ≤ naiveLoss c W := by
  have h1 := huber_ge hc (W 0 1)
  have h2 := huber_ge hc (W 1 0)
  have h3 : 0 ≤ c / 2 * (W 0 0) ^ 2 := by positivity
  unfold naiveLoss
  linarith

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the entries of `naiveGrad`. -/
theorem naiveGrad_apply (c : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    naiveGrad c W = !![c * W 0 0, dhuber c (W 0 1); dhuber c (W 1 0), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [naiveGrad, E₂]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `naiveGrad` is Lipschitz. -/
theorem naiveGrad_lipschitz {c : ℝ} (hc : 0 ≤ c) (W W' : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖naiveGrad c W - naiveGrad c W'‖ ≤ (c + 1) * ‖W - W'‖ := by
  have h1 := sq_le_sq.2 (abs_dhuber_sub_le hc (W 0 1) (W' 0 1))
  have h2 := sq_le_sq.2 (abs_dhuber_sub_le hc (W 1 0) (W' 1 0))
  have e1 : ‖naiveGrad c W - naiveGrad c W'‖ ^ 2 = (c * W 0 0 - c * W' 0 0) ^ 2
      + (dhuber c (W 0 1) - dhuber c (W' 0 1)) ^ 2
      + (dhuber c (W 1 0) - dhuber c (W' 1 0)) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [naiveGrad_apply, Fin.sum_univ_two]
  have e2 : ‖W - W'‖ ^ 2 = (W 0 0 - W' 0 0) ^ 2 + (W 0 1 - W' 0 1) ^ 2 + (W 1 0 - W' 1 0) ^ 2
      + (W 1 1 - W' 1 1) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  have hc1 : 1 ≤ (c + 1) ^ 2 := by nlinarith
  have hc2 : c ^ 2 ≤ (c + 1) ^ 2 := by nlinarith
  have key : ‖naiveGrad c W - naiveGrad c W'‖ ^ 2 ≤ ((c + 1) * ‖W - W'‖) ^ 2 := by
    rw [mul_pow, e1, e2]
    have k0 : (c * W 0 0 - c * W' 0 0) ^ 2 ≤ (c + 1) ^ 2 * (W 0 0 - W' 0 0) ^ 2 := by
      have : (c * W 0 0 - c * W' 0 0) ^ 2 = c ^ 2 * (W 0 0 - W' 0 0) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
    have k1 : (W 0 1 - W' 0 1) ^ 2 ≤ (c + 1) ^ 2 * (W 0 1 - W' 0 1) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hc1
    have k2 : (W 1 0 - W' 1 0) ^ 2 ≤ (c + 1) ^ 2 * (W 1 0 - W' 1 0) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hc1
    have k3 : 0 ≤ (c + 1) ^ 2 * (W 1 1 - W' 1 1) ^ 2 := by positivity
    nlinarith
  exact (abs_le_of_sq_le_sq' key (by positivity)).2

/-- The first unit vector of `ℝ²`, as a `2 × 1` matrix. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The second unit vector of `ℝ²`, as a `2 × 1` matrix. -/
def e₂ : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The vector `(1, x)ᵀ`. -/
noncomputable def uvec (x : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := e₁ + x • e₂

/-- The weight `x (1, x)ᵀ (1, x)` of the failing trajectory. -/
noncomputable def wmat (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  uvec x * (x • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (uvec x)ᵀ

/-- The gradient along the failing trajectory. -/
def gmat (c x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c * x, -c; -c, 0]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the entries of `wmat`. -/
theorem wmat_apply (x : ℝ) : wmat x = !![x, x ^ 2; x ^ 2, x ^ 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wmat, uvec, e₁, e₂, Matrix.mul_apply] <;> ring

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the gradient along the failing trajectory, where
`x² ≤ 1`. -/
theorem naiveGrad_wmat {c x : ℝ} (hc : 0 ≤ c) (hx : x ^ 2 ≤ 1) :
    naiveGrad c (wmat x) = gmat c x := by
  rw [naiveGrad_apply, wmat_apply]
  simp [gmat, dhuber_of_le hc hx]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `G u = -c e₂`. -/
theorem gmat_mul_uvec (c x : ℝ) : gmat c x * uvec x = (-c) • e₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gmat, uvec, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `gmat` is symmetric. -/
theorem gmat_transpose (c x : ℝ) : (gmat c x)ᵀ = gmat c x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmat]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `uᵀ e₂ = x`. -/
theorem uvec_transpose_mul_e₂ (x : ℝ) :
    (uvec x)ᵀ * e₂ = x • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [uvec, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `uᵀ u = 1 + x²`. -/
theorem uvec_transpose_mul_self (x : ℝ) :
    (uvec x)ᵀ * uvec x = (1 + x ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [uvec, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The normalised vector `(1, x)ᵀ / √(1 + x²)`. -/
noncomputable def uhat (x : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := (√(1 + x ^ 2))⁻¹ • uvec x

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `uhat` has norm one. -/
theorem uhat_orthonormal (x : ℝ) : (uhat x)ᵀ * uhat x = 1 := by
  have h : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hs : (√(1 + x ^ 2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt h.le
  have hs0 : √(1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  rw [uhat, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, uvec_transpose_mul_self,
    smul_smul, smul_smul]
  have : (√(1 + x ^ 2))⁻¹ * (√(1 + x ^ 2))⁻¹ * (1 + x ^ 2) = 1 := by
    generalize √(1 + x ^ 2) = r at hs hs0
    rw [← hs]
    field_simp
  rw [this, one_smul]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `wmat x` in the orthonormal factor `uhat x`. -/
theorem wmat_eq_uhat (x : ℝ) :
    wmat x = uhat x * ((x * (1 + x ^ 2)) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (uhat x)ᵀ := by
  have h : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hs : (√(1 + x ^ 2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt h.le
  have hs0 : √(1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  rw [wmat, uhat, Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  congr 1
  generalize √(1 + x ^ 2) = r at hs hs0
  rw [← hs]
  field_simp

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `‖e₂‖ = 1`. -/
theorem norm_e₂ : ‖e₂‖ = 1 := by
  have h : ‖e₂‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [e₂, Fin.sum_univ_two]
  nlinarith [norm_nonneg e₂, sq_nonneg (‖e₂‖ - 1), sq_nonneg (‖e₂‖ + 1)]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `‖e₁‖ = 1`. -/
theorem norm_e₁ : ‖e₁‖ = 1 := by
  have h : ‖e₁‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [e₁, Fin.sum_univ_two]
  nlinarith [norm_nonneg e₁, sq_nonneg (‖e₁‖ - 1), sq_nonneg (‖e₁‖ + 1)]

/-- Lower bound of the Riemannian gradient along the failing trajectory: the tangent projector
keeps `G û`, and `G û = -c e₂ / √(1 + x²)`. -/
theorem le_norm_tangentProj_gmat {c x : ℝ} (hc : 0 ≤ c) (hx : x ^ 2 ≤ 1) :
    c / 2 ≤ ‖tangentProj (uhat x) (uhat x) (gmat c x)‖ := by
  have hV := uhat_orthonormal x
  have h1 : tangentProj (uhat x) (uhat x) (gmat c x) * uhat x = gmat c x * uhat x := by
    rw [tangentProj_apply]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
    abel
  have h2 : ‖gmat c x * uhat x‖ ≤ ‖tangentProj (uhat x) (uhat x) (gmat c x)‖ := by
    rw [← h1]
    exact norm_mul_le_of_orthonormal hV _
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hs0 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hs2 : √(1 + x ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have h3 : gmat c x * uhat x = ((√(1 + x ^ 2))⁻¹ * (-c)) • e₂ := by
    rw [uhat, Matrix.mul_smul, gmat_mul_uvec, smul_smul]
  have h4 : ‖gmat c x * uhat x‖ = (√(1 + x ^ 2))⁻¹ * c := by
    rw [h3, norm_smul, norm_e₂, mul_one, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg hc, abs_of_pos (inv_pos.2 hs0)]
  have h5 : c / 2 ≤ (√(1 + x ^ 2))⁻¹ * c := by
    have h6 : (1 / 2 : ℝ) ≤ (√(1 + x ^ 2))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hs0 hs2
    have := mul_le_mul_of_nonneg_right h6 hc
    linarith
  linarith

/-- The exponential `ξ(t) = e^{-c t}` that drives the failing trajectory. -/
noncomputable def xi (c t : ℝ) : ℝ := Real.exp (-c * t)

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: the derivative of `xi`. -/
theorem hasDerivAt_xi (c t : ℝ) : HasDerivAt (xi c) (-c * xi c t) t := by
  have h : HasDerivAt (fun t => Real.exp (-c * t)) (Real.exp (-c * t) * (-c * 1)) t :=
    ((hasDerivAt_id t).const_mul (-c)).exp
  exact h.congr_deriv (by simp only [xi]; ring)

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `xi` is positive. -/
theorem xi_pos (c t : ℝ) : 0 < xi c t := Real.exp_pos _

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `xi² ≤ 1` for `t ≥ 0`. -/
theorem xi_sq_le_one {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) : (xi c t) ^ 2 ≤ 1 := by
  have h : xi c t ≤ 1 := by
    rw [xi, Real.exp_le_one_iff]
    nlinarith
  nlinarith [xi_pos c t]

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `naiveGrad_wmat` with `wmat` unfolded. -/
theorem naiveGrad_factor {c x : ℝ} (hc : 0 ≤ c) (hx : x ^ 2 ≤ 1) :
    naiveGrad c (uvec x * (x • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (uvec x)ᵀ) = gmat c x :=
  naiveGrad_wmat hc hx

/-- The explicit solution of the naive flow behind `naiveFlow_failure`. -/
theorem isNaiveFlow_example {γ : ℝ} (hγ : 0 ≤ γ) :
    IsNaiveFlow (naiveGrad (γ + 1)) γ (fun t => uvec (xi (γ + 1) t))
      (fun t => xi (γ + 1) t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun t => uvec (xi (γ + 1) t))
      (fun t => (-(γ + 1) * xi (γ + 1) t) • e₂)
      (fun t => (-(γ + 1) * xi (γ + 1) t) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (fun t => (-(γ + 1) * xi (γ + 1) t) • e₂) (Ici 0) := by
  have hc : (0 : ℝ) ≤ γ + 1 := by linarith
  have hx := hasDerivAt_xi (γ + 1)
  have hU : ∀ t, HasDerivAt (fun t => uvec (xi (γ + 1) t))
      ((-(γ + 1) * xi (γ + 1) t) • e₂) t := fun t => ((hx t).smul_const e₂).const_add e₁
  have hd : ∀ t, HasDerivAt (fun t => -(γ + 1) * xi (γ + 1) t)
      ((γ + 1) ^ 2 * xi (γ + 1) t) t := fun t => by
    refine ((hx t).const_mul (-(γ + 1))).congr_deriv ?_
    ring
  refine ⟨fun t _ => hU t, fun t _ => (hx t).smul_const _, fun t _ => hU t, fun t ht => ?_,
    fun t ht => ?_, fun t ht => ?_⟩
  · have hg := naiveGrad_factor hc (xi_sq_le_one hc ht)
    refine ((hd t).smul_const e₂).congr_deriv ?_
    rw [hg, gmat_mul_uvec, Matrix.transpose_smul, Matrix.transpose_one]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    module
  · have hg := naiveGrad_factor hc (xi_sq_le_one hc ht)
    refine ((hd t).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)).congr_deriv ?_
    rw [hg, Matrix.mul_assoc, gmat_mul_uvec, Matrix.mul_smul, uvec_transpose_mul_e₂]
    module
  · have hg := naiveGrad_factor hc (xi_sq_le_one hc ht)
    refine ((hd t).smul_const e₂).congr_deriv ?_
    rw [hg, gmat_transpose, gmat_mul_uvec]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    module

/-- Auxiliary for Theorem 4 of arXiv 2506.17475: `‖wmat x‖ ≤ 2 |x|` for `x² ≤ 1`. -/
theorem norm_wmat_le {x : ℝ} (hx : x ^ 2 ≤ 1) : ‖wmat x‖ ≤ 2 * |x| := by
  have h : ‖wmat x‖ ^ 2 ≤ (2 * |x|) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, mul_pow, sq_abs]
    simp only [wmat_apply, Fin.sum_univ_two]
    simp
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx),
      mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg x)) (sub_nonneg.2 hx)]
  exact (abs_le_of_sq_le_sq' h (by positivity)).2

/-- **Theorem 4 of arXiv 2506.17475 (failure of the conventional momentum flow), proved with a
genuine trajectory.**  For every `γ ≥ 0` there are a loss `ℒ` on `ℝ^{2×2}`, bounded below with a
Lipschitz gradient `g`, and an exact solution `(U, S, V, U_𝒱, S_𝒱, V_𝒱)` of the flow
Eqs. (4a)-(4c) on `[0, ∞)`, rank `r = 1`, such that `S(t)` is invertible for all `t` and
`W(t) = U S Vᵀ = Û σ Ûᵀ` has rank one, `Û` orthonormal, `σ > 0`; moreover `W(t) → W⋆ = 0`, where
`∇ℒ(W⋆) ≠ 0`, and the Riemannian gradient stays away from zero:
`δ ≤ ‖P(W(t)) ∇ℒ(W(t))‖` for all `t`, `δ > 0`.  So the flow converges to a point that is not
stationary for `ℒ` on `{rank ≤ 1}`.

**Difference from the paper.**  The paper's argument (the configuration `U_𝒱 = -U`, `S_𝒱 = 0`,
`V_𝒱 = V`) is not a proof of this; see `naiveFlow_not_stationary`.  The limit `W⋆` is of lower
rank, as it must be: at an equilibrium with invertible `S` one has `P(W) ∇ℒ(W) = 0`
(`LeanDLRA.FactorizedDynamics.loraPrecond_eq_zero_iff`).  The factors are not orthonormal, which
the flow does not preserve anyway.  The trajectory lies on a stable manifold of a saddle, so the
failure is not generic: the initial data are tuned. -/
theorem naiveFlow_failure {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ (ℒ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
      (Linf K δ : ℝ) (U V Uv Vv Uh : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
      (S Sv : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (σ : ℝ → ℝ),
      (∀ W, HasFDerivAt ℒ (innerSL ℝ (g W)) W) ∧ (∀ W, Linf ≤ ℒ W) ∧
      (∀ W W', ‖g W - g W'‖ ≤ K * ‖W - W'‖) ∧
      IsNaiveFlow g γ U S V Uv Sv Vv (Ici 0) ∧ (∀ t ≥ 0, IsUnit (S t).det) ∧
      (∀ t ≥ 0, (Uh t)ᵀ * Uh t = 1 ∧ 0 < σ t ∧
        U t * S t * (V t)ᵀ = Uh t * (σ t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (Uh t)ᵀ) ∧
      Tendsto (fun t => U t * S t * (V t)ᵀ) atTop (𝓝 0) ∧ g 0 ≠ 0 ∧ 0 < δ ∧
      ∀ t ≥ 0, δ ≤ ‖tangentProj (Uh t) (Uh t) (g (U t * S t * (V t)ᵀ))‖ := by
  have hc : (0 : ℝ) ≤ γ + 1 := by linarith
  have hc' : (0 : ℝ) < γ + 1 := by linarith
  refine ⟨naiveLoss (γ + 1), naiveGrad (γ + 1), 2 * (-(γ + 1) - (γ + 1) ^ 2 / 2), γ + 2,
    (γ + 1) / 2, fun t => uvec (xi (γ + 1) t), fun t => uvec (xi (γ + 1) t),
    fun t => (-(γ + 1) * xi (γ + 1) t) • e₂, fun t => (-(γ + 1) * xi (γ + 1) t) • e₂,
    fun t => uhat (xi (γ + 1) t), fun t => xi (γ + 1) t • 1,
    fun t => (-(γ + 1) * xi (γ + 1) t) • 1, fun t => xi (γ + 1) t * (1 + (xi (γ + 1) t) ^ 2),
    hasFDerivAt_naiveLoss _, naiveLoss_ge hc, fun W W' => ?_, isNaiveFlow_example hγ,
    fun t _ => ?_, fun t _ => ⟨uhat_orthonormal _, ?_, wmat_eq_uhat _⟩, ?_, ?_, by positivity,
    fun t ht => ?_⟩
  · have := naiveGrad_lipschitz hc W W'
    rwa [show γ + 1 + 1 = γ + 2 by ring] at this
  · simp [(xi_pos (γ + 1) t).ne']
  · have := xi_pos (γ + 1) t
    positivity
  · have ht : Tendsto (fun t : ℝ => 2 * |xi (γ + 1) t|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => -(γ + 1) * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      have h2 : Tendsto (xi (γ + 1)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h1
      have h3 := (h2.abs).const_mul (2 : ℝ)
      simpa using h3
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_ge_atTop 0] with t h0
    exact norm_wmat_le (xi_sq_le_one hc h0)
  · intro h
    have h1 := congrFun (congrFun h 0) 1
    have h2 : dhuber (γ + 1) 0 = -(γ + 1) := dhuber_of_le hc zero_le_one
    simp only [naiveGrad_apply] at h1
    simp [h2] at h1
    linarith
  · change (γ + 1) / 2 ≤ ‖tangentProj (uhat (xi (γ + 1) t)) (uhat (xi (γ + 1) t))
      (naiveGrad (γ + 1) (wmat (xi (γ + 1) t)))‖
    rw [naiveGrad_wmat hc (xi_sq_le_one hc ht)]
    exact le_norm_tangentProj_gmat hc (xi_sq_le_one hc ht)

/-- The stalling solution `naiveFlow_stall_of_singular` is not vacuous: for the loss of
`naiveFlow_failure` and `U₀ = V₀ = e₁`, its hypothesis holds and `P ∇ℒ(0) ≠ 0`. -/
theorem naiveFlow_stall_example {c : ℝ} (hc : 0 < c) :
    e₁ᵀ * naiveGrad c 0 * e₁ = 0 ∧ tangentProj e₁ e₁ (naiveGrad c 0) ≠ 0 := by
  have h0 : naiveGrad c 0 = gmat c 0 := by
    have h1 : wmat 0 = 0 := by simp [wmat]
    rw [← h1]
    exact naiveGrad_wmat hc.le (by norm_num)
  have ho : e₁ᵀ * e₁ = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]
  have hu : uvec 0 = e₁ := by simp [uvec]
  have h2 : gmat c 0 * e₁ = (-c) • e₂ := by
    rw [← gmat_mul_uvec, hu]
  rw [h0]
  constructor
  · rw [Matrix.mul_assoc, h2, Matrix.mul_smul]
    have : e₁ᵀ * e₂ = 0 := by
      ext i j
      fin_cases i; fin_cases j
      simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, smul_zero]
  · intro h
    have h3 : tangentProj e₁ e₁ (gmat c 0) * e₁ = gmat c 0 * e₁ := by
      rw [tangentProj_apply]
      simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, ho, Matrix.mul_one]
      abel
    rw [h, Matrix.zero_mul, h2] at h3
    have h4 := congrArg norm h3
    rw [norm_zero, norm_smul, norm_e₂, mul_one, norm_neg, Real.norm_of_nonneg hc.le] at h4
    linarith

end NaiveExample
/-! ### Theorem 1: the projected heavy-ball flow -/

section HeavyBallFlow

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ℒ : E → ℝ} {g : E → E}
  {P : ℝ → E →L[ℝ] E} {γ : ℝ} {W M : ℝ → E}

/-- **Theorem 1 of arXiv 2506.17475, energy identity.**  Along `Ẇ = P 𝒱`, `𝒱̇ = -γ 𝒱 - P ∇ℒ(W)`
with a symmetric `P = P(t)`, e.g. `P(W(t))`, the energy `E = ℒ(W) + ‖𝒱‖²/2` satisfies
`Ė = -γ ‖𝒱‖²`.  (The library has the resulting inequality as `LeanDLRA.heavyBall_energy_le`.) -/
theorem hasDerivWithinAt_heavyBall_energy (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {s : Set ℝ} {t : ℝ} (hP : ∀ u v, ⟪P t u, v⟫ = ⟪u, P t v⟫)
    (hW : HasDerivWithinAt W (P t (M t)) s t)
    (hM : HasDerivWithinAt M (-(γ • M t) - P t (g (W t))) s t) :
    HasDerivWithinAt (fun r => ℒ (W r) + ‖M r‖ ^ 2 / 2) (-(γ * ‖M t‖ ^ 2)) s t := by
  have h1 := hasDerivWithinAt_energy_comp hℒ hW
  have h2 := (hM.norm_sq).div_const 2
  refine (h1.add h2).congr_deriv ?_
  rw [inner_sub_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, ← hP,
    real_inner_comm (M t) (P t (g (W t)))]
  ring

/-- For `ℒ ≥ ℒ_inf` with `β`-Lipschitz gradient, `‖∇ℒ(x)‖² ≤ 2 β (ℒ(x) - ℒ_inf)`. -/
theorem norm_sq_grad_le {β Linf : ℝ} (hβ : 0 < β) (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hinf : ∀ x, Linf ≤ ℒ x) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * β * (ℒ x - Linf) := by
  have h := descent_lemma hℒ hg x (x - β⁻¹ • g x)
  have h2 := hinf (x - β⁻¹ • g x)
  have e : x - β⁻¹ • g x - x = -(β⁻¹ • g x) := by abel
  rw [e, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs] at h
  have e2 : β / 2 * ((β⁻¹) ^ 2 * ‖g x‖ ^ 2) = β⁻¹ * ‖g x‖ ^ 2 / 2 := by
    field_simp
  rw [e2] at h
  have e3 : ‖g x‖ ^ 2 = β * (β⁻¹ * ‖g x‖ ^ 2) := by
    field_simp
  rw [e3]
  have : β⁻¹ * ‖g x‖ ^ 2 ≤ 2 * (ℒ x - Linf) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hβ.le]

/-- Energy decay with a rate, the quantitative form of `hasDerivWithinAt_heavyBall_energy`. -/
theorem heavyBall_energy_decay {a s t d : ℝ} (hγ : 0 ≤ γ)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hPs : ∀ t ≥ a, ∀ u v, ⟪P t u, v⟫ = ⟪u, P t v⟫)
    (hWc : ContinuousOn W (Ici a)) (hMc : ContinuousOn M (Ici a))
    (hW : ∀ t ≥ a, HasDerivWithinAt W (P t (M t)) (Ici t) t)
    (hM : ∀ t ≥ a, HasDerivWithinAt M (-(γ • M t) - P t (g (W t))) (Ici t) t)
    (hs : a ≤ s) (hst : s ≤ t) (hd : ∀ r ∈ Ico s t, d ≤ ‖M r‖ ^ 2) :
    ℒ (W t) + ‖M t‖ ^ 2 / 2 ≤ ℒ (W s) + ‖M s‖ ^ 2 / 2 - γ * d * (t - s) := by
  have hsub : Icc s t ⊆ Ici a := fun r hr => hs.trans hr.1
  have hc : ContinuousOn (fun r => ℒ (W r) + ‖M r‖ ^ 2 / 2) (Icc s t) :=
    ((continuous_of_hasFDerivAt_innerSL hℒ).comp_continuousOn (hWc.mono hsub)).add
      (((hMc.mono hsub).norm.pow 2).div_const 2)
  have h := image_le_of_deriv_right_le_deriv_boundary hc
    (f' := fun r => -(γ * ‖M r‖ ^ 2))
    (fun r hr => hasDerivWithinAt_heavyBall_energy hℒ (hPs r (hs.trans hr.1))
      (hW r (hs.trans hr.1)) (hM r (hs.trans hr.1)))
    (B := fun r => ℒ (W s) + ‖M s‖ ^ 2 / 2 - γ * d * (r - s)) (B' := fun _ => -(γ * d))
    (by simp) (Continuous.continuousOn (by fun_prop))
    (fun r _ => by
      simpa using (((hasDerivWithinAt_id r (Ici r)).sub_const s).const_mul (γ * d)).const_sub
        (ℒ (W s) + ‖M s‖ ^ 2 / 2))
    (fun r hr => by
      have := mul_le_mul_of_nonneg_left (hd r hr) hγ
      linarith)
  exact h ⟨hst, le_rfl⟩

/-- A curve with `‖f'‖ ≤ C` is `C`-Lipschitz. -/
theorem norm_sub_le_of_deriv_le {f f' : ℝ → E} {a s t C : ℝ} (hc : ContinuousOn f (Ici a))
    (hd : ∀ t ≥ a, HasDerivWithinAt f (f' t) (Ici t) t) (hC : ∀ t ≥ a, ‖f' t‖ ≤ C)
    (hs : a ≤ s) (hst : s ≤ t) : ‖f t - f s‖ ≤ C * (t - s) :=
  norm_image_sub_le_of_norm_deriv_right_le_segment (hc.mono fun _ hr => hs.trans hr.1)
    (fun r hr => hd r (hs.trans hr.1)) (fun r hr => hC r (hs.trans hr.1)) t ⟨hst, le_rfl⟩

/-- `C * (x / (k * (C + 1))) ≤ x / k`. -/
theorem mul_div_mul_succ_le {C x k : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hk : 0 < k) :
    C * (x / (k * (C + 1))) ≤ x / k := by
  have h0 : 0 < C + 1 := by linarith
  have e : C * (x / (k * (C + 1))) = (C / (C + 1)) * (x / k) := by
    field_simp
  have h1 : C / (C + 1) ≤ 1 := by
    rw [div_le_one h0]
    linarith
  rw [e]
  have := mul_le_mul_of_nonneg_right h1 (div_nonneg hx hk.le)
  linarith

omit [InnerProductSpace ℝ E] in
/-- First half of Barbalat's argument for the heavy-ball flow: if an energy `En ≥ Linf` decays at
rate `c ‖M‖²` and `M` is Lipschitz, then `M → 0`.  (No integrals are needed.) -/
theorem tendsto_zero_of_energy_decay {En : ℝ → ℝ} {M : ℝ → E} {a Linf C₁ c : ℝ} (hc : 0 < c)
    (hC₁ : 0 ≤ C₁) (hinf : ∀ t ≥ a, Linf ≤ En t)
    (hdecay : ∀ {s t d : ℝ}, a ≤ s → s ≤ t → (∀ r ∈ Ico s t, d ≤ ‖M r‖ ^ 2) →
      En t ≤ En s - c * d * (t - s))
    (hMlip : ∀ {s t : ℝ}, a ≤ s → s ≤ t → ‖M t - M s‖ ≤ C₁ * (t - s)) :
    Tendsto M atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ, hfreq⟩ := hcon
  set τ : ℝ := δ / (2 * (C₁ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτC : C₁ * τ ≤ δ / 2 := mul_div_mul_succ_le hC₁ hδ.le (by norm_num)
  set η : ℝ := c * (δ ^ 2 / 4) * τ with hη
  have hη0 : 0 < η := by positivity
  have hbdd : BddBelow (En '' Ici a) := ⟨Linf, by
    rintro _ ⟨t, ht, rfl⟩
    exact hinf t ht⟩
  have hne : (En '' Ici a).Nonempty := ⟨En a, a, self_mem_Ici, rfl⟩
  obtain ⟨_, ⟨T₀, hT₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show sInf (En '' Ici a) < sInf (En '' Ici a) + η by linarith)
  obtain ⟨t, ht, hge⟩ := hfreq (max T₀ a)
  have htT : T₀ ≤ t := (le_max_left _ _).trans ht
  have hta : a ≤ t := (le_max_right _ _).trans ht
  rw [dist_zero_right] at hge
  have hbig : ∀ r ∈ Ico t (t + τ), δ ^ 2 / 4 ≤ ‖M r‖ ^ 2 := fun r hr => by
    have h1 := hMlip hta hr.1
    have h2 : ‖M t‖ ≤ ‖M r‖ + ‖M r - M t‖ := by
      have := norm_sub_norm_le (M t) (M r)
      rw [norm_sub_rev (M t)] at this
      linarith
    have h3 : C₁ * (r - t) ≤ C₁ * τ :=
      mul_le_mul_of_nonneg_left (by linarith [hr.2]) hC₁
    have h4 : δ / 2 ≤ ‖M r‖ := by linarith
    have h5 := pow_le_pow_left₀ (by positivity) h4 2
    calc δ ^ 2 / 4 = (δ / 2) ^ 2 := by ring
      _ ≤ ‖M r‖ ^ 2 := h5
  have h1 := hdecay hta (by linarith : t ≤ t + τ) hbig
  have h2 : En t ≤ En T₀ := by
    have := hdecay (s := T₀) (t := t) (d := 0) (mem_Ici.1 hT₀) htT fun r _ => by positivity
    simpa using this
  have h3 : sInf (En '' Ici a) ≤ En (t + τ) :=
    csInf_le hbdd ⟨t + τ, by simp only [Set.mem_Ici]; linarith, rfl⟩
  have h4 : c * (δ ^ 2 / 4) * (t + τ - t) = η := by
    rw [hη]
    ring_nf
  linarith

/-- Second half of Barbalat's argument: if `M → 0`, `Ṁ = -γ M - q` and `q` is Lipschitz, then
`q → 0`. -/
theorem tendsto_zero_of_deriv {M q : ℝ → E} {a γ L₂ : ℝ} (hγ : 0 ≤ γ) (hL₂ : 0 ≤ L₂)
    (hM0 : Tendsto M atTop (𝓝 0)) (hMc : ContinuousOn M (Ici a))
    (hM : ∀ t ≥ a, HasDerivWithinAt M (-(γ • M t) - q t) (Ici t) t)
    (hqlip : ∀ {s t : ℝ}, a ≤ s → s ≤ t → ‖q t - q s‖ ≤ L₂ * (t - s)) :
    Tendsto q atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ, hfreq⟩ := hcon
  set τ : ℝ := δ / (4 * (L₂ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτL : L₂ * τ ≤ δ / 4 := mul_div_mul_succ_le hL₂ hδ.le (by norm_num)
  set ι : ℝ := min (δ / (4 * (γ + 1))) (τ * δ / 8) with hι
  have hι0 : 0 < ι := lt_min (by positivity) (by positivity)
  have hι1 : γ * ι ≤ δ / 4 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hγ).trans
      (mul_div_mul_succ_le hγ hδ.le (by norm_num))
  have hι2 : ι ≤ τ * δ / 8 := min_le_right _ _
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hM0 ι hι0
  obtain ⟨t, ht, hge⟩ := hfreq (max T a)
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have hta : a ≤ t := (le_max_right _ _).trans ht
  rw [dist_zero_right] at hge
  set w : E := q t with hw
  have hw0 : 0 < ‖w‖ := hδ.trans_le hge
  have hMs : ∀ r ≥ t, ‖M r‖ ≤ ι := fun r hr => by
    have := hT r (htT.trans hr)
    rw [dist_zero_right] at this
    exact this.le
  have hin : ∀ r ≥ t, -(‖w‖ * ι) ≤ ⟪w, M r⟫ ∧ ⟪w, M r⟫ ≤ ‖w‖ * ι := fun r hr => by
    have h7 := abs_real_inner_le_norm w (M r)
    have h8 := mul_le_mul_of_nonneg_left (hMs r hr) (norm_nonneg w)
    have h9 := abs_le.1 (h7.trans h8)
    exact h9
  have hφ : ∀ r ≥ a, HasDerivWithinAt (fun r => ⟪w, M r⟫)
      (⟪w, -(γ • M r) - q r⟫) (Ici r) r := fun r hr =>
    ((innerSL ℝ w).hasFDerivAt).comp_hasDerivWithinAt r (hM r hr)
  have hφc : ContinuousOn (fun r => ⟪w, M r⟫) (Icc t (t + τ)) :=
    (continuous_const.inner continuous_id).comp_continuousOn
      (hMc.mono fun r hr => hta.trans hr.1)
  have hbound : ∀ r ∈ Ico t (t + τ), ⟪w, -(γ • M r) - q r⟫ ≤ -(‖w‖ * δ / 2) := fun r hr => by
    have h1 : ‖q r - w‖ ≤ δ / 4 := by
      have h2 := hqlip hta hr.1
      have h3 : L₂ * (r - t) ≤ L₂ * τ :=
        mul_le_mul_of_nonneg_left (by linarith [hr.2]) hL₂
      linarith
    have h4 : ⟪w, q r⟫ = ‖w‖ ^ 2 + ⟪w, q r - w⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    have h5 : -(‖w‖ * ‖q r - w‖) ≤ ⟪w, q r - w⟫ :=
      (abs_le.1 (abs_real_inner_le_norm w (q r - w))).1
    have h9 : ⟪w, -(γ • M r) - q r⟫ = -(γ * ⟪w, M r⟫) - ⟪w, q r⟫ := by
      rw [inner_sub_right, inner_neg_right, inner_smul_right]
    have h10 : ‖w‖ * ‖q r - w‖ ≤ ‖w‖ * (δ / 4) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
    have h11 := mul_le_mul_of_nonneg_left hι1 (norm_nonneg w)
    have h12 : ‖w‖ * δ ≤ ‖w‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hge (norm_nonneg w)
    have h13 := mul_le_mul_of_nonneg_left (hin r hr.1).1 hγ
    rw [h9, h4]
    linarith
  have hend := image_le_of_deriv_right_le_deriv_boundary hφc
    (fun r hr => hφ r (hta.trans hr.1))
    (B := fun r => ⟪w, M t⟫ - ‖w‖ * δ / 2 * (r - t)) (B' := fun _ => -(‖w‖ * δ / 2))
    (by simp) (Continuous.continuousOn (by fun_prop))
    (fun r _ => by
      simpa using (((hasDerivWithinAt_id r (Ici r)).sub_const t).const_mul
        (‖w‖ * δ / 2)).const_sub ⟪w, M t⟫)
    hbound (show t + τ ∈ Icc t (t + τ) from ⟨by linarith, le_rfl⟩)
  have h1 := (hin (t + τ) (by linarith)).1
  have h2 := (hin t le_rfl).2
  have h3 : ‖w‖ * δ / 2 * τ ≤ 2 * (‖w‖ * ι) := by
    have e : t + τ - t = τ := by ring
    simp only [e] at hend
    linarith
  have h4 := mul_le_mul_of_nonneg_left hι2 (norm_nonneg w)
  have h5 : 0 < ‖w‖ * δ * τ := by positivity
  linarith

/-- **Theorem 1 of arXiv 2506.17475, corrected: asymptotic stationarity.**  Let `ℒ ≥ ℒ_inf` have a
`β`-Lipschitz gradient, `γ > 0`, and let `(W, 𝒱)` solve `Ẇ = P 𝒱`, `𝒱̇ = -γ 𝒱 - P ∇ℒ(W)` on
`[a, ∞)` with orthogonal projectors `P(t)` satisfying `‖(P(s) - P(t)) x‖ ≤ K ‖W(s) - W(t)‖ ‖x‖`.
Then `𝒱(t) → 0` and `P(t) ∇ℒ(W(t)) → 0`.

**Differences from the paper.**  The paper claims that `W(t)` converges to a point `W⋆` with
`P(W⋆) ∇ℒ(W⋆) = 0`, assuming only that `ℒ` is bounded below.  That is false:
see `heavyBall_not_convergent`.  The proof in the paper infers `𝒱 → 0` from `∫ ‖𝒱‖² < ∞`, and the
convergence of `W` from nothing.  Here `∇ℒ` is Lipschitz, and `P` Lipschitz along the
trajectory; the latter is what a lower bound on the singular values gives, see
`heavyBall_tendsto_tangentProj`.  Boundedness of `𝒱` and of `∇ℒ(W(t))` is derived, not assumed.
The stationarity of limit points is `heavyBall_limit_stationary`. -/
theorem heavyBall_tendsto {β Linf K a : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hinf : ∀ x, Linf ≤ ℒ x) (hPo : ∀ t ≥ a, IsOrthProj (P t))
    (hPL : ∀ s ≥ a, ∀ t ≥ a, ∀ x, ‖P s x - P t x‖ ≤ K * ‖W s - W t‖ * ‖x‖)
    (hWc : ContinuousOn W (Ici a)) (hMc : ContinuousOn M (Ici a))
    (hW : ∀ t ≥ a, HasDerivWithinAt W (P t (M t)) (Ici t) t)
    (hM : ∀ t ≥ a, HasDerivWithinAt M (-(γ • M t) - P t (g (W t))) (Ici t) t) :
    Tendsto M atTop (𝓝 0) ∧ Tendsto (fun t => P t (g (W t))) atTop (𝓝 0) := by
  have hPs : ∀ t ≥ a, ∀ u v, ⟪P t u, v⟫ = ⟪u, P t v⟫ := fun t ht => (hPo t ht).symm
  set En : ℝ → ℝ := fun t => ℒ (W t) + ‖M t‖ ^ 2 / 2 with hEn
  have hdecay : ∀ {s t d : ℝ}, a ≤ s → s ≤ t → (∀ r ∈ Ico s t, d ≤ ‖M r‖ ^ 2) →
      En t ≤ En s - γ * d * (t - s) := fun hs hst hd =>
    heavyBall_energy_decay hγ.le hℒ hPs hWc hMc hW hM hs hst hd
  have hanti : ∀ t ≥ a, En t ≤ En a := fun t ht => by
    have := hdecay (s := a) (t := t) (d := 0) le_rfl ht fun r _ => by positivity
    simpa using this
  have hEnf : ∀ t ≥ a, Linf ≤ En t := fun t _ => by
    have := hinf (W t)
    have h2 : 0 ≤ ‖M t‖ ^ 2 / 2 := by positivity
    simp only [hEn]
    linarith
  set D : ℝ := En a - Linf with hD
  have hD0 : 0 ≤ D := sub_nonneg.2 (hEnf a le_rfl)
  have hβ' : 0 < β + 1 := by linarith
  have hg' : ∀ x y, ‖g x - g y‖ ≤ (β + 1) * ‖x - y‖ := fun x y => by
    have := hg x y
    nlinarith [norm_nonneg (x - y)]
  set Bm : ℝ := √(2 * D) with hBm
  set Bg : ℝ := √(2 * (β + 1) * D) with hBg
  have hBm0 : 0 ≤ Bm := Real.sqrt_nonneg _
  have hBg0 : 0 ≤ Bg := Real.sqrt_nonneg _
  have hMb : ∀ t ≥ a, ‖M t‖ ≤ Bm := fun t ht => by
    apply Real.le_sqrt_of_sq_le
    have h1 := hanti t ht
    have h2 := hinf (W t)
    simp only [hEn] at h1
    simp only [hD, hEn]
    linarith
  have hGb : ∀ t ≥ a, ‖g (W t)‖ ≤ Bg := fun t ht => by
    apply Real.le_sqrt_of_sq_le
    have h1 := hanti t ht
    have h2 : 0 ≤ ‖M t‖ ^ 2 / 2 := by positivity
    have h3 := norm_sq_grad_le hβ' hℒ hg' hinf (W t)
    simp only [hEn] at h1
    have h4 : ℒ (W t) - Linf ≤ D := by
      simp only [hD, hEn]
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * (β + 1))
    linarith
  set C₁ : ℝ := γ * Bm + Bg with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hMder : ∀ t ≥ a, ‖-(γ • M t) - P t (g (W t))‖ ≤ C₁ := fun t ht => by
    calc ‖-(γ • M t) - P t (g (W t))‖ ≤ ‖-(γ • M t)‖ + ‖P t (g (W t))‖ := norm_sub_le _ _
      _ ≤ γ * Bm + Bg := by
        rw [norm_neg, norm_smul, Real.norm_of_nonneg hγ.le]
        exact add_le_add (mul_le_mul_of_nonneg_left (hMb t ht) hγ.le)
          (((hPo t ht).norm_le _).trans (hGb t ht))
  have hWder : ∀ t ≥ a, ‖P t (M t)‖ ≤ Bm := fun t ht =>
    ((hPo t ht).norm_le _).trans (hMb t ht)
  have hMlip : ∀ {s t : ℝ}, a ≤ s → s ≤ t → ‖M t - M s‖ ≤ C₁ * (t - s) := fun hs hst =>
    norm_sub_le_of_deriv_le hMc hM hMder hs hst
  have hWlip : ∀ {s t : ℝ}, a ≤ s → s ≤ t → ‖W t - W s‖ ≤ Bm * (t - s) := fun hs hst =>
    norm_sub_le_of_deriv_le hWc hW hWder hs hst
  have hM0 : Tendsto M atTop (𝓝 0) :=
    tendsto_zero_of_energy_decay hγ hC₁0 hEnf hdecay hMlip
  refine ⟨hM0, ?_⟩
  set L₂ : ℝ := (β + 1) * Bm + K * Bm * Bg with hL₂
  have hL₂0 : 0 ≤ L₂ := by positivity
  have hqlip : ∀ {s t : ℝ}, a ≤ s → s ≤ t →
      ‖P t (g (W t)) - P s (g (W s))‖ ≤ L₂ * (t - s) := fun {s t} hs hst => by
    have ht : t ≥ a := hs.trans hst
    have e : P t (g (W t)) - P s (g (W s))
        = P t (g (W t) - g (W s)) + (P t (g (W s)) - P s (g (W s))) := by
      simp only [map_sub]
      abel
    have h0 : 0 ≤ t - s := by linarith
    have h1 : ‖P t (g (W t) - g (W s))‖ ≤ (β + 1) * (Bm * (t - s)) :=
      ((hPo t ht).norm_le _).trans ((hg' _ _).trans
        (mul_le_mul_of_nonneg_left (hWlip hs hst) hβ'.le))
    have h2 : ‖P t (g (W s)) - P s (g (W s))‖ ≤ K * (Bm * (t - s)) * Bg :=
      (hPL t ht s hs _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hWlip hs hst) hK)
        (hGb s hs) (norm_nonneg _) (by positivity))
    rw [e]
    calc _ ≤ ‖P t (g (W t) - g (W s))‖ + ‖P t (g (W s)) - P s (g (W s))‖ := norm_add_le _ _
      _ ≤ (β + 1) * (Bm * (t - s)) + K * (Bm * (t - s)) * Bg := add_le_add h1 h2
      _ = L₂ * (t - s) := by rw [hL₂]; ring
  exact tendsto_zero_of_deriv hγ.le hL₂0 hM0 hMc hM hqlip

/-- **Theorem 1 of arXiv 2506.17475: limit points are stationary.**  Under the hypotheses of
`heavyBall_tendsto`: if `W(t) → W⋆` and `P(t) → P⋆` strongly at `∇ℒ(W⋆)`, then `P⋆ ∇ℒ(W⋆) = 0`.
Unlike in the paper, the convergence of `W` is a hypothesis; it does not follow from the
others (`heavyBall_not_convergent`). -/
theorem heavyBall_limit_stationary {β : ℝ} {Wst Pst : E}
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {a : ℝ} (hPo : ∀ t ≥ a, IsOrthProj (P t))
    (hq : Tendsto (fun t => P t (g (W t))) atTop (𝓝 0)) (hlim : Tendsto W atTop (𝓝 Wst))
    (hPlim : Tendsto (fun t => P t (g Wst)) atTop (𝓝 Pst)) : Pst = 0 := by
  have h0 : Tendsto (fun t => P t (g (W t)) - P t (g Wst)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => β * ‖W t - Wst‖) atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).const_mul β)
      simpa using this
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop a] with t ht
    rw [← map_sub]
    exact ((hPo t ht).norm_le _).trans (hg _ _)
  have h2 := hq.sub h0
  simp only [sub_sub_cancel, sub_zero] at h2
  exact tendsto_nhds_unique hPlim h2

end HeavyBallFlow
/-! ### Theorem 1 on matrices, and the failure of the convergence claim -/

section HeavyBallMatrix

open scoped LeanDLRA.Frobenius
open LeanDLRA

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- **Theorem 1 of arXiv 2506.17475, corrected, for the tangent projector.**  Let `ℒ ≥ ℒ_inf` on
`ℝ^{m×n}` have a `β`-Lipschitz gradient and let `γ > 0`.  Let `W = U S Vᵀ` with orthonormal `U(t)`,
`V(t)` and `σ_min(S(t)) ≥ ρ > 0`, and let `(W, 𝒱)` solve Eq. (7) of the paper on
`[a, ∞)`: `Ẇ = P(W) 𝒱`, `𝒱̇ + γ 𝒱 = -P(W) ∇ℒ(W)`.  Then `𝒱(t) → 0`, `P(W(t)) ∇ℒ(W(t)) → 0`, and if
moreover `W(t)` converges to some `W⋆ = U⋆ S⋆ V⋆ᵀ` with orthonormal `U⋆`, `V⋆`, then
`P(W⋆) ∇ℒ(W⋆) = 0`.

**Differences from the paper.**  `∇ℒ` is Lipschitz; `σ_min ≥ ρ` is added (it makes `t ↦ P(W(t))`
Lipschitz, by `LeanDLRA.Curvature.koch_lubich_tangentProj`, and nothing is said about trajectories
leaving `ℳ_r`); `γ > 0`; and the convergence of `W` is assumed for the last claim, because it can
fail (`heavyBall_not_convergent`). -/
theorem heavyBall_tendsto_tangentProj {ℒ : Matrix m n ℝ → ℝ} {g : Matrix m n ℝ → Matrix m n ℝ}
    {γ β Linf ρ a : ℝ} {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}
    {M : ℝ → Matrix m n ℝ} (hβ : 0 ≤ β) (hρ : 0 < ρ) (hγ : 0 < γ)
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hinf : ∀ x, Linf ≤ ℒ x) (hU : ∀ t ≥ a, (U t)ᵀ * U t = 1) (hV : ∀ t ≥ a, (V t)ᵀ * V t = 1)
    (hS : ∀ t ≥ a, ∀ v : EuclideanSpace ℝ r, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (S t) v‖)
    (hWc : ContinuousOn (fun t => U t * S t * (V t)ᵀ) (Ici a)) (hMc : ContinuousOn M (Ici a))
    (hW : ∀ t ≥ a, HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (tangentProj (U t) (V t) (M t)) (Ici t) t)
    (hM : ∀ t ≥ a, HasDerivWithinAt M
      (-(γ • M t) - tangentProj (U t) (V t) (g (U t * S t * (V t)ᵀ))) (Ici t) t) :
    Tendsto M atTop (𝓝 0) ∧
      Tendsto (fun t => tangentProj (U t) (V t) (g (U t * S t * (V t)ᵀ))) atTop (𝓝 0) ∧
      ∀ {Ust : Matrix m r ℝ} {Sst : Matrix r r ℝ} {Vst : Matrix n r ℝ}, Ustᵀ * Ust = 1 →
        Vstᵀ * Vst = 1 → Tendsto (fun t => U t * S t * (V t)ᵀ) atTop (𝓝 (Ust * Sst * Vstᵀ)) →
        tangentProj Ust Vst (g (Ust * Sst * Vstᵀ)) = 0 := by
  classical
  set K : ℝ := 2 * √2 * ρ⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hkl : ∀ {U' : Matrix m r ℝ} {S' : Matrix r r ℝ} {V' : Matrix n r ℝ}, U'ᵀ * U' = 1 →
      V'ᵀ * V' = 1 → ∀ t ≥ a, ∀ x : Matrix m n ℝ,
      ‖tangentProj U' V' x - tangentProj (U t) (V t) x‖ ≤
        K * ‖U' * S' * V'ᵀ - U t * S t * (V t)ᵀ‖ * ‖x‖ := fun hU' hV' t ht x =>
    (Curvature.koch_lubich_tangentProj hρ (hU t ht) (hV t ht) hU' hV' (hS t ht) x).trans
      (mul_le_mul_of_nonneg_left (Curvature.specNorm_le_frob x) (by positivity))
  have hPo : ∀ t ≥ a, IsOrthProj (tangentProj (U t) (V t) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    fun t ht => isOrthProj_tangentProj (hU t ht) (hV t ht)
  obtain ⟨h1, h2⟩ := heavyBall_tendsto (P := fun t => tangentProj (U t) (V t))
    (W := fun t => U t * S t * (V t)ᵀ) (K := K) hβ hK0 hγ hℒ hg hinf hPo
    (fun s hs t ht x => hkl (hU s hs) (hV s hs) t ht x) hWc hMc hW hM
  refine ⟨h1, h2, fun {Ust Sst Vst} hUst hVst hlim => ?_⟩
  refine heavyBall_limit_stationary hg hPo h2 hlim ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun t => K * ‖Ust * Sst * Vstᵀ - U t * S t * (V t)ᵀ‖
      * ‖g (Ust * Sst * Vstᵀ)‖) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).const_mul K).mul_const
      ‖g (Ust * Sst * Vstᵀ)‖
    simpa [norm_sub_rev] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop a] with t ht
  rw [norm_sub_rev]
  exact hkl hUst hVst t ht _

end HeavyBallMatrix

section HeavyBallCounterexample

open scoped LeanDLRA.Frobenius
open LeanDLRA

/-- The scalar loss `ℓ(x) = -sech²(x) / 2 - γ arctan(sinh x)` of `heavyBall_not_convergent`. -/
noncomputable def driftLoss (γ x : ℝ) : ℝ :=
  -((Real.cosh x)⁻¹ ^ 2 / 2) - γ * Real.arctan (Real.sinh x)

/-- The derivative of `driftLoss`. -/
noncomputable def driftGrad (γ x : ℝ) : ℝ :=
  Real.sinh x * (Real.cosh x)⁻¹ ^ 3 - γ * (Real.cosh x)⁻¹

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: the derivative of `sech`. -/
theorem hasDerivAt_sech (x : ℝ) :
    HasDerivAt (fun x => (Real.cosh x)⁻¹) (-(Real.sinh x * (Real.cosh x)⁻¹ ^ 2)) x := by
  have := (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
  refine this.congr_deriv ?_
  have h := (Real.cosh_pos x).ne'
  field_simp

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `cosh · sech = 1`. -/
theorem cosh_mul_sech (x : ℝ) : Real.cosh x * (Real.cosh x)⁻¹ = 1 :=
  mul_inv_cancel₀ (Real.cosh_pos x).ne'

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `driftGrad` is the derivative of `driftLoss`. -/
theorem hasDerivAt_driftLoss (γ x : ℝ) : HasDerivAt (driftLoss γ) (driftGrad γ x) x := by
  have h1 := ((hasDerivAt_sech x).pow 2).div_const 2
  have h2 := (Real.hasDerivAt_sinh x).arctan
  refine (h1.neg.sub (h2.const_mul γ)).congr_deriv ?_
  have hc := Real.cosh_sq x
  have hc0 := (Real.cosh_pos x).ne'
  have e : 1 / (1 + Real.sinh x ^ 2) * Real.cosh x = (Real.cosh x)⁻¹ := by
    rw [show 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 by rw [hc]; ring]
    field_simp
  rw [e, driftGrad]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- The second derivative of `driftLoss`. -/
noncomputable def driftGrad' (γ x : ℝ) : ℝ :=
  (Real.cosh x)⁻¹ ^ 2 - 3 * (Real.sinh x * (Real.cosh x)⁻¹) ^ 2 * (Real.cosh x)⁻¹ ^ 2
    + γ * (Real.sinh x * (Real.cosh x)⁻¹) * (Real.cosh x)⁻¹

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `driftGrad'` is the derivative of `driftGrad`. -/
theorem hasDerivAt_driftGrad (γ x : ℝ) : HasDerivAt (driftGrad γ) (driftGrad' γ x) x := by
  have hs := hasDerivAt_sech x
  have h := ((Real.hasDerivAt_sinh x).mul (hs.pow 3)).sub (hs.const_mul γ)
  refine h.congr_deriv ?_
  have hcs := cosh_mul_sech x
  simp only [driftGrad', show (3 - 1 : ℕ) = 2 from rfl, Nat.cast_ofNat, Pi.pow_apply]
  linear_combination ((Real.cosh x)⁻¹ ^ 2) * hcs

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `sech ≤ 1`. -/
theorem sech_le_one (x : ℝ) : (Real.cosh x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh x)

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `sech > 0`. -/
theorem sech_pos (x : ℝ) : 0 < (Real.cosh x)⁻¹ := inv_pos.2 (Real.cosh_pos x)

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `tanh² ≤ 1`. -/
theorem sq_sinh_mul_sech_le (x : ℝ) : (Real.sinh x * (Real.cosh x)⁻¹) ^ 2 ≤ 1 := by
  have hc := Real.cosh_sq x
  have hcs := cosh_mul_sech x
  have h1 : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by rw [hc]; linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Real.cosh x)⁻¹)
  have e1 : Real.cosh x ^ 2 * (Real.cosh x)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, hcs, one_pow]
  rw [mul_pow]
  linarith

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `|driftGrad'| ≤ 4 + γ`. -/
theorem abs_driftGrad'_le {γ : ℝ} (hγ : 0 ≤ γ) (x : ℝ) : |driftGrad' γ x| ≤ 4 + γ := by
  set s := (Real.cosh x)⁻¹ with hs
  set τ := Real.sinh x * s with hτ
  have h0 : 0 < s := sech_pos x
  have h1 : s ≤ 1 := sech_le_one x
  have h2 : τ ^ 2 ≤ 1 := sq_sinh_mul_sech_le x
  have h3 : s ^ 2 ≤ 1 := by nlinarith
  have h4 : |τ| ≤ 1 := abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  have h5 : 0 ≤ τ ^ 2 * s ^ 2 := by positivity
  have h6 : τ ^ 2 * s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg τ]
  have h7 : |γ * τ * s| ≤ γ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hγ, abs_of_pos h0]
    have : |τ| * s ≤ 1 := by nlinarith [abs_nonneg τ]
    nlinarith
  have e : driftGrad' γ x = s ^ 2 - 3 * τ ^ 2 * s ^ 2 + γ * τ * s := rfl
  rw [e, abs_le]
  have h8 := abs_le.1 h7
  have h9 : 0 ≤ s ^ 2 := by positivity
  constructor <;> nlinarith [h8.1, h8.2]

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `driftGrad` is Lipschitz. -/
theorem driftGrad_lipschitz {γ : ℝ} (hγ : 0 ≤ γ) (x y : ℝ) :
    |driftGrad γ x - driftGrad γ y| ≤ (4 + γ) * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := driftGrad γ)
    (f' := driftGrad' γ) (s := univ) (x := y) (y := x) (C := 4 + γ)
    (fun z _ => (hasDerivAt_driftGrad γ z).hasDerivWithinAt)
    (fun z _ => abs_driftGrad'_le hγ z) convex_univ (mem_univ _) (mem_univ _)
  simpa using this

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: `driftLoss` is bounded below. -/
theorem driftLoss_ge {γ : ℝ} (hγ : 0 ≤ γ) (x : ℝ) :
    -(1 / 2) - γ * (Real.pi / 2) ≤ driftLoss γ x := by
  have h1 : (Real.cosh x)⁻¹ ^ 2 ≤ 1 := by
    nlinarith [sech_pos x, sech_le_one x]
  have h2 := (Real.arctan_lt_pi_div_two (Real.sinh x)).le
  have h3 := mul_le_mul_of_nonneg_left h2 hγ
  unfold driftLoss
  linarith

/-- The `(0, 0)` entry of a `1 × 1` matrix. -/
theorem inner_one_one (X : Matrix (Fin 1) (Fin 1) ℝ) :
    ⟪(1 : Matrix (Fin 1) (Fin 1) ℝ), X⟫ = X 0 0 := by
  rw [Frobenius.inner_def]
  simp

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: the entry of a `1 × 1` matrix has gradient `1`. -/
theorem hasFDerivAt_entry_one (W : Matrix (Fin 1) (Fin 1) ℝ) :
    HasFDerivAt (fun X : Matrix (Fin 1) (Fin 1) ℝ => X 0 0)
      (innerSL ℝ (1 : Matrix (Fin 1) (Fin 1) ℝ)) W := by
  refine ((innerSL ℝ (1 : Matrix (Fin 1) (Fin 1) ℝ)).hasFDerivAt (x := W)).congr_of_eventuallyEq
    (Eventually.of_forall fun X => ?_)
  simp [innerSL_apply_apply, inner_one_one]

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: the norm of a `1 × 1` matrix. -/
theorem norm_one_by_one (X : Matrix (Fin 1) (Fin 1) ℝ) : ‖X‖ = |X 0 0| := by
  have h : ‖X‖ ^ 2 = (X 0 0) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp
  rw [← abs_of_nonneg (norm_nonneg X)]
  exact (sq_eq_sq_iff_abs_eq_abs _ _).1 h

/-- Auxiliary for Theorem 1 of arXiv 2506.17475: for `1 × 1` matrices the tangent projector is the
identity. -/
theorem tangentProj_one_one (Z : Matrix (Fin 1) (Fin 1) ℝ) :
    tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) Z = Z := by
  rw [tangentProj_apply]
  simp

/-- **The convergence claim of Theorem 1 of arXiv 2506.17475 is false.**  The paper states that
every solution of `Ẇ = P(W) 𝒱`, `𝒱̇ + γ 𝒱 = -P(W) ∇ℒ(W)` with `ℒ` bounded below converges to a point
`W⋆` with `P(W⋆) ∇ℒ(W⋆) = 0`.  Here is a counterexample for every `γ ≥ 0`, with `m = n = r = 1`,
`U = V = 1`, `S = W`, where `P(W)` is the identity: `ℓ(x) = -sech²(x)/2 - γ arctan(sinh x)` is
bounded below with Lipschitz derivative, and `x(t) = arsinh(t + 1) > 0`,
`v = sech(x(t))` solves `ẋ = v`, `v̇ + γ v = -ℓ'(x)`.  Since `x(t) → ∞`, `W(t)` does not converge.
For `γ > 0` the corrected statement `heavyBall_tendsto` applies to this example. -/
theorem heavyBall_not_convergent {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ (ℒ : Matrix (Fin 1) (Fin 1) ℝ → ℝ) (g : Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ)
      (Linf K : ℝ) (W M : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
      (∀ X, HasFDerivAt ℒ (innerSL ℝ (g X)) X) ∧ (∀ X, Linf ≤ ℒ X) ∧
      (∀ X Y, ‖g X - g Y‖ ≤ K * ‖X - Y‖) ∧ (∀ t ≥ 0, IsUnit (W t).det) ∧
      (∀ t ≥ 0, HasDerivAt W (tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (M t)) t) ∧
      (∀ t ≥ 0, HasDerivAt M (-(γ • M t) - tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (g (W t))) t) ∧
      ¬ ∃ Wst, Tendsto W atTop (𝓝 Wst) := by
  set x : ℝ → ℝ := fun t => Real.arsinh (t + 1) with hx
  have hx' : ∀ t, HasDerivAt x (Real.cosh (x t))⁻¹ t := fun t => by
    have h1 := (Real.hasDerivAt_arsinh (t + 1)).comp t ((hasDerivAt_id t).add_const 1)
    refine h1.congr_deriv ?_
    simp [hx, Real.cosh_arsinh]
  have hs : ∀ t, HasDerivAt (fun t => (Real.cosh (x t))⁻¹)
      (-(Real.sinh (x t) * (Real.cosh (x t))⁻¹ ^ 3)) t := fun t => by
    have h1 := (hasDerivAt_sech (x t)).comp t (hx' t)
    refine h1.congr_deriv ?_
    ring
  refine ⟨fun X => driftLoss γ (X 0 0), fun X => driftGrad γ (X 0 0) • 1,
    -(1 / 2) - γ * (Real.pi / 2), 4 + γ, fun t => x t • 1,
    fun t => (Real.cosh (x t))⁻¹ • 1, fun X => ?_, fun X => driftLoss_ge hγ _, fun X Y => ?_,
    fun t ht => ?_, fun t _ => ?_, fun t _ => ?_, ?_⟩
  · have h := (hasDerivAt_driftLoss γ (X 0 0)).comp_hasFDerivAt X (hasFDerivAt_entry_one X)
    refine h.congr_fderiv ?_
    ext1 Y
    simp [innerSL_apply_apply]
  · have e : ∀ c d : ℝ, ‖c • (1 : Matrix (Fin 1) (Fin 1) ℝ) - d • 1‖ = |c - d| := fun c d => by
      rw [norm_one_by_one]
      simp
    rw [e, norm_one_by_one (X - Y)]
    exact driftGrad_lipschitz hγ _ _
  · have hpos : 0 < x t := Real.arsinh_pos_iff.2 (by linarith)
    simp [hpos.ne']
  · rw [tangentProj_one_one]
    exact (hx' t).smul_const 1
  · rw [tangentProj_one_one]
    refine ((hs t).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)).congr_deriv ?_
    have e : (x t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 = x t := by simp
    change _ = -(γ • ((Real.cosh (x t))⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
      - driftGrad γ ((x t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
    rw [e, driftGrad]
    module
  · rintro ⟨Wst, hlim⟩
    have hent : Continuous (fun X : Matrix (Fin 1) (Fin 1) ℝ => Real.sinh (X 0 0)) := by
      have h1 : Continuous (fun X : Matrix (Fin 1) (Fin 1) ℝ => X 0 0) :=
        (continuous_iff_continuousAt.2 fun W => (hasFDerivAt_entry_one W).continuousAt)
      exact Real.continuous_sinh.comp h1
    have h2 := hent.tendsto Wst |>.comp hlim
    have h3 : Tendsto (fun t : ℝ => t + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have h4 : (fun X : Matrix (Fin 1) (Fin 1) ℝ => Real.sinh (X 0 0)) ∘
        (fun t => x t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) = fun t => t + 1 := by
      funext t
      simp [hx, Real.sinh_arsinh]
    rw [h4] at h2
    exact not_tendsto_nhds_of_tendsto_atTop h3 _ h2

end HeavyBallCounterexample
/-! ### Theorem 3: the error of the low-rank heavy-ball method -/

section HeavyBallError

open LeanDLRA

/-- Consistency of one step: if `‖f' - v‖ ≤ c` on `[a, a + h)`, then
`‖f (a + h) - f a - h v‖ ≤ c h`. -/
theorem norm_sub_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {v : E} {a h c : ℝ} (hh : 0 ≤ h) (hc : ContinuousOn f (Icc a (a + h)))
    (hd : ∀ t ∈ Ico a (a + h), HasDerivWithinAt f (f' t) (Ici t) t)
    (hb : ∀ t ∈ Ico a (a + h), ‖f' t - v‖ ≤ c) : ‖f (a + h) - f a - h • v‖ ≤ c * h := by
  have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun t => f t - (t - a) • v) (f' := fun t => f' t - v) (C := c) (a := a) (b := a + h)
    (hc.sub (Continuous.continuousOn (by fun_prop)))
    (fun t ht => by
      have h2 := (hd t ht).sub (((hasDerivWithinAt_id t (Ici t)).sub_const a).smul_const v)
      exact h2.congr_deriv (by simp)) hb (a + h) ⟨by linarith, le_rfl⟩
  have e : f (a + h) - (a + h - a) • v - (f a - (a - a) • v) = f (a + h) - f a - h • v := by
    simp
    abel
  rw [e] at h1
  simpa using h1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step of the error recursion of the low-rank heavy-ball method, written for the augmented
momentum `mh = (1 - λ γ) m - λ p (g w)`, with truncation errors `ϑ`, `ϑh`, against a reference
pair `(x, y)` with consistency defects `D₁`, `D₂`. -/
theorem heavyBall_step_error {g : E → E} {β γ lr ε ϑ ϑh B BM D₁ D₂ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hlr : 0 ≤ lr) (hlrγ : lr * γ ≤ 1) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {p : E →L[ℝ] E} (hp : IsOrthProj p) {w m mh w₁ m₁ x y x₁ y₁ : E}
    (hmh : mh = (1 - lr * γ) • m - lr • p (g w)) (hw : ‖w₁ - (w + lr • mh)‖ ≤ ϑ)
    (hm : ‖m₁ - mh‖ ≤ ϑh) (hx : ‖x₁ - x - lr • y‖ ≤ D₁)
    (hy : ‖y₁ - y - lr • (-(γ • y) - g x)‖ ≤ D₂) (hε : ‖(1 - p) (g w)‖ ≤ ε) (hB : ‖g w‖ ≤ B)
    (hBM : ‖m‖ ≤ BM) :
    ‖w₁ - x₁‖ + ‖m₁ - y₁‖ ≤ Real.exp ((1 + β) * lr) * (‖w - x‖ + ‖m - y‖)
      + (ϑ + ϑh + D₁ + D₂ + lr * ε + lr ^ 2 * (γ * BM + B)) := by
  have hpg : ‖p (g w)‖ ≤ B := (hp.norm_le _).trans hB
  have hmm : ‖mh - m‖ ≤ lr * (γ * BM + B) := by
    have e : mh - m = -(lr • (γ • m + p (g w))) := by
      rw [hmh]
      module
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hlr]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ hpg)) hlr
    rw [norm_smul, Real.norm_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left hBM hγ
  have e1 : w₁ - x₁ = (w₁ - (w + lr • mh)) + (w - x) + lr • (m - y) + lr • (mh - m)
      - (x₁ - x - lr • y) := by
    module
  have e2 : m₁ - y₁ = (m₁ - mh) + (1 - lr * γ) • (m - y) - lr • (p (g w) - g x)
      - (y₁ - y - lr • (-(γ • y) - g x)) := by
    rw [hmh]
    module
  have h1 : ‖lr • (m - y)‖ = lr * ‖m - y‖ := by rw [norm_smul, Real.norm_of_nonneg hlr]
  have h2 : ‖lr • (mh - m)‖ ≤ lr * (lr * (γ * BM + B)) := by
    rw [norm_smul, Real.norm_of_nonneg hlr]
    exact mul_le_mul_of_nonneg_left hmm hlr
  have h3 : ‖(1 - lr * γ) • (m - y)‖ = (1 - lr * γ) * ‖m - y‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
  have h4 : ‖p (g w) - g x‖ ≤ ε + β * ‖w - x‖ := by
    have e3 : p (g w) - g x = -((1 - p) (g w)) + (g w - g x) := by
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [e3]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hg _ _))
    rw [norm_neg]
    exact hε
  have h5 : ‖lr • (p (g w) - g x)‖ ≤ lr * (ε + β * ‖w - x‖) := by
    rw [norm_smul, Real.norm_of_nonneg hlr]
    exact mul_le_mul_of_nonneg_left h4 hlr
  have hW : ‖w₁ - x₁‖ ≤ ϑ + ‖w - x‖ + lr * ‖m - y‖ + lr * (lr * (γ * BM + B)) + D₁ := by
    rw [e1]
    calc _ ≤ ‖(w₁ - (w + lr • mh)) + (w - x) + lr • (m - y) + lr • (mh - m)‖
          + ‖x₁ - x - lr • y‖ := norm_sub_le _ _
      _ ≤ ‖(w₁ - (w + lr • mh))‖ + ‖w - x‖ + ‖lr • (m - y)‖ + ‖lr • (mh - m)‖
          + ‖x₁ - x - lr • y‖ := by
        gcongr
        exact norm_add₄_le
      _ ≤ _ := by rw [h1]; gcongr
  have hM : ‖m₁ - y₁‖ ≤ ϑh + (1 - lr * γ) * ‖m - y‖ + lr * (ε + β * ‖w - x‖) + D₂ := by
    rw [e2]
    calc _ ≤ ‖(m₁ - mh) + (1 - lr * γ) • (m - y) - lr • (p (g w) - g x)‖
          + ‖y₁ - y - lr • (-(γ • y) - g x)‖ := norm_sub_le _ _
      _ ≤ ‖m₁ - mh‖ + ‖(1 - lr * γ) • (m - y)‖ + ‖lr • (p (g w) - g x)‖
          + ‖y₁ - y - lr • (-(γ • y) - g x)‖ := by
        gcongr
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ _ := by rw [h3]; gcongr
  have hexp : 1 + (1 + β) * lr ≤ Real.exp ((1 + β) * lr) := by
    linarith [Real.add_one_le_exp ((1 + β) * lr)]
  have hnn : 0 ≤ ‖w - x‖ + ‖m - y‖ := by positivity
  have h6 := mul_le_mul_of_nonneg_right hexp hnn
  have h7 : 0 ≤ lr * γ * ‖m - y‖ := by positivity
  have h8 : 0 ≤ lr * β * ‖m - y‖ := by positivity
  have h9 : 0 ≤ lr * ‖w - x‖ := by positivity
  nlinarith

/-- The two consistency defects of a pair `(X, Y)` with `‖Ẋ - Y‖ ≤ ε₁`, `‖Ẏ + γ Y + g(X)‖ ≤ ε₂`
over one step `[a, a + λ]`. -/
theorem heavyBall_defects {g : E → E} {β γ lr ε₁ ε₂ BX BY a : ℝ} (hγ : 0 ≤ γ) (hβ : 0 ≤ β)
    (hlr : 0 ≤ lr) (hBX0 : 0 ≤ BX) (hBY0 : 0 ≤ BY) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {X Y A C : ℝ → E} (hXc : ContinuousOn X (Icc a (a + lr)))
    (hYc : ContinuousOn Y (Icc a (a + lr)))
    (hX : ∀ t ∈ Ico a (a + lr), HasDerivWithinAt X (A t) (Ici t) t)
    (hY : ∀ t ∈ Ico a (a + lr), HasDerivWithinAt Y (C t) (Ici t) t)
    (hA : ∀ t ∈ Ico a (a + lr), ‖A t - Y t‖ ≤ ε₁)
    (hC : ∀ t ∈ Ico a (a + lr), ‖C t - (-(γ • Y t) - g (X t))‖ ≤ ε₂)
    (hBA : ∀ t ∈ Ico a (a + lr), ‖A t‖ ≤ BX) (hBC : ∀ t ∈ Ico a (a + lr), ‖C t‖ ≤ BY) :
    ‖X (a + lr) - X a - lr • Y a‖ ≤ (ε₁ + BY * lr) * lr ∧
      ‖Y (a + lr) - Y a - lr • (-(γ • Y a) - g (X a))‖ ≤
        (ε₂ + (γ * BY + β * BX) * lr) * lr := by
  have hXl : ∀ s ∈ Ico a (a + lr), ‖X s - X a‖ ≤ BX * lr := fun s hs => by
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hXc hX hBA s
      ⟨hs.1, hs.2.le⟩
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hBX0)
  have hYl : ∀ s ∈ Ico a (a + lr), ‖Y s - Y a‖ ≤ BY * lr := fun s hs => by
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hYc hY hBC s
      ⟨hs.1, hs.2.le⟩
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hBY0)
  constructor
  · refine norm_sub_sub_smul_le hlr hXc hX fun s hs => ?_
    have e : A s - Y a = (A s - Y s) + (Y s - Y a) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (hA s hs) (hYl s hs))
  · refine norm_sub_sub_smul_le hlr hYc hY fun s hs => ?_
    have e : C s - (-(γ • Y a) - g (X a)) = (C s - (-(γ • Y s) - g (X s)))
        + (-(γ • (Y s - Y a)) - (g (X s) - g (X a))) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hC s hs) ?_)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hγ]
    have h1 := mul_le_mul_of_nonneg_left (hYl s hs) hγ
    have h2 := (hg (X s) (X a)).trans (mul_le_mul_of_nonneg_left (hXl s hs) hβ)
    nlinarith

/-- The local defect `b` of the low-rank heavy-ball method: truncation errors `ϑ`, `ϑh`, normal
components `ε`, and `O(λ²)` terms. -/
noncomputable def hbLocal (β γ lr ε ϑ ϑh B BM BX BY : ℝ) : ℝ :=
  ϑ + ϑh + lr * ε + lr ^ 2 * (γ * BM + B + BY + γ * BY + β * BX)

/-- **Global error of the heavy-ball iteration against a perturbed flow** (the discrete Grönwall
argument in Theorem 3 of arXiv 2506.17475, on an abstract real inner product space).  The iteration
`m̂ₙ = (1 - λ γ) mₙ - λ Πₙ g(wₙ)`, `‖w_{n+1} - (wₙ + λ m̂ₙ)‖ ≤ ϑ`, `‖m_{n+1} - m̂ₙ‖ ≤ ϑh` with
orthogonal projectors `Πₙ`, `‖(1 - Πₙ) g(wₙ)‖ ≤ ε₀`, is compared with a pair `(X, Y)` with
`‖Ẋ - Y‖ ≤ ε₁`, `‖Ẏ + γ Y + g(X)‖ ≤ ε₂`.  The constant is `e^{(1 + β) n λ}`, and the projectors
enter only through being orthogonal: nothing depends on singular values. -/
theorem heavyBallIter_error {g : E → E} {β γ lr ε₀ ε₁ ε₂ ϑ ϑh B BM BX BY t₀ : ℝ} {N : ℕ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hlr : 0 ≤ lr) (hlrγ : lr * γ ≤ 1) (hε₀0 : 0 ≤ ε₀) (hε₁0 : 0 ≤ ε₁)
    (hε₂0 : 0 ≤ ε₂) (hϑ0 : 0 ≤ ϑ) (hϑh0 : 0 ≤ ϑh) (hB0 : 0 ≤ B) (hBM0 : 0 ≤ BM) (hBX0 : 0 ≤ BX)
    (hBY0 : 0 ≤ BY) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Wk Mk Mh : ℕ → E}
    {Pr : ℕ → E →L[ℝ] E} (hPr : ∀ n < N, IsOrthProj (Pr n))
    (hMh : ∀ n < N, Mh n = (1 - lr * γ) • Mk n - lr • Pr n (g (Wk n)))
    (hWs : ∀ n < N, ‖Wk (n + 1) - (Wk n + lr • Mh n)‖ ≤ ϑ)
    (hMs : ∀ n < N, ‖Mk (n + 1) - Mh n‖ ≤ ϑh) (hε₀ : ∀ n < N, ‖(1 - Pr n) (g (Wk n))‖ ≤ ε₀)
    (hBW : ∀ n < N, ‖g (Wk n)‖ ≤ B) (hBM : ∀ n < N, ‖Mk n‖ ≤ BM) {X Y A C : ℝ → E}
    (hXc : ContinuousOn X (Icc t₀ (t₀ + N * lr))) (hYc : ContinuousOn Y (Icc t₀ (t₀ + N * lr)))
    (hX : ∀ t ∈ Ico t₀ (t₀ + N * lr), HasDerivWithinAt X (A t) (Ici t) t)
    (hY : ∀ t ∈ Ico t₀ (t₀ + N * lr), HasDerivWithinAt Y (C t) (Ici t) t)
    (hA : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖A t - Y t‖ ≤ ε₁)
    (hC : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖C t - (-(γ • Y t) - g (X t))‖ ≤ ε₂)
    (hBA : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖A t‖ ≤ BX)
    (hBC : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖C t‖ ≤ BY) :
    ∀ n ≤ N, ‖Wk n - X (t₀ + n * lr)‖ + ‖Mk n - Y (t₀ + n * lr)‖ ≤
      Real.exp ((1 + β) * (n * lr)) * (‖Wk 0 - X t₀‖ + ‖Mk 0 - Y t₀‖
        + n * hbLocal β γ lr (ε₀ + ε₁ + ε₂) ϑ ϑh B BM BX BY) := by
  have hL : 0 ≤ 1 + β := by linarith
  set b : ℝ := hbLocal β γ lr (ε₀ + ε₁ + ε₂) ϑ ϑh B BM BX BY with hb
  have hb0 : 0 ≤ b := by
    simp only [hb, hbLocal]
    positivity
  set e : ℕ → ℝ := fun n => ‖Wk n - X (t₀ + n * lr)‖ + ‖Mk n - Y (t₀ + n * lr)‖ with he
  have hrec : ∀ n < N, e (n + 1) ≤ Real.exp ((1 + β) * lr) * e n + b := by
    intro n hn
    set a : ℝ := t₀ + n * lr with ha
    have hnext : t₀ + ((n + 1 : ℕ) : ℝ) * lr = a + lr := by
      rw [ha]
      push_cast
      ring
    have hNlr : a + lr ≤ t₀ + N * lr := by
      rw [← hnext]
      have : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
      have := mul_le_mul_of_nonneg_right this hlr
      linarith
    have ha0 : t₀ ≤ a := by
      have : 0 ≤ (n : ℝ) * lr := by positivity
      rw [ha]
      linarith
    have hsubI : Icc a (a + lr) ⊆ Icc t₀ (t₀ + N * lr) := Icc_subset_Icc ha0 hNlr
    have hsub : Ico a (a + lr) ⊆ Ico t₀ (t₀ + N * lr) := Ico_subset_Ico ha0 hNlr
    obtain ⟨hD₁, hD₂⟩ := heavyBall_defects (ε₁ := ε₁) (ε₂ := ε₂) hγ hβ hlr hBX0 hBY0 hg
      (hXc.mono hsubI) (hYc.mono hsubI) (fun t ht => hX t (hsub ht)) (fun t ht => hY t (hsub ht))
      (fun t ht => hA t (hsub ht)) (fun t ht => hC t (hsub ht)) (fun t ht => hBA t (hsub ht))
      (fun t ht => hBC t (hsub ht))
    have h := heavyBall_step_error hβ hγ hlr hlrγ hg (hPr n hn) (hMh n hn) (hWs n hn) (hMs n hn)
      hD₁ hD₂ (hε₀ n hn) (hBW n hn) (hBM n hn)
    simp only [he]
    rw [hnext]
    refine h.trans (le_of_eq ?_)
    simp only [hb, hbLocal]
    ring
  intro n hn
  have h := discrete_gronwall_exp_le hL hlr hb0 hrec n hn
  simpa [he] using h

/-- Bound of the exact momentum: if `Ṁ = -γ M - q`, `γ ≥ 0`, `‖q‖ ≤ B`, then
`‖M(t)‖ ≤ ‖M(a)‖ + (t - a) B`. -/
theorem norm_momentum_le {M q : ℝ → E} {γ B a b : ℝ} (hγ : 0 ≤ γ)
    (hc : ContinuousOn M (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt M (-(γ • M t) - q t) (Ici t) t)
    (hq : ∀ t ∈ Ico a b, ‖q t‖ ≤ B) : ∀ t ∈ Icc a b, ‖M t‖ ≤ ‖M a‖ + (t - a) * B := by
  intro t ht
  have hexp : ∀ s, HasDerivAt (fun s => Real.exp (γ * (s - t)))
      (γ * Real.exp (γ * (s - t))) s := fun s => by
    have h1 : HasDerivAt (fun s => γ * (s - t)) γ s := by
      simpa using ((hasDerivAt_id s).sub_const t).const_mul γ
    have h2 := h1.exp
    exact h2.congr_deriv (by ring)
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun s => Real.exp (γ * (s - t)) • M s)
    (f' := fun s => -(Real.exp (γ * (s - t)) • q s)) (C := B) (a := a) (b := t)
    ((Continuous.continuousOn (by fun_prop)).smul (hc.mono (Icc_subset_Icc_right ht.2)))
    (fun s hs => by
      have hs' : s ∈ Ico a b := ⟨hs.1, hs.2.trans_le ht.2⟩
      have h2 := (hexp s).hasDerivWithinAt.smul (hd s hs')
      refine h2.congr_deriv ?_
      module)
    (fun s hs => by
      have hs' : s ∈ Ico a b := ⟨hs.1, hs.2.trans_le ht.2⟩
      rw [norm_neg, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have h3 : Real.exp (γ * (s - t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : s - t ≤ 0 := by linarith [hs.2]
        nlinarith
      calc _ ≤ 1 * ‖q s‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ ≤ B := by rw [one_mul]; exact hq s hs') t ⟨ht.1, le_rfl⟩
  simp only [sub_self, mul_zero, Real.exp_zero, one_smul] at h
  have h4 : ‖Real.exp (γ * (a - t)) • M a‖ ≤ ‖M a‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h3 : Real.exp (γ * (a - t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : a - t ≤ 0 := by linarith [ht.1]
      nlinarith
    calc _ ≤ 1 * ‖M a‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = ‖M a‖ := one_mul _
  have h5 := norm_sub_norm_le (M t) (Real.exp (γ * (a - t)) • M a)
  have h6 : (t - a) * B = B * (t - a) := by ring
  linarith

/-- **Theorem 3 of arXiv 2506.17475, abstract form.**  The heavy-ball iteration of
`heavyBallIter_error` is compared with a solution of `Ẇ = P 𝒱`, `𝒱̇ = -γ 𝒱 - P g(W)` with orthogonal
projectors `P(t)`, assuming `‖(1 - P) g(W)‖ ≤ ε'` and `‖(1 - P) 𝒱‖ ≤ εV` along the flow.
All bounds on the momenta are derived; only `‖g‖ ≤ B` along the two trajectories is assumed. -/
theorem heavyBall_global_error {g : E → E} {β γ lr ε ε' εV ϑ ϑh B t₀ : ℝ} {N : ℕ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hlr : 0 ≤ lr) (hlrγ : lr * γ ≤ 1) (hε0 : 0 ≤ ε) (hε'0 : 0 ≤ ε')
    (hεV0 : 0 ≤ εV) (hϑ0 : 0 ≤ ϑ) (hϑh0 : 0 ≤ ϑh) (hB0 : 0 ≤ B)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Wk Mk Mh : ℕ → E}
    {Pr : ℕ → E →L[ℝ] E} (hPr : ∀ n < N, IsOrthProj (Pr n))
    (hMh : ∀ n < N, Mh n = (1 - lr * γ) • Mk n - lr • Pr n (g (Wk n)))
    (hWs : ∀ n < N, ‖Wk (n + 1) - (Wk n + lr • Mh n)‖ ≤ ϑ)
    (hMs : ∀ n < N, ‖Mk (n + 1) - Mh n‖ ≤ ϑh) (hMc : ∀ n < N, ‖Mk (n + 1)‖ ≤ ‖Mh n‖)
    (hε : ∀ n < N, ‖(1 - Pr n) (g (Wk n))‖ ≤ ε) (hBW : ∀ n < N, ‖g (Wk n)‖ ≤ B)
    {X Y : ℝ → E} {P : ℝ → E →L[ℝ] E}
    (hP : ∀ t ∈ Ico t₀ (t₀ + N * lr), IsOrthProj (P t))
    (hX : ODESolution (fun t _ => P t (Y t)) X t₀ (t₀ + N * lr))
    (hY : ODESolution (fun t Z => -(γ • Z) - P t (g (X t))) Y t₀ (t₀ + N * lr))
    (hε' : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (g (X t))‖ ≤ ε')
    (hεV : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (Y t)‖ ≤ εV)
    (hBX : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖g (X t)‖ ≤ B) :
    ∀ n ≤ N, ‖Wk n - X (t₀ + n * lr)‖ + ‖Mk n - Y (t₀ + n * lr)‖ ≤
      Real.exp ((1 + β) * (n * lr)) * (‖Wk 0 - X t₀‖ + ‖Mk 0 - Y t₀‖
        + n * hbLocal β γ lr (ε + εV + ε') ϑ ϑh B (‖Mk 0‖ + N * lr * B)
          (‖Y t₀‖ + N * lr * B) (γ * (‖Y t₀‖ + N * lr * B) + B)) := by
  set T : ℝ := N * lr with hT
  have hT0 : 0 ≤ T := by positivity
  -- the discrete momentum
  have hBMn : ∀ n ≤ N, ‖Mk n‖ ≤ ‖Mk 0‖ + n * lr * B := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk' : k < N := hk
      have h1 := ih hk'.le
      have h2 : ‖Mh k‖ ≤ (1 - lr * γ) * ‖Mk k‖ + lr * B := by
        rw [hMh k hk']
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        · rw [norm_smul, Real.norm_of_nonneg hlr]
          exact mul_le_mul_of_nonneg_left (((hPr k hk').norm_le _).trans (hBW k hk')) hlr
      have h3 : (1 - lr * γ) * ‖Mk k‖ ≤ ‖Mk k‖ := by
        have : 0 ≤ lr * γ * ‖Mk k‖ := by positivity
        linarith
      have h4 := hMc k hk'
      push_cast
      nlinarith
  have hBM : ∀ n < N, ‖Mk n‖ ≤ ‖Mk 0‖ + N * lr * B := fun n hn => by
    have h1 := hBMn n hn.le
    have h2 : (n : ℝ) * lr * B ≤ N * lr * B := by
      have : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      gcongr
    linarith
  -- the exact momentum
  have hPg : ∀ t ∈ Ico t₀ (t₀ + T), ‖P t (g (X t))‖ ≤ B := fun t ht =>
    ((hP t ht).norm_le _).trans (hBX t ht)
  have hYb := norm_momentum_le (b := t₀ + T) hγ hY.cont hY.deriv hPg
  have hYB : ∀ t ∈ Ico t₀ (t₀ + T), ‖Y t‖ ≤ ‖Y t₀‖ + T * B := fun t ht => by
    have h1 := hYb t ⟨ht.1, ht.2.le⟩
    have h2 : (t - t₀) * B ≤ T * B := by
      have : t - t₀ ≤ T := by linarith [ht.2]
      gcongr
    linarith
  refine heavyBallIter_error hβ hγ hlr hlrγ (ε₀ := ε) (ε₁ := εV) (ε₂ := ε') hε0 hεV0 hε'0 hϑ0 hϑh0
    hB0 (by positivity) (by positivity) (by positivity) hg hPr hMh hWs hMs hε hBW hBM
    hX.cont hY.cont (A := fun t => P t (Y t)) (C := fun t => -(γ • Y t) - P t (g (X t)))
    hX.deriv hY.deriv (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · have e : P t (Y t) - Y t = -((1 - P t) (Y t)) := by
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [e, norm_neg]
    exact hεV t ht
  · have e : -(γ • Y t) - P t (g (X t)) - (-(γ • Y t) - g (X t)) = (1 - P t) (g (X t)) := by
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [e]
    exact hε' t ht
  · exact ((hP t ht).norm_le _).trans (hYB t ht)
  · refine (norm_sub_le _ _).trans (add_le_add ?_ (hPg t ht))
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left (hYB t ht) hγ

end HeavyBallError
/-! ### Theorem 3 for Algorithm 1 -/

section Algorithm1

open scoped LeanDLRA.Frobenius
open LeanDLRA

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **One step of Algorithm 1 of arXiv 2506.17475**, with truncation errors `ϑ`, `ϑh` and damping
`d`: from `W = U S Vᵀ`, `𝒱 = U S_𝒱 Vᵀ`, build orthonormal `Û ⊇ [U, ∇ℒ(W) V]`,
`V̂ ⊇ [V, ∇ℒ(W)ᵀ U]`, put `S̄ = Ûᵀ W V̂`, `S̄_𝒱 = Ûᵀ 𝒱 V̂`, `G_S = Ûᵀ ∇ℒ(Û S̄ V̂ᵀ) V̂`, then
`Ŝ_𝒱 = d S̄_𝒱 - λ G_S`, `Ŝ = S̄ + λ Ŝ_𝒱`, and truncate to orthonormal `U₁`, `V₁`, with
`S_𝒱₁ = U₁ᵀ Û Ŝ_𝒱 V̂ᵀ V₁`.

The paper prints `d = 1 - γ` in Algorithm 1 and `d = 1 - λ γ` in Eqs. (3a)-(3c).  It
requires `Û ⊇ ∇_U ℒ = ∇ℒ(W) V Sᵀ`, which gives `augGU` for invertible `S`
(`augGU_of_gradU`).  Any `U₁`, `V₁`, `S₁` meeting the error bounds are allowed: the truncated SVD
is not needed.  `‖Û Ŝ V̂ᵀ - U₁ S₁ V₁ᵀ‖ ≤ ϑ` is the truncation tolerance, and `truncMerr` is the
hypothesis `‖Û Ûᵀ 𝒱 V̂ V̂ᵀ - U Uᵀ 𝒱 V Vᵀ‖ ≤ ϑ̂` of Theorem 3. -/
structure IsLRHeavyBallStep {r R R' r₁ : Type*} [Fintype r] [Fintype R] [Fintype R'] [Fintype r₁]
    [DecidableEq r] [DecidableEq R] [DecidableEq R'] [DecidableEq r₁]
    (g : Matrix m n ℝ → Matrix m n ℝ) (lr d ϑ ϑh : ℝ)
    (U : Matrix m r ℝ) (S Sv : Matrix r r ℝ) (V : Matrix n r ℝ)
    (Uh : Matrix m R ℝ) (Vh : Matrix n R' ℝ) (Sh Shv : Matrix R R' ℝ)
    (U₁ : Matrix m r₁ ℝ) (S₁ Sv₁ : Matrix r₁ r₁ ℝ) (V₁ : Matrix n r₁ ℝ) : Prop where
  orthU : Uᵀ * U = 1
  orthV : Vᵀ * V = 1
  orthUh : Uhᵀ * Uh = 1
  orthVh : Vhᵀ * Vh = 1
  orthU₁ : U₁ᵀ * U₁ = 1
  orthV₁ : V₁ᵀ * V₁ = 1
  augU : Uh * Uhᵀ * U = U
  augV : Vh * Vhᵀ * V = V
  augGU : Uh * Uhᵀ * (g (U * S * Vᵀ) * V) = g (U * S * Vᵀ) * V
  augGV : Vh * Vhᵀ * ((g (U * S * Vᵀ))ᵀ * U) = (g (U * S * Vᵀ))ᵀ * U
  momentum : Shv = d • (Uhᵀ * U * Sv * Vᵀ * Vh)
    - lr • (Uhᵀ * g (Uh * (Uhᵀ * U * S * Vᵀ * Vh) * Vhᵀ) * Vh)
  coeff : Sh = Uhᵀ * U * S * Vᵀ * Vh + lr • Shv
  trunc : ‖Uh * Sh * Vhᵀ - U₁ * S₁ * V₁ᵀ‖ ≤ ϑ
  truncM : Sv₁ = U₁ᵀ * Uh * Shv * Vhᵀ * V₁
  truncMerr : ‖Uh * Shv * Vhᵀ - U₁ * Sv₁ * V₁ᵀ‖ ≤ ϑh

/-- The augmentation of Algorithm 1 by `∇_U ℒ = G V Sᵀ` captures `G V` when `S` is invertible, as
the paper states (`Û = ortho(U, ∇_W ℒ V) = ortho(U, ∇_U ℒ)`). -/
theorem augGU_of_gradU {R r : Type*} [Fintype R] [Fintype r] [DecidableEq r] {Uh : Matrix m R ℝ}
    {X : Matrix m r ℝ} {S : Matrix r r ℝ} (hS : IsUnit S.det)
    (h : Uh * Uhᵀ * (X * Sᵀ) = X * Sᵀ) : Uh * Uhᵀ * X = X := by
  have hS' : IsUnit Sᵀ.det := by rwa [Matrix.det_transpose]
  have e : X * Sᵀ * (Sᵀ)⁻¹ = X := Matrix.mul_nonsing_inv_cancel_right _ _ hS'
  calc Uh * Uhᵀ * X = Uh * Uhᵀ * (X * Sᵀ * (Sᵀ)⁻¹) := by rw [e]
    _ = Uh * Uhᵀ * (X * Sᵀ) * (Sᵀ)⁻¹ := by rw [Matrix.mul_assoc (Uh * Uhᵀ) (X * Sᵀ)]
    _ = X := by rw [h, e]

namespace IsLRHeavyBallStep

variable {r R R' r₁ : Type*} [Fintype r] [Fintype R] [Fintype R'] [Fintype r₁]
  [DecidableEq r] [DecidableEq R] [DecidableEq R'] [DecidableEq r₁]
  {g : Matrix m n ℝ → Matrix m n ℝ} {lr d ϑ ϑh : ℝ}
  {U : Matrix m r ℝ} {S Sv : Matrix r r ℝ} {V : Matrix n r ℝ}
  {Uh : Matrix m R ℝ} {Vh : Matrix n R' ℝ} {Sh Shv : Matrix R R' ℝ}
  {U₁ : Matrix m r₁ ℝ} {S₁ Sv₁ : Matrix r₁ r₁ ℝ} {V₁ : Matrix n r₁ ℝ}

/-- Everything of the form `U X Vᵀ` lives in the augmented bases (this includes `W` and `𝒱`). -/
theorem proj_eq (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁)
    (X : Matrix r r ℝ) : Uh * (Uhᵀ * U * X * Vᵀ * Vh) * Vhᵀ = U * X * Vᵀ := by
  have h1 : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose hs.augV
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc Uh * (Uhᵀ * U * X * Vᵀ * Vh) * Vhᵀ = (Uh * Uhᵀ * U) * X * (Vᵀ * (Vh * Vhᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = U * X * Vᵀ := by rw [hs.augU, h1]

/-- The Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` of the step. -/
theorem isOrthProj_galerkin
    (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁) :
    IsOrthProj (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  isOrthProj_leftProj_mul_rightProj hs.orthUh hs.orthVh

/-- The augmented momentum in full space: `𝒱̂ = d 𝒱 - λ Π̂ ∇ℒ(W)`. -/
theorem momentum_eq (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁) :
    Uh * Shv * Vhᵀ = d • (U * Sv * Vᵀ)
      - lr • (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (g (U * S * Vᵀ)) := by
  rw [hs.momentum, hs.proj_eq S]
  simp only [mul_apply_eq_comp, leftProj_rightProj_apply, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hs.proj_eq Sv]

/-- The augmented weight in full space: `Û Ŝ V̂ᵀ = W + λ 𝒱̂`. -/
theorem weight_eq (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁) :
    Uh * Sh * Vhᵀ = U * S * Vᵀ + lr • (Uh * Shv * Vhᵀ) := by
  rw [hs.coeff]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hs.proj_eq S]

/-- Truncating the momentum does not increase its norm. -/
theorem norm_truncM_le (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁) :
    ‖U₁ * Sv₁ * V₁ᵀ‖ ≤ ‖Uh * Shv * Vhᵀ‖ := by
  have e : U₁ * Sv₁ * V₁ᵀ = (leftProj U₁ * rightProj V₁ :
      Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (Uh * Shv * Vhᵀ) := by
    rw [hs.truncM]
    simp only [mul_apply_eq_comp, leftProj_rightProj_apply, Matrix.mul_assoc]
  rw [e]
  exact (isOrthProj_leftProj_mul_rightProj hs.orthU₁ hs.orthV₁).norm_le _

/-- The Galerkin projector of the step captures the tangent part of `∇ℒ(W)`: its defect is at most
the normal component of the gradient at `W`. -/
theorem norm_one_sub_galerkin_le [DecidableEq m] [DecidableEq n]
    (hs : IsLRHeavyBallStep g lr d ϑ ϑh U S Sv V Uh Vh Sh Shv U₁ S₁ Sv₁ V₁) :
    ‖(1 - leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (g (U * S * Vᵀ))‖ ≤
      ‖(1 - U * Uᵀ) * g (U * S * Vᵀ) * (1 - V * Vᵀ)‖ := by
  set Z := g (U * S * Vᵀ) with hZ
  set Pr : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := leftProj Uh * rightProj Vh with hPr
  have hPo : IsOrthProj Pr := hs.isOrthProj_galerkin
  have hgu : Uh * Uhᵀ * (Z * V) = Z * V := hs.augGU
  have hgv : Vh * Vhᵀ * (Zᵀ * U) = Zᵀ * U := hs.augGV
  have hV1 : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    have := congrArg Matrix.transpose hs.augV
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hZ1 : Uᵀ * Z * (Vh * Vhᵀ) = Uᵀ * Z := by
    have := congrArg Matrix.transpose hgv
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using this
  have hfix : Pr (tangentProj U V Z) = tangentProj U V Z := by
    have e : ∀ X : Matrix m n ℝ, Pr X = Uh * Uhᵀ * X * (Vh * Vhᵀ) := fun X => by
      simp [hPr, Matrix.mul_assoc]
    have h1 : Uh * Uhᵀ * (U * Uᵀ * Z) * (Vh * Vhᵀ) = U * Uᵀ * Z := by
      calc _ = (Uh * Uhᵀ * U) * (Uᵀ * Z * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
        _ = U * Uᵀ * Z := by rw [hs.augU, hZ1, Matrix.mul_assoc]
    have h2 : Uh * Uhᵀ * (Z * V * Vᵀ) * (Vh * Vhᵀ) = Z * V * Vᵀ := by
      calc _ = (Uh * Uhᵀ * (Z * V)) * (Vᵀ * (Vh * Vhᵀ)) := by simp only [Matrix.mul_assoc]
        _ = Z * V * Vᵀ := by rw [hgu, hV1]
    have h3 : Uh * Uhᵀ * (U * Uᵀ * Z * V * Vᵀ) * (Vh * Vhᵀ) = U * Uᵀ * Z * V * Vᵀ := by
      calc _ = (Uh * Uhᵀ * U) * (Uᵀ * Z * V) * (Vᵀ * (Vh * Vhᵀ)) := by
            simp only [Matrix.mul_assoc]
        _ = U * Uᵀ * Z * V * Vᵀ := by
            rw [hs.augU, hV1]
            simp only [Matrix.mul_assoc]
    rw [tangentProj_apply, e]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [h1, h2, h3]
  have hsplit := tangentProj_add_normal U V Z
  have e : (1 - Pr) Z = (1 - Pr) ((1 - U * Uᵀ) * Z * (1 - V * Vᵀ)) := by
    conv_lhs => rw [← hsplit]
    rw [map_add]
    have : (1 - Pr) (tangentProj U V Z) = 0 := by
      simp only [sub_apply, one_apply_eq_self, hfix, sub_self]
    rw [this, zero_add]
  rw [e]
  exact hPo.compl.norm_le _

end IsLRHeavyBallStep

variable {r R R' : ℕ → ℕ}

/-- The constant `C` of the `O(λ)` term of `lowRankHeavyBall_error`. -/
noncomputable def hbConst (β γ B BM BX : ℝ) : ℝ :=
  γ * BM + B + (γ * BX + B) + γ * (γ * BX + B) + β * BX

/-- **Theorem 3 of arXiv 2506.17475 (robust error of the low-rank heavy-ball method), corrected.**
Let `(W^k, 𝒱^k)` be `k` steps of Algorithm 1 with step size `λ` and damping `1 - λ γ`, with rank
changing freely, and `(W, 𝒱)` a solution of Eq. (7),
`Ẇ = P 𝒱`, `𝒱̇ + γ 𝒱 = -P ∇ℒ(W)`, for orthogonal projectors `P(t)` (for instance the tangent
projector at `W(t)`).  With `‖∇ℒ‖ ≤ B` along both trajectories, `∇ℒ` `β`-Lipschitz and the normal
components `ε` at `W^k`, `ε'` of the gradient and `εV` of the momentum along the flow,
`‖W^k - W(t_k)‖ ≤ e^{(1 + β) t_k} (δ₀ + t_k (ε + ε' + εV) + t_k C λ + k ϑ + k ϑ̂)`,
`t_k - t₀ = k λ`, with `δ₀` the initial error and `C = hbConst …` depending only on `β`, `γ`, `B`
and on the initial momenta plus `T B`.  Nothing depends on the singular values of `S`, `S_𝒱`.
As `k ϑ = t_k ϑ / λ`, this is `c₀ δ₀ + c₁ ε + c₂ λ + c₃ ϑ / λ + c₄ ϑ̂ / λ`
(`lowRankHeavyBall_error_le`).

**Differences from the paper.**  (1) The damping is `1 - λ γ`.  With the printed `1 - γ` the
claim is false for fixed `γ`: `lowRankHeavyBall_printedDamping_false`.  (2) The term `εV`,
`‖(I - P(W)) 𝒱‖ ≤ εV` along the flow, is added, and the normal component `ε'` along the flow is
stated separately from `ε`.  The paper's proof replaces `Ẇ = P(W) 𝒱` by `Ẇ = 𝒱`, and `εV` cannot
be dropped: `lowRankHeavyBall_needs_normalMomentum`.  Without it the result holds against the
full-rank heavy-ball flow: `lowRankHeavyBall_error_fullFlow`.  (3) `‖∇ℒ‖ ≤ B` is only used along
the two trajectories.  (4) The error constants grow like `e^{(1 + β) T}`, and the proof uses the
discrete Grönwall lemma on `‖ΔW‖ + ‖Δ𝒱‖`, which also gives a bound for the momentum. -/
theorem lowRankHeavyBall_error {g : Matrix m n ℝ → Matrix m n ℝ}
    {β γ lr ε ε' εV ϑ ϑh B t₀ : ℝ} {N : ℕ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hlr : 0 ≤ lr)
    (hlrγ : lr * γ ≤ 1) (hε0 : 0 ≤ ε) (hε'0 : 0 ≤ ε') (hεV0 : 0 ≤ εV) (hϑ0 : 0 ≤ ϑ) (hϑh0 : 0 ≤ ϑh)
    (hB0 : 0 ≤ B) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {U : ∀ k, Matrix m (Fin (r k)) ℝ} {S Sv : ∀ k, Matrix (Fin (r k)) (Fin (r k)) ℝ}
    {V : ∀ k, Matrix n (Fin (r k)) ℝ} {Uh : ∀ k, Matrix m (Fin (R k)) ℝ}
    {Vh : ∀ k, Matrix n (Fin (R' k)) ℝ} {Sh Shv : ∀ k, Matrix (Fin (R k)) (Fin (R' k)) ℝ}
    (hstep : ∀ k < N, IsLRHeavyBallStep g lr (1 - lr * γ) ϑ ϑh (U k) (S k) (Sv k) (V k) (Uh k)
      (Vh k) (Sh k) (Shv k) (U (k + 1)) (S (k + 1)) (Sv (k + 1)) (V (k + 1)))
    [DecidableEq m] [DecidableEq n]
    (hε : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * g (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hBW : ∀ k < N, ‖g (U k * S k * (V k)ᵀ)‖ ≤ B) {X Y : ℝ → Matrix m n ℝ}
    {P : ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    (hP : ∀ t ∈ Ico t₀ (t₀ + N * lr), IsOrthProj (P t))
    (hX : ODESolution (fun t _ => P t (Y t)) X t₀ (t₀ + N * lr))
    (hY : ODESolution (fun t Z => -(γ • Z) - P t (g (X t))) Y t₀ (t₀ + N * lr))
    (hε' : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (g (X t))‖ ≤ ε')
    (hεV : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (Y t)‖ ≤ εV)
    (hBX : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖g (X t)‖ ≤ B) :
    ∀ k ≤ N, ‖U k * S k * (V k)ᵀ - X (t₀ + k * lr)‖ ≤
      Real.exp ((1 + β) * (k * lr)) *
        (‖U 0 * S 0 * (V 0)ᵀ - X t₀‖ + ‖U 0 * Sv 0 * (V 0)ᵀ - Y t₀‖ + k * lr * (ε + εV + ε')
          + k * lr * (hbConst β γ B (‖U 0 * Sv 0 * (V 0)ᵀ‖ + N * lr * B)
            (‖Y t₀‖ + N * lr * B) * lr) + k * ϑ + k * ϑh) := by
  obtain ⟨Wk, hWk⟩ : ∃ Wk : ℕ → Matrix m n ℝ, ∀ k, Wk k = U k * S k * (V k)ᵀ := ⟨_, fun _ => rfl⟩
  obtain ⟨Mk, hMk⟩ : ∃ Mk : ℕ → Matrix m n ℝ, ∀ k, Mk k = U k * Sv k * (V k)ᵀ := ⟨_, fun _ => rfl⟩
  obtain ⟨Mh, hMh⟩ : ∃ Mh : ℕ → Matrix m n ℝ, ∀ k, Mh k = Uh k * Shv k * (Vh k)ᵀ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Pr, hPr⟩ : ∃ Pr : ℕ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ,
      ∀ k, Pr k = leftProj (Uh k) * rightProj (Vh k) := ⟨_, fun _ => rfl⟩
  have h1 : ∀ n < N, IsOrthProj (Pr n) := fun k hk => by
    rw [hPr]
    exact (hstep k hk).isOrthProj_galerkin
  have h2 : ∀ n < N, Mh n = (1 - lr * γ) • Mk n - lr • Pr n (g (Wk n)) := fun k hk => by
    rw [hMh, hMk, hPr, hWk]
    exact (hstep k hk).momentum_eq
  have h3 : ∀ n < N, ‖Wk (n + 1) - (Wk n + lr • Mh n)‖ ≤ ϑ := fun k hk => by
    have hs := hstep k hk
    rw [hWk, hWk, hMh, ← hs.weight_eq, norm_sub_rev]
    exact hs.trunc
  have h4 : ∀ n < N, ‖Mk (n + 1) - Mh n‖ ≤ ϑh := fun k hk => by
    rw [hMk, hMh, norm_sub_rev]
    exact (hstep k hk).truncMerr
  have h5 : ∀ n < N, ‖Mk (n + 1)‖ ≤ ‖Mh n‖ := fun k hk => by
    rw [hMk, hMh]
    exact (hstep k hk).norm_truncM_le
  have h6 : ∀ n < N, ‖(1 - Pr n) (g (Wk n))‖ ≤ ε := fun k hk => by
    rw [hPr, hWk]
    exact (hstep k hk).norm_one_sub_galerkin_le.trans (hε k hk)
  have h7 : ∀ n < N, ‖g (Wk n)‖ ≤ B := fun k hk => by
    rw [hWk]
    exact hBW k hk
  intro k hk
  have h := heavyBall_global_error hβ hγ hlr hlrγ hε0 hε'0 hεV0 hϑ0 hϑh0 hB0 hg h1 h2 h3 h4 h5 h6 h7
    hP hX hY hε' hεV hBX k hk
  rw [← hWk k, ← hWk 0, ← hMk 0]
  have h8 := le_add_of_nonneg_right (a := ‖Wk k - X (t₀ + k * lr)‖)
    (norm_nonneg (Mk k - Y (t₀ + k * lr)))
  refine h8.trans (h.trans (le_of_eq ?_))
  simp only [hbLocal, hbConst]
  ring

/-- Numerical form of Theorem 3: `e^{L k λ} (δ₀ + k λ E + k λ C λ + k ϑ + k ϑ̂)` with `k λ ≤ T` is
at most `c₀ δ₀ + c₁ E + c₂ λ + c₃ ϑ / λ + c₄ ϑ̂ / λ`, with constants independent of `k`, `λ`. -/
theorem heavyBall_bound_le {L T lr δ₀ E C ϑ ϑh : ℝ} {k : ℕ} (hL : 0 ≤ L) (hlr : 0 < lr)
    (hk : k * lr ≤ T) (hδ₀ : 0 ≤ δ₀) (hE : 0 ≤ E) (hC : 0 ≤ C) (hϑ : 0 ≤ ϑ) (hϑh : 0 ≤ ϑh) :
    Real.exp (L * (k * lr)) * (δ₀ + k * lr * E + k * lr * (C * lr) + k * ϑ + k * ϑh) ≤
      Real.exp (L * T) * δ₀ + T * Real.exp (L * T) * E + T * C * Real.exp (L * T) * lr
        + T * Real.exp (L * T) * (ϑ / lr) + T * Real.exp (L * T) * (ϑh / lr) := by
  have hk0 : 0 ≤ (k : ℝ) * lr := by positivity
  have hexp : Real.exp (L * (k * lr)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hk hL)
  have e1 : (k : ℝ) * ϑ = k * lr * (ϑ / lr) := by field_simp
  have e2 : (k : ℝ) * ϑh = k * lr * (ϑh / lr) := by field_simp
  have hq1 : 0 ≤ ϑ / lr := by positivity
  have hq2 : 0 ≤ ϑh / lr := by positivity
  have hsum : δ₀ + k * lr * E + k * lr * (C * lr) + k * ϑ + k * ϑh ≤
      δ₀ + T * E + T * (C * lr) + T * (ϑ / lr) + T * (ϑh / lr) := by
    rw [e1, e2]
    gcongr
  have hT : 0 ≤ T := hk0.trans hk
  have h1 : 0 ≤ δ₀ + T * E + T * (C * lr) + T * (ϑ / lr) + T * (ϑh / lr) := by positivity
  calc _ ≤ Real.exp (L * T) * (δ₀ + T * E + T * (C * lr) + T * (ϑ / lr) + T * (ϑh / lr)) := by
        gcongr
    _ = _ := by ring

/-- **Theorem 3 of arXiv 2506.17475 in the paper's form**: under the hypotheses of
`lowRankHeavyBall_error`, for `t_k - t₀ = k λ ≤ T = N λ`,
`‖W(t_k) - W^k‖ ≤ c₀ δ₀ + c₁ (ε + εV + ε') + c₂ λ + c₃ ϑ / λ + c₄ ϑ̂ / λ`, with
`c₀ = e^{(1 + β) T}`, `c₁ = c₃ = c₄ = T c₀` and `c₂ = T C c₀`, `C = hbConst …`.  The constants
depend on `β`, `γ`, `B`, `T` and the initial momenta, not on singular values, `k` or `λ`. -/
theorem lowRankHeavyBall_error_le {g : Matrix m n ℝ → Matrix m n ℝ}
    {β γ lr ε ε' εV ϑ ϑh B t₀ : ℝ} {N : ℕ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hlr : 0 < lr)
    (hlrγ : lr * γ ≤ 1) (hε0 : 0 ≤ ε) (hε'0 : 0 ≤ ε') (hεV0 : 0 ≤ εV) (hϑ0 : 0 ≤ ϑ) (hϑh0 : 0 ≤ ϑh)
    (hB0 : 0 ≤ B) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {U : ∀ k, Matrix m (Fin (r k)) ℝ} {S Sv : ∀ k, Matrix (Fin (r k)) (Fin (r k)) ℝ}
    {V : ∀ k, Matrix n (Fin (r k)) ℝ} {Uh : ∀ k, Matrix m (Fin (R k)) ℝ}
    {Vh : ∀ k, Matrix n (Fin (R' k)) ℝ} {Sh Shv : ∀ k, Matrix (Fin (R k)) (Fin (R' k)) ℝ}
    (hstep : ∀ k < N, IsLRHeavyBallStep g lr (1 - lr * γ) ϑ ϑh (U k) (S k) (Sv k) (V k) (Uh k)
      (Vh k) (Sh k) (Shv k) (U (k + 1)) (S (k + 1)) (Sv (k + 1)) (V (k + 1)))
    [DecidableEq m] [DecidableEq n]
    (hε : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * g (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hBW : ∀ k < N, ‖g (U k * S k * (V k)ᵀ)‖ ≤ B) {X Y : ℝ → Matrix m n ℝ}
    {P : ℝ → Matrix m n ℝ →L[ℝ] Matrix m n ℝ}
    (hP : ∀ t ∈ Ico t₀ (t₀ + N * lr), IsOrthProj (P t))
    (hX : ODESolution (fun t _ => P t (Y t)) X t₀ (t₀ + N * lr))
    (hY : ODESolution (fun t Z => -(γ • Z) - P t (g (X t))) Y t₀ (t₀ + N * lr))
    (hε' : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (g (X t))‖ ≤ ε')
    (hεV : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖(1 - P t) (Y t)‖ ≤ εV)
    (hBX : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖g (X t)‖ ≤ B) :
    ∀ k ≤ N, ‖U k * S k * (V k)ᵀ - X (t₀ + k * lr)‖ ≤
      Real.exp ((1 + β) * (N * lr)) *
          (‖U 0 * S 0 * (V 0)ᵀ - X t₀‖ + ‖U 0 * Sv 0 * (V 0)ᵀ - Y t₀‖)
        + (N * lr) * Real.exp ((1 + β) * (N * lr)) * (ε + εV + ε')
        + (N * lr) * hbConst β γ B (‖U 0 * Sv 0 * (V 0)ᵀ‖ + N * lr * B) (‖Y t₀‖ + N * lr * B)
          * Real.exp ((1 + β) * (N * lr)) * lr
        + (N * lr) * Real.exp ((1 + β) * (N * lr)) * (ϑ / lr)
        + (N * lr) * Real.exp ((1 + β) * (N * lr)) * (ϑh / lr) := by
  intro k hk
  have h := lowRankHeavyBall_error hβ hγ hlr.le hlrγ hε0 hε'0 hεV0 hϑ0 hϑh0 hB0 hg hstep hε hBW hP
    hX hY hε' hεV hBX k hk
  have hkN : (k : ℝ) * lr ≤ N * lr := by
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    gcongr
  refine h.trans (heavyBall_bound_le (by linarith) hlr hkN (by positivity) (by positivity) ?_ hϑ0
    hϑh0)
  unfold hbConst
  positivity

/-- **Theorem 3 of arXiv 2506.17475 against the full-rank flow.**  The paper reads Theorem 3 as:
"the low-rank momentum method produces solutions that are close to the solutions of full-rank
(baseline) trained neural networks".  This version holds without the extra term `εV`:
`W^k` of Algorithm 1 (with damping `1 - λ γ`) tracks `Ẇ = 𝒱`, `𝒱̇ + γ 𝒱 = -∇ℒ(W)`
(Eq. (6)), with the bound of `lowRankHeavyBall_error` for `ε' = εV = 0`. -/
theorem lowRankHeavyBall_error_fullFlow {g : Matrix m n ℝ → Matrix m n ℝ}
    {β γ lr ε ϑ ϑh B t₀ : ℝ} {N : ℕ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hlr : 0 ≤ lr)
    (hlrγ : lr * γ ≤ 1) (hε0 : 0 ≤ ε) (hϑ0 : 0 ≤ ϑ) (hϑh0 : 0 ≤ ϑh)
    (hB0 : 0 ≤ B) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {U : ∀ k, Matrix m (Fin (r k)) ℝ} {S Sv : ∀ k, Matrix (Fin (r k)) (Fin (r k)) ℝ}
    {V : ∀ k, Matrix n (Fin (r k)) ℝ} {Uh : ∀ k, Matrix m (Fin (R k)) ℝ}
    {Vh : ∀ k, Matrix n (Fin (R' k)) ℝ} {Sh Shv : ∀ k, Matrix (Fin (R k)) (Fin (R' k)) ℝ}
    (hstep : ∀ k < N, IsLRHeavyBallStep g lr (1 - lr * γ) ϑ ϑh (U k) (S k) (Sv k) (V k) (Uh k)
      (Vh k) (Sh k) (Shv k) (U (k + 1)) (S (k + 1)) (Sv (k + 1)) (V (k + 1)))
    [DecidableEq m] [DecidableEq n]
    (hε : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * g (U k * S k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hBW : ∀ k < N, ‖g (U k * S k * (V k)ᵀ)‖ ≤ B) {X Y : ℝ → Matrix m n ℝ}
    (hX : ODESolution (fun t _ => Y t) X t₀ (t₀ + N * lr))
    (hY : ODESolution (fun t Z => -(γ • Z) - g (X t)) Y t₀ (t₀ + N * lr))
    (hBX : ∀ t ∈ Ico t₀ (t₀ + N * lr), ‖g (X t)‖ ≤ B) :
    ∀ k ≤ N, ‖U k * S k * (V k)ᵀ - X (t₀ + k * lr)‖ ≤
      Real.exp ((1 + β) * (k * lr)) *
        (‖U 0 * S 0 * (V 0)ᵀ - X t₀‖ + ‖U 0 * Sv 0 * (V 0)ᵀ - Y t₀‖ + k * lr * (ε + 0 + 0)
          + k * lr * (hbConst β γ B (‖U 0 * Sv 0 * (V 0)ᵀ‖ + N * lr * B)
            (‖Y t₀‖ + N * lr * B) * lr) + k * ϑ + k * ϑh) := by
  refine lowRankHeavyBall_error (P := fun _ => 1) hβ hγ hlr hlrγ hε0 le_rfl le_rfl hϑ0 hϑh0 hB0 hg
    hstep hε hBW (fun _ _ => IsOrthProj.one) ?_ ?_ (fun t _ => by simp) (fun t _ => by simp) hBX
  · exact ⟨hX.cont, fun t ht => by simpa using hX.deriv t ht⟩
  · exact ⟨hY.cont, fun t ht => by simpa using hY.deriv t ht⟩

end Algorithm1
/-! ### Theorem 3: the statement of the paper fails -/

section Theorem3Counterexamples

open scoped LeanDLRA.Frobenius
open LeanDLRA

/-- **Theorem 3 of arXiv 2506.17475 is false for Algorithm 1 as printed.**  Algorithm 1 (line 7)
and the derivation before it print the damping `1 - γ`, whereas the Euler step of the flow has
`1 - λ γ` (Eqs. (3a)-(3c)); here `γ` is read as the `γ` of Eq. (7), as the paper's notation
does.  Take
`m = n = r = 1`, `ℒ = 0`, `γ = 1`.  The solution of Eq. (7) with `W(0) = 𝒱(0) = 1` is
`W(t) = 2 - e^{-t}`, `𝒱(t) = e^{-t}`.  For every `k > 0` Algorithm 1 with `λ = 1 / k` and without
any truncation (`ϑ = ϑ̂ = 0`, and `ε = 0`) gives `W^k = 1`, so `‖W(1) - W^k‖ ≥ 1/2`, while the
claimed bound `c₁ ε + c₂ λ + c₃ ϑ / λ + c₄ ϑ̂ / λ = c₂ / k` tends to zero. -/
theorem lowRankHeavyBall_printedDamping_false :
    ∃ X Y : ℝ → Matrix (Fin 1) (Fin 1) ℝ, X 0 = 1 ∧ Y 0 = 1 ∧
      (∀ t, HasDerivAt X (tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (Y t)) t) ∧
      (∀ t, HasDerivAt Y (-((1 : ℝ) • Y t) - tangentProj (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)) t) ∧
      ∀ k : ℕ, 0 < k → ∃ U V Uh Vh S Sv Sh Shv : ℕ → Matrix (Fin 1) (Fin 1) ℝ,
        (∀ j < k, IsLRHeavyBallStep (fun _ => 0) (1 / (k : ℝ)) (1 - 1) 0 0 (U j) (S j) (Sv j) (V j)
          (Uh j) (Vh j) (Sh j) (Shv j) (U (j + 1)) (S (j + 1)) (Sv (j + 1)) (V (j + 1))) ∧
        U 0 * S 0 * (V 0)ᵀ = X 0 ∧ U 0 * Sv 0 * (V 0)ᵀ = Y 0 ∧
        1 / 2 ≤ ‖X 1 - U k * S k * (V k)ᵀ‖ := by
  have hE : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := fun t => by
    simpa using ((hasDerivAt_id t).neg).exp
  refine ⟨fun t => (2 - Real.exp (-t)) • 1, fun t => Real.exp (-t) • 1, ?_, ?_, fun t => ?_,
    fun t => ?_, fun k _ => ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1,
      fun j => if j = 0 then 1 else 0, fun _ => 1, fun _ => 0, fun j _ => ?_, ?_, ?_, ?_⟩⟩
  · ext i j
    fin_cases i; fin_cases j
    norm_num
  · simp
  · rw [tangentProj_one_one]
    have := ((hE t).const_sub 2).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)
    simpa using this
  · rw [tangentProj_one_one]
    have := (hE t).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)
    simpa using this
  · refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp⟩
  · norm_num
  · simp
  · have h1 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have h2 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    rw [norm_one_by_one]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [one_div, Matrix.one_apply_eq, mul_one, Matrix.transpose_one, Fin.isValue, ge_iff_le]
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The linear gradient `Z ↦ a (E Z + Z E)`, `E = e₁ e₁ᵀ`, of `linLoss`. -/
noncomputable def linGrad (a : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  a • (E₂ 0 0 * Z + Z * E₂ 0 0)

/-- The convex quadratic loss `ℒ(Z) = a (Z₀₀² + Z₀₁²/2 + Z₁₀²/2)`. -/
noncomputable def linLoss (a : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  a * ((Z 0 0) ^ 2 + (Z 0 1) ^ 2 / 2 + (Z 1 0) ^ 2 / 2)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `linGrad`. -/
theorem linGrad_apply (a : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    linGrad a Z = !![2 * a * Z 0 0, a * Z 0 1; a * Z 1 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | (simp [linGrad, E₂, Matrix.mul_apply, Matrix.single_apply]; done)
    | (simp [linGrad, E₂, Matrix.mul_apply, Matrix.single_apply]; ring)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `linGrad` is linear. -/
theorem linGrad_sub (a : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    linGrad a X - linGrad a Y = linGrad a (X - Y) := by
  simp only [linGrad, Matrix.mul_sub, Matrix.sub_mul]
  module

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `linGrad` has linear growth `2 a`. -/
theorem norm_linGrad_le {a : ℝ} (ha : 0 ≤ a) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖linGrad a Z‖ ≤ 2 * a * ‖Z‖ := by
  have e1 : ‖linGrad a Z‖ ^ 2 = (2 * a * Z 0 0) ^ 2 + (a * Z 0 1) ^ 2 + (a * Z 1 0) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, linGrad_apply]
    simp [Fin.sum_univ_two]
  have e2 : ‖Z‖ ^ 2 = (Z 0 0) ^ 2 + (Z 0 1) ^ 2 + (Z 1 0) ^ 2 + (Z 1 1) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  have key : ‖linGrad a Z‖ ^ 2 ≤ (2 * a * ‖Z‖) ^ 2 := by
    rw [mul_pow, e1, e2]
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (Z 0 1)),
      mul_nonneg (sq_nonneg a) (sq_nonneg (Z 1 0)), mul_nonneg (sq_nonneg a) (sq_nonneg (Z 1 1))]
  exact (abs_le_of_sq_le_sq' key (by positivity)).2

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `linGrad` is the gradient of `linLoss`. -/
theorem hasFDerivAt_linLoss (a : ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ) :
    HasFDerivAt (linLoss a) (innerSL ℝ (linGrad a W)) W := by
  have h1 : HasDerivAt (fun y : ℝ => a * y ^ 2) (2 * a * W 0 0) (W 0 0) := by
    have := (hasDerivAt_pow 2 (W 0 0)).const_mul a
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => a * (y ^ 2 / 2)) (a * y) y := fun y => by
    have := ((hasDerivAt_pow 2 y).div_const 2).const_mul a
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h := ((h1.comp_hasFDerivAt W (hasFDerivAt_entry 0 0 W)).add
    ((h2 (W 0 1)).comp_hasFDerivAt W (hasFDerivAt_entry 0 1 W))).add
    ((h2 (W 1 0)).comp_hasFDerivAt W (hasFDerivAt_entry 1 0 W))
  have e : linLoss a = fun Z : Matrix (Fin 2) (Fin 2) ℝ => a * (Z 0 0) ^ 2 + a * ((Z 0 1) ^ 2 / 2)
      + a * ((Z 1 0) ^ 2 / 2) := by
    funext Z
    simp only [linLoss]
    ring
  rw [e]
  refine h.congr_fderiv ?_
  ext1 X
  have e2 : linGrad a W = (2 * a * W 0 0) • E₂ 0 0 + (a * W 0 1) • E₂ 0 1
      + (a * W 1 0) • E₂ 1 0 := by
    rw [linGrad_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E₂]
  rw [e2]
  simp [innerSL_apply_apply, inner_E₂]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `linLoss` is nonnegative. -/
theorem linLoss_nonneg {a : ℝ} (ha : 0 ≤ a) (Z : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ linLoss a Z := by
  unfold linLoss
  positivity

/-- At `Z = U S Vᵀ` of any rank, `∇ℒ(Z)` has no normal component: `ε = 0` in Theorem 3. -/
theorem linGrad_normal {r : Type*} [Fintype r] [DecidableEq r] (a : ℝ) {U : Matrix (Fin 2) r ℝ}
    {V : Matrix (Fin 2) r ℝ} (S : Matrix r r ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (1 - U * Uᵀ) * linGrad a (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
  have h1 : (1 - U * Uᵀ) * (U * S * Vᵀ) = 0 := by
    have : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
      rw [Matrix.mul_assoc U Uᵀ, Matrix.mul_assoc U S, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, this, sub_self]
  have h2 : (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
    have : (U * S * Vᵀ) * (V * Vᵀ) = U * S * Vᵀ := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (U * S) Vᵀ V, hV, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  have key : ∀ Z P Q E : Matrix (Fin 2) (Fin 2) ℝ, P * Z = 0 → Z * Q = 0 →
      P * (a • (E * Z + Z * E)) * Q = 0 := by
    intro Z P Q E h1 h2
    have : P * (a • (E * Z + Z * E)) * Q = a • (P * (E * (Z * Q)) + (P * Z) * (E * Q)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [this, h1, h2]
    simp
  exact key _ _ _ _ h1 h2

/-- The unit vector `u(θ) = (cos θ, sin θ)ᵀ`. -/
noncomputable def uu (θ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := Real.cos θ • e₁ + Real.sin θ • e₂

/-- The unit vector `u⊥(θ) = (-sin θ, cos θ)ᵀ`. -/
noncomputable def up (θ : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := (-Real.sin θ) • e₁ + Real.cos θ • e₂

/-- `u uᵀ`. -/
noncomputable def EU (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := uu θ * (uu θ)ᵀ

/-- `u⊥ u⊥ᵀ`, the normal direction at `s u uᵀ`. -/
noncomputable def EN (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := up θ * (up θ)ᵀ

/-- `u⊥ uᵀ + u u⊥ᵀ`. -/
noncomputable def AA (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := up θ * (uu θ)ᵀ + uu θ * (up θ)ᵀ

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `u` has norm one. -/
theorem uu_orth (θ : ℝ) : (uu θ)ᵀ * uu θ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [uu, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sq_add_sin_sq, ← sq]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `u⊥` has norm one. -/
theorem up_orth (θ : ℝ) : (up θ)ᵀ * up θ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [up, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two, Real.sin_sq_add_cos_sq, ← sq]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `uᵀ u⊥ = 0`. -/
theorem uu_up (θ : ℝ) : (uu θ)ᵀ * up θ = 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [uu, up, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `u⊥ᵀ u = 0`. -/
theorem up_uu (θ : ℝ) : (up θ)ᵀ * uu θ = 0 := by
  have := congrArg Matrix.transpose (uu_up θ)
  simpa [Matrix.transpose_mul] using this

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `P(u uᵀ)` fixes `u⊥ uᵀ + u u⊥ᵀ`. -/
theorem tangentProj_AA (θ : ℝ) : tangentProj (uu θ) (uu θ) (AA θ) = AA θ := by
  rw [AA, map_add, tangentProj_mul_transpose _ (uu_orth θ), tangentProj_mul_left (uu_orth θ)]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `P(u uᵀ)` fixes `u uᵀ`. -/
theorem tangentProj_EU (θ : ℝ) : tangentProj (uu θ) (uu θ) (EU θ) = EU θ :=
  tangentProj_mul_left (uu_orth θ) _ _

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `P(u uᵀ)` kills the normal direction `u⊥ u⊥ᵀ`. -/
theorem tangentProj_EN (θ : ℝ) : tangentProj (uu θ) (uu θ) (EN θ) = 0 := by
  have h1 : uu θ * (uu θ)ᵀ * EN θ = 0 := by
    rw [EN, Matrix.mul_assoc, ← Matrix.mul_assoc (uu θ)ᵀ, uu_up]
    simp
  have h2 : EN θ * uu θ * (uu θ)ᵀ = 0 := by
    rw [EN, Matrix.mul_assoc (up θ), up_uu]
    simp
  rw [tangentProj_apply, h1, h2]
  simp

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `EU`. -/
theorem EU_apply (θ : ℝ) : EU θ = !![Real.cos θ ^ 2, Real.cos θ * Real.sin θ;
    Real.cos θ * Real.sin θ, Real.sin θ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [EU, uu, e₁, e₂, Matrix.mul_apply, sq, mul_comm]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `EN`. -/
theorem EN_apply (θ : ℝ) : EN θ = !![Real.sin θ ^ 2, -(Real.cos θ * Real.sin θ);
    -(Real.cos θ * Real.sin θ), Real.cos θ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [EN, up, e₁, e₂, Matrix.mul_apply, sq, mul_comm]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `u⊥ uᵀ`. -/
theorem up_mul_uu (θ : ℝ) : up θ * (uu θ)ᵀ = !![-(Real.cos θ * Real.sin θ), -Real.sin θ ^ 2;
    Real.cos θ ^ 2, Real.cos θ * Real.sin θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uu, up, e₁, e₂, Matrix.mul_apply, sq, mul_comm]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `AA`. -/
theorem AA_apply (θ : ℝ) : AA θ = !![-(2 * Real.cos θ * Real.sin θ),
    Real.cos θ ^ 2 - Real.sin θ ^ 2; Real.cos θ ^ 2 - Real.sin θ ^ 2,
    2 * Real.cos θ * Real.sin θ] := by
  have h : uu θ * (up θ)ᵀ = (up θ * (uu θ)ᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [AA, h, up_mul_uu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | (simp; done)
    | (simp; ring)

/-- The gradient at the rank-one point `s u uᵀ`, in the frame of `u`. -/
theorem linGrad_EU (a s θ : ℝ) : linGrad a (s • EU θ) =
    (2 * a * s * Real.cos θ ^ 2) • EU θ - (a * s * Real.cos θ * Real.sin θ) • AA θ := by
  have hcs := Real.cos_sq_add_sin_sq θ
  rw [linGrad_apply, EU_apply, AA_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.smul_apply, Matrix.sub_apply]
    simp
    linear_combination (-(2 * a * s * Real.cos θ ^ 2)) * hcs
  · simp
    linear_combination (-(a * s * Real.cos θ * Real.sin θ)) * hcs
  · simp
    linear_combination (-(a * s * Real.cos θ * Real.sin θ)) * hcs
  · simp
    ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `u̇ = θ̇ u⊥`. -/
theorem hasDerivAt_uu {θ : ℝ → ℝ} {w t : ℝ} (h : HasDerivAt θ w t) :
    HasDerivAt (fun t => uu (θ t)) (w • up (θ t)) t := by
  have h1 := (h.cos.smul_const e₁).add (h.sin.smul_const e₂)
  refine h1.congr_deriv ?_
  simp only [up, smul_add, smul_smul]
  congr 2 <;> ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `u̇⊥ = -θ̇ u`. -/
theorem hasDerivAt_up {θ : ℝ → ℝ} {w t : ℝ} (h : HasDerivAt θ w t) :
    HasDerivAt (fun t => up (θ t)) ((-w) • uu (θ t)) t := by
  have h1 := ((h.sin.neg).smul_const e₁).add (h.cos.smul_const e₂)
  refine h1.congr_deriv ?_
  simp only [uu, smul_add, smul_smul]
  congr 2 <;> ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the derivative of `EU`. -/
theorem hasDerivAt_EU {θ : ℝ → ℝ} {w t : ℝ} (h : HasDerivAt θ w t) :
    HasDerivAt (fun t => EU (θ t)) (w • AA (θ t)) t := by
  have hu := hasDerivAt_uu h
  refine (GaugeODE.hasDerivAt_mul hu (GaugeODE.hasDerivAt_transpose hu)).congr_deriv ?_
  simp only [AA, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, smul_add]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the derivative of `EN`. -/
theorem hasDerivAt_EN {θ : ℝ → ℝ} {w t : ℝ} (h : HasDerivAt θ w t) :
    HasDerivAt (fun t => EN (θ t)) ((-w) • AA (θ t)) t := by
  have hu := hasDerivAt_up h
  refine (GaugeODE.hasDerivAt_mul hu (GaugeODE.hasDerivAt_transpose hu)).congr_deriv ?_
  simp only [AA, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, smul_add]
  abel

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the derivative of `AA`. -/
theorem hasDerivAt_AA {θ : ℝ → ℝ} {w t : ℝ} (h : HasDerivAt θ w t) :
    HasDerivAt (fun t => AA (θ t)) ((2 * w) • (EN (θ t) - EU (θ t))) t := by
  have hu := hasDerivAt_uu h
  have hv := hasDerivAt_up h
  refine ((GaugeODE.hasDerivAt_mul hv (GaugeODE.hasDerivAt_transpose hu)).add
    (GaugeODE.hasDerivAt_mul hu (GaugeODE.hasDerivAt_transpose hv))).congr_deriv ?_
  simp only [EN, EU, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul]
  module

/-- **The projected heavy-ball flow in the frame `u, u⊥`.**  If `s, θ, p, m, n` satisfy the five
scalar equations below at `t`, then `X = s u uᵀ`, `Y = p (u⊥ uᵀ + u u⊥ᵀ) + m u uᵀ + n u⊥ u⊥ᵀ`
satisfy `Ẋ = P(X) Y`, `Ẏ + γ Y = -P(X) ∇ℒ(X)` for `ℒ = linLoss a`.  The curvature terms `2 p² / s`
feed the normal part `n` of the momentum. -/
theorem constrained_hasDerivAt {s θ p m n : ℝ → ℝ} {a γ t : ℝ} (hs0 : s t ≠ 0)
    (hs : HasDerivAt s (m t) t) (hθ : HasDerivAt θ (p t / s t) t)
    (hp : HasDerivAt p (-γ * p t + a * s t * Real.cos (θ t) * Real.sin (θ t)
      - (m t - n t) * p t / s t) t)
    (hm : HasDerivAt m (-γ * m t - 2 * a * s t * Real.cos (θ t) ^ 2 + 2 * p t ^ 2 / s t) t)
    (hn : HasDerivAt n (-γ * n t - 2 * p t ^ 2 / s t) t) :
    HasDerivAt (fun t => s t • EU (θ t)) (tangentProj (uu (θ t)) (uu (θ t))
      (p t • AA (θ t) + m t • EU (θ t) + n t • EN (θ t))) t ∧
    HasDerivAt (fun t => p t • AA (θ t) + m t • EU (θ t) + n t • EN (θ t))
      (-(γ • (p t • AA (θ t) + m t • EU (θ t) + n t • EN (θ t)))
        - tangentProj (uu (θ t)) (uu (θ t)) (linGrad a (s t • EU (θ t)))) t := by
  have hA := hasDerivAt_AA hθ
  have hE := hasDerivAt_EU hθ
  have hN := hasDerivAt_EN hθ
  constructor
  · refine (hs.smul hE).congr_deriv ?_
    rw [map_add, map_add, map_smul, map_smul, map_smul, tangentProj_AA, tangentProj_EU,
      tangentProj_EN, smul_zero, add_zero, smul_smul, mul_div_cancel₀ _ hs0]
  · refine (((hp.smul hA).add (hm.smul hE)).add (hn.smul hN)).congr_deriv ?_
    rw [linGrad_EU, map_sub, map_smul, map_smul, tangentProj_AA, tangentProj_EU]
    set w := p t / s t with hw
    have e1 : (2 * p t ^ 2 / s t) = 2 * p t * w := by rw [hw]; ring
    have e2 : (m t - n t) * p t / s t = (m t - n t) * w := by rw [hw]; ring
    rw [e1, e2]
    simp only [smul_sub, smul_add, smul_smul]
    module

/-- Damped oscillator solution `φ(t) = e^{-γ t/2} (cos ω t + γ/(2ω) sin ω t)`, `φ(0) = 1`,
`φ̇(0) = 0`, of `φ̈ + γ φ̇ + (ω² + γ²/4) φ = 0`. -/
noncomputable def phi (γ ω t : ℝ) : ℝ :=
  Real.exp (-γ / 2 * t) * (Real.cos (ω * t) + γ / (2 * ω) * Real.sin (ω * t))

/-- The derivative of `phi`. -/
noncomputable def psi (γ ω t : ℝ) : ℝ :=
  -((ω ^ 2 + γ ^ 2 / 4) / ω) * Real.exp (-γ / 2 * t) * Real.sin (ω * t)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the derivative of `t ↦ e^{c t}`. -/
theorem hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun t => Real.exp (c * t)) (c * Real.exp (c * t)) t := by
  have h : HasDerivAt (fun t => c * t) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  exact h.exp.congr_deriv (by ring)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `psi` is the derivative of `phi`. -/
theorem hasDerivAt_phi (γ : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (phi γ ω) (psi γ ω t) t := by
  have hl : HasDerivAt (fun t => ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h := (hasDerivAt_exp_mul (-γ / 2) t).mul
    (hl.cos.add (hl.sin.const_mul (γ / (2 * ω))))
  refine h.congr_deriv ?_
  simp only [psi, Pi.add_apply]
  field_simp
  ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the oscillator equation for `phi`. -/
theorem hasDerivAt_psi (γ : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (psi γ ω) (-γ * psi γ ω t - (ω ^ 2 + γ ^ 2 / 4) * phi γ ω t) t := by
  have hl : HasDerivAt (fun t => ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h := ((hasDerivAt_exp_mul (-γ / 2) t).const_mul (-((ω ^ 2 + γ ^ 2 / 4) / ω))).mul hl.sin
  refine h.congr_deriv ?_
  simp only [psi, phi]
  field_simp
  ring

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `φ(0) = 1`. -/
theorem phi_zero (γ ω : ℝ) : phi γ ω 0 = 1 := by simp [phi]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `φ̇(0) = 0`. -/
theorem psi_zero (γ ω : ℝ) : psi γ ω 0 = 0 := by simp [psi]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the first component of a curve in a product. -/
theorem hasDerivAt_prod_fst {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {f : ℝ → F₁ × F₂} {v : F₁ × F₂} {t : ℝ}
    (h : HasDerivAt f v t) : HasDerivAt (fun t => (f t).1) v.1 t :=
  (ContinuousLinearMap.fst ℝ F₁ F₂).hasFDerivAt.comp_hasDerivAt t h

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the second component of a curve in a product. -/
theorem hasDerivAt_prod_snd {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {f : ℝ → F₁ × F₂} {v : F₁ × F₂} {t : ℝ}
    (h : HasDerivAt f v t) : HasDerivAt (fun t => (f t).2) v.2 t :=
  (ContinuousLinearMap.snd ℝ F₁ F₂).hasFDerivAt.comp_hasDerivAt t h

/-- The vector field of the five scalar equations of `constrained_hasDerivAt`. -/
noncomputable def cField (γ a : ℝ) (z : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  (z.2.2.2.1, z.2.2.1 / z.1,
    -γ * z.2.2.1 + a * z.1 * Real.cos z.2.1 * Real.sin z.2.1
      - (z.2.2.2.1 - z.2.2.2.2) * z.2.2.1 / z.1,
    -γ * z.2.2.2.1 - 2 * a * z.1 * Real.cos z.2.1 ^ 2 + 2 * z.2.2.1 ^ 2 / z.1,
    -γ * z.2.2.2.2 - 2 * z.2.2.1 ^ 2 / z.1)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `cField` is `C¹` where `s ≠ 0`. -/
theorem contDiffAt_cField (γ a : ℝ) {z : ℝ × ℝ × ℝ × ℝ × ℝ} (hz : z.1 ≠ 0) :
    ContDiffAt ℝ 1 (cField γ a) z := by
  unfold cField
  fun_prop (disch := assumption)

/-- Local solution of the five scalar equations, from `s = 2`, `θ = π/4` and zero momentum. -/
theorem exists_constrained (γ a : ℝ) : ∃ (T₀ : ℝ) (s θ p m n : ℝ → ℝ), 0 < T₀ ∧ s 0 = 2 ∧
    θ 0 = Real.pi / 4 ∧ p 0 = 0 ∧ m 0 = 0 ∧ n 0 = 0 ∧ ∀ t ∈ Ioo (-T₀) T₀, 0 < s t ∧
      HasDerivAt s (m t) t ∧ HasDerivAt θ (p t / s t) t ∧
      HasDerivAt p (-γ * p t + a * s t * Real.cos (θ t) * Real.sin (θ t)
        - (m t - n t) * p t / s t) t ∧
      HasDerivAt m (-γ * m t - 2 * a * s t * Real.cos (θ t) ^ 2 + 2 * p t ^ 2 / s t) t ∧
      HasDerivAt n (-γ * n t - 2 * p t ^ 2 / s t) t := by
  obtain ⟨α, hα0, ε, hε, hα⟩ := (contDiffAt_cField γ a
    (z := (2, Real.pi / 4, 0, 0, 0)) (by norm_num)
    ).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hc0 : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  have hs0 : ContinuousAt (fun t => (α t).1) 0 := (hasDerivAt_prod_fst (hα 0 hc0)).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (α t).1 :=
    Filter.Tendsto.eventually_const_lt (by change 0 < (α 0).1; rw [hα0]; norm_num) hs0
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ t ∈ Ioo (-(min ε δ)) (min ε δ), t ∈ Ioo (0 - ε) (0 + ε) ∧ 0 < (α t).1 := by
    intro t ht
    have h1 : min ε δ ≤ ε := min_le_left _ _
    have h2 : min ε δ ≤ δ := min_le_right _ _
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨min ε δ, fun t => (α t).1, fun t => (α t).2.1, fun t => (α t).2.2.1,
    fun t => (α t).2.2.2.1, fun t => (α t).2.2.2.2, lt_min hε hδ, by simp [hα0], by simp [hα0],
    by simp [hα0], by simp [hα0], by simp [hα0], fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hmem t ht
  have h := hα t h1
  have h3 := hasDerivAt_prod_snd h
  have h4 := hasDerivAt_prod_snd h3
  have h5 := hasDerivAt_prod_snd h4
  exact ⟨h2, hasDerivAt_prod_fst h, hasDerivAt_prod_fst h3, hasDerivAt_prod_fst h4,
    hasDerivAt_prod_fst h5, hasDerivAt_prod_snd h5⟩

/-- The solution of the full-rank flow for `linLoss` from `W(0) = (1 1; 1 1)`, `𝒱(0) = 0`. -/
noncomputable def wFull (γ ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  phi γ ω t • E₂ 0 0 + phi γ 1 t • (E₂ 0 1 + E₂ 1 0) + E₂ 1 1

/-- The momentum of the full-rank flow for `linLoss`. -/
noncomputable def mFull (γ ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  psi γ ω t • E₂ 0 0 + psi γ 1 t • (E₂ 0 1 + E₂ 1 0)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the gradient along the full-rank flow. -/
theorem linGrad_wFull (a γ ω t : ℝ) : linGrad a (wFull γ ω t) =
    (2 * a * phi γ ω t) • E₂ 0 0 + (a * phi γ 1 t) • (E₂ 0 1 + E₂ 1 0) := by
  rw [linGrad_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wFull, E₂]

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `Ẇ = 𝒱` along the full-rank flow. -/
theorem hasDerivAt_wFull (γ : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (wFull γ ω) (mFull γ ω t) t := by
  have h := (((hasDerivAt_phi γ hω t).smul_const (E₂ 0 0)).add
    ((hasDerivAt_phi γ one_ne_zero t).smul_const (E₂ 0 1 + E₂ 1 0))).add_const (E₂ 1 1)
  exact h

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: `𝒱̇ + γ 𝒱 = -∇ℒ(W)` along the full-rank flow. -/
theorem hasDerivAt_mFull (γ : ℝ) {ω : ℝ} (hω0 : ω ≠ 0)
    (hω : ω ^ 2 + γ ^ 2 / 4 = 2 * (1 + γ ^ 2 / 4)) (t : ℝ) :
    HasDerivAt (mFull γ ω)
      (-(γ • mFull γ ω t) - linGrad (1 + γ ^ 2 / 4) (wFull γ ω t)) t := by
  have h := ((hasDerivAt_psi γ hω0 t).smul_const (E₂ 0 0)).add
    ((hasDerivAt_psi γ one_ne_zero t).smul_const (E₂ 0 1 + E₂ 1 0))
  refine h.congr_deriv ?_
  rw [linGrad_wFull, mFull, hω]
  simp only [one_pow]
  module

/-- The full-rank flow leaves the rank-one matrices: `det W(t) ≠ 0` for some arbitrarily small
`t > 0`, as `x = φ_{2a}`, `y = φ_a` satisfy `(x - y²)'' + γ (x - y²)' + 2 a (x - y²) = -2 ẏ²`. -/
theorem exists_phi_ne (γ : ℝ) {ω : ℝ} (hω0 : ω ≠ 0)
    (hω : ω ^ 2 + γ ^ 2 / 4 = 2 * (1 + γ ^ 2 / 4)) {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ T ∈ Ioo 0 T₀, phi γ ω T - (phi γ 1 T) ^ 2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hy := hasDerivAt_phi γ (one_ne_zero (α := ℝ))
  have hy' := hasDerivAt_psi γ (one_ne_zero (α := ℝ))
  have hx := hasDerivAt_phi γ hω0
  have hx' := hasDerivAt_psi γ hω0
  set D : ℝ → ℝ := fun t => phi γ ω t - (phi γ 1 t) ^ 2 with hD
  set D1 : ℝ → ℝ := fun t => psi γ ω t - 2 * phi γ 1 t * psi γ 1 t with hD1
  have hdD : ∀ t, HasDerivAt D (D1 t) t := fun t => by
    have h := (hx t).sub ((hy t).fun_pow 2)
    refine h.congr_deriv ?_
    simp only [hD1, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hdD1 : ∀ t, HasDerivAt D1 (-γ * D1 t - 2 * (1 + γ ^ 2 / 4) * D t
      - 2 * (psi γ 1 t) ^ 2) t := fun t => by
    have h := (hx' t).sub (((hy t).const_mul 2).mul (hy' t))
    refine h.congr_deriv ?_
    simp only [hD1, hD, hω, one_pow]
    ring
  have hnear : ∀ t ∈ Ioo 0 T₀, ∀ᶠ r in 𝓝 t, r ∈ Ioo 0 T₀ := fun t ht =>
    Ioo_mem_nhds ht.1 ht.2
  have hD0 : ∀ t ∈ Ioo 0 T₀, D t = 0 := hcon
  have hD10 : ∀ t ∈ Ioo 0 T₀, D1 t = 0 := fun t ht => by
    have h : HasDerivAt D 0 t := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [hnear t ht] with r hr using hD0 r hr)
    exact (hdD t).unique h
  have hψ : ∀ t ∈ Ioo 0 T₀, psi γ 1 t = 0 := fun t ht => by
    have h : HasDerivAt D1 0 t := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [hnear t ht] with r hr using hD10 r hr)
    have h2 := (hdD1 t).unique h
    rw [hD0 t ht, hD10 t ht] at h2
    have h3 : (psi γ 1 t) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 h3
  set t : ℝ := min T₀ 1 / 2 with ht
  have h0 : 0 < min T₀ 1 := lt_min hT₀ one_pos
  have ht0 : 0 < t := by positivity
  have ht1 : t < T₀ := by
    have := min_le_left T₀ 1
    linarith
  have ht2 : t < Real.pi := by
    have := min_le_right T₀ 1
    linarith [Real.pi_gt_three]
  have h5 := hψ t ⟨ht0, ht1⟩
  have h6 : 0 < Real.sin (1 * t) := by
    rw [one_mul]
    exact Real.sin_pos_of_pos_of_lt_pi ht0 ht2
  have h7 : psi γ 1 t < 0 := by
    have h8 : 0 < Real.exp (-γ / 2 * t) := Real.exp_pos _
    have h9 : 0 < (1 ^ 2 + γ ^ 2 / 4) / (1 : ℝ) := by positivity
    have : psi γ 1 t = -(((1 ^ 2 + γ ^ 2 / 4) / 1) * Real.exp (-γ / 2 * t) * Real.sin (1 * t)) := by
      simp only [psi]
      ring
    rw [this]
    have := mul_pos (mul_pos h9 h8) h6
    linarith
  linarith

/-- The untruncated iteration `m̂ = d m - λ g(w)`, `w⁺ = w + λ m̂`, `m⁺ = m̂`. -/
noncomputable def hbSeq (g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) (lr d : ℝ)
    (W₀ M₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ℕ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ
  | 0 => (W₀, M₀)
  | j + 1 => ((hbSeq g lr d W₀ M₀ j).1 + lr • (d • (hbSeq g lr d W₀ M₀ j).2
        - lr • g (hbSeq g lr d W₀ M₀ j).1),
      d • (hbSeq g lr d W₀ M₀ j).2 - lr • g (hbSeq g lr d W₀ M₀ j).1)

/-- A priori bound of the iteration `hbSeq` for a field of linear growth. -/
theorem hbSeq_bound {g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ} {c lr d : ℝ}
    (hc : 0 ≤ c) (hlr : 0 ≤ lr) (hlr1 : lr ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hg : ∀ x, ‖g x‖ ≤ c * ‖x‖) (W₀ M₀ : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    ‖(hbSeq g lr d W₀ M₀ n).1‖ + ‖(hbSeq g lr d W₀ M₀ n).2‖ ≤
      Real.exp ((1 + 2 * c) * (n * lr)) * (‖W₀‖ + ‖M₀‖) := by
  have h := discrete_gronwall_exp (e := fun n => ‖(hbSeq g lr d W₀ M₀ n).1‖
    + ‖(hbSeq g lr d W₀ M₀ n).2‖) (L := 1 + 2 * c) (h := lr) (b := 0) (by positivity) hlr le_rfl
    (fun n => ?_) n
  · simpa [hbSeq] using h
  · set w := (hbSeq g lr d W₀ M₀ n).1
    set m := (hbSeq g lr d W₀ M₀ n).2
    change ‖w + lr • (d • m - lr • g w)‖ + ‖d • m - lr • g w‖ ≤
      Real.exp ((1 + 2 * c) * lr) * (‖w‖ + ‖m‖) + 0
    have h1 : ‖d • m - lr • g w‖ ≤ ‖m‖ + lr * (c * ‖w‖) := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_of_nonneg hd0]
        exact mul_le_of_le_one_left (norm_nonneg _) hd1
      · rw [norm_smul, Real.norm_of_nonneg hlr]
        exact mul_le_mul_of_nonneg_left (hg w) hlr
    have h2 : ‖w + lr • (d • m - lr • g w)‖ ≤ ‖w‖ + lr * (‖m‖ + lr * (c * ‖w‖)) := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_of_nonneg hlr]
      exact mul_le_mul_of_nonneg_left h1 hlr
    have h3 : 0 ≤ lr * c * ‖w‖ := by positivity
    have h4 : lr * (lr * (c * ‖w‖)) ≤ lr * (c * ‖w‖) := by
      have : lr * (c * ‖w‖) * lr ≤ lr * (c * ‖w‖) * 1 :=
        mul_le_mul_of_nonneg_left hlr1 (by positivity)
      linarith
    have h5 : 1 + (1 + 2 * c) * lr ≤ Real.exp ((1 + 2 * c) * lr) := by
      linarith [Real.add_one_le_exp ((1 + 2 * c) * lr)]
    have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : 0 ≤ ‖w‖ + ‖m‖)
    have h7 : 0 ≤ lr * ‖w‖ := by positivity
    have h8 : 0 ≤ lr * c * ‖m‖ := by positivity
    nlinarith

/-- `hbSeq` with `λ = T / k`, `d = 1 - λ γ` is a first-order method for the full-rank flow
(`heavyBall_global_error` with `Π = P = 1`, no defects), with a bound along the iterates that does
not depend on `k`. -/
theorem hbSeq_close {g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ} {β c γ T : ℝ}
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hT : 0 < T) (hLip : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hgrow : ∀ x, ‖g x‖ ≤ c * ‖x‖) {X Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hX : ∀ t, HasDerivAt X (Y t) t) (hY : ∀ t, HasDerivAt Y (-(γ • Y t) - g (X t)) t)
    (hY0 : Y 0 = 0) : ∃ (C B : ℝ) (K : ℕ), 0 ≤ B ∧ ∀ k : ℕ, K ≤ k → 0 < k ∧
      (∀ j ≤ k, ‖g (hbSeq g (T / k) (1 - T / k * γ) (X 0) 0 j).1‖ ≤ B) ∧
      ‖(hbSeq g (T / k) (1 - T / k * γ) (X 0) 0 k).1 - X T‖ ≤ C / k := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (hX t).continuousAt
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun t => (hY t).continuousAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hXc.continuousOn
  set R : ℝ := Real.exp ((1 + 2 * c) * T) * ‖X 0‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set B : ℝ := c * (R + |B₂|) with hB
  have hB0 : 0 ≤ B := by positivity
  set C₀ : ℝ := γ * (T * B) + B + (γ * (T * B) + B) + γ * (γ * (T * B) + B) + β * (T * B) with hC₀
  refine ⟨Real.exp ((1 + β) * T) * (T * (T * C₀)), B, ⌈T + T * γ⌉₊ + 1, hB0, fun k hk => ?_⟩
  have hkpos : 0 < k := by omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hkT : T + T * γ ≤ k := by
    have h1 : T + T * γ ≤ ⌈T + T * γ⌉₊ := Nat.le_ceil _
    have h2 : ((⌈T + T * γ⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hTγ : 0 ≤ T * γ := by positivity
  set lr : ℝ := T / k with hlrdef
  have hlr : 0 < lr := by positivity
  have hklr : (k : ℝ) * lr = T := by rw [hlrdef]; field_simp
  have hlr1 : lr ≤ 1 := by
    rw [hlrdef, div_le_one hk']
    linarith
  have hlrγ : lr * γ ≤ 1 := by
    have : lr * γ = T * γ / k := by rw [hlrdef]; ring
    rw [this, div_le_one hk']
    linarith
  have hd0 : 0 ≤ 1 - lr * γ := by linarith
  have hd1 : 1 - lr * γ ≤ 1 := by
    have : 0 ≤ lr * γ := by positivity
    linarith
  obtain ⟨Sq, hSq⟩ : ∃ Sq, Sq = hbSeq g lr (1 - lr * γ) (X 0) 0 := ⟨_, rfl⟩
  have hsucc1 : ∀ n, (Sq (n + 1)).1 = (Sq n).1 + lr • (Sq (n + 1)).2 := fun n => by
    rw [hSq]
    rfl
  have hsucc2 : ∀ n, (Sq (n + 1)).2 = (1 - lr * γ) • (Sq n).2 - lr • g (Sq n).1 := fun n => by
    rw [hSq]
    rfl
  have hBW : ∀ j ≤ k, ‖g (Sq j).1‖ ≤ B := fun j hj => by
    have h1 := hbSeq_bound hc hlr.le hlr1 hd0 hd1 hgrow (X 0) 0 j
    rw [← hSq, norm_zero, add_zero] at h1
    have h2 : (j : ℝ) * lr ≤ T := by
      rw [← hklr]
      have : (j : ℝ) ≤ k := by exact_mod_cast hj
      gcongr
    have h3 : Real.exp ((1 + 2 * c) * (j * lr)) ≤ Real.exp ((1 + 2 * c) * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h4 : ‖(Sq j).1‖ ≤ R := by
      have h5 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (X 0))
      have h6 := norm_nonneg (Sq j).2
      rw [hR]
      linarith
    refine (hgrow _).trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith [abs_nonneg B₂]
  have hBX : ∀ t ∈ Ico (0 : ℝ) (0 + k * lr), ‖g (X t)‖ ≤ B := fun t ht => by
    have h1 := hB₂ t ⟨ht.1, by rw [zero_add, hklr] at ht; exact ht.2.le⟩
    refine (hgrow _).trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith [le_abs_self B₂]
  have hmain := heavyBall_global_error (Wk := fun n => (Sq n).1) (Mk := fun n => (Sq n).2)
    (Mh := fun n => (Sq (n + 1)).2) (Pr := fun _ => 1) (P := fun _ => 1) (X := X) (Y := Y)
    (ε := 0) (ε' := 0) (εV := 0) (ϑ := 0) (ϑh := 0) (B := B) (t₀ := 0) (N := k) hβ hγ hlr.le hlrγ
    le_rfl le_rfl le_rfl le_rfl le_rfl hB0 hLip (fun _ _ => IsOrthProj.one)
    (fun n _ => by simpa using hsucc2 n)
    (fun n _ => by simp [hsucc1 n])
    (fun n _ => by simp) (fun n _ => le_rfl) (fun n _ => by simp)
    (fun n hn => hBW n hn.le) (fun _ _ => IsOrthProj.one)
    ⟨hXc.continuousOn, fun t _ => by simpa using (hX t).hasDerivWithinAt⟩
    ⟨hYc.continuousOn, fun t _ => by simpa using (hY t).hasDerivWithinAt⟩
    (fun t _ => by simp) (fun t _ => by simp) hBX k le_rfl
  have hS0 : Sq 0 = (X 0, 0) := by rw [hSq]; rfl
  simp only [hklr, zero_add, hS0, sub_self, norm_zero, hY0, add_zero] at hmain
  refine ⟨hkpos, ?_, ?_⟩
  · rw [← hSq]
    exact hBW
  · rw [← hSq]
    have h1 := le_add_of_nonneg_right (a := ‖(Sq k).1 - X T‖) (norm_nonneg ((Sq k).2 - Y T))
    refine h1.trans (hmain.trans (le_of_eq ?_))
    have e5 : (k : ℝ) * (lr ^ 2 * C₀) = T * (T * C₀) / k := by
      rw [hlrdef]
      field_simp
    have e6 : Real.exp ((1 + β) * T) * (T * (T * C₀)) / k
        = Real.exp ((1 + β) * T) * (k * (lr ^ 2 * C₀)) := by
      rw [e5]
      ring
    rw [e6]
    simp only [hbLocal, hC₀]
    ring

/-- A step of Algorithm 1 with the full bases `Û = V̂ = U₁ = V₁ = I₂` and no truncation. -/
theorem isLRHeavyBallStep_id {r : Type*} [Fintype r] [DecidableEq r]
    {g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ} {lr d : ℝ}
    {U V : Matrix (Fin 2) r ℝ} {S Sv : Matrix r r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsLRHeavyBallStep g lr d 0 0 U S Sv V (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (U * S * Vᵀ + lr • (d • (U * Sv * Vᵀ) - lr • g (U * S * Vᵀ)))
      (d • (U * Sv * Vᵀ) - lr • g (U * S * Vᵀ)) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (U * S * Vᵀ + lr • (d • (U * Sv * Vᵀ) - lr • g (U * S * Vᵀ)))
      (d • (U * Sv * Vᵀ) - lr • g (U * S * Vᵀ)) (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨hU, hV, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp⟩

/-- The ranks of the run in `lowRankHeavyBall_needs_normalMomentum`: `1`, then `2`. -/
def rkSeq : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 2

/-- The bases of the run in `lowRankHeavyBall_needs_normalMomentum`. -/
noncomputable def runU (u₀ : Matrix (Fin 2) (Fin 1) ℝ) : ∀ j, Matrix (Fin 2) (Fin (rkSeq j)) ℝ
  | 0 => u₀
  | _ + 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The coefficients of the run in `lowRankHeavyBall_needs_normalMomentum`. -/
noncomputable def runS (s₀ : Matrix (Fin 1) (Fin 1) ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ j, Matrix (Fin (rkSeq j)) (Fin (rkSeq j)) ℝ
  | 0 => s₀
  | j + 1 => W (j + 1)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the bases of the run are orthonormal. -/
theorem runU_orth {u₀ : Matrix (Fin 2) (Fin 1) ℝ} (h : u₀ᵀ * u₀ = 1) (j : ℕ) :
    (runU u₀ j)ᵀ * runU u₀ j = 1 := by
  cases j with
  | zero => exact h
  | succ j => exact (by simp : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1)

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the weights of the run in factored form. -/
theorem run_mul {u₀ : Matrix (Fin 2) (Fin 1) ℝ} {s₀ : Matrix (Fin 1) (Fin 1) ℝ}
    {W : ℕ → Matrix (Fin 2) (Fin 2) ℝ} (h : u₀ * s₀ * u₀ᵀ = W 0) (j : ℕ) :
    runU u₀ j * runS s₀ W j * (runU u₀ j)ᵀ = W j := by
  cases j with
  | zero => exact h
  | succ j =>
    exact (by simp : (1 : Matrix (Fin 2) (Fin 2) ℝ) * W (j + 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      = W (j + 1))

/-- Auxiliary for Theorem 3 of arXiv 2506.17475: the entries of `wFull`. -/
theorem wFull_apply (γ ω t : ℝ) :
    wFull γ ω t = !![phi γ ω t, phi γ 1 t; phi γ 1 t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wFull, E₂]

/-- `2 u uᵀ` at `θ = π/4`. -/
theorem two_smul_EU_pi_div_four (γ ω : ℝ) :
    (2 : ℝ) • EU (Real.pi / 4) = wFull γ ω 0 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (2 : ℝ) * (√2 / 2) ^ 2 = 1 := by
    rw [div_pow, h2]
    norm_num
  have h4 : (2 : ℝ) * (√2 / 2 * (√2 / 2)) = 1 := by
    rw [← sq, h3]
  rw [wFull_apply, EU_apply, Real.cos_pi_div_four, Real.sin_pi_div_four, phi_zero, phi_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h3, h4]

/-- **The normal part of the momentum cannot be dropped from Theorem 3 of arXiv 2506.17475.**
Literally, Theorem 3 bounds `‖W(t) - W^r_t‖` by `c₁ ε + c₂ λ + c₃ ϑ / λ + c₄ ϑ̂ / λ`, without the
term `εV` of `lowRankHeavyBall_error`.  This remains false after correcting the damping to
`1 - λ γ`.  For every `γ ≥ 0` take on `ℝ^{2×2}` the convex quadratic
`ℒ(Z) = a (Z₀₀² + Z₀₁²/2 + Z₁₀²/2)`, `a = 1 + γ²/4`, whose gradient has no normal component at any
matrix (`linGrad_normal`), and start at the rank-one `W(0) = (1 1; 1 1)`, `𝒱(0) = 0`.  Then:

* there is a solution of `Ẇ = P(W) 𝒱`, `𝒱̇ + γ 𝒱 = -P(W) ∇ℒ(W)` on `[0, T]` of rank one
  (`W = σ u uᵀ`), so that `ε' = 0`;
* for every constant `c` there is `k` and a run of Algorithm 1 from the same initial data, with
  `λ = T / k`, damping `1 - λ γ`, no truncation at all (`ϑ = ϑ̂ = 0`), `ε = 0`, gradients bounded by
  the same `B`, such that `c λ < ‖W(T) - W^k‖`.

The run has rank `2` after the first step: without truncation it tracks `Ẇ = 𝒱`, the full flow,
which leaves the rank-one matrices because a second-order flow does not follow the curved manifold
(`exists_phi_ne`), although its force is tangent.  The paper's proof overlooks this by using
`Ẇ = 𝒱` in place of `Ẇ = P(W) 𝒱`.  The gradient of this `ℒ` is unbounded on `ℝ^{2×2}` but bounded
by `B` along both trajectories, which is all that `lowRankHeavyBall_error` uses.  Theorem 3 as
printed assumes a bounded gradient, so this is a counterexample to the damping-corrected
statement with that hypothesis restricted to the trajectories, not literally to the printed one
(a cutoff of `ℒ` far from the trajectories would close this gap; not formalized). -/
theorem lowRankHeavyBall_needs_normalMomentum {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ (ℒ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)
      (β T B : ℝ) (X Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ → Matrix (Fin 2) (Fin 1) ℝ)
      (σ : ℝ → ℝ), 0 < T ∧ (∀ Z, HasFDerivAt ℒ (innerSL ℝ (g Z)) Z) ∧ (∀ Z, 0 ≤ ℒ Z) ∧
      (∀ Z Z', ‖g Z - g Z'‖ ≤ β * ‖Z - Z'‖) ∧
      ODESolution (fun t _ => tangentProj (u t) (u t) (Y t)) X 0 T ∧
      ODESolution (fun t Z => -(γ • Z) - tangentProj (u t) (u t) (g (X t))) Y 0 T ∧
      (∀ t ∈ Icc 0 T, (u t)ᵀ * u t = 1 ∧ 0 < σ t ∧
        X t = u t * (σ t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * (u t)ᵀ ∧
        (1 - tangentProj (u t) (u t)) (g (X t)) = 0 ∧ ‖g (X t)‖ ≤ B) ∧
      ∀ c : ℝ, ∃ k : ℕ, 0 < k ∧ ∃ (U V : ∀ j, Matrix (Fin 2) (Fin (rkSeq j)) ℝ)
        (S Sv : ∀ j, Matrix (Fin (rkSeq j)) (Fin (rkSeq j)) ℝ)
        (Uh Vh Sh Shv : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
        (∀ j < k, IsLRHeavyBallStep g (T / k) (1 - T / k * γ) 0 0 (U j) (S j) (Sv j) (V j)
          (Uh j) (Vh j) (Sh j) (Shv j) (U (j + 1)) (S (j + 1)) (Sv (j + 1)) (V (j + 1))) ∧
        (∀ j < k, (1 - U j * (U j)ᵀ) * g (U j * S j * (V j)ᵀ) * (1 - V j * (V j)ᵀ) = 0) ∧
        (∀ j < k, ‖g (U j * S j * (V j)ᵀ)‖ ≤ B) ∧
        U 0 * S 0 * (V 0)ᵀ = X 0 ∧ U 0 * Sv 0 * (V 0)ᵀ = Y 0 ∧
        c * (T / k) < ‖X T - U k * S k * (V k)ᵀ‖ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 + γ ^ 2 / 4 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨ω, hωd⟩ : ∃ ω : ℝ, ω = √(2 + γ ^ 2 / 4) := ⟨_, rfl⟩
  have hωpos : 0 < ω := by
    rw [hωd]
    exact Real.sqrt_pos.2 (by positivity)
  have hω2 : ω ^ 2 + γ ^ 2 / 4 = 2 * (1 + γ ^ 2 / 4) := by
    rw [hωd, Real.sq_sqrt (by positivity)]
    ring
  obtain ⟨T₀, s, θ, p, m, n, hT₀, hs0, hθ0, hp0, hm0, hn0, hsol⟩ := exists_constrained γ a
  obtain ⟨T, hT, hne⟩ := exists_phi_ne γ hωpos.ne' hω2 hT₀
  obtain ⟨Xc, hXcd⟩ : ∃ Xc : ℝ → Matrix (Fin 2) (Fin 2) ℝ, Xc = fun t => s t • EU (θ t) :=
    ⟨_, rfl⟩
  obtain ⟨Yc, hYcd⟩ : ∃ Yc : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      Yc = fun t => p t • AA (θ t) + m t • EU (θ t) + n t • EN (θ t) := ⟨_, rfl⟩
  have hIcc : ∀ t ∈ Icc 0 T, t ∈ Ioo (-T₀) T₀ := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2, hT.2]⟩
  have hder : ∀ t ∈ Icc 0 T,
      HasDerivAt Xc (tangentProj (uu (θ t)) (uu (θ t)) (Yc t)) t ∧
      HasDerivAt Yc (-(γ • Yc t) - tangentProj (uu (θ t)) (uu (θ t)) (linGrad a (Xc t))) t := by
    intro t ht
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsol t (hIcc t ht)
    rw [hXcd, hYcd]
    exact constrained_hasDerivAt h1.ne' h2 h3 h4 h5 h6
  have hLip : ∀ Z Z', ‖linGrad a Z - linGrad a Z'‖ ≤ 2 * a * ‖Z - Z'‖ := fun Z Z' => by
    rw [linGrad_sub]
    exact norm_linGrad_le ha0.le _
  have hXF := hasDerivAt_wFull γ hωpos.ne'
  have hYF := hasDerivAt_mFull γ hωpos.ne' hω2
  rw [← ha] at hYF
  have hY0 : mFull γ ω 0 = 0 := by simp [mFull, psi_zero]
  obtain ⟨C, B₁, K, hB₁, hclose⟩ := hbSeq_close (by positivity) (by positivity) hγ hT.1 hLip
    (norm_linGrad_le ha0.le) hXF hYF hY0
  have hXcc : ContinuousOn Xc (Icc 0 T) := fun t ht =>
    (hder t ht).1.continuousAt.continuousWithinAt
  have hYcc : ContinuousOn Yc (Icc 0 T) := fun t ht =>
    (hder t ht).2.continuousAt.continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hXcc
  have hB₂0 : 0 ≤ 2 * a * |B₂| := by positivity
  have hinit : Xc 0 = wFull γ ω 0 := by
    rw [hXcd]
    simp only [hs0, hθ0]
    exact two_smul_EU_pi_div_four γ ω
  have hYinit : Yc 0 = 0 := by
    rw [hYcd]
    simp [hp0, hm0, hn0]
  have hgap : 0 < ‖Xc T - wFull γ ω T‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    apply hne
    have h' := h
    rw [hXcd, wFull_apply] at h'
    have e00 : s T * Real.cos (θ T) ^ 2 = phi γ ω T := by
      simpa [EU_apply] using congrFun (congrFun h' 0) 0
    have e01 : s T * (Real.cos (θ T) * Real.sin (θ T)) = phi γ 1 T := by
      simpa [EU_apply] using congrFun (congrFun h' 0) 1
    have e11 : s T * Real.sin (θ T) ^ 2 = 1 := by
      simpa [EU_apply] using congrFun (congrFun h' 1) 1
    rw [← e00, ← e01]
    calc _ = s T * Real.cos (θ T) ^ 2 * (s T * Real.sin (θ T) ^ 2)
          - (s T * (Real.cos (θ T) * Real.sin (θ T))) ^ 2 := by rw [e11]; ring
      _ = 0 := by ring
  refine ⟨linLoss a, linGrad a, 2 * a, T, B₁ + 2 * a * |B₂|, Xc, Yc, fun t => uu (θ t), s, hT.1,
    hasFDerivAt_linLoss a, linLoss_nonneg ha0.le, hLip,
    ⟨hXcc, fun t ht => (hder t ⟨ht.1, ht.2.le⟩).1.hasDerivWithinAt⟩,
    ⟨hYcc, fun t ht => (hder t ⟨ht.1, ht.2.le⟩).2.hasDerivWithinAt⟩,
    fun t ht => ⟨uu_orth _, (hsol t (hIcc t ht)).1, ?_, ?_, ?_⟩, fun c => ?_⟩
  · rw [hXcd]
    simp [EU, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hXcd]
    simp only [sub_apply, one_apply_eq_self]
    rw [linGrad_EU, map_sub, map_smul, map_smul, tangentProj_AA, tangentProj_EU, sub_self]
  · have h1 := hB₂ t ht
    have h2 := norm_linGrad_le ha0.le (Xc t)
    have h3 : 2 * a * ‖Xc t‖ ≤ 2 * a * |B₂| :=
      mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (by positivity)
    linarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((|c| * T + |C|) / ‖Xc T - wFull γ ω T‖)
  obtain ⟨hk0, hBj, hcl⟩ := hclose (max K (k₀ + 1)) (le_max_left _ _)
  have hkk₀ : k₀ + 1 ≤ max K (k₀ + 1) := le_max_right _ _
  obtain ⟨k, hkdef⟩ : ∃ k, k = max K (k₀ + 1) := ⟨_, rfl⟩
  rw [← hkdef] at hk0 hBj hcl hkk₀
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hk₀' : (k₀ : ℝ) ≤ k := by
    have : k₀ ≤ k := by omega
    exact_mod_cast this
  obtain ⟨lr, hlrd⟩ : ∃ lr : ℝ, lr = T / k := ⟨_, rfl⟩
  rw [← hlrd] at hBj hcl
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = 1 - lr * γ := ⟨_, rfl⟩
  rw [← hdd] at hBj hcl
  obtain ⟨Sq, hSq⟩ : ∃ Sq, Sq = hbSeq (linGrad a) lr d (wFull γ ω 0) 0 := ⟨_, rfl⟩
  rw [← hSq] at hBj hcl
  have hsucc2 : ∀ j, (Sq (j + 1)).2 = d • (Sq j).2 - lr • linGrad a (Sq j).1 := fun j => by
    rw [hSq]
    rfl
  have hsucc1 : ∀ j, (Sq (j + 1)).1 = (Sq j).1 + lr • (Sq (j + 1)).2 := fun j => by
    rw [hSq]
    rfl
  have hS0 : Sq 0 = (wFull γ ω 0, 0) := by rw [hSq]; rfl
  have hu : (uu (Real.pi / 4))ᵀ * uu (Real.pi / 4) = 1 := uu_orth _
  have h0W : uu (Real.pi / 4) * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      * (uu (Real.pi / 4))ᵀ = (fun j => (Sq j).1) 0 := by
    simp only [hS0]
    rw [← two_smul_EU_pi_div_four]
    simp [EU, Matrix.mul_smul, Matrix.smul_mul]
  have h0M : uu (Real.pi / 4) * (0 : Matrix (Fin 1) (Fin 1) ℝ)
      * (uu (Real.pi / 4))ᵀ = (fun j => (Sq j).2) 0 := by
    simp [hS0]
  refine ⟨k, hk0, runU (uu (Real.pi / 4)), runU (uu (Real.pi / 4)),
    runS ((2 : ℝ) • 1) (fun j => (Sq j).1), runS 0 (fun j => (Sq j).2), fun _ => 1, fun _ => 1,
    fun j => (Sq (j + 1)).1, fun j => (Sq (j + 1)).2, fun j _ => ?_, fun j _ => ?_,
    fun j hj => ?_, ?_, ?_, ?_⟩
  · have h := isLRHeavyBallStep_id (g := linGrad a) (lr := lr) (d := d)
      (S := runS ((2 : ℝ) • 1) (fun j => (Sq j).1) j) (Sv := runS 0 (fun j => (Sq j).2) j)
      (runU_orth hu j) (runU_orth hu j)
    rw [run_mul h0W j, run_mul h0M j, ← hsucc2 j, ← hsucc1 j] at h
    rw [← hlrd, ← hdd]
    exact h
  · exact linGrad_normal a _ (runU_orth hu j) (runU_orth hu j)
  · rw [run_mul h0W j]
    exact (hBj j hj.le).trans (by linarith)
  · rw [hinit]
    exact (run_mul h0W 0).trans (by simp [hS0])
  · rw [hYinit]
    exact (run_mul h0M 0).trans (by simp [hS0])
  · rw [run_mul h0W k, ← hlrd]
    have htri : ‖Xc T - wFull γ ω T‖ ≤ ‖Xc T - (Sq k).1‖ + ‖(Sq k).1 - wFull γ ω T‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hδ := hgap
    set δ := ‖Xc T - wFull γ ω T‖ with hδd
    have h1 : (|c| * T + |C|) / δ < k := hk₀.trans_le hk₀'
    rw [div_lt_iff₀ hδ] at h1
    have h2 : |c| * T + |C| < k * δ := h1
    have h3 : C / k + c * lr < δ := by
      rw [hlrd, div_add' _ _ _ hk'.ne', div_lt_iff₀ hk']
      have h4 : c * (T / k) * k = c * T := by field_simp
      rw [h4]
      have h5 := le_abs_self C
      have h6 := mul_le_mul_of_nonneg_right (le_abs_self c) hT.1.le
      linarith
    linarith

end Theorem3Counterexamples
end LeanDLRA.Literature.P2506_17475
