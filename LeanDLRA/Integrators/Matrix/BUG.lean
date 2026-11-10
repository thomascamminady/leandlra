import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Foundations.Existence
import LeanDLRA.Integrators.Matrix.Defs

/-!
# The BUG integrator for matrices, at the level of the factors

This file instantiates the abstract robust error analysis of the basis-update & Galerkin (BUG)
integrator (`LeanDLRA/Integrators/BUG.lean`) and of its rank-adaptive variant
(`LeanDLRA/Integrators/RankAdaptiveBUG.lean`) for real `m × n` matrices with the Frobenius norm
(`open scoped LeanDLRA.Frobenius`), **at the level of the factors** that the algorithms compute.

## The algorithms

**BUG integrator** (Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank
approximation*, BIT 2022, arXiv 2010.02022, §3.1).  One step from `Y₀ = U₀ S₀ V₀ᵀ`
(`U₀ᵀ U₀ = I`, `V₀ᵀ V₀ = I`) at `t₀` to `t₁ = t₀ + h`:

* K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`; QR step: `U₁` with `U₁ᵀ U₁ = I` and
  `U₁ U₁ᵀ K(t₁) = K(t₁)`;
* L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ`; QR step: `V₁` with `V₁ᵀ V₁ = I` and
  `V₁ V₁ᵀ L(t₁) = L(t₁)`;
* S-step `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, `S(t₀) = M S₀ Nᵀ`, `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`;
  `Y₁ = U₁ S(t₁) V₁ᵀ`.

The factor fields are `kField`, `lField`, `sField`; one step is bundled in `IsStep`.

**Rank-adaptive BUG integrator** (Ceruti–Kusch–Lubich, BIT 2022, arXiv 2104.05247, §2.1): the
same K- and L-steps, augmented bases `Û`, `V̂` (`2r` columns) capturing `(K(t₁), U₀)` and
`(L(t₁), V₀)`, the S-step in the augmented bases with `Ŝ(t₀) = M̂ S₀ N̂ᵀ`, and a truncation
`‖Y₁ - Û Ŝ(t₁) V̂ᵀ‖ ≤ ϑ`; bundled in `IsRankAdaptiveStep` (with `Û = Ua`, `V̂ = Va` in the code).

## Main results

* (a) **Derivative transfer**: `odeSolution_kField`, `odeSolution_lField`, `odeSolution_sField`
  lift the factor trajectories along the continuous linear maps `K ↦ K V₀ᵀ`, `L ↦ U₀ Lᵀ`,
  `S ↦ U₁ S V₁ᵀ` (`odeSolution_comp_clm`) to solutions of the projected full-space fields
  `YK' = Q₀ F(t, YK)`, `YL' = P₀ F(t, YL)`, `YS' = P₁ Q₁ F(t, YS)` of the abstract theory, with
  `P = leftProj U = (X ↦ U Uᵀ X)` and `Q = rightProj V = (X ↦ X V Vᵀ)`.
* (b) **Normal components**: the factored normal-component assumption
  `FactoredNormalBound F r ε` (`‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for orthonormal
  `U`, `V` with `r` columns) gives the abstract hypotheses at `YK(t₁) = U₁ (U₁ᵀ K(t₁)) V₀ᵀ` and
  `YL(t₁) = U₀ (L(t₁)ᵀ V₁) V₁ᵀ` (`kNormal_le`, `lNormal_le`); hence `IsStep.isBUGStep`: every
  matrix BUG step is an abstract `IsBUGStep` (pointwise version `IsStep.isBUGStep_of_normal`).
* (c) **Ceruti–Lubich Theorem 4** for matrices: Lemma 2 (`IsStep.capture_left`,
  `IsStep.capture_right`: `‖(I - U₁ U₁ᵀ) A(t₁)‖ ≤ ϑ`, `‖A(t₁) (I - V₁ V₁ᵀ)‖ ≤ ϑ`,
  `ϑ = h (4 L B h + ε)`), Lemma 3 (`IsStep.capture`: `‖U₁ U₁ᵀ A(t₁) V₁ V₁ᵀ - A(t₁)‖ ≤ 2ϑ`),
  Lemma 4 (`IsStep.local_error`, `IsStep.local_error_le`: `‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h)`), the
  factor-level form `IsStep.coeff_error_le` (`‖S(t₁) - U₁ᵀ A(t₁) V₁‖ ≤ h (c₁ ε + c₂ h)`, via
  `norm_coeff_sub_le`), and the global error `global_error`, `global_error_le`
  (`‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁ ε + c₂ h` for `j h ≤ T`).
* (d) **Ceruti–Kusch–Lubich Theorem 2** for matrices:
  `IsRankAdaptiveStep.isRankAdaptiveBUGStep` (every matrix rank-adaptive step is an abstract
  `IsRankAdaptiveBUGStep`), `IsRankAdaptiveStep.start_eq` (Lemma 1),
  `IsRankAdaptiveStep.local_error_le` (`‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h) + ϑ`),
  `IsRankAdaptiveStep.coeff_error_le`, and `rankAdaptive_global_error_le`
  (`‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ j ϑ`, with ranks `rⱼ` varying from step to step and the
  normal-component assumption at rank `rⱼ`, as in condition 2 of Theorem 2).  The rank-`r`
  normal-component assumption is transported to the augmented basis `Û` (`2r` columns) through
  an `r`-column basis `U'` capturing `K(t₁)` inside the range of `Û`
  (`exists_orthonormal_capture_within`) and the range monotonicity
  `‖(I - Û Ûᵀ) X (I - V₀ V₀ᵀ)‖ ≤ ‖(I - U' U'ᵀ) X (I - V₀ V₀ᵀ)‖` (`norm_normal_le_of_left`).
  `trunc_of_coeff`: a truncation of the small matrix `Ŝ(t₁)` to tolerance `ϑ` (truncated SVD)
  is a truncation of `Ŷ₁` to tolerance `ϑ`.
* (e) **Well-posedness**: `exists_qr`, `exists_aug_qr` (the QR captures exist, from
  `Matrix/Orthonormal.lean`), and `exists_isStep`, `exists_isRankAdaptiveStep`: for `F`
  Lipschitz, bounded and continuous in time, complete steps exist (substep ODEs solved by
  `Foundations/Existence.lean`, `exists_odeSolution_conj`).
* Satisfiability: `isStep_example` and `isRankAdaptiveStep_example` (`F ≡ I` on `2 × 2`
  matrices, rank `1`, non-tangential: `normal_unitCol_ne_zero`; the rank-adaptive example has a
  genuine truncation `diag(2, 1) ↦ diag(2, 0)` with `ϑ = 1`), with `example`s instantiating the
  local error bounds and the global error bounds `global_error_le`,
  `rankAdaptive_global_error_le`.

## Deviations from the papers and generalizations

* The constants are explicit: `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` (step sizes `h ≤ H`),
  `c₀ = e^{L T}` etc.; see `Integrators/BUG.lean` for the comparison with the paper's proof.
* The QR factorizations enter only through `Uᵀ U = I` and the capture `U Uᵀ K(t₁) = K(t₁)`
  (equivalent to `K(t₁) = U₁ R₁`, `kCap_of_qr`); rank-deficient `K(t₁)` is allowed.
* The normal-component assumption (condition 2 of Theorem 2 of arXiv 2010.02022: for `Y ∈ M_r`
  near `A(t)`) is imposed in the factored global form for all `U S Vᵀ` with orthonormal `U`, `V`
  (also for singular `S`, i.e. rank `≤ r`); only its instances at `YK(t₁)` and `YL(t₁)` are used,
  and `IsStep.isBUGStep_of_normal` states the result with just these two instances.
* The augmented bases may have any number of columns (`k`, `k'`), not only `2r`; the
  rank-adaptive global result allows varying ranks `rⱼ` and augmented sizes.
* As in the abstract files, the exact flows from the numerical values (Lady Windermere's fan)
  are hypotheses (`Φ`); their existence is `Foundations/Existence.lean`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

/-! ### Lifting factor trajectories along continuous linear maps -/

section Lift

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- **Lifting a solution.**  If a continuous linear map `Φ` intertwines two vector fields,
`g t (Φ x) = Φ (f t x)`, then it maps solutions of `y' = f(t, y)` to solutions of
`z' = g(t, z)` (derivative transfer through `Φ`).  With `Φ K = K V₀ᵀ`, `Φ L = U₀ Lᵀ` and
`Φ S = U₁ S V₁ᵀ` this lifts the factor ODEs of the BUG integrator to the full-space trajectories
of the abstract theory. -/
theorem odeSolution_comp_clm {f : ℝ → E → E} {g : ℝ → E' → E'} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (Φ : E →L[ℝ] E') (h : ∀ t x, g t (Φ x) = Φ (f t x)) :
    ODESolution g (fun t => Φ (y t)) a b where
  cont := Φ.continuous.comp_continuousOn hy.cont
  deriv t ht := by
    rw [h]
    exact Φ.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)

/-- Conjugating an `L`-Lipschitz field (`L ≥ 0`) by continuous linear maps,
`x ↦ Ψ (F t (Φ x))`, gives a field with Lipschitz constant `‖Ψ‖ L ‖Φ‖`. -/
theorem isLipschitzField_conj {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    IsLipschitzField (fun t x => Ψ (F t (Φ x))) (‖Ψ‖ * L * ‖Φ‖) := fun t x y => by
  calc ‖Ψ (F t (Φ x)) - Ψ (F t (Φ y))‖ = ‖Ψ (F t (Φ x) - F t (Φ y))‖ := by rw [map_sub]
    _ ≤ ‖Ψ‖ * ‖F t (Φ x) - F t (Φ y)‖ := Ψ.le_opNorm _
    _ ≤ ‖Ψ‖ * (L * ‖Φ (x - y)‖) := by
        rw [map_sub]
        exact mul_le_mul_of_nonneg_left (hF t _ _) (norm_nonneg _)
    _ ≤ ‖Ψ‖ * (L * (‖Φ‖ * ‖x - y‖)) := by
        gcongr
        exact Φ.le_opNorm _
    _ = ‖Ψ‖ * L * ‖Φ‖ * ‖x - y‖ := by ring

/-- Conjugating a field bounded by `B` gives a field bounded by `‖Ψ‖ B`. -/
theorem isBoundedField_conj {F : ℝ → E → E} {B : ℝ} (hB : IsBoundedField F B)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    IsBoundedField (fun t x => Ψ (F t (Φ x))) (‖Ψ‖ * B) := fun t _ =>
  (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB t _) (norm_nonneg _))

/-- **Existence for conjugated fields.**  If `F` is Lipschitz, bounded and continuous in time,
every field of the form `f t x = Ψ (F t (Φ x))` (the K-, L- and S-step factor fields) has a
solution on `[a, b]` with arbitrary initial value. -/
theorem exists_odeSolution_conj [CompleteSpace E'] {F : ℝ → E → E} {L B : ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ x, Continuous fun t => F t x)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') {f : ℝ → E' → E'} (hf : ∀ t x, f t x = Ψ (F t (Φ x)))
    {a b : ℝ} (hab : a ≤ b) (y₀ : E') : ∃ y : ℝ → E', ODESolution f y a b ∧ y a = y₀ := by
  have hfe : f = fun t x => Ψ (F t (Φ x)) := funext fun t => funext fun x => hf t x
  subst hfe
  have hF' : IsLipschitzField F (max L 0) := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  exact exists_ODESolution (isLipschitzField_conj hF' (le_max_right _ _) Φ Ψ)
    (isBoundedField_conj hB Φ Ψ) (fun x => Ψ.continuous.comp (hc (Φ x))) hab y₀

omit [NormedAddCommGroup E'] [NormedSpace ℝ E'] in
/-- The affine function `t ↦ y₀ + (t - a) c` solves the ODE with the constant field `c` (used in
the satisfiability examples, where `F` is constant and all substeps are explicit). -/
theorem odeSolution_affine (y₀ c : E) (a b : ℝ) :
    ODESolution (fun _ _ => c) (fun t => y₀ + (t - a) • c) a b where
  cont := by fun_prop
  deriv t _ := by
    have h : HasDerivAt (fun t : ℝ => y₀ + (t - a) • c) c t := by
      simpa using (((hasDerivAt_id t).sub_const a).smul_const c).const_add y₀
    exact h.hasDerivWithinAt

end Lift

/-! ### The factor fields of the BUG integrator -/

section Fields

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k']

/-- The K-step field `K ↦ F(t, K V₀ᵀ) V₀` (arXiv 2010.02022, §3.1). -/
def kField (V₀ : Matrix n k ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (K : Matrix m k ℝ) : Matrix m k ℝ :=
  F t (K * V₀ᵀ) * V₀

/-- The L-step field `L ↦ F(t, U₀ Lᵀ)ᵀ U₀` (arXiv 2010.02022, §3.1). -/
def lField (U₀ : Matrix m k ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (L : Matrix n k ℝ) : Matrix n k ℝ :=
  (F t (U₀ * Lᵀ))ᵀ * U₀

/-- The Galerkin S-step field `S ↦ U₁ᵀ F(t, U₁ S V₁ᵀ) V₁` (arXiv 2010.02022, §3.1; with the
augmented bases `Û`, `V̂` this is the S-step (5) of arXiv 2104.05247). -/
def sField (U₁ : Matrix m k ℝ) (V₁ : Matrix n k' ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (S : Matrix k k' ℝ) : Matrix k k' ℝ :=
  U₁ᵀ * F t (U₁ * S * V₁ᵀ) * V₁

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}

/-- **K-step lift.**  If `K' = F(t, K V₀ᵀ) V₀`, then `YK = K V₀ᵀ` solves
`YK' = Q₀ F(t, YK)` with `Q₀ = rightProj V₀ = (X ↦ X V₀ V₀ᵀ)`. -/
theorem odeSolution_kField {V₀ : Matrix n k ℝ} {K : ℝ → Matrix m k ℝ}
    (hK : ODESolution (kField V₀ F) K t₀ t₁) :
    ODESolution (fun t x => rightProj V₀ (F t x)) (fun t => K t * V₀ᵀ) t₀ t₁ :=
  odeSolution_comp_clm hK (Frobenius.rightMulCLM V₀ᵀ) fun t x => by
    simp only [Frobenius.rightMulCLM_apply, rightProj_apply, kField]

/-- **L-step lift.**  If `L' = F(t, U₀ Lᵀ)ᵀ U₀`, then `YL = U₀ Lᵀ` solves `YL' = P₀ F(t, YL)`
with `P₀ = leftProj U₀ = (X ↦ U₀ U₀ᵀ X)`. -/
theorem odeSolution_lField {U₀ : Matrix m k ℝ} {Lf : ℝ → Matrix n k ℝ}
    (hL : ODESolution (lField U₀ F) Lf t₀ t₁) :
    ODESolution (fun t x => leftProj U₀ (F t x)) (fun t => U₀ * (Lf t)ᵀ) t₀ t₁ :=
  odeSolution_comp_clm hL ((Frobenius.leftMulCLM U₀).comp Frobenius.transposeCLM) fun t x => by
    simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
      Frobenius.transposeCLM_apply, leftProj_apply, lField, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **S-step lift.**  If `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, then `YS = U₁ S V₁ᵀ` solves the Galerkin
equation `YS' = P₁ Q₁ F(t, YS)` with `P₁ = leftProj U₁`, `Q₁ = rightProj V₁`. -/
theorem odeSolution_sField {U₁ : Matrix m k ℝ} {V₁ : Matrix n k' ℝ} {S : ℝ → Matrix k k' ℝ}
    (hS : ODESolution (sField U₁ V₁ F) S t₀ t₁) :
    ODESolution (fun t x => leftProj U₁ (rightProj V₁ (F t x))) (fun t => U₁ * S t * V₁ᵀ)
      t₀ t₁ :=
  odeSolution_comp_clm hS ((Frobenius.rightMulCLM V₁ᵀ).comp (Frobenius.leftMulCLM U₁))
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftProj_rightProj_apply, sField]

/-- The K-step field as a conjugated field `Ψ (F t (Φ K))`. -/
lemma kField_eq (V₀ : Matrix n k ℝ) (t : ℝ) (K : Matrix m k ℝ) :
    kField V₀ F t K = Frobenius.rightMulCLM V₀ (F t (Frobenius.rightMulCLM V₀ᵀ K)) := rfl

/-- The L-step field as a conjugated field `Ψ (F t (Φ L))`. -/
lemma lField_eq (U₀ : Matrix m k ℝ) (t : ℝ) (L : Matrix n k ℝ) :
    lField U₀ F t L = ((Frobenius.rightMulCLM U₀).comp Frobenius.transposeCLM)
      (F t (((Frobenius.leftMulCLM U₀).comp Frobenius.transposeCLM) L)) := rfl

/-- The S-step field as a conjugated field `Ψ (F t (Φ S))`. -/
lemma sField_eq (U₁ : Matrix m k ℝ) (V₁ : Matrix n k' ℝ) (t : ℝ) (S : Matrix k k' ℝ) :
    sField U₁ V₁ F t S = ((Frobenius.rightMulCLM V₁).comp (Frobenius.leftMulCLM U₁ᵀ))
      (F t (((Frobenius.rightMulCLM V₁ᵀ).comp (Frobenius.leftMulCLM U₁)) S)) := rfl

end Fields

/-! ### Normal components and range monotonicity -/

section Normal

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq m]
  [DecidableEq n]

/-- The normal component with the complementary projectors applied in the other order:
`(1 - Q) ((1 - P) Z) = (I - U Uᵀ) Z (I - V Vᵀ)`. -/
theorem one_sub_rightProj_one_sub_leftProj_apply (U : Matrix m k ℝ) (V : Matrix n k' ℝ)
    (Z : Matrix m n ℝ) :
    (1 - rightProj V) ((1 - leftProj U) Z) = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  rw [one_sub_rightProj_apply, one_sub_leftProj_apply]

/-- **Range monotonicity of the normal component (left).**  If the range of `Û` contains the
range of `U` (`Û Ûᵀ U = U`) and `Û` has orthonormal columns, then
`‖(I - Û Ûᵀ) X (I - V Vᵀ)‖ ≤ ‖(I - U Uᵀ) X (I - V Vᵀ)‖`. -/
theorem norm_normal_le_of_left {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {U : Matrix m k ℝ}
    {Ua : Matrix m k₂ ℝ} (hUa : Uaᵀ * Ua = 1) (h : Ua * Uaᵀ * U = U) (V : Matrix n k' ℝ)
    (X : Matrix m n ℝ) :
    ‖(1 - Ua * Uaᵀ) * X * (1 - V * Vᵀ)‖ ≤ ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ := by
  rw [← one_sub_leftProj_one_sub_rightProj_apply, ← one_sub_leftProj_one_sub_rightProj_apply]
  exact norm_one_sub_leftProj_le hUa h _

/-- **Range monotonicity of the normal component (right).**  If the range of `V̂` contains the
range of `V` and `V̂` has orthonormal columns, then
`‖(I - U Uᵀ) X (I - V̂ V̂ᵀ)‖ ≤ ‖(I - U Uᵀ) X (I - V Vᵀ)‖`. -/
theorem norm_normal_le_of_right {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {V : Matrix n k' ℝ}
    {Va : Matrix n k₂ ℝ} (hVa : Vaᵀ * Va = 1) (h : Va * Vaᵀ * V = V) (U : Matrix m k ℝ)
    (X : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * X * (1 - Va * Vaᵀ)‖ ≤ ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ := by
  rw [← one_sub_rightProj_one_sub_leftProj_apply, ← one_sub_rightProj_one_sub_leftProj_apply]
  exact norm_one_sub_rightProj_le hVa h _

/-- The normal component never exceeds the matrix: `‖(I - U Uᵀ) Z (I - V Vᵀ)‖ ≤ ‖Z‖` for
orthonormal `U`, `V`. -/
theorem norm_normal_le [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * Z * (1 - V * Vᵀ)‖ ≤ ‖Z‖ := by
  rw [← one_sub_leftProj_one_sub_rightProj_apply]
  exact ((isOrthProj_leftProj hU).compl.norm_le _).trans
    ((isOrthProj_rightProj hV).compl.norm_le _)

omit [DecidableEq m] [DecidableEq n] in
/-- The factor-level coefficient error is bounded by the full-matrix error:
`‖S - U₁ᵀ A V₁‖ ≤ ‖U₁ S V₁ᵀ - A‖` for `U₁`, `V₁` with orthonormal columns (the first step of
the proof of Lemma 4 of arXiv 2010.02022, read backwards). -/
theorem norm_coeff_sub_le [DecidableEq k] [DecidableEq k'] {U₁ : Matrix m k ℝ}
    {V₁ : Matrix n k' ℝ} (hU : U₁ᵀ * U₁ = 1) (hV : V₁ᵀ * V₁ = 1) (S : Matrix k k' ℝ)
    (A : Matrix m n ℝ) : ‖S - U₁ᵀ * A * V₁‖ ≤ ‖U₁ * S * V₁ᵀ - A‖ := by
  have h1 : ‖S - U₁ᵀ * A * V₁‖ = ‖U₁ * (S - U₁ᵀ * A * V₁) * V₁ᵀ‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  have h2 : U₁ᵀ * (U₁ * S * V₁ᵀ - A) * V₁ = S - U₁ᵀ * A * V₁ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [show U₁ᵀ * (U₁ * S * V₁ᵀ) * V₁ = (U₁ᵀ * U₁) * S * (V₁ᵀ * V₁) by
      simp only [Matrix.mul_assoc], hU, hV, Matrix.one_mul, Matrix.mul_one]
  have h3 : U₁ * (S - U₁ᵀ * A * V₁) * V₁ᵀ = leftProj U₁ (rightProj V₁ (U₁ * S * V₁ᵀ - A)) := by
    rw [leftProj_rightProj_apply, h2]
  rw [h1, h3]
  exact (isOrthProj_leftProj_mul_rightProj hU hV).norm_le _

end Normal

/-! ### Orthonormal bases inside a given range -/

section Capture

variable {m : Type*} [Fintype m]

omit [Fintype m] in
/-- The column space of a product is contained in the column space of the left factor. -/
lemma colSpan_mul_le {k l : Type*} [Fintype k] (A : Matrix m k ℝ) (B : Matrix k l ℝ) :
    colSpan (A * B) ≤ colSpan A := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change WithLp.toLp 2 ((A * B).col j) ∈ colSpan A
  have h : WithLp.toLp 2 ((A * B).col j) = ∑ i, B i j • WithLp.toLp 2 (A.col i) := by
    ext a
    simp [Matrix.mul_apply, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toLp_col_mem_colSpan A i)

omit [Fintype m] in
/-- A matrix is the matrix of its columns. -/
lemma ofCols_toLp_col {k : Type*} (A : Matrix m k ℝ) :
    ofCols (fun j => WithLp.toLp 2 (A.col j)) = A := by
  ext i j
  rfl

/-- If an orthonormal `Û` captures an orthonormal `U₀` (`Û Ûᵀ U₀ = U₀`), then `Û` has at least
as many columns as `U₀`. -/
theorem card_le_of_capture {k ι : Type*} [Fintype k] [Fintype ι] [DecidableEq ι]
    {Ua : Matrix m k ℝ} {U₀ : Matrix m ι ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (h : Ua * Uaᵀ * U₀ = U₀) :
    Fintype.card ι ≤ Fintype.card k :=
  calc Fintype.card ι = U₀.rank := (rank_eq_card_of_transpose_mul_eq_one hU₀).symm
    _ = (Ua * (Uaᵀ * U₀)).rank := by rw [← Matrix.mul_assoc, h]
    _ ≤ Ua.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card k := Ua.rank_le_card_width

/-- **An `r`-column basis inside an augmented basis.**  Let `Û` have orthonormal columns and
capture `K` (`Û Ûᵀ K = K`).  If `rank K ≤ r ≤ card k`, there is `U' : Matrix m (Fin r) ℝ` with
orthonormal columns that captures `K` and lies in the range of `Û` (`Û Ûᵀ U' = U'`).  This is how
the rank-`r` normal-component assumption is transported to the augmented basis of the
rank-adaptive integrator. -/
theorem exists_orthonormal_capture_within {k k₂ : Type*} [Fintype k] [DecidableEq k]
    [Fintype k₂] {Ua : Matrix m k ℝ} (hUa : Uaᵀ * Ua = 1) {K : Matrix m k₂ ℝ}
    (hK : Ua * Uaᵀ * K = K) {r : ℕ} (hKr : K.rank ≤ r) (hr : r ≤ Fintype.card k) :
    ∃ U : Matrix m (Fin r) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ * K = K ∧ Ua * Uaᵀ * U = U := by
  have hWV : colSpan K ≤ colSpan Ua :=
    calc colSpan K = colSpan (Ua * (Uaᵀ * K)) := by rw [← Matrix.mul_assoc, hK]
      _ ≤ colSpan Ua := colSpan_mul_le _ _
  obtain ⟨u, hu, hV, hW⟩ := exists_orthonormal_of_le hWV (r := r)
    (by rw [finrank_colSpan]; exact hKr)
    (by rw [finrank_colSpan, rank_eq_card_of_transpose_mul_eq_one hUa]; exact hr)
  refine ⟨ofCols u, transpose_ofCols_mul_ofCols hu, ofCols_capture hu hW, ?_⟩
  obtain ⟨C, hC⟩ := exists_eq_mul_of_col_mem_span (u := fun j => WithLp.toLp 2 (Ua.col j))
    (X := ofCols u) fun j => by rw [toLp_col_ofCols]; exact hV j
  rw [ofCols_toLp_col] at hC
  exact mul_transpose_mul_eq_of_eq_mul hUa hC

end Capture

/-! ### The factored normal-component assumption -/

section NormalBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/- `FactoredNormalBound` is defined in `LeanDLRA/Integrators/Matrix/Defs.lean`. -/

/-- A constant field `F ≡ C` satisfies the factored normal-component assumption with `ε = ‖C‖`. -/
theorem factoredNormalBound_const (C : Matrix m n ℝ) (r : ℕ) :
    FactoredNormalBound (fun _ _ => C) r ‖C‖ := fun _ _ _ _ hU hV => norm_normal_le hU hV C

/-- **The K-step normal component through an intermediate basis.**  If `U'` (orthonormal, `r`
columns) captures `K₁` and lies in the range of the orthonormal `Û`, then the factored
normal-component assumption gives `‖(1 - P̂) ((1 - Q₀) F(t, K₁ V₀ᵀ))‖ ≤ ε` with
`P̂ = leftProj Û`, `Q₀ = rightProj V₀`.  For `Û = U'` this is the BUG case. -/
theorem kNormal_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε : ℝ}
    (hε : FactoredNormalBound F r ε) {k : Type*} [Fintype k] [DecidableEq k]
    {Ua : Matrix m k ℝ} (hUa : Uaᵀ * Ua = 1) {U' : Matrix m (Fin r) ℝ} (hU' : U'ᵀ * U' = 1)
    (hUaU' : Ua * Uaᵀ * U' = U') {K₁ : Matrix m (Fin r) ℝ} (hK : U' * U'ᵀ * K₁ = K₁)
    {V₀ : Matrix n (Fin r) ℝ} (hV₀ : V₀ᵀ * V₀ = 1) (t : ℝ) :
    ‖(1 - leftProj Ua) ((1 - rightProj V₀) (F t (K₁ * V₀ᵀ)))‖ ≤ ε := by
  rw [one_sub_leftProj_one_sub_rightProj_apply]
  have hK' : K₁ * V₀ᵀ = U' * (U'ᵀ * K₁) * V₀ᵀ := by rw [← Matrix.mul_assoc, hK]
  rw [hK']
  exact (norm_normal_le_of_left hUa hUaU' V₀ _).trans (hε t U' V₀ _ hU' hV₀)

/-- **The L-step normal component through an intermediate basis** (transposed version of
`kNormal_le`): if `V'` (orthonormal, `r` columns) captures `L₁` and lies in the range of the
orthonormal `V̂`, then `‖(1 - Q̂) ((1 - P₀) F(t, U₀ L₁ᵀ))‖ ≤ ε`. -/
theorem lNormal_le {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε : ℝ}
    (hε : FactoredNormalBound F r ε) {k : Type*} [Fintype k] [DecidableEq k]
    {Va : Matrix n k ℝ} (hVa : Vaᵀ * Va = 1) {V' : Matrix n (Fin r) ℝ} (hV' : V'ᵀ * V' = 1)
    (hVaV' : Va * Vaᵀ * V' = V') {L₁ : Matrix n (Fin r) ℝ} (hL : V' * V'ᵀ * L₁ = L₁)
    {U₀ : Matrix m (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (t : ℝ) :
    ‖(1 - rightProj Va) ((1 - leftProj U₀) (F t (U₀ * L₁ᵀ)))‖ ≤ ε := by
  rw [one_sub_rightProj_one_sub_leftProj_apply]
  have hT : L₁ᵀ * V' * V'ᵀ = L₁ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hL
  have hL' : U₀ * L₁ᵀ = U₀ * (L₁ᵀ * V') * V'ᵀ := by
    rw [Matrix.mul_assoc U₀, hT]
  rw [hL']
  exact (norm_normal_le_of_right hVa hVaV' U₀ _).trans (hε t U₀ V' _ hU₀ hV')

end NormalBound

/-! ### One step of the matrix BUG integrator -/

section StepDef

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **One step of the matrix BUG integrator** of Ceruti–Lubich (arXiv 2010.02022, §3.1) from
`Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`, at the level of the factors:

* K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and a new basis `U₁` with `U₁ᵀ U₁ = I` capturing
  `K(t₁)` (`U₁ U₁ᵀ K(t₁) = K(t₁)`, the QR step `K(t₁) = U₁ R₁`, see `kCap_of_qr`);
* L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ`, and `V₁` with `V₁ᵀ V₁ = I`,
  `V₁ V₁ᵀ L(t₁) = L(t₁)`;
* S-step `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, `S(t₀) = M S₀ Nᵀ` with `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`.

The new approximation is `Y₁ = U₁ S(t₁) V₁ᵀ`. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ)
    (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
    (S : ℝ → Matrix (Fin r) (Fin r) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- The new left basis captures `K(t₁)` (QR step). -/
  kCap : U₁ * U₁ᵀ * K t₁ = K t₁
  orthV₁ : V₁ᵀ * V₁ = 1
  /-- The new right basis captures `L(t₁)` (QR step). -/
  lCap : V₁ * V₁ᵀ * Lf t₁ = Lf t₁
  /-- Galerkin S-step `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`. -/
  sSol : ODESolution (sField U₁ V₁ F) S t₀ t₁
  /-- `S(t₀) = M S₀ Nᵀ` with `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`. -/
  sStart : S t₀ = U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁)

/-- A QR factorization `K₁ = U₁ R₁` with `U₁ᵀ U₁ = I` gives the capture `U₁ U₁ᵀ K₁ = K₁`. -/
theorem kCap_of_qr {k l : Type*} [Fintype k] [DecidableEq k] {U₁ : Matrix m k ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) {K₁ : Matrix m l ℝ} {R₁ : Matrix k l ℝ} (h : K₁ = U₁ * R₁) :
    U₁ * U₁ᵀ * K₁ = K₁ :=
  mul_transpose_mul_eq_of_eq_mul hU₁ h

namespace IsStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}

/-- The full-space K-step trajectory starts at `Y₀`: `K(t₀) V₀ᵀ = U₀ S₀ V₀ᵀ`. -/
lemma yk_start (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) : K t₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [hs.kStart]

/-- The full-space L-step trajectory starts at `Y₀`: `U₀ L(t₀)ᵀ = U₀ S₀ V₀ᵀ`. -/
lemma yl_start (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    U₀ * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The full-space S-step trajectory starts at the Galerkin projection of `Y₀`:
`U₁ S(t₀) V₁ᵀ = U₁ U₁ᵀ Y₀ V₁ V₁ᵀ`. -/
lemma ys_start (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    U₁ * S t₀ * V₁ᵀ = leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) := by
  rw [hs.sStart, leftProj_rightProj_apply]
  simp only [Matrix.mul_assoc]

/-- The new left basis captures the full K-step trajectory: `P₁ (K(t₁) V₀ᵀ) = K(t₁) V₀ᵀ`. -/
lemma yk_cap (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    leftProj U₁ (K t₁ * V₀ᵀ) = K t₁ * V₀ᵀ := by
  rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]

/-- The new right basis captures the full L-step trajectory: `Q₁ (U₀ L(t₁)ᵀ) = U₀ L(t₁)ᵀ`. -/
lemma yl_cap (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) :
    rightProj V₁ (U₀ * (Lf t₁)ᵀ) = U₀ * (Lf t₁)ᵀ := by
  have hT : (Lf t₁)ᵀ * V₁ * V₁ᵀ = (Lf t₁)ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
  rw [rightProj_apply, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hT]

end IsStep

end StepDef

section Step

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

namespace IsStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {Lf : ℝ → Matrix n (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ}

/-- **The factor trajectories satisfy the abstract hypotheses** (pointwise normal-component
version).  One step of the matrix BUG integrator (`IsStep`) is an abstract BUG step
(`IsBUGStep`) with `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`, `P₁ = leftProj U₁`,
`Q₁ = rightProj V₁`, `Y₀ = U₀ S₀ V₀ᵀ` and the full-space trajectories `YK = K V₀ᵀ`,
`YL = U₀ Lᵀ`, `YS = U₁ S V₁ᵀ`, provided the normal components at `K(t₁) V₀ᵀ` and
`U₀ L(t₁)ᵀ` are `ε`-small. -/
theorem isBUGStep_of_normal (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) {ε : ℝ}
    (hεK : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - U₁ * U₁ᵀ) * F t (K t₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hεL : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - U₀ * U₀ᵀ) * F t (U₀ * (Lf t₁)ᵀ) * (1 - V₁ * V₁ᵀ)‖ ≤ ε) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => U₁ * S t * V₁ᵀ) where
  projP₀ := isOrthProj_leftProj hs.orthU₀
  projQ₀ := isOrthProj_rightProj hs.orthV₀
  projP₁ := isOrthProj_leftProj hs.orthU₁
  projQ₁ := isOrthProj_rightProj hs.orthV₁
  comm₁ := leftProj_rightProj_comm U₁ V₁
  kSol := odeSolution_kField hs.kSol
  kStart := hs.yk_start
  kCap := hs.yk_cap
  kNormal t ht := by
    rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact hεK t ht
  lSol := odeSolution_lField hs.lSol
  lStart := hs.yl_start
  lCap := hs.yl_cap
  lNormal t ht := by
    rw [one_sub_rightProj_one_sub_leftProj_apply]
    exact hεL t ht
  sSol := odeSolution_sField hs.sSol
  sStart := hs.ys_start

/-- **The factor trajectories satisfy the abstract hypotheses** under the factored
normal-component assumption at rank `r` (`FactoredNormalBound F r ε`): it is applied at
`K(t₁) V₀ᵀ = U₁ (U₁ᵀ K(t₁)) V₀ᵀ` and at `U₀ L(t₁)ᵀ = U₀ (L(t₁)ᵀ V₁) V₁ᵀ`. -/
theorem isBUGStep (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S) {ε : ℝ}
    (hε : FactoredNormalBound F r ε) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => U₁ * S t * V₁ᵀ) where
  projP₀ := isOrthProj_leftProj hs.orthU₀
  projQ₀ := isOrthProj_rightProj hs.orthV₀
  projP₁ := isOrthProj_leftProj hs.orthU₁
  projQ₁ := isOrthProj_rightProj hs.orthV₁
  comm₁ := leftProj_rightProj_comm U₁ V₁
  kSol := odeSolution_kField hs.kSol
  kStart := hs.yk_start
  kCap := hs.yk_cap
  kNormal t _ := kNormal_le hε hs.orthU₁ hs.orthU₁
    (by rw [Matrix.mul_assoc, hs.orthU₁, Matrix.mul_one]) hs.kCap hs.orthV₀ t
  lSol := odeSolution_lField hs.lSol
  lStart := hs.yl_start
  lCap := hs.yl_cap
  lNormal t _ := lNormal_le hε hs.orthV₁ hs.orthV₁
    (by rw [Matrix.mul_assoc, hs.orthV₁, Matrix.mul_one]) hs.lCap hs.orthU₀ t
  sSol := odeSolution_sField hs.sSol
  sStart := hs.ys_start

/-! #### Robust error bounds (Ceruti–Lubich, Lemmas 2–4 and Theorem 4) -/

section Errors

variable {L B ε h : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Lemma 2 of arXiv 2010.02022 (matrix form, explicit constant).**  The new left basis
captures the exact solution: `‖(I - U₁ U₁ᵀ) A(t₁)‖ ≤ ϑ`, `ϑ = h (4 L B h + ε)`. -/
theorem capture_left (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖(1 - U₁ * U₁ᵀ) * A t₁‖ ≤ h * (4 * L * B * h + ε) := by
  have hb := hs.isBUGStep hε
  have h1 := kstep_capture hF hL hB hb.projP₁ hb.projQ₀ ht₁ hh hA hb.kSol
    (hb.kStart.trans hA₀.symm) hb.kCap hb.kNormal
  rwa [one_sub_leftProj_apply] at h1

/-- **Lemma 2 of arXiv 2010.02022 for the L-step (matrix form).**  The new right basis captures
the exact solution: `‖A(t₁) (I - V₁ V₁ᵀ)‖ ≤ ϑ`, `ϑ = h (4 L B h + ε)`. -/
theorem capture_right (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖A t₁ * (1 - V₁ * V₁ᵀ)‖ ≤ h * (4 * L * B * h + ε) := by
  have hb := hs.isBUGStep hε
  have h1 := kstep_capture hF hL hB hb.projQ₁ hb.projP₀ ht₁ hh hA hb.lSol
    (hb.lStart.trans hA₀.symm) hb.lCap hb.lNormal
  rwa [one_sub_rightProj_apply] at h1

/-- **Lemma 3 of arXiv 2010.02022 (matrix form).**
`‖U₁ U₁ᵀ A(t₁) V₁ V₁ᵀ - A(t₁)‖ ≤ 2ϑ`, `ϑ = h (4 L B h + ε)`. -/
theorem capture (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * U₁ᵀ * A t₁ * V₁ * V₁ᵀ - A t₁‖ ≤ 2 * (h * (4 * L * B * h + ε)) := by
  have hb := hs.isBUGStep hε
  have h1 := bug_capture hF hL hB hb.projP₀ hb.projQ₀ hb.projP₁ hb.projQ₁ ht₁ hh hA hb.kSol
    (hb.kStart.trans hA₀.symm) hb.kCap hb.kNormal hb.lSol (hb.lStart.trans hA₀.symm) hb.lCap
    hb.lNormal
  rw [norm_sub_rev]
  simpa [Matrix.mul_assoc] using h1

/-- **Robust local error of the matrix BUG integrator** (Ceruti–Lubich, arXiv 2010.02022,
Lemma 4, explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B` in the
Frobenius norm and satisfy the factored normal-component assumption at rank `r`.  If
`A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, with `A(t₀) = Y₀ = U₀ S₀ V₀ᵀ`, then
the BUG step `Y₁ = U₁ S(t₁) V₁ᵀ` satisfies, with `ϑ = h (4 L B h + ε)`,

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (B h + 2ϑ) + 2ϑ. -/
theorem local_error (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * S t₁ * V₁ᵀ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) :=
  (hs.isBUGStep hε).local_error hF hL hB ht₁ hh hA hA₀

/-- **Robust local error of the matrix BUG integrator, `O`-form** (Ceruti–Lubich,
arXiv 2010.02022, Lemma 4): for `0 ≤ h ≤ H`,
`‖U₁ S(t₁) V₁ᵀ - A(t₁)‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, independent
of the singular values of `A` and of the factors. -/
theorem local_error_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * S t₁ * V₁ᵀ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  (hs.isBUGStep hε).local_error_le hF hL hB ht₁ hh hhH hA hA₀

/-- **Factor-level local error** (the quantity `‖S₁ - U₁ᵀ A₁ V₁‖` estimated in the proof of
Lemma 4 of arXiv 2010.02022): for `0 ≤ h ≤ H`,
`‖S(t₁) - U₁ᵀ A(t₁) V₁‖ ≤ h (c₁ ε + c₂ h)`. -/
theorem coeff_error_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖S t₁ - U₁ᵀ * A t₁ * V₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  (norm_coeff_sub_le hs.orthU₁ hs.orthV₁ _ _).trans
    (hs.local_error_le hε hF hL hB ht₁ hh hhH hA hA₀)

end Errors

end IsStep

section Global

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε : ℝ}

/-- **Robust global error bound of the matrix BUG integrator** (Ceruti–Lubich,
arXiv 2010.02022, Theorem 4, explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and
bounded by `B` and satisfy the factored normal-component assumption at rank `r`; let
`tⱼ = t₀ + j h` with `0 ≤ h ≤ H` and let `A` solve `A' = F(t, A)` on `[t₀, t₀ + N h]`.  For
`j < N` let step `j` of the BUG integrator (`IsStep`) go from `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` to
`Yⱼ₊₁ = Uⱼ₊₁ Sⱼ₊₁ Vⱼ₊₁ᵀ` with `Sⱼ₊₁ = S⁽ʲ⁾(tⱼ₊₁)`, and let `Φ j` be the exact flow on
`[tⱼ, tⱼ₊₁]` started at `Yⱼ`.  Then for `j ≤ N`

    ‖Yⱼ - A(tⱼ)‖ ≤ e^{L j h} (‖Y₀ - A(t₀)‖ + j h (c₁ ε + c₂ h)),

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : FactoredNormalBound F r ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * (j * h)) *
      (‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ + j * h * (bugC₁ L H * ε + bugC₂ L B H * h)) :=
  bug_global_error hF hL hB hh hhH hA (P := fun j => leftProj (U j))
    (Q := fun j => rightProj (V j)) (Y := fun j => U j * Sm j * (V j)ᵀ)
    (YK := fun j t => K j t * (V j)ᵀ) (YL := fun j t => U j * (Lf j t)ᵀ)
    (YS := fun j t => U (j + 1) * S j t * (V (j + 1))ᵀ)
    (fun j hj => (hstep j hj).isBUGStep hε) (fun j hj => by simp only [hS j hj]) hΦ hΦ₀

/-- **Robust global error bound of the matrix BUG integrator, final form** (Ceruti–Lubich,
arXiv 2010.02022, Theorem 4 = Theorem 2 verbatim for the new integrator): under the hypotheses
of `global_error`, with `‖Y₀ - A(t₀)‖ ≤ δ`, `ε ≥ 0` and `j h ≤ T`,

    ‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁' ε + c₂' h,

`c₀ = e^{L T}`, `c₁' = T e^{L T} bugC₁ L H`, `c₂' = T e^{L T} bugC₂ L B H`, depending only on
`L`, `B`, `T` and the step-size bound `H`. -/
theorem global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : FactoredNormalBound F r ε) (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H)
    {N : ℕ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ j < N, IsStep F (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (U (j + 1))
      (V (j + 1)) (K j) (Lf j) (S j))
    (hS : ∀ j < N, Sm (j + 1) = S j (t₀ + (j + 1) * h))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h :=
  bug_global_error_le hF hL hB hε₀ hh hhH hA (P := fun j => leftProj (U j))
    (Q := fun j => rightProj (V j)) (Y := fun j => U j * Sm j * (V j)ᵀ)
    (YK := fun j t => K j t * (V j)ᵀ) (YL := fun j t => U j * (Lf j t)ᵀ)
    (YS := fun j t => U (j + 1) * S j t * (V (j + 1))ᵀ)
    (fun j hj => (hstep j hj).isBUGStep hε) (fun j hj => by simp only [hS j hj]) hΦ hΦ₀ hδ

end Global

end Step

/-! ### The rank-adaptive BUG integrator for matrices -/

section RankAdaptive

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq k]
  [DecidableEq k'] {r : ℕ}

/-- **One step of the matrix rank-adaptive BUG integrator** of Ceruti–Kusch–Lubich
(arXiv 2104.05247, §2.1) from `Y₀ = U₀ S₀ V₀ᵀ` (rank `r`) at `t₀` to `t₁`, at the level of the
factors:

* K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`,
  `L(t₀) = V₀ S₀ᵀ` (eqs. (3)–(4));
* augmented bases `Û = Ua` (`m × k`, e.g. `k = 2r`) and `V̂ = Va` (`n × k'`) with orthonormal
  columns whose ranges contain those of `(K(t₁), U₀)` and `(L(t₁), V₀)`;
* S-step `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂`, `Ŝ(t₀) = M̂ S₀ N̂ᵀ` with `M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀` (eq. (5)),
  giving `Ŷ₁ = Û Ŝ(t₁) V̂ᵀ` (eq. (7));
* truncation: the new approximation `Y₁` satisfies `‖Y₁ - Ŷ₁‖ ≤ ϑ` (eq. (6); for the truncated
  SVD of `Ŝ(t₁)` see `trunc_of_coeff`). -/
structure IsRankAdaptiveStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (ϑ : ℝ) (t₀ t₁ : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Ua : Matrix m k ℝ) (Va : Matrix n k' ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
    (Lf : ℝ → Matrix n (Fin r) ℝ) (Sa : ℝ → Matrix k k' ℝ) (Y₁ : Matrix m n ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  /-- L-step `L' = F(t, U₀ Lᵀ)ᵀ U₀`. -/
  lSol : ODESolution (lField U₀ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ
  orthUa : Uaᵀ * Ua = 1
  /-- `Û` captures `K(t₁)`. -/
  kCap : Ua * Uaᵀ * K t₁ = K t₁
  /-- `Û` captures `U₀` (augmentation). -/
  augU : Ua * Uaᵀ * U₀ = U₀
  orthVa : Vaᵀ * Va = 1
  /-- `V̂` captures `L(t₁)`. -/
  lCap : Va * Vaᵀ * Lf t₁ = Lf t₁
  /-- `V̂` captures `V₀` (augmentation). -/
  augV : Va * Vaᵀ * V₀ = V₀
  /-- Galerkin S-step `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂` in the augmented bases. -/
  sSol : ODESolution (sField Ua Va F) Sa t₀ t₁
  /-- `Ŝ(t₀) = M̂ S₀ N̂ᵀ` with `M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀`. -/
  sStart : Sa t₀ = Uaᵀ * U₀ * S₀ * (V₀ᵀ * Va)
  /-- Truncation to the tolerance `ϑ`. -/
  trunc : ‖Y₁ - Ua * Sa t₁ * Vaᵀ‖ ≤ ϑ

/-- The truncation is measured on the small matrix: if `Y₁ = Û T V̂ᵀ` with `‖T - Ŝ(t₁)‖ ≤ ϑ`
(e.g. `T = P̂_{r₁} Σ̂_{r₁} Q̂_{r₁}ᵀ` from the truncated SVD of `Ŝ(t₁)`, step 3 of the algorithm of
arXiv 2104.05247), then `‖Y₁ - Ŷ₁‖ ≤ ϑ`. -/
theorem trunc_of_coeff {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} (hUa : Uaᵀ * Ua = 1)
    (hVa : Vaᵀ * Va = 1) {T Ŝ : Matrix k k' ℝ} {ϑ : ℝ} (h : ‖T - Ŝ‖ ≤ ϑ) :
    ‖Ua * T * Vaᵀ - Ua * Ŝ * Vaᵀ‖ ≤ ϑ := by
  rwa [← Matrix.sub_mul, ← Matrix.mul_sub, Frobenius.norm_mul_transpose_of_orthonormal hVa,
    Frobenius.norm_mul_of_orthonormal hUa]

namespace IsRankAdaptiveStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ϑ t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Ua : Matrix m k ℝ}
  {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ}

/-- The augmented left basis has at least `r` columns. -/
lemma le_card_left (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    r ≤ Fintype.card k := by
  simpa using card_le_of_capture hs.orthU₀ hs.augU

/-- The augmented right basis has at least `r` columns. -/
lemma le_card_right (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    r ≤ Fintype.card k' := by
  simpa using card_le_of_capture hs.orthV₀ hs.augV

/-- An `r`-column orthonormal basis `U'` capturing `K(t₁)` inside the range of `Û`. -/
lemma exists_kBasis (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    ∃ U' : Matrix m (Fin r) ℝ, U'ᵀ * U' = 1 ∧ U' * U'ᵀ * K t₁ = K t₁ ∧ Ua * Uaᵀ * U' = U' :=
  exists_orthonormal_capture_within hs.orthUa hs.kCap
    (by simpa using (K t₁).rank_le_card_width) hs.le_card_left

/-- An `r`-column orthonormal basis `V'` capturing `L(t₁)` inside the range of `V̂`. -/
lemma exists_lBasis (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    ∃ V' : Matrix n (Fin r) ℝ, V'ᵀ * V' = 1 ∧ V' * V'ᵀ * Lf t₁ = Lf t₁ ∧ Va * Vaᵀ * V' = V' :=
  exists_orthonormal_capture_within hs.orthVa hs.lCap
    (by simpa using (Lf t₁).rank_le_card_width) hs.le_card_right

/-- The augmented left basis captures `Y₀`: `Û Ûᵀ Y₀ = Y₀`. -/
lemma aug_left (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    leftProj Ua (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
  rw [leftProj_apply]
  simp only [← Matrix.mul_assoc]
  rw [hs.augU]

/-- The augmented right basis captures `Y₀`: `Y₀ V̂ V̂ᵀ = Y₀`. -/
lemma aug_right (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    rightProj Va (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
  have hT : V₀ᵀ * Va * Vaᵀ = V₀ᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.augV
  rw [rightProj_apply, Matrix.mul_assoc (U₀ * S₀), Matrix.mul_assoc (U₀ * S₀), hT]

/-- The augmented S-step starts at the Galerkin projection of `Y₀`. -/
lemma ys_start (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    Ua * Sa t₀ * Vaᵀ = leftProj Ua (rightProj Va (U₀ * S₀ * V₀ᵀ)) := by
  rw [hs.sStart, leftProj_rightProj_apply]
  simp only [Matrix.mul_assoc]

/-- **Lemma 1 of arXiv 2104.05247 (matrix form).**  The augmented Galerkin step starts at `Y₀`:
`Û Ŝ(t₀) V̂ᵀ = Û M̂ S₀ N̂ᵀ V̂ᵀ = U₀ S₀ V₀ᵀ`. -/
theorem start_eq (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁) :
    Ua * Sa t₀ * Vaᵀ = U₀ * S₀ * V₀ᵀ := by
  rw [hs.ys_start, hs.aug_right, hs.aug_left]

variable [DecidableEq m] [DecidableEq n]

/-- **The factor trajectories satisfy the abstract hypotheses.**  One step of the matrix
rank-adaptive BUG integrator (`IsRankAdaptiveStep`) is an abstract rank-adaptive step
(`IsRankAdaptiveBUGStep`) with `P₀ = leftProj U₀`, `Q₀ = rightProj V₀`, the augmented projectors
`P̂ = leftProj Û`, `Q̂ = rightProj V̂`, `Y₀ = U₀ S₀ V₀ᵀ` and `YK = K V₀ᵀ`, `YL = U₀ Lᵀ`,
`YS = Û Ŝ V̂ᵀ`, under the factored normal-component assumption at rank `r`.  The normal
component at `YK(t₁) = K(t₁) V₀ᵀ` is controlled through an `r`-column basis `U'` capturing
`K(t₁)` inside the range of `Û` (`exists_kBasis`) and the range monotonicity
`‖(I - Û Ûᵀ) X (I - V₀ V₀ᵀ)‖ ≤ ‖(I - U' U'ᵀ) X (I - V₀ V₀ᵀ)‖` (`norm_normal_le_of_left`);
likewise for the L-step. -/
theorem isRankAdaptiveBUGStep (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    {ε : ℝ} (hε : FactoredNormalBound F r ε) :
    IsRankAdaptiveBUGStep F ε ϑ (leftProj U₀) (rightProj V₀) (leftProj Ua) (rightProj Va) t₀ t₁
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => Ua * Sa t * Vaᵀ) Y₁ where
  projP₀ := isOrthProj_leftProj hs.orthU₀
  projQ₀ := isOrthProj_rightProj hs.orthV₀
  projP₁ := isOrthProj_leftProj hs.orthUa
  projQ₁ := isOrthProj_rightProj hs.orthVa
  comm₁ := leftProj_rightProj_comm Ua Va
  kSol := odeSolution_kField hs.kSol
  kStart := by rw [hs.kStart]
  kCap := by rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
  kNormal t _ := by
    obtain ⟨U', hU', hcap, hin⟩ := hs.exists_kBasis
    exact kNormal_le hε hs.orthUa hU' hin hcap hs.orthV₀ t
  lSol := odeSolution_lField hs.lSol
  lStart := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  lCap := by
    have hT : (Lf t₁)ᵀ * Va * Vaᵀ = (Lf t₁)ᵀ := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hs.lCap
    rw [rightProj_apply, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hT]
  lNormal t _ := by
    obtain ⟨V', hV', hcap, hin⟩ := hs.exists_lBasis
    exact lNormal_le hε hs.orthVa hV' hin hcap hs.orthU₀ t
  sSol := odeSolution_sField hs.sSol
  sStart := hs.ys_start
  augP := hs.aug_left
  augQ := hs.aug_right
  trunc := hs.trunc

variable {L B ε h : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Robust local error of the matrix rank-adaptive BUG integrator** (Ceruti–Kusch–Lubich,
arXiv 2104.05247, Theorem 2, local form with explicit constants): for `0 ≤ h ≤ H`,
`‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h) + ϑ` with `c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`, where `ε` is the
normal-component bound at the rank `r` of `Y₀`. -/
theorem local_error_le (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖Y₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ :=
  (hs.isRankAdaptiveBUGStep hε).local_error_le hF hL hB ht₁ hh hhH hA hA₀

/-- **Local error of the untruncated rank-adaptive step, factor level**:
`‖Ŝ(t₁) - Ûᵀ A(t₁) V̂‖ ≤ ‖Ŷ₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h)`. -/
theorem coeff_error_le (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hε : FactoredNormalBound F r ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖Sa t₁ - Uaᵀ * A t₁ * Va‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) :=
  (norm_coeff_sub_le hs.orthUa hs.orthVa _ _).trans
    ((hs.isRankAdaptiveBUGStep hε).toIsBUGStep.local_error_le hF hL hB ht₁ hh hhH hA hA₀)

end IsRankAdaptiveStep

section Global

variable [DecidableEq m] [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε ϑ : ℝ}

/-- **Robust global error bound of the matrix rank-adaptive BUG integrator**
(Ceruti–Kusch–Lubich, arXiv 2104.05247, Theorem 2, explicit constants).  Let `F` be
`L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `tⱼ = t₀ + j h` with `0 ≤ h ≤ H`, and `A` a solution
of `A' = F(t, A)` on `[t₀, t₀ + N h]`.  The rank `rⱼ` may change from step to step: step `j`
(`IsRankAdaptiveStep`) goes from `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` of rank `rⱼ` (with augmented bases of
`kⱼ`, `k'ⱼ` columns) to the truncated `Yⱼ₊₁ = Uⱼ₊₁ Sⱼ₊₁ Vⱼ₊₁ᵀ` of rank `rⱼ₊₁`, with truncation
tolerance `ϑ`; the normal component of `F` is `ε`-small at rank `rⱼ` (condition 2 of
Theorem 2).  With `Φ j` the exact flow on `[tⱼ, tⱼ₊₁]` from `Yⱼ`, `‖Y₀ - A(t₀)‖ ≤ δ`, `ε ≥ 0`
and `j h ≤ T`:

    ‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ j ϑ,

`c₀ = c₃ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L H`, `c₂ = T e^{L T} bugC₂ L B H`. -/
theorem rankAdaptive_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {r ka kb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Ua : (j : ℕ) → Matrix m (Fin (ka j)) ℝ}
    {Va : (j : ℕ) → Matrix n (Fin (kb j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sa : (j : ℕ) → ℝ → Matrix (Fin (ka j)) (Fin (kb j)) ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hε : ∀ j < N, FactoredNormalBound F (r j) ε)
    (hstep : ∀ j < N, IsRankAdaptiveStep F ϑ (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j)
      (Ua j) (Va j) (K j) (Lf j) (Sa j) (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ))
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + (j + 1) * h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * j * ϑ :=
  rankAdaptiveBUG_global_error_le hF hL hB hε₀ hh hhH hA (P := fun j => leftProj (U j))
    (Q := fun j => rightProj (V j)) (Pa := fun j => leftProj (Ua j))
    (Qa := fun j => rightProj (Va j)) (Y := fun j => U j * Sm j * (V j)ᵀ)
    (YK := fun j t => K j t * (V j)ᵀ) (YL := fun j t => U j * (Lf j t)ᵀ)
    (YS := fun j t => Ua j * Sa j t * (Va j)ᵀ)
    (fun j hj => (hstep j hj).isRankAdaptiveBUGStep (hε j hj)) hΦ hΦ₀ hδ

end Global

end RankAdaptive

/-! ### Well-posedness: the steps exist -/

section WellPosed

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L B : ℝ}

/-- **The QR step exists** (arXiv 2010.02022, §3.1): for `r ≤ m` every `K₁ ∈ ℝ^{m×r}` (also
rank-deficient) admits `U₁ ∈ ℝ^{m×r}` with `U₁ᵀ U₁ = I` and `U₁ U₁ᵀ K₁ = K₁`. -/
theorem exists_qr (hr : r ≤ Fintype.card m) (K₁ : Matrix m (Fin r) ℝ) :
    ∃ U₁ : Matrix m (Fin r) ℝ, U₁ᵀ * U₁ = 1 ∧ U₁ * U₁ᵀ * K₁ = K₁ :=
  exists_orthonormal_capture_of_le_card K₁ hr

/-- **The augmented QR step exists** (arXiv 2104.05247, §2.1): for `2 r ≤ m` there is
`Û ∈ ℝ^{m×2r}` with orthonormal columns capturing `K₁` and `U₀`. -/
theorem exists_aug_qr (hr : 2 * r ≤ Fintype.card m) (K₁ U₀ : Matrix m (Fin r) ℝ) :
    ∃ Ua : Matrix m (Fin (2 * r)) ℝ, Uaᵀ * Ua = 1 ∧ Ua * Uaᵀ * K₁ = K₁ ∧ Ua * Uaᵀ * U₀ = U₀ :=
  exists_augmented_basis K₁ U₀ hr

/-- **Well-posedness of one BUG step.**  If `F` is Lipschitz, bounded and continuous in time,
`U₀`, `V₀` have orthonormal columns and `r ≤ m`, `r ≤ n`, then for every `S₀` and `t₀ ≤ t₁`
the K-, L- and S-steps have solutions and the QR bases exist: there are `U₁`, `V₁`, `K`, `L`,
`S` forming a step of the matrix BUG integrator (`IsStep`). -/
theorem exists_isStep (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ),
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ V₁ K Lf S := by
  obtain ⟨K, hK, hK₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t x => kField_eq V₀ t x) h01
    (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t x => lField_eq U₀ t x)
    h01 (V₀ * S₀ᵀ)
  obtain ⟨U₁, hU₁, hKcap⟩ := exists_qr hrm (K t₁)
  obtain ⟨V₁, hV₁, hLcap⟩ := exists_qr hrn (Lf t₁)
  obtain ⟨S, hS, hS₀⟩ := exists_odeSolution_conj hF hB hc _ _
    (fun t x => sField_eq U₁ V₁ t x) h01 (U₁ᵀ * U₀ * S₀ * (V₀ᵀ * V₁))
  exact ⟨U₁, V₁, K, Lf, S, hU₀, hV₀, hK, hK₀, hLf, hLf₀, hU₁, hKcap, hV₁, hLcap, hS, hS₀⟩

/-- **Well-posedness of one rank-adaptive BUG step** (before truncation).  Under the
assumptions of `exists_isStep` with `2 r ≤ m`, `2 r ≤ n`, there are augmented bases
`Û ∈ ℝ^{m×2r}`, `V̂ ∈ ℝ^{n×2r}` and substep solutions forming a step of the matrix rank-adaptive
integrator with the untruncated result `Y₁ = Ŷ₁ = Û Ŝ(t₁) V̂ᵀ` (any `ϑ ≥ 0`). -/
theorem exists_isRankAdaptiveStep (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    {U₀ : Matrix m (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hrm : 2 * r ≤ Fintype.card m)
    (hrn : 2 * r ≤ Fintype.card n) {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    ∃ (Ua : Matrix m (Fin (2 * r)) ℝ) (Va : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sa : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ),
      IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa (Ua * Sa t₁ * Vaᵀ) := by
  obtain ⟨K, hK, hK₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t x => kField_eq V₀ t x) h01
    (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := exists_odeSolution_conj hF hB hc _ _ (fun t x => lField_eq U₀ t x)
    h01 (V₀ * S₀ᵀ)
  obtain ⟨Ua, hUa, hKcap, haugU⟩ := exists_aug_qr hrm (K t₁) U₀
  obtain ⟨Va, hVa, hLcap, haugV⟩ := exists_aug_qr hrn (Lf t₁) V₀
  obtain ⟨Sa, hSa, hSa₀⟩ := exists_odeSolution_conj hF hB hc _ _
    (fun t x => sField_eq Ua Va t x) h01 (Uaᵀ * U₀ * S₀ * (V₀ᵀ * Va))
  exact ⟨Ua, Va, K, Lf, Sa, hU₀, hV₀, hK, hK₀, hLf, hLf₀, hUa, hKcap, haugU, hVa, hLcap, haugV,
    hSa, hSa₀, by simpa using hϑ⟩

end WellPosed

/-! ### Satisfiability of the hypotheses -/

section Examples

/-- The first unit vector of `ℝ²` as a `2 × 1` matrix (an orthonormal basis of rank `1`). -/
noncomputable def unitCol : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

@[simp] lemma unitCol_apply (i : Fin 2) (j : Fin 1) : unitCol i j = if i = 0 then 1 else 0 :=
  rfl

lemma unitCol_orth : unitColᵀ * unitCol = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply]

/-- For `F ≡ I` (the `2 × 2` identity) the normal component at `Y₀ = e₁ e₁ᵀ` does not vanish:
`(I - e₁ e₁ᵀ) I (I - e₁ e₁ᵀ) = e₂ e₂ᵀ ≠ 0`, so the examples below are not tangential. -/
lemma normal_unitCol_ne_zero :
    (1 - unitCol * unitColᵀ) * (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 - unitCol * unitColᵀ) ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Matrix.one_apply] at h11

/-- A solution of an ODE whose field is constant (`f t x = c`) is affine. -/
lemma odeSolution_of_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {c : E} (hf : ∀ t x, f t x = c) (y₀ : E) (a b : ℝ) :
    ODESolution f (fun t => y₀ + (t - a) • c) a b := by
  have hfe : f = fun _ _ => c := funext fun t => funext fun x => hf t x
  subst hfe
  exact odeSolution_affine y₀ c a b

/-- The K-step (and L-step) solution of the examples: `K(t) = (1 + t) e₁`. -/
noncomputable def exK : ℝ → Matrix (Fin 2) (Fin 1) ℝ := fun t => unitCol + (t - 0) • unitCol

/-- The S-step solution of the BUG example: `S(t) = 1 + t`. -/
noncomputable def exS : ℝ → Matrix (Fin 1) (Fin 1) ℝ := fun t => 1 + (t - 0) • 1

/-- The augmented S-step solution of the rank-adaptive example: `Ŝ(t) = e₁ e₁ᵀ + t I`. -/
noncomputable def exSa : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t => unitCol * unitColᵀ + (t - 0) • 1

/-- The exact solution of the examples: `A(t) = e₁ e₁ᵀ + t I`. -/
noncomputable def exA : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t => unitCol * (1 : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ + (t - 0) • 1

/-- **One BUG step for a non-tangential field** (satisfiability of `IsStep`): `F ≡ I` on
`2 × 2` matrices, `Y₀ = e₁ · 1 · e₁ᵀ` of rank `1`, `U₀ = V₀ = U₁ = V₁ = e₁`, on `[0, 1]`, with the
explicit affine substep solutions `K = L = exK`, `S = exS`. -/
theorem isStep_example :
    IsStep (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 unitCol 1 unitCol unitCol unitCol exK
      exK exS where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_of_const (fun _ _ => by simp [kField]) _ _ _
  kStart := by simp [exK]
  lSol := odeSolution_of_const (fun _ _ => by simp [lField]) _ _ _
  lStart := by simp [exK]
  orthU₁ := unitCol_orth
  kCap := kCap_of_qr unitCol_orth (R₁ := 1 + (1 - 0 : ℝ) • 1) (by simp [exK, Matrix.mul_add])
  orthV₁ := unitCol_orth
  lCap := kCap_of_qr unitCol_orth (R₁ := 1 + (1 - 0 : ℝ) • 1) (by simp [exK, Matrix.mul_add])
  sSol := odeSolution_of_const (fun _ _ => by simp [sField, unitCol_orth]) _ _ _
  sStart := by simp [exS, unitCol_orth]

/-- The hypotheses of the local error bound `IsStep.local_error_le` are jointly satisfiable for
the non-tangential example `isStep_example` (`L = 0`, `B = ε = ‖I‖`, `h = H = 1`, exact solution
`A(t) = Y₀ + t I`). -/
example : ‖unitCol * exS 1 * unitColᵀ - exA 1‖ ≤ 1 * (bugC₁ 0 1 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      + bugC₂ 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 * 1) :=
  isStep_example.local_error_le (factoredNormalBound_const _ 1) (fun _ _ _ => by simp) le_rfl
    (fun _ _ => le_rfl) (by norm_num) zero_le_one le_rfl (odeSolution_of_const (fun _ _ => rfl)
      (unitCol * (1 : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ) 0 1) (by simp [exA])

/-- **One rank-adaptive step with a genuine truncation** (satisfiability of
`IsRankAdaptiveStep`): `F ≡ I`, `Y₀ = e₁ e₁ᵀ` (rank `1`), augmented bases `Û = V̂ = I` (rank
`2`), untruncated result `Ŷ₁ = diag(2, 1)`, truncated to rank `1`: `Y₁ = e₁ (2) e₁ᵀ = diag(2, 0)`
with tolerance `ϑ = 1`. -/
theorem isRankAdaptiveStep_example :
    IsRankAdaptiveStep (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 1 unitCol 1 unitCol 1 1
      exK exK exSa (unitCol * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ) where
  orthU₀ := unitCol_orth
  orthV₀ := unitCol_orth
  kSol := odeSolution_of_const (fun _ _ => by simp [kField]) _ _ _
  kStart := by simp [exK]
  lSol := odeSolution_of_const (fun _ _ => by simp [lField]) _ _ _
  lStart := by simp [exK]
  orthUa := by simp
  kCap := by simp
  augU := by simp
  orthVa := by simp
  lCap := by simp
  augV := by simp
  sSol := odeSolution_of_const (fun _ _ => by simp [sField]) _ _ _
  sStart := by simp [exSa]
  trunc := by
    rw [Frobenius.norm_def]
    norm_num [exSa, Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply]

/-- The hypotheses of the rank-adaptive local error bound are jointly satisfiable, with a
genuine truncation (`isRankAdaptiveStep_example`). -/
example : ‖unitCol * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ - exA 1‖ ≤
      1 * (bugC₁ 0 1 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
        + bugC₂ 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 * 1) + 1 :=
  isRankAdaptiveStep_example.local_error_le (factoredNormalBound_const _ 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (by norm_num) zero_le_one le_rfl
    (odeSolution_of_const (fun _ _ => rfl) (unitCol * (1 : Matrix (Fin 1) (Fin 1) ℝ) * unitColᵀ)
      0 1) (by simp [exA])

/-- The hypotheses of the global error bound `global_error_le` (Ceruti–Lubich, Theorem 4) are
jointly satisfiable: one step (`N = 1`, `h = H = T = 1`) of the non-tangential example
`isStep_example`, exact solution `A(t) = e₁ e₁ᵀ + t I`, exact flow `Φ₀ = A`, `δ = 0`. -/
example : ‖unitCol * exS 1 * unitColᵀ - exA 1‖ ≤
    Real.exp (0 * 1) * 0 + 1 * Real.exp (0 * 1) * bugC₁ 0 1 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      + 1 * Real.exp (0 * 1) * bugC₂ 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 * 1 := by
  have h := global_error_le (F := fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) (r := 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (factoredNormalBound_const _ 1)
    (norm_nonneg _) (t₀ := 0) (h := 1) (H := 1) zero_le_one le_rfl (N := 1) (A := exA)
    (odeSolution_of_const (fun _ _ => rfl) _ _ _) (U := fun _ => unitCol)
    (Sm := fun j => if j = 0 then 1 else exS 1) (V := fun _ => unitCol) (K := fun _ => exK)
    (Lf := fun _ => exK) (S := fun _ => exS) (Φ := fun _ => exA)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using isStep_example)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      norm_num)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      have h0 : ODESolution (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) exA 0 1 :=
        odeSolution_of_const (fun _ _ => rfl) _ _ _
      simpa only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] using h0)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simp [exA])
    (δ := 0) (T := 1) (by simp [exA]) 1 le_rfl (by norm_num)
  simpa using h

/-- The hypotheses of the rank-adaptive global error bound `rankAdaptive_global_error_le`
(Ceruti–Kusch–Lubich, Theorem 2) are jointly satisfiable, with a genuine truncation: one step
(`N = 1`, `h = H = T = 1`) of `isRankAdaptiveStep_example`, ranks `r₀ = r₁ = 1`, augmented
bases with `2` columns, `ϑ = 1`, `δ = 0`. -/
example : ‖unitCol * ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * unitColᵀ - exA 1‖ ≤
    Real.exp (0 * 1) * 0 + 1 * Real.exp (0 * 1) * bugC₁ 0 1 * ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      + 1 * Real.exp (0 * 1) * bugC₂ 0 ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ 1 * 1
      + Real.exp (0 * 1) * 1 * 1 := by
  have h := rankAdaptive_global_error_le (F := fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (norm_nonneg _) (t₀ := 0) (h := 1)
    (H := 1) zero_le_one le_rfl (N := 1) (A := exA)
    (odeSolution_of_const (fun _ _ => rfl) _ _ _) (r := fun _ => 1) (ka := fun _ => 2)
    (kb := fun _ => 2) (U := fun _ => unitCol)
    (Sm := fun j => if j = 0 then 1 else (2 : ℝ) • 1) (V := fun _ => unitCol)
    (Ua := fun _ => 1) (Va := fun _ => 1) (K := fun _ => exK) (Lf := fun _ => exK)
    (Sa := fun _ => exSa) (Φ := fun _ => exA) (ϑ := 1)
    (fun _ _ => factoredNormalBound_const _ 1)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using isRankAdaptiveStep_example)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      have h0 : ODESolution (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) exA 0 1 :=
        odeSolution_of_const (fun _ _ => rfl) _ _ _
      simpa only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] using h0)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simp [exA])
    (δ := 0) (T := 1) (by simp [exA]) 1 le_rfl (by norm_num)
  simpa using h

end Examples

end MatrixBUG

end LeanDLRA
