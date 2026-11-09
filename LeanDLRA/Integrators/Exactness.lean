import LeanDLRA.Foundations.ODE
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.LinearAlgebra.Frobenius.Defs

/-!
# Exactness of low-rank integrators for rank-`r` data

Let `A(t)` be a matrix path of rank `r` and consider the right-hand side `F(t, Y) = Ȧ(t)`, which
does not depend on `Y`.  The remarkable *exactness property* states that the projector-splitting
(KSL) integrator, the basis-update & Galerkin (BUG) integrator and the rank-adaptive (augmented)
BUG integrator started from `Y₀ = A(t₀)` reproduce `A(t₁)` exactly after one step:

* Lubich–Oseledets, *A projector-splitting integrator for dynamical low-rank approximation*,
  arXiv:1301.1058, **Theorem 4.1** (KSL);
* Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank approximation*,
  arXiv:2010.02022, **Lemma 1**, **Theorem 1** (restatement of LO 4.1) and **Theorem 3** (BUG);
* Ceruti–Kusch–Lubich, *A rank-adaptive robust integrator for dynamical low-rank approximation*,
  arXiv:2104.05247, **Theorem 1** (augmented BUG, before truncation);
* Ceruti–Kusch–Lubich, *A parallel rank-adaptive integrator for dynamical low-rank
  approximation*, arXiv:2304.05660, §3: the parallel BUG integrator does **not** have the
  exactness property.  We prove the exact defect formula
  `Ŷ₁ = A₁ - (I - U₀U₀ᵀ)(A₁ - A₀)(I - V₀V₀ᵀ)` for the *untruncated* parallel update, so that
  this update is exact iff the doubly-normal part of the increment vanishes, and we give a
  concrete rank-one example where the untruncated update is not exact (the final truncation
  step of the integrator is not formalized).
* Ceruti–Lubich, arXiv:2010.02022, **Theorem 6** (Tucker BUG): only the Galerkin core-step
  part, for `d` abstract mode projectors (`tucker_exact_abstract`); the matricization layer is
  not formalized, see below.

## Mathematical content

For a `Y`-independent right-hand side every substep is an explicit increment: the K-step gives
`K(t₁) = U₀S₀ + (A₁ - A₀)V₀`, which equals `A₁V₀` when `Y₀ = U₀S₀V₀ᵀ = A₀` and `V₀ᵀV₀ = I`.
The key observation (CL Lemma 1, proof of LO Theorem 4.1) needs no rank theory: if
`A₁ = U S Vᵀ` (`r` columns, `S` possibly singular) with `G = Vᵀ V₀` invertible, then
`A₁ = A₁ V₀ G⁻¹ Vᵀ = K₁ G⁻¹ Vᵀ`, so any matrix `P` with `P K₁ = K₁` (e.g. `P = U₁U₁ᵀ` for the QR
factor `U₁` of `K₁`) satisfies `P A₁ = A₁`.  Everything else is
bookkeeping with the identities `U₀ᵀU₀ = I`, `V₀ᵀV₀ = I`.

## Formalization choices

All results except `IsDerivRHS`, `ODESolution.eq_add_map_sub` and the `IsBUGStep.*`,
`IsKSLStep.*`, `IsParallelBUGStep.*` corollaries live in the namespace `LeanDLRA.Exactness`.

* **Abstract layer** (`Abstract` section): on a real normed space `E` with arbitrary continuous
  linear maps (no projector or inner-product structure is needed), substeps are full-space
  trajectories `y' = Π F(t, y)` in the sense of `ODESolution`.  We prove that such a trajectory
  with `F(t,Y) = Ȧ(t)` is `y(t) = y(t₀) + Π (A(t) - A(t₀))`
  (`ODESolution.eq_add_map_sub`, via `constant_of_has_deriv_right_zero`) and derive abstract
  exactness for the Galerkin/BUG, augmented BUG and KSL steps, and the defect formula for the
  parallel BUG step.
* **Matrix layer** (`MatrixAlgebra` section): pure algebra over an arbitrary commutative ring
  (in particular `ℝ`), with the exact substep solutions written as explicit increments.  QR
  decompositions are replaced by *capture* hypotheses `U₁ U₁ᵀ K₁ = K₁` (implied by any QR
  decomposition `K₁ = U₁ R₁` with `U₁ᵀU₁ = I`, see `capture_of_qr`).  Orthonormality of the new
  bases is not needed for exactness and is therefore not assumed.  The rank assumption of the
  papers enters only through a factorization `A₁ = U S Vᵀ` with `Vᵀ V₀` (resp. `Uᵀ U₀`)
  invertible; `S` may be singular (rank `A₁ ≤ r`, as in LO Theorem 4.1) and orthonormality of
  `U`, `V` is not needed either.
* **ODE layer** (`MatrixODE` section): with the Frobenius norm, the factor ODEs of the
  K-, L- and S-steps with `F(t,Y) = Ȧ(t)` have the explicit increments as solutions, giving the
  exactness theorems for the actual ODE-based integrators.
* **Explicit results and criteria** (`ExplicitAbstract`, `MatrixExplicit` sections): without
  any rank assumption, the BUG step returns `P₁ Q₁ A(t₁)` (`U₁U₁ᵀ A₁ V₁V₁ᵀ`, `bug_eq_proj`) and
  the KSL step returns `P₁ A(t₁)` (`U₁U₁ᵀ A₁`, `ksl_eq_proj`), so these integrators are exact
  *iff* the new bases capture `A(t₁)` (`bug_exact_iff`, `ksl_exact_iff`): the conclusion of CL
  Lemma 1 is necessary and sufficient.
* **Abstract non-degeneracy** (`IsRecoverable`, `capture_abstract`): the argument of CL Lemma 1
  on an abstract space.  The non-degeneracy is the existence of a continuous linear map `T`
  that commutes with every operator of a class `𝓛` *fixed in advance* (independently of the new
  projector `P₁`, which is only required to belong to `𝓛`) and maps `Q₀ A(t₁)` back to
  `A(t₁)`.  For matrices, `𝓛` is the class of left multiplications (`leftMulClass`); then the
  commuting maps are exactly the right multiplications (`exists_mul_right_of_commute`), the
  condition is equivalent to the range condition `A₁ = A₁ V₀ C` and independent of `P₁`
  (`isRecoverable_leftMulClass_iff`), and it follows from the non-degeneracy hypothesis
  `Vᵀ V₀` invertible of the papers (`isRecoverable_leftMulClass_of_isUnit`).  It is strictly
  stronger than the capture conclusion (`RankOneExample.not_isRecoverable_B₁`).  For an
  abstract class the theorem is only as informative as the class: for `𝓛 = {P₁}` the
  hypothesis is essentially equivalent to `P₁ A(t₁) = A(t₁)`.
* **Paper form and multi-step exactness**: `isUnit_transpose_mul_of_eq` transfers invertibility
  of `V(t₁)ᵀV(t₀)` (exact factors, as in the papers) to `V(t₁)ᵀV₀` (factor of `Y₀`), giving
  `bug_exact_of_factors`, `ksl_exact_of_factors`, `augBug_exact_of_factors` (algebraic layer)
  and `bug_exact_ode_of_factors`, `ksl_exact_ode_of_factors` (ODE layer) under weakened forms
  of the hypotheses of CL Theorems 1, 3 and CKL Theorem 1 (only the endpoints enter, `S(t₁)`
  may be singular, `U(t₁)`, `V(t₁)` need not be orthonormal, and the KSL versions do not use
  the `U`-overlap), and by induction the exactness on a whole time grid
  (`bug_exact_multistep`, `ksl_exact_multistep`).  `exists_bug_trajectory_exact` shows that
  the matrix BUG integrator with orthonormal bases is well defined (via the QR step of
  `Matrix/Orthonormal.lean`); the trajectory it constructs (like every such trajectory, by
  `bug_exact_multistep`) is exact.
* **Bundled steps**: `IsBUGStep.exact` / `IsBUGStep.exact_iff`, `IsKSLStep.exact` /
  `IsKSLStep.exact_iff` and `IsParallelBUGStep.eq_of_isDerivRHS` /
  `IsParallelBUGStep.exact_iff` specialize the above to the step structures of
  `Integrators/BUG.lean`, `Integrators/ProjectorSplitting.lean` and
  `Integrators/ParallelBUG.lean`; `IsBUGStep.exact_matrix` and `IsKSLStep.exact_matrix` are
  the matrix instances (`P = U Uᵀ ·`, `Q = · V Vᵀ`), where the recoverability hypotheses are
  derived from the invertibility of the overlaps `Uᵀ U₀`, `Vᵀ V₀`.
* **Examples** (`RankOneExample`): the hypotheses are jointly satisfiable with `A₁ ≠ A₀`, in
  the algebraic, ODE and bundled forms (`isBUGStep_exact`, `isKSLStep_exact`: genuine rank-one
  BUG and KSL steps on `2 × 2` matrices); the untruncated parallel BUG update is not exact
  (`parBug_not_exact`); and the non-degeneracy hypothesis on `V(t₁)ᵀ V(t₀)` cannot be dropped
  when the QR factor of a rank-deficient `K₁` is arbitrary (`not_exact_of_degenerate`: a
  rank-one path from `e₁e₁ᵀ` to `e₂e₂ᵀ`).

The SVD truncation of the rank-adaptive and parallel integrators (which leaves `A(t₁)`
unchanged when the tolerance is below its smallest nonzero singular value) and the
tensor-specific matricization layer of the Tucker integrator (the identification of the mode
projectors and mode classes through matricizations, and the derivation of the recoverability
hypotheses from the multilinear-rank and overlap assumptions of CL Theorem 6) are not
formalized.
-/

open Set
open scoped Matrix

namespace LeanDLRA

/-! ## Abstract layer -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The right-hand side `F` equals `Ȧ(t)` on `[t₀, t₁]`, independently of the state: `A` is
continuous on `[t₀, t₁]` and has right derivative `F t Y` at every `t ∈ [t₀, t₁)`, for every
state `Y`. -/
structure IsDerivRHS (F : ℝ → E → E) (A : ℝ → E) (t₀ t₁ : ℝ) : Prop where
  cont : ContinuousOn A (Icc t₀ t₁)
  deriv : ∀ t ∈ Ico t₀ t₁, ∀ Y, HasDerivWithinAt A (F t Y) (Ici t) t

/-- **Explicit solution for a state-independent right-hand side.**  If `y' = f(t, y)` on
`[a, b]` and along the solution `f(t, y(t)) = Φ (Ȧ(t))` for a continuous linear map `Φ`, then
`y(t) = y(a) + Φ (A(t) - A(a))`. -/
theorem ODESolution.eq_add_map_sub {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : ℝ → E' → E'} {y : ℝ → E'} {a b : ℝ} (hy : ODESolution f y a b) (Φ : E →L[ℝ] E')
    {A A' : ℝ → E} (hAc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Ico a b, HasDerivWithinAt A (A' t) (Ici t) t)
    (hf : ∀ t ∈ Ico a b, f t (y t) = Φ (A' t)) :
    ∀ t ∈ Icc a b, y t = y a + Φ (A t - A a) := by
  have hc : ContinuousOn (fun t => y t - Φ (A t)) (Icc a b) :=
    hy.cont.sub (Φ.continuous.comp_continuousOn hAc)
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => y t - Φ (A t)) 0 (Ici t) t := by
    intro t ht
    have h1 := hy.deriv t ht
    have h2 := Φ.hasFDerivAt.comp_hasDerivWithinAt t (hA t ht)
    rw [hf t ht] at h1
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  intro t ht
  have h := constant_of_has_deriv_right_zero hc hd t ht
  rw [map_sub]
  calc y t = (y t - Φ (A t)) + Φ (A t) := by abel
    _ = (y a - Φ (A a)) + Φ (A t) := by rw [h]
    _ = y a + (Φ (A t) - Φ (A a)) := by abel

end Abstract

/-! The integrator-specific results live in the namespace `LeanDLRA.Exactness`. -/

namespace Exactness

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a constant field `f ≡ c` the affine path `t ↦ y₀ + t c` is a solution (used in the
examples). -/
theorem odeSolution_add_smul_of_const {f : ℝ → E → E} {c : E} (hf : ∀ t x, f t x = c) (y₀ : E)
    (a b : ℝ) : ODESolution f (fun t => y₀ + t • c) a b :=
  ⟨by fun_prop, fun t _ => by
    rw [hf]
    simpa using ((hasDerivWithinAt_id t (Ici t)).smul_const c).const_add y₀⟩

/-- The straight path `A(t) = A₀ + t c` has `Ȧ = c` (used in the examples). -/
theorem isDerivRHS_add_smul (A₀ c : E) (a b : ℝ) :
    IsDerivRHS (fun _ _ => c) (fun t => A₀ + t • c) a b :=
  have h := odeSolution_add_smul_of_const (f := fun _ _ => c) (fun _ _ => rfl) A₀ a b
  ⟨h.cont, fun t ht _ => h.deriv t ht⟩

/-- A Galerkin-type substep `y' = Π F(t, y)` with `F(t, Y) = Ȧ(t)` is the explicit increment
`y(t) = y(t₀) + Π (A(t) - A(t₀))`. -/
theorem galerkin_eq_add {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (hA : IsDerivRHS F A t₀ t₁)
    (Pg : E →L[ℝ] E) {f : ℝ → E → E} (hf : ∀ t Y, f t Y = Pg (F t Y)) {y : ℝ → E}
    (hy : ODESolution f y t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, y t = y t₀ + Pg (A t - A t₀) :=
  hy.eq_add_map_sub Pg (A' := fun t => F t (y t)) hA.cont (fun t ht => hA.deriv t ht (y t))
    (fun t _ => hf t (y t))

/-- **Abstract exactness of a Galerkin step** (the S-step of BUG-type integrators).
If `Π A(t₁) = A(t₁)`, the Galerkin trajectory `y' = Π F(t, y)` with `F(t,Y) = Ȧ(t)` started at
`y(t₀) = Π Y₀` reaches `y(t₁) = Π Y₀ + Π (A(t₁) - A(t₀)) = A(t₁)`, provided
`Π A(t₀) = Π Y₀` (e.g. `Y₀ = A(t₀)`). -/
theorem galerkin_exact {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Pg : E →L[ℝ] E} {y : ℝ → E}
    (hy : ODESolution (fun t Y => Pg (F t Y)) y t₀ t₁) {Y₀ : E} (h0 : y t₀ = Pg Y₀)
    (hY₀ : Pg (A t₀) = Pg Y₀) (h1 : Pg (A t₁) = A t₁) : y t₁ = A t₁ := by
  rw [galerkin_eq_add hA Pg (fun _ _ => rfl) hy t₁ ⟨ht, le_rfl⟩, h0, map_sub, h1, hY₀]
  abel

/-- **Abstract BUG exactness** (Ceruti–Lubich, arXiv:2010.02022, Thm 3, abstract form).
The S-step `y' = P₁ Q₁ F(t, y)`, `y(t₀) = P₁ Q₁ A(t₀)`, with `F(t,Y) = Ȧ(t)` returns `A(t₁)` as
soon as the new left and right projectors capture `A(t₁)`.  (For matrices the capture
hypotheses are provided by `left_capture` and `right_capture`.) -/
theorem bug_exact_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₁ : E →L[ℝ] E} {y : ℝ → E}
    (hy : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) y t₀ t₁) (h0 : y t₀ = P₁ (Q₁ (A t₀)))
    (hP₁ : P₁ (A t₁) = A t₁) (hQ₁ : Q₁ (A t₁) = A t₁) : y t₁ = A t₁ :=
  galerkin_exact (Pg := P₁ * Q₁) ht hA hy h0 rfl (by simp [hQ₁, hP₁])

/-- **Abstract augmented-BUG exactness** (Ceruti–Kusch–Lubich, arXiv:2104.05247, Thm 1,
abstract form, before truncation).  The augmented projectors `P̂`, `Q̂` fix the starting value
`Y₀ = A(t₀)`, the S-step starts at `Y₀` itself, and if `P̂`, `Q̂` capture `A(t₁)` the step is
exact. -/
theorem augBug_exact_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P Q : E →L[ℝ] E} {y : ℝ → E}
    (hy : ODESolution (fun t Y => P (Q (F t Y))) y t₀ t₁) (h0 : y t₀ = A t₀)
    (hP₀ : P (A t₀) = A t₀) (hQ₀ : Q (A t₀) = A t₀)
    (hP₁ : P (A t₁) = A t₁) (hQ₁ : Q (A t₁) = A t₁) : y t₁ = A t₁ :=
  galerkin_exact (Pg := P * Q) (Y₀ := A t₀) ht hA hy (by simp [h0, hQ₀, hP₀]) rfl
    (by simp [hQ₁, hP₁])

/-- **Abstract KSL exactness** (Lubich–Oseledets, arXiv:1301.1058, Thm 4.1, abstract form).
K-step `YK' = Q₀ F`, `YK(t₀) = A(t₀)`; the new left projector captures `YK(t₁)`; backward
S-step `YS' = -P₁ Q₀ F`, `YS(t₀) = YK(t₁)`; L-step `YL' = P₁ F`, `YL(t₀) = YS(t₁)`.
With `F(t,Y) = Ȧ(t)`, `Q₀ A(t₀) = A(t₀)` and `P₁ A(t₁) = A(t₁)` the result is exact. -/
theorem ksl_exact_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₀ : E →L[ℝ] E} {YK YS YL : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₁ (Q₀ (F t Y))) YS t₀ t₁)
    (hYL : ODESolution (fun t Y => P₁ (F t Y)) YL t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hS0 : YS t₀ = YK t₁) (hL0 : YL t₀ = YS t₁)
    (hQ₀ : Q₀ (A t₀) = A t₀) (hcap : P₁ (YK t₁) = YK t₁) (hP₁ : P₁ (A t₁) = A t₁) :
    YL t₁ = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := galerkin_eq_add hA Q₀ (fun _ _ => rfl) hYK t₁ h1
  have eS := galerkin_eq_add hA (-(P₁ * Q₀)) (fun _ _ => rfl) hYS t₁ h1
  have eL := galerkin_eq_add hA P₁ (fun _ _ => rfl) hYL t₁ h1
  have eS' : YS t₁ = YS t₀ - P₁ (Q₀ (A t₁ - A t₀)) := by
    rw [eS, sub_eq_add_neg (YS t₀)]; rfl
  rw [hK0, map_sub, hQ₀] at eK
  have hK : YK t₁ = Q₀ (A t₁) := by rw [eK]; abel
  rw [hK] at hcap
  rw [eL, hL0, eS', hS0, hK]
  simp only [map_sub, hcap, hQ₀, hP₁]
  abel

/-- **Abstract parallel BUG step** (Ceruti–Kusch–Lubich, arXiv:2304.05660, §3, abstract form).
K-, L- and S-steps are run in parallel from `Y₀ = A(t₀)` with `P₀ Y₀ = Y₀ = Q₀ Y₀`, and the
result is `Ŷ₁ = YS(t₁) + (I - P₀) YK(t₁) + (I - Q₀) YL(t₁)`.  For `F(t,Y) = Ȧ(t)` and commuting
`P₀`, `Q₀` this equals `A(t₁) - (I - P₀)(I - Q₀)(A(t₁) - A(t₀))` (i.e. `A(t₁)` minus
`normal P₀ Q₀ (A(t₁) - A(t₀))`): the parallel integrator misses exactly the doubly-normal part
of the increment. -/
theorem parBug_eq_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    {YK YL YS : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYL : ODESolution (fun t Y => P₀ (F t Y)) YL t₀ t₁)
    (hYS : ODESolution (fun t Y => P₀ (Q₀ (F t Y))) YS t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hL0 : YL t₀ = A t₀) (hS0 : YS t₀ = A t₀)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) :
    YS t₁ + (1 - P₀) (YK t₁) + (1 - Q₀) (YL t₁) = A t₁ - (1 - P₀) ((1 - Q₀) (A t₁ - A t₀)) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := galerkin_eq_add hA Q₀ (fun _ _ => rfl) hYK t₁ h1
  have eL := galerkin_eq_add hA P₀ (fun _ _ => rfl) hYL t₁ h1
  have eS := galerkin_eq_add hA (P₀ * Q₀) (fun _ _ => rfl) hYS t₁ h1
  have hsub : ∀ (T : E →L[ℝ] E) x, (1 - T) x = x - T x := fun _ _ => rfl
  have hmul : ∀ (T T' : E →L[ℝ] E) x, (T * T') x = T (T' x) := fun _ _ _ => rfl
  rw [eK, eL, eS, hK0, hL0, hS0]
  simp only [hsub, hmul, map_add, map_sub, hP₀, hQ₀, hc]
  abel

/-- The parallel BUG step is exact iff the doubly-normal part of the increment vanishes. -/
theorem parBug_exact_iff_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₀ Q₀ : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    {YK YL YS : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYL : ODESolution (fun t Y => P₀ (F t Y)) YL t₀ t₁)
    (hYS : ODESolution (fun t Y => P₀ (Q₀ (F t Y))) YS t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hL0 : YL t₀ = A t₀) (hS0 : YS t₀ = A t₀)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) :
    YS t₁ + (1 - P₀) (YK t₁) + (1 - Q₀) (YL t₁) = A t₁ ↔
      (1 - P₀) ((1 - Q₀) (A t₁ - A t₀)) = 0 := by
  rw [parBug_eq_abstract ht hA hc hYK hYL hYS hK0 hL0 hS0 hP₀ hQ₀, sub_eq_self]

end Abstract

/-! ## Matrix layer: exact substeps as explicit increments -/

section MatrixAlgebra

variable {R : Type*} [CommRing R] {m n r p q : Type*}
  [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]

/-! ### Elementary helpers -/

omit [Fintype m] in
/-- Reassociation helper: from `A * B = C` get `A * (B * X) = C * X`. -/
theorem mul_mul_eq_of_mul_eq {k l j : Type*} [Fintype k] [Fintype l] {A : Matrix m k R}
    {B : Matrix k l R} {C : Matrix m l R} (h : A * B = C) (X : Matrix l j R) :
    A * (B * X) = C * X := by
  rw [← Matrix.mul_assoc, h]

omit [Fintype m] in
/-- Reassociation helper: from `A * B * C = D` get `A * (B * (C * X)) = D * X`. -/
theorem mul_mul_mul_eq_of_eq {k l i j : Type*} [Fintype k] [Fintype l] [Fintype i]
    {A : Matrix m k R} {B : Matrix k l R} {C : Matrix l i R} {D : Matrix m i R}
    (h : A * B * C = D) (X : Matrix i j R) : A * (B * (C * X)) = D * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

omit [Fintype r] in
/-- A QR decomposition `K = U R` with `UᵀU = I` yields the capture property `U Uᵀ K = K` and
`R = Uᵀ K`. -/
theorem capture_of_qr [DecidableEq p] {U : Matrix m p R} {Rf : Matrix p r R} {K : Matrix m r R}
    (hU : Uᵀ * U = 1) (hK : U * Rf = K) : U * Uᵀ * K = K ∧ Uᵀ * K = Rf := by
  subst hK
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hU, Matrix.one_mul]
  · rw [mul_mul_eq_of_mul_eq hU, Matrix.one_mul]

/-- Capturing a column-partitioned matrix `[K, U]` means capturing both blocks. -/
theorem capture_fromCols {k l : Type*} {P : Matrix m m R} {K : Matrix m k R} {U : Matrix m l R} :
    P * Matrix.fromCols K U = Matrix.fromCols K U ↔ P * K = K ∧ P * U = U := by
  rw [Matrix.mul_fromCols, Matrix.fromCols_ext_iff]

/-! ### Capture of `A(t₁)` (Ceruti–Lubich, Lemma 1) -/

omit [Fintype m] in
/-- **Range condition from a non-degenerate factorization** (proof of Lubich–Oseledets,
arXiv:1301.1058, Theorem 4.1).  If `A = U S Vᵀ` with `r` columns in `U`, `V` (so `rank A ≤ r`;
`S` may be singular) and `G = Vᵀ W` is invertible, then `A = (A W) C` for `C = G⁻¹ Vᵀ`: the
range of `A` is contained in the range of `A W`. -/
theorem exists_eq_mul_mul_of_isUnit [DecidableEq r] {U : Matrix m r R} {S : Matrix r r R}
    {V W : Matrix n r R} {A : Matrix m n R} (hA : A = U * S * Vᵀ) (hG : IsUnit (Vᵀ * W)) :
    ∃ C : Matrix r n R, A = A * W * C := by
  obtain ⟨G, hG⟩ := hG
  have hGi : Vᵀ * W * (G⁻¹ : (Matrix r r R)ˣ).val = 1 := by
    rw [← hG]; exact G.mul_inv
  have h1 : ∀ X : Matrix r n R, Vᵀ * (W * ((G⁻¹ : (Matrix r r R)ˣ).val * X)) = X :=
    fun X => by
      simp only [← Matrix.mul_assoc] at hGi ⊢
      rw [hGi, Matrix.one_mul]
  refine ⟨(G⁻¹ : (Matrix r r R)ˣ).val * Vᵀ, ?_⟩
  subst hA
  simp only [Matrix.mul_assoc, h1]

/-- If `P K = K`, `K = A W` and `A = (A W) C`, then `P A = A`. -/
theorem mul_eq_self_of_capture {k : Type*} [Fintype k] {P : Matrix m m R} {K : Matrix m k R}
    {A : Matrix m n R} {W : Matrix n k R} (hK : K = A * W) (hP : P * K = K)
    (hA : ∃ C : Matrix k n R, A = A * W * C) : P * A = A := by
  obtain ⟨C, hA⟩ := hA
  have h : P * (A * W * C) = A * W * C := by rw [← hK, ← Matrix.mul_assoc, hP]
  rwa [← hA] at h

omit [Fintype m] in
/-- The exact K-step increment: for `Y₀ = U₀ S₀ V₀ᵀ = A₀` with `V₀ᵀ V₀ = I`,
`K₁ = U₀ S₀ + (A₁ - A₀) V₀ = A₁ V₀`. -/
theorem kStep_eq [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) :
    U₀ * S₀ + (A₁ - A₀) * V₀ = A₁ * V₀ := by
  subst hY₀
  rw [Matrix.sub_mul, Matrix.mul_assoc (U₀ * S₀), hV₀, Matrix.mul_one]
  abel

omit [Fintype n] in
/-- The exact L-step increment: for `Y₀ = U₀ S₀ V₀ᵀ = A₀` with `U₀ᵀ U₀ = I`,
`L₁ = V₀ S₀ᵀ + (A₁ - A₀)ᵀ U₀ = A₁ᵀ U₀`. -/
theorem lStep_eq [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} (hU₀ : U₀ᵀ * U₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) :
    V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀ = A₁ᵀ * U₀ := by
  subst hY₀
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_assoc, hU₀, Matrix.mul_one]
  abel

/-- **Ceruti–Lubich, Lemma 1** (left capture).  Let `Y₀ = U₀ S₀ V₀ᵀ = A₀` with `V₀ᵀV₀ = I`, and
let `A₁ = U S Vᵀ` (rank at most `r`) with `Vᵀ V₀` invertible.  If `P` captures the K-step
result
`K₁ = U₀ S₀ + (A₁ - A₀) V₀` (e.g. `P = U₁ U₁ᵀ` with `U₁` the QR factor of `K₁`), then
`P A₁ = A₁`. -/
theorem left_capture [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R}
    {V : Matrix n r R} (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hV : IsUnit (Vᵀ * V₀)) {P : Matrix m m R}
    (hP : P * (U₀ * S₀ + (A₁ - A₀) * V₀) = U₀ * S₀ + (A₁ - A₀) * V₀) : P * A₁ = A₁ :=
  mul_eq_self_of_capture (kStep_eq hV₀ hY₀) hP (exists_eq_mul_mul_of_isUnit hA₁ hV)

/-- **Ceruti–Lubich, Lemma 1** (right capture, via transposition).  Let `Y₀ = U₀ S₀ V₀ᵀ = A₀`
with `U₀ᵀU₀ = I`, and let `A₁ = U S Vᵀ` with `Uᵀ U₀` invertible.  If `Q` captures the
L-step result `L₁ = V₀ S₀ᵀ + (A₁ - A₀)ᵀ U₀`, then `A₁ Qᵀ = A₁`. -/
theorem right_capture [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R}
    {V : Matrix n r R} (hU₀ : U₀ᵀ * U₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hU : IsUnit (Uᵀ * U₀)) {Q : Matrix n n R}
    (hQ : Q * (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀) = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀) : A₁ * Qᵀ = A₁ := by
  have hA₁' : A₁ᵀ = V * Sᵀ * Uᵀ := by
    rw [hA₁]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have h := mul_eq_self_of_capture (lStep_eq hU₀ hY₀) hQ
    (exists_eq_mul_mul_of_isUnit hA₁' hU)
  have h' := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h'

/-! ### (a) BUG exactness -/

/-- **Exactness of the BUG integrator** (Ceruti–Lubich, arXiv:2010.02022, Theorem 3).

One step of the basis-update & Galerkin integrator for `F(t,Y) = Ȧ(t)` from
`Y₀ = U₀ S₀ V₀ᵀ = A₀ = A(t₀)` (orthonormal `U₀`, `V₀`):
* K-step `K₁ = U₀ S₀ + (A₁ - A₀) V₀`, new basis `U₁` capturing `K₁` (QR);
* L-step `L₁ = V₀ S₀ᵀ + (A₁ - A₀)ᵀ U₀`, new basis `V₁` capturing `L₁` (QR);
* S-step `S₁ = M S₀ Nᵀ + U₁ᵀ (A₁ - A₀) V₁` with `M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`.

If `A₁ = A(t₁) = U S Vᵀ` with `Uᵀ U₀` and `Vᵀ V₀` invertible (the non-degeneracy assumption
of CL Theorem 1), then `Y₁ = U₁ S₁ V₁ᵀ = A₁`.
Generalization: `S` need not be invertible (`A₁` may have rank `< r`, as in LO Theorem 4.1), the
new bases may have any number of columns, need not be orthonormal (only the capture property is
used), and the factors `U`, `V` of `A₁` need not be orthonormal. -/
theorem bug_exact [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R} {V : Matrix n r R}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀))
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {U₁ : Matrix m p R} {V₁ : Matrix n q R}
    {S₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hU₁ : U₁ * U₁ᵀ * K₁ = K₁) (hV₁ : V₁ * V₁ᵀ * L₁ = L₁)
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) :
    U₁ * S₁ * V₁ᵀ = A₁ := by
  subst hK₁ hL₁ hS₁
  have hP := left_capture hV₀ hY₀ hA₁ hV hU₁
  have hQ := right_capture hU₀ hY₀ hA₁ hU hV₁
  rw [Matrix.transpose_mul, Matrix.transpose_transpose] at hQ
  have key : U₁ * (U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) * V₁ᵀ =
      U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ) := by
    subst hY₀
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [key, hP, hQ]

/-! ### (b) Projector-splitting (KSL) exactness -/

/-- **Exactness of the projector-splitting integrator, capture form**
(Lubich–Oseledets, arXiv:1301.1058, Theorem 4.1; restated as CL Theorem 1).

One step of the KSL integrator of LO §3.2 for `F(t,Y) = Ȧ(t)` from `Y₀ = U₀ S₀ V₀ᵀ = A₀`
(`V₀ᵀ V₀ = I`): `K₁ = U₀ S₀ + (A₁ - A₀) V₀`; `U₁` captures `K₁` and `Ŝ₁ = U₁ᵀ K₁`;
`S̃₀ = Ŝ₁ - U₁ᵀ (A₁ - A₀) V₀`; `L₁ = V₀ S̃₀ᵀ + (A₁ - A₀)ᵀ U₁`; result `Y₁ = U₁ L₁ᵀ`
(`= U₁ S₁ V₁ᵀ` for `V₁ S₁ᵀ = L₁`).  If `A₁ = U S Vᵀ` (rank at most `r`, `S` may be singular, as
in LO Theorem 4.1) with `Vᵀ V₀` invertible, then `Y₁ = A₁`.  The invertibility of `Vᵀ V₀` is
the assumption made in the proof of LO 4.1 and stated in CL Theorem 1.  LO's perturbation
argument for the degenerate case does not hold for an arbitrary QR factor of a rank-deficient
`K₁` (see `RankOneExample.not_exact_of_degenerate`); it holds only for a suitably chosen
(limit) factor. -/
theorem ksl_exact_capture [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R}
    {V : Matrix n r R} (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hV : IsUnit (Vᵀ * V₀))
    {K₁ : Matrix m r R} {U₁ : Matrix m p R} {Ŝ₁ St₀ : Matrix p r R} {L₁ : Matrix n p R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hU₁ : U₁ * U₁ᵀ * K₁ = K₁) (hŜ₁ : Ŝ₁ = U₁ᵀ * K₁)
    (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁) :
    U₁ * L₁ᵀ = A₁ := by
  have hP : U₁ * U₁ᵀ * A₁ = A₁ := left_capture hV₀ hY₀ hA₁ hV (hK₁ ▸ hU₁)
  have hPr : U₁ * (U₁ᵀ * A₁) = A₁ := by rw [← Matrix.mul_assoc]; exact hP
  have hK : K₁ = A₁ * V₀ := hK₁.trans (kStep_eq hV₀ hY₀)
  have hA₀Q : A₀ * (V₀ * V₀ᵀ) = A₀ := by
    rw [← hY₀]; simp only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hV₀, Matrix.one_mul]
  subst hL₁ hSt₀ hŜ₁ hK
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, mul_mul_mul_eq_of_eq hP, hPr, hA₀Q]
  abel

/-- **Exactness of the projector-splitting integrator** (Lubich–Oseledets, arXiv:1301.1058,
Theorem 4.1), in the QR form of the algorithm of LO §3.2:
`K₁ = U₀ S₀ + ΔA V₀ = U₁ Ŝ₁` (`U₁ᵀ U₁ = I`), `S̃₀ = Ŝ₁ - U₁ᵀ ΔA V₀`,
`L₁ = V₀ S̃₀ᵀ + ΔAᵀ U₁ = V₁ S₁ᵀ`, and `Y₁ = U₁ S₁ V₁ᵀ`, where `ΔA = A₁ - A₀`.
If `Y₀ = U₀ S₀ V₀ᵀ = A₀`, `V₀ᵀ V₀ = I` and `A₁ = U S Vᵀ` (rank at most `r`) with `Vᵀ V₀`
invertible, then `Y₁ = A₁`. -/
theorem ksl_exact [DecidableEq r] [DecidableEq p] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R}
    {V : Matrix n r R} (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hV : IsUnit (Vᵀ * V₀))
    {K₁ : Matrix m r R} {U₁ : Matrix m p R} {Ŝ₁ St₀ : Matrix p r R} {L₁ : Matrix n p R}
    {V₁ : Matrix n q R} {S₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hU₁ : U₁ᵀ * U₁ = 1) (hqrK : U₁ * Ŝ₁ = K₁)
    (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁)
    (hqrL : V₁ * S₁ᵀ = L₁) :
    U₁ * S₁ * V₁ᵀ = A₁ := by
  obtain ⟨hcap, hŜ⟩ := capture_of_qr hU₁ hqrK
  have h := ksl_exact_capture hV₀ hY₀ hA₁ hV hK₁ hcap hŜ.symm hSt₀ hL₁
  rw [← hqrL, Matrix.transpose_mul, Matrix.transpose_transpose] at h
  rwa [Matrix.mul_assoc]

/-! ### (c) Augmented (rank-adaptive) BUG exactness -/

/-- The augmented S-step of Ceruti–Kusch–Lubich (arXiv:2104.05247, §2.1) starts at `Y₀`:
if the augmented bases `Û`, `V̂` capture `U₀` and `V₀`, then
`Û (M̂ S₀ N̂ᵀ) V̂ᵀ = U₀ S₀ V₀ᵀ` with `M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀`. -/
theorem augBug_start {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {Uh : Matrix m p R} {Vh : Matrix n q R} (hUh : Uh * Uhᵀ * U₀ = U₀) (hVh : Vh * Vhᵀ * V₀ = V₀) :
    Uh * (Uhᵀ * U₀ * S₀ * (Vhᵀ * V₀)ᵀ) * Vhᵀ = U₀ * S₀ * V₀ᵀ := by
  have hVh' : V₀ᵀ * (Vh * Vhᵀ) = V₀ᵀ := by
    have h := congrArg Matrix.transpose hVh
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    mul_mul_mul_eq_of_eq hUh, hVh']

/-- **Exactness of the rank-adaptive BUG integrator before truncation**
(Ceruti–Kusch–Lubich, arXiv:2104.05247, Theorem 1).

`Û` (resp. `V̂`) is a basis capturing the augmented matrix `[K₁, U₀]` (resp. `[L₁, V₀]`), i.e.
`Û Ûᵀ [K₁, U₀] = [K₁, U₀]`, the augmented S-step is
`Ŝ₁ = M̂ S₀ N̂ᵀ + Ûᵀ (A₁ - A₀) V̂` with `M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀`.  Under the assumptions of
`bug_exact`, `Ŷ₁ = Û Ŝ₁ V̂ᵀ = A₁`.  (`A₁` has rank at most `r`; a subsequent truncation with
tolerance below the smallest nonzero singular value of `A₁` leaves it unchanged.  The SVD
truncation itself is not formalized here.) -/
theorem augBug_exact [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {U : Matrix m r R} {S : Matrix r r R}
    {V : Matrix n r R} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    (hA₁ : A₁ = U * S * Vᵀ) (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀))
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {Uh : Matrix m p R} {Vh : Matrix n q R}
    {Ŝ₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hUh : Uh * Uhᵀ * Matrix.fromCols K₁ U₀ = Matrix.fromCols K₁ U₀)
    (hVh : Vh * Vhᵀ * Matrix.fromCols L₁ V₀ = Matrix.fromCols L₁ V₀)
    (hŜ₁ : Ŝ₁ = Uhᵀ * U₀ * S₀ * (Vhᵀ * V₀)ᵀ + Uhᵀ * (A₁ - A₀) * Vh) :
    Uh * Ŝ₁ * Vhᵀ = A₁ :=
  bug_exact hU₀ hV₀ hY₀ hA₁ hU hV hK₁ hL₁ (capture_fromCols.mp hUh).1
    (capture_fromCols.mp hVh).1 hŜ₁

/-! ### (d) Parallel BUG: the exactness defect -/

/-- **The parallel BUG step for `F(t,Y) = Ȧ(t)`** (Ceruti–Kusch–Lubich, arXiv:2304.05660, §3.1).

From `Y₀ = U₀ S₀ V₀ᵀ = A₀` with orthonormal `U₀`, `V₀`, the K-, L- and S-steps are computed in
parallel: `K₁ = U₀ S₀ + ΔA V₀`, `L₁ = V₀ S₀ᵀ + ΔAᵀ U₀`, `S̄₁ = S₀ + U₀ᵀ ΔA V₀` (`ΔA = A₁ - A₀`).
The augmented bases `Û = [U₀, Ũ₁]`, `V̂ = [V₀, Ṽ₁]` capture `[U₀, K₁]`, `[V₀, L₁]`, and with
`S̃ᴷ = Ũ₁ᵀ K₁`, `S̃ᴸ = L₁ᵀ Ṽ₁` the augmented coefficient matrix is
`Ŝ₁ = [[S̄₁, S̃ᴸ], [S̃ᴷ, 0]]`.  Then
`Ŷ₁ = Û Ŝ₁ V̂ᵀ = A₁ - (I - U₀ U₀ᵀ) (A₁ - A₀) (I - V₀ V₀ᵀ)`.
No rank or non-degeneracy assumption on `A₁` is needed. -/
theorem parBug_eq [DecidableEq m] [DecidableEq n] [DecidableEq r] {U₀ : Matrix m r R}
    {S₀ : Matrix r r R} {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {Sb₁ : Matrix r r R} {Ut₁ : Matrix m p R}
    {Vt₁ : Matrix n q R} {SK : Matrix p r R} {SL : Matrix r q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hSb₁ : Sb₁ = S₀ + U₀ᵀ * (A₁ - A₀) * V₀)
    (hUh : Matrix.fromCols U₀ Ut₁ * (Matrix.fromCols U₀ Ut₁)ᵀ * Matrix.fromCols U₀ K₁ =
      Matrix.fromCols U₀ K₁)
    (hVh : Matrix.fromCols V₀ Vt₁ * (Matrix.fromCols V₀ Vt₁)ᵀ * Matrix.fromCols V₀ L₁ =
      Matrix.fromCols V₀ L₁)
    (hSK : SK = Ut₁ᵀ * K₁) (hSL : SL = L₁ᵀ * Vt₁) :
    Matrix.fromCols U₀ Ut₁ * Matrix.fromBlocks Sb₁ SL SK 0 * (Matrix.fromCols V₀ Vt₁)ᵀ =
      A₁ - (1 - U₀ * U₀ᵀ) * (A₁ - A₀) * (1 - V₀ * V₀ᵀ) := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] at hUh hVh
  have hK : Ut₁ * (Ut₁ᵀ * K₁) = K₁ - U₀ * (U₀ᵀ * K₁) := by
    have h := (capture_fromCols.mp hUh).2
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [eq_sub_iff_add_eq, add_comm, h]
  have hL : L₁ᵀ * (Vt₁ * Vt₁ᵀ) = L₁ᵀ - L₁ᵀ * (V₀ * V₀ᵀ) := by
    have h := congrArg Matrix.transpose (capture_fromCols.mp hVh).2
    simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose,
      Matrix.mul_add] at h
    rw [eq_sub_iff_add_eq, add_comm, h]
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  subst hSK hSL hSb₁
  rw [hK, Matrix.mul_zero, add_zero, Matrix.mul_assoc U₀, Matrix.mul_assoc L₁ᵀ, hL]
  subst hK₁ hL₁ hY₀
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, mul_mul_eq_of_mul_eq hU₀,
    mul_mul_eq_of_mul_eq hV₀, hU₀, hV₀]
  abel

/-- The parallel BUG step is exact iff the doubly-normal part
`(I - U₀U₀ᵀ)(A₁ - A₀)(I - V₀V₀ᵀ)` of the increment vanishes (cf. Ceruti–Kusch–Lubich,
arXiv:2304.05660, §3: "the parallel integrator does not have the exactness property"). -/
theorem parBug_exact_iff [DecidableEq m] [DecidableEq n] [DecidableEq r] {U₀ : Matrix m r R}
    {S₀ : Matrix r r R} {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {Sb₁ : Matrix r r R} {Ut₁ : Matrix m p R}
    {Vt₁ : Matrix n q R} {SK : Matrix p r R} {SL : Matrix r q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hSb₁ : Sb₁ = S₀ + U₀ᵀ * (A₁ - A₀) * V₀)
    (hUh : Matrix.fromCols U₀ Ut₁ * (Matrix.fromCols U₀ Ut₁)ᵀ * Matrix.fromCols U₀ K₁ =
      Matrix.fromCols U₀ K₁)
    (hVh : Matrix.fromCols V₀ Vt₁ * (Matrix.fromCols V₀ Vt₁)ᵀ * Matrix.fromCols V₀ L₁ =
      Matrix.fromCols V₀ L₁)
    (hSK : SK = Ut₁ᵀ * K₁) (hSL : SL = L₁ᵀ * Vt₁) :
    Matrix.fromCols U₀ Ut₁ * Matrix.fromBlocks Sb₁ SL SK 0 * (Matrix.fromCols V₀ Vt₁)ᵀ = A₁ ↔
      (1 - U₀ * U₀ᵀ) * (A₁ - A₀) * (1 - V₀ * V₀ᵀ) = 0 := by
  rw [parBug_eq hU₀ hV₀ hY₀ hK₁ hL₁ hSb₁ hUh hVh hSK hSL, sub_eq_self]

end MatrixAlgebra

/-! ## ODE layer: the factor ODEs of the integrators

With the Frobenius norm on matrices, the substeps of the integrators are genuine ODEs for the
factors.  For `F(t, Y) = Ȧ(t)` their solutions are the explicit increments used above, which
yields the exactness theorems for the integrators as formulated in the papers. -/

section MatrixODE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]

/-- **Factor ODEs with a state-independent right-hand side.**  If `S' = M F(t, Ψ(S)) N` (for any
reconstruction map `Ψ`, e.g. `Ψ S = U₁ S V₁ᵀ`) and `F(t,Y) = Ȧ(t)`, then
`S(t) = S(t₀) + M (A(t) - A(t₀)) N`.  This covers the S-steps of the BUG, augmented BUG,
parallel BUG and (with `M = -U₁ᵀ`) projector-splitting integrators. -/
theorem factorODE_eq_add {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {t₀ t₁ : ℝ} (hA : IsDerivRHS F A t₀ t₁) (M : Matrix p m ℝ) (N : Matrix n q ℝ)
    (Ψ : Matrix p q ℝ → Matrix m n ℝ) {f : ℝ → Matrix p q ℝ → Matrix p q ℝ}
    (hf : ∀ t S, f t S = M * F t (Ψ S) * N) {S : ℝ → Matrix p q ℝ}
    (hS : ODESolution f S t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, S t = S t₀ + M * (A t - A t₀) * N := by
  intro t ht
  exact hS.eq_add_map_sub (Frobenius.sandwichCLM M N) (A' := fun t => F t (Ψ (S t))) hA.cont
    (fun t ht => hA.deriv t ht _) (fun t _ => by rw [hf]; rfl) t ht

/-- **Exact K-step** (Ceruti–Lubich, arXiv:2010.02022, proof of Lemma 1; Lubich–Oseledets,
arXiv:1301.1058, Lemma 3.1): the solution of `K' = F(t, K V₀ᵀ) V₀` with `F(t,Y) = Ȧ(t)` is
`K(t) = K(t₀) + (A(t) - A(t₀)) V₀`. -/
theorem kStepODE_eq_add {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {t₀ t₁ : ℝ} (hA : IsDerivRHS F A t₀ t₁) {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ}
    (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, K t = K t₀ + (A t - A t₀) * V₀ := by
  classical
  intro t ht
  have h := factorODE_eq_add hA 1 V₀ (fun K => K * V₀ᵀ) (fun t K => by rw [Matrix.one_mul]) hK
    t ht
  rwa [Matrix.one_mul] at h

/-- **Exact L-step**: the solution of `L' = F(t, U₀ Lᵀ)ᵀ U₀` with `F(t,Y) = Ȧ(t)` is
`L(t) = L(t₀) + (A(t) - A(t₀))ᵀ U₀`. -/
theorem lStepODE_eq_add {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {t₀ t₁ : ℝ} (hA : IsDerivRHS F A t₀ t₁) {U₀ : Matrix m r ℝ} {L : ℝ → Matrix n r ℝ}
    (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, L t = L t₀ + (A t - A t₀)ᵀ * U₀ := by
  classical
  intro t ht
  have h := hL.eq_add_map_sub (Frobenius.sandwichTransposeCLM 1 U₀)
    (A' := fun t => F t (U₀ * (L t)ᵀ)) hA.cont (fun t ht => hA.deriv t ht _)
    (fun t _ => by
      change _ = (1 : Matrix n n ℝ) * (F t (U₀ * (L t)ᵀ))ᵀ * U₀
      rw [Matrix.one_mul]) t ht
  change L t = L t₀ + (1 : Matrix n n ℝ) * (A t - A t₀)ᵀ * U₀ at h
  rwa [Matrix.one_mul] at h

/-- **Exactness of the BUG integrator, ODE form** (Ceruti–Lubich, arXiv:2010.02022,
Theorem 3).  The K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, the L-step
`L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ`, new bases `U₁`, `V₁` capturing `K(t₁)`, `L(t₁)`
(e.g. by QR), and the Galerkin S-step `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`, `S(t₀) = M S₀ Nᵀ`
(`M = U₁ᵀ U₀`, `N = V₁ᵀ V₀`), applied to `F(t,Y) = Ȧ(t)` from `Y₀ = U₀ S₀ V₀ᵀ = A(t₀)`, give
`U₁ S(t₁) V₁ᵀ = A(t₁)` whenever `A(t₁) = U S Vᵀ` with `Uᵀ U₀`, `Vᵀ V₀` invertible. -/
theorem bug_exact_ode [DecidableEq r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hA₁ : A t₁ = U * S * Vᵀ)
    (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀))
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀)
    {L : ℝ → Matrix n r ℝ} (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁)
    (hL₀ : L t₀ = V₀ * S₀ᵀ)
    {U₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ} (hU₁ : U₁ * U₁ᵀ * K t₁ = K t₁)
    (hV₁ : V₁ * V₁ᵀ * L t₁ = L t₁) {Sf : ℝ → Matrix p q ℝ}
    (hSf : ODESolution (fun t S => U₁ᵀ * F t (U₁ * S * V₁ᵀ) * V₁) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ) :
    U₁ * Sf t₁ * V₁ᵀ = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := kStepODE_eq_add hA hK t₁ h1
  have eL := lStepODE_eq_add hA hL t₁ h1
  have eS := factorODE_eq_add hA U₁ᵀ V₁ (fun S => U₁ * S * V₁ᵀ) (fun _ _ => rfl) hSf t₁ h1
  rw [hK₀] at eK
  rw [hL₀] at eL
  rw [hSf₀] at eS
  exact bug_exact hU₀ hV₀ hY₀ hA₁ hU hV eK eL hU₁ hV₁ eS

/-- **Exactness of the rank-adaptive BUG integrator before truncation, ODE form**
(Ceruti–Kusch–Lubich, arXiv:2104.05247, Theorem 1).  As `bug_exact_ode`, but the bases `Û`, `V̂`
capture the augmented matrices `[K(t₁), U₀]`, `[L(t₁), V₀]`, and the S-step
`Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂` starts at `Ŝ(t₀) = M̂ S₀ N̂ᵀ` (`M̂ = Ûᵀ U₀`, `N̂ = V̂ᵀ V₀`). -/
theorem augBug_exact_ode [DecidableEq r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hA₁ : A t₁ = U * S * Vᵀ)
    (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀))
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀)
    {L : ℝ → Matrix n r ℝ} (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁)
    (hL₀ : L t₀ = V₀ * S₀ᵀ)
    {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ}
    (hUh : Uh * Uhᵀ * Matrix.fromCols (K t₁) U₀ = Matrix.fromCols (K t₁) U₀)
    (hVh : Vh * Vhᵀ * Matrix.fromCols (L t₁) V₀ = Matrix.fromCols (L t₁) V₀)
    {Sf : ℝ → Matrix p q ℝ}
    (hSf : ODESolution (fun t S => Uhᵀ * F t (Uh * S * Vhᵀ) * Vh) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = Uhᵀ * U₀ * S₀ * (Vhᵀ * V₀)ᵀ) :
    Uh * Sf t₁ * Vhᵀ = A t₁ :=
  bug_exact_ode ht hA hU₀ hV₀ hY₀ hA₁ hU hV hK hK₀ hL hL₀ (capture_fromCols.mp hUh).1
    (capture_fromCols.mp hVh).1 hSf hSf₀

/-- **Exactness of the projector-splitting integrator, ODE form** (Lubich–Oseledets,
arXiv:1301.1058, Lemma 3.1 and Theorem 4.1).  K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`,
QR `K(t₁) = U₁ Ŝ₁`; backward S-step `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, `S(t₀) = Ŝ₁`; L-step
`L' = F(t, U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S(t₁)ᵀ`, QR `L(t₁) = V₁ S₁ᵀ`.  For `F(t,Y) = Ȧ(t)`,
`Y₀ = U₀ S₀ V₀ᵀ = A(t₀)` and `A(t₁) = U S Vᵀ` with `Vᵀ V₀` invertible, `U₁ S₁ V₁ᵀ = A(t₁)`. -/
theorem ksl_exact_ode [DecidableEq r] [DecidableEq p] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hA₁ : A t₁ = U * S * Vᵀ)
    (hV : IsUnit (Vᵀ * V₀))
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀) {U₁ : Matrix m p ℝ} {Ŝ₁ : Matrix p r ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hqrK : U₁ * Ŝ₁ = K t₁) {Sf : ℝ → Matrix p r ℝ}
    (hSf : ODESolution (fun t S => -(U₁ᵀ * F t (U₁ * S * V₀ᵀ) * V₀)) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = Ŝ₁) {L : ℝ → Matrix n p ℝ}
    (hL : ODESolution (fun t L => (F t (U₁ * Lᵀ))ᵀ * U₁) L t₀ t₁) (hL₀ : L t₀ = V₀ * (Sf t₁)ᵀ)
    {V₁ : Matrix n q ℝ} {S₁ : Matrix p q ℝ} (hqrL : V₁ * S₁ᵀ = L t₁) :
    U₁ * S₁ * V₁ᵀ = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := kStepODE_eq_add hA hK t₁ h1
  have eS := factorODE_eq_add hA (-U₁ᵀ) V₀ (fun S => U₁ * S * V₀ᵀ)
    (fun _ _ => by rw [Matrix.neg_mul, Matrix.neg_mul]) hSf t₁ h1
  have eL := lStepODE_eq_add hA hL t₁ h1
  rw [hK₀] at eK
  rw [hL₀] at eL
  have eS' : Sf t₁ = Ŝ₁ - U₁ᵀ * (A t₁ - A t₀) * V₀ := by
    rw [eS, hSf₀, Matrix.neg_mul, Matrix.neg_mul, ← sub_eq_add_neg]
  exact ksl_exact hV₀ hY₀ hA₁ hV eK hU₁ hqrK eS' eL hqrL

/-- **The parallel BUG step, ODE form** (Ceruti–Kusch–Lubich, arXiv:2304.05660, §3.1).  K-step
and L-step as in `bug_exact_ode`, the S-step `S̄' = U₀ᵀ F(t, U₀ S̄ V₀ᵀ) V₀`, `S̄(t₀) = S₀`, all
run in parallel; with augmented bases `[U₀, Ũ₁]`, `[V₀, Ṽ₁]` capturing `[U₀, K(t₁)]`,
`[V₀, L(t₁)]`, the result for `F(t,Y) = Ȧ(t)` is
`A(t₁) - (I - U₀U₀ᵀ)(A(t₁) - A(t₀))(I - V₀V₀ᵀ)`. -/
theorem parBug_eq_ode [DecidableEq m] [DecidableEq n] [DecidableEq r]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀)
    {L : ℝ → Matrix n r ℝ} (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁)
    (hL₀ : L t₀ = V₀ * S₀ᵀ) {Sb : ℝ → Matrix r r ℝ}
    (hSb : ODESolution (fun t S => U₀ᵀ * F t (U₀ * S * V₀ᵀ) * V₀) Sb t₀ t₁) (hSb₀ : Sb t₀ = S₀)
    {Ut₁ : Matrix m p ℝ} {Vt₁ : Matrix n q ℝ}
    (hUh : Matrix.fromCols U₀ Ut₁ * (Matrix.fromCols U₀ Ut₁)ᵀ * Matrix.fromCols U₀ (K t₁) =
      Matrix.fromCols U₀ (K t₁))
    (hVh : Matrix.fromCols V₀ Vt₁ * (Matrix.fromCols V₀ Vt₁)ᵀ * Matrix.fromCols V₀ (L t₁) =
      Matrix.fromCols V₀ (L t₁)) :
    Matrix.fromCols U₀ Ut₁ * Matrix.fromBlocks (Sb t₁) ((L t₁)ᵀ * Vt₁) (Ut₁ᵀ * K t₁) 0 *
        (Matrix.fromCols V₀ Vt₁)ᵀ =
      A t₁ - (1 - U₀ * U₀ᵀ) * (A t₁ - A t₀) * (1 - V₀ * V₀ᵀ) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := kStepODE_eq_add hA hK t₁ h1
  have eL := lStepODE_eq_add hA hL t₁ h1
  have eS := factorODE_eq_add hA U₀ᵀ V₀ (fun S => U₀ * S * V₀ᵀ) (fun _ _ => rfl) hSb t₁ h1
  rw [hK₀] at eK
  rw [hL₀] at eL
  rw [hSb₀] at eS
  exact parBug_eq hU₀ hV₀ hY₀ eK eL eS hUh hVh rfl rfl

end MatrixODE

/-! ## Explicit step results and exactness criteria (abstract) -/

section ExplicitAbstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full-space K-step `YK' = Q₀ F(t, YK)`, `YK(t₀) = A(t₀) = Q₀ A(t₀)`, with
`F(t,Y) = Ȧ(t)` ends at `YK(t₁) = Q₀ A(t₁)` (the matrix identity `K(t₁) = A(t₁) V₀`). -/
theorem kStep_eq_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Q₀ : E →L[ℝ] E} {YK : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁) (hK0 : YK t₀ = A t₀)
    (hQ₀ : Q₀ (A t₀) = A t₀) : YK t₁ = Q₀ (A t₁) := by
  rw [galerkin_eq_add hA Q₀ (fun _ _ => rfl) hYK t₁ ⟨ht, le_rfl⟩, hK0, map_sub, hQ₀]
  abel

/-- **Abstract non-degeneracy condition.**  `x` is *recoverable from `Q x` modulo the class
`𝓛`* if some continuous linear map `T` commuting with every operator of `𝓛` maps `Q x` back
to `x`.

The class `𝓛` is meant to be fixed in advance, independently of the new projector of the
integrator (which is only required to belong to `𝓛`).  For `m × n` matrices, `𝓛` is the class
of all left multiplications `X ↦ M X` (`leftMulClass`) and `Q = rightProj V₀`; the commuting
maps are then exactly the right multiplications (`exists_mul_right_of_commute`), and the
condition says that `x = x V₀ C` for some `C`, i.e. that the column space of `x V₀` contains
that of `x` (`isRecoverable_leftMulClass_iff`).  It follows from the non-degeneracy hypothesis
of Ceruti–Lubich (`isRecoverable_leftMulClass_of_isUnit`).  For a class tailored to one
projector, such as `𝓛 = {P}`, the condition is essentially equivalent to `P x = x` and carries
no rank information. -/
def IsRecoverable (𝓛 : Set (E →L[ℝ] E)) (Q : E →L[ℝ] E) (x : E) : Prop :=
  ∃ T : E →L[ℝ] E, (∀ L ∈ 𝓛, ∀ y, L (T y) = T (L y)) ∧ T (Q x) = x

/-- **The capture argument of Ceruti–Lubich, Lemma 1, abstract form.**  If `P ∈ 𝓛` fixes `Q x`
and `x` is recoverable from `Q x` modulo `𝓛`, then `P x = x`. -/
theorem apply_eq_self_of_isRecoverable {𝓛 : Set (E →L[ℝ] E)} {P Q : E →L[ℝ] E} {x : E}
    (hP : P ∈ 𝓛) (hcap : P (Q x) = Q x) (hrec : IsRecoverable 𝓛 Q x) : P x = x := by
  obtain ⟨T, hT, hTx⟩ := hrec
  rw [← hTx, hT P hP, hcap]

/-- **Abstract form of Ceruti–Lubich, arXiv:2010.02022, Lemma 1.**  Let the K-step end at
`YK(t₁) = Q₀ A(t₁)` (`kStep_eq_abstract`) and let the new projector `P₁` capture it.  The
rank/non-degeneracy assumption of the paper is replaced by the recoverability of `A(t₁)` from
`Q₀ A(t₁)` modulo a class `𝓛` containing `P₁` (`IsRecoverable`).  Then `P₁ A(t₁) = A(t₁)`.

For matrices (`𝓛 = leftMulClass`, `P₁ = leftProj U₁`, `Q₀ = rightProj V₀`) the recoverability
hypothesis does not involve `P₁` and is implied by the non-degeneracy hypothesis of the paper
(`isRecoverable_leftMulClass_of_isUnit`); this recovers `left_capture`.  For an abstract class
the statement is only as strong as the class (see `IsRecoverable`). -/
theorem capture_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Q₀ P₁ : E →L[ℝ] E} {YK : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁) (hK0 : YK t₀ = A t₀)
    (hQ₀ : Q₀ (A t₀) = A t₀) (hcap : P₁ (YK t₁) = YK t₁) {𝓛 : Set (E →L[ℝ] E)}
    (hP₁ : P₁ ∈ 𝓛) (hrec : IsRecoverable 𝓛 Q₀ (A t₁)) : P₁ (A t₁) = A t₁ := by
  rw [kStep_eq_abstract ht hA hYK hK0 hQ₀] at hcap
  exact apply_eq_self_of_isRecoverable hP₁ hcap hrec

/-- **Explicit result of the abstract Galerkin (BUG S-) step**: for `F(t,Y) = Ȧ(t)` and
`YS(t₀) = P₁ Q₁ A(t₀)`, `YS(t₁) = P₁ Q₁ A(t₁)`.  No rank assumption is needed. -/
theorem bug_eq_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₁ : E →L[ℝ] E} {YS : ℝ → E}
    (hYS : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) YS t₀ t₁) (h0 : YS t₀ = P₁ (Q₁ (A t₀))) :
    YS t₁ = P₁ (Q₁ (A t₁)) := by
  have hmul : ∀ x, (P₁ * Q₁) x = P₁ (Q₁ x) := fun _ => rfl
  rw [galerkin_eq_add (Pg := P₁ * Q₁) hA (fun _ _ => rfl) hYS t₁ ⟨ht, le_rfl⟩, h0, hmul]
  simp only [map_sub]
  abel

/-- **Exactness criterion for the abstract BUG step.**  For commuting idempotents `P₁`, `Q₁`,
the S-step with `F(t,Y) = Ȧ(t)` started at `P₁ Q₁ A(t₀)` is exact iff both new projectors
capture `A(t₁)`.  (So the capture property of CL Lemma 1 is necessary as well as sufficient.) -/
theorem bug_exact_iff_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₁ : E →L[ℝ] E} (hP : ∀ x, P₁ (P₁ x) = P₁ x)
    (hQ : ∀ x, Q₁ (Q₁ x) = Q₁ x) (hc : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)) {YS : ℝ → E}
    (hYS : ODESolution (fun t Y => P₁ (Q₁ (F t Y))) YS t₀ t₁) (h0 : YS t₀ = P₁ (Q₁ (A t₀))) :
    YS t₁ = A t₁ ↔ P₁ (A t₁) = A t₁ ∧ Q₁ (A t₁) = A t₁ := by
  rw [bug_eq_abstract ht hA hYS h0]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← h]
      rw [hP, h]
    · conv_lhs => rw [← h]
      rw [← hc, hQ, h]
  · rintro ⟨h1, h2⟩
    rw [h2, h1]

/-- **Explicit result of the abstract KSL step.**  K-step `YK' = Q₀ F`, `YK(t₀) = A(t₀)`;
backward S-step `YS' = -P₁ Q₀ F`, `YS(t₀) = P₁ YK(t₁)` (in matrix form `U₁ Ŝ₁ V₀ᵀ` with
`Ŝ₁ = U₁ᵀ K(t₁)`); L-step `YL' = P₁ F`, `YL(t₀) = YS(t₁)`.  For `F(t,Y) = Ȧ(t)` and
`Q₀ A(t₀) = A(t₀)` the result is `YL(t₁) = P₁ A(t₁)`, whatever the new projector `P₁` is. -/
theorem ksl_eq_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₀ : E →L[ℝ] E} {YK YS YL : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₁ (Q₀ (F t Y))) YS t₀ t₁)
    (hYL : ODESolution (fun t Y => P₁ (F t Y)) YL t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hS0 : YS t₀ = P₁ (YK t₁)) (hL0 : YL t₀ = YS t₁)
    (hQ₀ : Q₀ (A t₀) = A t₀) : YL t₁ = P₁ (A t₁) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hK := kStep_eq_abstract ht hA hYK hK0 hQ₀
  have eS := galerkin_eq_add hA (-(P₁ * Q₀)) (fun _ _ => rfl) hYS t₁ h1
  have eL := galerkin_eq_add hA P₁ (fun _ _ => rfl) hYL t₁ h1
  have eS' : YS t₁ = YS t₀ - P₁ (Q₀ (A t₁ - A t₀)) := by
    rw [eS, sub_eq_add_neg (YS t₀)]; rfl
  rw [eL, hL0, eS', hS0, hK]
  simp only [map_sub, hQ₀]
  abel

/-- The abstract KSL step with `F(t,Y) = Ȧ(t)` is exact iff the new projector captures
`A(t₁)`. -/
theorem ksl_exact_iff_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {P₁ Q₀ : E →L[ℝ] E} {YK YS YL : ℝ → E}
    (hYK : ODESolution (fun t Y => Q₀ (F t Y)) YK t₀ t₁)
    (hYS : ODESolution (fun t Y => -P₁ (Q₀ (F t Y))) YS t₀ t₁)
    (hYL : ODESolution (fun t Y => P₁ (F t Y)) YL t₀ t₁)
    (hK0 : YK t₀ = A t₀) (hS0 : YS t₀ = P₁ (YK t₁)) (hL0 : YL t₀ = YS t₁)
    (hQ₀ : Q₀ (A t₀) = A t₀) : YL t₁ = A t₁ ↔ P₁ (A t₁) = A t₁ := by
  rw [ksl_eq_abstract ht hA hYK hYS hYL hK0 hS0 hL0 hQ₀]

/-- A product of maps each fixing `x` fixes `x`. -/
theorem list_prod_apply_eq_self {l : List (E →L[ℝ] E)} {x : E} (h : ∀ T ∈ l, T x = x) :
    l.prod x = x := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    have hmul : ∀ y, (T * l.prod) y = T (l.prod y) := fun _ => rfl
    rw [List.prod_cons, hmul,
      ih (fun T' hT' => h T' (List.mem_cons_of_mem T hT')), h T List.mem_cons_self]

/-- **Tucker core-step exactness from mode-wise capture** (the Galerkin part of Ceruti–Lubich,
arXiv:2010.02022, Theorem 6, for `d` abstract mode projectors).  For each mode `i < d` the
mode-`i` K-step is the full-space trajectory `YKᵢ' = Qᵢ F(t, YKᵢ)`,
`YKᵢ(t₀) = A(t₀) = Qᵢ A(t₀)`, and the new mode projector `Pᵢ` (`X ↦ X ×ᵢ U¹ᵢU¹ᵢᵀ`) captures
`YKᵢ(t₁)`.  If moreover `A(t₁)` is recoverable from `Qᵢ A(t₁)` modulo a class `𝓛ᵢ` containing
`Pᵢ` (`IsRecoverable`; so that `Pᵢ A(t₁) = A(t₁)` by `capture_abstract`), the core step in
full-space form `y' = (∏ᵢ Pᵢ) F(t, y)`, `y(t₀) = (∏ᵢ Pᵢ) A(t₀)` (i.e. `C(t₀) = C₀ ×ᵢ Mᵢ`)
returns `y(t₁) = A(t₁)`.  The mode projectors need not commute.

This is **not** a formalization of Theorem 6: the tensor-specific layer (the mode classes
`𝓛ᵢ` of operators acting on mode `i` only, the identification of `Qᵢ`, `Pᵢ` through
matricizations, and the derivation of the recoverability hypotheses from the multilinear-rank
and overlap assumptions `Uᵢ(t₁)ᵀ Uᵢ(t₀)` invertible, i.e. Lemma 1 on each matricization) is
not formalized.  For `d = 2` (matrices, `𝓛 = ![leftMulClass, rightMulClass]`) the hypotheses
are derived from the overlap assumptions by `isRecoverable_leftMulClass_of_isUnit` and
`isRecoverable_rightMulClass_of_isUnit`; see `RankOneExample.tucker_two_exact` for a
non-trivial instance. -/
theorem tucker_exact_abstract {F : ℝ → E → E} {A : ℝ → E} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {d : ℕ} {P Q : Fin d → E →L[ℝ] E} {YK : Fin d → ℝ → E}
    (hYK : ∀ i, ODESolution (fun t Y => Q i (F t Y)) (YK i) t₀ t₁)
    (hK0 : ∀ i, YK i t₀ = A t₀) (hQ : ∀ i, Q i (A t₀) = A t₀)
    (hcap : ∀ i, P i (YK i t₁) = YK i t₁) {𝓛 : Fin d → Set (E →L[ℝ] E)}
    (hP𝓛 : ∀ i, P i ∈ 𝓛 i) (hrec : ∀ i, IsRecoverable (𝓛 i) (Q i) (A t₁)) {y : ℝ → E}
    (hy : ODESolution (fun t Y => (List.ofFn P).prod (F t Y)) y t₀ t₁)
    (h0 : y t₀ = (List.ofFn P).prod (A t₀)) : y t₁ = A t₁ := by
  have hP1 : ∀ i, P i (A t₁) = A t₁ := fun i =>
    capture_abstract ht hA (hYK i) (hK0 i) (hQ i) (hcap i) (hP𝓛 i) (hrec i)
  refine galerkin_exact ht hA hy h0 rfl (list_prod_apply_eq_self ?_)
  intro T' hT'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT'
  exact hP1 i

end ExplicitAbstract

/-! ## Explicit step results, exactness criteria and multi-step exactness (matrices) -/

section MatrixExplicit

variable {R : Type*} [CommRing R] {m n r p q : Type*}
  [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]

/-- **Explicit result of the BUG S-step** (proof of Ceruti–Lubich, arXiv:2010.02022,
Theorem 3).  For `F(t,Y) = Ȧ(t)` and `Y₀ = U₀ S₀ V₀ᵀ = A₀`, the S-step gives
`S₁ = U₁ᵀ A₁ V₁` and `Y₁ = U₁ U₁ᵀ A₁ V₁ V₁ᵀ`, for arbitrary new bases `U₁`, `V₁` (no rank,
orthonormality or capture assumptions). -/
theorem bug_eq_proj {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) {U₁ : Matrix m p R} {V₁ : Matrix n q R}
    {S₁ : Matrix p q R} (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) :
    S₁ = U₁ᵀ * A₁ * V₁ ∧ U₁ * S₁ * V₁ᵀ = U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ) := by
  have hS : S₁ = U₁ᵀ * A₁ * V₁ := by
    subst hS₁ hY₀
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  refine ⟨hS, ?_⟩
  rw [hS]
  simp only [Matrix.mul_assoc]

/-- **Exactness criterion for the BUG step.**  With orthonormal new bases, the BUG step for
`F(t,Y) = Ȧ(t)` from `Y₀ = A₀` is exact iff both new bases capture `A₁`:
`U₁ S₁ V₁ᵀ = A₁ ↔ U₁U₁ᵀA₁ = A₁ ∧ A₁V₁V₁ᵀ = A₁`.  Thus the conclusion of CL Lemma 1 is necessary
and sufficient. -/
theorem bug_exact_iff [DecidableEq p] [DecidableEq q] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) {U₁ : Matrix m p R}
    {V₁ : Matrix n q R} {S₁ : Matrix p q R} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) :
    U₁ * S₁ * V₁ᵀ = A₁ ↔ U₁ * U₁ᵀ * A₁ = A₁ ∧ A₁ * (V₁ * V₁ᵀ) = A₁ := by
  rw [(bug_eq_proj hY₀ hS₁).2]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · calc U₁ * U₁ᵀ * A₁ = U₁ * U₁ᵀ * (U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ)) := by rw [h]
        _ = U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ) := by
          simp only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hU₁, Matrix.one_mul]
        _ = A₁ := h
    · calc A₁ * (V₁ * V₁ᵀ) = U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ) * (V₁ * V₁ᵀ) := by rw [h]
        _ = U₁ * U₁ᵀ * A₁ * (V₁ * V₁ᵀ) := by
          simp only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hV₁, Matrix.one_mul]
        _ = A₁ := h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- **Explicit result of the projector-splitting (KSL) step.**  For `F(t,Y) = Ȧ(t)` and
`Y₀ = U₀ S₀ V₀ᵀ = A₀`, the KSL step of `ksl_exact_capture` (`K₁ = U₀ S₀ + ΔA V₀`,
`Ŝ₁ = U₁ᵀ K₁`, `S̃₀ = Ŝ₁ - U₁ᵀ ΔA V₀`, `L₁ = V₀ S̃₀ᵀ + ΔAᵀ U₁`) gives `L₁ = A₁ᵀ U₁` and
`Y₁ = U₁ L₁ᵀ = U₁ U₁ᵀ A₁`, for an arbitrary new basis `U₁` (no rank, orthonormality or capture
assumptions, not even `V₀ᵀ V₀ = I`). -/
theorem ksl_eq_proj {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) {K₁ : Matrix m r R} {U₁ : Matrix m p R}
    {Ŝ₁ St₀ : Matrix p r R} {L₁ : Matrix n p R} (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀)
    (hŜ₁ : Ŝ₁ = U₁ᵀ * K₁) (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀)
    (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁) :
    L₁ = A₁ᵀ * U₁ ∧ U₁ * L₁ᵀ = U₁ * U₁ᵀ * A₁ := by
  have hL : L₁ = A₁ᵀ * U₁ := by
    subst hL₁ hSt₀ hŜ₁ hK₁ hY₀
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  refine ⟨hL, ?_⟩
  rw [hL, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Exactness criterion for the KSL step**: under the hypotheses of `ksl_eq_proj`, the step
is exact iff the new basis captures `A₁`. -/
theorem ksl_exact_iff {U₀ : Matrix m r R} {S₀ : Matrix r r R} {V₀ : Matrix n r R}
    {A₀ A₁ : Matrix m n R} (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) {K₁ : Matrix m r R} {U₁ : Matrix m p R}
    {Ŝ₁ St₀ : Matrix p r R} {L₁ : Matrix n p R} (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀)
    (hŜ₁ : Ŝ₁ = U₁ᵀ * K₁) (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀)
    (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁) :
    U₁ * L₁ᵀ = A₁ ↔ U₁ * U₁ᵀ * A₁ = A₁ := by
  rw [(ksl_eq_proj hY₀ hK₁ hŜ₁ hSt₀ hL₁).2]

/-! ### Non-degeneracy in terms of the exact factors -/

omit [Fintype r] in
/-- For square matrices over a commutative ring, `IsUnit (A * B)` implies `IsUnit A`. -/
theorem isUnit_of_isUnit_mul [DecidableEq r] [Fintype r] {A B : Matrix r r R}
    (h : IsUnit (A * B)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_left h

/-- **Transfer of the non-degeneracy condition** from the exact factors to the numerical
factors.  If `U₀ S₀ V₀ᵀ = U S Vᵀ` with `Uᵀ U = I` and `S` invertible, then `V = V₀ N` for an
`r × r` matrix `N`; hence invertibility of `Wᵀ V` implies invertibility of `Wᵀ V₀`.  This turns
the hypothesis `V(t₁)ᵀ V(t₀)` invertible of the papers (on the exact factors) into the
hypothesis `V(t₁)ᵀ V₀` invertible used by `left_capture` (on the factor `V₀` of `Y₀`). -/
theorem isUnit_transpose_mul_of_eq [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {U : Matrix m r R} {S : Matrix r r R} {V : Matrix n r R}
    (h : U₀ * S₀ * V₀ᵀ = U * S * Vᵀ) (hU : Uᵀ * U = 1) (hS : IsUnit S) {W : Matrix n r R}
    (hW : IsUnit (Wᵀ * V)) : IsUnit (Wᵀ * V₀) := by
  have hSt : IsUnit (Sᵀ).det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det S).mp hS
  have h1 : V * Sᵀ = V₀ * (S₀ᵀ * (U₀ᵀ * U)) := by
    have h2 := congrArg (fun X => Xᵀ * U) h
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hU,
      Matrix.mul_one] at h2
    exact h2.symm
  have hV : V = V₀ * (S₀ᵀ * (U₀ᵀ * U) * (Sᵀ)⁻¹) := by
    calc V = V * Sᵀ * (Sᵀ)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSt, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc]
  rw [hV, ← Matrix.mul_assoc] at hW
  exact isUnit_of_isUnit_mul hW

/-- Left version of `isUnit_transpose_mul_of_eq`: if `U₀ S₀ V₀ᵀ = U S Vᵀ` with `Vᵀ V = I` and `S`
invertible, invertibility of `Wᵀ U` implies invertibility of `Wᵀ U₀`. -/
theorem isUnit_transpose_mul_of_eq' [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {U : Matrix m r R} {S : Matrix r r R} {V : Matrix n r R}
    (h : U₀ * S₀ * V₀ᵀ = U * S * Vᵀ) (hV : Vᵀ * V = 1) (hS : IsUnit S) {W : Matrix m r R}
    (hW : IsUnit (Wᵀ * U)) : IsUnit (Wᵀ * U₀) := by
  have h' : V₀ * S₀ᵀ * U₀ᵀ = V * Sᵀ * Uᵀ := by
    have h2 := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h2
  exact isUnit_transpose_mul_of_eq h' hV ((Matrix.isUnit_transpose S).mpr hS) hW

/-- **Exactness of the BUG integrator, paper form** (Ceruti–Lubich, arXiv:2010.02022,
Theorem 3 with the hypotheses of Theorem 1).  Let `A(t₀) = U(t₀) S(t₀) V(t₀)ᵀ` and
`A(t₁) = U(t₁) S(t₁) V(t₁)ᵀ` (here `Ue₀ Se₀ Ve₀ᵀ`, `Ue₁ Se₁ Ve₁ᵀ`) with orthonormal
`U(t₀)`, `V(t₀)` and invertible `S(t₀)`, and assume that `U(t₁)ᵀ U(t₀)` and
`V(t₁)ᵀ V(t₀)` are invertible.  Then one BUG step from any factorization
`Y₀ = U₀ S₀ V₀ᵀ = A(t₀)` with orthonormal `U₀`, `V₀` is exact.  The hypotheses are weakened
forms of those of the paper: only the endpoints `t₀`, `t₁` enter; `S(t₁)` may be singular and
`U(t₁)`, `V(t₁)` need not be orthonormal; the new bases need only capture `K₁`, `L₁`. -/
theorem bug_exact_of_factors [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {Ue₀ Ue₁ : Matrix m r R} {Se₀ Se₁ : Matrix r r R}
    {Ve₀ Ve₁ : Matrix n r R} (hA₀ : A₀ = Ue₀ * Se₀ * Ve₀ᵀ) (hA₁ : A₁ = Ue₁ * Se₁ * Ve₁ᵀ)
    (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hVe₀ : Ve₀ᵀ * Ve₀ = 1) (hSe₀ : IsUnit Se₀)
    (hUU : IsUnit (Ue₁ᵀ * Ue₀)) (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {U₁ : Matrix m p R} {V₁ : Matrix n q R}
    {S₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hU₁ : U₁ * U₁ᵀ * K₁ = K₁) (hV₁ : V₁ * V₁ᵀ * L₁ = L₁)
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) :
    U₁ * S₁ * V₁ᵀ = A₁ :=
  bug_exact hU₀ hV₀ hY₀ hA₁ (isUnit_transpose_mul_of_eq' (hY₀.trans hA₀) hVe₀ hSe₀ hUU)
    (isUnit_transpose_mul_of_eq (hY₀.trans hA₀) hUe₀ hSe₀ hVV) hK₁ hL₁ hU₁ hV₁ hS₁

/-- **Exactness of the rank-adaptive BUG integrator before truncation, paper form**
(Ceruti–Kusch–Lubich, arXiv:2104.05247, Theorem 1).  Under the hypotheses of
`bug_exact_of_factors` on the exact factors, the augmented step of `augBug_exact` (bases `Û`,
`V̂` capturing `[K₁, U₀]`, `[L₁, V₀]`, Galerkin step in the augmented bases) returns
`Û Ŝ₁ V̂ᵀ = A(t₁)`.  The final truncation (which leaves `A(t₁)` unchanged when the tolerance is
below its smallest nonzero singular value) is not formalized. -/
theorem augBug_exact_of_factors [DecidableEq r] {U₀ : Matrix m r R} {S₀ : Matrix r r R}
    {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {Ue₀ Ue₁ : Matrix m r R} {Se₀ Se₁ : Matrix r r R}
    {Ve₀ Ve₁ : Matrix n r R} (hA₀ : A₀ = Ue₀ * Se₀ * Ve₀ᵀ) (hA₁ : A₁ = Ue₁ * Se₁ * Ve₁ᵀ)
    (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hVe₀ : Ve₀ᵀ * Ve₀ = 1) (hSe₀ : IsUnit Se₀)
    (hUU : IsUnit (Ue₁ᵀ * Ue₀)) (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    {K₁ : Matrix m r R} {L₁ : Matrix n r R} {Uh : Matrix m p R} {Vh : Matrix n q R}
    {Ŝ₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hUh : Uh * Uhᵀ * Matrix.fromCols K₁ U₀ = Matrix.fromCols K₁ U₀)
    (hVh : Vh * Vhᵀ * Matrix.fromCols L₁ V₀ = Matrix.fromCols L₁ V₀)
    (hŜ₁ : Ŝ₁ = Uhᵀ * U₀ * S₀ * (Vhᵀ * V₀)ᵀ + Uhᵀ * (A₁ - A₀) * Vh) :
    Uh * Ŝ₁ * Vhᵀ = A₁ :=
  augBug_exact hU₀ hV₀ hY₀ hA₁ (isUnit_transpose_mul_of_eq' (hY₀.trans hA₀) hVe₀ hSe₀ hUU)
    (isUnit_transpose_mul_of_eq (hY₀.trans hA₀) hUe₀ hSe₀ hVV) hK₁ hL₁ hUh hVh hŜ₁

/-- **Exactness of the projector-splitting integrator, paper form** (Lubich–Oseledets,
arXiv:1301.1058, Theorem 4.1; Ceruti–Lubich, arXiv:2010.02022, Theorem 1).  As
`bug_exact_of_factors`, for the KSL step of `ksl_exact`.  Only the invertibility of
`V(t₁)ᵀ V(t₀)` is needed (the condition on `U(t₁)ᵀ U(t₀)` in CL Theorem 1 is not used),
`S(t₁)` may be singular (rank `A(t₁) ≤ r`, as in LO Theorem 4.1), and `U₀` need not be
orthonormal. -/
theorem ksl_exact_of_factors [DecidableEq r] [DecidableEq p] {U₀ : Matrix m r R}
    {S₀ : Matrix r r R} {V₀ : Matrix n r R} {A₀ A₁ : Matrix m n R} {Ue₀ Ue₁ : Matrix m r R}
    {Se₀ Se₁ : Matrix r r R} {Ve₀ Ve₁ : Matrix n r R} (hA₀ : A₀ = Ue₀ * Se₀ * Ve₀ᵀ)
    (hA₁ : A₁ = Ue₁ * Se₁ * Ve₁ᵀ) (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hSe₀ : IsUnit Se₀)
    (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A₀)
    {K₁ : Matrix m r R} {U₁ : Matrix m p R} {Ŝ₁ St₀ : Matrix p r R} {L₁ : Matrix n p R}
    {V₁ : Matrix n q R} {S₁ : Matrix p q R}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hU₁ : U₁ᵀ * U₁ = 1) (hqrK : U₁ * Ŝ₁ = K₁)
    (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀) (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁)
    (hqrL : V₁ * S₁ᵀ = L₁) :
    U₁ * S₁ * V₁ᵀ = A₁ :=
  ksl_exact hV₀ hY₀ hA₁ (isUnit_transpose_mul_of_eq (hY₀.trans hA₀) hUe₀ hSe₀ hVV) hK₁ hU₁ hqrK
    hSt₀ hL₁ hqrL

/-! ### Multi-step exactness -/

/-- One step of the matrix BUG integrator with exact substeps for `F(t,Y) = Ȧ(t)`, from
`Y₀ = U₀ S₀ V₀ᵀ` (target `A₀`) to `Y₁ = U₁ S₁ V₁ᵀ` (target `A₁`): the new bases capture the
K- and L-step results and `S₁` is the Galerkin S-step result. -/
structure IsBUGIncrementStep (A₀ A₁ : Matrix m n R) (U₀ : Matrix m r R) (S₀ : Matrix r r R)
    (V₀ : Matrix n r R) (U₁ : Matrix m r R) (S₁ : Matrix r r R) (V₁ : Matrix n r R) : Prop where
  /-- The new left basis captures `K₁ = U₀ S₀ + (A₁ - A₀) V₀`. -/
  capK : U₁ * U₁ᵀ * (U₀ * S₀ + (A₁ - A₀) * V₀) = U₀ * S₀ + (A₁ - A₀) * V₀
  /-- The new right basis captures `L₁ = V₀ S₀ᵀ + (A₁ - A₀)ᵀ U₀`. -/
  capL : V₁ * V₁ᵀ * (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀) = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀
  /-- Galerkin S-step `S₁ = (U₁ᵀU₀) S₀ (V₁ᵀV₀)ᵀ + U₁ᵀ (A₁ - A₀) V₁`. -/
  sStep : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁

/-- **Multi-step exactness of the BUG integrator.**  Let `A k = A(t_k)` (`k ≤ N`) have
factorizations `Ue k * Se k * (Ve k)ᵀ`, with orthonormal `Ue k`, `Ve k` and invertible `Se k`
for `k < N` (`A N` may have rank `< r`), and invertible overlaps `(Ue (k+1))ᵀ Ue k`,
`(Ve (k+1))ᵀ Ve k` (the hypotheses of CL Theorem 3 on every step).  Then the BUG integrator
with orthonormal bases, started from
`U 0 * S 0 * (V 0)ᵀ = A 0`, reproduces `A k` at every step: the exactness property propagates
along the time grid, since each numerical factorization `U k S k V kᵀ = A k` is an admissible
starting value for the next step (`isUnit_transpose_mul_of_eq`). -/
theorem bug_exact_multistep [DecidableEq r] {N : ℕ} {A : ℕ → Matrix m n R}
    {Ue : ℕ → Matrix m r R} {Se : ℕ → Matrix r r R} {Ve : ℕ → Matrix n r R}
    (hA : ∀ k ≤ N, A k = Ue k * Se k * (Ve k)ᵀ) (hUe : ∀ k < N, (Ue k)ᵀ * Ue k = 1)
    (hVe : ∀ k < N, (Ve k)ᵀ * Ve k = 1) (hSe : ∀ k < N, IsUnit (Se k))
    (hUU : ∀ k < N, IsUnit ((Ue (k + 1))ᵀ * Ue k))
    (hVV : ∀ k < N, IsUnit ((Ve (k + 1))ᵀ * Ve k))
    {U : ℕ → Matrix m r R} {S : ℕ → Matrix r r R} {V : ℕ → Matrix n r R}
    (hU : ∀ k ≤ N, (U k)ᵀ * U k = 1) (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1)
    (h0 : U 0 * S 0 * (V 0)ᵀ = A 0)
    (hstep : ∀ k < N, IsBUGIncrementStep (A k) (A (k + 1)) (U k) (S k) (V k) (U (k + 1))
      (S (k + 1)) (V (k + 1))) :
    ∀ k ≤ N, U k * S k * (V k)ᵀ = A k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hk' : k < N := Nat.lt_of_succ_le hk
    have hkle : k ≤ N := hk'.le
    exact bug_exact_of_factors (hA k hkle) (hA (k + 1) hk) (hUe k hk') (hVe k hk') (hSe k hk')
      (hUU k hk') (hVV k hk') (hU k hkle) (hV k hkle) (ih hkle) rfl rfl (hstep k hk').capK
      (hstep k hk').capL (hstep k hk').sStep

/-- One step of the matrix projector-splitting (KSL) integrator with exact substeps for
`F(t,Y) = Ȧ(t)`, in the QR form of Lubich–Oseledets §3.2: `U₁ Ŝ₁ = K₁` with `U₁ᵀ U₁ = I`, and
`V₁ S₁ᵀ = L₁ = V₀ S̃₀ᵀ + (A₁ - A₀)ᵀ U₁`, `S̃₀ = Ŝ₁ - U₁ᵀ (A₁ - A₀) V₀`. -/
structure IsKSLIncrementStep [DecidableEq r] (A₀ A₁ : Matrix m n R) (U₀ : Matrix m r R)
    (S₀ : Matrix r r R) (V₀ : Matrix n r R) (U₁ : Matrix m r R) (Ŝ₁ S₁ : Matrix r r R)
    (V₁ : Matrix n r R) : Prop where
  /-- The new left basis has orthonormal columns. -/
  orthU : U₁ᵀ * U₁ = 1
  /-- QR decomposition of the K-step result `K₁ = U₀ S₀ + (A₁ - A₀) V₀`. -/
  qrK : U₁ * Ŝ₁ = U₀ * S₀ + (A₁ - A₀) * V₀
  /-- QR decomposition of the L-step result after the backward S-step. -/
  qrL : V₁ * S₁ᵀ = V₀ * (Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀)ᵀ + (A₁ - A₀)ᵀ * U₁

/-- **Multi-step exactness of the projector-splitting integrator** (Lubich–Oseledets,
arXiv:1301.1058, Theorem 4.1, iterated over the time grid).  If `A k = Ue k Se k (Ve k)ᵀ` with
orthonormal `Ue k` and invertible `Se k` for `k < N`, and invertible overlaps
`(Ve (k+1))ᵀ Ve k`, then the KSL
integrator with orthonormal right bases `V k`, started from `U 0 S 0 (V 0)ᵀ = A 0`, reproduces
`A k` at every step. -/
theorem ksl_exact_multistep [DecidableEq r] {N : ℕ} {A : ℕ → Matrix m n R}
    {Ue : ℕ → Matrix m r R} {Se : ℕ → Matrix r r R} {Ve : ℕ → Matrix n r R}
    (hA : ∀ k ≤ N, A k = Ue k * Se k * (Ve k)ᵀ) (hUe : ∀ k < N, (Ue k)ᵀ * Ue k = 1)
    (hSe : ∀ k < N, IsUnit (Se k)) (hVV : ∀ k < N, IsUnit ((Ve (k + 1))ᵀ * Ve k))
    {U : ℕ → Matrix m r R} {Sh S : ℕ → Matrix r r R} {V : ℕ → Matrix n r R}
    (hV : ∀ k ≤ N, (V k)ᵀ * V k = 1) (h0 : U 0 * S 0 * (V 0)ᵀ = A 0)
    (hstep : ∀ k < N, IsKSLIncrementStep (A k) (A (k + 1)) (U k) (S k) (V k) (U (k + 1))
      (Sh (k + 1)) (S (k + 1)) (V (k + 1))) :
    ∀ k ≤ N, U k * S k * (V k)ᵀ = A k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hk' : k < N := Nat.lt_of_succ_le hk
    have hkle : k ≤ N := hk'.le
    exact ksl_exact_of_factors (hA k hkle) (hA (k + 1) hk) (hUe k hk') (hSe k hk') (hVV k hk')
      (hV k hkle) (ih hkle) rfl (hstep k hk').orthU
      (hstep k hk').qrK rfl rfl (hstep k hk').qrL

end MatrixExplicit

/-! ## ODE layer, paper form -/

section MatrixODEFactors

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]

/-- **Exactness of the BUG integrator, ODE and paper form** (Ceruti–Lubich, arXiv:2010.02022,
Theorem 3 with the hypotheses of Theorem 1): `bug_exact_ode` with the non-degeneracy stated on
exact factors `A(t₀) = U(t₀) S(t₀) V(t₀)ᵀ`, `A(t₁) = U(t₁) S(t₁) V(t₁)ᵀ` (orthonormal `U(t₀)`,
`V(t₀)`, invertible `S(t₀)`, invertible overlaps `U(t₁)ᵀ U(t₀)`, `V(t₁)ᵀ V(t₀)`), as in
`bug_exact_of_factors`.  Weakened hypotheses: only the endpoints enter, `S(t₁)` may be singular
and `U(t₁)`, `V(t₁)` need not be orthonormal. -/
theorem bug_exact_ode_of_factors [DecidableEq r] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {Ue₀ Ue₁ : Matrix m r ℝ} {Se₀ Se₁ : Matrix r r ℝ} {Ve₀ Ve₁ : Matrix n r ℝ}
    (hA₀ : A t₀ = Ue₀ * Se₀ * Ve₀ᵀ) (hA₁ : A t₁ = Ue₁ * Se₁ * Ve₁ᵀ)
    (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hVe₀ : Ve₀ᵀ * Ve₀ = 1) (hSe₀ : IsUnit Se₀)
    (hUU : IsUnit (Ue₁ᵀ * Ue₀)) (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀)
    {L : ℝ → Matrix n r ℝ} (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁)
    (hL₀ : L t₀ = V₀ * S₀ᵀ)
    {U₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ} (hU₁ : U₁ * U₁ᵀ * K t₁ = K t₁)
    (hV₁ : V₁ * V₁ᵀ * L t₁ = L t₁) {Sf : ℝ → Matrix p q ℝ}
    (hSf : ODESolution (fun t S => U₁ᵀ * F t (U₁ * S * V₁ᵀ) * V₁) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ) :
    U₁ * Sf t₁ * V₁ᵀ = A t₁ :=
  bug_exact_ode ht hA hU₀ hV₀ hY₀ hA₁
    (isUnit_transpose_mul_of_eq' (hY₀.trans hA₀) hVe₀ hSe₀ hUU)
    (isUnit_transpose_mul_of_eq (hY₀.trans hA₀) hUe₀ hSe₀ hVV) hK hK₀ hL hL₀ hU₁ hV₁ hSf hSf₀

/-- **Exactness of the projector-splitting integrator, ODE and paper form** (Lubich–Oseledets,
arXiv:1301.1058, Theorem 4.1; Ceruti–Lubich, arXiv:2010.02022, Theorem 1): `ksl_exact_ode`
with the non-degeneracy stated on exact factors, as in `ksl_exact_of_factors` (only the
`V`-overlap is used, `S(t₁)` may be singular). -/
theorem ksl_exact_ode_of_factors [DecidableEq r] [DecidableEq p]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Ue₀ Ue₁ : Matrix m r ℝ} {Se₀ Se₁ : Matrix r r ℝ}
    {Ve₀ Ve₁ : Matrix n r ℝ} (hA₀ : A t₀ = Ue₀ * Se₀ * Ve₀ᵀ) (hA₁ : A t₁ = Ue₁ * Se₁ * Ve₁ᵀ)
    (hUe₀ : Ue₀ᵀ * Ue₀ = 1) (hSe₀ : IsUnit Se₀) (hVV : IsUnit (Ve₁ᵀ * Ve₀))
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀) {U₁ : Matrix m p ℝ} {Ŝ₁ : Matrix p r ℝ} (hU₁ : U₁ᵀ * U₁ = 1)
    (hqrK : U₁ * Ŝ₁ = K t₁) {Sf : ℝ → Matrix p r ℝ}
    (hSf : ODESolution (fun t S => -(U₁ᵀ * F t (U₁ * S * V₀ᵀ) * V₀)) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = Ŝ₁) {L : ℝ → Matrix n p ℝ}
    (hL : ODESolution (fun t L => (F t (U₁ * Lᵀ))ᵀ * U₁) L t₀ t₁) (hL₀ : L t₀ = V₀ * (Sf t₁)ᵀ)
    {V₁ : Matrix n q ℝ} {S₁ : Matrix p q ℝ} (hqrL : V₁ * S₁ᵀ = L t₁) :
    U₁ * S₁ * V₁ᵀ = A t₁ :=
  ksl_exact_ode ht hA hV₀ hY₀ hA₁ (isUnit_transpose_mul_of_eq (hY₀.trans hA₀) hUe₀ hSe₀ hVV) hK
    hK₀ hU₁ hqrK hSf hSf₀ hL hL₀ hqrL

end MatrixODEFactors

/-! ## Non-degeneracy as recoverability modulo left multiplications (matrices)

The abstract condition `IsRecoverable` for `m × n` matrices with the class of left
multiplications: it does not involve the new basis, it is equivalent to the range condition
`A₁ = A₁ V₀ C`, and it follows from the non-degeneracy hypothesis of Ceruti–Lubich. -/

section MatrixRecoverable

open scoped LeanDLRA.Frobenius

variable {m n r k : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype k]

/-- The class of left multiplications `X ↦ M X` on `m × n` matrices.  It contains every left
projector `leftProj U` (`leftProj_mem_leftMulClass`). -/
def leftMulClass : Set (Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  {L | ∃ M : Matrix m m ℝ, ∀ X, L X = M * X}

/-- The class of right multiplications `X ↦ X M` on `m × n` matrices.  It contains every right
projector `rightProj V` (`rightProj_mem_rightMulClass`). -/
def rightMulClass : Set (Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  {L | ∃ M : Matrix n n ℝ, ∀ X, L X = X * M}

theorem leftProj_mem_leftMulClass (U : Matrix m k ℝ) :
    (leftProj U : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ∈ leftMulClass :=
  ⟨U * Uᵀ, fun _ => rfl⟩

theorem rightProj_mem_rightMulClass (V : Matrix n k ℝ) :
    (rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) ∈ rightMulClass :=
  ⟨V * Vᵀ, fun _ => rfl⟩

/-- The range condition `A = A V₀ C` (with `V₀ᵀ V₀ = I`) gives recoverability of `A` from
`A V₀ V₀ᵀ` modulo left multiplications, with the right multiplication `T X = X V₀ C`. -/
theorem isRecoverable_leftMulClass_of_eq_mul [DecidableEq r] {V₀ : Matrix n r ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) {A : Matrix m n ℝ} {C : Matrix r n ℝ} (hC : A = A * V₀ * C) :
    IsRecoverable leftMulClass (rightProj V₀) A := by
  refine ⟨Frobenius.rightMulCLM (V₀ * C), ?_, ?_⟩
  · rintro L ⟨M, hM⟩ Y
    simp only [Frobenius.rightMulCLM_apply, hM, Matrix.mul_assoc]
  · rw [Frobenius.rightMulCLM_apply, rightProj_apply']
    simp only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hV₀, Matrix.one_mul]
    rw [← Matrix.mul_assoc, ← hC]

/-- **Non-degeneracy implies recoverability** (left version; proof of Ceruti–Lubich,
arXiv:2010.02022, Lemma 1).  If `A₁ = U S Vᵀ` (rank at most `r`) with `Vᵀ V₀` invertible and
`V₀ᵀ V₀ = I`, then `A₁` is recoverable from `Q₀ A₁ = A₁ V₀ V₀ᵀ` modulo left multiplications. -/
theorem isRecoverable_leftMulClass_of_isUnit [DecidableEq r] {V₀ : Matrix n r ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) {A₁ : Matrix m n ℝ} {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} (hA₁ : A₁ = U * S * Vᵀ) (hV : IsUnit (Vᵀ * V₀)) :
    IsRecoverable leftMulClass (rightProj V₀) A₁ :=
  (exists_eq_mul_mul_of_isUnit hA₁ hV).elim fun _ hC =>
    isRecoverable_leftMulClass_of_eq_mul hV₀ hC

/-- **Non-degeneracy implies recoverability** (right version).  If `A₁ = U S Vᵀ` with `Uᵀ U₀`
invertible and `U₀ᵀ U₀ = I`, then `A₁` is recoverable from `P₀ A₁ = U₀ U₀ᵀ A₁` modulo right
multiplications, with the left multiplication `T X = Cᵀ U₀ᵀ X`. -/
theorem isRecoverable_rightMulClass_of_isUnit [DecidableEq r] {U₀ : Matrix m r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) {A₁ : Matrix m n ℝ} {U : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} (hA₁ : A₁ = U * S * Vᵀ) (hU : IsUnit (Uᵀ * U₀)) :
    IsRecoverable rightMulClass (leftProj U₀) A₁ := by
  have hA₁' : A₁ᵀ = V * Sᵀ * Uᵀ := by
    rw [hA₁]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨C, hC⟩ := exists_eq_mul_mul_of_isUnit hA₁' hU
  have hC' : A₁ = Cᵀ * U₀ᵀ * A₁ := by
    have h := congrArg Matrix.transpose hC
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h
  refine ⟨Frobenius.leftMulCLM (Cᵀ * U₀ᵀ), ?_, ?_⟩
  · rintro L ⟨M, hM⟩ Y
    simp only [Frobenius.leftMulCLM_apply, hM, Matrix.mul_assoc]
  · rw [Frobenius.leftMulCLM_apply, leftProj_apply]
    simp only [Matrix.mul_assoc, mul_mul_eq_of_mul_eq hU₀, Matrix.one_mul]
    rw [← Matrix.mul_assoc, ← hC']

/-- **The commutant of the left multiplications.**  A continuous linear map on `m × n`
matrices (`m` nonempty) that commutes with every left multiplication is a right
multiplication `X ↦ X N`. -/
theorem exists_mul_right_of_commute [Nonempty m]
    (T : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (hT : ∀ L ∈ leftMulClass, ∀ Y, L (T Y) = T (L Y)) :
    ∃ N : Matrix n n ℝ, ∀ X, T X = X * N := by
  classical
  let i₀ : m := Classical.arbitrary m
  have hsingle : ∀ a j, T (Matrix.single a j (1 : ℝ)) =
      Matrix.single a i₀ (1 : ℝ) * T (Matrix.single i₀ j 1) := fun a j => by
    have h := hT (Frobenius.leftMulCLM (Matrix.single a i₀ (1 : ℝ))) ⟨_, fun _ => rfl⟩
      (Matrix.single i₀ j 1)
    rw [Frobenius.leftMulCLM_apply, Frobenius.leftMulCLM_apply, Matrix.single_mul_single_same,
      one_mul] at h
    exact h.symm
  refine ⟨Matrix.of fun j k => T (Matrix.single i₀ j 1) i₀ k, fun X => ?_⟩
  have hX : T X =
      ∑ a, ∑ j, X a j • (Matrix.single a i₀ (1 : ℝ) * T (Matrix.single i₀ j 1)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hsingle, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hX]
  ext a k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · rw [Matrix.mul_apply]
    simp only [Matrix.single_mul_apply_same, one_mul, Matrix.of_apply]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ (Ne.symm hb), mul_zero]
  · simp

/-- **Recoverability modulo left multiplications is the range condition.**  For `V₀ᵀ V₀ = I`
(and `m` nonempty), `A` is recoverable from `A V₀ V₀ᵀ` modulo left multiplications iff
`A = A V₀ C` for some `C`, i.e. iff the column space of `A V₀` contains that of `A`.  In
particular the condition does not involve the new left basis `U₁`, and it is exactly the
non-degeneracy used in the proof of Ceruti–Lubich, arXiv:2010.02022, Lemma 1. -/
theorem isRecoverable_leftMulClass_iff [DecidableEq r]
    [Nonempty m] {V₀ : Matrix n r ℝ} (hV₀ : V₀ᵀ * V₀ = 1) (A : Matrix m n ℝ) :
    IsRecoverable leftMulClass (rightProj V₀) A ↔ ∃ C : Matrix r n ℝ, A = A * V₀ * C := by
  classical
  constructor
  · rintro ⟨T, hT, hTA⟩
    obtain ⟨N, hN⟩ := exists_mul_right_of_commute T hT
    refine ⟨V₀ᵀ * N, ?_⟩
    calc A = T (rightProj V₀ A) := hTA.symm
      _ = A * V₀ * (V₀ᵀ * N) := by rw [hN, rightProj_apply]; simp only [Matrix.mul_assoc]
  · rintro ⟨C, hC⟩
    exact isRecoverable_leftMulClass_of_eq_mul hV₀ hC

end MatrixRecoverable

/-! ## Well-posedness: the exact BUG trajectory exists -/

section WellPosed

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- A BUG step with exact substeps and orthonormal new bases exists for all data, as soon as
`r ≤ card m` and `r ≤ card n` (QR step via `exists_orthonormal_capture_of_le_card`). -/
theorem exists_bugIncrementStep (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (A₀ A₁ : Matrix m n ℝ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix n (Fin r) ℝ) :
    ∃ U₁ : Matrix m (Fin r) ℝ, ∃ S₁ : Matrix (Fin r) (Fin r) ℝ, ∃ V₁ : Matrix n (Fin r) ℝ,
      U₁ᵀ * U₁ = 1 ∧ V₁ᵀ * V₁ = 1 ∧ IsBUGIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ S₁ V₁ := by
  obtain ⟨U₁, hU₁, hcK⟩ := exists_orthonormal_capture_of_le_card (U₀ * S₀ + (A₁ - A₀) * V₀) hm
  obtain ⟨V₁, hV₁, hcL⟩ := exists_orthonormal_capture_of_le_card (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀) hn
  exact ⟨U₁, _, V₁, hU₁, hV₁, ⟨hcK, hcL, rfl⟩⟩

/-- **The BUG integrator is well defined and exact for rank-`r` data.**  For every sequence of
targets `A k` satisfying the hypotheses of `bug_exact_multistep` up to `N`, and every
factorization `U₀ S₀ V₀ᵀ = A 0` with orthonormal `U₀`, `V₀`, there is a BUG trajectory
(orthonormal bases, exact substeps for `F(t,Y) = Ȧ(t)`) starting from `(U₀, S₀, V₀)`, and it
(like every such trajectory, by `bug_exact_multistep`) reproduces `A k` for `k ≤ N`.  Relative
to the hypotheses on the exact factors `Ue`, `Se`, `Ve` (which are assumed here), this shows
that the trajectory hypotheses of `bug_exact_multistep` are jointly satisfiable. -/
theorem exists_bug_trajectory_exact (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    {N : ℕ} {A : ℕ → Matrix m n ℝ} {Ue : ℕ → Matrix m (Fin r) ℝ}
    {Se : ℕ → Matrix (Fin r) (Fin r) ℝ} {Ve : ℕ → Matrix n (Fin r) ℝ}
    (hA : ∀ k ≤ N, A k = Ue k * Se k * (Ve k)ᵀ) (hUe : ∀ k < N, (Ue k)ᵀ * Ue k = 1)
    (hVe : ∀ k < N, (Ve k)ᵀ * Ve k = 1) (hSe : ∀ k < N, IsUnit (Se k))
    (hUU : ∀ k < N, IsUnit ((Ue (k + 1))ᵀ * Ue k))
    (hVV : ∀ k < N, IsUnit ((Ve (k + 1))ᵀ * Ve k))
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A 0) :
    ∃ U : ℕ → Matrix m (Fin r) ℝ, ∃ S : ℕ → Matrix (Fin r) (Fin r) ℝ,
      ∃ V : ℕ → Matrix n (Fin r) ℝ, U 0 = U₀ ∧ S 0 = S₀ ∧ V 0 = V₀ ∧
        (∀ k, (U k)ᵀ * U k = 1) ∧ (∀ k, (V k)ᵀ * V k = 1) ∧
        (∀ k, IsBUGIncrementStep (A k) (A (k + 1)) (U k) (S k) (V k) (U (k + 1)) (S (k + 1))
          (V (k + 1))) ∧
        ∀ k ≤ N, U k * S k * (V k)ᵀ = A k := by
  choose U₁ S₁ V₁ hU₁ hV₁ hst using fun (k : ℕ)
    (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
    exists_bugIncrementStep hm hn (A k) (A (k + 1)) x.1 x.2.1 x.2.2
  let seq : ℕ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ :=
    fun k => Nat.rec (U₀, S₀, V₀) (fun k x => (U₁ k x, S₁ k x, V₁ k x)) k
  have hseq : ∀ k, seq (k + 1) = (U₁ k (seq k), S₁ k (seq k), V₁ k (seq k)) := fun _ => rfl
  have hUo : ∀ k, (seq k).1ᵀ * (seq k).1 = 1 := by
    intro k; cases k with
    | zero => exact hU₀
    | succ k => rw [hseq]; exact hU₁ k (seq k)
  have hVo : ∀ k, (seq k).2.2ᵀ * (seq k).2.2 = 1 := by
    intro k; cases k with
    | zero => exact hV₀
    | succ k => rw [hseq]; exact hV₁ k (seq k)
  have hstep : ∀ k, IsBUGIncrementStep (A k) (A (k + 1)) (seq k).1 (seq k).2.1 (seq k).2.2
      (seq (k + 1)).1 (seq (k + 1)).2.1 (seq (k + 1)).2.2 := by
    intro k; rw [hseq]; exact hst k (seq k)
  refine ⟨fun k => (seq k).1, fun k => (seq k).2.1, fun k => (seq k).2.2, rfl, rfl, rfl, hUo,
    hVo, hstep, ?_⟩
  exact bug_exact_multistep hA hUe hVe hSe hUU hVV (fun k _ => hUo k) (fun k _ => hVo k) hY₀
    (fun k _ => hstep k)

end WellPosed

/-! ## A concrete rank-one example

`U₀ = V₀ = e₁`, `S₀ = 1`, `A₀ = e₁ e₁ᵀ`, and `A₁ = u uᵀ` with the unit vector `u = (3/5, 4/5)`.
Then `A₁` has rank one with `uᵀ U₀ = 3/5` invertible, so all hypotheses of the exactness
theorems hold (with `U₁ = V₁ = u`): this shows that they are jointly satisfiable in a
non-trivial situation (`A₁ ≠ A₀`).  For the same data the untruncated parallel BUG update with
the orthonormal augmented bases `[e₁, e₂]` is **not** exact, confirming the remark of
Ceruti–Kusch–Lubich (arXiv:2304.05660, §3). -/

namespace RankOneExample

/-- The first unit vector of `ℝ²` as a `2 × 1` matrix. -/
noncomputable def e₁ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- The second unit vector of `ℝ²` as a `2 × 1` matrix. -/
noncomputable def e₂ : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 0 else 1

/-- The unit vector `u = (3/5, 4/5)` as a `2 × 1` matrix. -/
noncomputable def u : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun i _ => if i = 0 then 3 / 5 else 4 / 5

/-- The `1 × 1` coefficient matrix `S₀ = 1`. -/
noncomputable def S₀ : Matrix (Fin 1) (Fin 1) ℝ := 1

/-- The initial value `A₀ = e₁ e₁ᵀ`. -/
noncomputable def A₀ : Matrix (Fin 2) (Fin 2) ℝ := e₁ * e₁ᵀ

/-- The rank-one target `A₁ = u uᵀ`. -/
noncomputable def A₁ : Matrix (Fin 2) (Fin 2) ℝ := u * uᵀ

theorem e₁_orth : e₁ᵀ * e₁ = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply]

theorem u_orth : uᵀ * u = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [u, Matrix.mul_apply]; norm_num

theorem isUnit_u_e₁ : IsUnit (uᵀ * e₁) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  simp [u, e₁, Matrix.mul_apply]

theorem Y₀_eq : e₁ * S₀ * e₁ᵀ = A₀ := by rw [S₀, Matrix.mul_one]; rfl

theorem A₁_eq : A₁ = u * S₀ * uᵀ := by rw [S₀, Matrix.mul_one]; rfl

theorem A₁_ne_A₀ : A₁ ≠ A₀ := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [A₁, A₀, u, e₁, Matrix.mul_apply] at h00
  norm_num at h00

/-- The augmented basis `[e₁, e₂]` is orthonormal. -/
theorem basis_orth : (Matrix.fromCols e₁ e₂)ᵀ * Matrix.fromCols e₁ e₂ = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply]

/-- The augmented basis `[e₁, e₂]` spans `ℝ²`, so it captures everything. -/
theorem basis_full : Matrix.fromCols e₁ e₂ * (Matrix.fromCols e₁ e₂)ᵀ = 1 := by
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply]

theorem defect_ne_zero : (1 - e₁ * e₁ᵀ) * (A₁ - A₀) * (1 - e₁ * e₁ᵀ) ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [A₁, A₀, e₁, u, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] at h11

/-- The K-step result `K₁ = A₁ e₁ = u (uᵀ e₁)` is captured by `U₁ = u`. -/
theorem capture_K : u * uᵀ * (e₁ * S₀ + (A₁ - A₀) * e₁) = e₁ * S₀ + (A₁ - A₀) * e₁ := by
  rw [kStep_eq e₁_orth Y₀_eq, A₁, Matrix.mul_assoc u uᵀ e₁]
  exact (capture_of_qr u_orth rfl).1

/-- The L-step result `L₁ = A₁ᵀ e₁ = u (uᵀ e₁)` is captured by `V₁ = u`. -/
theorem capture_L : u * uᵀ * (e₁ * S₀ᵀ + (A₁ - A₀)ᵀ * e₁) = e₁ * S₀ᵀ + (A₁ - A₀)ᵀ * e₁ := by
  rw [lStep_eq e₁_orth Y₀_eq, A₁, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc u uᵀ e₁]
  exact (capture_of_qr u_orth rfl).1

/-- The hypotheses of `bug_exact` are jointly satisfiable with `A₁ ≠ A₀`: the BUG step with
`U₁ = V₁ = u` reproduces `A₁` exactly. -/
example : u * (uᵀ * e₁ * S₀ * (uᵀ * e₁)ᵀ + uᵀ * (A₁ - A₀) * u) * uᵀ = A₁ :=
  bug_exact e₁_orth e₁_orth Y₀_eq A₁_eq isUnit_u_e₁ isUnit_u_e₁ rfl rfl
    capture_K capture_L rfl

/-- The hypotheses of `ksl_exact_capture` are jointly satisfiable with `A₁ ≠ A₀`. -/
example : u * (e₁ * (uᵀ * (e₁ * S₀ + (A₁ - A₀) * e₁) - uᵀ * (A₁ - A₀) * e₁)ᵀ +
    (A₁ - A₀)ᵀ * u)ᵀ = A₁ :=
  ksl_exact_capture e₁_orth Y₀_eq A₁_eq isUnit_u_e₁ rfl capture_K rfl rfl rfl

/-- **The untruncated parallel BUG update is not exact** (Ceruti–Kusch–Lubich,
arXiv:2304.05660, §3).  For the rank-one data above (for which BUG and KSL are exact) and the
orthonormal augmented bases `Û = V̂ = [e₁, e₂]` (see `basis_orth`), the untruncated update
`Ŷ₁ = Û Ŝ₁ V̂ᵀ` of `parBug_eq` does not reproduce `A₁`.  (Here `Ŷ₁ = [[9,12],[12,0]]/25` has
rank `2`, and its best rank-one approximation is not `A₁` either, so the claim survives the
truncation step of the integrator; that part is not formalized.) -/
theorem parBug_not_exact :
    Matrix.fromCols e₁ e₂ *
        Matrix.fromBlocks (S₀ + e₁ᵀ * (A₁ - A₀) * e₁) ((e₁ * S₀ᵀ + (A₁ - A₀)ᵀ * e₁)ᵀ * e₂)
          (e₂ᵀ * (e₁ * S₀ + (A₁ - A₀) * e₁)) 0 * (Matrix.fromCols e₁ e₂)ᵀ ≠ A₁ := by
  intro h
  refine defect_ne_zero ((parBug_exact_iff e₁_orth e₁_orth Y₀_eq rfl rfl rfl ?_ ?_ rfl rfl).mp h)
  · rw [basis_full, Matrix.one_mul]
  · rw [basis_full, Matrix.one_mul]

/-- The hypotheses of the paper-form theorem `bug_exact_of_factors` are jointly satisfiable with
`A₁ ≠ A₀`: exact factors `(e₁, 1, e₁)` at `t₀` and `(u, 1, u)` at `t₁`, overlaps `uᵀ e₁ = 3/5`. -/
example : u * (uᵀ * e₁ * S₀ * (uᵀ * e₁)ᵀ + uᵀ * (A₁ - A₀) * u) * uᵀ = A₁ :=
  bug_exact_of_factors Y₀_eq.symm A₁_eq e₁_orth e₁_orth (by simp [S₀]) isUnit_u_e₁ isUnit_u_e₁
    e₁_orth e₁_orth Y₀_eq rfl rfl capture_K capture_L rfl

/-- The explicit BUG result `U₁ U₁ᵀ A₁ V₁ V₁ᵀ` of `bug_eq_proj` for a basis that does **not**
capture `A₁`: with `U₁ = V₁ = e₁` the BUG step returns `e₁e₁ᵀ A₁ e₁e₁ᵀ ≠ A₁`, in accordance
with `bug_exact_iff` (the capture hypotheses cannot be dropped). -/
theorem bug_not_exact_of_not_capture :
    e₁ * (e₁ᵀ * e₁ * S₀ * (e₁ᵀ * e₁)ᵀ + e₁ᵀ * (A₁ - A₀) * e₁) * e₁ᵀ ≠ A₁ := by
  rw [(bug_eq_proj Y₀_eq rfl).2]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [A₁, e₁, u, Matrix.mul_apply] at h11

/-- `ksl_exact_capture` also covers rank-deficient targets (singular `S`, as in LO Theorem 4.1):
for `A₁ = 0 = u 0 uᵀ`, with `uᵀ e₁` invertible, the KSL step returns `0`. -/
example : u * (e₁ * (uᵀ * (e₁ * S₀ + (0 - A₀) * e₁) - uᵀ * (0 - A₀) * e₁)ᵀ + (0 - A₀)ᵀ * u)ᵀ = 0 :=
  ksl_exact_capture (U := u) (S := 0) e₁_orth Y₀_eq (by simp) isUnit_u_e₁ rfl
    (by rw [kStep_eq e₁_orth Y₀_eq, Matrix.zero_mul, Matrix.mul_zero]) rfl rfl rfl

/-- The rank-one target `B₁ = e₂ e₂ᵀ`, whose row space is orthogonal to that of `A₀ = e₁ e₁ᵀ`
(both lie on the rank-one path `v(t) v(t)ᵀ`, `v(t) = (cos t, sin t)`, `t ∈ [0, π/2]`). -/
noncomputable def B₁ : Matrix (Fin 2) (Fin 2) ℝ := e₂ * e₂ᵀ

theorem e₂_e₁ : e₂ᵀ * e₁ = 0 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, e₂, Matrix.mul_apply]

theorem e₁_e₂ : e₁ᵀ * e₂ = 0 := by
  ext i j; fin_cases i; fin_cases j; simp [e₁, e₂, Matrix.mul_apply]

theorem B₁_ne_zero : B₁ ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [B₁, e₂, Matrix.mul_apply] at h11

/-- **The non-degeneracy hypothesis cannot be dropped.**  For `Y₀ = A₀ = e₁e₁ᵀ` and the rank-one
target `B₁ = e₂e₂ᵀ`, the overlap `V(t₁)ᵀV(t₀) = e₂ᵀe₁ = 0` is singular, the K-step result
`K₁ = B₁ e₁` vanishes, and `U₁ = e₁` (with `Ŝ₁ = 0`) is an admissible QR factor of `K₁`.  With
this choice the projector-splitting step returns `U₁U₁ᵀB₁ = 0 ≠ B₁` (likewise the BUG step
with `U₁ = V₁ = e₁`).  So the invertibility of `V(t₁)ᵀ V(t₀)` assumed in the proof of
Lubich–Oseledets, arXiv:1301.1058, Theorem 4.1 (whose statement only requires rank at most `r`
and appeals to a perturbation argument), and in Ceruti–Lubich, arXiv:2010.02022, Theorems 1
and 3, is needed when the QR factor of a rank-deficient `K₁` is chosen arbitrarily. -/
theorem not_exact_of_degenerate :
    ¬ IsUnit (e₂ᵀ * e₁) ∧
      e₁ * e₁ᵀ * (e₁ * S₀ + (B₁ - A₀) * e₁) = e₁ * S₀ + (B₁ - A₀) * e₁ ∧
      e₁ * e₁ᵀ * (e₁ * S₀ᵀ + (B₁ - A₀)ᵀ * e₁) = e₁ * S₀ᵀ + (B₁ - A₀)ᵀ * e₁ ∧
      e₁ * (e₁ * (e₁ᵀ * (e₁ * S₀ + (B₁ - A₀) * e₁) - e₁ᵀ * (B₁ - A₀) * e₁)ᵀ +
        (B₁ - A₀)ᵀ * e₁)ᵀ ≠ B₁ ∧
      e₁ * (e₁ᵀ * e₁ * S₀ * (e₁ᵀ * e₁)ᵀ + e₁ᵀ * (B₁ - A₀) * e₁) * e₁ᵀ ≠ B₁ := by
  have hK : e₁ * S₀ + (B₁ - A₀) * e₁ = 0 := by
    rw [kStep_eq e₁_orth Y₀_eq, B₁, Matrix.mul_assoc, e₂_e₁, Matrix.mul_zero]
  have hL : e₁ * S₀ᵀ + (B₁ - A₀)ᵀ * e₁ = 0 := by
    rw [lStep_eq e₁_orth Y₀_eq, B₁, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, e₂_e₁, Matrix.mul_zero]
  have hP : e₁ * e₁ᵀ * B₁ = 0 := by
    rw [B₁, Matrix.mul_assoc, ← Matrix.mul_assoc e₁ᵀ, e₁_e₂, Matrix.zero_mul, Matrix.mul_zero]
  refine ⟨by rw [e₂_e₁]; exact not_isUnit_zero, by rw [hK, Matrix.mul_zero],
    by rw [hL, Matrix.mul_zero], ?_, ?_⟩
  · rw [(ksl_eq_proj Y₀_eq rfl rfl rfl rfl).2, hP]
    exact B₁_ne_zero.symm
  · rw [(bug_eq_proj Y₀_eq rfl).2, hP, Matrix.zero_mul]
    exact B₁_ne_zero.symm

section Recoverable

open scoped LeanDLRA.Frobenius

/-- **Recoverability is strictly stronger than capture.**  For `B₁ = e₂e₂ᵀ` and `V₀ = e₁`, the
identity (a left multiplication) fixes `B₁` (and `Q₀ B₁ = B₁ e₁e₁ᵀ = 0`), but `B₁` is not
recoverable from `Q₀ B₁` modulo left multiplications (the column space of `B₁ e₁ = 0` does
not contain that of `B₁`, cf. `isRecoverable_leftMulClass_iff`).  So, for
`𝓛 = leftMulClass`, the hypothesis of `capture_abstract` is not implied by its conclusion. -/
theorem not_isRecoverable_B₁ :
    (1 : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) ∈ leftMulClass ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ) B₁ = B₁ ∧
      ¬ IsRecoverable leftMulClass (rightProj e₁) B₁ := by
  refine ⟨⟨1, fun X => (Matrix.one_mul X).symm⟩, rfl, ?_⟩
  rintro ⟨T, -, hT⟩
  have h0 : rightProj e₁ B₁ = 0 := by
    rw [rightProj_apply, B₁, Matrix.mul_assoc e₂, e₂_e₁, Matrix.mul_zero, Matrix.zero_mul]
  rw [h0, map_zero] at hT
  exact B₁_ne_zero hT.symm

end Recoverable

/-- The straight path `A(t) = A₀ + t (A₁ - A₀)` from `A₀ = e₁e₁ᵀ` to `A₁ = uuᵀ`
(`Ȧ = A₁ - A₀`). -/
noncomputable def Apath (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := A₀ + t • (A₁ - A₀)

theorem Apath_zero : Apath 0 = A₀ := by simp [Apath]

theorem Apath_one : Apath 1 = A₁ := by simp [Apath]

section ODE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The hypotheses of the ODE form `bug_exact_ode` are jointly satisfiable with `A₁ ≠ A₀`: for
the path `Apath` (`F(t, Y) = A₁ - A₀`), the exact K- and L-trajectories
`K(t) = e₁S₀ + t (A₁ - A₀)e₁`, `L(t) = e₁S₀ᵀ + t (A₁ - A₀)ᵀe₁`, the new bases `U₁ = V₁ = u` and
the Galerkin trajectory `S(t) = (uᵀe₁) S₀ (uᵀe₁)ᵀ + t uᵀ(A₁ - A₀)u`, the BUG step returns
`u S(1) uᵀ = A(1)`. -/
example : u * (uᵀ * e₁ * S₀ * (uᵀ * e₁)ᵀ + (1 : ℝ) • (uᵀ * (A₁ - A₀) * u)) * uᵀ = Apath 1 :=
  bug_exact_ode (F := fun _ _ => A₁ - A₀) (A := Apath) zero_le_one
    (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1) e₁_orth e₁_orth (Y₀_eq.trans Apath_zero.symm)
    (Apath_one.trans A₁_eq) isUnit_u_e₁ isUnit_u_e₁
    (K := fun t => e₁ * S₀ + t • ((A₁ - A₀) * e₁))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)
    (L := fun t => e₁ * S₀ᵀ + t • ((A₁ - A₀)ᵀ * e₁))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)
    (by simp only [one_smul]; exact capture_K) (by simp only [one_smul]; exact capture_L)
    (Sf := fun t => uᵀ * e₁ * S₀ * (uᵀ * e₁)ᵀ + t • (uᵀ * (A₁ - A₀) * u))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)

/-- The hypotheses of the ODE form `ksl_exact_ode` are jointly satisfiable with `A₁ ≠ A₀`: for
the path `Apath`, the K-trajectory `K(t) = e₁S₀ + t (A₁ - A₀)e₁`, `U₁ = u`, `Ŝ₁ = uᵀK(1)`, the
backward S-trajectory `S(t) = Ŝ₁ - t uᵀ(A₁ - A₀)e₁` and the L-trajectory
`L(t) = e₁ S(1)ᵀ + t (A₁ - A₀)ᵀu`, the KSL step returns `u L(1)ᵀ = A(1)` (with the trivial
factorization `L(1) = L(1) · 1`). -/
example : u * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
    (e₁ * (uᵀ * (e₁ * S₀ + (A₁ - A₀) * e₁) - uᵀ * (A₁ - A₀) * e₁)ᵀ + (A₁ - A₀)ᵀ * u)ᵀ =
      Apath 1 := by
  have h := ksl_exact_ode (F := fun _ _ => A₁ - A₀) (A := Apath) zero_le_one
    (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1) e₁_orth (Y₀_eq.trans Apath_zero.symm)
    (Apath_one.trans A₁_eq) isUnit_u_e₁
    (K := fun t => e₁ * S₀ + t • ((A₁ - A₀) * e₁))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp) u_orth
    (Ŝ₁ := uᵀ * (e₁ * S₀ + (1 : ℝ) • ((A₁ - A₀) * e₁)))
    (by rw [← Matrix.mul_assoc, one_smul]; exact capture_K)
    (Sf := fun t => uᵀ * (e₁ * S₀ + (1 : ℝ) • ((A₁ - A₀) * e₁)) +
      t • -(uᵀ * (A₁ - A₀) * e₁))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)
    (L := fun t => e₁ * (uᵀ * (e₁ * S₀ + (1 : ℝ) • ((A₁ - A₀) * e₁)) +
      (1 : ℝ) • -(uᵀ * (A₁ - A₀) * e₁))ᵀ + t • ((A₁ - A₀)ᵀ * u))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp)
    (S₁ := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by rw [Matrix.transpose_one, Matrix.mul_one])
  simpa only [one_smul, ← sub_eq_add_neg] using h

end ODE

end RankOneExample

end Exactness

/-! ## Exactness of the bundled abstract integrator steps -/

section Bundled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Explicit result of a bundled BUG step** (`IsBUGStep`, see `Integrators/BUG.lean`) for
`F(t,Y) = Ȧ(t)` from `Y₀ = A(t₀)`: `YS(t₁) = P₁ Q₁ A(t₁)`. -/
theorem IsBUGStep.eq_of_isDerivRHS {F : ℝ → E → E} {ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) :
    YS t₁ = P₁ (Q₁ (A t₁)) :=
  Exactness.bug_eq_abstract ht hA hs.sSol (hs.sStart.trans (by rw [hY₀]))

/-- **A bundled BUG step is exact iff the new projectors capture `A(t₁)`.** -/
theorem IsBUGStep.exact_iff {F : ℝ → E → E} {ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) :
    YS t₁ = A t₁ ↔ P₁ (A t₁) = A t₁ ∧ Q₁ (A t₁) = A t₁ :=
  Exactness.bug_exact_iff_abstract ht hA (fun x => hs.projP₁.idem x)
    (fun x => hs.projQ₁.idem x) hs.comm₁ hs.sSol (hs.sStart.trans (by rw [hY₀]))

/-- **Exactness of a bundled BUG step** (Ceruti–Lubich, arXiv:2010.02022, Theorem 3, abstract
form).  For `F(t,Y) = Ȧ(t)` and `Y₀ = A(t₀)` fixed by `P₀` and `Q₀`, assume that `A(t₁)` is
recoverable (`Exactness.IsRecoverable`) from `Q₀ A(t₁)` modulo a class `𝓛 ∋ P₁` and from
`P₀ A(t₁)` modulo a class `𝓡 ∋ Q₁`.  Then the BUG step is exact: `YS(t₁) = A(t₁)`.

The classes should be fixed independently of `P₁`, `Q₁` (for a class tailored to the new
projector the hypothesis is essentially the capture conclusion, see `Exactness.IsRecoverable`).
For matrices they are the left and right multiplications, and the recoverability hypotheses
are derived from the invertibility of the overlaps `Uᵀ U₀`, `Vᵀ V₀` in
`IsBUGStep.exact_matrix`. -/
theorem IsBUGStep.exact {F : ℝ → E → E} {ε : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hP₀ : P₀ (A t₀) = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) {𝓛 𝓡 : Set (E →L[ℝ] E)}
    (hP₁ : P₁ ∈ 𝓛) (hQ₁ : Q₁ ∈ 𝓡) (hrecL : Exactness.IsRecoverable 𝓛 Q₀ (A t₁))
    (hrecR : Exactness.IsRecoverable 𝓡 P₀ (A t₁)) : YS t₁ = A t₁ :=
  (hs.exact_iff ht hA hY₀).mpr
    ⟨Exactness.capture_abstract ht hA hs.kSol (hs.kStart.trans hY₀) hQ₀ hs.kCap hP₁ hrecL,
      Exactness.capture_abstract ht hA hs.lSol (hs.lStart.trans hY₀) hP₀ hs.lCap hQ₁ hrecR⟩

/-- **Explicit result of a bundled KSL step** (`IsKSLStep`, see
`Integrators/ProjectorSplitting.lean`) for `F(t,Y) = Ȧ(t)` from `Y₀ = A(t₀) = Q₀ A(t₀)`:
`YL(t₁) = P₁ A(t₁)`. -/
theorem IsKSLStep.eq_of_isDerivRHS {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (ht : t₀ ≤ t₁)
    {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) :
    YL t₁ = P₁ (A t₁) :=
  Exactness.ksl_eq_abstract ht hA hs.kSol hs.sSol hs.lSol (hs.kStart.trans hY₀)
    (hs.sStart.trans hs.kCap.symm) hs.lStart hQ₀

/-- **A bundled KSL step is exact iff the new left projector captures `A(t₁)`.** -/
theorem IsKSLStep.exact_iff {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (ht : t₀ ≤ t₁)
    {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀) :
    YL t₁ = A t₁ ↔ P₁ (A t₁) = A t₁ := by
  rw [hs.eq_of_isDerivRHS ht hA hY₀ hQ₀]

/-- **Exactness of a bundled KSL step** (Lubich–Oseledets, arXiv:1301.1058, Theorem 4.1,
abstract form).  For `F(t,Y) = Ȧ(t)` and `Y₀ = A(t₀)` fixed by `Q₀`, assume that `A(t₁)` is
recoverable (`Exactness.IsRecoverable`) from `Q₀ A(t₁)` modulo a class `𝓛 ∋ P₁` (fixed
independently of `P₁`; for matrices, the left multiplications).  Then the KSL step is exact:
`YL(t₁) = A(t₁)`.  The matrix instance, with the hypothesis derived from the invertibility of
`Vᵀ V₀`, is `IsKSLStep.exact_matrix`. -/
theorem IsKSLStep.exact {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (ht : t₀ ≤ t₁)
    {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) (hQ₀ : Q₀ (A t₀) = A t₀)
    {𝓛 : Set (E →L[ℝ] E)} (hP₁ : P₁ ∈ 𝓛) (hrec : Exactness.IsRecoverable 𝓛 Q₀ (A t₁)) :
    YL t₁ = A t₁ :=
  (hs.exact_iff ht hA hY₀ hQ₀).mpr
    (Exactness.capture_abstract ht hA hs.kSol (hs.kStart.trans hY₀) hQ₀ hs.kCap hP₁ hrec)

/-- **Explicit result of a bundled parallel BUG step** (`IsParallelBUGStep`, see
`Integrators/ParallelBUG.lean`; Ceruti–Kusch–Lubich, arXiv:2304.05660, §3) for
`F(t,Y) = Ȧ(t)` from `Y₀ = A(t₀)`: the untruncated update is
`parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) = A(t₁) - (1 - P₀)(1 - Q₀)(A(t₁) - A(t₀))`. -/
theorem IsParallelBUGStep.eq_of_isDerivRHS {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) :
    parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) = A t₁ - (1 - P₀) ((1 - Q₀) (A t₁ - A t₀)) := by
  subst hY₀
  exact Exactness.parBug_eq_abstract ht hA hs.comm hs.solK hs.solL hs.solS hs.initK hs.initL
    hs.initS hs.fixP hs.fixQ

/-- **A bundled parallel BUG step is exact iff the doubly-normal part of the increment
vanishes** (cf. arXiv:2304.05660, §3: the parallel integrator does not have the exactness
property; see `Exactness.RankOneExample.parBug_not_exact`). -/
theorem IsParallelBUGStep.exact_iff {F : ℝ → E → E} {P₀ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YL YS : ℝ → E} (hs : IsParallelBUGStep F P₀ Q₀ t₀ t₁ Y₀ YK YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → E} (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) :
    parallelBUG P₀ Q₀ (YK t₁) (YL t₁) (YS t₁) = A t₁ ↔
      (1 - P₀) ((1 - Q₀) (A t₁ - A t₀)) = 0 := by
  rw [hs.eq_of_isDerivRHS ht hA hY₀, sub_eq_self]

end Bundled

/-! ## Bundled steps for matrices -/

section BundledMatrix

open scoped LeanDLRA.Frobenius

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]
  [DecidableEq r]

/-- **Exactness of a bundled matrix BUG step** (Ceruti–Lubich, arXiv:2010.02022, Theorem 3).
Let `IsBUGStep` hold for `m × n` matrices (Frobenius inner product) with the projectors
`P₀ = U₀U₀ᵀ·`, `Q₀ = ·V₀V₀ᵀ`, `P₁ = U₁U₁ᵀ·`, `Q₁ = ·V₁V₁ᵀ`, for `F(t,Y) = Ȧ(t)` and
`Y₀ = U₀ S₀ V₀ᵀ = A(t₀)` with orthonormal `U₀`, `V₀`.  If `A(t₁) = U S Vᵀ` with `Uᵀ U₀` and
`Vᵀ V₀` invertible, then `YS(t₁) = A(t₁)`.  (The recoverability hypotheses of
`IsBUGStep.exact` are derived by `Exactness.isRecoverable_leftMulClass_of_isUnit` and
`Exactness.isRecoverable_rightMulClass_of_isUnit`.) -/
theorem IsBUGStep.exact_matrix {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ}
    {t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ} {YK YL YS : ℝ → Matrix m n ℝ}
    (hs : IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ t₁ Y₀ YK
      YL YS)
    (ht : t₀ ≤ t₁) {A : ℝ → Matrix m n ℝ} (hA : IsDerivRHS F A t₀ t₁)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {S₀ : Matrix r r ℝ} (hY₀ : U₀ * S₀ * V₀ᵀ = Y₀)
    (hA₀ : Y₀ = A t₀) {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    (hA₁ : A t₁ = U * S * Vᵀ) (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀)) :
    YS t₁ = A t₁ := by
  have hP₀ : leftProj U₀ (A t₀) = A t₀ := by
    rw [← hA₀, ← hY₀, Matrix.mul_assoc, leftProj_mul_left hU₀]
  have hQ₀ : rightProj V₀ (A t₀) = A t₀ := by
    rw [← hA₀, ← hY₀, rightProj_mul_transpose hV₀]
  exact hs.exact ht hA hA₀ hP₀ hQ₀ (Exactness.leftProj_mem_leftMulClass U₁)
    (Exactness.rightProj_mem_rightMulClass V₁)
    (Exactness.isRecoverable_leftMulClass_of_isUnit hV₀ hA₁ hV)
    (Exactness.isRecoverable_rightMulClass_of_isUnit hU₀ hA₁ hU)

/-- **Exactness of a bundled matrix KSL step** (Lubich–Oseledets, arXiv:1301.1058,
Theorem 4.1).  Let `IsKSLStep` hold for `m × n` matrices with `P₁ = U₁U₁ᵀ·`, `Q₀ = ·V₀V₀ᵀ`, for
`F(t,Y) = Ȧ(t)` and `Y₀ = U₀ S₀ V₀ᵀ = A(t₀)` with `V₀ᵀ V₀ = I`.  If `A(t₁) = U S Vᵀ` (rank at
most `r`) with `Vᵀ V₀` invertible, then `YL(t₁) = A(t₁)`. -/
theorem IsKSLStep.exact_matrix {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {U₁ : Matrix m p ℝ} {t₀ t₁ : ℝ}
    {Y₀ : Matrix m n ℝ} {YK YS YL : ℝ → Matrix m n ℝ}
    (hs : IsKSLStep F ε (leftProj U₁) (rightProj V₀) t₀ t₁ Y₀ YK YS YL)
    (ht : t₀ ≤ t₁) {A : ℝ → Matrix m n ℝ} (hA : IsDerivRHS F A t₀ t₁)
    (hV₀ : V₀ᵀ * V₀ = 1) {S₀ : Matrix r r ℝ} (hY₀ : U₀ * S₀ * V₀ᵀ = Y₀) (hA₀ : Y₀ = A t₀)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hA₁ : A t₁ = U * S * Vᵀ)
    (hV : IsUnit (Vᵀ * V₀)) :
    YL t₁ = A t₁ := by
  have hQ₀ : rightProj V₀ (A t₀) = A t₀ := by
    rw [← hA₀, ← hY₀, rightProj_mul_transpose hV₀]
  exact hs.exact ht hA hA₀ hQ₀ (Exactness.leftProj_mem_leftMulClass U₁)
    (Exactness.isRecoverable_leftMulClass_of_isUnit hV₀ hA₁ hV)

end BundledMatrix

/-! ## The rank-one example in bundled and Tucker form -/

namespace Exactness.RankOneExample

open scoped LeanDLRA.Frobenius

theorem leftProj_e₁_A₀ : leftProj e₁ A₀ = A₀ := by
  rw [← Y₀_eq, Matrix.mul_assoc, leftProj_mul_left e₁_orth]

theorem rightProj_e₁_A₀ : rightProj e₁ A₀ = A₀ := by
  rw [← Y₀_eq, rightProj_mul_transpose e₁_orth]

/-- The full-space K-step result `A₀ + (A₁ - A₀) e₁e₁ᵀ = A₁ e₁e₁ᵀ` is captured by `u uᵀ`. -/
theorem leftProj_u_kStep :
    leftProj u (A₀ + rightProj e₁ (A₁ - A₀)) = A₀ + rightProj e₁ (A₁ - A₀) := by
  simp only [leftProj_apply, rightProj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, A₁, u, e₁, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The full-space L-step result `A₀ + e₁e₁ᵀ (A₁ - A₀) = e₁e₁ᵀ A₁` is captured by `· u uᵀ`. -/
theorem rightProj_u_lStep :
    rightProj u (A₀ + leftProj e₁ (A₁ - A₀)) = A₀ + leftProj e₁ (A₁ - A₀) := by
  simp only [leftProj_apply, rightProj_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A₀, A₁, u, e₁, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **A genuine rank-one BUG step in bundled form.**  On `2 × 2` matrices with the Frobenius
inner product, for `F(t, Y) = A₁ - A₀` (the derivative of `Apath`), the projectors
`P₀ = e₁e₁ᵀ·`, `Q₀ = ·e₁e₁ᵀ`, `P₁ = uuᵀ·`, `Q₁ = ·uuᵀ`, the exact full-space K-, L- and S-step
trajectories and the smallest admissible normal-component bound `ε`, all hypotheses of
`IsBUGStep` hold, and (by `IsBUGStep.exact_matrix`) the step returns
`P₁ Q₁ A₀ + P₁ Q₁ (A₁ - A₀) = A₁`, although `A₁ ≠ A₀` (`A₁_ne_A₀`). -/
theorem isBUGStep_exact :
    IsBUGStep (fun _ _ => A₁ - A₀)
        (‖(1 - leftProj u) ((1 - rightProj e₁) (A₁ - A₀))‖ +
          ‖(1 - rightProj u) ((1 - leftProj e₁) (A₁ - A₀))‖)
        (leftProj e₁) (rightProj e₁) (leftProj u) (rightProj u) 0 1 A₀
        (fun t => A₀ + t • rightProj e₁ (A₁ - A₀)) (fun t => A₀ + t • leftProj e₁ (A₁ - A₀))
        (fun t => leftProj u (rightProj u A₀) + t • leftProj u (rightProj u (A₁ - A₀))) ∧
      leftProj u (rightProj u A₀) + leftProj u (rightProj u (A₁ - A₀)) = A₁ := by
  have hs : IsBUGStep (fun _ _ => A₁ - A₀)
      (‖(1 - leftProj u) ((1 - rightProj e₁) (A₁ - A₀))‖ +
        ‖(1 - rightProj u) ((1 - leftProj e₁) (A₁ - A₀))‖)
      (leftProj e₁) (rightProj e₁) (leftProj u) (rightProj u) 0 1 A₀
      (fun t => A₀ + t • rightProj e₁ (A₁ - A₀)) (fun t => A₀ + t • leftProj e₁ (A₁ - A₀))
      (fun t => leftProj u (rightProj u A₀) + t • leftProj u (rightProj u (A₁ - A₀))) :=
    { projP₀ := isOrthProj_leftProj e₁_orth
      projQ₀ := isOrthProj_rightProj e₁_orth
      projP₁ := isOrthProj_leftProj u_orth
      projQ₁ := isOrthProj_rightProj u_orth
      comm₁ := leftProj_rightProj_comm u u
      kSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      kStart := by simp
      kCap := by simpa only [one_smul] using leftProj_u_kStep
      kNormal := fun _ _ => le_add_of_nonneg_right (norm_nonneg _)
      lSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      lStart := by simp
      lCap := by simpa only [one_smul] using rightProj_u_lStep
      lNormal := fun _ _ => le_add_of_nonneg_left (norm_nonneg _)
      sSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      sStart := by simp }
  refine ⟨hs, ?_⟩
  have h := hs.exact_matrix (A := Apath) zero_le_one (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1)
    e₁_orth e₁_orth Y₀_eq Apath_zero.symm (Apath_one.trans A₁_eq) isUnit_u_e₁ isUnit_u_e₁
  simpa only [one_smul, Apath_one] using h

/-- **A genuine rank-one KSL step in bundled form.**  With the data of `isBUGStep_exact`
(`P₁ = uuᵀ·`, `Q₀ = ·e₁e₁ᵀ`), the exact full-space K-, backward S- and L-step trajectories
satisfy all hypotheses of `IsKSLStep`, and (by `IsKSLStep.exact_matrix`) the step returns
`A₀ + Q₀ ΔA - P₁ Q₀ ΔA + P₁ ΔA = A₁` for `ΔA = A₁ - A₀ ≠ 0`. -/
theorem isKSLStep_exact :
    IsKSLStep (fun _ _ => A₁ - A₀) ‖(1 - leftProj u) ((1 - rightProj e₁) (A₁ - A₀))‖
        (leftProj u) (rightProj e₁) 0 1 A₀
        (fun t => A₀ + t • rightProj e₁ (A₁ - A₀))
        (fun t => A₀ + rightProj e₁ (A₁ - A₀) + t • -leftProj u (rightProj e₁ (A₁ - A₀)))
        (fun t => A₀ + rightProj e₁ (A₁ - A₀) - leftProj u (rightProj e₁ (A₁ - A₀)) +
          t • leftProj u (A₁ - A₀)) ∧
      A₀ + rightProj e₁ (A₁ - A₀) - leftProj u (rightProj e₁ (A₁ - A₀)) +
        leftProj u (A₁ - A₀) = A₁ := by
  have hs : IsKSLStep (fun _ _ => A₁ - A₀) ‖(1 - leftProj u) ((1 - rightProj e₁) (A₁ - A₀))‖
      (leftProj u) (rightProj e₁) 0 1 A₀
      (fun t => A₀ + t • rightProj e₁ (A₁ - A₀))
      (fun t => A₀ + rightProj e₁ (A₁ - A₀) + t • -leftProj u (rightProj e₁ (A₁ - A₀)))
      (fun t => A₀ + rightProj e₁ (A₁ - A₀) - leftProj u (rightProj e₁ (A₁ - A₀)) +
        t • leftProj u (A₁ - A₀)) :=
    { projP₁ := isOrthProj_leftProj u_orth
      projQ₀ := isOrthProj_rightProj e₁_orth
      kSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      kStart := by simp
      kCap := by simpa only [one_smul] using leftProj_u_kStep
      kNormal := fun _ _ => le_rfl
      sSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      sStart := by simp
      lSol := odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      lStart := by simp [sub_eq_add_neg] }
  refine ⟨hs, ?_⟩
  have h := hs.exact_matrix (A := Apath) zero_le_one (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1)
    e₁_orth Y₀_eq Apath_zero.symm (Apath_one.trans A₁_eq) isUnit_u_e₁
  simpa only [one_smul, Apath_one] using h

/-- The hypotheses of `tucker_exact_abstract` are jointly satisfiable non-trivially: for
`d = 2` on `2 × 2` matrices, with mode projectors `P = ![uuᵀ·, ·uuᵀ]`,
`Q = ![·e₁e₁ᵀ, e₁e₁ᵀ·]`, mode classes `![leftMulClass, rightMulClass]` (recoverability derived
from the overlap `uᵀe₁ = 3/5`) and the data of `isBUGStep_exact`, the core step returns
`A₁`.  (For `d = 2` the Tucker core step is the BUG S-step.) -/
theorem tucker_two_exact :
    (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ),
        rightProj u]).prod A₀ +
      (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ),
        rightProj u]).prod (A₁ - A₀) = A₁ := by
  have hA₁ : Apath 1 = u * S₀ * uᵀ := Apath_one.trans A₁_eq
  have h := tucker_exact_abstract (F := fun _ _ => A₁ - A₀) (A := Apath) zero_le_one
    (isDerivRHS_add_smul A₀ (A₁ - A₀) 0 1)
    (P := ![leftProj u, rightProj u]) (Q := ![rightProj e₁, leftProj e₁])
    (YK := ![fun t => A₀ + t • rightProj e₁ (A₁ - A₀), fun t => A₀ + t • leftProj e₁ (A₁ - A₀)])
    (fun i => by
      fin_cases i
      · exact odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1
      · exact odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1)
    (fun i => by fin_cases i <;> simp [Apath_zero])
    (fun i => by
      fin_cases i
      · simpa [Apath_zero] using rightProj_e₁_A₀
      · simpa [Apath_zero] using leftProj_e₁_A₀)
    (fun i => by
      fin_cases i
      · have h := leftProj_u_kStep
        rw [← one_smul ℝ (rightProj e₁ (A₁ - A₀))] at h
        exact h
      · have h := rightProj_u_lStep
        rw [← one_smul ℝ (leftProj e₁ (A₁ - A₀))] at h
        exact h)
    (𝓛 := ![leftMulClass, rightMulClass])
    (fun i => by
      fin_cases i
      · exact leftProj_mem_leftMulClass u
      · exact rightProj_mem_rightMulClass u)
    (fun i => by
      fin_cases i
      · exact isRecoverable_leftMulClass_of_isUnit e₁_orth hA₁ isUnit_u_e₁
      · exact isRecoverable_rightMulClass_of_isUnit e₁_orth hA₁ isUnit_u_e₁)
    (y := fun t => (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _),
        rightProj u]).prod A₀ +
      t • (List.ofFn ![(leftProj u : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] _), rightProj u]).prod
        (A₁ - A₀))
    (odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp [Apath_zero])
  simpa only [one_smul, Apath_one] using h

end Exactness.RankOneExample

end LeanDLRA
