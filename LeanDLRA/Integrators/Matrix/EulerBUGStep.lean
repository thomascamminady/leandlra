import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Integrators.Matrix.ParallelBUGStep

/-!
# The explicit Euler BUG step as a step relation

This file states the basis-update & Galerkin (BUG) integrator with explicit Euler substeps for
matrices. The error analysis of this integrator at the level of orthogonal projectors of an inner
product space is in `LeanDLRA/Integrators/EulerBUG.lean`. Here the projectors are `U Uᵀ` and
`V Vᵀ` for matrices `U`, `V` with orthonormal columns, the step is a relation between the old
value `Y₀` and the new value `Y₁` (`StepRel`), and the local error has the form `HasLocalError`
used by the convergence theorems of `LeanDLRA/Integrators/Tube.lean` and
`LeanDLRA/Integrators/Method.lean`. The error bounds are taken from the projector-level file:
the comparison of the step with the explicit Euler step of the full problem
(`matrix_augmentedBug_euler_sub_euler`) and the local error of that Euler step
(`norm_sub_exact_le_of_sub_euler`, which rests on `euler_defect_le`). They are not proved a
second time. That the step relation is a tube-local method (`StepMethod.IsTubeLocal`), and the
existence and the error bound of runs, are shown in
`LeanDLRA/Integrators/Matrix/EulerBUGRun.lean`.

**The step.** The integrator advances a rank-`r` matrix `Y₀ = U₀ S₀ V₀ᵀ` over a time step
`[t₀, t₁]` with one evaluation `F₀ = F(t₀, Y₀)` of the vector field (Nobile and Riffaud,
arXiv:2502.07040, §2.1, Algorithm 1). The K-step takes an orthonormal basis `Û` of the range of
`[U₀, F₀ V₀]`, the L-step an orthonormal basis `V̂` of the range of `[V₀, F₀ᵀ U₀]`, and the S-step
sets `Ŝ = Ûᵀ (Y₀ + (t₁ - t₀) F₀) V̂`. The matrix `Ŷ₁ = Û Ŝ V̂ᵀ` has rank at most `2 r`. For the
integrator with a fixed rank `r` it is then truncated to a best approximation of rank at most
`r`.

The step relations contain the algorithm only. The size `ε` of the normal part of the vector
field, the Lipschitz constants and the bound of the field are hypotheses of the error theorems,
not part of the step.

## Main definitions

* `MatrixEulerBUG.IsStep F t₀ t₁ U₀ S₀ V₀ Û Ŝ V̂`: the K-, L- and S-step at the level of the
  factors, for any index types of the columns.
* `MatrixEulerBUG.augmentedRel F r`: the step without truncation.
  `augmentedRel F r t₀ t₁ Y₀ Ŷ₁` says that `Ŷ₁ = Û Ŝ V̂ᵀ` for a step of the factors started from
  some factorization `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`, where `Û` and `V̂` have at
  most `2 r` columns.
* `MatrixEulerBUG.stepRel F r`: the step relation of the fixed-rank integrator.
  `stepRel F r t₀ t₁ Y₀ Y₁` says that `Y₁` has rank at most `r` and is as close to a result `Ŷ₁`
  of the step without truncation as a matrix of rank at most `r` can be.

## Main results

* `IsBoundedOnTube.norm_sub_le_of_near`: a point `Y₀` with `‖Y₀ - A t₀‖ + B (t₁ - t₀) ≤ ρ` lies
  in the tube of radius `ρ` around the reference solution `A` at all times of `[t₀, t₁]`.
* `MatrixEulerBUG.IsStep.norm_sub_euler_le`: the result `Û Ŝ V̂ᵀ` of a step differs from the
  explicit Euler step `Y₀ + (t₁ - t₀) F₀` by at most `t₁ - t₀` times the norm of the normal part
  `(1 - U₀ U₀ᵀ) F₀ (1 - V₀ V₀ᵀ)`.
* `MatrixEulerBUG.IsStep.hasLocalError`, `MatrixEulerBUG.IsStep.hasLocalError_of_tube`,
  `MatrixEulerBUG.augmentedRel.hasLocalError_of_tube`: the step without truncation has local
  error `(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`, where `Lₜ` is a Lipschitz constant of
  `t ↦ F(t, Y₀)` at `t₀`.
* `MatrixEulerBUG.stepRel.hasLocalError_of_tube`: the fixed-rank step has local error
  `(t₁ - t₀) ((11 L B + Lₜ) (t₁ - t₀) + 3 ε)` when the field is continuous, Lipschitz and
  bounded and its normal part is small on a tube around a reference solution.
* `MatrixEulerBUG.augmentedRel.rank_le`: the result of the step without truncation has rank at
  most `2 r`.
* `MatrixEulerBUG.augmentedRel.exists_stepRel`, `MatrixEulerBUG.augmentedRel.stepRel_truncation`:
  the truncation exists, and the truncated singular value decomposition
  `EckartYoung.truncation Ŷ₁ r` is one.
* `MatrixEulerBUG.isStep_tubeExt_iff`, `MatrixEulerBUG.augmentedRel_tubeExt_iff`,
  `MatrixEulerBUG.stepRel_tubeExt_iff`: if `Y₀` lies in the tube at time `t₀`, a step for the
  tube extension `tubeExt F A a b ρ` is the same as a step for `F`.

## Implementation notes

`MatrixEulerBUG.IsStep` asks that the range of `Û` contains the columns of `U₀` and of `F₀ V₀`,
and that the range of `V̂` contains the columns of `V₀` and of `F₀ᵀ U₀`. In the algorithm the
ranges are equal to the spans of these columns. A basis with further columns is also a step of
the predicate, and all error bounds hold for it. In `MatrixEulerBUG.augmentedRel` the numbers of
columns of `Û` and `V̂` are at most `2 r`, as in the algorithm; they need not be equal. Without
this cap `Û = 1` and `V̂ = 1` would be allowed, which is the explicit Euler step of the full
problem.

The step evaluates the field only at `(t₀, Y₀)`. A step for the tube extension of the field is
therefore a step for the field itself as soon as `Y₀` lies in the tube at time `t₀`; no margin
for substeps is needed. The local error theorems keep the condition
`‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ` of `HasLocalError.of_tubeExt`, because the exact solution
through `Y₀` has to stay in the tube during the step.

The dependence of the field on time enters through the constant `Lₜ` with
`‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)` for `t` in `[t₀, t₁)`, at the start value only. For an
autonomous field `Lₜ = 0`.

The truncation is a best approximation of rank at most `r`. The constants of the fixed-rank step
are `11 = 10 + 2 · 1/2`, `1 = 2 · 1/2` in front of `Lₜ` and `3 = 1 + 2 · 1`: the distance of the
exact solution to the matrices of rank at most `r` (`distLR_flow_le_of_tube`) plus twice the
error before truncation (`norm_bestTrunc_sub_le`). The bound for the distance uses a
projector-splitting step from the same start value, which exists if the field is continuous in
time. This is the only place where continuity of the field enters.

## References

* F. Nobile, S. Riffaud, *High-order BUG dynamical low-rank integrators based on explicit
  Runge–Kutta methods*, arXiv:2502.07040, §2.1, Algorithm 1.
* G. Ceruti, J. Kusch, Ch. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv:2104.05247 (BIT Numer. Math. 2022), for the augmented bases.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### A point near the reference solution stays in the tube during a step -/

section Near

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A fixed point near a reference solution stays in the tube during a step.** Let `F` be
bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`. If
`‖Y₀ - A t₀‖ + B (t₁ - t₀) ≤ ρ` for a step `[t₀, t₁] ⊆ [a, b]`, then `‖Y₀ - A t‖ ≤ ρ` for all
`t` in `[t₀, t₁]`: the reference solution moves by at most `B (t - t₀)`. -/
theorem IsBoundedOnTube.norm_sub_le_of_near {F : ℝ → E → E} {A : ℝ → E} {a b ρ B t₀ t₁ : ℝ}
    {Y₀ : E} (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + B * (t₁ - t₀) ≤ ρ) :
    ∀ t ∈ Icc t₀ t₁, ‖Y₀ - A t‖ ≤ ρ := by
  intro t ht
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 (ht.1.trans ht.2))
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Y₀ - A t₀)]
  have hAt : ‖A t - A t₀‖ ≤ B * (t - t₀) := hA.norm_sub_le (hFB.along hρ ha hb) t ht
  have hmono : B * (t - t₀) ≤ B * (t₁ - t₀) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB
  have e : Y₀ - A t = (Y₀ - A t₀) - (A t - A t₀) := by abel
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

end Near

namespace MatrixEulerBUG

/-! ### The step of the factors -/

section Step

variable {m n k s s' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype s] [Fintype s']
  [DecidableEq k] [DecidableEq s] [DecidableEq s']

/-- **One step of the BUG integrator with explicit Euler substeps, at the level of the factors,
before the truncation** (arXiv:2502.07040, §2.1, Algorithm 1, lines 2 to 7). The start value is
`Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `U₀`, `V₀`, and `F₀ = F t₀ Y₀`. The new bases `Ua`, `Va` are
orthonormal, the range of `Ua` contains the columns of `U₀` and of `F₀ V₀` (K-step), the range
of `Va` contains the columns of `V₀` and of `F₀ᵀ U₀` (L-step), and
`Sa = Uaᵀ (Y₀ + (t₁ - t₀) F₀) Va` (S-step). The result of the step is `Ua Sa Vaᵀ`. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m k ℝ)
    (S₀ : Matrix k k ℝ) (V₀ : Matrix n k ℝ) (Ua : Matrix m s ℝ) (Sa : Matrix s s' ℝ)
    (Va : Matrix n s' ℝ) : Prop where
  /-- The old column basis is orthonormal. -/
  orthU₀ : U₀ᵀ * U₀ = 1
  /-- The old row basis is orthonormal. -/
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- The new column basis is orthonormal. -/
  orthUa : Uaᵀ * Ua = 1
  /-- The new row basis is orthonormal. -/
  orthVa : Vaᵀ * Va = 1
  /-- The range of the new column basis contains the old column basis. -/
  capU : Ua * Uaᵀ * U₀ = U₀
  /-- K-step: the range of the new column basis contains the columns of `F₀ V₀`. -/
  capK : Ua * Uaᵀ * (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀) = F t₀ (U₀ * S₀ * V₀ᵀ) * V₀
  /-- The range of the new row basis contains the old row basis. -/
  capV : Va * Vaᵀ * V₀ = V₀
  /-- L-step: the range of the new row basis contains the columns of `F₀ᵀ U₀`. -/
  capL : Va * Vaᵀ * ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀) = (F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀
  /-- S-step: the Galerkin projection of the explicit Euler step onto the new bases. -/
  sStep : Sa = Uaᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₀ (U₀ * S₀ * V₀ᵀ)) * Va

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m k ℝ}
  {S₀ : Matrix k k ℝ} {V₀ : Matrix n k ℝ} {Ua : Matrix m s ℝ} {Sa : Matrix s s' ℝ}
  {Va : Matrix n s' ℝ}

/-- The result of a step is the explicit Euler step `Y₀ + (t₁ - t₀) F₀`, projected onto the
ranges of the new bases from both sides. -/
theorem IsStep.mul_mul_transpose_eq (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va) :
    Ua * Sa * Vaᵀ =
      Ua * Uaᵀ * (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₀ (U₀ * S₀ * V₀ᵀ)) * Va * Vaᵀ := by
  rw [hs.sStep]
  simp only [Matrix.mul_assoc]

/-- **A step depends on the field only through its value at the start.** If `G` and `F` have the
same value at `(t₀, U₀ S₀ V₀ᵀ)`, a step for `F` is a step for `G`. -/
theorem IsStep.congr_field {G : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va)
    (e : G t₀ (U₀ * S₀ * V₀ᵀ) = F t₀ (U₀ * S₀ * V₀ᵀ)) :
    IsStep G t₀ t₁ U₀ S₀ V₀ Ua Sa Va :=
  ⟨hs.orthU₀, hs.orthV₀, hs.orthUa, hs.orthVa, hs.capU, by rw [e]; exact hs.capK, hs.capV,
    by rw [e]; exact hs.capL, by rw [e]; exact hs.sStep⟩

/-- **A step for the tube extension is a step for the field.** If the start value lies in the
tube of radius `ρ` around `A` at time `t₀ ∈ [a, b]`, the tube extension `tubeExt F A a b ρ` and
`F` have the same value there, so they have the same steps. No condition on the step size is
needed, because the step evaluates the field only at the start. -/
theorem isStep_tubeExt_iff {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hx : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ ≤ ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ Ua Sa Va ↔ IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va :=
  ⟨fun h => h.congr_field (tubeExt_eq ht₀ hx).symm, fun h => h.congr_field (tubeExt_eq ht₀ hx)⟩

variable [DecidableEq m] [DecidableEq n] {L B ε Lt : ℝ}

/-- **Distance of a step to the explicit Euler step of the full problem.** The result
`Ua Sa Vaᵀ` of a step differs from `Y₀ + (t₁ - t₀) F₀` by at most `t₁ - t₀` times the norm of
the normal part `(1 - U₀ U₀ᵀ) F₀ (1 - V₀ V₀ᵀ)` of the field at the start value. This is
`matrix_augmentedBug_euler_sub_euler` for the factors of a step. -/
theorem IsStep.norm_sub_euler_le (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va) (h01 : t₀ ≤ t₁) :
    ‖Ua * Sa * Vaᵀ - (U₀ * S₀ * V₀ᵀ + (t₁ - t₀) • F t₀ (U₀ * S₀ * V₀ᵀ))‖ ≤
      (t₁ - t₀) * ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ := by
  rw [hs.mul_mul_transpose_eq]
  exact matrix_augmentedBug_euler_sub_euler hs.orthU₀ hs.orthV₀ hs.orthUa hs.orthVa hs.capU
    hs.capV S₀ _ hs.capK hs.capL (sub_nonneg.2 h01)

/-- **Local error of the explicit Euler BUG step without truncation.** Let `F` be `L`-Lipschitz
and bounded by `B`, let the normal part of `F` at the start value `Y₀ = U₀ S₀ V₀ᵀ` and time `t₀`
be at most `ε`, and let `‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. Then the result of
a step differs from the exact solution through the start value by at most
`(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`. The factor in front of `ε` is `1`. -/
theorem IsStep.hasLocalError (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁,
      ‖F t (U₀ * S₀ * V₀ᵀ) - F t₀ (U₀ * S₀ * V₀ᵀ)‖ ≤ Lt * (t - t₀)) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ua * Sa * Vaᵀ)
      ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by
  intro Φ hΦ hΦ₀
  have h0 : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have h1 := (hs.norm_sub_euler_le h01).trans (mul_le_mul_of_nonneg_left hε h0)
  have h2 := norm_sub_exact_le_of_sub_euler hF hL hB (by ring : t₁ = t₀ + (t₁ - t₀)) h0 hΦ hΦ₀
    hFt h1
  have e : (t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε) =
      (t₁ - t₀) * ε + (L * B + Lt) * (t₁ - t₀) ^ 2 / 2 := by ring
  rw [e]
  exact h2

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the explicit Euler BUG step without truncation near a reference solution.**
Let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`. Let the normal part of `F` at the start value `Y₀ = U₀ S₀ V₀ᵀ` and time `t₀` be at
most `ε`, and let `‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. If the start value of a
step over `[t₀, t₁] ⊆ [a, b]` satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the result of
the step differs from the exact solution through the start value by at most
`(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`. Nothing is assumed about `F` outside the tube. -/
theorem IsStep.hasLocalError_of_tube (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁,
      ‖F t (U₀ * S₀ * V₀ᵀ) - F t₀ (U₀ * S₀ * V₀ᵀ)‖ ≤ Lt * (t - t₀))
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ua * Sa * Vaᵀ)
      ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have hnear : ∀ t ∈ Icc t₀ t₁, ‖U₀ * S₀ * V₀ᵀ - A t‖ ≤ ρ :=
    hFB.norm_sub_le_of_near hB ha hb hA (by linarith)
  have heq : ∀ t ∈ Icc t₀ t₁,
      tubeExt F A a b ρ t (U₀ * S₀ * V₀ᵀ) = F t (U₀ * S₀ * V₀ᵀ) := fun t ht =>
    tubeExt_eq ⟨ha.trans ht.1, ht.2.trans hb⟩ (hnear t ht)
  have ht₀ : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.2 h01
  have hext : IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ Ua Sa Va :=
    hs.congr_field (heq t₀ ht₀)
  have hε' : ‖(1 - U₀ * U₀ᵀ) * tubeExt F A a b ρ t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε := by
    rw [heq t₀ ht₀]
    exact hε
  have hFt' : ∀ t ∈ Ico t₀ t₁, ‖tubeExt F A a b ρ t (U₀ * S₀ * V₀ᵀ) -
      tubeExt F A a b ρ t₀ (U₀ * S₀ * V₀ᵀ)‖ ≤ Lt * (t - t₀) := fun t ht => by
    rw [heq t (Ico_subset_Icc_self ht), heq t₀ ht₀]
    exact hFt t ht
  exact (hext.hasLocalError hε' (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) h01 hFt').of_tubeExt hFB hB ha hb h01 hA hsmall

end Step

/-! ### The step relations -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The explicit Euler BUG step without truncation, as a relation between matrices.**
`augmentedRel F r t₀ t₁ Y₀ Ŷ₁` holds if `Y₀ = U₀ S₀ V₀ᵀ` for factors with `r` columns and
orthonormal `U₀`, `V₀`, and `Ŷ₁ = Ua Sa Vaᵀ` for a step `MatrixEulerBUG.IsStep` of these factors
over `[t₀, t₁]` in which the new bases `Ua`, `Va` have at most `2 r` columns
(arXiv:2502.07040, §2.1, Algorithm 1, lines 2 to 7). The new bases are any orthonormal bases
with this number of columns whose ranges contain the columns named in the K- and L-step. -/
def augmentedRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (s s' : ℕ) (Ua : Matrix m (Fin s) ℝ) (Sa : Matrix (Fin s) (Fin s') ℝ)
      (Va : Matrix n (Fin s') ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ s ≤ 2 * r ∧ s' ≤ 2 * r ∧ IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va ∧
        Y₁ = Ua * Sa * Vaᵀ

/-- **The step of the fixed-rank explicit Euler BUG integrator, as a relation between
matrices** (arXiv:2502.07040, §2.1, Algorithm 1). `stepRel F r t₀ t₁ Y₀ Y₁` holds if `Y₁` is a
best approximation of rank at most `r` to a result `Ŷ₁` of the step without truncation from
`Y₀` over `[t₀, t₁]`: `Y₁` has rank at most `r`, and `‖Y₁ - Ŷ₁‖` is at most the distance
`distLR r Ŷ₁` of `Ŷ₁` to the matrices of rank at most `r`. The relation contains every
truncation with this property, in particular the truncated singular value decomposition of `Ŷ₁`
used in the algorithm (`MatrixEulerBUG.augmentedRel.stepRel_truncation`). -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ => ∃ Yh : Matrix m n ℝ, augmentedRel F r t₀ t₁ Y₀ Yh ∧ Y₁.rank ≤ r ∧
    ‖Y₁ - Yh‖ ≤ distLR r Yh

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {s s' : ℕ}
  {Ua : Matrix m (Fin s) ℝ} {Sa : Matrix (Fin s) (Fin s') ℝ} {Va : Matrix n (Fin s') ℝ}
  {Y₀ Y₁ Yh : Matrix m n ℝ}

/-- A step of the factors whose new bases have at most `2 r` columns is a step of the relation
`augmentedRel`. -/
theorem IsStep.augmentedRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va) (hsr : s ≤ 2 * r)
    (hsr' : s' ≤ 2 * r) : augmentedRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (Ua * Sa * Vaᵀ) :=
  ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, rfl, hsr, hsr', hs, rfl⟩

/-- A step of the factors whose new bases have at most `2 r` columns, followed by a best
approximation of rank at most `r`, is a step of the relation `stepRel`. -/
theorem IsStep.stepRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Ua Sa Va) (hsr : s ≤ 2 * r)
    (hsr' : s' ≤ 2 * r) (hr : Y₁.rank ≤ r)
    (htr : ‖Y₁ - Ua * Sa * Vaᵀ‖ ≤ distLR r (Ua * Sa * Vaᵀ)) :
    stepRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ :=
  ⟨_, hs.augmentedRel hsr hsr', hr, htr⟩

/-- An explicit Euler BUG step can only be started from a matrix of rank at most `r`. -/
theorem augmentedRel.rank_start_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, rfl, -, -, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- The result of the step without truncation has rank at most `2 r`. -/
theorem augmentedRel.rank_le (h : augmentedRel F r t₀ t₁ Y₀ Yh) : Yh.rank ≤ 2 * r := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, -, hsr, -, -, rfl⟩ := h
  calc (Ua * Sa * Vaᵀ).rank ≤ (Ua * Sa).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Ua.rank := Matrix.rank_mul_le_left _ _
    _ ≤ s := by simpa using Ua.rank_le_card_width
    _ ≤ 2 * r := hsr

/-- **The truncation exists.** Every result of the step without truncation has a best
approximation of rank at most `r`, so it can be completed to a step of the fixed-rank
integrator. -/
theorem augmentedRel.exists_stepRel (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    ∃ Y₁, stepRel F r t₀ t₁ Y₀ Y₁ := by
  obtain ⟨Z, hZ, hd⟩ := exists_best_approx r Yh
  exact ⟨Z, Yh, h, hZ, by rw [norm_sub_rev, hd]⟩

/-- **The truncated singular value decomposition is a truncation of the step.** The result of
the step without truncation, truncated to its `r` largest singular values, is a step of the
fixed-rank integrator: by the Eckart–Young theorem (`EckartYoung.norm_sub_truncation_le`) it is
a best approximation of rank at most `r`. -/
theorem augmentedRel.stepRel_truncation [DecidableEq n] (h : augmentedRel F r t₀ t₁ Y₀ Yh) :
    stepRel F r t₀ t₁ Y₀ (EckartYoung.truncation Yh r) :=
  ⟨Yh, h, EckartYoung.rank_truncation_le Yh r, by
    rw [norm_sub_rev]
    exact le_distLR_iff.2 fun Z hZ => EckartYoung.norm_sub_truncation_le Yh hZ⟩

/-- The result of a fixed-rank explicit Euler BUG step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨Yh, -, hr, -⟩ := h
  exact hr

/-- A fixed-rank explicit Euler BUG step can only be started from a matrix of rank at most
`r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨Yh, hYh, -, -⟩ := h
  exact hYh.rank_start_le

/-- All values of a run of the fixed-rank explicit Euler BUG integrator have rank at most `r`,
provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-! ### Near the reference solution -/

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **A step without truncation for the tube extension is a step for the field.** If `Y₀` lies
in the tube of radius `ρ` around `A` at time `t₀ ∈ [a, b]`, the relation `augmentedRel` is the
same for `tubeExt F A a b ρ` and for `F`. -/
theorem augmentedRel_tubeExt_iff (ht₀ : t₀ ∈ Icc a b) (hx : ‖Y₀ - A t₀‖ ≤ ρ) :
    augmentedRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Yh ↔ augmentedRel F r t₀ t₁ Y₀ Yh := by
  constructor
  · rintro ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, rfl, hsr, hsr', hs, rfl⟩
    exact ((isStep_tubeExt_iff ht₀ hx).1 hs).augmentedRel hsr hsr'
  · rintro ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, rfl, hsr, hsr', hs, rfl⟩
    exact ((isStep_tubeExt_iff ht₀ hx).2 hs).augmentedRel hsr hsr'

/-- **A fixed-rank step for the tube extension is a step for the field.** If `Y₀` lies in the
tube of radius `ρ` around `A` at time `t₀ ∈ [a, b]`, the relation `stepRel` is the same for
`tubeExt F A a b ρ` and for `F`. -/
theorem stepRel_tubeExt_iff (ht₀ : t₀ ∈ Icc a b) (hx : ‖Y₀ - A t₀‖ ≤ ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ :=
  ⟨fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff ht₀ hx).1 h, hr⟩,
    fun ⟨Yh, h, hr⟩ => ⟨Yh, (augmentedRel_tubeExt_iff ht₀ hx).2 h, hr⟩⟩

end Tube

/-! ### Local error -/

section Error

variable [DecidableEq m] [DecidableEq n] {L B ε Lt : ℝ} {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of the step without truncation, as a relation, near a reference solution.**
Let `F` be `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over
`[a, b]`, let the normal part of `F` be at most `ε` at the factored rank-`r` points of this
tube, and let `‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. If the start value of a step
over `[t₀, t₁] ⊆ [a, b]` satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then every step of
`MatrixEulerBUG.augmentedRel` from `Y₀` has local error at most
`(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`. -/
theorem augmentedRel.hasLocalError_of_tube (h : augmentedRel F r t₀ t₁ Y₀ Yh)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Yh ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by
  obtain ⟨U₀, S₀, V₀, s, s', Ua, Sa, Va, rfl, -, -, hs, rfl⟩ := h
  have ht₀ : t₀ ∈ Icc a b := ⟨ha, h01.trans hb⟩
  have hx : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ ≤ ρ := by
    linarith [mul_nonneg hB (sub_nonneg.2 h01)]
  exact hs.hasLocalError_of_tube (hε t₀ U₀ V₀ S₀ hs.orthU₀ hs.orthV₀ ⟨ht₀, hx⟩) hFL hL hFB hB
    ha hb h01 hA hFt hsmall

/-- **Local error of the fixed-rank explicit Euler BUG step near a reference solution.** Let
`F` be continuous, `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution
`A` over `[a, b]`, let the normal part of `F` be at most `ε` at the factored rank-`r` points of
this tube, and let `‖F t Y₀ - F t₀ Y₀‖ ≤ Lₜ (t - t₀)` during the step. If the start value of a
step over `[t₀, t₁] ⊆ [a, b]` satisfies `‖Y₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the truncated
result differs from the exact solution `Φ` through the start value by at most
`(t₁ - t₀) ((11 L B + Lₜ) (t₁ - t₀) + 3 ε)`.

The step without truncation contributes `(t₁ - t₀) ((L B + Lₜ) / 2 (t₁ - t₀) + ε)`. The
truncation to rank `r` is a best approximation, so it costs at most the distance of `Φ t₁` to
the matrices of rank at most `r` plus twice the error before truncation
(`norm_bestTrunc_sub_le`), and this distance is at most `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`
(`distLR_flow_le_of_tube`). No truncation tolerance appears. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε) (hε₀ : 0 ≤ ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ))
    (hAc : ContinuousOn A (Icc a b)) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (hsmall : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * ((11 * L * B + Lt) * (t₁ - t₀) + 3 * ε)) := by
  obtain ⟨Yh, hYh, -, htr⟩ := h
  intro Φ hΦ hΦ₀
  have h₁ := hYh.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hA hFt hsmall Φ hΦ hΦ₀
  have h₂ := distLR_flow_le_of_tube hε hε₀ hFL hL hFB hB hc hAc ha hb h01 hA hΦ
    (by rw [hΦ₀]; exact hYh.rank_start_le) (by rwa [hΦ₀])
  have h₃ := norm_bestTrunc_sub_le (A₁ := Φ t₁) htr
  have e : (t₁ - t₀) * ((11 * L * B + Lt) * (t₁ - t₀) + 3 * ε) =
      (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) +
        2 * ((t₁ - t₀) * ((L * B + Lt) / 2 * (t₁ - t₀) + ε)) := by ring
  rw [e]
  linarith

end Error

end Rel

end MatrixEulerBUG

end LeanDLRA
