import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Integrators.Matrix.Defs
import LeanDLRA.Integrators.Method

/-!
# The matrix projector-splitting step as a step relation

The projector-splitting (KSL) integrator of Lubich and Oseledets advances a rank-`r` matrix
`Y₀ = U₀ S₀ V₀ᵀ` over a time step `[t₀, t₁]` by three substeps that follow one another: a K-step
with the old row basis `V₀`, an S-step backwards in time with the new column basis `U₁` and the
old row basis `V₀`, and an L-step with the new column basis `U₁`. The predicate
`MatrixKSL.IsStep` of `LeanDLRA/Integrators/Matrix/ProjectorSplitting.lean` describes one such
step at the level of the factors. This file states the step on the level of the matrices
themselves, as a relation between the old value `Y₀` and the new value `Y₁`, and proves its local
error bound in the form `HasLocalError` used by the convergence theorems of
`LeanDLRA/Integrators/GlobalError.lean` and `LeanDLRA/Integrators/Tube.lean`.

The step relation contains the algorithm only. The size `ε` of the normal part of the vector
field, the Lipschitz constant and the bound of the field are hypotheses of the error theorems,
not part of the step.

## Main definitions

* `MatrixKSL.stepRel F r`: the step relation of the rank-`r` matrix projector-splitting
  integrator for the field `F`. `stepRel F r t₀ t₁ Y₀ Y₁` says that `Y₁` is the result of some
  step over `[t₀, t₁]` started from some factorization `Y₀ = U₀ S₀ V₀ᵀ` with orthonormal `V₀`.

## Main results

* `ODESolution.near_of_comp_proj`: one substep of a splitting method near a reference solution.
  A solution of a projected field that starts close to the reference solution stays in the tube
  and moves by at most `B (t - t₀)`.
* `MatrixKSL.IsStep.norm_sub_lt_of_near`: if the start value satisfies
  `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, the three substeps of a step stay in the tube of
  radius `ρ` around the reference solution `A`.
* `MatrixKSL.isStep_tubeExt_iff_of_near`, `MatrixKSL.stepRel_tubeExt_iff_of_near`: near the
  reference solution, a step for the tube extension `tubeExt F A a b ρ` is the same as a step
  for `F`.
* `MatrixKSL.IsStep.norm_kNormal_le`: the normal bound of the error analysis follows from
  `FactoredNormalBoundOn F r D ε` as soon as the result of the K-step lies in the region `D`.
* `MatrixKSL.IsStep.hasLocalError`, `MatrixKSL.stepRel.hasLocalError`: the local error bound
  `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` for a globally Lipschitz and bounded field.
* `MatrixKSL.IsStep.hasLocalError_of_tube`, `MatrixKSL.stepRel.hasLocalError_of_tube`: the same
  bound when the field is Lipschitz and bounded and its normal part is small only on a tube
  around a reference solution.
* `MatrixKSL.isRun_stepRel_of_isStep`: a chain of factor steps is a run of the step relation.

## Implementation notes

A run of `MatrixKSL.stepRel` (see `IsRun` in `LeanDLRA/Integrators/Defs.lean`) is more general
than a chain of factor steps: between two steps the factorization of the current value may be
replaced by any other factorization with an orthonormal row basis. The error theorems do not
depend on this choice.

The three substeps follow one another, so the distance to the reference solution can grow by
`B (t₁ - t₀)` in each of them. This is the reason for the factor `4` in the condition on the
start value: the L-step starts within `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀)` of `A t₀`, and one
substep from a start value at distance `d` stays in the tube if `d + 2 B (t₁ - t₀) < ρ`.

## References

* [LubichOseledets2014, §3.2]
* [KieriLubichWalach2016, Theorem 2.1]
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### One substep near a reference solution -/

section Substep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {G : ℝ → E → E}
  {A y : ℝ → E} {a b ρ B t₀ t₁ : ℝ}

/-- **One substep of a splitting method near a reference solution.** Let `G` be bounded by `B`
on the tube of radius `ρ` around a solution `A` of `G` over `[a, b]`, and let `y` solve the
projected equation `ẏ = Ψ (G t y)` on `[t₀, t₁] ⊆ [a, b]`, where the map `Ψ` does not increase
norms. If the start value satisfies `‖y t₀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then `y` stays strictly
inside the tube and `‖y t - y t₀‖ ≤ B (t - t₀)` on `[t₀, t₁]`. -/
theorem ODESolution.near_of_comp_proj {Ψ : E → E}
    (hy : ODESolution (fun t x => Ψ (G t x)) y t₀ t₁) (hΨ : ∀ x, ‖Ψ x‖ ≤ ‖x‖)
    (hGB : IsBoundedOnTube G A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hA : ODESolution G A t₀ t₁) (hsmall : ‖y t₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁, ‖y t - A t‖ < ρ ∧ ‖y t - y t₀‖ ≤ B * (t - t₀) := by
  intro t ht
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 (ht.1.trans ht.2))
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (y t₀ - A t₀)]
  have hg := hGB.comp_proj ha hb Ψ hΨ
  have hin := tube_trap hA hy hB hB (hGB.along hρ ha hb) hg (by linarith)
  exact ⟨hin t ht, hy.norm_sub_start_le_of_tube hg hin t ht⟩

end Substep

namespace MatrixKSL

/-! ### The step relation -/

section Rel

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ}

/-- **The step relation of the rank-`r` matrix projector-splitting integrator.**
`stepRel F r t₀ t₁ Y₀ Y₁` holds if `Y₀ = U₀ S₀ V₀ᵀ` for some factors with orthonormal `V₀`, and
`Y₁ = U₁ L(t₁)ᵀ` is the result of a projector-splitting step (`MatrixKSL.IsStep`) over
`[t₀, t₁]` started from these factors. The relation contains no constants of the error
analysis. -/
def stepRel (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) : StepRel (Matrix m n ℝ) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin r) ℝ) (Ŝ₁ : Matrix (Fin r) (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
      (S : ℝ → Matrix (Fin r) (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ),
      Y₀ = U₀ * S₀ * V₀ᵀ ∧ IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf ∧ Y₁ = U₁ * (Lf t₁)ᵀ

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ Ŝ₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Y₀ Y₁ : Matrix m n ℝ}

/-- A factor step relates the matrices `U₀ S₀ V₀ᵀ` and `U₁ L(t₁)ᵀ`. -/
theorem IsStep.stepRel (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) :
    MatrixKSL.stepRel F r t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * (Lf t₁)ᵀ) :=
  ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, hs, rfl⟩

/-- The result of a projector-splitting step has rank at most `r`. -/
theorem stepRel.rank_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₁.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, -, -, rfl⟩ := h
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using U₁.rank_le_card_width)

/-- A projector-splitting step can only be started from a matrix of rank at most `r`. -/
theorem stepRel.rank_start_le (h : stepRel F r t₀ t₁ Y₀ Y₁) : Y₀.rank ≤ r := by
  obtain ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, -, -⟩ := h
  exact rank_mul_mul_transpose_le _ _ _

/-- All values of a run of the matrix projector-splitting integrator have rank at most `r`,
provided the start value has. -/
theorem IsRun.rank_le {τ : ℕ → ℝ} {N : ℕ} {Y : ℕ → Matrix m n ℝ}
    (hY : IsRun (stepRel F r) τ N Y) (h0 : (Y 0).rank ≤ r) : ∀ n ≤ N, (Y n).rank ≤ r
  | 0, _ => h0
  | n + 1, hn => (hY.step n hn).rank_le

/-- **A chain of factor steps is a run.** Let the factors `(U j, Sm j, V j)` be advanced by
projector-splitting steps along the grid `τ`: step `j` produces the column basis `U (j + 1)`,
and the result `L(τ (j + 1))` of its L-step is factored as `V (j + 1) (Sm (j + 1))ᵀ`. Then the
matrices `U j * Sm j * (V j)ᵀ` form a run of `MatrixKSL.stepRel`. -/
theorem isRun_stepRel_of_isStep {τ : ℕ → ℝ} {N : ℕ} {U : ℕ → Matrix m (Fin r) ℝ}
    {Sm Ŝ : ℕ → Matrix (Fin r) (Fin r) ℝ} {V : ℕ → Matrix n (Fin r) ℝ}
    {K : ℕ → ℝ → Matrix m (Fin r) ℝ} {S : ℕ → ℝ → Matrix (Fin r) (Fin r) ℝ}
    {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ} (hτ : IsGrid τ N)
    (hstep : ∀ j < N, IsStep F (τ j) (τ (j + 1)) (U j) (Sm j) (V j) (U (j + 1)) (Ŝ j) (K j)
      (S j) (Lf j))
    (hLQR : ∀ j < N, Lf j (τ (j + 1)) = V (j + 1) * (Sm (j + 1))ᵀ) :
    IsRun (stepRel F r) τ N fun j => U j * Sm j * (V j)ᵀ :=
  ⟨hτ, fun j hj => by
    have h := (hstep j hj).stepRel
    rw [IsStep.eq_factored (hLQR j hj)] at h
    exact h⟩

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ B : ℝ}

/-- **The K-step near the reference solution.** Let `F` be bounded by `B` on the tube of radius
`ρ` around a solution `A` over `[a, b]`, and let `[t₀, t₁] ⊆ [a, b]`. If the start value
satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀) < ρ`, then the trajectory `K(t) V₀ᵀ` of the K-step
stays strictly inside the tube and differs from the start value by at most `B (t - t₀)`. -/
theorem IsStep.norm_kStep_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁,
      ‖K t * V₀ᵀ - A t‖ < ρ ∧ ‖K t * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t - t₀) := by
  have h := (odeSolution_kField hs.kSol).near_of_comp_proj (Ψ := fun x => rightProj V₀ x)
    (isOrthProj_rightProj hs.orthV₀).norm_le hFB hB ha hb hA
    (by simpa only [hs.kStart] using hsmall)
  simpa only [hs.kStart] using h

/-- Under the hypotheses of `MatrixKSL.IsStep.norm_kStep_of_near` the result `K(t₁) V₀ᵀ` of the
K-step stays within `‖U₀ S₀ V₀ᵀ - A t₀‖ + 2 B (t₁ - t₀)` of `A t` for all times `t` of the
step. -/
theorem IsStep.norm_kStep_sub_le_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁, ‖K t₁ * V₀ᵀ - A t‖ ≤ ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) := by
  intro t ht
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have h₁ := (hs.norm_kStep_of_near hFB hB ha hb hA hsmall t₁ ⟨h01, le_rfl⟩).2
  have h₂ := hA.norm_sub_le (hFB.along hρ ha hb) t ht
  have h₃ : B * (t - t₀) ≤ B * (t₁ - t₀) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 t₀) hB
  have e : K t₁ * V₀ᵀ - A t =
      (K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - A t₀) - (A t - A t₀) := by abel
  rw [e]
  have h₄ := norm_sub_le ((K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - A t₀)) (A t - A t₀)
  have h₅ := norm_add_le (K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ) (U₀ * S₀ * V₀ᵀ - A t₀)
  linarith

/-- Under the hypotheses of `MatrixKSL.IsStep.norm_kStep_of_near` the result of the K-step lies
in the tube at all times of the step. This is the point at which the error analysis evaluates
the normal part of `F`. -/
theorem IsStep.mem_tubeSet_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ) :
    ∀ t ∈ Icc t₀ t₁, (t, K t₁ * V₀ᵀ) ∈ tubeSet A a b ρ :=
  fun t ht => ⟨⟨ha.trans ht.1, ht.2.trans hb⟩,
    (hs.norm_kStep_sub_le_of_near hFB hB ha hb h01 hA hsmall t ht).trans hsmall.le⟩

/-- **The three substeps stay in the tube.** Let `F` be bounded by `B` on the tube of radius `ρ`
around a solution `A` over `[a, b]`, and let `[t₀, t₁] ⊆ [a, b]`. If the start value satisfies
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then the trajectories `K(t) V₀ᵀ`, `U₁ S(t) V₀ᵀ` and
`U₁ L(t)ᵀ` of the three substeps stay strictly inside the tube. The S-step starts where the
K-step ends and the L-step starts where the S-step ends, so the distance of the start values to
`A t₀` grows by at most `B (t₁ - t₀)` from one substep to the next. -/
theorem IsStep.norm_sub_lt_of_near (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    (∀ t ∈ Icc t₀ t₁, ‖K t * V₀ᵀ - A t‖ < ρ) ∧ (∀ t ∈ Icc t₀ t₁, ‖U₁ * S t * V₀ᵀ - A t‖ < ρ) ∧
      ∀ t ∈ Icc t₀ t₁, ‖U₁ * (Lf t)ᵀ - A t‖ < ρ := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hend : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hK := hs.norm_kStep_of_near hFB hB ha hb hA (by linarith)
  have hK₁ : ‖K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) := (hK t₁ hend).2
  have eS : U₁ * S t₀ * V₀ᵀ = K t₁ * V₀ᵀ := by rw [hs.sStart, hs.kQR]
  have hS₀ : ‖U₁ * S t₀ * V₀ᵀ - A t₀‖ ≤ ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + B * (t₁ - t₀) := by
    have e : U₁ * S t₀ * V₀ᵀ - A t₀ =
        (K t₁ * V₀ᵀ - U₀ * S₀ * V₀ᵀ) + (U₀ * S₀ * V₀ᵀ - A t₀) := by rw [eS]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  have hS := (odeSolution_sField hs.sSol).near_of_comp_proj
    (Ψ := fun x => -leftProj U₁ (rightProj V₀ x))
    (fun x => by
      rw [norm_neg]
      exact ((isOrthProj_leftProj hs.orthU₁).norm_le _).trans
        ((isOrthProj_rightProj hs.orthV₀).norm_le x))
    hFB hB ha hb hA (by linarith)
  have hS₁ : ‖U₁ * S t₁ * V₀ᵀ - U₁ * S t₀ * V₀ᵀ‖ ≤ B * (t₁ - t₀) := (hS t₁ hend).2
  have eL : U₁ * (Lf t₀)ᵀ = U₁ * S t₁ * V₀ᵀ := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hL₀ : ‖U₁ * (Lf t₀)ᵀ - A t₀‖ ≤ ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) := by
    have e : U₁ * (Lf t₀)ᵀ - A t₀ =
        (U₁ * S t₁ * V₀ᵀ - U₁ * S t₀ * V₀ᵀ) + (U₁ * S t₀ * V₀ᵀ - A t₀) := by rw [eL]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  have hL := (odeSolution_lField hs.lSol).near_of_comp_proj (Ψ := fun x => leftProj U₁ x)
    (isOrthProj_leftProj hs.orthU₁).norm_le hFB hB ha hb hA (by linarith)
  exact ⟨fun t ht => (hK t ht).1, fun t ht => (hS t ht).1, fun t ht => (hL t ht).1⟩

/-- **A step for the tube extension is a step for the field, if the step stays in the tube.**
The tube extension `tubeExt F A a b ρ` agrees with `F` on the tube of radius `ρ` around `A` over
`[a, b]`. If the three full-space trajectories of a step over `[t₀, t₁] ⊆ [a, b]` stay in the
tube, it does not matter which of the two fields drives the step. -/
theorem isStep_tubeExt_iff (ha : a ≤ t₀) (hb : t₁ ≤ b)
    (hK : ∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ)
    (hS : ∀ t ∈ Ico t₀ t₁, ‖U₁ * S t * V₀ᵀ - A t‖ ≤ ρ)
    (hLf : ∀ t ∈ Ico t₀ t₁, ‖U₁ * (Lf t)ᵀ - A t‖ ≤ ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf := by
  have hmem : ∀ t ∈ Ico t₀ t₁, t ∈ Icc a b := fun t ht => ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  have ek : ∀ t ∈ Ico t₀ t₁, kField V₀ (tubeExt F A a b ρ) t (K t) = kField V₀ F t (K t) :=
    fun t ht => by simp only [kField, tubeExt_eq (hmem t ht) (hK t ht)]
  have es : ∀ t ∈ Ico t₀ t₁,
      sField U₁ V₀ (tubeExt F A a b ρ) t (S t) = sField U₁ V₀ F t (S t) :=
    fun t ht => by simp only [sField, tubeExt_eq (hmem t ht) (hS t ht)]
  have el : ∀ t ∈ Ico t₀ t₁, lField U₁ (tubeExt F A a b ρ) t (Lf t) = lField U₁ F t (Lf t) :=
    fun t ht => by simp only [lField, tubeExt_eq (hmem t ht) (hLf t ht)]
  exact ⟨fun h => ⟨h.orthV₀, h.kSol.congr_field ek, h.kStart, h.orthU₁, h.kQR,
      h.sSol.congr_field es, h.sStart, h.lSol.congr_field el, h.lStart⟩,
    fun h => ⟨h.orthV₀, h.kSol.congr_field fun t ht => (ek t ht).symm, h.kStart, h.orthU₁,
      h.kQR, h.sSol.congr_field fun t ht => (es t ht).symm, h.sStart,
      h.lSol.congr_field fun t ht => (el t ht).symm, h.lStart⟩⟩

/-- **Near the reference solution, the tube extension has the same steps as the field.** Let `F`
be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let
`[t₀, t₁] ⊆ [a, b]`. If the start value satisfies `‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then
every step for either field stays in the tube, so the steps for `tubeExt F A a b ρ` are exactly
the steps for `F`. -/
theorem isStep_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    IsStep (tubeExt F A a b ρ) t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf ↔
      IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have key : ∀ G : ℝ → Matrix m n ℝ → Matrix m n ℝ, IsBoundedOnTube G A a b ρ B →
      ODESolution G A t₀ t₁ → IsStep G t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf →
      (∀ t ∈ Ico t₀ t₁, ‖K t * V₀ᵀ - A t‖ ≤ ρ) ∧
        (∀ t ∈ Ico t₀ t₁, ‖U₁ * S t * V₀ᵀ - A t‖ ≤ ρ) ∧
        ∀ t ∈ Ico t₀ t₁, ‖U₁ * (Lf t)ᵀ - A t‖ ≤ ρ := fun G hGB hGA hs => by
    obtain ⟨hK, hS, hLf⟩ := hs.norm_sub_lt_of_near hGB hB ha hb h01 hGA hsmall
    exact ⟨fun t ht => (hK t (Ico_subset_Icc_self ht)).le,
      fun t ht => (hS t (Ico_subset_Icc_self ht)).le,
      fun t ht => (hLf t (Ico_subset_Icc_self ht)).le⟩
  constructor
  · intro hs
    obtain ⟨hK, hS, hLf⟩ := key _ ((isBoundedField_tubeExt hFB hB hρ).isBoundedOnTube A a b ρ)
      ((odeSolution_tubeExt_iff ha hb fun t _ => by simpa using hρ).2 hA) hs
    exact (isStep_tubeExt_iff ha hb hK hS hLf).1 hs
  · intro hs
    obtain ⟨hK, hS, hLf⟩ := key F hFB hA hs
    exact (isStep_tubeExt_iff ha hb hK hS hLf).2 hs

/-- The statement of `isStep_tubeExt_iff_of_near` for the step relation: near the reference
solution, `tubeExt F A a b ρ` and `F` have the same projector-splitting steps. -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ := by
  constructor
  · rintro ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1 hs).stepRel
  · rintro ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, hs, rfl⟩
    exact ((isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs).stepRel

end Tube

end Rel

/-! ### The normal bound and the local error -/

section Error

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m (Fin r) ℝ}
  {S₀ Ŝ₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
  {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {Y₀ Y₁ : Matrix m n ℝ}
  {L B ε : ℝ}

/-- **Normal bound at the result of the K-step.** The result `K(t₁) V₀ᵀ` of the K-step has the
orthonormal factorization `U₁ Ŝ₁ V₀ᵀ`. Hence a bound `ε` for the normal part of `F` at factored
points of a region `D` applies to it whenever `(t, K(t₁) V₀ᵀ)` lies in `D`. -/
theorem IsStep.norm_kNormal_le {D : Set (ℝ × Matrix m n ℝ)}
    (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) (hε : FactoredNormalBoundOn F r D ε) {t : ℝ}
    (hmem : (t, K t₁ * V₀ᵀ) ∈ D) :
    ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε :=
  hε t U₁ V₀ Ŝ₁ hs.orthU₁ hs.orthV₀ (by rwa [← hs.kQR])

/-- **Local error of a matrix projector-splitting step, in the form used by the convergence
theorems.** Let `F` be `L`-Lipschitz and bounded by `B`, and let the normal part of `F` at the
result `U₁ Ŝ₁ V₀ᵀ` of the K-step be at most `ε` during the step. Then the result `U₁ L(t₁)ᵀ` of
the step differs from the exact solution through the start value `U₀ S₀ V₀ᵀ` by at most
`(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`. The bound does not depend on the singular values of the
factors, and it holds for every step size [KieriLubichWalach2016, Theorem 2.1]. -/
theorem IsStep.hasLocalError (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * (Lf t₁)ᵀ)
      ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) :=
  fun _ hΦ hΦ₀ => hs.local_error_sharp_of_pointwise hF hL hB hε (by ring) (sub_nonneg.2 h01)
    hΦ hΦ₀

/-- **Local error of the matrix projector-splitting step relation, global hypotheses.** If `F`
is `L`-Lipschitz and bounded by `B` and its normal part is at most `ε` at all factored rank-`r`
points, then every step of `MatrixKSL.stepRel` over `[t₀, t₁]` has local error at most
`(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`. -/
theorem stepRel.hasLocalError (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r univ ε) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (h01 : t₀ ≤ t₁) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) := by
  obtain ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, hs, rfl⟩ := h
  exact hs.hasLocalError (fun t _ => hs.norm_kNormal_le hε (mem_univ _)) hF hL hB h01

/-- The matrix projector-splitting step relation has local error
`(t₁ - t₀) (10 L B (t₁ - t₀) + ε)` on the whole space, in the form `StepRel.HasLocalErrorOn` of
`LeanDLRA/Integrators/Defs.lean`. -/
theorem stepRel_hasLocalErrorOn (hε : FactoredNormalBoundOn F r univ ε)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) :
    (stepRel F r).HasLocalErrorOn F univ fun t₀ t₁ =>
      (t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε) :=
  fun _ _ _ _ h01 _ h => h.hasLocalError hε hF hL hB h01

section Tube

variable {A : ℝ → Matrix m n ℝ} {a b ρ : ℝ}

/-- **Local error of a matrix projector-splitting step near a reference solution.** Let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
and let the normal part of `F` be at most `ε` at the factored rank-`r` points of this tube. If
the start value of a step over `[t₀, t₁] ⊆ [a, b]` satisfies
`‖U₀ S₀ V₀ᵀ - A t₀‖ + 4 B (t₁ - t₀) < ρ`, then its result differs from the exact solution through
the start value by at most `(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`. Nothing is assumed about `F`
outside the tube, and there is no bound on the step size other than the condition on the start
value. -/
theorem IsStep.hasLocalError_of_tube (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ (U₀ * S₀ * V₀ᵀ) (U₁ * (Lf t₁)ᵀ)
      ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) := by
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (U₀ * S₀ * V₀ᵀ - A t₀)]
  have h2 : ‖U₀ * S₀ * V₀ᵀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have hmem := hs.mem_tubeSet_of_near hFB hB ha hb h01 hA h2
  have hext := (isStep_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2 hs
  refine (hext.hasLocalError (fun t ht => ?_) (isLipschitzField_tubeExt hFL hL hρ) hL
    (isBoundedField_tubeExt hFB hB hρ) h01).of_tubeExt hFB hB ha hb h01 hA h2
  have hm := hmem t ht
  rw [hs.kQR] at hm
  have ht' : t ∈ Icc a b := hm.1
  have hx : ‖U₁ * Ŝ₁ * V₀ᵀ - A t‖ ≤ ρ := hm.2
  rw [tubeExt_eq ht' hx]
  exact hε t U₁ V₀ Ŝ₁ hs.orthU₁ hs.orthV₀ hm

/-- **Local error of the matrix projector-splitting step relation near a reference solution.**
Under the hypotheses of `MatrixKSL.IsStep.hasLocalError_of_tube`, stated for the start value
`Y₀`, every step of `MatrixKSL.stepRel` from `Y₀` has local error at most
`(t₁ - t₀) (10 L B (t₁ - t₀) + ε)`. -/
theorem stepRel.hasLocalError_of_tube (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + 4 * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁ ((t₁ - t₀) * (10 * L * B * (t₁ - t₀) + ε)) := by
  obtain ⟨U₀, S₀, V₀, U₁, Ŝ₁, K, S, Lf, rfl, hs, rfl⟩ := h
  exact hs.hasLocalError_of_tube hε hFL hL hFB hB ha hb h01 hA hsmall

end Tube

end Error

end MatrixKSL

end LeanDLRA
