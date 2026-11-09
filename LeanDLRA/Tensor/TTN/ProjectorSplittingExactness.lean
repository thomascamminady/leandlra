import LeanDLRA.Tensor.TTN.ProjectorSplitting
import LeanDLRA.OpenProblems.TensorNetworks.Part1b

/-!
# Exactness of the recursive TTN projector-splitting integrator

Ceruti–Lubich–Walach (arXiv 2002.11392, Theorem 5.1) prove that the recursive tree tensor network
(TTN) projector-splitting integrator reproduces a time-dependent family `A(t)` of tree tensor
networks exactly when it is applied to `F(t, Y) = Ȧ(t)` from `Y⁰ = A(t₀)`, provided the restrictions
`A_τ(t₁)` keep full tree rank for every subtree `τ` (the non-degeneracy condition (5.2)). The
proof is an induction over the height of the tree, with the exactness of the nested Tucker
projector-splitting integrator (Lubich–Vandereycken–Walach, arXiv 1709.02594, Thm 3;
`OpenProblems.TensorNetworks.tucker_ksl_exact`) at every node.

The full-rank condition enters only through the capture argument: the new basis of child `i`,
which captures the `K`-value `Q₀ i A(t₁)`, must also capture `A(t₁)` itself. As in the matrix and
Tucker cases of the library (`Exactness.IsRecoverable`), we state it in the abstract form
"`A(t₁)` is recoverable from its `K`-step projection `Q₀ i A(t₁)` modulo the operators acting on
the modes of `τᵢ`", i.e. `A(t₁) = T (Q₀ i A(t₁))` for a map `T` commuting with every operator
acting on the modes of `τᵢ`. For the matricization `M = Mat_{τᵢ}(A(t₁))` this says
`M = M V⁰ᵢ C` for some `C`, i.e. the column space of `M V⁰ᵢ` contains that of `M`, which follows
from the full-rank condition of the paper (matrix case: `Exactness.isRecoverable_leftMulClass_iff`,
`Exactness.isRecoverable_leftMulClass_of_isUnit`). Down the tree the condition is imposed on the
restricted targets
`A_{τᵢ}(t) = X i + Q₀ i P₁ 0 ⋯ P₁ (i-1) (A(t) - A(t₀))`, the solutions of the subtree problems,
which are the paper's `A_{τᵢ}` prolongated to the full tensor space.

## Main definitions

* `DimTree.IsNondegenerateProjectorSplittingStep`: a step of the recursive projector-splitting
  integrator (`DimTree.IsProjectorSplittingStep`) together with the recoverability condition at
  every node for the target trajectory `A`.

## Main results

* `DimTree.IsNondegenerateProjectorSplittingStep.isProjectorSplittingStep`: such steps are steps
  of the integrator, so the error bounds apply to them.
* `DimTree.IsNondegenerateProjectorSplittingStep.eq`: **exactness** (arXiv 2002.11392, Thm 5.1).
-/

open Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

namespace DimTree

open OpenProblems.TensorNetworks

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- A step of the **recursive TTN projector-splitting integrator** (`IsProjectorSplittingStep`)
from `(t₀, Y₀)` to `(t₁, Y₁)` that is **non-degenerate for the trajectory `A`** (arXiv
2002.11392, condition (5.2), abstract form): at every inner node `(τ₁, …, τ_m)` with co-range
projectors `Q₀ i` and new subtree projectors `P₁ i`, the target `A(t₁)` is recoverable from
`Q₀ i A(t₁)` modulo the operators acting on the modes of `τᵢ` (`Exactness.IsRecoverable`), and
the step of child `i` is non-degenerate for the restricted target
`t ↦ X i + Q₀ i P₁ 0 ⋯ P₁ (i-1) (A(t) - A(t₀))`. -/
def IsNondegenerateProjectorSplittingStep : DimTree κ → (ℝ → Tensor ι) →
    (ℝ → Tensor ι → Tensor ι) → ℝ → ℝ → ℝ → Tensor ι → Tensor ι → Prop
  | .leaf _, _, F, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → Tensor ι, ODESolution F y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node (m := m) cs, A, F, ε, t₀, t₁, Y₀, Y₁ =>
      ∃ (r s : Fin m → ℕ) (U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (r i)) ℝ)
        (V₀ : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (Fin (s i)) ℝ)
        (X : Fin (m + 1) → Tensor ι) (K : Fin m → Tensor ι) (YS : Fin m → ℝ → Tensor ι)
        (YC : ℝ → Tensor ι),
        (∀ i, (U₁ i)ᵀ * U₁ i = 1) ∧ (∀ i, (V₀ i)ᵀ * V₀ i = 1) ∧
        IsTuckerKSLStep F ε (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
          (fun i => (cs i).subtreeProj (U₁ i)) t₀ t₁ Y₀ X K YS YC ∧
        (∀ i, Exactness.IsRecoverable (Set.range (Tensor.actOn (ι := ι) (· ∈ (cs i).modes)))
          (Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ)) (A t₁)) ∧
        (∀ i, IsNondegenerateProjectorSplittingStep (cs i)
          (fun t => X i.castSucc + (Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ) *
            modePrefix (fun i => (cs i).subtreeProj (U₁ i)) (i : ℕ)) (A t - A t₀))
          (kslModeField (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
            (fun i => (cs i).subtreeProj (U₁ i)) F i) ε t₀ t₁ (X i.castSucc) (K i)) ∧
        YC t₁ = Y₁

/-- Non-degenerate steps are steps of the recursive projector-splitting integrator. -/
theorem IsNondegenerateProjectorSplittingStep.isProjectorSplittingStep :
    ∀ {τ : DimTree κ} {A : ℝ → Tensor ι} {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
      {Y₀ Y₁ : Tensor ι}, τ.IsNondegenerateProjectorSplittingStep A F ε t₀ t₁ Y₀ Y₁ →
      τ.IsProjectorSplittingStep F ε t₀ t₁ Y₀ Y₁
  | .leaf _, _, _, _, _, _, _, _, h => h
  | .node _, _, _, _, _, _, _, _, ⟨r, s, U₁, V₀, X, K, YS, YC, hU, hV, hs, _, hch, hY⟩ =>
      ⟨r, s, U₁, V₀, X, K, YS, YC, hU, hV, hs,
        fun i => (hch i).isProjectorSplittingStep, hY⟩

/-- **Exactness of the recursive TTN projector-splitting integrator** (Ceruti–Lubich–Walach,
arXiv 2002.11392, Theorem 5.1). Let `F(t, Y) = Ȧ(t)` on `[t₀, t₁]` (`IsDerivRHS`). A step of the
integrator from `Y₀ = A(t₀)` that is non-degenerate for `A` (condition (5.2), abstract form; see
the module docstring) reproduces `A(t₁)` exactly. -/
theorem IsNondegenerateProjectorSplittingStep.eq :
    ∀ {τ : DimTree κ} {A : ℝ → Tensor ι} {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
      {Y₀ Y₁ : Tensor ι}, t₀ ≤ t₁ → IsDerivRHS F A t₀ t₁ → Y₀ = A t₀ →
      τ.IsNondegenerateProjectorSplittingStep A F ε t₀ t₁ Y₀ Y₁ → Y₁ = A t₁
  | .leaf _, A, F, _, t₀, t₁, Y₀, Y₁, ht, hA, hY₀, ⟨y, hy, hy₀, hy₁⟩ => by
    have h := hy.eq_add_map_sub (ContinuousLinearMap.id ℝ (Tensor ι)) hA.cont
      (fun t ht => hA.deriv t ht (y t)) (fun _ _ => rfl) t₁ ⟨ht, le_rfl⟩
    rw [← hy₁, h, hy₀, hY₀]
    simp
  | .node (m := m) cs, A, F, ε, t₀, t₁, Y₀, Y₁, ht, hA, hY₀,
      ⟨r, s, U₁, V₀, X, K, YS, YC, _, _, hs, hrec, hch, hY⟩ => by
    subst hY₀
    set Q : Fin m → Tensor ι →L[ℝ] Tensor ι :=
      fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ) with hQ
    set P : Fin m → Tensor ι →L[ℝ] Tensor ι := fun i => (cs i).subtreeProj (U₁ i) with hP
    set B : Fin m → ℝ → Tensor ι :=
      fun i t => X i.castSucc + (Q i * modePrefix P (i : ℕ)) (A t - A t₀) with hB
    have hBd : ∀ i, IsDerivRHS (kslModeField Q P F i) (B i) t₀ t₁ := fun i =>
      { cont := continuousOn_const.add ((Q i * modePrefix P (i : ℕ)).continuous.comp_continuousOn
          (hA.cont.sub continuousOn_const))
        deriv := fun t ht Y => by
          have h := ((Q i * modePrefix P (i : ℕ)).hasFDerivAt.comp_hasDerivWithinAt t
            ((hA.deriv t ht Y).sub_const (A t₀))).const_add (X i.castSucc)
          exact h }
    have hB₀ : ∀ i, X i.castSucc = B i t₀ := fun i => by simp [hB]
    have hK : ∀ i, K i = B i t₁ := fun i => (hch i).eq ht (hBd i) (hB₀ i)
    have hexact : IsExactKSteps F Q P t₀ t₁ X K := fun i =>
      ⟨B i, ⟨(hBd i).cont, fun t ht => (hBd i).deriv t ht (B i t)⟩, (hB₀ i).symm, (hK i).symm⟩
    rw [← hY]
    exact tucker_ksl_exact ht hA hs hexact (𝓛 := fun i =>
      Set.range (Tensor.actOn (ι := ι) (· ∈ (cs i).modes))) (fun i => ⟨U₁ i * (U₁ i)ᵀ, rfl⟩)
      hrec

/-! ### Non-vacuity -/

/-- Non-vacuity of `IsNondegenerateProjectorSplittingStep` at an inner node: on the valid tree
with two leaves (modes `0` and `1` of dimension one), the zero field reproduces the zero trajectory
with rank-zero bases, and the recoverability conditions hold. -/
example : (node ![leaf (0 : Fin 2), leaf 1]).IsNondegenerateProjectorSplittingStep
    (ι := fun _ : Fin 2 => Fin 1) (fun _ => 0) (fun _ _ => 0) 0 0 1 0 0 := by
  have hv : (node ![leaf (0 : Fin 2), leaf 1]).IsValid := by
    refine ⟨fun i => by fin_cases i <;> trivial, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all
  have hz : ODESolution (fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1)))
      (fun _ => 0) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ _ => 0, fun _ => 0, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
    hv.isTuckerKSLStep (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _) rfl
      (fun _ => map_zero _) (fun _ => map_zero _) (fun _ t _ => by simp)
      (fun _ => by simpa using hz) (fun _ => rfl) (fun _ => rfl) (by simpa using hz) rfl,
    fun _ => ⟨0, fun _ _ _ => by simp, by simp⟩, fun i => ?_, rfl⟩
  fin_cases i <;>
  · refine ⟨fun _ => 0, ?_, rfl, rfl⟩
    convert hz using 1
    funext t x
    simp [kslModeField]

end DimTree

end LeanDLRA
