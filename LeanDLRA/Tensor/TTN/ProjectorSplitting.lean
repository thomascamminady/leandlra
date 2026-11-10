import LeanDLRA.Tensor.TTN.Integrators
import LeanDLRA.Tensor.TTN.Abstract.ProjectorSplitting
import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Galerkin

/-!
# The recursive TTN projector-splitting integrator on concrete tree tensor networks

The recursive tree tensor network (TTN) projector-splitting integrator of Ceruti–Lubich–Walach
(arXiv 2002.11392, §4, Algorithms 4–6) is stated on an abstract inner product space
(`Tensor/Steps.lean`), with the projectors of every inner node existentially quantified
(`IsTTNKSLStep` over a `TreeShape`); its robust global error bound
(`ttn_ksl_global_error`, Thm 6.1 of the paper) holds for every family of commuting orthogonal
projectors. This file realizes the integrator on actual tensors `Tensor ι` over a dimension tree
`τ : DimTree κ`: at an inner node `τ = (τ₁, …, τ_m)` the new basis projector of child `i` is the
subtree projector `Z ↦ Ten_{τᵢ}(U¹ᵢ U¹ᵢᵀ Mat_{τᵢ}(Z))` of a basis matrix `U¹ᵢ` with orthonormal
columns (rows indexed by the modes of `τᵢ`), and the `K`-step projector is the co-range projector
`Z ↦ Ten_{τᵢ}(Mat_{τᵢ}(Z) V⁰ᵢ V⁰ᵢᵀ)` of a matrix `V⁰ᵢ` with orthonormal columns (rows indexed by
the complementary modes).

## The paper's reduced problems and the prolongated formulation

The paper poses the subproblem of child `τᵢ` on the small space `V_{τᵢ}` through the prolongation
`π_{τ,i}(Y) = Tenᵢ((V⁰ᵢ Mat₀(Y))ᵀ)` and the restriction `π†_{τ,i}`, with reduced field
`F_{τᵢ} = π† ∘ F_τ ∘ π` and reduced initial value `π†(Y⁰_τ)` (Definition 4.2). Since
`π† π = 1` and `π π† = Q₀ i` is the co-range projector (Lemma 4.1), the reduced problem is
conjugate by `π` to the `K`-step problem `Ż = Q₀ i F(t, Z)` posed on the full tensor space
(`odeSolution_prolong`, `odeSolution_restrict`). This file therefore works in the full tensor
space throughout, as the abstract integrator does: the subtree step of child `i` is a step of the
same integrator for the field `kslModeField Q₀ P₁ F i = Q₀ i (P₁ 0 ⋯ P₁ (i-1)) F`, and the
prolongated co-range projectors of deeper nodes are again of the form
`actOn {k ∉ σ} (W Wᵀ)` with `Wᵀ W = 1` (`W = (V⁰ᵢ ⊗ 1) Ṽ` for the co-range basis `Ṽ` of the
reduced problem).

## Main definitions

* `DimTree.IsProjectorSplittingStep`: one step of the recursive TTN projector-splitting integrator
  on concrete tree tensor networks.

## Main results

* `odeSolution_prolong`, `odeSolution_restrict`: the reduced problem `ẏ = π† F(t, π y)` of the
  paper and the projected problem `ż = π π† F(t, z)` are conjugate by an isometry `π`.
* `DimTree.isProjectorSplittingStep_node`: on a valid dimension tree, orthonormal bases and the
  substep conditions give a node step; orthogonality and commutation of the projectors are
  derived (`DimTree.IsValid.isTuckerKSLStep`).
* `DimTree.IsProjectorSplittingStep.isTTNKSLStep`: every concrete step is a step of the abstract
  integrator over the shape `τ.toTreeShape`.
* `DimTree.projectorSplitting_global_error`: the robust error bound
  `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h` (arXiv 2002.11392, Thm 6.1) with constants depending only on
  the tree, `L`, `B` and `T`, uniformly in the mode dimensions and ranks.
-/

open Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA

/-! ### Reduced problems and prolongation -/

section Prolongation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Prolongation of a reduced trajectory** (arXiv 2002.11392, Definition 4.2). If `y` solves the
reduced problem `ẏ = π† G(t, π y)` on the small space `F`, then `π y` solves the projected
problem `ż = (π π†) G(t, z)` on the big space `E`. -/
theorem odeSolution_prolong (π : F →L[ℝ] E) {G : ℝ → E → E} {y : ℝ → F} {a b : ℝ}
    (hy : ODESolution (fun t x => π.adjoint (G t (π x))) y a b) :
    ODESolution (fun t z => (π.comp π.adjoint) (G t z)) (fun t => π (y t)) a b where
  cont := π.continuous.comp_continuousOn hy.cont
  deriv t ht := π.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)

/-- **Restriction of a projected trajectory** (arXiv 2002.11392, Definition 4.2). Let
`π† π = 1`. If `z` solves `ż = (π π†) G(t, z)` with `z a = π y₀`, then `y = π† z` solves the
reduced problem `ẏ = π† G(t, π y)` with `y a = y₀`, and `z = π y` on `[a, b]`. -/
theorem odeSolution_restrict (π : F →L[ℝ] E) (hπ : ∀ y, π.adjoint (π y) = y)
    {G : ℝ → E → E} {z : ℝ → E} {a b : ℝ}
    (hz : ODESolution (fun t x => (π.comp π.adjoint) (G t x)) z a b) {y₀ : F} (hz₀ : z a = π y₀) :
    ODESolution (fun t x => π.adjoint (G t (π x))) (fun t => π.adjoint (z t)) a b ∧
      π.adjoint (z a) = y₀ ∧ ∀ t ∈ Icc a b, π (π.adjoint (z t)) = z t := by
  have hQ : IsOrthProj (π.comp π.adjoint) := by
    refine ⟨fun x => ?_, fun x w => ?_⟩
    · change π (π.adjoint (π (π.adjoint x))) = π (π.adjoint x)
      rw [hπ]
    · change ⟪π (π.adjoint x), w⟫ = ⟪x, π (π.adjoint w)⟫
      rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  have hfix : ∀ t ∈ Icc a b, π (π.adjoint (z t)) = z t := by
    intro t ht
    have h := normal_const_of_deriv_mem_range hQ hz.cont (G := fun t => G t (z t)) hz.deriv t ht
    have h0 : z a - (π.comp π.adjoint) (z a) = 0 := by
      rw [hz₀]
      change π y₀ - π (π.adjoint (π y₀)) = 0
      rw [hπ, sub_self]
    rw [h0] at h
    exact (sub_eq_zero.1 h).symm
  refine ⟨⟨π.adjoint.continuous.comp_continuousOn hz.cont, fun t ht => ?_⟩, ?_, hfix⟩
  · have h := π.adjoint.hasFDerivAt.comp_hasDerivWithinAt t (hz.deriv t ht)
    have e : π.adjoint ((π.comp π.adjoint) (G t (z t))) =
        π.adjoint (G t (π (π.adjoint (z t)))) := by
      rw [hfix t (Ico_subset_Icc_self ht)]
      change π.adjoint (π (π.adjoint (G t (z t)))) = _
      rw [hπ]
    simpa only [Function.comp_def, e] using h
  · rw [hz₀, hπ]

end Prolongation

namespace DimTree

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-! ### The concrete recursive projector-splitting step -/

/-- One step of the **recursive TTN projector-splitting integrator** (Ceruti–Lubich–Walach,
arXiv 2002.11392, Algorithms 4–6) on concrete tree tensor networks of the dimension tree `τ`, for
the field `F` on the full tensor space, from `(t₀, Y₀)` to `(t₁, Y₁)` with doubly-normal bound `ε`:

* at a **leaf** the step is the exact flow of `F` (Algorithm 5: the leaf matrix differential
  equation is solved exactly);
* at an **inner node** `τ = (τ₁, …, τ_m)` there are new subtree bases `U¹ᵢ` and co-range bases
  `V⁰ᵢ` with orthonormal columns such that, with the subtree projectors
  `P₁ i = (τᵢ).subtreeProj U¹ᵢ` and the co-range projectors `Q₀ i = actOn {k ∉ τᵢ} (V⁰ᵢ V⁰ᵢᵀ)`,
  the nested Tucker projector-splitting conditions hold (`IsTuckerKSLStep`: `Q₀ i` fixes the
  state `X i` before mode `i`, `P₁ i` captures the `K`-value `K i`, the backward `S`-step and the
  final core step `Ψ_τ`), and every `K`-value is computed by the same integrator on the subtree
  `τᵢ` for the `K`-step field `kslModeField Q₀ P₁ F i` from `X i` (the prolongated reduced problem
  of Definition 4.2; see the module docstring). The result is `Y₁ = YC t₁`. -/
def IsProjectorSplittingStep : DimTree κ → (ℝ → Tensor ι → Tensor ι) → ℝ → ℝ → ℝ →
    Tensor ι → Tensor ι → Prop
  | .leaf _, F, _, t₀, t₁, Y₀, Y₁ =>
      ∃ y : ℝ → Tensor ι, ODESolution F y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁
  | .node (m := m) cs, F, ε, t₀, t₁, Y₀, Y₁ =>
      ∃ (r s : Fin m → ℕ) (U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (r i)) ℝ)
        (V₀ : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (Fin (s i)) ℝ)
        (X : Fin (m + 1) → Tensor ι) (K : Fin m → Tensor ι) (YS : Fin m → ℝ → Tensor ι)
        (YC : ℝ → Tensor ι),
        (∀ i, (U₁ i)ᵀ * U₁ i = 1) ∧ (∀ i, (V₀ i)ᵀ * V₀ i = 1) ∧
        IsTuckerKSLStep F ε (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
          (fun i => (cs i).subtreeProj (U₁ i)) t₀ t₁ Y₀ X K YS YC ∧
        (∀ i, IsProjectorSplittingStep (cs i)
          (kslModeField (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
            (fun i => (cs i).subtreeProj (U₁ i)) F i) ε t₀ t₁ (X i.castSucc) (K i)) ∧
        YC t₁ = Y₁

/-- A leaf step is the exact flow. -/
@[simp] lemma isProjectorSplittingStep_leaf (k : κ) {F : ℝ → Tensor ι → Tensor ι}
    {ε t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι} :
    (leaf k).IsProjectorSplittingStep F ε t₀ t₁ Y₀ Y₁ ↔
      ∃ y : ℝ → Tensor ι, ODESolution F y t₀ t₁ ∧ y t₀ = Y₀ ∧ y t₁ = Y₁ :=
  Iff.rfl

/-- **Node steps from the substeps.** At an inner node of a valid dimension tree, new subtree
bases `U¹ᵢ` and co-range bases `V⁰ᵢ` with orthonormal columns, the substep conditions of the
nested Tucker projector-splitting step and subtree steps for the `K`-step fields give a step of
the recursive integrator. Orthogonality of all projectors and commutation of the `P₁ i` are
derived, not assumed. -/
theorem isProjectorSplittingStep_node {m : ℕ} {cs : Fin m → DimTree κ}
    (hv : (node cs).IsValid) {r s : Fin m → ℕ}
    {U₁ : ∀ i, Matrix (∀ k : {k // k ∈ (cs i).modes}, ι k) (Fin (r i)) ℝ}
    (hU₁ : ∀ i, (U₁ i)ᵀ * U₁ i = 1)
    {V₀ : ∀ i, Matrix (∀ k : {k // k ∉ (cs i).modes}, ι k) (Fin (s i)) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ}
    {Y₀ Y₁ : Tensor ι} {X : Fin (m + 1) → Tensor ι} {K : Fin m → Tensor ι}
    {YS : Fin m → ℝ → Tensor ι} {YC : ℝ → Tensor ι}
    (start : X 0 = Y₀)
    (qFix : ∀ i, Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ) (X i.castSucc) = X i.castSucc)
    (kCap : ∀ i, (cs i).subtreeProj (U₁ i) (K i) = K i)
    (kNormal : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ‖(1 - (cs i).subtreeProj (U₁ i))
      ((1 - Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
        (modePrefix (fun i => (cs i).subtreeProj (U₁ i)) (i : ℕ) (F t (K i))))‖ ≤ ε)
    (sSol : ∀ i, ODESolution (fun t x => -((cs i).subtreeProj (U₁ i)
      (Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ)
        (modePrefix (fun i => (cs i).subtreeProj (U₁ i)) (i : ℕ) (F t x))))) (YS i) t₀ t₁)
    (sStart : ∀ i, YS i t₀ = K i) (next : ∀ i, X i.succ = YS i t₁)
    (cSol : ODESolution (fun t x => modeProd (fun i => (cs i).subtreeProj (U₁ i)) (F t x))
      YC t₀ t₁)
    (cStart : YC t₀ = X (Fin.last m))
    (sub : ∀ i, (cs i).IsProjectorSplittingStep
      (kslModeField (fun i => Tensor.actOn (· ∉ (cs i).modes) (V₀ i * (V₀ i)ᵀ))
        (fun i => (cs i).subtreeProj (U₁ i)) F i) ε t₀ t₁ (X i.castSucc) (K i))
    (hY : YC t₁ = Y₁) :
    (node cs).IsProjectorSplittingStep F ε t₀ t₁ Y₀ Y₁ :=
  ⟨r, s, U₁, V₀, X, K, YS, YC, hU₁, hV₀,
    hv.isTuckerKSLStep hU₁ hV₀ start qFix kCap kNormal sSol sStart next cSol cStart, sub, hY⟩

/-- **Concrete steps are abstract steps.** Every step of the recursive TTN projector-splitting
integrator on concrete tree tensor networks of the dimension tree `τ` is a step of the abstract
recursive integrator `IsTTNKSLStep` of shape `τ.toTreeShape`. -/
theorem IsProjectorSplittingStep.isTTNKSLStep :
    ∀ {τ : DimTree κ} {F : ℝ → Tensor ι → Tensor ι} {ε t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι},
      τ.IsProjectorSplittingStep F ε t₀ t₁ Y₀ Y₁ → IsTTNKSLStep τ.toTreeShape F ε t₀ t₁ Y₀ Y₁
  | .leaf _, _, _, _, _, _, _, h => h
  | .node _, _, _, _, _, _, _, ⟨_, _, _, _, X, K, YS, YC, _, _, hs, hch, hY⟩ =>
      ⟨_, _, X, K, YS, YC, hs, fun i => (hch i).isTTNKSLStep, hY⟩

/-- **Robust error bound of the recursive TTN projector-splitting integrator on concrete tree
tensor networks** (Ceruti–Lubich–Walach, arXiv 2002.11392, Theorem 6.1). For every dimension tree
`τ` and `L, B, T ≥ 0` there are constants `c₀, c₁, c₂` such that, for all mode dimensions, all
ranks and all fields `F` on the tensor space that are `L`-Lipschitz and bounded by `B`, `N` steps
of the integrator with step size `h ≥ 0`, `N h ≤ T`, from `Y 0` with `‖Y 0 - A t₀‖ ≤ δ` satisfy
`‖Y n - A (t₀ + n h)‖ ≤ c₀ δ + c₁ ε + c₂ h`, where `A` is the exact solution and `ε` the
doubly-normal bound of the node steps. The exact flows from the numerical values exist because
`F` is continuous in time. -/
theorem projectorSplitting_global_error.{v} (τ : DimTree κ) {L B T : ℝ} (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ {ι : κ → Type v} [∀ k, Fintype (ι k)] {F : ℝ → Tensor ι → Tensor ι}
      {ε δ t₀ h : ℝ} {N : ℕ} {A : ℝ → Tensor ι} {Y : ℕ → Tensor ι},
      IsLipschitzField F L → IsBoundedField F B → (∀ x, Continuous fun t => F t x) → 0 ≤ ε →
      0 ≤ h → (N : ℝ) * h ≤ T → ODESolution F A t₀ (t₀ + N * h) →
      (∀ n < N, τ.IsProjectorSplittingStep F ε (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
        (Y (n + 1))) →
      ‖Y 0 - A t₀‖ ≤ δ →
      ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ c₀ * δ + c₁ * ε + c₂ * h := by
  obtain ⟨c₀, c₁, c₂, hc⟩ := ttn_ksl_global_error.{max u_1 v} τ.toTreeShape hL hB hT
  refine ⟨c₀, c₁, c₂, ?_⟩
  intro ι _ F ε δ t₀ h N A Y hF hBf hcont hε hh hNh hA hstep hδ n hn
  have hex : ∀ n : ℕ, ∃ Φ : ℝ → Tensor ι, ODESolution F Φ (t₀ + n * h) (t₀ + (n + 1) * h) ∧
      Φ (t₀ + n * h) = Y n := fun n =>
    exists_ODESolution hF hBf hcont (by nlinarith) (Y n)
  choose Φ hΦ hΦ₀ using hex
  exact hc hF hBf hε hh hNh hA (fun n hn => (hstep n hn).isTTNKSLStep) (fun n _ => hΦ n)
    (fun n _ => hΦ₀ n) hδ n hn

/-! ### Non-vacuity -/

/-- Non-vacuity of `IsProjectorSplittingStep` at an inner node: on the valid tree with two leaves
(modes `0` and `1` of dimension one), the zero field with the zero tensor and rank-zero bases is
a step of the integrator. -/
example : (node ![leaf (0 : Fin 2), leaf 1]).IsProjectorSplittingStep
    (ι := fun _ : Fin 2 => Fin 1) (fun _ _ => 0) 0 0 1 0 0 := by
  have hv : (node ![leaf (0 : Fin 2), leaf 1]).IsValid := by
    refine ⟨fun i => by fin_cases i <;> trivial, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all
  have hz : ODESolution (fun _ _ => (0 : Tensor (fun _ : Fin 2 => Fin 1)))
      (fun _ => 0) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) _⟩
  refine isProjectorSplittingStep_node hv (r := fun _ => 0) (s := fun _ => 0) (U₁ := fun _ => 0)
    (fun _ => Subsingleton.elim _ _) (V₀ := fun _ => 0) (fun _ => Subsingleton.elim _ _)
    (X := fun _ => 0) (K := fun _ => 0) (YS := fun _ _ => 0) (YC := fun _ => 0) rfl
    (fun _ => map_zero _) (fun _ => map_zero _) (fun _ t _ => by simp) (fun _ => ?_)
    (fun _ => rfl) (fun _ => rfl) ?_ rfl (fun i => ?_) rfl
  · simpa using hz
  · simpa using hz
  · fin_cases i <;>
    · refine ⟨fun _ => 0, ?_, rfl, rfl⟩
      convert hz using 1
      funext t x
      simp [kslModeField]

end DimTree

end LeanDLRA
