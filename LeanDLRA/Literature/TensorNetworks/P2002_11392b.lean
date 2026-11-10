import LeanDLRA.Tensor.TTN.Basic

/-!
# Results of arXiv 2002.11392: Time integration of tree tensor networks (part b)

Ceruti–Lubich–Walach, *Time integration of tree tensor networks*, arXiv 2002.11392. Part a
(`LeanDLRA/Literature/TensorNetworks/P2002_11392a.lean`) has the abstract forms of Lemma 4.1 and
of the `L`- and `B`-parts of Lemma 6.2. This module proves Lemma 2.4 and records where the other
results of the paper are in the library.

## Results of the paper and where they are

* Definitions 2.1–2.3 (trees, tree tensor networks, orthonormality): `DimTree`, `TTN`,
  `TTN.basis`, `TTN.IsOrthonormal` (`LeanDLRA/Tensor/Defs.lean`).
* **Lemma 2.4**: `basis_transpose_mul_self_iff` (this module, the equivalence as printed); its
  recursive consequence for orthonormal tree tensor networks is `TTN.basis_transpose_mul_self`.
* Algorithms 4–6 (the recursive TTN integrator): `DimTree.IsProjectorSplittingStep`, whose nodes
  are nested Tucker projector-splitting steps (`IsTuckerKSLStep`) with
  subtree and co-range projectors of orthonormal matrices.
* **Lemma 4.1** (restriction and prolongation): abstractly `restriction_prolongation` (part a); for
  the concrete maps `π = DimTree.prolong τ V`, `π† = DimTree.restrict τ V` of a child of the root:
  `DimTree.restrict_prolong` (4.8), `DimTree.inner_prolong`, `DimTree.adjoint_prolong` (4.9),
  `DimTree.norm_prolong`, `DimTree.norm_restrict_le`, and `π π† = Q₀`
  (`DimTree.prolong_restrict`).
* **Definition 4.2** (reduced functions and initial data): the reduced problem
  `ẏ = π† F(t, π y)`, `y(t₀) = π†(Y⁰)`, is conjugate to the `K`-step problem `ż = Q₀ F(t, z)` on the
  full tensor space (`DimTree.odeSolution_kStep_of_reduced`,
  `DimTree.odeSolution_reduced_of_kStep`), which is how the library poses the subtree problems.
* **Theorem 5.1** (exactness): `DimTree.IsNondegenerateProjectorSplittingStep.eq`, with the
  non-degeneracy condition (5.2) in the library's recoverability form (`Exactness.IsRecoverable`
  modulo the operators acting on the modes of each subtree), imposed on the restricted targets.
* **Theorem 6.1** (robust error bound): `DimTree.projectorSplitting_global_error` for concrete tree
  tensor networks, with constants depending only on the tree, `L`, `B` and `t*` (uniformly in the
  mode dimensions and ranks); abstract form `OpenProblems.TensorNetworks.ttn_ksl_global_error`.
  **Conditional**: the paper's normal-component assumption (6.3) on the TTN manifold is replaced
  by the per-node doubly-normal bounds `‖(1 - P₁ i)(1 - Q₀ i) P₁ 0 ⋯ P₁ (i-1) F_τ(t, Kᵢ)‖ ≤ ε` of
  the nested Tucker steps (the consequence of Lemma 6.2 that the paper's Tucker analysis uses),
  `F` is Lipschitz and bounded on the whole tensor space, and the ball condition `‖Yⁿ‖ ≤ ρ` is
  not needed.
* **Lemma 6.2**, `L`- and `B`-parts: `reduced_field_lipschitz_bounded` (part a, abstract, for any
  `π` with `π† π = 1`); the concrete `π = DimTree.prolong τ V` satisfies `π† π = 1`
  (`DimTree.restrict_prolong`, `DimTree.adjoint_prolong`).

## Not formalized

* Lemma 2.5 and Lemmas 4.3–4.4 (the TTN manifold, full tree rank of the restricted initial data
  and of prolongations): the library has no TTN manifold.
* Lemma 3.1 (the subflow `Φ⁽⁰⁾` of the extended Tucker integrator is trivial): in the library's
  formulation the subproblems are prolongated to the full tensor space, which has no root index,
  so the subflow `Φ⁽⁰⁾` does not occur; moreover the library uses the forward formulation of the
  `S`-step, for which the backward-in-time argument of the proof does not apply verbatim.
* The `ε`-part (6.7) of Lemma 6.2 and Lemma 6.3 (tangent spaces of the TTN manifolds).
* Lemma 4.5 (computational complexity) is not a mathematical statement about the integrator.
-/

open Set
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2002_11392

open LeanDLRA

variable {κ : Type*} [DecidableEq κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

/-- **Lemma 2.4 of arXiv 2002.11392.** For a tree `τ = (τ₁, …, τ_m)` (a valid dimension tree) let
the basis matrices `U_{τᵢ}` of the subtrees have orthonormal columns. Then the basis matrix
`U_τ = (⊗ᵢ U_{τᵢ}) Mat₀(C_τ)ᵀ` has orthonormal columns if and only if `Mat₀(C_τ)ᵀ` has orthonormal
columns, i.e. `Mat₀(C_τ) Mat₀(C_τ)ᵀ = 1` (the connecting tensor is stored as its root
matricization `C`). The paper requires `m ≥ 2`; the statement holds for every `m`. -/
theorem basis_transpose_mul_self_iff {m : ℕ} {cs : Fin m → DimTree κ}
    (hv : (DimTree.node cs).IsValid) {rs : Fin m → ℕ} {r : ℕ} (ds : ∀ i, TTN ι (cs i) (rs i))
    (C : Matrix (Fin r) (∀ i, Fin (rs i)) ℝ) (hds : ∀ i, ((ds i).basis)ᵀ * (ds i).basis = 1) :
    ((TTN.node ds C).basis)ᵀ * (TTN.node ds C).basis = 1 ↔ C * Cᵀ = 1 := by
  set P : Matrix (∀ k : {k // k ∈ (DimTree.node cs).modes}, ι k) (∀ i, Fin (rs i)) ℝ :=
    Matrix.of fun x b => ∏ i, (ds i).basis (fun k => x ⟨k.1, DimTree.mem_modes_node i k.2⟩)
      (b i) with hP
  have hPP : Pᵀ * P = 1 := by
    ext b b'
    rw [Matrix.mul_apply]
    simp only [hP, Matrix.transpose_apply, Matrix.of_apply, ← Finset.prod_mul_distrib]
    rw [hv.sum_prod_restrict (fun i y => (ds i).basis y (b i) * (ds i).basis y (b' i))]
    have hi : ∀ i, ∑ y, (ds i).basis y (b i) * (ds i).basis y (b' i) =
        if b i = b' i then 1 else 0 := fun i => by
      have := congrFun (congrFun (hds i) (b i)) (b' i)
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    simp only [hi, Matrix.one_apply]
    by_cases hb : b = b'
    · subst hb; simp
    · obtain ⟨i, hi'⟩ := Function.ne_iff.mp hb
      rw [ite_eq_right_iff.mpr fun h => (hb h).elim]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])
  rw [TTN.basis_node_eq, ← hP, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul]

/-- Non-vacuity of Lemma 2.4: on the tree with two leaves `0`, `1` (dimension two), leaf bases equal
to the identity satisfy the hypotheses, and the connecting tensor `C = e_{(0, 0)}ᵀ` (root rank one)
gives an orthonormal basis matrix. -/
example :
    let C : Matrix (Fin 1) (∀ _ : Fin 2, Fin 2) ℝ :=
      Matrix.of fun _ b => if b = fun _ => 0 then 1 else 0
    let t := TTN.node (ι := fun _ : Fin 2 => Fin 2) (cs := fun i : Fin 2 => DimTree.leaf i)
      (fun i => TTN.leaf (k := i) (1 : Matrix (Fin 2) (Fin 2) ℝ)) C
    t.basisᵀ * t.basis = 1 := by
  intro C t
  refine (basis_transpose_mul_self_iff (cs := fun i : Fin 2 => DimTree.leaf i)
    ⟨fun _ => trivial, fun _ _ hij => Finset.disjoint_singleton.2 hij⟩ _ C fun i =>
      TTN.basis_transpose_mul_self _ trivial (by simp [TTN.IsOrthonormal])).2 ?_
  ext a a'
  fin_cases a; fin_cases a'
  rw [Matrix.mul_apply]
  simp [C]

end LeanDLRA.Literature.P2002_11392
