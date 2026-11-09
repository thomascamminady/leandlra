import LeanDLRA.Foundations.OneSided
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generalization gap of gradients of input convex networks (arXiv 2201.10364)

Schotthöfer, Xiao, Frank and Hauck, *Neural network-based, structure-preserving entropy closures
for the Boltzmann moment system* (arXiv 2201.10364).  Section 4.3 bounds the error of the
gradient of an input convex neural network `N_θ` trained in Sobolev norm on a convex function
`f*` (here the entropy of the moment closure): if the gradients agree at `d + 1` training points
`x₀, …, x_d ∈ ℝ^d` whose convex hull contains the point of interest `x* = 0` in its interior, then
the gradient of every convex function with these gradients lies in the set of feasible
gradients `A = {v : v · xᵢ ≤ ∇f*(xᵢ) · xᵢ}` (Eq. (83)), and

* **Theorem 1**: `A` is the bounded polyhedron with the `d + 1` faces
  `Fᵢ = {v : v · xᵢ = ∇f*(xᵢ) · xᵢ}` and the vertices `vᵢ = ⋂_{j ≠ i} F_j` (Eq. (85));
* **Eq. (100)**: `‖∇f*(x*) - ∇N_θ(x*)‖ ≤ diam(A)`;
* **Theorem 2**: for unit vectors `xᵢ`, `‖vᵢ - vⱼ‖ ≤ (‖Xᵢ⁻¹‖ + ‖Xⱼ⁻¹‖) C_{x*}` (Eq. (102)), where
  `Xᵢ` has the rows `x_k`, `k ≠ i` (Eq. (101): `Xᵢ vᵢ = bᵢ`), `‖Xᵢ⁻¹‖` is its norm from
  `(ℝ^d, ‖·‖_∞)` to `(ℝ^d, ‖·‖₂)` and `C_{x*} = max_{k,l} ‖∇f*(x_k) - ∇f*(x_l)‖`; hence Eq. (109).

The rest of the paper (network architectures, sampling, simulations) is empirical; its scaling
relations (44)–(51) for normalized moments are formalized in `P2106_09445a`
(`alpha0_eq_neg_log_iff`, `isMultiplier_add_single_log_iff`, `entropy_scaling_one`).

## Formalization

The space is any real inner product space `E` of dimension `d` (`ℝ^d` in the paper).  The point
of interest is `0` (the paper's w.l.o.g. shift), and "`0` lies in the interior of
`C(X_d) = conv{x₀, …, x_d}`" is used in the form `IsInteriorConfig`: `0 = ∑ aᵢ xᵢ` with all
`aᵢ > 0` (the paper's Eq. (90)) and the `xᵢ` span `E` (this is what interiority of `0` in the hull
of `d + 1` points means).  Convexity of `f*` enters only through the monotonicity of its gradient
(the characterization the paper invokes), which is the core property that the gradient-flow field
`x ↦ -∇f(x)` is one-sided Lipschitz with constant `0`
(`isOneSidedLipschitzField_neg_gradient`).

## Main results

* `isOneSidedLipschitzField_neg_gradient`: convex `f` with gradient `g` ⇒ `-g` is one-sided
  Lipschitz with constant `0` (core `IsOneSidedLipschitzField`), i.e. `g` is monotone.
* `gradient_mem_feasibleSet`: the gradient at `0` of every such `f` lies in `A`.
* `existsUnique_vertex`: the vertices `vᵢ` are well defined (part 1 of the proof of Theorem 1).
* `IsVertex.mem_feasibleSet`: every vertex lies in `A` (part 2), by a direct argument from
  `∑ aⱼ xⱼ = 0` and a feasible point instead of the paper's sign argument (89)–(99).
* `feasibleSet_eq_convexHull`, `isBounded_feasibleSet`, `exists_vertices_feasibleSet_eq_convexHull`
  (**Theorem 1**): `A = conv{v₀, …, v_d}`, in particular bounded.
* `norm_gradient_sub_le_diam` (**Eq. (100)**): two convex functions with the same gradients at the
  training points have gradients at `0` at distance at most `diam{vᵢ} = diam A`.
* `IsVertex.inner_eq` (**Eq. (101)**), `norm_vertex_sub_le` (**Theorem 2**, Eq. (102)) and
  `norm_gradient_sub_le_of_invBound` (**Eq. (109)**).

No claim of the paper was found to be false.  The paper's sentence "all `xᵢ ∈ X_d` are linearly
independent" (proof of Theorem 1) is read as "every `d` of them are", which is what is used and
what `existsUnique_vertex` derives.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2201_10364

open LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

/-- The **set of feasible gradients** (Eq. (83)) at the point of interest `0` for training points
`xᵢ` (relative to `0`) with gradients `Gᵢ = ∇f*(xᵢ)`: `A = {v : v · xᵢ ≤ Gᵢ · xᵢ for all i}`. -/
def feasibleSet (x G : Fin (d + 1) → E) : Set E := {v | ∀ i, ⟪v, x i⟫ ≤ ⟪G i, x i⟫}

/-- `v` is the **vertex opposite the face `Fᵢ`** (Eq. (85)): it lies on every face `F_j`,
`j ≠ i`. -/
def IsVertex (x G : Fin (d + 1) → E) (i : Fin (d + 1)) (v : E) : Prop :=
  ∀ j, j ≠ i → ⟪v, x j⟫ = ⟪G j, x j⟫

/-- The point of interest `0` lies in the interior of the convex hull of `x₀, …, x_d`, in the form
used by the proofs: positive barycentric weights `0 = ∑ aᵢ xᵢ`, `aᵢ > 0` (Eq. (90)), and the
`xᵢ` span the space. -/
structure IsInteriorConfig (x : Fin (d + 1) → E) : Prop where
  weights : ∃ a : Fin (d + 1) → ℝ, (∀ i, 0 < a i) ∧ ∑ i, a i • x i = 0
  span : Submodule.span ℝ (Set.range x) = ⊤

/-! ### Convex functions have monotone gradients (core: one-sided Lipschitz) -/

/-- First-order condition of a differentiable convex function: `f y ≥ f x + ⟪∇f(x), y - x⟫`. -/
theorem inner_gradient_le_sub [CompleteSpace E] {f : E → ℝ} {g : E → E} (hf : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (x y : E) : ⟪g x, y - x⟫ ≤ f y - f x := by
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hφ : ConvexOn ℝ univ (f ∘ L) := by
    simpa using hf.comp_affineMap L
  have hd : HasDerivAt (f ∘ L) ⟪g x, y - x⟫ 0 := by
    have h1 := (hasGradientAt_iff_hasFDerivAt.1 (hg x))
    have h2 : HasDerivAt (L : ℝ → E) (y - x) 0 := AffineMap.hasDerivAt_lineMap
    have h3 := h1.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp [L])
    simpa using h3
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simpa [slope, L, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using this

/-- **The negative gradient of a convex function is one-sided Lipschitz with constant `0`**
(core `IsOneSidedLipschitzField`), i.e. the gradient is monotone,
`⟪∇f(x) - ∇f(y), x - y⟫ ≥ 0` — the characterization of convexity used in Section 3.2.2 and in the
proof of Theorem 1. -/
theorem isOneSidedLipschitzField_neg_gradient [CompleteSpace E] {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) : IsOneSidedLipschitzField (fun _ x => -g x) 0 := by
  intro _ x y
  have h1 := inner_gradient_le_sub hf hg x y
  have h2 := inner_gradient_le_sub hf hg y x
  have e : ⟪g x, x - y⟫ = -⟪g x, y - x⟫ := by rw [← inner_neg_right, neg_sub]
  rw [neg_sub_neg, zero_mul, inner_sub_left, e]
  linarith

/-- **The gradient at the point of interest is feasible**: for a field `g` whose negative is
one-sided Lipschitz with constant `0` (e.g. the gradient of a convex function), `g 0 ∈ A` for the
gradients `Gᵢ = g(xᵢ)`. -/
theorem gradient_mem_feasibleSet {g : E → E} (hg : IsOneSidedLipschitzField (fun _ x => -g x) 0)
    (x : Fin (d + 1) → E) : g 0 ∈ feasibleSet x (fun i => g (x i)) := by
  intro i
  have h := hg 0 (x i) 0
  simp only [sub_zero, zero_mul, neg_sub_neg] at h
  rw [inner_sub_left] at h
  linarith

/-! ### Theorem 1: the feasible set is the simplex spanned by the vertices -/

section Theorem1

variable {x G : Fin (d + 1) → E}

/-- Points with the same inner products with all `xᵢ` coincide (the `xᵢ` span). -/
theorem IsInteriorConfig.eq_of_inner_eq (hx : IsInteriorConfig x) {u w : E}
    (h : ∀ i, ⟪u, x i⟫ = ⟪w, x i⟫) : u = w := by
  have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker (innerₛₗ ℝ (u - w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [h i]
  rw [hx.span] at hle
  have hmem := hle (Submodule.mem_top (x := u - w))
  rw [LinearMap.mem_ker] at hmem
  have h0 : ⟪u - w, u - w⟫ = 0 := hmem
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

/-- The weights give `∑ⱼ aⱼ ⟪v, xⱼ⟫ = 0` for every `v`. -/
lemma sum_weight_inner {a : Fin (d + 1) → ℝ} (ha : ∑ i, a i • x i = 0) (v : E) :
    ∑ j, a j * ⟪v, x j⟫ = 0 := by
  have : ⟪v, ∑ j, a j • x j⟫ = 0 := by rw [ha, inner_zero_right]
  rw [inner_sum] at this
  simpa [inner_smul_right] using this

/-- **Every vertex is feasible** (part 2 of the proof of Theorem 1): if `A` is nonempty, the
vertex `vᵢ` satisfies `vᵢ · xᵢ ≤ Gᵢ · xᵢ`. -/
theorem IsVertex.mem_feasibleSet (hx : IsInteriorConfig x) {i : Fin (d + 1)} {v : E}
    (hv : IsVertex x G i v) (hA : (feasibleSet x G).Nonempty) : v ∈ feasibleSet x G := by
  obtain ⟨g, hg⟩ := hA
  obtain ⟨a, ha, hsum⟩ := hx.weights
  intro j
  by_cases hj : j = i
  · subst hj
    have h1 := sum_weight_inner hsum g
    have h2 := sum_weight_inner hsum v
    have hdiff : ∑ k, a k * (⟪g, x k⟫ - ⟪v, x k⟫) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hdiff
    have hrest : ∑ k ∈ univ.erase j, a k * (⟪g, x k⟫ - ⟪v, x k⟫) ≤ 0 := by
      refine Finset.sum_nonpos fun k hk => ?_
      rw [hv k (Finset.ne_of_mem_erase hk)]
      exact mul_nonpos_of_nonneg_of_nonpos (ha k).le (sub_nonpos.2 (hg k))
    have h3 : 0 ≤ a j * (⟪g, x j⟫ - ⟪v, x j⟫) := by linarith
    have h4 : 0 ≤ ⟪g, x j⟫ - ⟪v, x j⟫ := nonneg_of_mul_nonneg_right h3 (ha j)
    linarith [hg j]
  · exact (hv j hj).le

/-- **The vertices are well defined** (part 1 of the proof of Theorem 1): in dimension `d`, for
every `i` there is exactly one point on all faces `F_j`, `j ≠ i`. -/
theorem existsUnique_vertex [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = d)
    (hx : IsInteriorConfig x) (G : Fin (d + 1) → E) (i : Fin (d + 1)) :
    ∃! v, IsVertex x G i v := by
  obtain ⟨a, ha, hsum⟩ := hx.weights
  let T : E →ₗ[ℝ] ({j // j ≠ i} → ℝ) :=
    { toFun := fun v j => ⟪v, x j⟫
      map_add' := fun u w => by funext j; simp [inner_add_left]
      map_smul' := fun c u => by funext j; simp [inner_smul_left] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hvj : ∀ j, j ≠ i → ⟪v, x j⟫ = 0 := fun j hj => congrFun hv ⟨j, hj⟩
    have h1 := sum_weight_inner hsum v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      Finset.sum_eq_zero fun j hj => by rw [hvj j (Finset.ne_of_mem_erase hj), mul_zero],
      add_zero] at h1
    have hvi : ⟪v, x i⟫ = 0 := (mul_eq_zero.1 h1).resolve_left (ha i).ne'
    refine hx.eq_of_inner_eq fun j => ?_
    rw [inner_zero_left]
    by_cases hj : j = i
    · rw [hj, hvi]
    · exact hvj j hj
  have hdim : Module.finrank ℝ E = Module.finrank ℝ ({j // j ≠ i} → ℝ) := by
    rw [hd, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_subtype_eq]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨v, hv⟩ := hsurj fun j => ⟪G j, x j⟫
  refine ⟨v, fun j hj => congrFun hv ⟨j, hj⟩, fun w hw => hinj ?_⟩
  funext j
  exact (hw j j.2).trans (congrFun hv j).symm

/-- **Theorem 1** (arXiv 2201.10364): if `0` is interior to `conv{xᵢ}` and the feasible set is
nonempty (e.g. `gradient_mem_feasibleSet`), then `A` is the simplex spanned by the vertices,
`A = conv{v₀, …, v_d}`. -/
theorem feasibleSet_eq_convexHull (hx : IsInteriorConfig x) {v : Fin (d + 1) → E}
    (hv : ∀ i, IsVertex x G i (v i)) (hA : (feasibleSet x G).Nonempty) :
    feasibleSet x G = convexHull ℝ (Set.range v) := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨a, ha, hsum⟩ := hx.weights
    set c : Fin (d + 1) → ℝ := fun j => ⟪G j, x j⟫
    set s : Fin (d + 1) → ℝ := fun j => c j - ⟪p, x j⟫ with hs
    set δ : Fin (d + 1) → ℝ := fun i => c i - ⟪v i, x i⟫ with hδ
    set S : ℝ := ∑ j, a j * c j
    have hvx : ∀ i j, ⟪v i, x j⟫ = c j - if j = i then δ i else 0 := by
      intro i j
      by_cases h : j = i
      · subst h; simp [hδ]
      · simp [h, hv i j h, c]
    have haδ : ∀ i, a i * δ i = S := by
      intro i
      have h := sum_weight_inner hsum (v i)
      simp only [hvx i, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
      have hSdef : S = ∑ j, a j * c j := rfl
      linarith
    have has : ∑ j, a j * s j = S := by
      have h := sum_weight_inner hsum p
      have hSdef : S = ∑ j, a j * c j := rfl
      simp only [hs, mul_sub, Finset.sum_sub_distrib, h, sub_zero, hSdef]
    have hs0 : ∀ j, 0 ≤ s j := fun j => sub_nonneg.2 (hp j)
    rcases (Finset.sum_nonneg fun j _ => mul_nonneg (ha j).le (hs0 j)).lt_or_eq' with hS | hS
    · rw [has] at hS
      set μ : Fin (d + 1) → ℝ := fun j => a j * s j / S
      have hμ0 : ∀ j ∈ Finset.univ, 0 ≤ μ j := fun j _ =>
        div_nonneg (mul_nonneg (ha j).le (hs0 j)) hS.le
      have hμ1 : ∑ j ∈ Finset.univ, μ j = 1 := by
        simp only [μ, ← Finset.sum_div, has, div_self hS.ne']
      have hpeq : p = ∑ j ∈ Finset.univ, μ j • v j := by
        refine hx.eq_of_inner_eq fun i => ?_
        rw [sum_inner]
        simp only [inner_smul_left, conj_trivial, hvx _ i, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hμ1, one_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ite_true]
        have : μ i * δ i = s i := by
          simp only [μ]
          rw [div_mul_eq_mul_div, div_eq_iff hS.ne', ← haδ i]
          ring
        rw [this, hs]; ring
      rw [hpeq]
      exact (convex_convexHull ℝ _).sum_mem hμ0 hμ1 fun j _ =>
        subset_convexHull ℝ _ ⟨j, rfl⟩
    · have hS' : ∑ j, a j * s j = 0 := by linarith [hS]
      rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (ha j).le (hs0 j)] at hS'
      have hs' : ∀ j, s j = 0 := fun j =>
        (mul_eq_zero.1 (hS' j (Finset.mem_univ j))).resolve_left (ha j).ne'
      have hp0 : p = v 0 := by
        refine hx.eq_of_inner_eq fun j => ?_
        have h1 : ⟪p, x j⟫ = c j := by linarith [hs' j]
        by_cases hj : j = 0
        · subst hj
          have hδ0 : δ 0 = 0 := by
            have h0 := haδ 0
            have hS0 : S = 0 := by rw [← has]; simp [hs']
            rw [hS0] at h0
            exact (mul_eq_zero.1 h0).resolve_left (ha 0).ne'
          rw [h1, hvx 0 0]; simp [hδ0]
        · rw [h1, hv 0 j hj]
      rw [hp0]
      exact subset_convexHull ℝ _ ⟨0, rfl⟩
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact (hv i).mem_feasibleSet hx hA
    · intro p hp q hq α β hα hβ hαβ j
      simp only [inner_add_left, inner_smul_left, conj_trivial]
      calc α * ⟪p, x j⟫ + β * ⟪q, x j⟫ ≤ α * ⟪G j, x j⟫ + β * ⟪G j, x j⟫ :=
            add_le_add (mul_le_mul_of_nonneg_left (hp j) hα) (mul_le_mul_of_nonneg_left (hq j) hβ)
        _ = ⟪G j, x j⟫ := by rw [← add_mul, hαβ, one_mul]

/-- **Theorem 1**, boundedness: `A` is a bounded polyhedron. -/
theorem isBounded_feasibleSet (hx : IsInteriorConfig x) {v : Fin (d + 1) → E}
    (hv : ∀ i, IsVertex x G i (v i)) (hA : (feasibleSet x G).Nonempty) :
    Bornology.IsBounded (feasibleSet x G) := by
  rw [feasibleSet_eq_convexHull hx hv hA, isBounded_convexHull]
  exact (Set.finite_range v).isBounded

/-- **Theorem 1** (arXiv 2201.10364) with the paper's hypotheses: for a convex `f*` with gradient
`g` on a space of dimension `d` and training points with `0` interior to their hull, the vertices
`vᵢ = ⋂_{j ≠ i} F_j` exist and the set of feasible gradients is the bounded simplex
`A = conv{v₀, …, v_d}`. -/
theorem exists_vertices_feasibleSet_eq_convexHull [FiniteDimensional ℝ E]
    (hd : Module.finrank ℝ E = d) {f : E → ℝ} {g : E → E} (hf : ConvexOn ℝ univ f)
    (hg : ∀ y, HasGradientAt f (g y) y) (hx : IsInteriorConfig x) :
    ∃ v : Fin (d + 1) → E, (∀ i, IsVertex x (fun j => g (x j)) i (v i)) ∧
      feasibleSet x (fun j => g (x j)) = convexHull ℝ (Set.range v) ∧
      Bornology.IsBounded (feasibleSet x fun j => g (x j)) := by
  choose v hv _ using fun i => existsUnique_vertex hd hx (fun j => g (x j)) i
  have hA : (feasibleSet x fun j => g (x j)).Nonempty :=
    ⟨_, gradient_mem_feasibleSet (isOneSidedLipschitzField_neg_gradient hf hg) x⟩
  exact ⟨v, hv, feasibleSet_eq_convexHull hx hv hA, isBounded_feasibleSet hx hv hA⟩

/-- **Eq. (100)** (arXiv 2201.10364): if a convex network `N` (gradient `gN`) is trained in
Sobolev norm so that its gradients agree with those of the convex `f*` (gradient `gf`) at the
training points, then `‖∇f*(0) - ∇N(0)‖ ≤ diam A = diam{v₀, …, v_d}`. -/
theorem norm_gradient_sub_le_diam [CompleteSpace E] {f N : E → ℝ} {gf gN : E → E}
    (hf : ConvexOn ℝ univ f)
    (hN : ConvexOn ℝ univ N) (hgf : ∀ y, HasGradientAt f (gf y) y)
    (hgN : ∀ y, HasGradientAt N (gN y) y) (hx : IsInteriorConfig x)
    (htrain : ∀ i, gf (x i) = gN (x i)) {v : Fin (d + 1) → E}
    (hv : ∀ i, IsVertex x (fun j => gf (x j)) i (v i)) :
    ‖gf 0 - gN 0‖ ≤ Metric.diam (Set.range v) := by
  have h1 := gradient_mem_feasibleSet (isOneSidedLipschitzField_neg_gradient hf hgf) x
  have h2 := gradient_mem_feasibleSet (isOneSidedLipschitzField_neg_gradient hN hgN) x
  have htr : (fun i => gN (x i)) = fun i => gf (x i) := funext fun i => (htrain i).symm
  rw [htr] at h2
  have hA := feasibleSet_eq_convexHull hx hv ⟨_, h1⟩
  rw [hA] at h1 h2
  rw [← dist_eq_norm, ← convexHull_diam]
  exact Metric.dist_le_diam_of_mem
    (isBounded_convexHull.2 (Set.finite_range v).isBounded) h1 h2

end Theorem1

/-! ### Theorem 2: distance between vertices -/

section Theorem2

variable {x G : Fin (d + 1) → E}

/-- **Eq. (101)**: the vertex `vᵢ` solves `Xᵢ vᵢ = bᵢ`, i.e. `xₖⁿ · vᵢ = ∇f*(xₖ) · xₖⁿ` for the
normalized `xₖⁿ = xₖ / ‖xₖ‖`, `k ≠ i`. -/
theorem IsVertex.inner_eq {i : Fin (d + 1)} {v : E} (hv : IsVertex x G i v) {k : Fin (d + 1)}
    (hk : k ≠ i) : ⟪‖x k‖⁻¹ • x k, v⟫ = ⟪G k, ‖x k‖⁻¹ • x k⟫ := by
  rw [inner_smul_left, inner_smul_right, real_inner_comm, hv k hk]; simp

/-- **Theorem 2** (arXiv 2201.10364, Eq. (102)): let the `xₖ` have unit length, let `Kᵢ` bound the
norm of `Xᵢ⁻¹ : (ℝ^d, ‖·‖_∞) → (ℝ^d, ‖·‖₂)`, i.e. `‖y‖ ≤ Kᵢ max_{k ≠ i} |xₖ · y|`, and let
`C ≥ ‖Gₖ - Gₗ‖` for all `k, l` (`C_{x*}`).  Then `‖vᵢ - vⱼ‖ ≤ (Kᵢ + Kⱼ) C`. -/
theorem norm_vertex_sub_le (hunit : ∀ k, ‖x k‖ = 1) {K : Fin (d + 1) → ℝ}
    (hK : ∀ i y M, (∀ k, k ≠ i → |⟪x k, y⟫| ≤ M) → ‖y‖ ≤ K i * M) {C : ℝ}
    (hC : ∀ k l, ‖G k - G l‖ ≤ C) {v : Fin (d + 1) → E} (hv : ∀ i, IsVertex x G i (v i))
    (i j : Fin (d + 1)) : ‖v i - v j‖ ≤ (K i + K j) * C := by
  have hξ : ∀ i, ‖v i - G 0‖ ≤ K i * C := by
    intro i
    refine hK i _ C fun k hk => ?_
    have : ⟪x k, v i - G 0⟫ = ⟪x k, G k - G 0⟫ := by
      rw [inner_sub_right, inner_sub_right, real_inner_comm, hv i k hk, real_inner_comm]
    rw [this]
    calc |⟪x k, G k - G 0⟫| ≤ ‖x k‖ * ‖G k - G 0‖ := abs_real_inner_le_norm _ _
      _ ≤ C := by rw [hunit k, one_mul]; exact hC k 0
  calc ‖v i - v j‖ = ‖(v i - G 0) - (v j - G 0)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖v i - G 0‖ + ‖v j - G 0‖ := norm_sub_le _ _
    _ ≤ K i * C + K j * C := add_le_add (hξ i) (hξ j)
    _ = (K i + K j) * C := by ring

/-- **Eq. (109)** (arXiv 2201.10364): under the hypotheses of Eq. (100) and Theorem 2, the
generalization gap of the gradient is at most `max_{i,j} (‖Xᵢ⁻¹‖ + ‖Xⱼ⁻¹‖) C_{x*}`, here
`‖∇f*(0) - ∇N(0)‖ ≤ 2 K C` for a common bound `K ≥ Kᵢ`. -/
theorem norm_gradient_sub_le_of_invBound [CompleteSpace E] {f N : E → ℝ} {gf gN : E → E}
    (hf : ConvexOn ℝ univ f)
    (hN : ConvexOn ℝ univ N) (hgf : ∀ y, HasGradientAt f (gf y) y)
    (hgN : ∀ y, HasGradientAt N (gN y) y) (hx : IsInteriorConfig x)
    (htrain : ∀ i, gf (x i) = gN (x i)) (hunit : ∀ k, ‖x k‖ = 1) {K : ℝ}
    (hK : ∀ i y M, (∀ k, k ≠ i → |⟪x k, y⟫| ≤ M) → ‖y‖ ≤ K * M) {C : ℝ}
    (hC : ∀ k l, ‖gf (x k) - gf (x l)‖ ≤ C) {v : Fin (d + 1) → E}
    (hv : ∀ i, IsVertex x (fun j => gf (x j)) i (v i)) :
    ‖gf 0 - gN 0‖ ≤ 2 * K * C := by
  refine (norm_gradient_sub_le_diam hf hN hgf hgN hx htrain hv).trans ?_
  have hK0 : 0 ≤ K * C := by
    have := norm_vertex_sub_le (K := fun _ => K) hunit hK hC hv 0 0
    simp at this
    nlinarith
  refine Metric.diam_le_of_forall_dist_le (by nlinarith) ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [dist_eq_norm]
  have := norm_vertex_sub_le (K := fun _ => K) hunit hK hC hv i j
  linarith

end Theorem2

/-- Non-vacuity: on `ℝ`, the points `x₀ = 1`, `x₁ = -1` (weights `1, 1`) have `0` in the
interior of their hull. -/
example : IsInteriorConfig (d := 1) (E := ℝ) ![1, -1] := by
  refine ⟨⟨fun _ => 1, fun _ => one_pos, by simp [Fin.sum_univ_two]⟩, ?_⟩
  rw [eq_top_iff]
  intro y _
  have : y = y • (1 : ℝ) := by simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)

end LeanDLRA.Literature.P2201_10364
