import LeanDLRA.Integrators.BUG
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Existence

/-!
# The Tucker-tensor (`d`-mode) BUG integrator

This file formalises the robust error analysis of the Tucker-tensor version of the
basis-update & Galerkin (BUG) integrator:

* Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank approximation*,
  BIT 2022, [CerutiLubich2022, §5]: Lemma 5, **Lemma 6**, **Lemma 7** (local error) and
  **Theorem 7** (robust global error bound); Theorem 6 (exactness) is formalised in abstract form
  as `LeanDLRA.Exactness.tucker_exact_abstract` in `Integrators/Exactness.lean`;
* Ceruti–Kusch–Lubich, *A rank-adaptive robust integrator for dynamical low-rank approximation*,
  BIT 2022, [CerutiKuschLubich2022, §4.2]: the rank-adaptive Tucker integrator inherits the robust
  error bound with an extra term `c₃ n ϑ`, norm conservation up to `ϑ` (Thm 4) and energy decay
  for gradient systems up to `O(ϑ)` (Thm 5);
* Ceruti–Kusch–Lubich–Sulz, *A parallel basis update and Galerkin integrator for tree tensor
  networks*, [CerutiEtAl2024, §3]: the **parallel Tucker BUG integrator** and its robust error
  bound (**Theorem 3.1**);
* for context: Lubich–Vandereycken–Walach, [LubichVandereyckenWalach2018] (projector-splitting
  integrator for rank-constrained Tucker tensors, same robust error bound), and the
  tree-tensor-network extensions [CerutiLubichWalach2021] and 2412.00858, §4, whose analysis is the
  recursive application of the argument below.

## The integrator as full-space trajectories

A Tucker tensor `Y₀ = C₀ ×ᵢ U⁰ᵢ` of multilinear rank `(r₁, …, r_d)` is advanced from `t₀` to
`t₁ = t₀ + h` as follows (Ceruti–Lubich, §5.1).  With `Matᵢ(Y₀) = U⁰ᵢ S⁰ᵢ V⁰ᵢᵀ` (QR of
`Matᵢ(C₀)ᵀ`), for each mode `i` (in parallel) the K-step
`K̇ᵢ = Fᵢ(t, Kᵢ V⁰ᵢᵀ) V⁰ᵢ`, `Kᵢ(t₀) = U⁰ᵢ S⁰ᵢ`, `Fᵢ = Matᵢ ∘ F ∘ Tenᵢ`, is integrated and
`U¹ᵢ` is an orthonormal basis of the range of `Kᵢ(t₁)`; then the core is updated by the Galerkin ODE
`Ċ = F(t, C ×ᵢ U¹ᵢ) ×ᵢ U¹ᵢᵀ`, `C(t₀) = C₀ ×ᵢ (U¹ᵢᵀ U⁰ᵢ)`, and `Y₁ = C(t₁) ×ᵢ U¹ᵢ`.

As in the rest of the library, all this is written on an abstract real inner product space `E`
(here: the tensors `ℝ^{n₁ × ⋯ × n_d}` with the Euclidean norm of the entries) with orthogonal
projectors indexed by the modes `i : Fin d`:

* `Q₀ i` is the orthogonal projector `X ↦ Tenᵢ(Matᵢ(X) V⁰ᵢ V⁰ᵢᵀ)` onto the co-range of the
  `i`-th matricization of `Y₀`; the K-step is the trajectory `YK i = Tenᵢ(Kᵢ V⁰ᵢᵀ)`, which solves
  `YK i' = Q₀ i F(t, YK i)` with `YK i t₀ = Y₀`;
* `P₁ i` is the new mode-`i` basis projector `X ↦ X ×ᵢ U¹ᵢ U¹ᵢᵀ`; the QR step gives the capture
  property `P₁ i (YK i t₁) = YK i t₁`;
* the projectors `P₁ i` act on different modes and therefore commute, and their product
  `Π = P₁ 0 ∘ ⋯ ∘ P₁ (d-1)` (`modeProd P₁`) is the orthogonal projector `X ↦ X ×ᵢ U¹ᵢ U¹ᵢᵀ`;
* the core step is the trajectory `YS = C ×ᵢ U¹ᵢ`, which solves `YS' = Π F(t, YS)` with
  `YS t₀ = C₀ ×ᵢ U¹ᵢ U¹ᵢᵀ U⁰ᵢ = Π Y₀`, and `Y₁ = YS t₁`.

All hypotheses of one step are bundled in `IsTuckerBUGStep`.  The old basis projectors
`P₀ i = (X ↦ X ×ᵢ U⁰ᵢ U⁰ᵢᵀ)` play no role in the error analysis (they only enter through `Y₀`
and `Q₀ i`), so they do not appear in the abstract statements.

## The normal-component hypothesis

The paper's assumption 2 (`‖(I - P(Y)) F(t, Y)‖ ≤ ε` for Tucker tensors `Y` of multilinear rank
`r` near the exact solution, `P(Y)` the tangent projector of the Tucker manifold) is used only at
the points `YK i t₁`, in the form `‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε`.  This follows
from the Tucker assumption because **`(1 - P₁ i)(1 - Q₀ i)` annihilates the Tucker tangent space
at `YK i t₁`**: a tangent vector at `Y = C ×ⱼ Uⱼ` has the form
`δY = δC ×ⱼ Uⱼ + ∑ₖ C ×ₖ δUₖ ×_{j ≠ k} Uⱼ`.  In the `i`-th matricization, every term except
`k = i` is of the form `Uᵢ (⋯)`, i.e. lies in the range of the left projector onto the column
space of `Matᵢ(Y)`, and the term `k = i` is `δUᵢ Matᵢ(C) (⊗_{j ≠ i} Uⱼ)ᵀ`, whose rows lie in the
row space of `Matᵢ(Y)`.  So the Tucker tangent space at `Y` is contained in the tangent space of
the rank-`rᵢ` matrix manifold at `Matᵢ(Y)` (this is Lemma 5 of [CerutiLubich2022]).  At
`Y = YK i t₁` we have `Matᵢ(YK i t₁) = Kᵢ(t₁) V⁰ᵢᵀ`: its column space is contained in the range of
`U¹ᵢ` (fixed by `P₁ i`) and its row space in the range of `V⁰ᵢ` (fixed by `Q₀ i`).  Hence every
tangent vector is `a + b` with `P₁ i a = a` and `Q₀ i b = b`, i.e. it lies in the range of the
"matrix tangent projector" `tangent (P₁ i) (Q₀ i) = P₁ i + Q₀ i - P₁ i Q₀ i`, which is
annihilated by `normal (P₁ i) (Q₀ i) = (1 - P₁ i)(1 - Q₀ i)` (`normal_tangent_apply`; `P₁ i` and
`Q₀ i` act on different modes and commute).  Consequently
`(1 - P₁ i)(1 - Q₀ i) F = (1 - P₁ i)(1 - Q₀ i)(I - P(YK i t₁)) F`, and since both factors are
contractions, `‖(1 - P₁ i)(1 - Q₀ i) F‖ ≤ ‖(I - P(YK i t₁)) F‖ ≤ ε`.  This implication is
formalised as `norm_normal_le_of_tangent`, and `tucker_local_error_of_tangent` states the local
error bound directly under the Tucker normal-component assumption.

For `d = 2` (matrices, `Mat₁(Y) = Y`, `Mat₂(Y) = Yᵀ`) the mode projectors are the left and the
right projector, `Q₀ = ![Q₀, P₀]`, `P₁ = ![P₁, Q₁]`, and the Tucker BUG integrator *is* the matrix
BUG integrator: `IsBUGStep.toTucker`, `IsBUGStep.local_error_of_tucker`, `tuckerC₁_two`,
`tuckerC₂_two` recover `bug_local_error` of `Integrators/BUG.lean` with the same constants.

## Main results

With `F` `L`-Lipschitz and bounded by `B`, and `ϑ = h (4 L B h + ε)`:

* `norm_sub_modeProd_apply_le` (**telescoping bound**, proof of Lemma 6): for contractions,
  `‖x - (P 0 ∘ ⋯ ∘ P (d-1)) x‖ ≤ ∑ᵢ ‖x - P i x‖` (no commutativity needed);
  `IsOrthProj.modeProd`: a product of pairwise commuting orthogonal projectors is an orthogonal
  projector; `modeProd_apply_eq_self_iff`: it fixes exactly the common fixed points;
* `tucker_capture` (**Lemma 6**): `‖A t₁ - Π A t₁‖ ≤ d ϑ`;
* `tucker_local_error` (**Lemma 7**, explicit): `‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + d ϑ) + d ϑ`;
  `IsTuckerBUGStep.local_error_le`: `‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` for `h ≤ H`, with
  `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`;
* `tucker_global_error`, `tucker_global_error_le` (**Theorem 7**): via Lady Windermere's fan,
  `‖Yₙ - A tₙ‖ ≤ c₀ δ + c₁' ε + c₂' h` for `n h ≤ T`, with constants depending only on `L`, `B`,
  `T`, `H` and `d` — not on singular values of matricizations;
* rank-adaptive Tucker BUG ([CerutiKuschLubich2022, §4.2]), `IsAugTuckerBUGStep`: the augmented mode
  projectors also fix `Y₀`, so the core step starts at `Y₀` itself; local error plus truncation
  tolerance (`IsAugTuckerBUGStep.local_error_trunc`), global error with the extra `c₃ n ϑ` term
  (`aug_tucker_global_error`, `aug_tucker_global_error_le`: Tucker version of Thm 2), exact norm
  conservation of the untruncated step and conservation up to `ϑ` after truncation
  (`IsAugTuckerBUGStep.norm_eq`, `IsAugTuckerBUGStep.norm_sub_le`: Thm 4), norm dissipation
  (`IsAugTuckerBUGStep.norm_le`), energy decay for gradient systems
  (`IsAugTuckerBUGStep.energy_le`, `IsAugTuckerBUGStep.energy_le_trunc`: Thm 5) and energy
  conservation for Hamiltonian-type fields `F = J ∇ℰ` (`IsAugTuckerBUGStep.energy_eq_of_skew`,
  `IsAugTuckerBUGStep.energy_sub_le_of_skew`: Thms 6–7); the sequential mode-wise truncation with
  tolerance `ϑ/d` per mode has total error `≤ ϑ` (`norm_sub_le_of_chain`);
* parallel Tucker BUG integrator ([CerutiEtAl2024, §3]), `IsParTuckerBUGStep`, `parTuckerBUG`:
  all Kᵢ-steps and a rank-`r` core step `YC' = (∏ P₀ i) F(t, YC)` run in parallel; the augmented
  core has the blocks `C(t₁)` (core), `h F(Y₀) ×_{j ≠ i} U⁰ⱼᵀ ×ᵢ Ũᵢᵀ` (one new mode) and zero
  (two or more new modes).  The block projectors are `modeProd P₀`, `modeProdLeOne P₀ Pa` ("at most
  one new mode", an orthogonal projector: `isOrthProj_modeProdLeOne`) and the augmented
  `modeProd (P₀ + Pa)`, with the algebra in `ModeSplit`.  Results: the distance to the rank-adaptive
  integrator with the same bases is `≤ h ((3 L B + Lₜ) h + ε)` (`parallel_sub_galerkin_le`,
  `IsParTuckerBUGStep.parallel_sub_aug`), the local error
  `(e^{L h} - 1)(B h + d ϑ) + d ϑ + h ((3 L B + Lₜ) h + ε)` (`IsParTuckerBUGStep.local_error`,
  `local_error_le`, `local_error_of_complete`) and the global error
  `c₀ δ + c₁ ε + c₂ h + c₃ n ϑ` (`par_tucker_global_error`, `par_tucker_global_error_le`:
  **Theorem 3.1**).

## Deviations from the papers

* The paper proves Lemma 6 via Lemma 5 (matricization) and the matrix Lemma 2 for each mode; we
  use the direct capture lemma `kstep_capture` for each mode, which gives the explicit
  `ϑ = h (4 L B h + ε)`, and the abstract telescoping bound.  The identification of the mode
  projectors through matricizations is explained above but not formalised (tensors are not
  modelled; any family of orthogonal projectors with the stated properties is allowed).
* Lemma 7 is stated in the paper as `‖Y₁ - A₁‖ ≤ ĉ h (B L h + ε)` "up to minor modifications"
  of the matrix proof; we give the explicit bound `(e^{L h} - 1)(B h + d ϑ) + d ϑ` and the
  constants `tuckerC₁`, `tuckerC₂`.
* Exact flows from the numerical values (needed for Lady Windermere's fan) are hypotheses; their
  existence is proved in `Foundations/Existence.lean`.
* Parallel Tucker integrator ([CerutiEtAl2024, Thm. 3.1]): the paper's proof is a sketch for
  autonomous `F`; we allow time-dependent `F` with `‖F(t, x) - F(s, x)‖ ≤ Lₜ (t - s)` (`Lₜ = 0` in
  the autonomous case), and assume the normal-component bound at `(t₀, Y₀)` for the "tangent hull"
  `modeProdLeOne P₀ (1 - P₀) = Π₀ + ∑ᵢ (1 - P₀ i) ∏_{j ≠ i} P₀ j`.  This operator is the formula
  displayed for the Tucker tangent projector in §3.2 of the paper; for `d ≥ 3` it is in general
  the projector onto a space strictly containing the tangent space (the mode-`i` tangent
  directions only fill the `rᵢ`-dimensional co-range of `Matᵢ(Y₀)`, not the whole
  `∏_{j ≠ i} rⱼ`-dimensional range of `∏_{j ≠ i} P₀ j`), and it coincides with the matrix tangent
  projector for `d = 2` (`modeProdLeOne_compl_two`).  The proof only uses that it contains the
  tangent space, so our assumption is implied by the paper's (`norm_sub_tangentHull_le`).  The
  comparison rank-adaptive trajectory of the proof is a hypothesis of the local bounds and is
  constructed internally (via `exists_ODESolution_clm`) in `local_error_of_complete` and
  `par_tucker_global_error_le`.
-/

open Set

namespace LeanDLRA

/-! ### Ordered products of mode projectors -/

section ModeProd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordered product `P 0 * P 1 * ⋯ * P (d - 1)` of a family of operators indexed by the
modes `i : Fin d`; applied to `x` it is `P 0 (P 1 (⋯ (P (d - 1) x)))`.  For the Tucker mode
projectors `P i X = X ×ᵢ Uᵢ Uᵢᵀ` it is the projector `X ↦ X ×ᵢ Uᵢ Uᵢᵀ` onto the tensors with
mode-`i` bases in the ranges of the `Uᵢ`. -/
def modeProd {d : ℕ} (P : Fin d → E →L[ℝ] E) : E →L[ℝ] E := (List.ofFn P).prod

@[simp] lemma modeProd_zero (P : Fin 0 → E →L[ℝ] E) : modeProd P = 1 := by
  simp [modeProd]

lemma modeProd_succ {d : ℕ} (P : Fin (d + 1) → E →L[ℝ] E) :
    modeProd P = P 0 * modeProd (fun i => P i.succ) := by
  simp [modeProd, List.ofFn_succ]

/-- For two modes the product is the product of the two projectors (left and right projector
in the matrix case). -/
@[simp] lemma modeProd_two (P Q : E →L[ℝ] E) : modeProd ![P, Q] = P * Q := by
  simp [modeProd, List.ofFn_succ]

/-- A product of maps each fixing `x` fixes `x`. -/
lemma listProd_apply_eq_self {l : List (E →L[ℝ] E)} {x : E} (h : ∀ T ∈ l, T x = x) :
    l.prod x = x := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    rw [List.prod_cons]
    change T (l.prod x) = x
    rw [ih (fun T' hT' => h T' (List.mem_cons_of_mem T hT')), h T List.mem_cons_self]

/-- If every mode projector fixes `x`, so does their product. -/
lemma modeProd_apply_eq_self {d : ℕ} {P : Fin d → E →L[ℝ] E} {x : E} (h : ∀ i, P i x = x) :
    modeProd P x = x :=
  listProd_apply_eq_self fun T hT => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact h i

/-- A map commuting with every factor commutes with the product. -/
lemma listProd_apply_comm {l : List (E →L[ℝ] E)} {T : E →L[ℝ] E}
    (h : ∀ S ∈ l, ∀ x, T (S x) = S (T x)) (x : E) : T (l.prod x) = l.prod (T x) := by
  induction l generalizing x with
  | nil => rfl
  | cons S l ih =>
    rw [List.prod_cons]
    change T (S (l.prod x)) = S (l.prod (T x))
    rw [h S List.mem_cons_self, ih (fun S' hS' => h S' (List.mem_cons_of_mem S hS'))]

/-- An idempotent factor commuting with all factors absorbs the product: `T (∏ l) = ∏ l`. -/
lemma apply_listProd_eq_self {l : List (E →L[ℝ] E)} {T : E →L[ℝ] E} (hT : T ∈ l)
    (hidem : ∀ x, T (T x) = T x) (hc : ∀ S ∈ l, ∀ x, T (S x) = S (T x)) (x : E) :
    T (l.prod x) = l.prod x := by
  induction l generalizing x with
  | nil => simp at hT
  | cons S l ih =>
    rw [List.prod_cons]
    change T (S (l.prod x)) = S (l.prod x)
    rcases List.mem_cons.mp hT with rfl | hT'
    · rw [hidem]
    · rw [hc S List.mem_cons_self, ih hT' (fun S' hS' => hc S' (List.mem_cons_of_mem S hS'))]

/-- For pairwise commuting idempotent mode projectors, each `P i` fixes the range of the
product. -/
lemma apply_modeProd_eq_self {d : ℕ} {P : Fin d → E →L[ℝ] E} (hidem : ∀ i x, P i (P i x) = P i x)
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (i : Fin d) (x : E) :
    P i (modeProd P x) = modeProd P x :=
  apply_listProd_eq_self (List.mem_ofFn.mpr ⟨i, rfl⟩) (hidem i)
    (fun S hS y => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
      exact hc i j y) x

/-- **Telescoping bound for products of contractions** (list form):
`‖x - (T₁ ∘ ⋯ ∘ T_k) x‖ ≤ ∑ⱼ ‖x - Tⱼ x‖`. -/
lemma norm_sub_listProd_apply_le {l : List (E →L[ℝ] E)} (hl : ∀ T ∈ l, ∀ y, ‖T y‖ ≤ ‖y‖)
    (x : E) : ‖x - l.prod x‖ ≤ (l.map fun T => ‖x - T x‖).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    change ‖x - T (l.prod x)‖ ≤ _
    have hdec : x - T (l.prod x) = (x - T x) + T (x - l.prod x) := by rw [map_sub]; abel
    rw [hdec]
    calc _ ≤ ‖x - T x‖ + ‖T (x - l.prod x)‖ := norm_add_le _ _
      _ ≤ ‖x - T x‖ + ‖x - l.prod x‖ := add_le_add le_rfl (hl T List.mem_cons_self _)
      _ ≤ _ := add_le_add le_rfl (ih fun T' hT' => hl T' (List.mem_cons_of_mem T hT'))

/-- **Telescoping bound for products of mode projectors** (proof of Lemma 6 of
[CerutiLubich2022]): if every `P i` is a contraction, then
`‖x - (P 0 ∘ ⋯ ∘ P (d-1)) x‖ ≤ ∑ᵢ ‖x - P i x‖`.  No commutativity is needed. -/
theorem norm_sub_modeProd_apply_le {d : ℕ} {P : Fin d → E →L[ℝ] E}
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) (x : E) : ‖x - modeProd P x‖ ≤ ∑ i, ‖x - P i x‖ := by
  have h := norm_sub_listProd_apply_le (l := List.ofFn P) (fun T hT y => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact hP i y) x
  rw [List.map_ofFn, List.sum_ofFn] at h
  exact h

omit [NormedSpace ℝ E] in
/-- **Sequential truncation.**  If a chain `C 0, C 1, …, C d` (e.g. the mode-by-mode truncations
`Ĉ = C₀ ↦ C₁ ↦ ⋯ ↦ C_d` of the rank-adaptive Tucker integrator, [CerutiKuschLubich2022, §4.1], step
3) moves by at most `τ` in each step, then `‖C 0 - C d‖ ≤ d τ`. With the tolerance `τ = ϑ / d` per
mode, the total truncation error is at most `ϑ`. -/
theorem norm_sub_le_of_chain {C : ℕ → E} {d : ℕ} {τ : ℝ}
    (hC : ∀ i < d, ‖C i - C (i + 1)‖ ≤ τ) : ‖C 0 - C d‖ ≤ d * τ := by
  have h := dist_le_range_sum_dist C d
  rw [dist_eq_norm] at h
  refine h.trans ?_
  calc ∑ i ∈ Finset.range d, dist (C i) (C (i + 1)) ≤ ∑ _i ∈ Finset.range d, τ :=
        Finset.sum_le_sum fun i hi => by
          rw [dist_eq_norm]; exact hC i (Finset.mem_range.mp hi)
    _ = d * τ := by simp

end ModeProd

/-! ### Block structure of the augmented Tucker projectors -/

section ModeBlocks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sum of the "at most one new mode" blocks: for families `p`, `q` indexed by the modes,
`modeProdLeOne p q = ∑_{|I| ≤ 1} ∏_{i ∈ I} q i ∏_{j ∉ I} p j`, i.e.
`p 0 ⋯ p (d-1) + ∑ᵢ p 0 ⋯ q i ⋯ p (d-1)`, defined recursively by
`p 0 * modeProdLeOne p' q' + q 0 * modeProd p'` (`p'`, `q'` the families of the remaining modes);
see `modeProdLeOne_eq_sum` for the explicit sum.

* With `p i = U⁰ᵢ U⁰ᵢᵀ` (old bases) and `q i = Ũᵢ Ũᵢᵀ` (new directions orthogonal to the old
  basis) it is the projector onto the core block `C(t₁) ×ᵢ U⁰ᵢ` together with the blocks
  `C̃ᵢ ×ᵢ Ũᵢ ×_{j ≠ i} U⁰ⱼ` of the augmented core of the parallel Tucker integrator
  ([CerutiEtAl2024], (3.3)–(3.4)).
* With `q i = 1 - p i` it is `Π₀ + ∑ᵢ (1 - P₀ i) ∏_{j ≠ i} P₀ j`, the projector onto the sum of the
  ranges of the `∏_{j ≠ i} P₀ j`, which contains the tangent space of the Tucker manifold at `Y₀`
  (the formula used for the tangent projector in [CerutiEtAl2024, §3.2]). -/
def modeProdLeOne : {d : ℕ} → (Fin d → E →L[ℝ] E) → (Fin d → E →L[ℝ] E) → E →L[ℝ] E
  | 0, _, _ => 1
  | _ + 1, p, q => p 0 * modeProdLeOne (fun i => p i.succ) (fun i => q i.succ)
      + q 0 * modeProd (fun i => p i.succ)

@[simp] lemma modeProdLeOne_zero (p q : Fin 0 → E →L[ℝ] E) : modeProdLeOne p q = 1 := rfl

lemma modeProdLeOne_succ {d : ℕ} (p q : Fin (d + 1) → E →L[ℝ] E) :
    modeProdLeOne p q = p 0 * modeProdLeOne (fun i => p i.succ) (fun i => q i.succ)
      + q 0 * modeProd (fun i => p i.succ) := rfl

/-- **Explicit form of the "at most one new mode" blocks**:
`modeProdLeOne p q = ∏ p i + ∑ᵢ p 0 ⋯ p (i-1) q i p (i+1) ⋯ p (d-1)`. -/
lemma modeProdLeOne_eq_sum {d : ℕ} (p q : Fin d → E →L[ℝ] E) :
    modeProdLeOne p q = modeProd p + ∑ i, modeProd (Function.update p i (q i)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h0 : (fun i : Fin d => Function.update p 0 (q 0) i.succ) = fun i => p i.succ :=
      funext fun i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
    have hs : ∀ i : Fin d, modeProd (Function.update p i.succ (q i.succ))
        = p 0 * modeProd (Function.update (fun j => p j.succ) i (q i.succ)) := fun i => by
      rw [modeProd_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      exact Function.update_comp_eq_of_injective p (Fin.succ_injective d) i (q i.succ)
    rw [modeProdLeOne_succ, ih (fun i => p i.succ) (fun i => q i.succ), Fin.sum_univ_succ,
      modeProd_succ (Function.update p 0 (q 0)), Function.update_self, h0, modeProd_succ p]
    simp only [hs, ← Finset.mul_sum, mul_add]
    abel

/-- Pointwise form of `Commute` for continuous linear maps. -/
lemma Commute.clm_apply {a b : E →L[ℝ] E} (h : Commute a b) (x : E) : a (b x) = b (a x) :=
  congrArg (fun f : E →L[ℝ] E => f x) h.eq

/-- A map commuting with every factor commutes with the mode product. -/
lemma commute_modeProd {d : ℕ} {p : Fin d → E →L[ℝ] E} {a : E →L[ℝ] E}
    (h : ∀ i, Commute a (p i)) : Commute a (modeProd p) :=
  Commute.list_prod_right _ _ fun b hb => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact h i

/-- A map commuting with all `p i` and `q i` commutes with `modeProdLeOne p q`. -/
lemma commute_modeProdLeOne {d : ℕ} {p q : Fin d → E →L[ℝ] E} {a : E →L[ℝ] E}
    (hp : ∀ i, Commute a (p i)) (hq : ∀ i, Commute a (q i)) :
    Commute a (modeProdLeOne p q) := by
  induction d with
  | zero => exact Commute.one_right a
  | succ d ih =>
    rw [modeProdLeOne_succ]
    exact ((hp 0).mul_right (ih (fun i => hp i.succ) (fun i => hq i.succ))).add_right
      ((hq 0).mul_right (commute_modeProd fun i => hp i.succ))

/-- Algebraic structure of the old mode projectors `p i = U⁰ᵢ U⁰ᵢᵀ` and the new directions
`q i = Ũᵢ Ũᵢᵀ` (`U⁰ᵢᵀ Ũᵢ = 0`): idempotents, `p i q i = q i p i = 0`, and all of them commute
(projectors acting on different modes commute). -/
structure ModeSplit {d : ℕ} (p q : Fin d → E →L[ℝ] E) : Prop where
  pp : ∀ i, p i * p i = p i
  qq : ∀ i, q i * q i = q i
  pq : ∀ i, p i * q i = 0
  qp : ∀ i, q i * p i = 0
  cpp : ∀ i j, Commute (p i) (p j)
  cpq : ∀ i j, Commute (p i) (q j)
  cqq : ∀ i j, Commute (q i) (q j)

namespace ModeSplit

variable {d : ℕ} {p q : Fin d → E →L[ℝ] E}

/-- Restriction to the modes `1, …, d`. -/
lemma tail {p q : Fin (d + 1) → E →L[ℝ] E} (hs : ModeSplit p q) :
    ModeSplit (fun i => p i.succ) (fun i => q i.succ) where
  pp i := hs.pp i.succ
  qq i := hs.qq i.succ
  pq i := hs.pq i.succ
  qp i := hs.qp i.succ
  cpp i j := hs.cpp i.succ j.succ
  cpq i j := hs.cpq i.succ j.succ
  cqq i j := hs.cqq i.succ j.succ

/-- The old projectors and their complements `1 - p i` form a mode split. -/
lemma compl (hs : ModeSplit p q) : ModeSplit p (fun i => 1 - p i) where
  pp := hs.pp
  qq i := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hs.pp, sub_self, sub_zero]
  pq i := by
    rw [mul_sub, mul_one, hs.pp, sub_self]
  qp i := by
    rw [sub_mul, one_mul, hs.pp, sub_self]
  cpp := hs.cpp
  cpq i j := (Commute.one_right _).sub_right (hs.cpp i j)
  cqq i j := (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hs.cpp i j))

/-- The augmented projectors `p i + q i` commute pairwise. -/
lemma commute_add (hs : ModeSplit p q) (i j : Fin d) : Commute (p i + q i) (p j + q j) :=
  ((hs.cpp i j).add_right (hs.cpq i j)).add_left
    (((hs.cpq j i).symm).add_right (hs.cqq i j))

/-- The augmented projectors `p i + q i` are idempotent. -/
lemma add_idem (hs : ModeSplit p q) (i : Fin d) : (p i + q i) * (p i + q i) = p i + q i := by
  rw [add_mul, mul_add, mul_add, hs.pp, hs.qq, hs.pq, hs.qp, add_zero, zero_add]

/-- The old core projector `∏ p i` is idempotent. -/
lemma modeProd_idem (hs : ModeSplit p q) : modeProd p * modeProd p = modeProd p := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [modeProd_succ]
    have hc : Commute (p 0) (modeProd fun i => p i.succ) := commute_modeProd fun i => hs.cpp 0 _
    calc p 0 * modeProd (fun i => p i.succ) * (p 0 * modeProd fun i => p i.succ)
        = p 0 * (modeProd (fun i => p i.succ) * p 0) * modeProd (fun i => p i.succ) := by
          simp only [mul_assoc]
      _ = p 0 * p 0 * (modeProd (fun i => p i.succ) * modeProd fun i => p i.succ) := by
          rw [← hc.eq]; simp only [mul_assoc]
      _ = p 0 * modeProd (fun i => p i.succ) := by rw [hs.pp, ih hs.tail]

/-- The augmented core projector `∏ (p i + q i)` fixes the range of the old core projector
`∏ p i`. -/
lemma modeProd_add_mul_modeProd (hs : ModeSplit p q) :
    modeProd (fun i => p i + q i) * modeProd p = modeProd p := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [modeProd_succ (fun i => p i + q i), modeProd_succ p]
    have hc : Commute (p 0) (modeProd fun i => p i.succ + q i.succ) :=
      commute_modeProd fun i => (hs.cpp 0 _).add_right (hs.cpq 0 _)
    have ih' := ih hs.tail
    calc (p 0 + q 0) * modeProd (fun i => p i.succ + q i.succ) * (p 0 * modeProd fun i => p i.succ)
        = (p 0 + q 0) * (modeProd (fun i => p i.succ + q i.succ) * p 0)
            * modeProd (fun i => p i.succ) := by simp only [mul_assoc]
      _ = (p 0 * p 0 + q 0 * p 0)
            * (modeProd (fun i => p i.succ + q i.succ) * modeProd fun i => p i.succ) := by
          rw [← hc.eq]; simp only [mul_assoc, add_mul]
      _ = p 0 * modeProd (fun i => p i.succ) := by rw [hs.pp, hs.qp, add_zero, ih']

/-- The augmented core projector `∏ (p i + q i)` fixes the range of `modeProdLeOne p q`. -/
lemma modeProd_add_mul_leOne (hs : ModeSplit p q) :
    modeProd (fun i => p i + q i) * modeProdLeOne p q = modeProdLeOne p q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [modeProd_succ (fun i => p i + q i), modeProdLeOne_succ]
    set X := modeProd fun i => p i.succ + q i.succ with hX
    set M := modeProdLeOne (fun i => p i.succ) (fun i => q i.succ) with hM
    set Y := modeProd fun i => p i.succ with hY
    have hpX : Commute (p 0) X := commute_modeProd fun i => (hs.cpp 0 _).add_right (hs.cpq 0 _)
    have hqX : Commute (q 0) X :=
      commute_modeProd fun i => ((hs.cpq _ 0).symm).add_right (hs.cqq 0 _)
    have h1 : X * M = M := ih hs.tail
    have h2 : X * Y = Y := modeProd_add_mul_modeProd hs.tail
    calc (p 0 + q 0) * X * (p 0 * M + q 0 * Y)
        = (p 0 + q 0) * ((X * p 0) * M + (X * q 0) * Y) := by
          simp only [mul_assoc, mul_add]
      _ = (p 0 * p 0) * (X * M) + (p 0 * q 0) * (X * Y) + ((q 0 * p 0) * (X * M)
            + (q 0 * q 0) * (X * Y)) := by
          rw [← hpX.eq, ← hqX.eq]; simp only [mul_assoc, mul_add, add_mul]; abel
      _ = p 0 * M + q 0 * Y := by
          rw [h1, h2, hs.pp, hs.pq, hs.qp, hs.qq, zero_mul, zero_mul, add_zero, zero_add]

/-- `∏ (p i + q i)` maps the "tangent hull" `modeProdLeOne p (1 - p)` onto
`modeProdLeOne p q`. -/
lemma modeProd_add_mul_tangent (hs : ModeSplit p q) :
    modeProd (fun i => p i + q i) * modeProdLeOne p (fun i => 1 - p i) = modeProdLeOne p q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [modeProd_succ (fun i => p i + q i), modeProdLeOne_succ, modeProdLeOne_succ p q]
    set X := modeProd fun i => p i.succ + q i.succ with hX
    set T := modeProdLeOne (fun i => p i.succ) (fun i => 1 - p i.succ) with hT
    set M := modeProdLeOne (fun i => p i.succ) (fun i => q i.succ) with hM
    set Y := modeProd fun i => p i.succ with hY
    have hpX : Commute (p 0) X := commute_modeProd fun i => (hs.cpp 0 _).add_right (hs.cpq 0 _)
    have h1 : X * T = M := ih hs.tail
    have h2 : X * Y = Y := modeProd_add_mul_modeProd hs.tail
    have hcX : Commute (1 - p 0) X := (Commute.one_left X).sub_left hpX
    calc (p 0 + q 0) * X * (p 0 * T + (1 - p 0) * Y)
        = (p 0 + q 0) * ((X * p 0) * T + (X * (1 - p 0)) * Y) := by
          simp only [mul_assoc, mul_add]
      _ = (p 0 * p 0) * (X * T) + (p 0 * (1 - p 0)) * (X * Y) + ((q 0 * p 0) * (X * T)
            + (q 0 * (1 - p 0)) * (X * Y)) := by
          rw [← hpX.eq, ← hcX.eq]; simp only [mul_assoc, mul_add, add_mul]; abel
      _ = p 0 * M + q 0 * Y := by
          rw [h1, h2, hs.pp, hs.compl.pq, mul_sub, mul_one, hs.qp, sub_zero, zero_mul,
            zero_mul, add_zero, zero_add]

/-- `modeProdLeOne p q` fixes nothing outside the tangent hull:
`modeProdLeOne p q * modeProdLeOne p (1 - p) = modeProdLeOne p q`. -/
lemma leOne_mul_tangent (hs : ModeSplit p q) :
    modeProdLeOne p q * modeProdLeOne p (fun i => 1 - p i) = modeProdLeOne p q := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [modeProdLeOne_succ p q, modeProdLeOne_succ p (fun i => 1 - p i)]
    set T := modeProdLeOne (fun i => p i.succ) (fun i => 1 - p i.succ) with hT
    set M := modeProdLeOne (fun i => p i.succ) (fun i => q i.succ) with hM
    set Y := modeProd fun i => p i.succ with hY
    have hpM : Commute (p 0) M := commute_modeProdLeOne (fun i => hs.cpp 0 _)
      (fun i => hs.cpq 0 _)
    have hpY : Commute (p 0) Y := commute_modeProd fun i => hs.cpp 0 _
    have hcY : Commute (1 - p 0) Y := (Commute.one_left Y).sub_left hpY
    have h1 : M * T = M := ih hs.tail
    have h2 : Y * Y = Y := modeProd_idem hs.tail
    calc (p 0 * M + q 0 * Y) * (p 0 * T + (1 - p 0) * Y)
        = p 0 * (M * p 0) * T + p 0 * (M * (1 - p 0)) * Y + (q 0 * (Y * p 0) * T
            + q 0 * (Y * (1 - p 0)) * Y) := by
          simp only [mul_assoc, mul_add, add_mul]; abel
      _ = (p 0 * p 0) * (M * T) + (p 0 * (1 - p 0)) * (M * Y) + ((q 0 * p 0) * (Y * T)
            + (q 0 * (1 - p 0)) * (Y * Y)) := by
          rw [← hpM.eq, ← hpY.eq, ← (Commute.one_left M).sub_left hpM |>.eq, ← hcY.eq]
          simp only [mul_assoc]
      _ = p 0 * M + q 0 * Y := by
          rw [h1, h2, hs.pp, hs.compl.pq, mul_sub, mul_one, hs.qp, sub_zero, zero_mul,
            zero_mul, add_zero, zero_add]

end ModeSplit

end ModeBlocks

/-! ### Orthogonal projector facts -/

section Proj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A product of pairwise commuting orthogonal projectors is an orthogonal projector
(list form). -/
theorem IsOrthProj.listProd {l : List (E →L[ℝ] E)} (hl : ∀ T ∈ l, IsOrthProj T)
    (hc : ∀ S ∈ l, ∀ T ∈ l, ∀ x, S (T x) = T (S x)) : IsOrthProj l.prod := by
  induction l with
  | nil => exact IsOrthProj.one
  | cons T l ih =>
    rw [List.prod_cons]
    refine (hl T List.mem_cons_self).mul
      (ih (fun S hS => hl S (List.mem_cons_of_mem T hS))
        (fun S hS U hU => hc S (List.mem_cons_of_mem T hS) U (List.mem_cons_of_mem T hU))) ?_
    exact listProd_apply_comm fun S hS => hc T List.mem_cons_self S (List.mem_cons_of_mem T hS)

/-- **The product of pairwise commuting orthogonal mode projectors is an orthogonal projector**
(the Tucker projector `X ↦ X ×ᵢ Uᵢ Uᵢᵀ` of the core step). -/
theorem IsOrthProj.modeProd {d : ℕ} {P : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P i))
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) : IsOrthProj (modeProd P) :=
  IsOrthProj.listProd
    (fun T hT => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
      exact hP i)
    (fun S hS T hT x => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hT
      exact hc i j x)

/-- For pairwise commuting orthogonal projectors, the product fixes exactly the common fixed
points of the factors: `range (∏ P i) = ⋂ range (P i)`. -/
theorem modeProd_apply_eq_self_iff {d : ℕ} {P : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P i))
    (hc : ∀ i j x, P i (P j x) = P j (P i x)) (x : E) :
    modeProd P x = x ↔ ∀ i, P i x = x := by
  refine ⟨fun h i => ?_, modeProd_apply_eq_self⟩
  rw [← h]
  exact apply_modeProd_eq_self (fun i => (hP i).idem) hc i x

/-- The normal projector `(1 - P)(1 - Q)` annihilates the range of the tangent projector
`P + Q - P Q` for commuting idempotents `P`, `Q`. -/
theorem normal_tangent_apply {P Q : E →L[ℝ] E} (hP : ∀ x, P (P x) = P x)
    (hQ : ∀ x, Q (Q x) = Q x) (hc : ∀ x, P (Q x) = Q (P x)) (w : E) :
    normal P Q (tangent P Q w) = 0 := by
  have h1 : Q (P (Q w)) = Q (P w) := by rw [← hc, hQ, hc]
  have h2 : P (Q (P w)) = Q (P w) := by rw [hc, hP]
  simp only [normal_apply, tangent_apply, map_sub, map_add, hP, hQ, h1, h2]
  abel

/-- **Doubly-normal components are controlled by the normal component** (the reduction of the
Tucker normal-component assumption to the hypothesis used in the K-step capture lemma).  Let
`P`, `Q` be commuting orthogonal projectors and let `T` be a map whose range lies in the range of
the tangent projector `P + Q - P Q` (e.g. the tangent projector of the Tucker manifold at
`YK i t₁`, with `P = P₁ i`, `Q = Q₀ i`, see the module docstring).  Then
`‖(1 - P) ((1 - Q) z)‖ ≤ ‖z - T z‖`. -/
theorem norm_normal_le_of_tangent {P Q T : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hc : ∀ x, P (Q x) = Q (P x)) (hT : ∀ y, tangent P Q (T y) = T y) (z : E) :
    ‖(1 - P) ((1 - Q) z)‖ ≤ ‖z - T z‖ := by
  have hzero : (1 - P) ((1 - Q) (T z)) = 0 := by
    rw [← hT z]
    exact normal_tangent_apply hP.idem hQ.idem hc _
  have heq : (1 - P) ((1 - Q) z) = (1 - P) ((1 - Q) (z - T z)) := by
    rw [map_sub (1 - Q), map_sub (1 - P), hzero, sub_zero]
  rw [heq]
  exact (hP.compl.norm_le _).trans (hQ.compl.norm_le _)

end Proj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Constants -/

section Constants

lemma tuckerC₁_nonneg (d : ℕ) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) : 0 ≤ tuckerC₁ d L H := by
  unfold tuckerC₁; positivity

lemma tuckerC₂_nonneg (d : ℕ) {L B H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    0 ≤ tuckerC₂ d L B H := by
  unfold tuckerC₂; positivity

/-- For `d = 2` the Tucker constant `c₁` is the matrix BUG constant. -/
lemma tuckerC₁_two (L H : ℝ) : tuckerC₁ 2 L H = bugC₁ L H := by
  unfold tuckerC₁ bugC₁; push_cast; ring

/-- For `d = 2` the Tucker constant `c₂` is the matrix BUG constant. -/
lemma tuckerC₂_two (L B H : ℝ) : tuckerC₂ 2 L B H = bugC₂ L B H := by
  unfold tuckerC₂ bugC₂; push_cast; ring

/-- The explicit local bound `(e^{L h} - 1) (B h + d ϑ) + d ϑ`, `ϑ = h (4 L B h + ε)`, is bounded
by `h (c₁ ε + c₂ h)` for `0 ≤ h ≤ H`.  Only `d ε ≥ 0` is needed (so `ε` may be arbitrary when
`d = 0`). -/
lemma tucker_bound_le {d : ℕ} {L B ε h H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hdε : 0 ≤ (d : ℝ) * ε) (hh : 0 ≤ h) (hhH : h ≤ H) :
    (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
        + d * (h * (4 * L * B * h + ε))
      ≤ h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
  set e := Real.exp (L * H) with he
  set D : ℝ := (d : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg d
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have hHh : 0 ≤ H - h := by linarith
  have hexp : Real.exp (L * h) ≤ e := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have h1 : Real.exp (L * h) - 1 ≤ L * h * e :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left hexp hLh)
  have hX : 0 ≤ B * h + D * (h * (4 * L * B * h + ε)) := by
    have hrw : B * h + D * (h * (4 * L * B * h + ε))
        = B * h + 4 * D * L * B * h ^ 2 + h * (D * ε) := by ring
    rw [hrw]
    have : 0 ≤ h * (D * ε) := mul_nonneg hh hdε
    positivity
  have h2 : (Real.exp (L * h) - 1) * (B * h + D * (h * (4 * L * B * h + ε)))
      ≤ L * h * e * (B * h + D * (h * (4 * L * B * h + ε))) :=
    mul_le_mul_of_nonneg_right h1 hX
  have hgap1 : 0 ≤ L * e * h * (D * ε) * (H - h) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hL he0) hh) hdε) hHh
  have hgap2 : 0 ≤ 4 * D * L ^ 2 * B * e * h ^ 2 * (H - h) := by positivity
  have hid : h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)
      = L * h * e * (B * h + D * (h * (4 * L * B * h + ε))) + D * (h * (4 * L * B * h + ε))
        + (L * e * h * (D * ε) * (H - h) + 4 * D * L ^ 2 * B * e * h ^ 2 * (H - h)) := by
    unfold tuckerC₁ tuckerC₂; rw [← he, ← hD]; ring
  rw [hid]
  linarith

end Constants

/-! ### Capture and local error -/

section Local

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {d : ℕ}

/-- **Lemma 6 of [CerutiLubich2022]** (abstract form, explicit constant).  Let `F` be
`L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A` a solution of `A' = F(t, A)` on `[t₀, t₁]`,
`t₁ = t₀ + h`, `h ≥ 0`.  For each mode `i : Fin d` let the K-step trajectory `YK i` solve
`YK i' = Q₀ i F(t, YK i)`, `YK i t₀ = A t₀`, let the new mode projector capture it,
`P₁ i (YK i t₁) = YK i t₁`, and let `‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε` on the step.
Then the new bases together capture the exact solution:

    ‖A t₁ - (P₁ 0 ∘ ⋯ ∘ P₁ (d-1)) A t₁‖ ≤ d ϑ,    ϑ = h (4 L B h + ε).

The mode projectors need not commute here. -/
theorem tucker_capture {P₁ Q₀ : Fin d → E →L[ℝ] E} {YK : Fin d → ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i)) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = A t₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hεK : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ d * (h * (4 * L * B * h + ε)) := by
  refine (norm_sub_modeProd_apply_le (fun i => (hP₁ i).norm_le) (A t₁)).trans ?_
  calc ∑ i, ‖A t₁ - P₁ i (A t₁)‖ ≤ ∑ _i : Fin d, h * (4 * L * B * h + ε) :=
        Finset.sum_le_sum fun i _ => by
          have := kstep_capture hF hL hB (hP₁ i) (hQ₀ i) ht₁ hh hA (hK i) (hK₀ i) (hKcap i)
            (hεK i)
          simpa using this
    _ = d * (h * (4 * L * B * h + ε)) := by simp

/-- **Robust local error of the Tucker BUG integrator** (Ceruti–Lubich, [CerutiLubich2022],
Lemma 7, with explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, `A`
the exact solution on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, with `A t₀ = Y₀`.  Assume for every
mode `i : Fin d`

* K-step: `YK i' = Q₀ i F(t, YK i)`, `YK i t₀ = Y₀`, `P₁ i (YK i t₁) = YK i t₁`,
  `‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε` on `[t₀, t₁]`;

and the core (Galerkin) step `YS' = Π F(t, YS)`, `YS t₀ = Π Y₀` with `Π = P₁ 0 ∘ ⋯ ∘ P₁ (d-1)`,
where the `Q₀ i`, `P₁ i` are orthogonal projectors and the `P₁ i` commute pairwise.  Then, with
`ϑ = h (4 L B h + ε)`,

    ‖YS t₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + d ϑ) + d ϑ  ( = O(h (h + ε)) ).

No rank or invertibility assumption is made: the bound is independent of singular values of
matricizations. -/
theorem tucker_local_error {P₁ Q₀ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E}
    {YS : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i))
    (hc : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hεK : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd P₁ Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
      + d * (h * (4 * L * B * h + ε)) :=
  galerkin_step_error (IsOrthProj.modeProd hP₁ hc) hF hL hB ht₁ hh hA hS (by rw [hS₀, hA₀])
    (tucker_capture hF hL hB hP₁ hQ₀ ht₁ hh hA hK (fun i => (hK₀ i).trans hA₀.symm) hKcap hεK)

/-- **Robust local error of the Tucker BUG integrator under the Tucker normal-component
assumption** ([CerutiLubich2022, Lemma 7] with assumption 2 of Theorem 7).  Same as
`tucker_local_error`, but instead of the doubly-normal bound we assume, for each mode `i`, a map
`T i` (the tangent projector of the Tucker manifold at `YK i t₁`) whose range lies in the range
of `tangent (P₁ i) (Q₀ i)` (see the module docstring), with `P₁ i`, `Q₀ i` commuting, and the
normal-component bound `‖F(t, YK i t₁) - T i F(t, YK i t₁)‖ ≤ ε`. -/
theorem tucker_local_error_of_tangent {P₁ Q₀ T : Fin d → E →L[ℝ] E} {Y₀ : E}
    {YK : Fin d → ℝ → E} {YS : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : ∀ i, IsOrthProj (P₁ i)) (hQ₀ : ∀ i, IsOrthProj (Q₀ i))
    (hc : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)) (hPQ : ∀ i x, P₁ i (Q₀ i x) = Q₀ i (P₁ i x))
    (hT : ∀ i y, tangent (P₁ i) (Q₀ i) (T i y) = T i y) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁) (hK₀ : ∀ i, YK i t₀ = Y₀)
    (hKcap : ∀ i, P₁ i (YK i t₁) = YK i t₁)
    (hεT : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖F t (YK i t₁) - T i (F t (YK i t₁))‖ ≤ ε)
    (hS : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd P₁ Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
      + d * (h * (4 * L * B * h + ε)) :=
  tucker_local_error hF hL hB hP₁ hQ₀ hc ht₁ hh hA hA₀ hK hK₀ hKcap
    (fun i t ht => (norm_normal_le_of_tangent (hP₁ i) (hQ₀ i) (hPQ i) (hT i) _).trans
      (hεT i t ht)) hS hS₀

/-- All hypotheses of one step of the Tucker BUG integrator with `d` modes from `(t₀, Y₀)` to
`t₁`: co-range projectors `Q₀ i` of the matricizations of `Y₀`, new mode-basis projectors
`P₁ i`, K-step trajectories `YK i`, core-step trajectory `YS` (the new approximation is `YS t₁`)
and doubly-normal bound `ε` at the points `YK i t₁`. -/
structure IsTuckerBUGStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₁ : ∀ i, IsOrthProj (P₁ i)
  /-- The new mode projectors act on different modes and commute. -/
  comm₁ : ∀ i j x, P₁ i (P₁ j x) = P₁ j (P₁ i x)
  /-- Mode-`i` K-step: `YK i' = Q₀ i F(t, YK i)` (the matrix K-step `K̇ᵢ = Fᵢ(t, Kᵢ V⁰ᵢᵀ) V⁰ᵢ`). -/
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- The new mode-`i` basis captures `Kᵢ(t₁)`. -/
  kCap : ∀ i, P₁ i (YK i t₁) = YK i t₁
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁ i) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  /-- Core (Galerkin) step: `YS' = Π F(t, YS)` with `Π = P₁ 0 ∘ ⋯ ∘ P₁ (d-1)`. -/
  sSol : ODESolution (fun t x => modeProd P₁ (F t x)) YS t₀ t₁
  sStart : YS t₀ = modeProd P₁ Y₀

namespace IsTuckerBUGStep

variable {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E} {YS : ℝ → E}

/-- The core-step projector of a Tucker BUG step is an orthogonal projector. -/
lemma proj (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) : IsOrthProj (modeProd P₁) :=
  IsOrthProj.modeProd hs.projP₁ hs.comm₁

/-- On a nonempty step with at least one mode, the normal-component bound forces `ε ≥ 0`; in
any case `d ε ≥ 0`. -/
lemma natCast_mul_eps_nonneg (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁) :
    0 ≤ (d : ℝ) * ε := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact mul_nonneg (Nat.cast_nonneg d)
      ((norm_nonneg _).trans (hs.kNormal ⟨0, hd⟩ t₀ ⟨le_rfl, h01⟩))

/-- **Lemma 6 of [CerutiLubich2022]**, bundled form of `tucker_capture`. -/
theorem capture (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - modeProd P₁ (A t₁)‖ ≤ d * (h * (4 * L * B * h + ε)) :=
  tucker_capture hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hs.kSol
    (fun i => (hs.kStart i).trans hA₀.symm) hs.kCap hs.kNormal

/-- **Robust local error of the Tucker BUG integrator** ([CerutiLubich2022, Lemma 7]), bundled
form of `tucker_local_error`. -/
theorem local_error (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
      + d * (h * (4 * L * B * h + ε)) :=
  tucker_local_error hF hL hB hs.projP₁ hs.projQ₀ hs.comm₁ ht₁ hh hA hA₀ hs.kSol hs.kStart
    hs.kCap hs.kNormal hs.sSol hs.sStart

/-- **Robust local error of the Tucker BUG integrator, `O`-form** ([CerutiLubich2022, Lemma 7]:
`‖Y₁ - A₁‖ ≤ ĉ h (B L h + ε)`).  For step sizes `0 ≤ h ≤ H`:
`‖YS t₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`
depending only on `d`, `L`, `B` and `H`. -/
theorem local_error_le (hs : IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) :=
  (hs.local_error hF hL hB ht₁ hh hA hA₀).trans
    (tucker_bound_le hL hB.nonneg (hs.natCast_mul_eps_nonneg (by linarith)) hh hhH)

end IsTuckerBUGStep

end Local

/-! ### `d = 2`: the matrix BUG integrator -/

section MatrixCase

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- **For `d = 2` the Tucker BUG integrator is the matrix BUG integrator.**  A step of the
matrix BUG integrator (K-step with the right projector `Q₀`, L-step with the left projector
`P₀`, new projectors `P₁`, `Q₁`) is a step of the two-mode Tucker BUG integrator with co-range
projectors `![Q₀, P₀]` and new mode projectors `![P₁, Q₁]`. -/
theorem IsBUGStep.toTucker {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) :
    IsTuckerBUGStep F ε ![Q₀, P₀] ![P₁, Q₁] t₀ t₁ Y₀ ![YK, YL] YS where
  projQ₀ := Fin.forall_fin_two.2 ⟨hs.projQ₀, hs.projP₀⟩
  projP₁ := Fin.forall_fin_two.2 ⟨hs.projP₁, hs.projQ₁⟩
  comm₁ := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun _ => rfl, hs.comm₁⟩,
    Fin.forall_fin_two.2 ⟨fun x => (hs.comm₁ x).symm, fun _ => rfl⟩⟩
  kSol := Fin.forall_fin_two.2 ⟨hs.kSol, hs.lSol⟩
  kStart := Fin.forall_fin_two.2 ⟨hs.kStart, hs.lStart⟩
  kCap := Fin.forall_fin_two.2 ⟨hs.kCap, hs.lCap⟩
  kNormal := Fin.forall_fin_two.2 ⟨hs.kNormal, hs.lNormal⟩
  sSol := by rw [modeProd_two]; exact hs.sSol
  sStart := by rw [modeProd_two]; exact hs.sStart

/-- The two-mode Tucker local error bound is exactly the matrix BUG local error bound
`bug_local_error` ([CerutiLubich2022, Lemma 4]): the case `d = 2` of `tucker_local_error`. -/
theorem IsBUGStep.local_error_of_tucker {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {Y₀ : E} {YK YL YS : ℝ → E}
    (hs : IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) := by
  have h2 := hs.toTucker.local_error hF hL hB ht₁ hh hA hA₀
  simpa using h2

end MatrixCase

/-! ### Global error -/

section Global

variable {F : ℝ → E → E} {L B ε : ℝ} {d : ℕ}

/-- **Robust global error bound of the Tucker BUG integrator** (Ceruti–Lubich,
[CerutiLubich2022, Thm. 7], with explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and
bounded by `B`, `tₙ = t₀ + n h` with `0 ≤ h ≤ H`, and `A` a solution of `A' = F(t, A)` on
`[t₀, t₀ + N h]`.  For `n < N` let step `n` of the Tucker BUG integrator with `d` modes go from
`(tₙ, Y n)` to `Y (n+1) = YS n tₙ₊₁` with co-range projectors `Q n i` and new mode projectors
`P n i`, as described by `IsTuckerBUGStep`, and let `Φ n` be the exact flow on `[tₙ, tₙ₊₁]`
started at `Y n`.  Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (c₁ ε + c₂ h)),

with `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H` independent of singular values of
matricizations.  (Proof: `IsTuckerBUGStep.local_error_le` and Lady Windermere's fan.) -/
theorem tucker_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E}
    {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  intro n hn
  calc _ ≤ _ := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
    _ = _ := by ring

/-- **Robust global error bound of the Tucker BUG integrator, final form** (Ceruti–Lubich,
[CerutiLubich2022, Thm. 7]): under the hypotheses of `tucker_global_error`, with `ε ≥ 0`, an
initial error `‖Y 0 - A t₀‖ ≤ δ` and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁' ε + c₂' h,

with `c₀ = e^{L T}`, `c₁' = T e^{L T} c₁`, `c₂' = T e^{L T} c₂` depending only on `L`, `B`, `T`,
the step-size bound `H` and the number of modes `d`. -/
theorem tucker_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E}
    {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    (hY : ∀ n < N, Y (n + 1) = YS n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * tuckerC₁ d L H * ε
        + T * Real.exp (L * T) * tuckerC₂ d L B H * h := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (tuckerC₂_nonneg d hL hB.nonneg hH) hh)
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have h2 : Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h))
      ≤ Real.exp (L * T) * (δ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Global

/-! ### The rank-adaptive Tucker BUG integrator -/

section RankAdaptive

open scoped RealInnerProductSpace

variable {F : ℝ → E → E} {L B ε : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E} {d : ℕ}

/-- One step of the **rank-adaptive Tucker BUG integrator** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022, §4.1]) before truncation: a Tucker BUG step whose augmented mode projectors
`P̂ i` (bases `Ûᵢ` of the range of `(Kᵢ(t₁), U⁰ᵢ)`) also fix the starting value `Y₀`.  The core
step starts at `C₀ ×ᵢ (Ûᵢᵀ U⁰ᵢ)`, i.e. at `Π̂ Y₀ = Y₀` (`IsAugTuckerBUGStep.start`). -/
structure IsAugTuckerBUGStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₁ : Fin d → E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YS : ℝ → E) : Prop
    extends IsTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS where
  /-- The augmented bases contain the old bases: `P̂ i Y₀ = Y₀`. -/
  augment : ∀ i, P₁ i Y₀ = Y₀

namespace IsAugTuckerBUGStep

variable {Q₀ P₁ : Fin d → E →L[ℝ] E} {Y₀ : E} {YK : Fin d → ℝ → E} {YS : ℝ → E}

/-- The augmented core step starts at `Y₀` itself (Lemma 1 of [CerutiKuschLubich2022], Tucker
version). -/
lemma start (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) : YS t₀ = Y₀ := by
  rw [hs.sStart, modeProd_apply_eq_self hs.augment]

/-- **Local error of the rank-adaptive Tucker BUG integrator** ([CerutiKuschLubich2022, §4.2],
Tucker version of Thm 2): if the truncated result `Y₁` satisfies `‖Y₁ - YS t₁‖ ≤ ϑtr`, then
`‖Y₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + d ϑ) + d ϑ + ϑtr`. -/
theorem local_error_trunc (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) {Y₁ : E} {ϑtr : ℝ}
    (htr : ‖Y₁ - YS t₁‖ ≤ ϑtr) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
      + d * (h * (4 * L * B * h + ε)) + ϑtr := by
  have h1 := hs.local_error hF hL hB ht₁ hh hA hA₀
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Local error of the rank-adaptive Tucker BUG integrator, `O`-form**: for `0 ≤ h ≤ H`,
`‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h) + ϑtr`. -/
theorem local_error_trunc_le (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    {Y₁ : E} {ϑtr : ℝ} (htr : ‖Y₁ - YS t₁‖ ≤ ϑtr) :
    ‖Y₁ - A t₁‖ ≤ h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + ϑtr := by
  have h1 := hs.local_error_le hF hL hB ht₁ hh hhH hA hA₀
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Norm conservation of the untruncated rank-adaptive Tucker step**
([CerutiKuschLubich2022, §4.2], Tucker version of the proof of Thm 4): if `⟪F(t, x), x⟫ = 0` for all
`t`, `x`, then `‖YS t₁‖ = ‖Y₀‖`. -/
theorem norm_eq (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ := by
  have h0 : modeProd P₁ (YS t₀) = YS t₀ := by
    rw [hs.start]; exact modeProd_apply_eq_self hs.augment
  rw [← hs.start]
  exact hs.sSol.galerkin_norm_eq hs.proj h0 (fun t _ => hF t _) t₁ ⟨h01, le_rfl⟩

/-- **Norm conservation up to the truncation tolerance** for the rank-adaptive Tucker BUG
integrator ([CerutiKuschLubich2022, Thm. 4] and §4.2): if `⟪F(t, x), x⟫ = 0` and the truncated
result satisfies `‖Y₁ - YS t₁‖ ≤ ϑ`, then `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`. -/
theorem norm_sub_le (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) {Y₁ : E} {ϑ : ℝ} (htr : ‖Y₁ - YS t₁‖ ≤ ϑ) :
    |‖Y₁‖ - ‖Y₀‖| ≤ ϑ := by
  rw [← hs.norm_eq h01 hF]
  exact (abs_norm_sub_norm_le _ _).trans htr

/-- **Energy decay of the untruncated rank-adaptive Tucker step for gradient systems**
([CerutiKuschLubich2022, Thm. 5] and §4.2): if `F(t, x) = -∇ℰ(x)` then `ℰ(YS t₁) ≤ ℰ(Y₀)`. -/
theorem energy_le (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    {ℰ : E → ℝ} {g : E → E} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hFg : ∀ t x, F t x = -g x) : ℰ (YS t₁) ≤ ℰ Y₀ := by
  have hfun : (fun t x => modeProd P₁ (F t x)) = fun _ x => -modeProd P₁ (g x) := by
    funext t x; rw [hFg, map_neg]
  have hS := hs.sSol
  rw [hfun] at hS
  rw [← hs.start]
  exact hS.energy_le_gradFlow hs.proj hℰ t₁ ⟨h01, le_rfl⟩

/-- **Energy decay up to truncation for gradient systems** ([CerutiKuschLubich2022, Thm. 5] and
§4.2): if `F(t, x) = -∇ℰ(x)`, the truncated result satisfies `‖Y₁ - YS t₁‖ ≤ ϑ` and `‖∇ℰ‖ ≤ β` on
the segment `[YS t₁, Y₁]` (`β` plays the role of `‖G(Y₁)‖ + O(ϑ)` in the paper), then
`ℰ(Y₁) ≤ ℰ(Y₀) + β ϑ`. -/
theorem energy_le_trunc (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    {ℰ : E → ℝ} {g : E → E} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hFg : ∀ t x, F t x = -g x) {Y₁ : E} {ϑ β : ℝ} (htr : ‖Y₁ - YS t₁‖ ≤ ϑ)
    (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) : ℰ Y₁ ≤ ℰ Y₀ + β * ϑ := by
  have h1 := hs.energy_le h01 hℰ hFg
  have h2 := abs_energy_sub_le hℰ hβ
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ _ (left_mem_segment ℝ _ _))
  have h3 : β * ‖Y₁ - YS t₁‖ ≤ β * ϑ := mul_le_mul_of_nonneg_left htr hβ0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Norm dissipation of the untruncated rank-adaptive Tucker step**: if
`⟪F(t, x), x⟫ ≤ 0` for all `t`, `x` (dissipative problems), then `‖YS t₁‖ ≤ ‖Y₀‖`. -/
theorem norm_le (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ ≤ 0) : ‖YS t₁‖ ≤ ‖Y₀‖ := by
  have h0 : modeProd P₁ (YS t₀) = YS t₀ := by
    rw [hs.start]; exact modeProd_apply_eq_self hs.augment
  rw [← hs.start]
  exact hs.sSol.galerkin_norm_le hs.proj h0 (fun t _ => hF t _) t₁ ⟨h01, le_rfl⟩

/-- A map commuting with every mode projector commutes with their product. -/
lemma comm_modeProd {J : E →L[ℝ] E} (hJP : ∀ i z, J (P₁ i z) = P₁ i (J z)) (z : E) :
    J (modeProd P₁ z) = modeProd P₁ (J z) :=
  listProd_apply_comm (fun S hS x => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS
    exact hJP i x) z

/-- **Energy conservation of the untruncated rank-adaptive Tucker step for Hamiltonian-type
fields** ([CerutiKuschLubich2022], Thms 6–7 and §4.2): if `F(t, x) = J ∇ℰ(x)` with `J` skew
(`⟪J z, z⟫ = 0`, e.g. multiplication by `-i` for Schrödinger equations in real form) and `J`
commuting with every mode projector, then `ℰ(YS t₁) = ℰ(Y₀)`. -/
theorem energy_eq_of_skew (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    {ℰ : E → ℝ} {g : E → E} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E}
    (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ i z, J (P₁ i z) = P₁ i (J z))
    (hFJ : ∀ t x, F t x = J (g x)) : ℰ (YS t₁) = ℰ Y₀ := by
  rw [← hs.start]
  exact hs.sSol.galerkin_energy_eq_of_skew hs.proj hℰ hJ (comm_modeProd hJP) hFJ t₁
    ⟨h01, le_rfl⟩

/-- **Energy conservation up to truncation for Hamiltonian-type fields** ([CerutiKuschLubich2022],
Thms 6–7 and §4.2): under the hypotheses of `energy_eq_of_skew`, if the truncated result
satisfies `‖Y₁ - YS t₁‖ ≤ ϑ` and `‖∇ℰ‖ ≤ β` on the segment `[YS t₁, Y₁]`, then
`|ℰ(Y₁) - ℰ(Y₀)| ≤ β ϑ`. -/
theorem energy_sub_le_of_skew (hs : IsAugTuckerBUGStep F ε Q₀ P₁ t₀ t₁ Y₀ YK YS)
    (h01 : t₀ ≤ t₁) {ℰ : E → ℝ} {g : E → E} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ i z, J (P₁ i z) = P₁ i (J z))
    (hFJ : ∀ t x, F t x = J (g x)) {Y₁ : E} {ϑ β : ℝ} (htr : ‖Y₁ - YS t₁‖ ≤ ϑ)
    (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) : |ℰ Y₁ - ℰ Y₀| ≤ β * ϑ := by
  have h := hs.sSol.truncated_energy_sub_le_of_skew hs.proj hℰ hJ (comm_modeProd hJP) hFJ h01
    htr hβ
  rwa [hs.start] at h

end IsAugTuckerBUGStep

/-- **Robust global error bound of the rank-adaptive Tucker BUG integrator**
(Ceruti–Kusch–Lubich, [CerutiKuschLubich2022, §4.2]: Theorem 7 of [CerutiLubich2022] "with an extra
term `c₃ ϑ` as in Theorem 2"). Under the hypotheses of `tucker_global_error`, with augmented steps
(`IsAugTuckerBUGStep`) followed by truncations `‖Y (n+1) - YS n tₙ₊₁‖ ≤ ϑ`, for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (c₁ ε + c₂ h) + n ϑ). -/
theorem aug_tucker_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E}
    {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsAugTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    {ϑ : ℝ} (htr : ∀ n < N, ‖Y (n + 1) - YS n (t₀ + (n + 1) * h)‖ ≤ ϑ)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + n * ϑ) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + ϑ := fun n hn =>
    (hstep n hn).local_error_trunc_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn) (htr n hn)
  intro n hn
  calc _ ≤ _ := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
    _ = _ := by ring

/-- **Robust global error bound of the rank-adaptive Tucker BUG integrator, final form**
(Ceruti–Kusch–Lubich, [CerutiKuschLubich2022, Thm. 2] and §4.2): under the hypotheses of
`aug_tucker_global_error`, with `ε ≥ 0`, `‖Y 0 - A t₀‖ ≤ δ` and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁' ε + c₂' h + c₃ n ϑ,

with `c₀ = c₃ = e^{L T}`, `c₁' = T e^{L T} c₁`, `c₂' = T e^{L T} c₂` depending only on `L`, `B`,
`T`, `H` and `d`. -/
theorem aug_tucker_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Q P : ℕ → Fin d → E →L[ℝ] E}
    {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E} {YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsAugTuckerBUGStep F ε (Q n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n))
    {ϑ : ℝ} (htr : ∀ n < N, ‖Y (n + 1) - YS n (t₀ + (n + 1) * h)‖ ≤ ϑ)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * tuckerC₁ d L H * ε
        + T * Real.exp (L * T) * tuckerC₂ d L B H * h + Real.exp (L * T) * (n * ϑ) := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ tuckerC₁ d L H * ε + tuckerC₂ d L B H * h :=
    add_nonneg (mul_nonneg (tuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (tuckerC₂_nonneg d hL hB.nonneg hH) hh)
  have hnϑ : 0 ≤ (n : ℝ) * ϑ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (htr 0 (by omega)))
  have h1 := aug_tucker_global_error hF hL hB hh hhH hA hstep htr hΦ hΦ₀ n hn
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hTg := mul_le_mul_of_nonneg_right hT hg
  have hng := mul_nonneg hnh hg
  have hin : ‖Y 0 - A t₀‖ + n * h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + n * ϑ
      ≤ δ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + n * ϑ := by linarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h)
      + n * ϑ := by
    have := norm_nonneg (Y 0 - A t₀)
    linarith
  calc _ ≤ _ := h1
    _ ≤ Real.exp (L * T) * (δ + T * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) + n * ϑ) :=
        mul_le_mul hexp hin hin0 (Real.exp_pos _).le
    _ = _ := by ring

end RankAdaptive

/-! ### The parallel Tucker BUG integrator -/

section ParallelTucker

/-- The sum of two orthogonal projectors with orthogonal ranges (`P Q = 0`) is an orthogonal
projector (e.g. `U⁰ᵢU⁰ᵢᵀ + ŨᵢŨᵢᵀ = ÛᵢÛᵢᵀ` for `Ûᵢ = (U⁰ᵢ, Ũᵢ)`). -/
lemma IsOrthProj.add_of_orth {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (h : ∀ x, P (Q x) = 0) : IsOrthProj (P + Q) where
  idem x := by
    have hQP : Q (P x) = 0 := ext_inner_right ℝ fun y => by
      rw [hQ.symm, hP.symm, h, inner_zero_right, inner_zero_left]
    simp only [add_apply, map_add, hP.idem, hQ.idem, h, hQP]
    abel
  symm x y := by
    simp only [add_apply, inner_add_left, inner_add_right, hP.symm, hQ.symm]

/-- Old mode projectors `P₀ i` and new directions `Pa i` (orthogonal projectors with
`P₀ i Pa i = 0`, pairwise commuting) form a `ModeSplit`. -/
lemma ModeSplit.of_proj {d : ℕ} {p q : Fin d → E →L[ℝ] E} (hp : ∀ i, IsOrthProj (p i))
    (hq : ∀ i, IsOrthProj (q i)) (horth : ∀ i x, p i (q i x) = 0)
    (hpp : ∀ i j x, p i (p j x) = p j (p i x)) (hpq : ∀ i j x, p i (q j x) = q j (p i x))
    (hqq : ∀ i j x, q i (q j x) = q j (q i x)) : ModeSplit p q where
  pp i := (hp i).idem'
  qq i := (hq i).idem'
  pq i := ContinuousLinearMap.ext (horth i)
  qp i := ContinuousLinearMap.ext fun x => by
    change q i (p i x) = 0
    rw [← hpq, horth]
  cpp i j := ContinuousLinearMap.ext (hpp i j)
  cpq i j := ContinuousLinearMap.ext (hpq i j)
  cqq i j := ContinuousLinearMap.ext (hqq i j)

/-- The "at most one new mode" block projector is an orthogonal projector. -/
theorem isOrthProj_modeProdLeOne {d : ℕ} {p q : Fin d → E →L[ℝ] E} (hp : ∀ i, IsOrthProj (p i))
    (hq : ∀ i, IsOrthProj (q i)) (hs : ModeSplit p q) : IsOrthProj (modeProdLeOne p q) := by
  induction d with
  | zero => exact IsOrthProj.one
  | succ d ih =>
    rw [modeProdLeOne_succ]
    have hM := ih (fun i => hp i.succ) (fun i => hq i.succ) hs.tail
    have hY : IsOrthProj (modeProd fun i => p i.succ) :=
      IsOrthProj.modeProd (fun i => hp i.succ) fun i j => Commute.clm_apply (hs.cpp i.succ j.succ)
    have hpM : Commute (p 0) (modeProdLeOne (fun i => p i.succ) fun i => q i.succ) :=
      commute_modeProdLeOne (fun i => hs.cpp 0 _) (fun i => hs.cpq 0 _)
    have hqY : Commute (q 0) (modeProd fun i => p i.succ) :=
      commute_modeProd fun i => (hs.cpq _ 0).symm
    refine IsOrthProj.add_of_orth ((hp 0).mul hM (Commute.clm_apply hpM))
      ((hq 0).mul hY (Commute.clm_apply hqY))
      fun x => ?_
    have hqM : Commute (q 0) (modeProdLeOne (fun i => p i.succ) fun i => q i.succ) :=
      commute_modeProdLeOne (fun i => (hs.cpq _ 0).symm) (fun i => hs.cqq 0 _)
    change p 0 (modeProdLeOne (fun i => p i.succ) (fun i => q i.succ)
      (q 0 (modeProd (fun i => p i.succ) x))) = 0
    rw [← Commute.clm_apply hqM]
    exact congrArg (fun f : E →L[ℝ] E => f _) (hs.pq 0)

/-- **Distance between the parallel and the rank-adaptive Tucker integrators** (abstract form of
the proof of Theorem 3.1 of [CerutiEtAl2024]).  Let `M₀` (old core projector `∏ P₀ i`), `S`
(core plus single-new-mode blocks) and `M` (augmented core projector `∏ (P₀ i + Pa i)`) be
orthogonal projectors with `M M₀ = M₀`, `M S = S`, and let `T` be a map (the tangent projector
at `Y₀`) with `M T = S T`.  Let `YC' = M₀ F(t, YC)` (the parallel core step) and
`YB' = M F(t, YB)` (the rank-adaptive Galerkin step), both started at `Y₀`.  If `F` is
`L`-Lipschitz, bounded by `B`, `‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)` and
`‖F(t₀, Y₀) - T F(t₀, Y₀)‖ ≤ ε`, then the parallel result
`YC(t₁) + h (S - M₀) F(t₀, Y₀)` (`h = t₁ - t₀`) satisfies

    ‖YC(t₁) + h (S - M₀) F(t₀, Y₀) - YB(t₁)‖ ≤ h ((3 L B + Lₜ) h + ε).

(In the paper: `2 L B h²` for the core block (3.3), `L B h²` for the blocks (3.4), and
`c h² + h ε` for the remaining blocks; for autonomous `F`, `Lₜ = 0`.) -/
theorem parallel_sub_galerkin_le {F : ℝ → E → E} {L B ε Lt : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt) {M₀ S M T : E →L[ℝ] E}
    (hM₀ : IsOrthProj M₀) (hS : IsOrthProj S) (hM : IsOrthProj M) (hMM₀ : ∀ x, M (M₀ x) = M₀ x)
    (hMS : ∀ x, M (S x) = S x) (hMT : ∀ y, M (T y) = S (T y)) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    {Y₀ : E} {YC YB : ℝ → E} (hC : ODESolution (fun t x => M₀ (F t x)) YC t₀ t₁)
    (hC₀ : YC t₀ = Y₀) (hYB : ODESolution (fun t x => M (F t x)) YB t₀ t₁) (hYB₀ : YB t₀ = Y₀)
    (hε : ‖F t₀ Y₀ - T (F t₀ Y₀)‖ ≤ ε)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) :
    ‖YC t₁ + (t₁ - t₀) • (S - M₀) (F t₀ Y₀) - YB t₁‖
      ≤ (t₁ - t₀) * ((3 * L * B + Lt) * (t₁ - t₀) + ε) := by
  set w : E := (S - M₀) (F t₀ Y₀) with hw
  set g : ℝ → E := fun t => YC t + (t - t₀) • w - YB t with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (hC.cont.add ((continuous_id.sub continuous_const).smul continuous_const).continuousOn).sub
      hYB.cont
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g
      (M₀ (F t (YC t)) + (1 : ℝ) • w - M (F t (YB t))) (Ici t) t := fun t ht =>
    ((hC.deriv t ht).add (((hasDerivWithinAt_id t _).sub_const t₀).smul_const w)).sub
      (hYB.deriv t ht)
  have hR : IsOrthProj (M - S) := hS.sub_of_le hM hMS
  have hMM : IsOrthProj (M - M₀) := hM₀.sub_of_le hM hMM₀
  have hB0 : 0 ≤ B := hB.nonneg
  have hBC := hC.norm_sub_le_of_bounded (hB.comp_contraction M₀ hM₀.norm_le)
  have hBB := hYB.norm_sub_le_of_bounded (hB.comp_contraction M hM.norm_le)
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖M₀ (F t (YC t)) + (1 : ℝ) • w - M (F t (YB t))‖
      ≤ (3 * L * B + Lt) * (t₁ - t₀) + ε := by
    intro t ht
    have htI : t ∈ Icc t₀ t₁ := Ico_subset_Icc_self ht
    have hdec : M₀ (F t (YC t)) + (1 : ℝ) • w - M (F t (YB t))
        = -(M₀ (F t (YB t) - F t (YC t)) + (M - M₀) (F t (YB t) - F t₀ Y₀)
          + (M - S) (F t₀ Y₀ - T (F t₀ Y₀))) := by
      have h := hMT (F t₀ Y₀)
      simp only [hw, one_smul, sub_apply, map_sub, h]
      abel
    have hC' : ‖YC t - Y₀‖ ≤ B * (t - t₀) := by rw [← hC₀]; exact hBC t htI
    have hB' : ‖YB t - Y₀‖ ≤ B * (t - t₀) := by rw [← hYB₀]; exact hBB t htI
    have h1 : ‖M₀ (F t (YB t) - F t (YC t))‖ ≤ L * (2 * B * (t - t₀)) := by
      refine (hM₀.norm_le _).trans ((hF t _ _).trans (mul_le_mul_of_nonneg_left ?_ hL))
      calc ‖YB t - YC t‖ ≤ ‖YB t - Y₀‖ + ‖Y₀ - YC t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ B * (t - t₀) + B * (t - t₀) := by rw [norm_sub_rev Y₀]; exact add_le_add hB' hC'
        _ = 2 * B * (t - t₀) := by ring
    have h2 : ‖(M - M₀) (F t (YB t) - F t₀ Y₀)‖ ≤ L * (B * (t - t₀)) + Lt * (t - t₀) := by
      refine (hMM.norm_le _).trans ?_
      calc ‖F t (YB t) - F t₀ Y₀‖ ≤ ‖F t (YB t) - F t Y₀‖ + ‖F t Y₀ - F t₀ Y₀‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ L * (B * (t - t₀)) + Lt * (t - t₀) :=
            add_le_add ((hF t _ _).trans (mul_le_mul_of_nonneg_left hB' hL)) (hFt t ht)
    have h3 : ‖(M - S) (F t₀ Y₀ - T (F t₀ Y₀))‖ ≤ ε := (hR.norm_le _).trans hε
    have hts : t - t₀ ≤ t₁ - t₀ := by linarith [ht.2]
    have hcoef : 0 ≤ 3 * L * B + Lt := by positivity
    rw [hdec, norm_neg]
    calc _ ≤ ‖M₀ (F t (YB t) - F t (YC t))‖ + ‖(M - M₀) (F t (YB t) - F t₀ Y₀)‖
          + ‖(M - S) (F t₀ Y₀ - T (F t₀ Y₀))‖ := norm_add₃_le
      _ ≤ L * (2 * B * (t - t₀)) + (L * (B * (t - t₀)) + Lt * (t - t₀)) + ε := by
          linarith
      _ = (3 * L * B + Lt) * (t - t₀) + ε := by ring
      _ ≤ (3 * L * B + Lt) * (t₁ - t₀) + ε := by
          have := mul_le_mul_of_nonneg_left hts hcoef
          linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨ht, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hC₀, hYB₀]
  rw [hg₀, sub_zero] at hmvt
  calc ‖YC t₁ + (t₁ - t₀) • w - YB t₁‖ = ‖g t₁‖ := rfl
    _ ≤ _ := hmvt
    _ = _ := by ring

/-- The untruncated result `Ŷ₁ = Ĉ₁ ×ᵢ Ûᵢ` of one step of the **parallel Tucker BUG integrator**
([CerutiEtAl2024, §3.1]), `Ûᵢ = (U⁰ᵢ, Ũᵢ)`: with `P₀ i = U⁰ᵢU⁰ᵢᵀ`, `Pa i = ŨᵢŨᵢᵀ`, the core block
(3.3) is `yC = C(t₁) ×ᵢ U⁰ᵢ` (the parallel core step) and the blocks (3.4) are
`C̃ᵢ ×ᵢ Ũᵢ ×_{j ≠ i} U⁰ⱼ = h (Pa i ∏_{j ≠ i} P₀ j) F(Y₀)`, whose sum is
`h (modeProdLeOne P₀ Pa - modeProd P₀) F(Y₀)` (`modeProdLeOne_eq_sum`); all other blocks of `Ĉ₁`
are zero. -/
def parTuckerBUG {d : ℕ} (P₀ Pa : Fin d → E →L[ℝ] E) (yC : E) (h : ℝ) (f₀ : E) : E :=
  yC + h • (modeProdLeOne P₀ Pa - modeProd P₀) f₀

lemma parTuckerC₁_nonneg (d : ℕ) {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H) : 0 ≤ parTuckerC₁ d L H :=
  add_nonneg (tuckerC₁_nonneg d hL hH) zero_le_one

lemma parTuckerC₂_nonneg (d : ℕ) {L B Lt H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hLt : 0 ≤ Lt)
    (hH : 0 ≤ H) : 0 ≤ parTuckerC₂ d L B Lt H := by
  have := tuckerC₂_nonneg d hL hB hH
  unfold parTuckerC₂; positivity

/-- One step of the **parallel Tucker BUG integrator** (Ceruti–Kusch–Lubich–Sulz,
[CerutiEtAl2024, §3.1]) from `(t₀, Y₀)` to `t₁`, abstract form.  For each mode `i`:

* `P₀ i = U⁰ᵢU⁰ᵢᵀ` (old basis, `P₀ i Y₀ = Y₀`) and `Pa i = ŨᵢŨᵢᵀ` (new directions, `U⁰ᵢᵀŨᵢ = 0`,
  i.e. `P₀ i Pa i = 0`) are orthogonal projectors, all commuting (different modes); the
  augmented basis `Ûᵢ = (U⁰ᵢ, Ũᵢ)` has projector `P₀ i + Pa i`;
* the Kᵢ-step `YK i' = Q₀ i F(t, YK i)`, `YK i t₀ = Y₀`, is captured by the augmented basis,
  with doubly-normal component at most `ε` (as for the rank-adaptive integrator);
* the core step `YC' = (∏ P₀ i) F(t, YC)`, `YC t₀ = Y₀` (rank-`r` core update, eq. (3.2)) runs in
  parallel with the Kᵢ-steps;
* `normal₀`: the normal component of `F(t₀, Y₀)` with respect to the tangent hull
  `modeProdLeOne P₀ (1 - P₀)` at `Y₀` is at most `ε` (implied by the paper's assumption 2 at `Y₀`,
  see `norm_sub_tangentHull_le`).

The untruncated result is `parTuckerBUG P₀ Pa (YC t₁) (t₁ - t₀) (F t₀ Y₀)`. -/
structure IsParTuckerBUGStep (F : ℝ → E → E) (ε : ℝ) {d : ℕ} (Q₀ P₀ Pa : Fin d → E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK : Fin d → ℝ → E) (YC : ℝ → E) : Prop where
  projQ₀ : ∀ i, IsOrthProj (Q₀ i)
  projP₀ : ∀ i, IsOrthProj (P₀ i)
  projPa : ∀ i, IsOrthProj (Pa i)
  /-- The new directions are orthogonal to the old basis: `U⁰ᵢᵀ Ũᵢ = 0`. -/
  orth : ∀ i x, P₀ i (Pa i x) = 0
  comm₀₀ : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x)
  comm₀a : ∀ i j x, P₀ i (Pa j x) = Pa j (P₀ i x)
  commaa : ∀ i j x, Pa i (Pa j x) = Pa j (Pa i x)
  /-- `Y₀` has mode-`i` basis `U⁰ᵢ`. -/
  start₀ : ∀ i, P₀ i Y₀ = Y₀
  kSol : ∀ i, ODESolution (fun t x => Q₀ i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i, YK i t₀ = Y₀
  /-- The augmented basis `Ûᵢ = (U⁰ᵢ, Ũᵢ)` spans the range of `(U⁰ᵢ, Kᵢ(t₁))`. -/
  kCap : ∀ i, (P₀ i + Pa i) (YK i t₁) = YK i t₁
  kNormal : ∀ i, ∀ t ∈ Icc t₀ t₁, ‖(1 - (P₀ i + Pa i)) ((1 - Q₀ i) (F t (YK i t₁)))‖ ≤ ε
  /-- The core step (3.2): `YC = C ×ᵢ U⁰ᵢ` solves `YC' = (∏ P₀ i) F(t, YC)`. -/
  cSol : ODESolution (fun t x => modeProd P₀ (F t x)) YC t₀ t₁
  cStart : YC t₀ = Y₀
  normal₀ : ‖F t₀ Y₀ - modeProdLeOne P₀ (fun i => 1 - P₀ i) (F t₀ Y₀)‖ ≤ ε

/-- For `d = 2` (matrices) the tangent hull `modeProdLeOne ![P, Q] (1 - ![P, Q])` is the matrix
tangent projector `P + Q - P Q` (`tangent P Q`). -/
lemma modeProdLeOne_compl_two (P Q : E →L[ℝ] E) :
    modeProdLeOne ![P, Q] (fun i => 1 - ![P, Q] i) = tangent P Q := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, modeProdLeOne_succ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, modeProdLeOne_zero,
    mul_one, modeProd_zero, add_sub_cancel, modeProd_succ, tangent]
  noncomm_ring

/-- The paper's normal-component assumption implies `normal₀`: if `T` (the tangent projector of
the Tucker manifold at `Y₀`) has range in the range of the tangent hull
`Tₕ = modeProdLeOne P₀ (1 - P₀)` (every tangent vector `δC ×ⱼ U⁰ⱼ + ∑ᵢ C ×ᵢ δUᵢ ×_{j ≠ i} U⁰ⱼ` is
fixed by `Tₕ`), then `‖z - Tₕ z‖ ≤ ‖z - T z‖`. -/
theorem norm_sub_tangentHull_le {d : ℕ} {P₀ : Fin d → E →L[ℝ] E} (hP : ∀ i, IsOrthProj (P₀ i))
    (hc : ∀ i j x, P₀ i (P₀ j x) = P₀ j (P₀ i x)) {T : E →L[ℝ] E}
    (hT : ∀ y, modeProdLeOne P₀ (fun i => 1 - P₀ i) (T y) = T y) (z : E) :
    ‖z - modeProdLeOne P₀ (fun i => 1 - P₀ i) z‖ ≤ ‖z - T z‖ := by
  have hs : ModeSplit P₀ (fun i => 1 - P₀ i) :=
    ModeSplit.of_proj hP (fun i => (hP i).compl) (fun i x => by simp [(hP i).idem])
      hc (fun i j x => by simp [hc]) (fun i j x => by simp [hc]; abel)
  have hTh : IsOrthProj (modeProdLeOne P₀ fun i => 1 - P₀ i) :=
    isOrthProj_modeProdLeOne hP (fun i => (hP i).compl) hs
  have heq : z - modeProdLeOne P₀ (fun i => 1 - P₀ i) z
      = (z - T z) - modeProdLeOne P₀ (fun i => 1 - P₀ i) (z - T z) := by
    rw [map_sub, hT]; abel
  rw [heq]
  exact hTh.norm_sub_le _

namespace IsParTuckerBUGStep

variable {F : ℝ → E → E} {ε : ℝ} {d : ℕ} {Q₀ P₀ Pa : Fin d → E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK : Fin d → ℝ → E} {YC : ℝ → E}

lemma split (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) : ModeSplit P₀ Pa :=
  ModeSplit.of_proj hs.projP₀ hs.projPa hs.orth hs.comm₀₀ hs.comm₀a hs.commaa

/-- The augmented mode projectors `ÛᵢÛᵢᵀ = P₀ i + Pa i` are orthogonal projectors. -/
lemma projAug (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) (i : Fin d) :
    IsOrthProj (P₀ i + Pa i) :=
  (hs.projP₀ i).add_of_orth (hs.projPa i) (hs.orth i)

/-- The augmented mode projectors fix `Y₀`. -/
lemma augFix (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) (i : Fin d) :
    (P₀ i + Pa i) Y₀ = Y₀ := by
  have h : Pa i Y₀ = 0 := by
    rw [← hs.start₀ i]
    exact congrArg (fun f : E →L[ℝ] E => f Y₀) (hs.split.qp i)
  rw [add_apply, hs.start₀ i, h, add_zero]

/-- **The comparison rank-adaptive step.**  With the same augmented bases, the rank-adaptive
Tucker BUG step (`IsAugTuckerBUGStep`, [CerutiKuschLubich2022]) whose Galerkin trajectory `YB`
solves `YB' = (∏ (P₀ i + Pa i)) F(t, YB)`, `YB t₀ = Y₀`, has all the hypotheses of the parallel
step. -/
theorem toAug (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) {YB : ℝ → E}
    (hYB : ODESolution (fun t x => modeProd (fun i => P₀ i + Pa i) (F t x)) YB t₀ t₁)
    (hYB₀ : YB t₀ = Y₀) : IsAugTuckerBUGStep F ε Q₀ (fun i => P₀ i + Pa i) t₀ t₁ Y₀ YK YB where
  projQ₀ := hs.projQ₀
  projP₁ := hs.projAug
  comm₁ i j := Commute.clm_apply (hs.split.commute_add i j)
  kSol := hs.kSol
  kStart := hs.kStart
  kCap := hs.kCap
  kNormal := hs.kNormal
  sSol := hYB
  sStart := by rw [hYB₀, modeProd_apply_eq_self hs.augFix]
  augment := hs.augFix

/-- **The parallel and the rank-adaptive Tucker integrators differ by `O(h (h + ε))`** (proof
of Theorem 3.1 of [CerutiEtAl2024]): `‖Ŷ₁ - Ŷ₁ᴮᵁᴳ‖ ≤ h ((3 L B + Lₜ) h + ε)`. -/
theorem parallel_sub_aug (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) {L B Lt : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) (ht : t₀ ≤ t₁) {YB : ℝ → E}
    (hYB : ODESolution (fun t x => modeProd (fun i => P₀ i + Pa i) (F t x)) YB t₀ t₁)
    (hYB₀ : YB t₀ = Y₀) :
    ‖parTuckerBUG P₀ Pa (YC t₁) (t₁ - t₀) (F t₀ Y₀) - YB t₁‖
      ≤ (t₁ - t₀) * ((3 * L * B + Lt) * (t₁ - t₀) + ε) := by
  have hsp := hs.split
  have app : ∀ {a b c : E →L[ℝ] E}, a * b = c → ∀ x, a (b x) = c x := fun h x =>
    congrArg (fun f : E →L[ℝ] E => f x) h
  exact parallel_sub_galerkin_le hF hL hB hLt
    (IsOrthProj.modeProd hs.projP₀ hs.comm₀₀)
    (isOrthProj_modeProdLeOne hs.projP₀ hs.projPa hsp)
    (IsOrthProj.modeProd hs.projAug fun i j => Commute.clm_apply (hsp.commute_add i j))
    (app hsp.modeProd_add_mul_modeProd) (app hsp.modeProd_add_mul_leOne)
    (fun y => (app hsp.modeProd_add_mul_tangent y).trans (app hsp.leOne_mul_tangent y).symm)
    ht hs.cSol hs.cStart hYB hYB₀ hs.normal₀ hFt

/-- **Robust local error of the parallel Tucker BUG integrator** (Ceruti–Kusch–Lubich–Sulz,
[CerutiEtAl2024], proof of Theorem 3.1, explicit constants).  Let `F` be `L`-Lipschitz
(`L ≥ 0`), bounded by `B`, with `‖F(t, Y₀) - F(t₀, Y₀)‖ ≤ Lₜ (t - t₀)` on the step (`Lₜ = 0` for
autonomous `F`, as in the paper), and let `A` be the exact solution with `A t₀ = Y₀`,
`t₁ = t₀ + h`, `h ≥ 0`.  Given the (auxiliary, not computed) Galerkin trajectory `YB` of the
rank-adaptive Tucker integrator with the same augmented bases, the untruncated parallel result
`Ŷ₁` satisfies, with `ϑ = h (4 L B h + ε)`,

    ‖Ŷ₁ - A t₁‖ ≤ (e^{L h} - 1) (B h + d ϑ) + d ϑ + h ((3 L B + Lₜ) h + ε).

The bound does not depend on singular values of matricizations.  (`YB` exists by
`exists_ODESolution_clm`; see `local_error_of_complete`.) -/
theorem local_error (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) {L B Lt h : ℝ}
    {A : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hLt : 0 ≤ Lt) (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    {YB : ℝ → E} (hYB : ODESolution (fun t x => modeProd (fun i => P₀ i + Pa i) (F t x)) YB t₀ t₁)
    (hYB₀ : YB t₀ = Y₀) :
    ‖parTuckerBUG P₀ Pa (YC t₁) h (F t₀ Y₀) - A t₁‖
      ≤ (Real.exp (L * h) - 1) * (B * h + d * (h * (4 * L * B * h + ε)))
        + d * (h * (4 * L * B * h + ε)) + h * ((3 * L * B + Lt) * h + ε) := by
  have hth : t₁ - t₀ = h := by rw [ht₁]; ring
  have h1 := hs.parallel_sub_aug hF hL hB hLt hFt (by linarith) hYB hYB₀
  rw [hth] at h1
  have h2 := (hs.toAug hYB hYB₀).local_error hF hL hB ht₁ hh hA hA₀
  calc _ ≤ ‖parTuckerBUG P₀ Pa (YC t₁) h (F t₀ Y₀) - YB t₁‖ + ‖YB t₁ - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Robust local error of the parallel Tucker BUG integrator, `O`-form**: for `0 ≤ h ≤ H`,
`‖Ŷ₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)` with `c₁ = parTuckerC₁ d L H`, `c₂ = parTuckerC₂ d L B Lₜ H`
([CerutiEtAl2024]: `c₁ h² + c₂ h ε`). -/
theorem local_error_le (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) {L B Lt h H : ℝ}
    {A : ℝ → E} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hLt : 0 ≤ Lt) (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀))
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) {YB : ℝ → E}
    (hYB : ODESolution (fun t x => modeProd (fun i => P₀ i + Pa i) (F t x)) YB t₀ t₁)
    (hYB₀ : YB t₀ = Y₀) :
    ‖parTuckerBUG P₀ Pa (YC t₁) h (F t₀ Y₀) - A t₁‖
      ≤ h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) := by
  have hth : t₁ - t₀ = h := by rw [ht₁]; ring
  have h1 := hs.parallel_sub_aug hF hL hB hLt hFt (by linarith) hYB hYB₀
  rw [hth] at h1
  have h2 := (hs.toAug hYB hYB₀).local_error_le hF hL hB ht₁ hh hhH hA hA₀
  calc _ ≤ ‖parTuckerBUG P₀ Pa (YC t₁) h (F t₀ Y₀) - YB t₁‖ + ‖YB t₁ - A t₁‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ h * ((3 * L * B + Lt) * h + ε) + h * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * h) :=
        by linarith
    _ = _ := by unfold parTuckerC₁ parTuckerC₂; ring

/-- **Robust local error of the parallel Tucker BUG integrator without auxiliary trajectory**:
on a Banach space and for `F` continuous in time, the comparison trajectory of
`local_error_le` exists (`exists_ODESolution_clm`), so `‖Ŷ₁ - A t₁‖ ≤ h (c₁ ε + c₂ h)`. -/
theorem local_error_of_complete [CompleteSpace E]
    (hs : IsParTuckerBUGStep F ε Q₀ P₀ Pa t₀ t₁ Y₀ YK YC) {L B Lt h H : ℝ} {A : ℝ → E}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hLt : 0 ≤ Lt)
    (hFt : ∀ t ∈ Ico t₀ t₁, ‖F t Y₀ - F t₀ Y₀‖ ≤ Lt * (t - t₀)) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖parTuckerBUG P₀ Pa (YC t₁) h (F t₀ Y₀) - A t₁‖
      ≤ h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) := by
  obtain ⟨YB, hYB, hYB₀⟩ :=
    exists_ODESolution_clm hF hB hcont (modeProd fun i => P₀ i + Pa i)
      (show t₀ ≤ t₁ by linarith) Y₀
  exact hs.local_error_le hF hL hB hLt hFt ht₁ hh hhH hA hA₀ hYB hYB₀

end IsParTuckerBUGStep

/-- **Robust global error bound of the parallel Tucker BUG integrator** (Ceruti–Kusch–Lubich–Sulz,
[CerutiEtAl2024, Thm. 3.1], explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`),
bounded by `B` and `Lₜ`-Lipschitz in time, `tₙ = t₀ + n h` with `0 ≤ h ≤ H`, and `A` the exact
solution on `[t₀, t₀ + N h]`.  For `n < N` let step `n` be a parallel Tucker BUG step
(`IsParTuckerBUGStep`) from `(tₙ, Y n)` followed by a truncation with
`‖Y (n+1) - Ŷₙ₊₁‖ ≤ ϑ`, let `YB n` be the comparison rank-adaptive Galerkin trajectories and
`Φ n` the exact flows started at `Y n`.  Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (c₁ ε + c₂ h) + n ϑ),

with `c₁ = parTuckerC₁ d L H`, `c₂ = parTuckerC₂ d L B Lₜ H`, independent of singular values of
matricizations of the core tensors. -/
theorem par_tucker_global_error {F : ℝ → E → E} {L B ε Lt : ℝ} {d : ℕ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Q P Pa : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E}
    {YC YB Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParTuckerBUGStep F ε (Q n) (P n) (Pa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YC n))
    (hYB : ∀ n < N, ODESolution (fun t x => modeProd (fun i => P n i + Pa n i) (F t x)) (YB n)
      (t₀ + n * h) (t₀ + (n + 1) * h))
    (hYB₀ : ∀ n < N, YB n (t₀ + n * h) = Y n) {ϑ : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - parTuckerBUG (P n) (Pa n) (YC n (t₀ + (n + 1) * h)) h
      (F (t₀ + n * h) (Y n))‖ ≤ ϑ)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) + n * ϑ) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) + ϑ := by
    intro n hn
    have h1 := (hstep n hn).local_error_le hF hL hB hLt
      (fun t ht => hFt _ _ _ ht.1) (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn) (hYB n hn) (hYB₀ n hn)
    calc _ ≤ ‖Y (n + 1) - parTuckerBUG (P n) (Pa n) (YC n (t₀ + (n + 1) * h)) h
            (F (t₀ + n * h) (Y n))‖ + ‖parTuckerBUG (P n) (Pa n) (YC n (t₀ + (n + 1) * h)) h
            (F (t₀ + n * h) (Y n)) - Φ n (t₀ + (n + 1) * h)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith [htr n hn]
  intro n hn
  calc _ ≤ _ := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
    _ = _ := by ring

/-- **Robust global error bound of the parallel Tucker BUG integrator, final form**
([CerutiEtAl2024, Thm. 3.1]: `‖Yₖ - A(tₖ)‖ ≤ c₁ h + c₂ ε + c₃ δ + c₄ k ϑ`).  On a Banach space,
for `F` continuous in time, `ε ≥ 0`, `‖Y 0 - A t₀‖ ≤ δ` and `n h ≤ T`, under the hypotheses of
`par_tucker_global_error` (the comparison trajectories are constructed internally):

    ‖Y n - A tₙ‖ ≤ e^{L T} δ + T e^{L T} c₁ ε + T e^{L T} c₂ h + e^{L T} n ϑ,

with `c₁ = parTuckerC₁ d L H`, `c₂ = parTuckerC₂ d L B Lₜ H` depending only on `d`, `L`, `B`,
`Lₜ` and `H`. -/
theorem par_tucker_global_error_le [CompleteSpace E] {F : ℝ → E → E} {L B ε Lt : ℝ} {d : ℕ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (hε : 0 ≤ ε) (hLt : 0 ≤ Lt)
    (hFt : ∀ s t x, s ≤ t → ‖F t x - F s x‖ ≤ Lt * (t - s)) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Q P Pa : ℕ → Fin d → E →L[ℝ] E} {Y : ℕ → E} {YK : ℕ → Fin d → ℝ → E} {YC Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsParTuckerBUGStep F ε (Q n) (P n) (Pa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YC n)) {ϑ : ℝ}
    (htr : ∀ n < N, ‖Y (n + 1) - parTuckerBUG (P n) (Pa n) (YC n (t₀ + (n + 1) * h)) h
      (F (t₀ + n * h) (Y n))‖ ≤ ϑ)
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * parTuckerC₁ d L H * ε
        + T * Real.exp (L * T) * parTuckerC₂ d L B Lt H * h + Real.exp (L * T) * (n * ϑ) := by
  have hle : ∀ n : ℕ, t₀ + n * h ≤ t₀ + (n + 1) * h := fun n => by nlinarith
  have hex : ∀ n : ℕ, ∃ y : ℝ → E, ODESolution
      (fun t x => modeProd (fun i => P n i + Pa n i) (F t x)) y (t₀ + n * h) (t₀ + (n + 1) * h)
      ∧ y (t₀ + n * h) = Y n := fun n =>
    exists_ODESolution_clm hF hB hcont _ (hle n) (Y n)
  choose YB hYB hYB₀ using hex
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h :=
    add_nonneg (mul_nonneg (parTuckerC₁_nonneg d hL hH) hε)
      (mul_nonneg (parTuckerC₂_nonneg d hL hB.nonneg hLt hH) hh)
  have hnϑ : 0 ≤ (n : ℝ) * ϑ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (htr 0 (by omega)))
  have h1 := par_tucker_global_error hF hL hB hLt hFt hh hhH hA hstep (fun n _ => hYB n)
    (fun n _ => hYB₀ n) htr hΦ hΦ₀ n hn
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hTg := mul_le_mul_of_nonneg_right hT hg
  have hng := mul_nonneg hnh hg
  have hin : ‖Y 0 - A t₀‖ + n * h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h)
        + n * ϑ
      ≤ δ + T * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) + n * ϑ := by linarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖
      + n * h * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) + n * ϑ := by
    have := norm_nonneg (Y 0 - A t₀)
    linarith
  calc _ ≤ _ := h1
    _ ≤ Real.exp (L * T)
          * (δ + T * (parTuckerC₁ d L H * ε + parTuckerC₂ d L B Lt H * h) + n * ϑ) :=
        mul_le_mul hexp hin hin0 (Real.exp_pos _).le
    _ = _ := by ring

end ParallelTucker

/-! ### Satisfiability of the hypotheses -/

/-- The hypotheses of one Tucker BUG step with three modes are jointly satisfiable with a nonzero
vector field: on `ℝ`, `F(t, y) = 1`, all projectors the identity, all trajectories `t ↦ t` on
`[0, 1]`, `ε = 0`.  (The augmented version also holds since the identity fixes `Y₀ = 0`.) -/
example : IsAugTuckerBUGStep (E := ℝ) (d := 3) (fun _ _ => 1) 0 (fun _ => 1) (fun _ => 1) 0 1 0
    (fun _ t => t) (fun t => t) where
  projQ₀ _ := IsOrthProj.one
  projP₁ _ := IsOrthProj.one
  comm₁ _ _ _ := rfl
  kSol _ := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart _ := rfl
  kCap _ := rfl
  kNormal _ _ _ := by simp
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_apply_eq_self]) _ _
  sStart := by simp [modeProd_apply_eq_self]
  augment _ := rfl

/-- The hypotheses of `tucker_global_error` are jointly satisfiable: on `ℝ` with `F(t, y) = 1`
(`L = 0`, `B = 1`), `d = 3` modes, step size `h = 1`, five steps, exact solution `A t = t`,
numerical values `Y n = n`, all projectors the identity, and all substep trajectories and exact
flows `t ↦ t`. -/
example : ∀ n ≤ 5, ‖((n : ℕ) : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * (n * 1)) *
    (‖((0 : ℕ) : ℝ) - 0‖ + n * 1 * (tuckerC₁ 3 0 1 * 0 + tuckerC₂ 3 0 1 1 * 1)) :=
  tucker_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0) (d := 3)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (t₀ := 0) (h := 1) (H := 1) zero_le_one
    le_rfl (N := 5) (A := fun t => t)
    (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) (Q := fun _ _ => 1) (P := fun _ _ => 1)
    (Y := fun n => (n : ℝ)) (YK := fun _ _ t => t) (YS := fun _ t => t) (Φ := fun _ t => t)
    (fun n _ => {
      projQ₀ := fun _ => IsOrthProj.one
      projP₁ := fun _ => IsOrthProj.one
      comm₁ := fun _ _ _ => rfl
      kSol := fun _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      kStart := fun _ => by simp
      kCap := fun _ => rfl
      kNormal := fun _ _ _ => by simp
      sSol := odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_apply_eq_self]) _ _
      sStart := by simp [modeProd_apply_eq_self] })
    (fun n _ => by simp)
    (fun _ _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _)
    (fun n _ => by simp)

/-- A nondegenerate instance of the Tucker local error bound with non-identity projectors and a
nonzero local error: on `ℝ` with `F(t, y) = 1` (`L = 0`, `B = 1`) and `d = 2` modes, take the
co-range projectors `![0, 1]` and the new mode projectors `![0, 1]`, so that the mode-0 K-step is
frozen at `Y₀ = 0` and the core-step projector `0 * 1 = 0` discards everything.  The
doubly-normal component of mode 0 is `1`, so `ε = 1`.  The local error `‖0 - A 1‖ = 1` is
consistent with the bound `(e⁰ - 1)(B h + 2ϑ) + 2ϑ = 2`, `ϑ = 1`. -/
example : ‖(0 : ℝ) - 1‖ ≤ (Real.exp (0 * 1) - 1)
      * (1 * 1 + ((2 : ℕ) : ℝ) * (1 * (4 * 0 * 1 * 1 + 1)))
      + ((2 : ℕ) : ℝ) * (1 * (4 * 0 * 1 * 1 + 1)) :=
  (show IsTuckerBUGStep (E := ℝ) (d := 2) (fun _ _ => 1) 1 ![0, 1] ![0, 1] 0 1 0
      ![fun _ => 0, fun t => t] (fun _ => 0) from {
    projQ₀ := Fin.forall_fin_two.2 ⟨IsOrthProj.zero, IsOrthProj.one⟩
    projP₁ := Fin.forall_fin_two.2 ⟨IsOrthProj.zero, IsOrthProj.one⟩
    comm₁ := Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun _ => rfl, fun _ => by simp⟩,
      Fin.forall_fin_two.2 ⟨fun _ => by simp, fun _ => rfl⟩⟩
    kSol := Fin.forall_fin_two.2
      ⟨⟨continuousOn_const, fun t _ => (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_deriv
        (by simp)⟩, odeSolution_id_of_eq_one (fun _ _ => by simp) _ _⟩
    kStart := Fin.forall_fin_two.2 ⟨rfl, rfl⟩
    kCap := Fin.forall_fin_two.2 ⟨by simp, by simp⟩
    kNormal := Fin.forall_fin_two.2 ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    sSol := ⟨continuousOn_const, fun t _ =>
      (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_deriv (by simp)⟩
    sStart := by simp }).local_error (A := fun t => t) (L := 0) (B := 1) (h := 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (by norm_num) zero_le_one
    (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) rfl

/-- A nondegenerate instance of the parallel Tucker BUG step on `ℝ` with `d = 2` modes: rank-zero
start `Y₀ = 0` (`P₀ = ![0, 0]`), new directions `Pa = ![1, 1]`, `F(t, y) = 1` (`L = 0`, `B = 1`,
`Lₜ = 0`), `ε = 1`.  The core step is frozen at `0` and both single-new-mode blocks vanish, so the
parallel result is `Ŷ₁ = 0` (the whole update lies in the doubly-new block `Pa 0 Pa 1`, which the
parallel integrator sets to zero), while the rank-adaptive comparison trajectory and the exact
solution are `t ↦ t`.  The local error `‖Ŷ₁ - A 1‖ = 1` is consistent with the bound `3`. -/
example : ‖parTuckerBUG (E := ℝ) ![0, 0] ![1, 1] 0 1 1 - 1‖ ≤ 3 := by
  have hs : IsParTuckerBUGStep (E := ℝ) (d := 2) (fun _ _ => 1) 1 ![1, 1] ![0, 0] ![1, 1] 0 1 0
      (fun _ t => t) (fun _ => 0) :=
    { projQ₀ := Fin.forall_fin_two.2 ⟨IsOrthProj.one, IsOrthProj.one⟩
      projP₀ := Fin.forall_fin_two.2 ⟨IsOrthProj.zero, IsOrthProj.zero⟩
      projPa := Fin.forall_fin_two.2 ⟨IsOrthProj.one, IsOrthProj.one⟩
      orth := fun i x => by fin_cases i <;> simp
      comm₀₀ := fun i j x => by fin_cases i <;> fin_cases j <;> simp
      comm₀a := fun i j x => by fin_cases i <;> fin_cases j <;> simp
      commaa := fun i j x => by fin_cases i <;> fin_cases j <;> simp
      start₀ := fun i => by fin_cases i <;> simp
      kSol := fun i => odeSolution_id_of_eq_one (fun _ _ => by fin_cases i <;> simp) _ _
      kStart := fun _ => rfl
      kCap := fun i => by fin_cases i <;> simp
      kNormal := fun i _ _ => by fin_cases i <;> simp
      cSol := ⟨continuousOn_const, fun t _ =>
        (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_deriv (by simp [modeProd_succ])⟩
      cStart := rfl
      normal₀ := by simp [modeProdLeOne_succ, modeProd_succ] }
  have h := hs.local_error (L := 0) (B := 1) (Lt := 0) (h := 1) (A := fun t => t)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) le_rfl (fun _ _ => by simp)
    (by norm_num) zero_le_one (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) rfl
    (YB := fun t => t) (odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_succ]) _ _) rfl
  norm_num at h
  exact h

/-- In the example above the parallel result is indeed `Ŷ₁ = 0`, so the local error is `1`. -/
example : parTuckerBUG (E := ℝ) ![0, 0] ![1, 1] 0 1 1 = 0 := by
  simp [parTuckerBUG, modeProdLeOne_succ, modeProd_succ]

/-- The hypotheses of `par_tucker_global_error` are jointly satisfiable: on `ℝ` with `F(t, y) = 1`
(`L = 0`, `B = 1`, `Lₜ = 0`), `d = 2` modes, step size `h = 1`, five steps, exact solution
`A t = t`, numerical values `Y n = n`, old mode projectors the identity, no new directions,
no truncation (`ϑ = 0`), and all substep trajectories and exact flows `t ↦ t`. -/
example : ∀ n ≤ 5, ‖((n : ℕ) : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * (n * 1)) *
    (‖((0 : ℕ) : ℝ) - 0‖ + n * 1 * (parTuckerC₁ 2 0 1 * 0 + parTuckerC₂ 2 0 1 0 1 * 1)
      + n * 0) :=
  par_tucker_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0) (Lt := 0)
    (d := 2) (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) le_rfl (fun _ _ _ _ => by simp)
    (t₀ := 0) (h := 1) (H := 1) zero_le_one le_rfl (N := 5) (A := fun t => t)
    (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) (Q := fun _ _ => 1) (P := fun _ _ => 1)
    (Pa := fun _ _ => 0) (Y := fun n => (n : ℝ)) (YK := fun _ _ t => t) (YC := fun _ t => t)
    (YB := fun _ t => t) (Φ := fun _ t => t)
    (fun n _ => {
      projQ₀ := fun _ => IsOrthProj.one
      projP₀ := fun _ => IsOrthProj.one
      projPa := fun _ => IsOrthProj.zero
      orth := fun _ _ => by simp
      comm₀₀ := fun _ _ _ => rfl
      comm₀a := fun _ _ _ => by simp
      commaa := fun _ _ _ => rfl
      start₀ := fun _ => rfl
      kSol := fun _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      kStart := fun _ => by simp
      kCap := fun _ => by simp
      kNormal := fun _ _ _ => by simp
      cSol := odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_succ]) _ _
      cStart := by simp
      normal₀ := by simp [modeProdLeOne_succ, modeProd_succ] })
    (fun _ _ => odeSolution_id_of_eq_one (fun _ _ => by simp [modeProd_succ]) _ _)
    (fun n _ => by simp) (ϑ := 0)
    (fun n _ => by simp [parTuckerBUG, modeProdLeOne_succ, modeProd_succ])
    (fun _ _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _) (fun n _ => by simp)


end LeanDLRA
