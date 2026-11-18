import LeanDLRA.Tensor.Tucker.ProjectorLipschitz

/-!
# The Lipschitz constant of the tangent projector of the Tucker manifold is larger than one

For matrices of fixed rank the tangent projector satisfies `‖P(Y) B - P(X) B‖ ≤ ρ⁻¹ ‖Y - X‖ ‖B‖`
with the constant `1` (`norm_tangentProjAt_sub_le_inv_mul`). This file shows that the constant
`1` is not valid for Tucker tensors with three modes: there are tensors `X`, `Y` of multilinear
rank `(1, 1, 1)` in `ℝ^{2 × 2 × 2}` and a tensor `B` with

  `23/20 · ρ⁻¹ ‖Y - X‖ ‖B‖ ≤ ‖P(Y) B - P(X) B‖`,

where `ρ = 1` is the smallest nonzero singular value of the matricizations of `X`. So every
constant `c` in a bound `‖P(Y) B - P(X) B‖ ≤ c ρ⁻¹ ‖Y - X‖ ‖B‖` for three modes satisfies
`c ≥ 23/20`; `norm_tuckerTangentProj_sub_le` has `c = √3`. The same data show that the hypotheses
of `norm_tuckerTangentProj_sub_le` hold in a case with three modes in which the two tangent
projectors differ.

The example is `X = e₁ ⊗ e₁ ⊗ e₁`, `Y = v ⊗ v ⊗ v` with the unit vector `v = (840/841, 41/841)`,
and `B = e₂ ⊗ e₁ ⊗ e₁ + e₁ ⊗ e₂ ⊗ e₁ + e₁ ⊗ e₁ ⊗ e₂`, a tangent vector at `X`. With the unit
vector `w = (-41/841, 840/841) ⊥ v` the tensor `N = v ⊗ w ⊗ w + w ⊗ v ⊗ w + w ⊗ w ⊗ v` is normal
at `Y`, so that `‖P(Y) B - B‖ ‖N‖ ≥ |⟪B, N⟫|`. For the angle `θ` between `e₁` and `v` the quotient
`|⟪B, N⟫| / (‖Y - X‖ ‖B‖ ‖N‖)` tends to `2/√3` as `θ → 0`, the norm of the second fundamental
form of the manifold of tensors of rank one with three modes at a tensor of norm one.

## Main results

* `LeanDLRA.Tensor.tucker_apply_of_unique`, `LeanDLRA.Tensor.inner_tucker_tucker_of_unique`:
  entries and inner products of Tucker tensors with a core with one entry (elementary tensors).
* `LeanDLRA.Tensor.tuckerTangentProj_tucker_eq_zero`: a multilinear product `Cm ×ₖ Mₖ` whose
  bases are orthogonal to the bases of `X` in two modes is normal at `X`.
* `LeanDLRA.Tensor.exists_mul_le_norm_tuckerTangentProj_sub`: the lower bound `23/20`.

## References

* [BachmayrEisenmannUschmajew2025, Props. 4.2 and 4.7]
-/

open Matrix
open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA

namespace Tensor

/-! ### Elementary tensors and normal vectors -/

/-- **The entries of a Tucker tensor with a core with one entry**:
`(C ×ₖ Uₖ)(x) = (∏ₖ Uₖ(xₖ)) C`. -/
theorem tucker_apply_of_unique {d : ℕ} {ι ρ : Fin d → Type*} [∀ k, Fintype (ρ k)]
    [∀ k, Unique (ρ k)] (C : Tensor ρ) (U : ∀ k, Matrix (ι k) (ρ k) ℝ) (x : ∀ k, ι k) :
    tucker C U x = (∏ k, U k (x k) default) * C default := by
  rw [tucker_apply, Fintype.sum_unique]
  rfl

/-- **The inner product of two elementary tensors** is the product of the inner products of
their factors: `⟪C ×ₖ Uₖ, C' ×ₖ Vₖ⟫ = C C' ∏ₖ Uₖᵀ Vₖ` for cores with one entry. -/
theorem inner_tucker_tucker_of_unique {d : ℕ} {ι ρ : Fin d → Type*} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ρ k)] [∀ k, Unique (ρ k)] (C C' : Tensor ρ)
    (U V : ∀ k, Matrix (ι k) (ρ k) ℝ) :
    ⟪tucker C U, tucker C' V⟫ =
      C default * C' default * ∏ k, ((U k)ᵀ * V k) default default := by
  rw [inner_tucker_left, tucker_tucker, inner_eq_sum, Fintype.sum_unique, tucker_apply_of_unique]
  change C default * ((∏ k, ((U k)ᵀ * V k) default default) * C' default) = _
  ring

/-- **Multilinear products orthogonal to the bases in two modes are normal.** Let
`X = C ×ₖ Uₖ` with orthonormal `Uₖ` and co-range bases `W` as in
`tuckerTangentProj_eq_starProjection`. If `Uᵢᵀ Mᵢ = 0` and `Uⱼᵀ Mⱼ = 0` for two modes `i ≠ j`,
then the tangent projector at `X` vanishes on `Cm ×ₖ Mₖ` for every core `Cm`. -/
theorem tuckerTangentProj_tucker_eq_zero {d : ℕ} {ι r s ρ : Fin d → Type*} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (r k)] [∀ k, DecidableEq (r k)] [∀ k, Fintype (s k)] [∀ k, Fintype (ρ k)]
    {U : ∀ k, Matrix (ι k) (r k) ℝ} {C : Tensor r}
    {W : ∀ k, Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (s k) ℝ} (hU : ∀ k, (U k)ᵀ * U k = 1)
    (hWX : ∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U)
    (hWB : ∀ k, ∃ B : Matrix _ (s k) ℝ, W k = unfold (· ≠ k) (tucker C U) * B)
    (Cm : Tensor ρ) (M : ∀ k, Matrix (ι k) (ρ k) ℝ) {i j : Fin d} (hij : i ≠ j)
    (hi : (U i)ᵀ * M i = 0) (hj : (U j)ᵀ * M j = 0) :
    tuckerTangentProj U 1 W (tucker Cm M) = 0 := by
  rw [tuckerTangentProj_eq_starProjection hU IsOrthProj.one hWX hWB,
    Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨Cdot, -, Udot, -, rfl⟩ := hξ
    have e1 : ⟪tucker Cdot U, tucker Cm M⟫ = 0 := by
      rw [inner_tucker_left, tucker_tucker]
      exact (congrArg (fun T => ⟪Cdot, T⟫)
        (tucker_eq_zero_of (U := fun k => (U k)ᵀ * M k) (k := i) hi Cm)).trans
        (inner_zero_right _)
    have e2 : ∀ k, ⟪tucker C (Function.update U k (Udot k)), tucker Cm M⟫ = 0 := fun k => by
      obtain ⟨l, hlk, hl⟩ : ∃ l, l ≠ k ∧ (U l)ᵀ * M l = 0 := by
        by_cases hk : i = k
        · exact ⟨j, fun h => hij (hk.trans h.symm), hj⟩
        · exact ⟨i, hk, hi⟩
      have hl' : (Function.update U k (Udot k) l)ᵀ * M l = 0 := by
        rw [Function.update_of_ne hlk]
        exact hl
      rw [inner_tucker_left, tucker_tucker]
      exact (congrArg (fun T => ⟪C, T⟫)
        (tucker_eq_zero_of (U := fun k' => (Function.update U k (Udot k) k')ᵀ * M k') (k := l)
          hl' Cm)).trans (inner_zero_right _)
    rw [inner_add_left, sum_inner, e1, Finset.sum_eq_zero fun k _ => e2 k, add_zero]
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]

namespace TuckerProjectorLowerBoundExamples

/-! ### Tensors of rank one: the hypotheses of the Lipschitz bound -/

/-- The core with the single entry `c`. -/
private def core {d : ℕ} (c : ℝ) : Tensor fun _ : Fin d => Fin 1 := WithLp.toLp 2 fun _ => c

/-- The co-range basis of the elementary tensor `⊗ₖ uₖ` in mode `k`: the column `⊗_{j ≠ k} uⱼ`. -/
private def coW {d : ℕ} {ι : Fin d → Type*} (u : ∀ k, Matrix (ι k) (Fin 1) ℝ) (k : Fin d) :
    Matrix (∀ j : {j : Fin d // j ≠ k}, ι j) (Fin 1) ℝ :=
  Matrix.of fun a _ => ∏ j : {j : Fin d // j ≠ k}, u j (a j) 0

/-- The row `c uₖᵀ`, indexed by the multi-indices of the complement of the modes `≠ k`. -/
private def coR {d : ℕ} {ι : Fin d → Type*} (u : ∀ k, Matrix (ι k) (Fin 1) ℝ) (c : ℝ)
    (k : Fin d) : Matrix (Fin 1) (∀ j : {j : Fin d // ¬ j ≠ k}, ι j) ℝ :=
  Matrix.of fun _ b => c * u k (compEquiv k b) 0

/-- The entries of a unit column have the sum of squares one. -/
private theorem sum_mul_self_eq_one {m : Type*} [Fintype m] {w : Matrix m (Fin 1) ℝ}
    (h : wᵀ * w = 1) : ∑ i, w i 0 * w i 0 = 1 := by
  have := congrFun (congrFun h 0) 0
  simpa [Matrix.mul_apply] using this

/-- A unit column has the Frobenius norm one. -/
private theorem norm_col_eq_one {m : Type*} [Fintype m] {w : Matrix m (Fin 1) ℝ}
    (h : wᵀ * w = 1) : ‖w‖ = 1 := by
  have h2 : ‖w‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    exact (Finset.sum_congr rfl fun i _ => by rw [Fin.sum_univ_one, sq]).trans
      (sum_mul_self_eq_one h)
  exact (sq_eq_sq₀ (norm_nonneg w) zero_le_one).1 (h2.trans (one_pow 2).symm)

/-- The co-range basis of an elementary tensor of unit vectors is a unit column. -/
private theorem coW_transpose_mul_self {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]
    {u : ∀ k, Matrix (ι k) (Fin 1) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1) (k : Fin d) :
    (coW u k)ᵀ * coW u k = 1 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  simp only [Matrix.transpose_apply, coW, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : {j : Fin d // j ≠ k}) c => u j c 0 * u j c 0)]
  exact Finset.prod_eq_one fun j _ => sum_mul_self_eq_one (hu j)

/-- The rows `c uₖᵀ` and `c' uₖᵀ` have the inner product `c c'`. -/
private theorem coR_mul_transpose {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]
    {u : ∀ k, Matrix (ι k) (Fin 1) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1) (c c' : ℝ) (k : Fin d) :
    coR u c k * (coR u c' k)ᵀ = (c * c') • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  calc ∑ b, coR u c k 0 b * (coR u c' k)ᵀ b 0
      = ∑ a, c * c' * (u k a 0 * u k a 0) :=
        Fintype.sum_equiv (compEquiv k) _ _ fun b => by
          simp only [Matrix.transpose_apply, coR, Matrix.of_apply]
          ring
    _ = c * c' := by rw [← Finset.mul_sum, sum_mul_self_eq_one (hu k), mul_one]

/-- The unfolding of an elementary tensor with respect to the modes `≠ k` is the product of the
column `⊗_{j ≠ k} uⱼ` and the row `c uₖᵀ`. -/
private theorem unfold_tucker_core {d : ℕ} {ι : Fin d → Type*}
    (u : ∀ k, Matrix (ι k) (Fin 1) ℝ) (c : ℝ) (k : Fin d) :
    unfold (· ≠ k) (tucker (core c) u) = coW u k * coR u c k := by
  ext a b
  have hk : merge (· ≠ k) a b k = compEquiv k b := by simp [merge, compEquiv]
  have hj : ∀ j : {j : Fin d // j ≠ k}, merge (· ≠ k) a b j = a j := fun j => by
    simp [merge, j.2]
  have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun j : Fin d => j ≠ k)
    (fun j => u j (merge (· ≠ k) a b j) 0)
  have huniq : ∏ i : {x : Fin d // ¬ x ≠ k}, u i (merge (· ≠ k) a b i) 0 =
      u k (compEquiv k b) 0 := by
    rw [Fintype.prod_eq_single ⟨k, not_not.2 rfl⟩ fun x hx =>
      absurd (Subtype.ext (not_not.1 x.2)) hx]
    exact congrArg (fun t => u k t 0) hk
  have hfirst : ∏ i : {x : Fin d // x ≠ k}, u i (merge (· ≠ k) a b i) 0 =
      ∏ i : {x : Fin d // x ≠ k}, u i (a i) 0 :=
    Finset.prod_congr rfl fun j _ => by rw [hj j]
  rw [unfold_apply, tucker_apply_of_unique, Matrix.mul_apply, Fin.sum_univ_one]
  change (∏ j, u j (merge (· ≠ k) a b j) 0) * c =
    (∏ j : {j : Fin d // j ≠ k}, u j (a j) 0) * (c * u k (compEquiv k b) 0)
  rw [← hsplit, huniq, hfirst]
  ring

/-- The co-range projector of an elementary tensor of unit vectors fixes the tensor. -/
private theorem actOn_coW {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]
    {u : ∀ k, Matrix (ι k) (Fin 1) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1) (c : ℝ) (k : Fin d) :
    actOn (· ≠ k) (coW u k * (coW u k)ᵀ) (tucker (core c) u) = tucker (core c) u := by
  refine unfold_injective (· ≠ k) ?_
  rw [unfold_actOn, unfold_tucker_core, Matrix.mul_assoc,
    ← Matrix.mul_assoc (coW u k)ᵀ (coW u k) (coR u c k), coW_transpose_mul_self hu,
    Matrix.one_mul]

/-- The co-range basis of an elementary tensor `c ⊗ₖ uₖ`, `c ≠ 0`, lies in the column space of
the unfolding. -/
private theorem coW_eq_unfold_mul {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]
    {u : ∀ k, Matrix (ι k) (Fin 1) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1) {c : ℝ} (hc : c ≠ 0)
    (k : Fin d) :
    ∃ B : Matrix (∀ j : {j : Fin d // ¬ j ≠ k}, ι j) (Fin 1) ℝ,
      coW u k = unfold (· ≠ k) (tucker (core c) u) * B := by
  refine ⟨(coR u c⁻¹ k)ᵀ, ?_⟩
  rw [unfold_tucker_core, Matrix.mul_assoc, coR_mul_transpose hu, mul_inv_cancel₀ hc, one_smul,
    Matrix.mul_one]

/-- The unfoldings of an elementary tensor `c ⊗ₖ uₖ`, `c ≠ 0`, have rank one. -/
private theorem rank_unfold_tucker_core {d : ℕ} {ι : Fin d → Type*} [∀ k, Fintype (ι k)]
    {u : ∀ k, Matrix (ι k) (Fin 1) ℝ} (hu : ∀ k, (u k)ᵀ * u k = 1) {c : ℝ} (hc : c ≠ 0)
    (k : Fin d) : (unfold (· ≠ k) (tucker (core c) u)).rank = Fintype.card (Fin 1) := by
  obtain ⟨B, hB⟩ := coW_eq_unfold_mul hu hc k
  refine le_antisymm ?_ ?_
  · rw [unfold_tucker_core]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  · calc Fintype.card (Fin 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ).rank := rank_one.symm
      _ = ((coW u k)ᵀ * coW u k).rank := by rw [coW_transpose_mul_self hu]
      _ ≤ (coW u k).rank := rank_mul_le_right _ _
      _ = (unfold (· ≠ k) (tucker (core c) u) * B).rank := by rw [← hB]
      _ ≤ _ := rank_mul_le_left _ _

/-- The largest singular value of the unfoldings of an elementary tensor `c ⊗ₖ uₖ` of unit
vectors, `c ≥ 0`, is at least `c`. -/
private theorem le_singularValues_unfold_tucker_core {d : ℕ} {ι : Fin d → Type*}
    [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)] {u : ∀ k, Matrix (ι k) (Fin 1) ℝ}
    (hu : ∀ k, (u k)ᵀ * u k = 1) {c : ℝ} (hc : 0 ≤ c) (k : Fin d) :
    c ≤ (toEuclideanLin (unfold (· ≠ k) (tucker (core c) u))).singularValues
      (Fintype.card (Fin 1) - 1) := by
  have hB : ((coR u 1 k)ᵀ)ᵀ * (coR u 1 k)ᵀ = 1 := by
    rw [Matrix.transpose_transpose, coR_mul_transpose hu, mul_one, one_smul]
  have h := Curvature.frob_mul_le (coW u k * coR u c k) (coR u 1 k)ᵀ
  rw [Matrix.mul_assoc, coR_mul_transpose hu, mul_one, Matrix.mul_smul, Matrix.mul_one,
    norm_smul, Real.norm_of_nonneg hc, norm_col_eq_one (coW_transpose_mul_self hu k),
    norm_col_eq_one hB, mul_one, mul_one] at h
  rwa [show Fintype.card (Fin 1) - 1 = 0 by simp,
    ← EckartYoung.specNorm_eq_singularValues_zero, unfold_tucker_core]


/-! ### The example with three modes -/

/-- The first unit column of `ℝ²`. -/
local notation "e₁" => (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The second unit column of `ℝ²`. -/
local notation "e₂" => (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The unit column `v = (840/841, 41/841)ᵀ` of `ℝ²`. -/
local notation "vθ" => (!![840 / 841; 41 / 841] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The unit column `w = (-41/841, 840/841)ᵀ ⊥ v` of `ℝ²`. -/
local notation "wθ" => (!![-41 / 841; 840 / 841] : Matrix (Fin 2) (Fin 1) ℝ)

/-- The inner product of two columns of `ℝ²`. -/
private def dot (a b : Matrix (Fin 2) (Fin 1) ℝ) : ℝ := a 0 0 * b 0 0 + a 1 0 * b 1 0

/-- The elementary tensor `a ⊗ b ⊗ c` in `ℝ^{2 × 2 × 2}`. -/
private def pt (a b c : Matrix (Fin 2) (Fin 1) ℝ) : Tensor fun _ : Fin 3 => Fin 2 :=
  tucker (core 1) ![a, b, c]

private theorem transpose_mul_apply (a b : Matrix (Fin 2) (Fin 1) ℝ) :
    (aᵀ * b) 0 0 = dot a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, dot]

private theorem transpose_mul_eq_zero {a b : Matrix (Fin 2) (Fin 1) ℝ} (h : dot a b = 0) :
    aᵀ * b = 0 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [transpose_mul_apply, h, Matrix.zero_apply]

private theorem transpose_mul_eq_one {a : Matrix (Fin 2) (Fin 1) ℝ} (h : dot a a = 1) :
    aᵀ * a = 1 := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [transpose_mul_apply, h, Matrix.one_apply_eq]

/-- The inner product of two elementary tensors with three modes. -/
private theorem inner_pt (a b c a' b' c' : Matrix (Fin 2) (Fin 1) ℝ) :
    ⟪pt a b c, pt a' b' c'⟫ = dot a a' * dot b b' * dot c c' := by
  rw [pt, pt, inner_tucker_tucker_of_unique, Fin.prod_univ_three]
  change (1 : ℝ) * 1 * ((aᵀ * a') 0 0 * (bᵀ * b') 0 0 * (cᵀ * c') 0 0) = _
  rw [transpose_mul_apply, transpose_mul_apply, transpose_mul_apply]
  ring

private theorem const_eq (a : Matrix (Fin 2) (Fin 1) ℝ) :
    (fun _ : Fin 3 => a) = ![a, a, a] := by
  funext l
  fin_cases l <;> rfl

private theorem update_zero (a b : Matrix (Fin 2) (Fin 1) ℝ) :
    Function.update (fun _ : Fin 3 => a) 0 b = ![b, a, a] := by
  funext l
  fin_cases l <;> rfl

private theorem update_one (a b : Matrix (Fin 2) (Fin 1) ℝ) :
    Function.update (fun _ : Fin 3 => a) 1 b = ![a, b, a] := by
  funext l
  fin_cases l <;> rfl

private theorem update_two (a b : Matrix (Fin 2) (Fin 1) ℝ) :
    Function.update (fun _ : Fin 3 => a) 2 b = ![a, a, b] := by
  funext l
  fin_cases l <;> rfl

private theorem he₁ : ∀ _ : Fin 3, e₁ᵀ * e₁ = 1 := fun _ =>
  transpose_mul_eq_one (by norm_num [dot])

private theorem hvθ : ∀ _ : Fin 3, vθᵀ * vθ = 1 := fun _ =>
  transpose_mul_eq_one (by norm_num [dot])

/-- The tangent vector `B = e₂ ⊗ e₁ ⊗ e₁ + e₁ ⊗ e₂ ⊗ e₁ + e₁ ⊗ e₁ ⊗ e₂` at `X`, in the form of the
generators of the tangent space. -/
private def tanB : Tensor fun _ : Fin 3 => Fin 2 :=
  tucker (0 : Tensor fun _ : Fin 3 => Fin 1) (fun _ : Fin 3 => e₁) +
    ∑ k : Fin 3, tucker (core 1) (Function.update (fun _ : Fin 3 => e₁) k e₂)

/-- The normal vector `N = v ⊗ w ⊗ w + w ⊗ v ⊗ w + w ⊗ w ⊗ v` at `Y`. -/
private noncomputable def nrmN : Tensor fun _ : Fin 3 => Fin 2 :=
  pt vθ wθ wθ + pt wθ vθ wθ + pt wθ wθ vθ

private theorem tanB_eq : tanB = pt e₂ e₁ e₁ + pt e₁ e₂ e₁ + pt e₁ e₁ e₂ := by
  have h0 : tucker (0 : Tensor fun _ : Fin 3 => Fin 1) (fun _ : Fin 3 => e₁) = 0 :=
    (tuckerCLM (fun _ : Fin 3 => e₁)).map_zero
  rw [tanB, h0, zero_add, Fin.sum_univ_three, update_zero, update_one, update_two]
  rfl

/-- `B` is tangent at `X`. -/
private theorem tuckerTangentProj_tanB :
    tuckerTangentProj (fun _ : Fin 3 => e₁) 1 (coW fun _ : Fin 3 => e₁) tanB = tanB :=
  (tuckerTangentProj_eq_self_iff he₁ IsOrthProj.one (actOn_coW he₁ 1)
    (coW_eq_unfold_mul he₁ one_ne_zero) tanB).2
    (Submodule.subset_span ⟨0, map_zero _, fun _ => e₂,
      fun _ => transpose_mul_eq_zero (by norm_num [dot]), rfl⟩)

/-- `N` is normal at `Y`. -/
private theorem tuckerTangentProj_nrmN :
    tuckerTangentProj (fun _ : Fin 3 => vθ) 1 (coW fun _ : Fin 3 => vθ) nrmN = 0 := by
  have hvw : vθᵀ * wθ = 0 := transpose_mul_eq_zero (by norm_num [dot])
  have h := fun (M : ∀ _ : Fin 3, Matrix (Fin 2) (Fin 1) ℝ) (i j : Fin 3) (hij : i ≠ j)
      (hi : vθᵀ * M i = 0) (hj : vθᵀ * M j = 0) =>
    tuckerTangentProj_tucker_eq_zero (C := core 1) hvθ (actOn_coW hvθ 1)
      (coW_eq_unfold_mul hvθ one_ne_zero) (core 1) M hij hi hj
  rw [nrmN, map_add, map_add, pt, pt, pt, h ![vθ, wθ, wθ] 1 2 (by decide) hvw hvw,
    h ![wθ, vθ, wθ] 0 2 (by decide) hvw hvw, h ![wθ, wθ, vθ] 0 1 (by decide) hvw hvw, add_zero,
    add_zero]

private theorem inner_tanB_nrmN : ⟪tanB, nrmN⟫ = -(173370837 / 594823321) := by
  rw [tanB_eq, nrmN]
  simp only [inner_add_left, inner_add_right, inner_pt]
  norm_num [dot]

private theorem norm_sq_tanB : ‖tanB‖ ^ 2 = 3 := by
  rw [← real_inner_self_eq_norm_sq, tanB_eq]
  simp only [inner_add_left, inner_add_right, inner_pt]
  norm_num [dot]

private theorem norm_sq_nrmN : ‖nrmN‖ ^ 2 = 3 := by
  rw [← real_inner_self_eq_norm_sq, nrmN]
  simp only [inner_add_left, inner_add_right, inner_pt]
  norm_num [dot]

private theorem norm_sq_sub :
    ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ ^ 2 =
      4238642 / 594823321 := by
  rw [← real_inner_self_eq_norm_sq, const_eq, const_eq]
  change ⟪pt vθ vθ vθ - pt e₁ e₁ e₁, pt vθ vθ vθ - pt e₁ e₁ e₁⟫ = _
  simp only [inner_sub_left, inner_sub_right, inner_pt]
  norm_num [dot]

/-- The lower bound for the data of the example. -/
private theorem lower_bound :
    23 / 20 * ((1 : ℝ)⁻¹ *
        ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
        ‖tanB‖) ≤
      ‖tuckerTangentProj (fun _ : Fin 3 => vθ) 1 (coW fun _ : Fin 3 => vθ) tanB -
        tuckerTangentProj (fun _ : Fin 3 => e₁) 1 (coW fun _ : Fin 3 => e₁) tanB‖ := by
  have hsym := (isOrthProj_tuckerTangentProj hvθ IsOrthProj.one (actOn_coW hvθ 1)
    (coW_eq_unfold_mul hvθ one_ne_zero)).symm tanB nrmN
  have hN : (0 : ℝ) < ‖nrmN‖ := by nlinarith [norm_nonneg nrmN, norm_sq_nrmN]
  have hkey : (173370837 / 594823321 : ℝ) ≤
      ‖tuckerTangentProj (fun _ : Fin 3 => vθ) 1 (coW fun _ : Fin 3 => vθ) tanB - tanB‖ *
        ‖nrmN‖ := by
    refine le_trans (le_of_eq ?_) (real_inner_le_norm _ _)
    rw [inner_sub_left, hsym, tuckerTangentProj_nrmN, inner_zero_right, zero_sub,
      inner_tanB_nrmN, neg_neg]
  have h1 : 23 / 20 *
      ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
      ‖tanB‖ * ‖nrmN‖ ≤ 173370837 / 594823321 := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, mul_pow, norm_sq_sub, norm_sq_tanB, norm_sq_nrmN]
    norm_num
  rw [tuckerTangentProj_tanB, inv_one, one_mul]
  refine le_of_mul_le_mul_right ?_ hN
  calc 23 / 20 *
        (‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
          ‖tanB‖) * ‖nrmN‖
      = 23 / 20 *
          ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
          ‖tanB‖ * ‖nrmN‖ := by ring
    _ ≤ 173370837 / 594823321 := h1
    _ ≤ _ := hkey

/-- The right-hand side of the Lipschitz bound is positive for the data of the example. -/
private theorem rhs_pos :
    0 < (1 : ℝ)⁻¹ *
      ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
      ‖tanB‖ := by
  have h1 : (0 : ℝ) <
      ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ := by
    nlinarith [norm_nonneg (tucker (core 1) (fun _ : Fin 3 => vθ) -
      tucker (core 1) (fun _ : Fin 3 => e₁)), norm_sq_sub]
  have h2 : (0 : ℝ) < ‖tanB‖ := by nlinarith [norm_nonneg tanB, norm_sq_tanB]
  rw [inv_one, one_mul]
  exact mul_pos h1 h2

/-- The data of the example satisfy the hypotheses of `norm_tuckerTangentProj_sub_le`, the
right-hand side of its bound is positive, and the lower bound holds. -/
private theorem example_spec :
    ∃ (U U' : ∀ _ : Fin 3, Matrix (Fin 2) (Fin 1) ℝ) (C C' : Tensor fun _ : Fin 3 => Fin 1)
      (W W' : ∀ k : Fin 3, Matrix (∀ _ : {j : Fin 3 // j ≠ k}, Fin 2) (Fin 1) ℝ) (ρ : ℝ)
      (B : Tensor fun _ : Fin 3 => Fin 2),
      (∀ k, (U k)ᵀ * U k = 1) ∧
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) ∧
      (∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (Fin 1)) ∧
      (∀ k, (U' k)ᵀ * U' k = 1) ∧
      (∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U') ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B) ∧
      (∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (Fin 1)) ∧
      0 < ρ ∧
      (∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
        (Fintype.card (Fin 1) - 1)) ∧
      0 < ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖ ∧
      23 / 20 * (ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖) ≤
        ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ :=
  ⟨fun _ => e₁, fun _ => vθ, core 1, core 1, coW fun _ => e₁, coW fun _ => vθ, 1, tanB, he₁,
    actOn_coW he₁ 1, coW_eq_unfold_mul he₁ one_ne_zero, rank_unfold_tucker_core he₁ one_ne_zero,
    hvθ, actOn_coW hvθ 1, coW_eq_unfold_mul hvθ one_ne_zero,
    rank_unfold_tucker_core hvθ one_ne_zero, one_pos,
    le_singularValues_unfold_tucker_core he₁ zero_le_one, rhs_pos, lower_bound⟩

/-- The two tangent projectors of the example differ at `B`. -/
private theorem tuckerTangentProj_ne :
    tuckerTangentProj (fun _ : Fin 3 => vθ) 1 (coW fun _ : Fin 3 => vθ) tanB ≠
      tuckerTangentProj (fun _ : Fin 3 => e₁) 1 (coW fun _ : Fin 3 => e₁) tanB := fun h => by
  have h1 := lower_bound
  have h2 := rhs_pos
  rw [h, sub_self, norm_zero] at h1
  linarith

/-- The bound of `norm_tuckerTangentProj_sub_le` for the data of the example. -/
private theorem upper_bound :
    ‖tuckerTangentProj (fun _ : Fin 3 => vθ) 1 (coW fun _ : Fin 3 => vθ) tanB -
        tuckerTangentProj (fun _ : Fin 3 => e₁) 1 (coW fun _ : Fin 3 => e₁) tanB‖ ≤
      √((3 : ℕ) : ℝ) * (1 : ℝ)⁻¹ *
        ‖tucker (core 1) (fun _ : Fin 3 => vθ) - tucker (core 1) (fun _ : Fin 3 => e₁)‖ *
        ‖tanB‖ := by
  -- the hypotheses are supplied before the conclusion is compared with the goal
  have h := norm_tuckerTangentProj_sub_le (d := 3) (ι := fun _ => Fin 2) (r := fun _ => Fin 1)
    (s := fun _ => Fin 1) (s' := fun _ => Fin 1) (U := fun _ => e₁) (U' := fun _ => vθ)
    (C := core 1) (C' := core 1) (W := coW fun _ => e₁) (W' := coW fun _ => vθ) (ρ := 1) he₁
    (actOn_coW he₁ 1) (coW_eq_unfold_mul he₁ one_ne_zero)
    (rank_unfold_tucker_core he₁ one_ne_zero) hvθ (actOn_coW hvθ 1)
    (coW_eq_unfold_mul hvθ one_ne_zero) (rank_unfold_tucker_core hvθ one_ne_zero) one_pos
  exact h (le_singularValues_unfold_tucker_core he₁ zero_le_one) tanB

end TuckerProjectorLowerBoundExamples

open TuckerProjectorLowerBoundExamples in
/-- **The constant of the Lipschitz bound of the tangent projector of the Tucker manifold with
three modes is at least `23/20`.** There are Tucker tensors `X = C ×ₖ Uₖ` and `Y = C' ×ₖ U'ₖ` of
multilinear rank `(1, 1, 1)` in `ℝ^{2 × 2 × 2}`, co-range bases `W`, `W'`, a lower bound `ρ > 0`
of the smallest nonzero singular values of the unfoldings of `X` and a tensor `B` which satisfy
all hypotheses of `norm_tuckerTangentProj_sub_le` and
`23/20 · ρ⁻¹ ‖Y - X‖ ‖B‖ ≤ ‖P(Y) B - P(X) B‖`. In particular the bound with the constant `1` of
the manifold of matrices of fixed rank (`norm_tangentProjAt_sub_le_inv_mul`) does not hold for
Tucker tensors with three modes. -/
theorem exists_mul_le_norm_tuckerTangentProj_sub :
    ∃ (U U' : ∀ _ : Fin 3, Matrix (Fin 2) (Fin 1) ℝ) (C C' : Tensor fun _ : Fin 3 => Fin 1)
      (W W' : ∀ k : Fin 3, Matrix (∀ _ : {j : Fin 3 // j ≠ k}, Fin 2) (Fin 1) ℝ) (ρ : ℝ)
      (B : Tensor fun _ : Fin 3 => Fin 2),
      (∀ k, (U k)ᵀ * U k = 1) ∧
      (∀ k, actOn (· ≠ k) (W k * (W k)ᵀ) (tucker C U) = tucker C U) ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W k = unfold (· ≠ k) (tucker C U) * B) ∧
      (∀ k, (unfold (· ≠ k) (tucker C U)).rank = Fintype.card (Fin 1)) ∧
      (∀ k, (U' k)ᵀ * U' k = 1) ∧
      (∀ k, actOn (· ≠ k) (W' k * (W' k)ᵀ) (tucker C' U') = tucker C' U') ∧
      (∀ k, ∃ B : Matrix _ (Fin 1) ℝ, W' k = unfold (· ≠ k) (tucker C' U') * B) ∧
      (∀ k, (unfold (· ≠ k) (tucker C' U')).rank = Fintype.card (Fin 1)) ∧
      0 < ρ ∧
      (∀ k, ρ ≤ (toEuclideanLin (unfold (· ≠ k) (tucker C U))).singularValues
        (Fintype.card (Fin 1) - 1)) ∧
      23 / 20 * (ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖) ≤
        ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ := by
  obtain ⟨U, U', C, C', W, W', ρ, B, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, h12⟩ :=
    example_spec
  exact ⟨U, U', C, C', W, W', ρ, B, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12⟩

open TuckerProjectorLowerBoundExamples in
/-- Non-vacuity of `norm_tuckerTangentProj_sub_le` with three modes and two different tangent
projectors: for the tensors `X = e₁ ⊗ e₁ ⊗ e₁` and `Y = v ⊗ v ⊗ v` of
`exists_mul_le_norm_tuckerTangentProj_sub` all hypotheses hold, `P(Y) B ≠ P(X) B`, and the bound
`‖P(Y) B - P(X) B‖ ≤ √3 ρ⁻¹ ‖Y - X‖ ‖B‖` follows. -/
example :
    ∃ (U U' : ∀ _ : Fin 3, Matrix (Fin 2) (Fin 1) ℝ) (C C' : Tensor fun _ : Fin 3 => Fin 1)
      (W W' : ∀ k : Fin 3, Matrix (∀ _ : {j : Fin 3 // j ≠ k}, Fin 2) (Fin 1) ℝ) (ρ : ℝ)
      (B : Tensor fun _ : Fin 3 => Fin 2),
      tuckerTangentProj U' 1 W' B ≠ tuckerTangentProj U 1 W B ∧
      ‖tuckerTangentProj U' 1 W' B - tuckerTangentProj U 1 W B‖ ≤
        √((3 : ℕ) : ℝ) * ρ⁻¹ * ‖tucker C' U' - tucker C U‖ * ‖B‖ :=
  ⟨_, _, _, _, _, _, _, _, tuckerTangentProj_ne, upper_bound⟩

end Tensor

end LeanDLRA
