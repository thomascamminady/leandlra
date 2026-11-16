import LeanDLRA.DLRA.Defs
import LeanDLRA.FixedRank.TangentSpace.Curvature
import LeanDLRA.Foundations.AprioriExistence
import LeanDLRA.Matrix.GaugeODE

/-!
# Existence and uniqueness of the DLRA solution

For a field `F` that is Lipschitz in the state, bounded by `B` and continuous in time, and a
starting value `Y₀` of rank `r`, the projected equation `Ẏ = P(Y) F(t, Y)` of dynamical low-rank
approximation has a solution of rank `r` on every interval `[a, b]` with `B (b - a) < σ_r(Y₀)`
(`σ_r` the smallest nonzero singular value, `σ_{r-1}` in the `0`-indexed numbering of the
library), and any two solutions of rank `r` with the same starting value agree. The solution is
`Y = U S Vᵀ` with factors that solve the gauge-fixed factor equations
`U̇ = (1 - U Uᵀ) F V S⁻¹`, `Ṡ = Uᵀ F V`, `V̇ = (1 - V Vᵀ) Fᵀ U S⁻ᵀ`.

## Main results

* `LeanDLRA.IsDLRASolution.sub_le_singularValues`: along a DLRA solution of rank `r`,
  `σ_{r-1}(Y(a)) - B (t - a) ≤ σ_{r-1}(Y(t))`.
* `LeanDLRA.norm_tangentProjAt_field_sub_le`: the projected field `Y ↦ P(Y) F(t, Y)` is Lipschitz
  with constant `2 B / ρ + L` between matrices of rank `r`, one of which has `σ_{r-1} ≥ ρ`.
* `LeanDLRA.IsDLRASolution.eqOn`: two DLRA solutions of rank `r` on `[a, b]` with the same value
  at `a` agree on `[a, b]`.
* `LeanDLRA.exists_factors_isDLRASolution`: for orthonormal `U₀`, `V₀` and a core `S₀` with
  `ρ ‖v‖ ≤ ‖S₀ v‖` and `B (b - a) < ρ`, the factor equations have a solution on `[a, b]` with
  these starting values; the factors stay orthonormal, `(ρ - B (t - a)) ‖v‖ ≤ ‖S(t) v‖`, and
  `U S Vᵀ` is a DLRA solution of rank `r`.
* `LeanDLRA.exists_isDLRASolution`: existence and uniqueness of the DLRA solution with starting
  value `Y₀` of rank `r` on `[a, b]` with `B (b - a) < σ_{r-1}(Y₀)`.
* `LeanDLRA.IsDLRASolution.exists_factors`: a DLRA solution with `B (b - a) < σ_{r-1}(Y(a))` has
  factors `Y = U S Vᵀ` on `[a, b]` that are orthonormal and solve the factor equations.

## Implementation notes

The factor equations are not Lipschitz on the whole space, since they contain `S⁻¹`. The proof
uses `exists_ODESolution_of_apriori_sublevel`: on the region where `‖U‖`, `‖V‖` are bounded and
`‖S - S₀‖ ≤ δ₂ < ρ` the factor field is Lipschitz and bounded, and for every damped factor
system the factors stay orthonormal (`transpose_mul_self_eq_one_of_odeSolution_of_bound`), so
that `‖Ṡ‖ ≤ B` and `‖S(t) - S₀‖ ≤ B (t - a)`. No continuation argument is needed.

Uniqueness needs no lower bound for the singular values in the statement: `σ_{r-1}` is continuous
and positive along both solutions, so it has a positive minimum on `[a, b]`.

For `r = 0` the hypothesis `B (b - a) < σ_{r-1}(Y₀)` of the existence theorems cannot hold
(`σ₀(0) = 0`); the uniqueness theorem covers `r = 0`.

## TODO

* The solution up to the first time at which `σ_r` reaches zero, as one statement. The
  existence theorem can be applied again at `b` as long as `B` times the remaining time is below
  the current `σ_r`.
* Fields that are Lipschitz and bounded on a tube only (`DLRAProblem`) instead of on the whole
  space.

## References

* [KochLubich2007] (factor equations and their solution of the projected equation)
-/

open Set Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

/-! ### Bounded Lipschitz families of matrices -/

section BddLip

variable {X : Type*} [NormedAddCommGroup X] {p q s : Type*} [Fintype p] [Fintype q] [Fintype s]

/-- A family `h t x` of matrices is bounded and Lipschitz in `x` on the set `K`, with constants
that do not depend on `t`. A device of this file for the factor field. -/
private def BddLip (K : Set X) (h : ℝ → X → Matrix p q ℝ) : Prop :=
  ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ (∀ t, ∀ x ∈ K, ‖h t x‖ ≤ M) ∧
    ∀ t, ∀ x ∈ K, ∀ y ∈ K, ‖h t x - h t y‖ ≤ L * ‖x - y‖

variable {K : Set X}

private lemma BddLip.intro {h : ℝ → X → Matrix p q ℝ} {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ t, ∀ x ∈ K, ‖h t x‖ ≤ M)
    (hl : ∀ t, ∀ x ∈ K, ∀ y ∈ K, ‖h t x - h t y‖ ≤ L * ‖x - y‖) : BddLip K h :=
  ⟨M, L, hM, hL, hb, hl⟩

private lemma BddLip.mul {h₁ : ℝ → X → Matrix p q ℝ} {h₂ : ℝ → X → Matrix q s ℝ}
    (H₁ : BddLip K h₁) (H₂ : BddLip K h₂) : BddLip K (fun t x => h₁ t x * h₂ t x) := by
  obtain ⟨M₁, L₁, hM₁, hL₁, hb₁, hl₁⟩ := H₁
  obtain ⟨M₂, L₂, hM₂, hL₂, hb₂, hl₂⟩ := H₂
  refine ⟨M₁ * M₂, M₁ * L₂ + L₁ * M₂, mul_nonneg hM₁ hM₂,
    add_nonneg (mul_nonneg hM₁ hL₂) (mul_nonneg hL₁ hM₂), fun t x hx => ?_,
    fun t x hx y hy => ?_⟩
  · exact (Frobenius.norm_mul_le _ _).trans
      (mul_le_mul (hb₁ t x hx) (hb₂ t x hx) (norm_nonneg _) hM₁)
  · have e : h₁ t x * h₂ t x - h₁ t y * h₂ t y =
        h₁ t x * (h₂ t x - h₂ t y) + (h₁ t x - h₁ t y) * h₂ t y := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    change ‖h₁ t x * h₂ t x - h₁ t y * h₂ t y‖ ≤ _
    rw [e]
    calc ‖h₁ t x * (h₂ t x - h₂ t y) + (h₁ t x - h₁ t y) * h₂ t y‖
        ≤ ‖h₁ t x‖ * ‖h₂ t x - h₂ t y‖ + ‖h₁ t x - h₁ t y‖ * ‖h₂ t y‖ :=
          (norm_add_le _ _).trans
            (add_le_add (Frobenius.norm_mul_le _ _) (Frobenius.norm_mul_le _ _))
      _ ≤ M₁ * (L₂ * ‖x - y‖) + L₁ * ‖x - y‖ * M₂ :=
          add_le_add (mul_le_mul (hb₁ t x hx) (hl₂ t x hx y hy) (norm_nonneg _) hM₁)
            (mul_le_mul (hl₁ t x hx y hy) (hb₂ t y hy) (norm_nonneg _)
              (mul_nonneg hL₁ (norm_nonneg _)))
      _ = (M₁ * L₂ + L₁ * M₂) * ‖x - y‖ := by ring

private lemma BddLip.transpose {h : ℝ → X → Matrix p q ℝ} (H : BddLip K h) :
    BddLip K (fun t x => (h t x)ᵀ) := by
  obtain ⟨M, L, hM, hL, hb, hl⟩ := H
  refine ⟨M, L, hM, hL, fun t x hx => ?_, fun t x hx y hy => ?_⟩
  · change ‖(h t x)ᵀ‖ ≤ M
    rw [Frobenius.norm_transpose]
    exact hb t x hx
  · change ‖(h t x)ᵀ - (h t y)ᵀ‖ ≤ _
    rw [← Matrix.transpose_sub, Frobenius.norm_transpose]
    exact hl t x hx y hy

private lemma BddLip.one_sub [DecidableEq p] {h : ℝ → X → Matrix p p ℝ} (H : BddLip K h) :
    BddLip K (fun t x => 1 - h t x) := by
  obtain ⟨M, L, hM, hL, hb, hl⟩ := H
  refine ⟨‖(1 : Matrix p p ℝ)‖ + M, L, add_nonneg (norm_nonneg _) hM, hL, fun t x hx => ?_,
    fun t x hx y hy => ?_⟩
  · exact (norm_sub_le _ _).trans (add_le_add le_rfl (hb t x hx))
  · change ‖1 - h t x - (1 - h t y)‖ ≤ _
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
    exact hl t x hx y hy

private lemma BddLip.comp {F : ℝ → Matrix p q ℝ → Matrix p q ℝ} {L B : ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) {h : ℝ → X → Matrix p q ℝ}
    (H : BddLip K h) : BddLip K (fun t x => F t (h t x)) := by
  obtain ⟨M, L', hM, hL', hb, hl⟩ := H
  refine ⟨max B 0, max L 0 * L', le_max_right _ _, mul_nonneg (le_max_right _ _) hL',
    fun t x _ => (hB t (h t x)).trans (le_max_left _ _), fun t x hx y hy => ?_⟩
  calc ‖F t (h t x) - F t (h t y)‖ ≤ L * ‖h t x - h t y‖ := hF t _ _
    _ ≤ max L 0 * ‖h t x - h t y‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max L 0 * (L' * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hl t x hx y hy) (le_max_right _ _)
    _ = max L 0 * L' * ‖x - y‖ := by ring

private lemma BddLip.inv [DecidableEq p] {h : ℝ → X → Matrix p p ℝ} (H : BddLip K h) {ρ : ℝ}
    (hρ : 0 < ρ)
    (hbelow : ∀ t, ∀ x ∈ K, ∀ v : EuclideanSpace ℝ p, ρ * ‖v‖ ≤ ‖toEuclideanLin (h t x) v‖) :
    BddLip K (fun t x => (h t x)⁻¹) := by
  obtain ⟨M, L, hM, hL, hb, hl⟩ := H
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
  have hinv : ∀ t, ∀ x ∈ K, Curvature.specNorm (h t x)⁻¹ ≤ ρ⁻¹ := fun t x hx =>
    Curvature.specNorm_inv_le hρ (hbelow t x hx)
  refine ⟨ρ⁻¹ * ‖(1 : Matrix p p ℝ)‖, ρ⁻¹ * (L * ρ⁻¹), mul_nonneg hρi (norm_nonneg _),
    mul_nonneg hρi (mul_nonneg hL hρi), fun t x hx => ?_, fun t x hx y hy => ?_⟩
  · calc ‖(h t x)⁻¹‖ = ‖(h t x)⁻¹ * 1‖ := by rw [Matrix.mul_one]
      _ ≤ Curvature.specNorm (h t x)⁻¹ * ‖(1 : Matrix p p ℝ)‖ := Curvature.frob_mul_le _ _
      _ ≤ ρ⁻¹ * ‖(1 : Matrix p p ℝ)‖ :=
          mul_le_mul_of_nonneg_right (hinv t x hx) (norm_nonneg _)
  · have hdx := Curvature.isUnit_det_of_bounded_below hρ (hbelow t x hx)
    have hdy := Curvature.isUnit_det_of_bounded_below hρ (hbelow t y hy)
    have e : (h t x)⁻¹ - (h t y)⁻¹ = (h t x)⁻¹ * (h t y - h t x) * (h t y)⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hdx, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdy, Matrix.mul_one]
    change ‖(h t x)⁻¹ - (h t y)⁻¹‖ ≤ _
    rw [e, Matrix.mul_assoc]
    calc ‖(h t x)⁻¹ * ((h t y - h t x) * (h t y)⁻¹)‖
        ≤ Curvature.specNorm (h t x)⁻¹ * ‖(h t y - h t x) * (h t y)⁻¹‖ :=
          Curvature.frob_mul_le _ _
      _ ≤ ρ⁻¹ * (‖h t y - h t x‖ * Curvature.specNorm (h t y)⁻¹) :=
          mul_le_mul (hinv t x hx) (Curvature.frob_mul_le' _ _) (norm_nonneg _) hρi
      _ ≤ ρ⁻¹ * (L * ‖x - y‖ * ρ⁻¹) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hinv t y hy)
            (Curvature.specNorm_nonneg _) (mul_nonneg hL (norm_nonneg _))) hρi
          rw [norm_sub_rev]
          exact hl t x hx y hy
      _ = ρ⁻¹ * (L * ρ⁻¹) * ‖x - y‖ := by ring

end BddLip

/-! ### Auxiliary facts -/

section Auxiliary

variable {p q s : Type*} [Fintype p] [Fintype q] [Fintype s]

private lemma hasDerivWithinAt_clm_apply {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : E →L[ℝ] G) {y : ℝ → E} {y' : E} {u : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt y y' u t) : HasDerivWithinAt (fun t => A (y t)) (A y') u t :=
  A.hasFDerivAt.comp_hasDerivWithinAt t h

private lemma continuous_const_matrix_mul {G : ℝ → Matrix p q ℝ} (hG : Continuous G)
    (A : Matrix s p ℝ) : Continuous fun t => A * G t :=
  (Frobenius.leftMulCLM A).continuous.comp hG

private lemma continuous_matrix_mul_const {G : ℝ → Matrix p q ℝ} (hG : Continuous G)
    (W : Matrix q s ℝ) : Continuous fun t => G t * W :=
  (Frobenius.rightMulCLM W).continuous.comp hG

private lemma continuous_matrix_transpose {G : ℝ → Matrix p q ℝ} (hG : Continuous G) :
    Continuous fun t => (G t)ᵀ :=
  (Frobenius.transposeCLM : Matrix p q ℝ →L[ℝ] Matrix q p ℝ).continuous.comp hG

private lemma norm_smul_le_of_eq_zero_or {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ M : ℝ} {z : E} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (hM : 0 ≤ M) (h : κ = 0 ∨ ‖z‖ ≤ M) :
    ‖κ • z‖ ≤ M := by
  rcases h with h | h
  · rw [h, zero_smul, norm_zero]
    exact hM
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    calc κ * ‖z‖ ≤ 1 * M := mul_le_mul h1 h (norm_nonneg _) zero_le_one
      _ = M := one_mul M

private lemma norm_eq_of_transpose_mul_self_eq_one [DecidableEq q] {U U' : Matrix p q ℝ}
    (hU : Uᵀ * U = 1) (hU' : U'ᵀ * U' = 1) : ‖U‖ = ‖U'‖ :=
  calc ‖U‖ = ‖U * 1‖ := by rw [Matrix.mul_one]
    _ = ‖(1 : Matrix q q ℝ)‖ := Frobenius.norm_mul_of_orthonormal hU 1
    _ = ‖U' * 1‖ := (Frobenius.norm_mul_of_orthonormal hU' 1).symm
    _ = ‖U'‖ := by rw [Matrix.mul_one]

/-- A core that is within `δ` of a core bounded below by `ρ` is bounded below by `ρ - δ`. -/
private lemma sub_mul_norm_le_of_norm_sub_le [DecidableEq p] {S S₀ : Matrix p p ℝ} {ρ δ : ℝ}
    (hS₀ : ∀ v : EuclideanSpace ℝ p, ρ * ‖v‖ ≤ ‖toEuclideanLin S₀ v‖) (h : ‖S - S₀‖ ≤ δ)
    (v : EuclideanSpace ℝ p) : (ρ - δ) * ‖v‖ ≤ ‖toEuclideanLin S v‖ := by
  have e : toEuclideanLin S = toEuclideanLin S₀ + toEuclideanLin (S - S₀) := by
    rw [← map_add, add_sub_cancel]
  have h1 := hS₀ v
  have h2 : ‖toEuclideanLin (S - S₀) v‖ ≤ δ * ‖v‖ :=
    (Curvature.norm_toEuclideanLin_le (S - S₀) v).trans
      (mul_le_mul_of_nonneg_right ((Curvature.specNorm_le_frob _).trans h) (norm_nonneg v))
  have h3 := norm_sub_le (toEuclideanLin S₀ v + toEuclideanLin (S - S₀) v)
    (toEuclideanLin (S - S₀) v)
  rw [add_sub_cancel_right] at h3
  rw [e, LinearMap.add_apply]
  linarith

end Auxiliary

private lemma matrix_eq_zero_of_rank_eq_zero {p q : Type*} [Fintype q] {M : Matrix p q ℝ}
    (h0 : M.rank = 0) : M = 0 := by
  classical
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h0
  simpa [Matrix.mulVec_single] using this

/-! ### The a priori bound and uniqueness -/

section Uniqueness

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Y Z : ℝ → Matrix m n ℝ} {a b L B : ℝ}

/-- **A priori bound for the smallest singular value.** Along a DLRA solution of rank `r` for a
field bounded by `B`, the `r`-th singular value decreases at most with speed `B`:
`σ_{r-1}(Y(a)) - B (t - a) ≤ σ_{r-1}(Y(t))`. The solution moves with speed at most `B`, because
the tangent projector does not increase norms, and singular values are `1`-Lipschitz. -/
theorem IsDLRASolution.sub_le_singularValues (hB : IsBoundedField F B)
    (hY : IsDLRASolution r F Y a b) : ∀ t ∈ Icc a b,
      (toEuclideanLin (Y a)).singularValues (r - 1) - B * (t - a) ≤
        (toEuclideanLin (Y t)).singularValues (r - 1) := by
  intro t ht
  have h1 := hY.1.norm_sub_le (B := B)
    (fun s _ => ((isOrthProj_tangentProjAt (Y s)).norm_le _).trans (hB s (Y s))) t ht
  have h2 := WeylSingular.abs_singularValues_sub_le_frobenius (Y a) (Y t) (r - 1)
  rw [norm_sub_rev] at h2
  linarith [(abs_le.1 h2).2]

/-- **The projected field is Lipschitz on the matrices of rank `r` with `σ_{r-1} ≥ ρ`.** For a
field `F` that is `L`-Lipschitz and bounded by `B`, and `X`, `Y` of rank `r` with
`0 < ρ ≤ σ_{r-1}(X)`: `‖P(Y) F(t, Y) - P(X) F(t, X)‖ ≤ (2 B / ρ + L) ‖Y - X‖`. -/
theorem norm_tangentProjAt_field_sub_le (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    {X Y : Matrix m n ℝ} (hX : X.rank = r) (hY : Y.rank = r) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (r - 1)) (t : ℝ) :
    ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖ ≤ (2 * ρ⁻¹ * B + L) * ‖Y - X‖ := by
  have h1 := norm_tangentProjAt_sub_le hX hY hρ hσ (F t Y)
  have h2 : ‖tangentProjAt X (F t Y - F t X)‖ ≤ L * ‖Y - X‖ :=
    ((isOrthProj_tangentProjAt X).norm_le _).trans (hF t Y X)
  have h3 : 2 * ρ⁻¹ * ‖Y - X‖ * ‖F t Y‖ ≤ 2 * ρ⁻¹ * ‖Y - X‖ * B :=
    mul_le_mul_of_nonneg_left (hB t Y)
      (mul_nonneg (mul_nonneg zero_le_two (inv_nonneg.2 hρ.le)) (norm_nonneg _))
  calc ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t X)‖
      = ‖(tangentProjAt Y (F t Y) - tangentProjAt X (F t Y)) +
          tangentProjAt X (F t Y - F t X)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖tangentProjAt Y (F t Y) - tangentProjAt X (F t Y)‖ +
          ‖tangentProjAt X (F t Y - F t X)‖ := norm_add_le _ _
    _ ≤ (2 * ρ⁻¹ * B + L) * ‖Y - X‖ := by linarith

omit [DecidableEq n] in
/-- **Uniqueness of the DLRA solution.** For a field that is Lipschitz in the state and bounded,
two DLRA solutions of rank `r` on `[a, b]` with the same value at `a` agree on `[a, b]`. No lower
bound for the singular values is assumed: `σ_{r-1}` is continuous and positive along both
solutions, so it has a positive minimum `ρ` on `[a, b]`, and the projected field is Lipschitz on
the matrices of rank `r` with `σ_{r-1} ≥ ρ` (`norm_tangentProjAt_field_sub_le`). -/
theorem IsDLRASolution.eqOn (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hY : IsDLRASolution r F Y a b) (hZ : IsDLRASolution r F Z a b) (h0 : Y a = Z a) :
    EqOn Y Z (Icc a b) := by
  classical
  rcases lt_or_ge b a with hba | hab
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.2 hba)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · intro t ht
    rw [matrix_eq_zero_of_rank_eq_zero ((hY.2 t ht).trans hr),
      matrix_eq_zero_of_rank_eq_zero ((hZ.2 t ht).trans hr)]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a 0)
  have hσc : Continuous fun X : Matrix m n ℝ => (toEuclideanLin X).singularValues (r - 1) :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun X X' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      exact WeylSingular.abs_singularValues_sub_le_frobenius X X' (r - 1)).continuous
  have hmin : ∀ {W : ℝ → Matrix m n ℝ}, IsDLRASolution r F W a b →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ t ∈ Icc a b, ρ ≤ (toEuclideanLin (W t)).singularValues (r - 1) := by
    intro W hW
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
      (hσc.comp_continuousOn hW.1.cont)
    exact ⟨_, SVD.singularValues_pred_rank_pos (hW.2 t₀ ht₀) hr,
      fun t ht => isMinOn_iff.1 hmin t ht⟩
  obtain ⟨ρY, hρY, hYσ⟩ := hmin hY
  obtain ⟨ρZ, hρZ, hZσ⟩ := hmin hZ
  have hρ : 0 < min ρY ρZ := lt_min hρY hρZ
  have hF' : IsLipschitzField F (max L 0) := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hK : 0 ≤ 2 * (min ρY ρZ)⁻¹ * B + max L 0 :=
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two (inv_nonneg.2 hρ.le)) hB0) (le_max_right _ _)
  have hLip : ∀ t ∈ Ico a b, LipschitzOnWith ⟨_, hK⟩ (fun X => tangentProjAt X (F t X))
      {X : Matrix m n ℝ | X.rank = r ∧
        min ρY ρZ ≤ (toEuclideanLin X).singularValues (r - 1)} := fun t _ =>
    LipschitzOnWith.of_dist_le_mul fun X hX X' hX' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact norm_tangentProjAt_field_sub_le (X := X') (Y := X) hF' hB hX'.1 hX.1 hρ hX'.2 t
  exact ODE_solution_unique_of_mem_Icc_right hLip hY.1.cont hY.1.deriv
    (fun t ht => ⟨hY.2 t (Ico_subset_Icc_self ht),
      (min_le_left _ _).trans (hYσ t (Ico_subset_Icc_self ht))⟩)
    hZ.1.cont hZ.1.deriv
    (fun t ht => ⟨hZ.2 t (Ico_subset_Icc_self ht),
      (min_le_right _ _).trans (hZσ t (Ico_subset_Icc_self ht))⟩) h0

end Uniqueness

/-! ### The factor field -/

section FactorField

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B : ℝ}

/-- The right-hand side of the factor equations `U̇ = (1 - U Uᵀ) F V S⁻¹`, `Ṡ = Uᵀ F V`,
`V̇ = (1 - V Vᵀ) Fᵀ U S⁻ᵀ` with `F = F(t, U S Vᵀ)`, as a field on the triples `(U, S, V)`. -/
private noncomputable def factorField (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) :
    Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ :=
  ((1 - x.1 * x.1ᵀ) * F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2 * x.2.1⁻¹,
    x.1ᵀ * F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2,
    (1 - x.2.2 * x.2.2ᵀ) * (F t (x.1 * x.2.1 * x.2.2ᵀ))ᵀ * x.1 * (x.2.1⁻¹)ᵀ)

/-- The projection of a triple `(U, S, V)` to `U`, as a continuous linear map. -/
private noncomputable def leftCLM :
    (Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) →L[ℝ]
      Matrix m (Fin r) ℝ :=
  ContinuousLinearMap.fst ℝ (Matrix m (Fin r) ℝ) (Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ)

/-- The projection of a triple `(U, S, V)` to `S`, as a continuous linear map. -/
private noncomputable def coreCLM :
    (Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) →L[ℝ]
      Matrix (Fin r) (Fin r) ℝ :=
  (ContinuousLinearMap.fst ℝ (Matrix (Fin r) (Fin r) ℝ) (Matrix n (Fin r) ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Matrix m (Fin r) ℝ)
      (Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ))

/-- The projection of a triple `(U, S, V)` to `V`, as a continuous linear map. -/
private noncomputable def rightCLM :
    (Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) →L[ℝ]
      Matrix n (Fin r) ℝ :=
  (ContinuousLinearMap.snd ℝ (Matrix (Fin r) (Fin r) ℝ) (Matrix n (Fin r) ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Matrix m (Fin r) ℝ)
      (Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ))

/-- On a bounded set of triples whose cores are bounded below, the factor field is Lipschitz and
bounded, and so are the products `Uᵀ (F V S⁻¹)` and `Vᵀ (Fᵀ U S⁻ᵀ)`. -/
private lemma factorField_bddLip (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    {K : Set (Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ)} {R ρ : ℝ}
    (hR : 0 ≤ R) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hρ : 0 < ρ)
    (hbelow : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖toEuclideanLin x.2.1 v‖) :
    ∃ M L' : ℝ, 0 ≤ M ∧ IsLipschitzFieldOn (factorField F) (univ ×ˢ K) L' ∧
      IsBoundedFieldOn (factorField F) (univ ×ˢ K) M ∧
      (∀ t, ∀ x ∈ K, ‖x.1ᵀ * (F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2 * x.2.1⁻¹)‖ ≤ M) ∧
      ∀ t, ∀ x ∈ K, ‖x.2.2ᵀ * ((F t (x.1 * x.2.1 * x.2.2ᵀ))ᵀ * x.1 * (x.2.1⁻¹)ᵀ)‖ ≤ M := by
  have hU : BddLip K (fun (_ : ℝ)
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) => x.1) :=
    BddLip.intro hR zero_le_one (fun _ x hx => (norm_fst_le x).trans (hK x hx))
      fun _ x _ y _ => by
        rw [one_mul]
        exact norm_fst_le (x - y)
  have hS : BddLip K (fun (_ : ℝ)
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) => x.2.1) :=
    BddLip.intro hR zero_le_one
      (fun _ x hx => ((norm_fst_le x.2).trans (norm_snd_le x)).trans (hK x hx))
      fun _ x _ y _ => by
        rw [one_mul]
        exact (norm_fst_le (x - y).2).trans (norm_snd_le (x - y))
  have hV : BddLip K (fun (_ : ℝ)
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) => x.2.2) :=
    BddLip.intro hR zero_le_one
      (fun _ x hx => ((norm_snd_le x.2).trans (norm_snd_le x)).trans (hK x hx))
      fun _ x _ y _ => by
        rw [one_mul]
        exact (norm_snd_le (x - y).2).trans (norm_snd_le (x - y))
  have hSi : BddLip K (fun (_ : ℝ)
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) => x.2.1⁻¹) :=
    hS.inv hρ fun _ x hx => hbelow x hx
  have hFY : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        F t (x.1 * x.2.1 * x.2.2ᵀ)) :=
    ((hU.mul hS).mul hV.transpose).comp hF hB
  have h₁ : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        (1 - x.1 * x.1ᵀ) * F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2 * x.2.1⁻¹) :=
    (((hU.mul hU.transpose).one_sub.mul hFY).mul hV).mul hSi
  have h₂ : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        x.1ᵀ * F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2) :=
    (hU.transpose.mul hFY).mul hV
  have h₃ : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        (1 - x.2.2 * x.2.2ᵀ) * (F t (x.1 * x.2.1 * x.2.2ᵀ))ᵀ * x.1 * (x.2.1⁻¹)ᵀ) :=
    (((hV.mul hV.transpose).one_sub.mul hFY.transpose).mul hU).mul hSi.transpose
  have h₄ : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        x.1ᵀ * (F t (x.1 * x.2.1 * x.2.2ᵀ) * x.2.2 * x.2.1⁻¹)) :=
    hU.transpose.mul ((hFY.mul hV).mul hSi)
  have h₅ : BddLip K (fun t
      (x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ) =>
        x.2.2ᵀ * ((F t (x.1 * x.2.1 * x.2.2ᵀ))ᵀ * x.1 * (x.2.1⁻¹)ᵀ)) :=
    hV.transpose.mul ((hFY.transpose.mul hU).mul hSi.transpose)
  obtain ⟨M₁, L₁, hM₁, hL₁, hb₁, hl₁⟩ := h₁
  obtain ⟨M₂, L₂, hM₂, hL₂, hb₂, hl₂⟩ := h₂
  obtain ⟨M₃, L₃, hM₃, hL₃, hb₃, hl₃⟩ := h₃
  obtain ⟨M₄, -, hM₄, -, hb₄, -⟩ := h₄
  obtain ⟨M₅, -, hM₅, -, hb₅, -⟩ := h₅
  refine ⟨M₁ + M₂ + M₃ + M₄ + M₅, L₁ + L₂ + L₃, by linarith, ?_, ?_, ?_, ?_⟩
  · rintro t x y ⟨-, hx⟩ ⟨-, hy⟩
    have hd := norm_nonneg (x - y)
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · exact (hl₁ t x hx y hy).trans (by nlinarith)
    · exact (hl₂ t x hx y hy).trans (by nlinarith)
    · exact (hl₃ t x hx y hy).trans (by nlinarith)
  · rintro t x ⟨-, hx⟩
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
    · exact (hb₁ t x hx).trans (by linarith)
    · exact (hb₂ t x hx).trans (by linarith)
    · exact (hb₃ t x hx).trans (by linarith)
  · exact fun t x hx => (hb₄ t x hx).trans (by linarith)
  · exact fun t x hx => (hb₅ t x hx).trans (by linarith)

/-- **A priori bounds for a damped factor system.** If `U`, `S`, `V` solve the factor equations
with the right-hand sides multiplied by a factor `κ(t) ∈ [0, 1]`, start with orthonormal `U`,
`V`, and the damped products `κ Uᵀ (F V S⁻¹)`, `κ Vᵀ (Fᵀ U S⁻ᵀ)` are bounded, then `U`, `V` stay
orthonormal and `‖S(t) - S(a)‖ ≤ B (t - a)`. -/
private lemma factor_apriori (hB : IsBoundedField F B) {U : ℝ → Matrix m (Fin r) ℝ}
    {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ} {κ : ℝ → ℝ} {a b M : ℝ}
    (hκ0 : ∀ t, 0 ≤ κ t) (hκ1 : ∀ t, κ t ≤ 1)
    (hUc : ContinuousOn U (Icc a b)) (hSc : ContinuousOn S (Icc a b))
    (hVc : ContinuousOn V (Icc a b))
    (hU : ∀ t ∈ Ico a b, HasDerivWithinAt U (κ t • ((1 - U t * (U t)ᵀ) *
      F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹)) (Ici t) t)
    (hS : ∀ t ∈ Ico a b, HasDerivWithinAt S (κ t • ((U t)ᵀ * F t (U t * S t * (V t)ᵀ) * V t))
      (Ici t) t)
    (hV : ∀ t ∈ Ico a b, HasDerivWithinAt V (κ t • ((1 - V t * (V t)ᵀ) *
      (F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)) (Ici t) t)
    (hbU : ∀ t ∈ Ico a b,
      ‖κ t • ((U t)ᵀ * (F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹))‖ ≤ M)
    (hbV : ∀ t ∈ Ico a b,
      ‖κ t • ((V t)ᵀ * ((F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ))‖ ≤ M)
    (hUa : (U a)ᵀ * U a = 1) (hVa : (V a)ᵀ * V a = 1) :
    ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ ‖S t - S a‖ ≤ B * (t - a) := by
  have hUo : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 :=
    transpose_mul_self_eq_one_of_odeSolution_of_bound (U := U)
      (G := fun t => κ t • (F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹)) (C := M)
      ⟨hUc, fun t ht => by
        convert hU t ht using 1
        simp only [Matrix.mul_smul, Matrix.mul_assoc]⟩
      (fun t ht => by simpa only [Matrix.mul_smul] using hbU t ht) hUa
  have hVo : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1 :=
    transpose_mul_self_eq_one_of_odeSolution_of_bound (U := V)
      (G := fun t => κ t • ((F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)) (C := M)
      ⟨hVc, fun t ht => by
        convert hV t ht using 1
        simp only [Matrix.mul_smul, Matrix.mul_assoc]⟩
      (fun t ht => by simpa only [Matrix.mul_smul] using hbV t ht) hVa
  intro t ht
  refine ⟨hUo t ht, hVo t ht, ?_⟩
  have hbd : ∀ s ∈ Ico a b, ‖κ s • ((U s)ᵀ * F s (U s * S s * (V s)ᵀ) * V s)‖ ≤ B := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s 0)
    refine norm_smul_le_of_eq_zero_or (hκ0 s) (hκ1 s) hB0 (Or.inr ?_)
    exact ((norm_mul_le_of_orthonormal (hVo s hs') _).trans
      (norm_transpose_mul_le (hUo s hs') _)).trans (hB s _)
  exact norm_image_sub_le_of_norm_deriv_right_le_segment hSc hS hbd t ht

end FactorField

/-! ### Existence -/

section Existence

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b L B : ℝ}

/-- **Existence of the factors of the DLRA solution** (for the factor equations and the solution
of the projected equation by them see [KochLubich2007]). Let `F` be Lipschitz in the state,
bounded by `B` and continuous in time, let `U₀`, `V₀` have `r` orthonormal columns and let the
core `S₀` be bounded below, `ρ ‖v‖ ≤ ‖S₀ v‖`. On every interval `[a, b]` with `B (b - a) < ρ`
the factor equations
`U̇ = (1 - U Uᵀ) F V S⁻¹`, `Ṡ = Uᵀ F V`, `V̇ = (1 - V Vᵀ) Fᵀ U S⁻ᵀ` with `F = F(t, U S Vᵀ)`
have a solution with the starting values `U₀`, `S₀`, `V₀`. Along it `U`, `V` stay orthonormal,
`S` stays invertible with `(ρ - B (t - a)) ‖v‖ ≤ ‖S(t) v‖`, and `Y = U S Vᵀ` is a DLRA solution
of rank `r`. -/
theorem exists_factors_isDLRASolution [DecidableEq m] (hF : IsLipschitzField F L)
    (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) {ρ : ℝ}
    (hS₀ : ∀ v : EuclideanSpace ℝ (Fin r), ρ * ‖v‖ ≤ ‖toEuclideanLin S₀ v‖) (hab : a ≤ b)
    (hρ : B * (b - a) < ρ) :
    ∃ (U : ℝ → Matrix m (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ)
      (V : ℝ → Matrix n (Fin r) ℝ), U a = U₀ ∧ S a = S₀ ∧ V a = V₀ ∧
      (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ IsUnit (S t).det ∧
        ∀ v : EuclideanSpace ℝ (Fin r), (ρ - B * (t - a)) * ‖v‖ ≤ ‖toEuclideanLin (S t) v‖) ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹) U a b ∧
      ODESolution (fun t _ => (U t)ᵀ * F t (U t * S t * (V t)ᵀ) * V t) S a b ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * (F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)
        V a b ∧
      IsDLRASolution r F (fun t => U t * S t * (V t)ᵀ) a b := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a 0)
  have hδ₁ : 0 ≤ B * (b - a) := mul_nonneg hB0 (sub_nonneg.2 hab)
  obtain ⟨δ₂, hδ12, hδ2ρ⟩ := exists_between hρ
  -- the gauge function: at most `B (b - a)` along solutions, at most `δ₂` on the safe region
  let g : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ → ℝ := fun x =>
    max (max (‖x.1‖ - ‖U₀‖ + B * (b - a)) (‖x.2.2‖ - ‖V₀‖ + B * (b - a))) ‖x.2.1 - S₀‖
  have hgdef : ∀ x, g x = max (max (‖x.1‖ - ‖U₀‖ + B * (b - a))
      (‖x.2.2‖ - ‖V₀‖ + B * (b - a))) ‖x.2.1 - S₀‖ := fun _ => rfl
  have hg : ∀ x y, |g x - g y| ≤ 1 * ‖x - y‖ := by
    intro x y
    rw [one_mul, hgdef x, hgdef y]
    refine (abs_max_sub_max_le_max _ _ _ _).trans
      (max_le ((abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)) ?_)
    · calc |‖x.1‖ - ‖U₀‖ + B * (b - a) - (‖y.1‖ - ‖U₀‖ + B * (b - a))|
          = |‖x.1‖ - ‖y.1‖| := by
            congr 1
            ring
        _ ≤ ‖x.1 - y.1‖ := abs_norm_sub_norm_le _ _
        _ ≤ ‖x - y‖ := norm_fst_le (x - y)
    · calc |‖x.2.2‖ - ‖V₀‖ + B * (b - a) - (‖y.2.2‖ - ‖V₀‖ + B * (b - a))|
          = |‖x.2.2‖ - ‖y.2.2‖| := by
            congr 1
            ring
        _ ≤ ‖x.2.2 - y.2.2‖ := abs_norm_sub_norm_le _ _
        _ ≤ ‖x - y‖ := (norm_snd_le (x - y).2).trans (norm_snd_le (x - y))
    · calc |‖x.2.1 - S₀‖ - ‖y.2.1 - S₀‖| ≤ ‖x.2.1 - S₀ - (y.2.1 - S₀)‖ :=
            abs_norm_sub_norm_le _ _
        _ = ‖x.2.1 - y.2.1‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖x - y‖ := (norm_fst_le (x - y).2).trans (norm_snd_le (x - y))
  -- the safe region `{g ≤ δ₂}` is bounded and its cores are bounded below by `ρ - δ₂`
  have hgS : ∀ x, g x ≤ δ₂ → ‖x.2.1 - S₀‖ ≤ δ₂ := fun x hx => by
    rw [hgdef] at hx
    exact (le_max_right _ _).trans hx
  have hKR : ∀ x ∈ {x | g x ≤ δ₂}, ‖x‖ ≤ ‖U₀‖ + ‖S₀‖ + ‖V₀‖ + δ₂ := by
    intro x hx
    have hx' : g x ≤ δ₂ := hx
    rw [hgdef] at hx'
    have h1 : ‖x.1‖ - ‖U₀‖ + B * (b - a) ≤ δ₂ :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hx'
    have h3 : ‖x.2.2‖ - ‖V₀‖ + B * (b - a) ≤ δ₂ :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hx'
    have h2 := norm_add_le (x.2.1 - S₀) S₀
    rw [sub_add_cancel] at h2
    have h2' : ‖x.2.1 - S₀‖ ≤ δ₂ := hgS x hx
    have hU0 := norm_nonneg U₀
    have hS0 := norm_nonneg S₀
    have hV0 := norm_nonneg V₀
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;> linarith
  have hR : 0 ≤ ‖U₀‖ + ‖S₀‖ + ‖V₀‖ + δ₂ := by
    have hU0 := norm_nonneg U₀
    have hS0 := norm_nonneg S₀
    have hV0 := norm_nonneg V₀
    linarith
  obtain ⟨M, L', hM0, hLip, hBdd, hbU, hbV⟩ := factorField_bddLip hF hB (K := {x | g x ≤ δ₂}) hR
    hKR (sub_pos.2 hδ2ρ) fun x hx v => sub_mul_norm_le_of_norm_sub_le hS₀ (hgS x hx) v
  -- a priori bounds for every damped factor system that is damped to zero outside the region
  have key : ∀ (c : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ → ℝ)
      (y : ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ),
      (∀ x, 0 ≤ c x) → (∀ x, c x ≤ 1) → (∀ t ∈ Ico a b, c (y t) = 0 ∨ g (y t) ≤ δ₂) →
      y a = (U₀, S₀, V₀) → ODESolution (fun t x => c x • factorField F t x) y a b →
      ∀ t ∈ Icc a b, ((y t).1)ᵀ * (y t).1 = 1 ∧ ((y t).2.2)ᵀ * (y t).2.2 = 1 ∧
        ‖(y t).2.1 - S₀‖ ≤ B * (t - a) := by
    intro c y hc0 hc1 hcK hya hy t ht
    have hSa : (y a).2.1 = S₀ := by rw [hya]
    have h := factor_apriori hB (U := fun t => (y t).1) (S := fun t => (y t).2.1)
      (V := fun t => (y t).2.2) (κ := fun t => c (y t)) (a := a) (b := b) (M := M)
      (fun _ => hc0 _) (fun _ => hc1 _)
      (leftCLM.continuous.comp_continuousOn hy.cont)
      (coreCLM.continuous.comp_continuousOn hy.cont)
      (rightCLM.continuous.comp_continuousOn hy.cont)
      (fun t ht => hasDerivWithinAt_clm_apply leftCLM (hy.deriv t ht))
      (fun t ht => hasDerivWithinAt_clm_apply coreCLM (hy.deriv t ht))
      (fun t ht => hasDerivWithinAt_clm_apply rightCLM (hy.deriv t ht))
      (fun t ht => norm_smul_le_of_eq_zero_or (hc0 _) (hc1 _) hM0
        ((hcK t ht).imp id fun h => hbU t (y t) h))
      (fun t ht => norm_smul_le_of_eq_zero_or (hc0 _) (hc1 _) hM0
        ((hcK t ht).imp id fun h => hbV t (y t) h))
      (by rw [hya]; exact hU₀) (by rw [hya]; exact hV₀) t ht
    exact ⟨h.1, h.2.1, by simpa only [hSa] using h.2.2⟩
  have hgle : ∀ (y : ℝ → Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ)
      (t : ℝ), t ∈ Icc a b → ((y t).1)ᵀ * (y t).1 = 1 ∧ ((y t).2.2)ᵀ * (y t).2.2 = 1 ∧
        ‖(y t).2.1 - S₀‖ ≤ B * (t - a) → g (y t) ≤ B * (b - a) := by
    intro y t ht h
    have hU := norm_eq_of_transpose_mul_self_eq_one h.1 hU₀
    have hV := norm_eq_of_transpose_mul_self_eq_one h.2.1 hV₀
    have hS := h.2.2.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hB0)
    rw [hgdef]
    exact max_le (max_le (by linarith) (by linarith)) hS
  have hcont : ∀ x : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ,
      Continuous fun t => factorField F t x := by
    intro x
    have hG := hc (x.1 * x.2.1 * x.2.2ᵀ)
    exact (continuous_matrix_mul_const (continuous_matrix_mul_const
      (continuous_const_matrix_mul hG _) _) _).prodMk
      ((continuous_matrix_mul_const (continuous_const_matrix_mul hG _) _).prodMk
        (continuous_matrix_mul_const (continuous_matrix_mul_const
          (continuous_const_matrix_mul (continuous_matrix_transpose hG) _) _) _))
  obtain ⟨y, hy, hya, hgy⟩ := exists_ODESolution_of_apriori_sublevel (f := factorField F) (g := g)
    (y₀ := (U₀, S₀, V₀)) hg hδ12 hLip hBdd (fun x _ => hcont x) hab
    (fun c y hc0 hc1 hcout hya hy t ht => hgle y t ht (key c y hc0 hc1
      (fun s _ => (le_or_gt (g (y s)) δ₂).elim Or.inr fun h => Or.inl (hcout _ h))
      hya hy t ht))
  -- the solution of the undamped system
  have hy1 : ODESolution (fun t x => (fun _ => (1 : ℝ)) x • factorField F t x) y a b :=
    ⟨hy.cont, fun t ht => by simpa only [one_smul] using hy.deriv t ht⟩
  have hfac := key (fun _ => 1) y (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun t ht => Or.inr ((hgy t (Ico_subset_Icc_self ht)).trans hδ12.le)) hya hy1
  have hbel : ∀ t ∈ Icc a b, ∀ v : EuclideanSpace ℝ (Fin r),
      (ρ - B * (t - a)) * ‖v‖ ≤ ‖toEuclideanLin (y t).2.1 v‖ := fun t ht v =>
    sub_mul_norm_le_of_norm_sub_le hS₀ (hfac t ht).2.2 v
  have hpos : ∀ t ∈ Icc a b, 0 < ρ - B * (t - a) := by
    intro t ht
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hB0
    linarith
  have hdet : ∀ t ∈ Icc a b, IsUnit ((y t).2.1).det := fun t ht =>
    Curvature.isUnit_det_of_bounded_below (hpos t ht) (hbel t ht)
  have hK : ∀ t ∈ Icc a b, g (y t) ≤ δ₂ := fun t ht => (hgy t ht).trans hδ12.le
  have hUode : ODESolution (fun t X => (1 - X * Xᵀ) *
      F t ((y t).1 * (y t).2.1 * ((y t).2.2)ᵀ) * (y t).2.2 * ((y t).2.1)⁻¹)
      (fun t => (y t).1) a b :=
    ⟨leftCLM.continuous.comp_continuousOn hy.cont, fun t ht =>
      hasDerivWithinAt_clm_apply leftCLM (hy.deriv t ht)⟩
  have hSode : ODESolution (fun t _ => ((y t).1)ᵀ *
      F t ((y t).1 * (y t).2.1 * ((y t).2.2)ᵀ) * (y t).2.2) (fun t => (y t).2.1) a b :=
    ⟨coreCLM.continuous.comp_continuousOn hy.cont, fun t ht =>
      hasDerivWithinAt_clm_apply coreCLM (hy.deriv t ht)⟩
  have hVode : ODESolution (fun t X => (1 - X * Xᵀ) *
      (F t ((y t).1 * (y t).2.1 * ((y t).2.2)ᵀ))ᵀ * (y t).1 * (((y t).2.1)⁻¹)ᵀ)
      (fun t => (y t).2.2) a b :=
    ⟨rightCLM.continuous.comp_continuousOn hy.cont, fun t ht =>
      hasDerivWithinAt_clm_apply rightCLM (hy.deriv t ht)⟩
  obtain ⟨-, hYode⟩ := factorODE_solution_isDLRA_tangentProj
    (Ad := fun t => F t ((y t).1 * (y t).2.1 * ((y t).2.2)ᵀ)) hUode hSode hVode
    (fun t ht => hdet t (Ico_subset_Icc_self ht))
    (fun _ hb' => ⟨M, fun t ht => hbU t (y t) (hK t ⟨ht.1, (ht.2.trans hb').le⟩)⟩)
    (fun _ hb' => ⟨M, fun t ht => hbV t (y t) (hK t ⟨ht.1, (ht.2.trans hb').le⟩)⟩)
    (by rw [hya]; exact hU₀) (by rw [hya]; exact hV₀)
  refine ⟨fun t => (y t).1, fun t => (y t).2.1, fun t => (y t).2.2,
    congrArg Prod.fst hya, congrArg (fun x => x.2.1) hya, congrArg (fun x => x.2.2) hya,
    fun t ht => ⟨(hfac t ht).1, (hfac t ht).2.1, hdet t ht, hbel t ht⟩,
    hUode, hSode, hVode, ⟨hYode.cont, fun t ht => ?_⟩, fun t ht => ?_⟩
  · have h := hYode.deriv t ht
    have hP := tangentProjAt_eq_tangentProj (hfac t (Ico_subset_Icc_self ht)).1
      (hfac t (Ico_subset_Icc_self ht)).2.1 (hdet t (Ico_subset_Icc_self ht))
    simpa only [hP] using h
  · exact (SVD.rank_eq_iff_exists_factor _).2
      ⟨(y t).1, (y t).2.1, (y t).2.2, (hfac t ht).1, (hfac t ht).2.1, hdet t ht, rfl⟩

end Existence

/-! ### Existence and uniqueness for a starting value of rank `r` -/

section ExistsUnique

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {a b L B : ℝ}

/-- **Existence and uniqueness of the DLRA solution** (for the kind of result see
[KochLubich2007]). Let `F` be Lipschitz in the state, bounded by `B` and continuous in time, and
let `Y₀` have rank `r`. On every interval `[a, b]` with `B (b - a) < σ_{r-1}(Y₀)` the projected
equation `Ẏ = P(Y) F(t, Y)` has a solution of rank `r` with `Y(a) = Y₀`; its `r`-th singular
value is at least `σ_{r-1}(Y₀) - B (t - a)`, and every DLRA solution of rank `r` with the same
starting value agrees with it on `[a, b]`. -/
theorem exists_isDLRASolution (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {Y₀ : Matrix m n ℝ} (hY₀ : Y₀.rank = r) (hab : a ≤ b)
    (hρ : B * (b - a) < (toEuclideanLin Y₀).singularValues (r - 1)) :
    ∃ Y : ℝ → Matrix m n ℝ, Y a = Y₀ ∧ IsDLRASolution r F Y a b ∧
      (∀ t ∈ Icc a b, (toEuclideanLin Y₀).singularValues (r - 1) - B * (t - a) ≤
        (toEuclideanLin (Y t)).singularValues (r - 1)) ∧
      ∀ Z : ℝ → Matrix m n ℝ, Z a = Y₀ → IsDLRASolution r F Z a b → EqOn Z Y (Icc a b) := by
  classical
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, -, rfl⟩ := (SVD.rank_eq_iff_exists_factor Y₀).1 hY₀
  obtain ⟨U, S, V, hUa, hSa, hVa, -, -, -, -, hsol⟩ := exists_factors_isDLRASolution hF hB hc
    hU₀ hV₀ (SVD.singularValues_mul_norm_le_of_eq_mul hU₀ hV₀ rfl hY₀) hab hρ
  have hYa : U a * S a * (V a)ᵀ = U₀ * S₀ * V₀ᵀ := by rw [hUa, hSa, hVa]
  refine ⟨fun t => U t * S t * (V t)ᵀ, hYa, hsol, fun t ht => ?_, fun Z hZa hZ => ?_⟩
  · have h := hsol.sub_le_singularValues hB t ht
    simpa only [hYa] using h
  · exact hZ.eqOn hF hB hsol (hZa.trans hYa.symm)

/-- **Factors along a DLRA solution** (for the kind of result see [KochLubich2007]). Let `F` be
Lipschitz in the state, bounded by `B` and continuous in time, and let `Y` be a DLRA solution of
rank `r` on `[a, b]` with `B (b - a) < σ_{r-1}(Y(a))`. Then `Y = U S Vᵀ` on `[a, b]` with factors
that solve the factor equations
`U̇ = (1 - U Uᵀ) F V S⁻¹`, `Ṡ = Uᵀ F V`, `V̇ = (1 - V Vᵀ) Fᵀ U S⁻ᵀ`, where `U`, `V` have
orthonormal columns and `S` is invertible. -/
theorem IsDLRASolution.exists_factors [DecidableEq m] {Y : ℝ → Matrix m n ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    (hY : IsDLRASolution r F Y a b) (hab : a ≤ b)
    (hρ : B * (b - a) < (toEuclideanLin (Y a)).singularValues (r - 1)) :
    ∃ (U : ℝ → Matrix m (Fin r) ℝ) (S : ℝ → Matrix (Fin r) (Fin r) ℝ)
      (V : ℝ → Matrix n (Fin r) ℝ),
      (∀ t ∈ Icc a b, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ IsUnit (S t).det ∧
        Y t = U t * S t * (V t)ᵀ) ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * F t (U t * S t * (V t)ᵀ) * V t * (S t)⁻¹) U a b ∧
      ODESolution (fun t _ => (U t)ᵀ * F t (U t * S t * (V t)ᵀ) * V t) S a b ∧
      ODESolution (fun t X => (1 - X * Xᵀ) * (F t (U t * S t * (V t)ᵀ))ᵀ * U t * ((S t)⁻¹)ᵀ)
        V a b := by
  have hra := hY.2 a (left_mem_Icc.2 hab)
  obtain ⟨U₀, S₀, V₀, hU₀, hV₀, -, hYa⟩ := (SVD.rank_eq_iff_exists_factor (Y a)).1 hra
  obtain ⟨U, S, V, hUa, hSa, hVa, hprop, hUo, hSo, hVo, hsol⟩ :=
    exists_factors_isDLRASolution hF hB hc hU₀ hV₀
      (SVD.singularValues_mul_norm_le_of_eq_mul hU₀ hV₀ hYa hra) hab hρ
  have h0 : Y a = U a * S a * (V a)ᵀ := by rw [hUa, hSa, hVa, hYa]
  have heq := hY.eqOn hF hB hsol h0
  exact ⟨U, S, V, fun t ht => ⟨(hprop t ht).1, (hprop t ht).2.1, (hprop t ht).2.2.1, heq ht⟩,
    hUo, hSo, hVo⟩

/-- **Non-vacuity.** For the constant field `F(t, Y) = G` on the `r × r` matrices, with any `G`
of norm less than `2` (not necessarily zero), there is a DLRA solution of rank `r` on `[0, 1/2]`
that starts at the identity matrix. -/
example {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : ‖G‖ < 2) :
    ∃ Y : ℝ → Matrix (Fin r) (Fin r) ℝ, Y 0 = 1 ∧
      IsDLRASolution r (fun _ _ => G) Y 0 (1 / 2) := by
  have h1 : (1 : Matrix (Fin r) (Fin r) ℝ)ᵀ * 1 = 1 := by
    rw [Matrix.transpose_one, Matrix.mul_one]
  obtain ⟨U, S, V, hU, hS, hV, -, -, -, -, hsol⟩ := exists_factors_isDLRASolution
    (F := fun (_ : ℝ) (_ : Matrix (Fin r) (Fin r) ℝ) => G) (L := 0) (B := ‖G‖) (ρ := 1)
    (a := 0) (b := 1 / 2) (U₀ := 1) (S₀ := 1) (V₀ := 1) (fun _ _ _ => by simp)
    (fun _ _ => le_rfl) (fun _ => continuous_const) h1 h1
    (fun v => by simp [Matrix.toLpLin_one]) (by norm_num) (by linarith)
  exact ⟨_, by simp [hU, hS, hV], hsol⟩

end ExistsUnique

end LeanDLRA
