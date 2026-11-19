import LeanDLRA.Analysis.GronwallVariableRate
import LeanDLRA.Matrix.LowRankDistance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A lower bound for methods that evaluate the field on low-rank matrices only

A low-rank integrator of rank `k` for `y' = F(t, y)` uses the field only through values
`F(t, Z)` at matrices `Z` of rank at most `k`. Two fields that agree on `M_{≤ k}` (`lowRankSet`)
are therefore treated alike by every such method, adaptive or not, whatever the output is. If
their exact solutions `A₁`, `A₂` differ, the method has error at least `‖A₁(T) - A₂(T)‖ / 2` for
one of them.

For a field `G` and a direction `W`, the fields `G ± c dist(·, M_{≤ k}) W` agree with `G` on
`M_{≤ k}`; the perturbation raises the Lipschitz constant and the one-sided Lipschitz constant
by at most `|c| ‖W‖`. For `2 × 2` matrices, `k = 1`, `G ≡ e₂e₂ᵀ`, `W = e₁e₁ᵀ` and the start
`a e₁e₁ᵀ` of rank one the solutions are `diag(a ± L t²/2, t)`, with `dist(A(t), M_{≤ 1}) = t`, and

    ‖A₊(T) - A₋(T)‖ = L T² = 2 L ∫₀ᵀ dist(A±(s), M_{≤ 1}) ds.

Hence every such method has error at least `L ∫₀ᵀ dist(A(s), M_{≤ 1}) ds` for one of two
`L`-Lipschitz fields. The constant `1` in front of `L ∫ dist` cannot be raised for this
information: if `F` is `L`-Lipschitz and equals a constant `B` on `M_{≤ k}`, the output
`A(0) + T B` has error at most `L ∫₀ᵀ dist(A(s), M_{≤ k}) ds`.

## Main results

* `InformationLowerBound.half_dist_le_max_dist`, `half_norm_sub_le_max_error`: a map that
  depends on the field only through its restriction to a set has error at least half the
  distance of the solutions, for one of two fields equal on the set.
* `InformationLowerBound.isLipschitzField_add_distLR_smul`,
  `isOneSidedLipschitzField_add_distLR_smul`, `add_distLR_smul_of_rank_le`: the perturbed fields.
* `InformationLowerBound.norm_sub_affine_le_integral_distLR`: the upper bound for the output
  `A(0) + T B`.
* `InformationLowerBound.linearMap_ext_of_rank_le_one`: a linear field is determined by its
  values on matrices of rank at most one, so the lower bound does not apply to linear fields.
* `InformationLowerBoundExample.odeSolution_pairSol`, `norm_pairSol_sub_pairSol`,
  `norm_pairSol_sub_eq_two_mul_integral`, `mul_integral_distLR_le_max_error`: the `2 × 2` pair.
* `InformationLowerBoundExample.norm_pairSol_sub_central`: for both fields of the pair the
  output `A(0) + T B` has error exactly `L ∫₀ᵀ dist(A(s), M_{≤ 1}) ds`.
-/

open Set MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.InformationLowerBound

/-! ### Two problems with the same information -/

/-- Any point `z` has distance at least `dist x y / 2` from one of `x`, `y`. -/
theorem half_dist_le_max_dist {α : Type*} [PseudoMetricSpace α] (z x y : α) :
    dist x y / 2 ≤ max (dist z x) (dist z y) := by
  have h := dist_triangle_left x y z
  have h1 := le_max_left (dist z x) (dist z y)
  have h2 := le_max_right (dist z x) (dist z y)
  linarith

/-- **Two fields with the same information.** Let the output `Φ F` of a method depend on the field
`F` only through the values of `F` on a set `S` of times and states. If `F₁ = F₂` on `S`, then for
any targets `A₁`, `A₂` (the exact solutions at the final time) the error for one of the two fields
is at least `‖A₁ - A₂‖ / 2`. -/
theorem half_norm_sub_le_max_error {X Y V : Type*} [NormedAddCommGroup V] {S : Set (ℝ × X)}
    (Φ : (ℝ → X → Y) → V)
    (hΦ : ∀ F G : ℝ → X → Y, (∀ p ∈ S, F p.1 p.2 = G p.1 p.2) → Φ F = Φ G)
    {F₁ F₂ : ℝ → X → Y} (h : ∀ p ∈ S, F₁ p.1 p.2 = F₂ p.1 p.2) (A₁ A₂ : V) :
    ‖A₁ - A₂‖ / 2 ≤ max ‖Φ F₁ - A₁‖ ‖Φ F₂ - A₂‖ := by
  have key := half_dist_le_max_dist (Φ F₁) A₁ A₂
  simp only [dist_eq_norm] at key
  rw [← hΦ F₁ F₂ h]
  exact key

/-! ### Perturbations that vanish on the low-rank set -/

section Perturbation

variable {m n : Type*} [Fintype m] [Fintype n] {k : ℕ}
  {G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {W : Matrix m n ℝ} {c L₀ ℓ : ℝ}

/-- The field `G + c dist(·, M_{≤ k}) W` equals `G` on matrices of rank at most `k`. -/
theorem add_distLR_smul_of_rank_le (G : ℝ → Matrix m n ℝ → Matrix m n ℝ) (W : Matrix m n ℝ)
    (c t : ℝ) {Z : Matrix m n ℝ} (hZ : Z.rank ≤ k) :
    G t Z + (c * distLR k Z) • W = G t Z := by
  rw [distLR_eq_zero_of_rank_le hZ, mul_zero, zero_smul, add_zero]

private lemma sub_eq_aux (t : ℝ) (X Y : Matrix m n ℝ) :
    (G t X + (c * distLR k X) • W) - (G t Y + (c * distLR k Y) • W) =
      (G t X - G t Y) + (c * (distLR k X - distLR k Y)) • W := by
  rw [mul_sub, sub_smul]; abel

/-- If `G` is `L₀`-Lipschitz, then `G + c dist(·, M_{≤ k}) W` is Lipschitz with constant
`L₀ + |c| ‖W‖`. -/
theorem isLipschitzField_add_distLR_smul (hG : IsLipschitzField G L₀) (W : Matrix m n ℝ)
    (c : ℝ) (k : ℕ) :
    IsLipschitzField (fun t Z => G t Z + (c * distLR k Z) • W) (L₀ + |c| * ‖W‖) := by
  intro t X Y
  change ‖(G t X + (c * distLR k X) • W) - (G t Y + (c * distLR k Y) • W)‖ ≤ _
  rw [sub_eq_aux]
  calc ‖(G t X - G t Y) + (c * (distLR k X - distLR k Y)) • W‖
      ≤ ‖G t X - G t Y‖ + ‖(c * (distLR k X - distLR k Y)) • W‖ := norm_add_le _ _
    _ ≤ L₀ * ‖X - Y‖ + |c| * ‖X - Y‖ * ‖W‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact add_le_add (hG t X Y) (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_distLR_sub_le X Y) (abs_nonneg c)) (norm_nonneg W))
    _ = (L₀ + |c| * ‖W‖) * ‖X - Y‖ := by ring

/-- If `G` is one-sided Lipschitz with constant `ℓ`, then `G + c dist(·, M_{≤ k}) W` is one-sided
Lipschitz with constant `ℓ + |c| ‖W‖`. In particular the perturbed field is dissipative if
`ℓ + |c| ‖W‖ ≤ 0`. -/
theorem isOneSidedLipschitzField_add_distLR_smul (hG : IsOneSidedLipschitzField G ℓ)
    (W : Matrix m n ℝ) (c : ℝ) (k : ℕ) :
    IsOneSidedLipschitzField (fun t Z => G t Z + (c * distLR k Z) • W) (ℓ + |c| * ‖W‖) := by
  intro t X Y
  change ⟪(G t X + (c * distLR k X) • W) - (G t Y + (c * distLR k Y) • W), X - Y⟫ ≤ _
  rw [sub_eq_aux, inner_add_left, real_inner_smul_left]
  have h2 : c * (distLR k X - distLR k Y) * ⟪W, X - Y⟫ ≤ |c| * ‖W‖ * ‖X - Y‖ ^ 2 := by
    calc c * (distLR k X - distLR k Y) * ⟪W, X - Y⟫
        ≤ |c * (distLR k X - distLR k Y) * ⟪W, X - Y⟫| := le_abs_self _
      _ = |c| * |distLR k X - distLR k Y| * |⟪W, X - Y⟫| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * ‖X - Y‖ * (‖W‖ * ‖X - Y‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (abs_distLR_sub_le X Y) (abs_nonneg c))
            (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (mul_nonneg (abs_nonneg c) (norm_nonneg _))
      _ = |c| * ‖W‖ * ‖X - Y‖ ^ 2 := by ring
  calc ⟪G t X - G t Y, X - Y⟫ + c * (distLR k X - distLR k Y) * ⟪W, X - Y⟫
      ≤ ℓ * ‖X - Y‖ ^ 2 + |c| * ‖W‖ * ‖X - Y‖ ^ 2 := add_le_add (hG t X Y) h2
    _ = (ℓ + |c| * ‖W‖) * ‖X - Y‖ ^ 2 := by ring

/-- The affine field `Z ↦ B - μ Z` is one-sided Lipschitz with constant `-μ`. -/
theorem isOneSidedLipschitzField_sub_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E) (μ : ℝ) :
    IsOneSidedLipschitzField (fun _ Z => B - μ • Z) (-μ) := by
  intro t x y
  have e : (B - μ • x) - (B - μ • y) = (-μ) • (x - y) := by
    rw [smul_sub, neg_smul, neg_smul]; abel
  have h : ⟪(B - μ • x) - (B - μ • y), x - y⟫ = -μ * ‖x - y‖ ^ 2 := by
    rw [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact h.le

end Perturbation

/-! ### The matching upper bound for constant data -/

section Upper

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Upper bound for constant data.** Let `F` be `L`-Lipschitz and equal to the constant `B` on
the matrices of rank at most `k`, and let `A` solve `y' = F(t, y)` on `[0, T]`. Then the output
`A(0) + T B`, which uses only the values of `F` on `M_{≤ k}`, satisfies
`‖A(T) - (A(0) + T B)‖ ≤ L ∫₀ᵀ dist(A(s), M_{≤ k}) ds`. -/
theorem norm_sub_affine_le_integral_distLR {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {B : Matrix m n ℝ} {L T : ℝ} {k : ℕ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : ∀ t (Z : Matrix m n ℝ), Z.rank ≤ k → F t Z = B)
    (hA : ODESolution F A 0 T) (hT : 0 ≤ T) :
    ‖A T - (A 0 + T • B)‖ ≤ L * ∫ s in (0 : ℝ)..T, distLR k (A s) := by
  have hpt : ∀ t (Z : Matrix m n ℝ), ‖F t Z - B‖ ≤ L * distLR k Z := by
    intro t Z
    rcases hL.eq_or_lt with h0 | hpos
    · subst h0
      have h := hF t Z 0
      rw [hB t 0 (by simp)] at h
      simpa using h
    · have h1 : ‖F t Z - B‖ / L ≤ distLR k Z := le_distLR_iff.2 fun Y hY => by
        rw [div_le_iff₀ hpos, mul_comm]
        have h := hF t Z Y
        rwa [hB t Y hY] at h
      calc ‖F t Z - B‖ = L * (‖F t Z - B‖ / L) := by field_simp
        _ ≤ L * distLR k Z := mul_le_mul_of_nonneg_left h1 hL
  set g : ℝ → ℝ := fun s => L * distLR k (IccExtend hT ((Icc (0 : ℝ) T).domRestrict A) s) with hg
  have hgc : Continuous g :=
    continuous_const.mul ((lipschitzWith_distLR k).continuous.comp hA.cont.domRestrict.Icc_extend')
  have hgA : ∀ s ∈ Icc (0 : ℝ) T, g s = L * distLR k (A s) := fun s hs => by
    simp only [hg, IccExtend_of_mem _ _ hs, domRestrict_apply]
  have hf : ContinuousOn (fun x : ℝ => A x - (A 0 + x • B)) (Icc 0 T) :=
    hA.cont.sub (Continuous.continuousOn (by fun_prop))
  have hf' : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun x : ℝ => A x - (A 0 + x • B)) (F x (A x) - B) (Ici x) x := by
    intro x hx
    have h2 : HasDerivAt (fun x : ℝ => A 0 + x • B) B x := by
      simpa using ((hasDerivAt_id x).smul_const B).const_add (A 0)
    exact (hA.deriv x hx).sub h2.hasDerivWithinAt
  have key := norm_le_exp_integral_mul_add_integral_exp_integral_mul
    (f := fun x : ℝ => A x - (A 0 + x • B)) (f' := fun x => F x (A x) - B) (δ := 0) (a := 0)
    (b := T) (k := fun _ => 0) (g := g) continuous_const hgc hf hf' (by simp)
    (fun x hx => by
      rw [zero_mul, zero_add, hgA x (Ico_subset_Icc_self hx)]
      exact hpt x (A x)) T (right_mem_Icc.2 hT)
  have hint : ∫ s in (0 : ℝ)..T, g s = L * ∫ s in (0 : ℝ)..T, distLR k (A s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    exact hgA s hs
  simp only [intervalIntegral.integral_zero, Real.exp_zero, mul_zero, zero_add, one_mul] at key
  rwa [hint] at key

end Upper

/-! ### Linear fields are determined by rank-one evaluations -/

section Linear

variable {m n : Type*} [Finite m] [Fintype n]

/-- Two linear maps on real matrices that agree on all matrices of rank at most one are equal:
the matrices `eᵢ eⱼᵀ` span the space. Hence a linear field is determined by its restriction to
`M_{≤ 1}`, and there is no pair of distinct linear fields with the same low-rank information. -/
theorem linearMap_ext_of_rank_le_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f g : Matrix m n ℝ →ₗ[ℝ] V} (h : ∀ Z : Matrix m n ℝ, Z.rank ≤ 1 → f Z = g Z) : f = g := by
  classical
  apply Matrix.ext_linearMap
  intro i j
  refine LinearMap.ext fun c => ?_
  change f (Matrix.single i j c) = g (Matrix.single i j c)
  refine h _ ?_
  have e : Matrix.single i j c = Matrix.vecMulVec (Pi.single i c) (Pi.single j (1 : ℝ)) := by
    ext a b
    rcases eq_or_ne a i with rfl | ha <;> rcases eq_or_ne b j with rfl | hb
    · simp [Matrix.vecMulVec_apply]
    · simp [Matrix.vecMulVec_apply, hb, hb.symm]
    · simp [Matrix.vecMulVec_apply, ha, ha.symm]
    · simp [Matrix.vecMulVec_apply, ha, ha.symm]
  rw [e]
  exact Matrix.rank_vecMulVec_le _ _

end Linear

end LeanDLRA.InformationLowerBound

/-! ### The explicit pair of `2 × 2` fields -/

namespace LeanDLRA.InformationLowerBoundExample

open LeanDLRA.InformationLowerBound

/-- The direction `e₂ e₂ᵀ` of the common field on rank-one matrices. -/
noncomputable def dirB : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 1]

/-- The direction `e₁ e₁ᵀ` of the perturbation. -/
noncomputable def dirW : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]

/-- The field `F_c(t, Z) = e₂e₂ᵀ + c dist(Z, M_{≤ 1}) e₁e₁ᵀ`. -/
noncomputable def pairField (c : ℝ) (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  dirB + (c * distLR 1 Z) • dirW

/-- The curve `A_c(t) = diag(a + c t²/2, t)`. -/
noncomputable def pairSol (a c t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (a + c * t ^ 2 / 2) • dirW + t • dirB

lemma norm_dirB : ‖dirB‖ = 1 := by
  rw [Frobenius.norm_def]
  simp [dirB, Fin.sum_univ_two, Matrix.diagonal_apply]

lemma norm_dirW : ‖dirW‖ = 1 := by
  rw [Frobenius.norm_def]
  simp [dirW, Fin.sum_univ_two, Matrix.diagonal_apply]

lemma pairSol_eq_diagonal (a c t : ℝ) :
    pairSol a c t = Matrix.diagonal ![a + c * t ^ 2 / 2, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSol, dirW, dirB]

/-- For `0 ≤ y ≤ x` the distance of `diag(x, y)` to the matrices of rank at most one is `y`. -/
theorem distLR_one_diagonal {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    distLR 1 (Matrix.diagonal ![x, y]) = y := by
  refine le_antisymm ?_ ?_
  · have hr : (MatrixBUG.unitCol * (x • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        MatrixBUG.unitColᵀ).rank ≤ 1 := rank_mul_mul_transpose_le _ _ _
    refine (distLR_le_norm_sub hr).trans (le_of_eq ?_)
    have e : Matrix.diagonal ![x, y] - MatrixBUG.unitCol * (x • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        MatrixBUG.unitColᵀ = y • dirB := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dirB, Matrix.mul_apply]
    rw [e, norm_smul, norm_dirB, mul_one, Real.norm_of_nonneg hy]
  · refine le_distLR_diagonal hy (fun i => ?_) (by simp)
    fin_cases i
    · simpa [abs_of_nonneg (hy.trans hxy)] using hxy
    · simp [abs_of_nonneg hy]

/-- Both fields equal the constant `e₂e₂ᵀ` on matrices of rank at most one. -/
theorem pairField_of_rank_le (c t : ℝ) {Z : Matrix (Fin 2) (Fin 2) ℝ} (hZ : Z.rank ≤ 1) :
    pairField c t Z = dirB := by
  rw [pairField, distLR_eq_zero_of_rank_le hZ, mul_zero, zero_smul, add_zero]

/-- The field `F_c` is Lipschitz with constant `|c|`. -/
theorem isLipschitzField_pairField (c : ℝ) : IsLipschitzField (pairField c) |c| := by
  have h := isLipschitzField_add_distLR_smul (G := fun _ _ => dirB) (L₀ := 0)
    (fun t X Y => by simp) dirW c 1
  rwa [norm_dirW, mul_one, zero_add] at h

/-- The start `A_c(0) = a e₁e₁ᵀ` has rank at most one and does not depend on `c`. -/
theorem rank_pairSol_zero (a c : ℝ) : (pairSol a c 0).rank ≤ 1 := by
  have e : pairSol a c 0 = MatrixBUG.unitCol * (a • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      MatrixBUG.unitColᵀ := by
    rw [pairSol_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  rw [e]
  exact rank_mul_mul_transpose_le _ _ _

theorem pairSol_zero (a c c' : ℝ) : pairSol a c 0 = pairSol a c' 0 := by
  simp [pairSol]

/-- Along the curve the distance to the rank-one matrices is `t`, as long as
`T + |c| T² / 2 ≤ a`. -/
theorem distLR_pairSol {a c t T : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ T) (hT : T + |c| * T ^ 2 / 2 ≤ a) :
    distLR 1 (pairSol a c t) = t := by
  rw [pairSol_eq_diagonal]
  refine distLR_one_diagonal h0 ?_
  have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h2 : 0 ≤ (c + |c|) * t ^ 2 := mul_nonneg (by linarith [neg_abs_le c]) (sq_nonneg t)
  have h3 : 0 ≤ |c| * (T ^ 2 - t ^ 2) := mul_nonneg (abs_nonneg c) (sub_nonneg.2 hsq)
  nlinarith

lemma hasDerivAt_pairSol (a c t : ℝ) :
    HasDerivAt (pairSol a c) (dirB + (c * t) • dirW) t := by
  have h1 : HasDerivAt (fun s : ℝ => a + c * s ^ 2 / 2) (c * t) t := by
    have h := (((hasDerivAt_pow 2 t).const_mul c).div_const 2).const_add a
    refine h.congr_deriv ?_
    norm_num
    ring
  have h2 : HasDerivAt (fun s : ℝ => (a + c * s ^ 2 / 2) • dirW + s • dirB)
      ((c * t) • dirW + (1 : ℝ) • dirB) t :=
    (h1.smul_const dirW).add ((hasDerivAt_id' t).smul_const dirB)
  rw [one_smul, add_comm ((c * t) • dirW) dirB] at h2
  exact h2

/-- **The exact solutions.** `A_c(t) = diag(a + c t²/2, t)` solves `y' = F_c(t, y)` on `[0, T]`
if `T + |c| T² / 2 ≤ a`. -/
theorem odeSolution_pairSol {a c T : ℝ} (hT : T + |c| * T ^ 2 / 2 ≤ a) :
    ODESolution (pairField c) (pairSol a c) 0 T where
  cont := fun t _ => (hasDerivAt_pairSol a c t).continuousAt.continuousWithinAt
  deriv t ht := by
    rw [pairField, distLR_pairSol ht.1 ht.2.le hT]
    exact (hasDerivAt_pairSol a c t).hasDerivWithinAt

/-- The two solutions differ by `L T²` at time `T`. -/
theorem norm_pairSol_sub_pairSol (a T : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖pairSol a L T - pairSol a (-L) T‖ = L * T ^ 2 := by
  have e : pairSol a L T - pairSol a (-L) T = (L * T ^ 2) • dirW := by
    have h : L * T ^ 2 = (a + L * T ^ 2 / 2) - (a + -L * T ^ 2 / 2) := by ring
    rw [h, sub_smul, pairSol, pairSol]
    abel
  rw [e, norm_smul, norm_dirW, mul_one, Real.norm_of_nonneg (mul_nonneg hL (sq_nonneg T))]

theorem integral_distLR_pairSol {a c T : ℝ} (h0 : 0 ≤ T) (hT : T + |c| * T ^ 2 / 2 ≤ a) :
    ∫ s in (0 : ℝ)..T, distLR 1 (pairSol a c s) = T ^ 2 / 2 := by
  have h : ∫ s in (0 : ℝ)..T, distLR 1 (pairSol a c s) = ∫ s in (0 : ℝ)..T, s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le h0] at hs
      exact distLR_pairSol hs.1 hs.2 hT
  rw [h, integral_id]
  ring

/-- **The identity of the pair.** For `c = L` and for `c = -L`:
`‖A₊(T) - A₋(T)‖ = 2 L ∫₀ᵀ dist(A_c(s), M_{≤ 1}) ds`. -/
theorem norm_pairSol_sub_eq_two_mul_integral {a L T c : ℝ} (hL : 0 ≤ L) (h0 : 0 ≤ T)
    (hT : T + L * T ^ 2 / 2 ≤ a) (hc : c = L ∨ c = -L) :
    ‖pairSol a L T - pairSol a (-L) T‖ = 2 * L * ∫ s in (0 : ℝ)..T, distLR 1 (pairSol a c s) := by
  have hc' : |c| = L := by
    rcases hc with rfl | rfl
    · exact abs_of_nonneg hL
    · rw [abs_neg, abs_of_nonneg hL]
  rw [norm_pairSol_sub_pairSol a T hL, integral_distLR_pairSol h0 (by rwa [hc'])]
  ring

/-- **Lower bound for every method with rank-one information.** Let the output `Φ F` depend on
`F` only through the values of `F` at matrices of rank at most one. For the two `L`-Lipschitz
fields `F_L`, `F_{-L}` (equal on `M_{≤ 1}`, with the same start of rank one) the error at time `T`
is at least `L ∫₀ᵀ dist(A(s), M_{≤ 1}) ds` for one of them; the integral is the same for both
solutions. -/
theorem mul_integral_distLR_le_max_error {a L T c : ℝ} (hL : 0 ≤ L) (h0 : 0 ≤ T)
    (hT : T + L * T ^ 2 / 2 ≤ a) (hc : c = L ∨ c = -L)
    (Φ : (ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hΦ : ∀ F G : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ t (Z : Matrix (Fin 2) (Fin 2) ℝ), Z.rank ≤ 1 → F t Z = G t Z) → Φ F = Φ G) :
    L * ∫ s in (0 : ℝ)..T, distLR 1 (pairSol a c s) ≤
      max ‖Φ (pairField L) - pairSol a L T‖ ‖Φ (pairField (-L)) - pairSol a (-L) T‖ := by
  have h := half_norm_sub_le_max_error
    (S := {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ | p.2.rank ≤ 1}) Φ
    (fun F G hFG => hΦ F G fun t Z hZ => hFG (t, Z) hZ)
    (F₁ := pairField L) (F₂ := pairField (-L))
    (fun p hp => by rw [pairField_of_rank_le L p.1 hp, pairField_of_rank_le (-L) p.1 hp])
    (pairSol a L T) (pairSol a (-L) T)
  rw [norm_pairSol_sub_eq_two_mul_integral hL h0 hT hc] at h
  linarith

/-- For each field of the pair the output `A(0) + T e₂e₂ᵀ` has error `|c| T² / 2`, which is
`|c| ∫₀ᵀ dist(A_c(s), M_{≤ 1}) ds`: the bound `norm_sub_affine_le_integral_distLR` holds with
equality, and so does the lower bound `mul_integral_distLR_le_max_error` for this output. -/
theorem norm_pairSol_sub_central (a c T : ℝ) :
    ‖pairSol a c T - (pairSol a c 0 + T • dirB)‖ = |c| * T ^ 2 / 2 := by
  have e : pairSol a c T - (pairSol a c 0 + T • dirB) = (c * T ^ 2 / 2) • dirW := by
    have h : c * T ^ 2 / 2 = (a + c * T ^ 2 / 2) - (a + c * 0 ^ 2 / 2) := by ring
    rw [h, sub_smul, pairSol, pairSol, zero_smul]
    abel
  rw [e, norm_smul, norm_dirW, mul_one, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg T), abs_two]

/-- Non-vacuity of the lower bound: `a = 2`, `L = 1`, `T = 1`; every output that ignores the
field has error at least `1 / 2` for one of the two fields. -/
example (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    1 / 2 ≤ max ‖Y - pairSol 2 1 1‖ ‖Y - pairSol 2 (-1) 1‖ := by
  have h := mul_integral_distLR_le_max_error (a := 2) (L := 1) (T := 1) (c := 1) zero_le_one
    zero_le_one (by norm_num) (Or.inl rfl) (fun _ => Y) (fun _ _ _ => rfl)
  rw [integral_distLR_pairSol zero_le_one (by norm_num)] at h
  norm_num at h ⊢
  exact h

/-- Non-vacuity of the upper bound `norm_sub_affine_le_integral_distLR`: the field `F_1` on
`[0, 1]` with `a = 2`. -/
example : ‖pairSol 2 1 1 - (pairSol 2 1 0 + (1 : ℝ) • dirB)‖ ≤
    1 * ∫ s in (0 : ℝ)..1, distLR 1 (pairSol 2 1 s) :=
  norm_sub_affine_le_integral_distLR (by simpa using isLipschitzField_pairField 1) zero_le_one
    (fun t _ hZ => pairField_of_rank_le 1 t hZ) (odeSolution_pairSol (by norm_num)) zero_le_one

/-- Non-vacuity of the dissipative class: `Z ↦ e₂e₂ᵀ - 2 Z + dist(Z, M_{≤ 1}) e₁e₁ᵀ` is one-sided
Lipschitz with the negative constant `-2 + 1 · 1`, and equals `e₂e₂ᵀ - 2 Z` on `M_{≤ 1}`. -/
example : IsOneSidedLipschitzField
    (fun _ Z => (dirB - (2 : ℝ) • Z) + ((1 : ℝ) * distLR 1 Z) • dirW) (-2 + |(1 : ℝ)| * ‖dirW‖) :=
  isOneSidedLipschitzField_add_distLR_smul (isOneSidedLipschitzField_sub_smul dirB 2) dirW 1 1

end LeanDLRA.InformationLowerBoundExample
