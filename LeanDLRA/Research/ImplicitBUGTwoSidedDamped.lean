import LeanDLRA.Research.ImplicitBUGStiffDamped

/-!
# A posteriori error bounds with damping for backward Euler of a two-sided stiff problem

Let `F(Z) = -BᵀB Z - Z CᵀC` and let `𝒫 Z = Z + h (BᵀB Z + Z CᵀC)` be the operator of a backward
Euler step, `R = 𝒫⁻¹`. For any sequence `Y_j` with the residuals `ρ_j = Y_j - 𝒫 Y_{j+1}` and a
backward Euler reference `X_{j+1} = R X_j` the error is `R^N (Y₀ - X₀) - ∑_j R^(N-j) ρ_j`, and each
power `R^k` is bounded by the `k`-th power of either one-sided resolvent, `(1 + h BᵀB)⁻¹` from the
left or `(1 + h CᵀC)⁻¹` from the right, whichever is smaller. Splitting a residual with two
partitions of unity, one acting on each side, before the choice of the side is made part by part
gives a smaller bound; the resolvent `(1 + h BᵀB)⁻¹` and its complement `h BᵀB (1 + h BᵀB)⁻¹` form
such a partition.

## Main results

* `ImplicitBUGTwoSidedDamped.norm_sub_le_sum_min_add_sum_min_of_sylvester`: the run bound for any
  sequence and any splittings of the start error and of the residuals into finitely many parts;
  `norm_sub_le_min_add_sum_min_of_sylvester` without a splitting of the start error.
* `norm_sub_le_min_add_sum_min_of_sylvester_residual`: the same with the residual and the defect
  of the reference as the two parts.
* `norm_sub_le_sum_min_add_sum_min_of_sylvester_partition`: the run bound with the parts
  `F_a (Y₀ - X₀) G_b` and `F_a ρ_j G_b` for partitions of unity `∑ F_a = 1`, `∑ G_b = 1`.
* `norm_sub_le_sum_min_add_sum_min_of_sylvester_resolvent`: the four parts given by the
  resolvents and their complements.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator, whose runs are the intended
  sequences `Y_j`; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffDamped

namespace ImplicitBUGTwoSidedDamped

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  {B : Matrix l m ℝ} {C : Matrix k n ℝ} {h : ℝ}

/-- The backward Euler operator of the two-sided problem in the form with a dissipative left
factor. -/
theorem sub_smul_neg_gram_mul_add (B : Matrix l m ℝ) (C : Matrix k n ℝ) (h : ℝ)
    (Z : Matrix m n ℝ) :
    Z - h • (-(Bᵀ * B) * Z) + h • (Z * (Cᵀ * C)) = Z + h • (Bᵀ * B * Z + Z * (Cᵀ * C)) := by
  rw [Matrix.neg_mul, smul_neg, sub_neg_eq_add, smul_add, add_assoc]

variable [DecidableEq m] [DecidableEq n]

/-- **The resolvent and its complement are a partition of unity**:
`(1 + h BᵀB)⁻¹ + h BᵀB (1 + h BᵀB)⁻¹ = 1`. -/
theorem inv_add_smul_gram_mul_inv (B : Matrix l m ℝ) (hh : 0 ≤ h) :
    (1 + h • (Bᵀ * B))⁻¹ + h • (Bᵀ * B) * (1 + h • (Bᵀ * B))⁻¹ = 1 := by
  have hu := isUnit_det_one_add_smul_gram B hh
  nth_rewrite 1 [← Matrix.one_mul (1 + h • (Bᵀ * B))⁻¹]
  rw [← Matrix.add_mul, Matrix.mul_nonsing_inv _ hu]

/-- **Damped a posteriori bound for any sequence, with splittings of the start error and of the
residuals.** Let `𝒫 Z = Z + h (BᵀB Z + Z CᵀC)`, let `X` be a backward Euler reference with defects,
`𝒫 X_{j+1} = X_j + δ_j`, and let `Y_j` be any sequence. For all splittings `Y₀ - X₀ = ∑_b Q_b` and
`Y_j - 𝒫 Y_{j+1} + δ_j = ∑_a P_{j,a}` into finitely many parts,

  `‖Y_N - X_N‖ ≤ ∑_b min(‖(1 + h BᵀB)⁻¹ ^ N Q_b‖, ‖Q_b (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} ∑_a min(‖(1 + h BᵀB)⁻¹ ^ (N-j) P_{j,a}‖, ‖P_{j,a} (1 + h CᵀC)⁻¹ ^ (N-j)‖)`.

Nothing is assumed on how `Y_j` was computed. -/
theorem norm_sub_le_sum_min_add_sum_min_of_sylvester {ι κ : Type*} (s : Finset ι)
    (t : Finset κ) {N : ℕ} {Y X δ : ℕ → Matrix m n ℝ} {P : ℕ → ι → Matrix m n ℝ}
    {Q : κ → Matrix m n ℝ} (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hQ : ∑ b ∈ t, Q b = Y 0 - X 0)
    (hP : ∀ j < N, ∑ a ∈ s, P j a =
      Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C))) + δ j) :
    ‖Y N - X N‖ ≤
      ∑ b ∈ t, min ‖(1 + h • (Bᵀ * B))⁻¹ ^ N * Q b‖ ‖Q b * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a ∈ s, min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) * P j a‖
        ‖P j a * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ := by
  have e : 1 - h • (-(Bᵀ * B)) = 1 + h • (Bᵀ * B) := by rw [smul_neg, sub_neg_eq_add]
  have key := norm_sub_le_sum_min_add_sum_min_of_backwardEuler s t (M := -(Bᵀ * B)) (C := C)
    (dotProduct_neg_gram_mulVec_nonpos B) hh
    (fun j hj => (sub_smul_neg_gram_mul_add B C h _).trans (hX j hj)) hQ
    (fun j hj => by rw [sub_smul_neg_gram_mul_add]; exact hP j hj)
  rwa [e] at key

/-- **Damped a posteriori bound for any sequence, with a splitting of the residuals.** In the
setting of `norm_sub_le_sum_min_add_sum_min_of_sylvester`, without a splitting of the start error:

  `‖Y_N - X_N‖ ≤ min(‖(1 + h BᵀB)⁻¹ ^ N (Y₀ - X₀)‖, ‖(Y₀ - X₀) (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} ∑_a min(‖(1 + h BᵀB)⁻¹ ^ (N-j) P_{j,a}‖, ‖P_{j,a} (1 + h CᵀC)⁻¹ ^ (N-j)‖)`. -/
theorem norm_sub_le_min_add_sum_min_of_sylvester {ι : Type*} (s : Finset ι) {N : ℕ}
    {Y X δ : ℕ → Matrix m n ℝ} {P : ℕ → ι → Matrix m n ℝ} (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (hP : ∀ j < N, ∑ a ∈ s, P j a =
      Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C))) + δ j) :
    ‖Y N - X N‖ ≤
      min ‖(1 + h • (Bᵀ * B))⁻¹ ^ N * (Y 0 - X 0)‖ ‖(Y 0 - X 0) * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a ∈ s, min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) * P j a‖
        ‖P j a * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ := by
  have key := norm_sub_le_sum_min_add_sum_min_of_sylvester s ({()} : Finset Unit)
    (Q := fun _ => Y 0 - X 0) hh hX (Finset.sum_singleton _ _) hP
  simpa only [Finset.sum_singleton] using key

/-- **Damped a posteriori bound for any sequence: residual and defect.** In the setting of
`norm_sub_le_min_add_sum_min_of_sylvester`, with the residuals
`ρ_j = Y_j - (Y_{j+1} + h (BᵀB Y_{j+1} + Y_{j+1} CᵀC))` of the sequence,

  `‖Y_N - X_N‖ ≤ min(‖(1 + h BᵀB)⁻¹ ^ N (Y₀ - X₀)‖, ‖(Y₀ - X₀) (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} (min(‖(1 + h BᵀB)⁻¹ ^ (N-j) ρ_j‖, ‖ρ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖)
      + min(‖(1 + h BᵀB)⁻¹ ^ (N-j) δ_j‖, ‖δ_j (1 + h CᵀC)⁻¹ ^ (N-j)‖))`. -/
theorem norm_sub_le_min_add_sum_min_of_sylvester_residual {N : ℕ}
    {Y X δ : ℕ → Matrix m n ℝ} (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j + δ j) :
    ‖Y N - X N‖ ≤
      min ‖(1 + h • (Bᵀ * B))⁻¹ ^ N * (Y 0 - X 0)‖ ‖(Y 0 - X 0) * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N,
        (min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) *
            (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C))))‖
          ‖(Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) *
            (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ +
        min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) * δ j‖
          ‖δ j * (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖) := by
  have key := norm_sub_le_min_add_sum_min_of_sylvester (Finset.univ : Finset Bool)
    (P := fun j b => cond b
      (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) (δ j))
    hh hX fun j _ => by rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
  simpa only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false] using key

/-- **Damped a posteriori bound with a two-sided splitting of the start error and of the
residuals.** Let `𝒫 Z = Z + h (BᵀB Z + Z CᵀC)`, `𝒫 X_{j+1} = X_j`, and let `Y_j` be any sequence
with the residuals `ρ_j = Y_j - 𝒫 Y_{j+1}`. For matrices with `∑_a F_a = 1` and `∑_b G_b = 1`,

  `‖Y_N - X_N‖ ≤ ∑_a ∑_b min(‖(1 + h BᵀB)⁻¹ ^ N (F_a (Y₀ - X₀) G_b)‖,
      ‖(F_a (Y₀ - X₀) G_b) (1 + h CᵀC)⁻¹ ^ N‖)
    + ∑_{j<N} ∑_a ∑_b min(‖(1 + h BᵀB)⁻¹ ^ (N-j) (F_a ρ_j G_b)‖,
      ‖(F_a ρ_j G_b) (1 + h CᵀC)⁻¹ ^ (N-j)‖)`:

the side from which a part is damped is chosen part by part. -/
theorem norm_sub_le_sum_min_add_sum_min_of_sylvester_partition {ι κ : Type*} (s : Finset ι)
    (t : Finset κ) {N : ℕ} {Y X : ℕ → Matrix m n ℝ} {F : ι → Matrix m m ℝ}
    {G : κ → Matrix n n ℝ} (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j)
    (hF : ∑ a ∈ s, F a = 1) (hG : ∑ b ∈ t, G b = 1) :
    ‖Y N - X N‖ ≤
      ∑ a ∈ s, ∑ b ∈ t,
        min ‖(1 + h • (Bᵀ * B))⁻¹ ^ N * (F a * (Y 0 - X 0) * G b)‖
          ‖F a * (Y 0 - X 0) * G b * (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a ∈ s, ∑ b ∈ t,
        min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) * (F a *
            (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) * G b)‖
          ‖F a * (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) * G b *
            (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ := by
  have hsplit : ∀ Z : Matrix m n ℝ, ∑ ab ∈ s ×ˢ t, F ab.1 * Z * G ab.2 = Z := fun Z => by
    rw [Finset.sum_product]
    simp only [← Matrix.mul_sum, ← Matrix.sum_mul, hF, hG, Matrix.one_mul, Matrix.mul_one]
  have key := norm_sub_le_sum_min_add_sum_min_of_sylvester (s ×ˢ t) (s ×ˢ t) (Y := Y) (X := X)
    (δ := fun _ => 0)
    (P := fun j ab => F ab.1 *
      (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) * G ab.2)
    (Q := fun ab => F ab.1 * (Y 0 - X 0) * G ab.2)
    hh (fun j hj => by rw [add_zero]; exact hX j hj) (hsplit _)
    (fun j _ => by rw [add_zero]; exact hsplit _)
  simpa only [Finset.sum_product] using key

/-- **Damped a posteriori bound with the four resolvent parts.** In the setting of
`norm_sub_le_sum_min_add_sum_min_of_sylvester_partition` take the partitions
`F ∈ {(1 + h BᵀB)⁻¹, h BᵀB (1 + h BᵀB)⁻¹}` and `G ∈ {(1 + h CᵀC)⁻¹, h CᵀC (1 + h CᵀC)⁻¹}`: the
start error and the residual of each step are split into four parts, and each part is damped by
the better of the two one-sided resolvents. -/
theorem norm_sub_le_sum_min_add_sum_min_of_sylvester_resolvent {N : ℕ}
    {Y X : ℕ → Matrix m n ℝ} (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j) :
    ‖Y N - X N‖ ≤
      ∑ a : Bool, ∑ b : Bool,
        min ‖(1 + h • (Bᵀ * B))⁻¹ ^ N *
            (cond a (1 + h • (Bᵀ * B))⁻¹ (h • (Bᵀ * B) * (1 + h • (Bᵀ * B))⁻¹) * (Y 0 - X 0) *
            cond b (1 + h • (Cᵀ * C))⁻¹ (h • (Cᵀ * C) * (1 + h • (Cᵀ * C))⁻¹))‖
          ‖cond a (1 + h • (Bᵀ * B))⁻¹ (h • (Bᵀ * B) * (1 + h • (Bᵀ * B))⁻¹) * (Y 0 - X 0) *
            cond b (1 + h • (Cᵀ * C))⁻¹ (h • (Cᵀ * C) * (1 + h • (Cᵀ * C))⁻¹) *
            (1 + h • (Cᵀ * C))⁻¹ ^ N‖ +
      ∑ j ∈ range N, ∑ a : Bool, ∑ b : Bool,
        min ‖(1 + h • (Bᵀ * B))⁻¹ ^ (N - j) *
            (cond a (1 + h • (Bᵀ * B))⁻¹ (h • (Bᵀ * B) * (1 + h • (Bᵀ * B))⁻¹) *
            (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) *
            cond b (1 + h • (Cᵀ * C))⁻¹ (h • (Cᵀ * C) * (1 + h • (Cᵀ * C))⁻¹))‖
          ‖cond a (1 + h • (Bᵀ * B))⁻¹ (h • (Bᵀ * B) * (1 + h • (Bᵀ * B))⁻¹) *
            (Y j - (Y (j + 1) + h • (Bᵀ * B * Y (j + 1) + Y (j + 1) * (Cᵀ * C)))) *
            cond b (1 + h • (Cᵀ * C))⁻¹ (h • (Cᵀ * C) * (1 + h • (Cᵀ * C))⁻¹) *
            (1 + h • (Cᵀ * C))⁻¹ ^ (N - j)‖ :=
  norm_sub_le_sum_min_add_sum_min_of_sylvester_partition Finset.univ Finset.univ hh hX
    (by rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, inv_add_smul_gram_mul_inv B hh])
    (by rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, inv_add_smul_gram_mul_inv C hh])

end ImplicitBUGTwoSidedDamped

/-! ### Non-vacuity -/

namespace ImplicitBUGTwoSidedDampedExample

/-- The hypotheses of the damped run bounds of the two-sided problem hold with a nonzero start
error and a nonzero residual. -/
example {h : ℝ} (hh : 0 < h) : ∃ (Y X δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
    (∀ j < 2, X (j + 1) + h • ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ *
      (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) * X (j + 1) + X (j + 1) *
      ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ))) =
      X j + δ j) ∧
    Y 0 - X 0 ≠ 0 ∧
    Y 0 - (Y 1 + h • ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ *
      (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ) * Y 1 + Y 1 *
      ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ)))) ≠ 0 := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun j _ => by simp, by simp, fun hc => ?_⟩
  have h00 : h = 0 := by simpa [Matrix.mul_apply] using congrFun (congrFun hc 0) 0
  exact hh.ne' h00

end ImplicitBUGTwoSidedDampedExample

end LeanDLRA
