import LeanDLRA.Classical.SVD
import LeanDLRA.Classical.EckartYoung

/-!
# Lower bounds for singular values from subspaces

The max-min characterisation of the singular values (Courant–Fischer for `T† T`) gives lower bounds
for `σ_k(T)`: if `T` is bounded below by `ρ` on a subspace of dimension at least `k + 1`, then
`ρ ≤ σ_k(T)` (`σ₀ ≥ σ₁ ≥ ⋯`, `0`-indexed as Mathlib's `LinearMap.singularValues`). For a matrix
given as `X = U S Vᵀ` with `r` orthonormal columns in `U` and `V`, a lower bound `ρ` of the core `S`
is therefore a lower bound of the `r`-th singular value `σ_{r-1}(X)`; this is the converse of
`LeanDLRA.WeylSingular.mul_norm_le_norm_toEuclideanLin_core`. The file also records that the
truncated SVD of a matrix of rank at most `r` is the matrix itself.

## Main results

* `LinearMap.le_singularValues_of_mul_norm_le`: `ρ ‖y‖ ≤ ‖T y‖` on a subspace `W` with
  `k + 1 ≤ dim W` implies `ρ ≤ σ_k(T)`.
* `LeanDLRA.SVD.le_singularValues_of_eq_mul`: for `X = U S Vᵀ` with orthonormal `U`, `V` (`r > 0`
  columns) and `ρ ‖w‖ ≤ ‖S w‖` for all `w`: `ρ ≤ σ_{r-1}(X)`.
* `LeanDLRA.EckartYoung.truncation_eq_self`: `truncation A r = A` if `rank A ≤ r`; with
  `EckartYoung.rank_truncation_le` it gives `LeanDLRA.RandomizedBUG.truncation_eq_self_iff`.

## References

* [Bhatia1997] R. Bhatia, *Matrix Analysis*, GTM 169, Springer 1997, §III.1 (max-min principle)
-/

open Module Submodule
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Max-min lower bound for a singular value.** If `ρ ‖y‖ ≤ ‖T y‖` for every `y` of a subspace
`W` of dimension at least `k + 1`, then `ρ ≤ σ_k(T)`. By Courant–Fischer for `T† T`, `W` contains
a vector `x ≠ 0` with `‖T x‖² ≤ σ_k(T)² ‖x‖²`. -/
theorem le_singularValues_of_mul_norm_le (T : E →ₗ[𝕜] F) {W : Submodule 𝕜 E} {k : ℕ}
    (hW : k + 1 ≤ finrank 𝕜 W) {ρ : ℝ} (hρ : ∀ y ∈ W, ρ * ‖y‖ ≤ ‖T y‖) :
    ρ ≤ T.singularValues k := by
  rcases le_or_gt ρ 0 with h0 | h0
  · exact h0.trans (T.singularValues_nonneg k)
  have hkE : k < finrank 𝕜 E := lt_of_lt_of_le (Nat.lt_succ_self k)
    (hW.trans (Submodule.finrank_le W))
  obtain ⟨x, hxW, hx0, hx⟩ := T.isSymmetric_adjoint_comp_self.exists_re_inner_le_of_le_finrank
    rfl ⟨k, hkE⟩ W hW
  rw [← T.sq_norm_apply, ← T.sq_singularValues_fin rfl ⟨k, hkE⟩] at hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : (ρ * ‖x‖) ^ 2 ≤ (T.singularValues k * ‖x‖) ^ 2 := by
    rw [mul_pow (T.singularValues k)]
    exact (pow_le_pow_left₀ (by positivity) (hρ x hxW) 2).trans hx
  have h2 := (pow_le_pow_iff_left₀ (by positivity)
    (mul_nonneg (T.singularValues_nonneg k) hxpos.le) two_ne_zero).mp h1
  exact le_of_mul_le_mul_right h2 hxpos

end LinearMap

namespace LeanDLRA

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Lower bound of `σ_{r-1}` from the core of a factorization.** If `X = U S Vᵀ` with `r > 0`
orthonormal columns in `U` and `V` and `ρ ‖w‖ ≤ ‖S w‖` for all `w`, then `ρ ≤ σ_{r-1}(X)`: on the
`r`-dimensional range of `V`, `‖X V w‖ = ‖S w‖ ≥ ρ ‖w‖ = ρ ‖V w‖`. This is the converse of
`LeanDLRA.WeylSingular.mul_norm_le_norm_toEuclideanLin_core`. -/
theorem SVD.le_singularValues_of_eq_mul {r : ℕ} (hr : 0 < r) {X : Matrix m n ℝ}
    {U : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hX : X = U * S * Vᵀ) {ρ : ℝ}
    (hS : ∀ w, ρ * ‖w‖ ≤ ‖toEuclideanLin S w‖) :
    ρ ≤ (toEuclideanLin X).singularValues (r - 1) := by
  have hinj : Function.Injective (toEuclideanLin V) := fun w w' h => by
    rw [← sub_eq_zero, ← norm_eq_zero, ← SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hV,
      map_sub, h, sub_self, norm_zero]
  have hW : r - 1 + 1 ≤ finrank ℝ (LinearMap.range (toEuclideanLin V)) := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine (toEuclideanLin X).le_singularValues_of_mul_norm_le hW fun y hy => ?_
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hy
  have hXV : toEuclideanLin X (toEuclideanLin V w) = toEuclideanLin U (toEuclideanLin S w) := by
    rw [hX, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLpLin_mul_same,
      ← toLpLin_mul_same, Matrix.mul_assoc (U * S), hV, Matrix.mul_one]
  rw [hXV, SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hU,
    SVD.norm_toEuclideanLin_of_transpose_mul_eq_one hV]
  exact hS w

open scoped LeanDLRA.Frobenius in
/-- **The truncated SVD of a matrix of rank at most `r` is the matrix itself**: by Eckart–Young,
`‖A - truncation A r‖ ≤ ‖A - A‖ = 0`. -/
theorem EckartYoung.truncation_eq_self {r : ℕ} {A : Matrix m n ℝ} (hA : A.rank ≤ r) :
    EckartYoung.truncation A r = A := by
  have h := EckartYoung.norm_sub_truncation_le A hA
  rw [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-! ### Examples -/

/-- `le_singularValues_of_mul_norm_le` with a nonzero bound: the identity of `ℝ²` is bounded below
by `1` on the whole space, so `1 ≤ σ₁(id)`. -/
example : (1 : ℝ) ≤ (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _).singularValues 1 :=
  LinearMap.le_singularValues_of_mul_norm_le _ (W := ⊤) (by simp) fun y _ => by simp

/-- `SVD.le_singularValues_of_eq_mul` with `U = V = 1` and the core `S = 2 • 1` (`1 × 1`):
`2 ≤ σ₀(1 (2 • 1) 1ᵀ)`. -/
example : (2 : ℝ) ≤
    (toEuclideanLin ((1 : Matrix (Fin 1) (Fin 1) ℝ) * ((2 : ℝ) • 1) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)).singularValues (1 - 1) := by
  refine SVD.le_singularValues_of_eq_mul one_pos (by simp) (by simp) rfl fun w => ?_
  have : toEuclideanLin ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) w = (2 : ℝ) • w := by
    rw [LinearEquiv.map_smul, toLpLin_one]
    rfl
  rw [this, norm_smul]
  simp

/-- `EckartYoung.truncation_eq_self` for a nonzero `2 × 2` matrix and `r = 2`. -/
example : EckartYoung.truncation (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ) 2 =
    !![1, 2; 2, 4] :=
  EckartYoung.truncation_eq_self ((Matrix.rank_le_card_width _).trans (by simp))

end LeanDLRA
