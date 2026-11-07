import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2605.15382: Sylvester solver via a Schur reduction (Section 3)

This module formalises the direct Sylvester solver of Section 3 of arXiv:2605.15382 (Wang and Hu,
*Implicit dynamical tensor train approximation for kinetic equations with stiff Fokker-Planck
collisions*), in its matrix form, eqs. (3.1)-(3.4).

The paper solves `L₁ᵀ X + X L₂ = R` (eq. (3.2)) with `L₁ ∈ ℂ^{N×N}` large (tridiagonal in the
application) and `L₂ ∈ ℂ^{r×r}` small. It Schur-decomposes only `L₂ = U W Uᴴ`, solves the triangular
system `L₁ᵀ Z + Z W = E` column by column (eq. (3.4), Thomas algorithm), and recovers `X = Z Uᴴ`.
The file proves:

* `sylvester_iff_schur_reduced` (eq. (3.2) ⇔ (3.3)): the reduction to `Z = X U`, `E = R U` is an
  equivalence whenever `U` is unitary and `L₂ = U W Uᴴ`.
* `triangular_iff_columns` (eq. (3.3) ⇔ (3.4)): the column recurrence, where the `j`-th
  column solves `(L₁ᵀ + W_jj I) z_j = e_j - Σ_{k<j} W_kj z_k`.
* `triangular_sylvester_existsUnique`: if every shifted block `L₁ᵀ + W_jj I` is invertible, the
  triangular equation `A Z + Z W = E` has exactly one solution.
* `schur_sylvester_existsUnique`: under the same hypotheses, `L₁ᵀ X + X L₂ = R` has exactly
  one solution `X` for every `R`, so the Schur-based solver is well posed.
* an `example` after `schur_sylvester_existsUnique`: a non-diagonal
  instance (a permutation `U`, an upper triangular
  `W`, and a tridiagonal `L₁`) where all hypotheses hold, so the theorems are not vacuous.

Hypotheses. The complex Schur decomposition `L₂ = U W Uᴴ` (`U` unitary, `W` upper
triangular) is taken as an input. It is a classical theorem that Mathlib does not contain.
The shifted-block invertibility
`det (L₁ᵀ + W_jj I) ≠ 0` is a hypothesis; the paper gives no criterion for it, and the
disjoint-spectra criterion is not in Mathlib. No key step of the paper is assumed.

Left out. (a) The TT reductions of substeps 1, 3 and 5 to the matrix or tensor Sylvester equations
(eqs. (2.34), (2.36), (2.38)) need tensor-train contraction bookkeeping and are not formalised.
(b) The three-mode tensor Sylvester equation (eqs. (3.5)-(3.7)) needs n-mode products and is not
formalised. (c) The `O(N_v r²)` operation count and the real quasi-triangular variant are not
formalised.

Core definitions. This file uses no `LeanDLRA` definitions and adds none; it works with
Mathlib matrices over `ℂ`. The diagonalizable real solver `sylvester_iff_shifted_columns` in
`LeanDLRA/Stiff/ImplicitSolvability.lean` (`B Q = Q diag d`) is a different statement; the
triangular Schur form used here is not a special case of it.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2605_15382

variable {n r : ℕ}

/-- Entry `(i, j)` of `Z W` for an upper triangular `W` (`W k j = 0` when `j < k`). -/
private lemma mul_apply_upper (Z : Matrix (Fin n) (Fin r) ℂ) (W : Matrix (Fin r) (Fin r) ℂ)
    (hW : ∀ i j : Fin r, j < i → W i j = 0) (i : Fin n) (j : Fin r) :
    (Z * W) i j = Z i j * W j j + ∑ k ∈ Finset.Iio j, Z i k * W k j := by
  have hz : ∀ k ∈ (Finset.univ : Finset (Fin r)), k ∉ Finset.Iic j → Z i k * W k j = 0 :=
    fun k _ hk => by
      have hjk : j < k := by simpa [not_le] using hk
      rw [hW k j hjk, mul_zero]
  rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic j)) hz,
    ← Finset.Iio_insert, Finset.sum_insert (by simp)]

/-- **Schur reduction** (arXiv 2605.15382, eqs. (3.2) ⇔ (3.3)).  If `U` is unitary and
`L₂ = U W Uᴴ`, then `L₁ᵀ X + X L₂ = R` holds iff `Z = X U` satisfies `L₁ᵀ Z + Z W = R U`. -/
theorem sylvester_iff_schur_reduced (L1 : Matrix (Fin n) (Fin n) ℂ) (L2 : Matrix (Fin r) (Fin r) ℂ)
    (R X : Matrix (Fin n) (Fin r) ℂ) (U W : Matrix (Fin r) (Fin r) ℂ) (hU : Uᴴ * U = 1)
    (hL2 : L2 = U * W * Uᴴ) :
    L1ᵀ * X + X * L2 = R ↔ L1ᵀ * (X * U) + (X * U) * W = R * U := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  subst hL2
  have key : X * (U * W * Uᴴ) * U = X * U * W := by
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  have e1 : (L1ᵀ * X + X * (U * W * Uᴴ)) * U = L1ᵀ * (X * U) + X * U * W := by
    rw [Matrix.add_mul, key, Matrix.mul_assoc]
  have e2 : (L1ᵀ * (X * U) + X * U * W) * Uᴴ = L1ᵀ * X + X * (U * W * Uᴴ) := by
    simp only [Matrix.add_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]
  constructor
  · intro h
    rw [← e1, h]
  · intro h
    rw [← e2, h, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- **Column recurrence** (arXiv 2605.15382, eqs. (3.3) ⇔ (3.4)).  For upper triangular `W`, the
equation `A Z + Z W = E` holds iff each column satisfies
`(A + W_jj I) z_j = e_j - Σ_{k<j} W_kj z_k`. -/
theorem triangular_iff_columns (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin r) (Fin r) ℂ)
    (hW : ∀ i j : Fin r, j < i → W i j = 0) (Z E : Matrix (Fin n) (Fin r) ℂ) :
    A * Z + Z * W = E ↔
      ∀ j : Fin r, (A + W j j • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ (fun i => Z i j) =
        (fun i => E i j) - ∑ k ∈ Finset.Iio j, W k j • (fun i => Z i k) := by
  constructor
  · intro h j
    funext i
    have h' := congrFun (congrFun h i) j
    rw [Matrix.add_apply, mul_apply_upper Z W hW] at h'
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.mulVec, dotProduct] at h' ⊢
    have hs : ∑ k ∈ Finset.Iio j, Z i k * W k j = ∑ k ∈ Finset.Iio j, W k j * Z i k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linear_combination h' - hs
  · intro h
    ext i j
    have hj := congrFun (h j) i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hj
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct] at hj ⊢
    rw [Matrix.add_apply, mul_apply_upper Z W hW]
    simp only [Matrix.mul_apply]
    have hs : ∑ k ∈ Finset.Iio j, Z i k * W k j = ∑ k ∈ Finset.Iio j, W k j * Z i k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    linear_combination hj + hs

/-- A solution of the homogeneous triangular equation vanishes, when all shifted blocks are
invertible. -/
private lemma eq_zero_of_triangular (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin r) (Fin r) ℂ)
    (hW : ∀ i j : Fin r, j < i → W i j = 0)
    (hA : ∀ j : Fin r, IsUnit (A + W j j • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
    (Z : Matrix (Fin n) (Fin r) ℂ) (hZ : A * Z + Z * W = 0) : Z = 0 := by
  have hcol := (triangular_iff_columns A W hW Z 0).mp hZ
  have key : ∀ m : ℕ, ∀ j : Fin r, j.val < m → (fun i => Z i j) = 0 := by
    intro m
    induction m with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro j hj
      have hprev : ∑ k ∈ Finset.Iio j, W k j • (fun i => Z i k) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hkj : k.val < j.val := Fin.lt_def.mp (Finset.mem_Iio.mp hk)
        rw [ih k (by omega), smul_zero]
      have h := hcol j
      rw [hprev, sub_zero] at h
      have hunit : IsUnit (A + W j j • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (hA j)
      apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
      rw [h, Matrix.mulVec_zero]
      funext i
      simp
  ext i j
  exact congrFun (key (j.val + 1) j (Nat.lt_succ_self _)) i

/-- **Well-posedness of the triangular Sylvester equation** (arXiv 2605.15382, Section 3,
eq. (3.4)).
If `W` is upper triangular and every shifted block `A + W_jj I` is invertible, then `A Z + Z W = E`
has exactly one solution for every `E`. -/
theorem triangular_sylvester_existsUnique (A : Matrix (Fin n) (Fin n) ℂ)
    (W : Matrix (Fin r) (Fin r) ℂ) (hW : ∀ i j : Fin r, j < i → W i j = 0)
    (hA : ∀ j : Fin r, IsUnit (A + W j j • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
    (E : Matrix (Fin n) (Fin r) ℂ) : ∃! Z : Matrix (Fin n) (Fin r) ℂ, A * Z + Z * W = E := by
  let f : Matrix (Fin n) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin r) ℂ :=
    { toFun := fun Z => A * Z + Z * W
      map_add' := fun X Y => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c X => by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add,
        RingHom.id_apply] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro Z hZ
    exact eq_zero_of_triangular A W hW hA Z hZ
  obtain ⟨Z, hZ⟩ := LinearMap.injective_iff_surjective.mp hinj E
  exact ⟨Z, hZ, fun Y hY => hinj (show f Y = f Z from hY.trans hZ.symm)⟩

/-- **Well-posedness of the Schur-based solver** (arXiv 2605.15382, Section 3, eqs. (3.1)-(3.4)).
Let `L₂ = U W Uᴴ` with `U` unitary and `W` upper triangular, and assume every shifted block
`L₁ᵀ + W_jj I` is invertible.  Then `L₁ᵀ X + X L₂ = R` has exactly one solution for every `R`. -/
theorem schur_sylvester_existsUnique (L1 : Matrix (Fin n) (Fin n) ℂ) (L2 : Matrix (Fin r) (Fin r) ℂ)
    (U W : Matrix (Fin r) (Fin r) ℂ) (hU : Uᴴ * U = 1) (hL2 : L2 = U * W * Uᴴ)
    (hW : ∀ i j : Fin r, j < i → W i j = 0)
    (hA : ∀ j : Fin r, IsUnit (L1ᵀ + W j j • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
    (R : Matrix (Fin n) (Fin r) ℂ) : ∃! X : Matrix (Fin n) (Fin r) ℂ, L1ᵀ * X + X * L2 = R := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  obtain ⟨Z, hZ, hZu⟩ := triangular_sylvester_existsUnique L1ᵀ W hW hA (R * U)
  have hZU : Z * Uᴴ * U = Z := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  refine ⟨Z * Uᴴ, ?_, fun X hX => ?_⟩
  · dsimp only
    rw [sylvester_iff_schur_reduced L1 L2 R (Z * Uᴴ) U W hU hL2, hZU]
    exact hZ
  · have hX' := (sylvester_iff_schur_reduced L1 L2 R X U W hU hL2).mp hX
    have hXU : X * U = Z := hZu (X * U) hX'
    calc X = X * U * Uᴴ := by rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
      _ = Z * Uᴴ := by rw [hXU]

/-- **Non-vacuity instance** of `schur_sylvester_existsUnique`: `U` is the swap permutation,
`W = [[7, 1], [0, 5]]` is upper triangular, so `L₂ = [[5, 0], [1, 7]]`, and `L₁` is the tridiagonal
matrix `[[-2, 1], [1, -2]]`.  The shifted blocks are `[[5, 1], [1, 5]]` (det 24) and
`[[3, 1], [1, 3]]` (det 8). -/
example (R : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃! X : Matrix (Fin 2) (Fin 2) ℂ,
      !![-2, 1; 1, -2]ᵀ * X + X * !![5, 0; 1, 7] = R := by
  refine schur_sylvester_existsUnique (L1 := !![-2, 1; 1, -2]) (L2 := !![5, 0; 1, 7])
    (U := !![0, 1; 1, 0]) (W := !![7, 1; 0, 5]) ?_ ?_ ?_ ?_ R
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j
    fin_cases j <;> simp [Matrix.det_fin_two] <;> norm_num

end LeanDLRA.Literature.P2605_15382
