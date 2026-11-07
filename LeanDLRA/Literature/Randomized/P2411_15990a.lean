import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2411.15990: DEIM well-posedness (Algorithm 1, invertibility part)

Formalizes the greedy DEIM selection of Algorithm 1 in interpolation form (`IsDEIMStep`,
`IsDEIMSelection`) for a real matrix `M ∈ ℝ^{n×r}`. The main theorem
`det_submatrix_ne_zero_of_isDEIMSelection` shows that under full column rank every greedy
selection gives an invertible block `M(l,:)`. The example `isDEIMSelection_identity` shows the
hypotheses hold for the identity.

Not formalized, and left out on purpose:
* Existence of a greedy selection for every full-rank `M` (the algorithm never stalls). The
  invertibility part above holds for any selection that satisfies the step conditions, but the
  construction of such a selection by recursion over `j` is not proved here.
* The growth bound `‖M(l,:)⁻¹‖ ≤ (1+√(2n))^{r−1}/‖m₁‖_∞`. The text of arXiv 2411.15990 that was
  read (Algorithm 1 and the surrounding remarks) states no such bound and gives no proof; it only
  refers to the DEIM literature for accuracy guarantees. The header's citation is therefore not
  supported by this paper's text, and the bound is not stated here.
* Eqs. (21)-(23) (interpolatory projector-splitting integrator) and Eqs. (27)-(29) (basis-update
  and collocate scheme), which are not part of this module.

The norm used for "arg max" is the absolute value of the entry, as in the algorithm.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2411_15990

variable {n r : ℕ}

/-- Step `j` of the greedy DEIM selection (arXiv 2411.15990, Algorithm 1, steps 6–9), in
interpolation form. `l : Fin r → Fin n` are the selected rows and `c` is the coefficient vector
of the interpolant of column `j` on the columns `< j`, which must match column `j` at the rows
`l i` for `i < j`. The new index `l j` maximises the absolute residual `|M i j - (M c) i|`.
The coefficients are required to be supported on `k < j`; when the interpolation matrix
`M(l i, k)_{i,k<j}` is invertible (as it is for a DEIM selection, see
`det_submatrix_ne_zero_of_isDEIMSelection`), `c` is unique and equals the paper's
`M(l,1:j-1)⁻¹ m(l)`. -/
def IsDEIMStep (M : Matrix (Fin n) (Fin r) ℝ) (l : Fin r → Fin n) (j : Fin r) : Prop :=
  ∃ c : Fin r → ℝ, (∀ k, j ≤ k → c k = 0) ∧
    (∀ i, i < j → ∑ k, M (l i) k * c k = M (l i) j) ∧
    ∀ i : Fin n, |M i j - ∑ k, M i k * c k| ≤ |M (l j) j - ∑ k, M (l j) k * c k|

/-- A complete greedy DEIM selection: every step `j` is a `IsDEIMStep`. -/
def IsDEIMSelection (M : Matrix (Fin n) (Fin r) ℝ) (l : Fin r → Fin n) : Prop :=
  ∀ j, IsDEIMStep M l j

/-- **DEIM well-posedness (arXiv 2411.15990, Algorithm 1; the invertibility part).**
If `M ∈ ℝ^{n×r}` has full column rank and `l` is a greedy DEIM selection for `M`, then the
selected square block `M(l,:)` is invertible. The proof writes `M T = N` with `T = 1 - C`
unit upper triangular, `N(l a, b) = 0` for `a < b` and `N(l b, b) ≠ 0`. -/
theorem det_submatrix_ne_zero_of_isDEIMSelection (M : Matrix (Fin n) (Fin r) ℝ)
    (hM : ∀ v : Fin r → ℝ, M.mulVec v = 0 → v = 0) {l : Fin r → Fin n}
    (hl : IsDEIMSelection M l) : (M.submatrix l id).det ≠ 0 := by
  choose c hc0 hcint hcmax using hl
  -- the coefficient matrix `C k j = c j k` and the unit triangular matrix `T = 1 - C`
  set T : Matrix (Fin r) (Fin r) ℝ := 1 - Matrix.of fun k j => c j k with hT
  set N : Matrix (Fin n) (Fin r) ℝ := M * T with hN
  have hTent : ∀ k j, T k j = (if k = j then 1 else 0) - c j k := by
    intro k j
    simp [hT, Matrix.one_apply]
  have hNent : ∀ i j, N i j = M i j - ∑ k, M i k * c j k := by
    intro i j
    simp only [hN, Matrix.mul_apply, hTent, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
      mul_zero]
    simp
  have hTup : T.IsUpperTriangular := by
    intro i j hji
    have hji' : j < i := hji
    simp [hTent, hji'.ne', hc0 j i hji'.le]
  have hTdiag : ∀ j, T j j = 1 := by
    intro j
    simp [hTent, hc0 j j le_rfl]
  have hTdet : T.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hTup]
    simp [hTdiag]
  -- the interpolation property: `N(l a, b) = 0` for `a < b`
  have hzero : ∀ a b, a < b → N (l a) b = 0 := by
    intro a b hab
    rw [hNent, hcint b a hab, sub_self]
  -- the residual is not identically zero: column `b` of `T` is nonzero
  have hdiag : ∀ b, N (l b) b ≠ 0 := by
    intro b
    have hex : ∃ i, N i b ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ i, N i b = 0 := fun i => by
        by_contra h
        exact hcon ⟨i, h⟩
      have hv : M.mulVec (fun k => T k b) = 0 := by
        funext i
        have := hcon' i
        rw [hN, Matrix.mul_apply] at this
        simpa [Matrix.mulVec, dotProduct] using this
      have h0 := hM _ hv
      have := congrFun h0 b
      rw [hTdiag b] at this
      exact one_ne_zero this
    obtain ⟨i, hi⟩ := hex
    have hle := hcmax b i
    rw [← hNent, ← hNent] at hle
    intro hzb
    rw [hzb, abs_zero] at hle
    exact hi (abs_nonpos_iff.mp hle)
  -- `M(l,:) * T` is lower triangular with nonzero diagonal
  have hA : (M.submatrix l id * T).IsLowerTriangular := by
    intro a b hab
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    have := hzero a b hab
    rw [hN, Matrix.mul_apply] at this
    exact this
  have hdetA : (M.submatrix l id * T).det ≠ 0 := by
    rw [(hA.det_ne_zero_iff)]
    intro i
    have := hdiag i
    simpa [Matrix.diag, Matrix.mul_apply, hN] using this
  rw [Matrix.det_mul, hTdet, mul_one] at hdetA
  exact hdetA

/-- **Non-vacuity.** The identity matrix with `l = ![0, 1]` satisfies the DEIM step conditions
(the coefficients may be taken to be zero), so `IsDEIMSelection` is not vacuous. -/
theorem isDEIMSelection_identity : IsDEIMSelection (1 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] := by
  intro j
  refine ⟨0, fun k _ => rfl, fun i hi => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [Matrix.one_apply]
  · fin_cases j <;> fin_cases i <;> simp [Matrix.one_apply]

end LeanDLRA.Literature.P2411_15990
