import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Classical.EckartYoung

/-!
# CUR for implicit DLRA of random PDEs (arXiv 2408.16591)

The paper discretises a random PDE as the matrix ODE `dV/dt = F(V)` (rows: spatial degrees of
freedom, columns: samples `ξ_j`, `F` acting column by column), advances it by implicit Euler,
`V^k = V̂^{k-1} + Δt F(V^k)`, and replaces the rank-`r` SVD truncation of `V^k` by the cross (CUR)
approximation `V̂^k = CUR(V^k) = V^k(:,s) V^k(p,s)⁻¹ V^k(p,:)` with DEIM-selected rows `p` and
columns `s` (TDB-CUR).  This module formalises the mathematical claims of its Section 3: the rank
growth of the implicit iterates for quadratic nonlinearities (Sec. 3.2), the spectral-norm CUR
error bound (19) and the DEIM growth bound (20), the interpolation property of CUR with and
without row oversampling (Remark 1, eqs. (21)–(22)), and the claim that CUR is a residual
collocation method (Sec. 3.3.1).  The collocation claim is false as stated; eq. (19) holds as
printed but fails under a second reading the text suggests.  Both failures are shown by explicit
counterexamples, and the correct versions are proved.

## Main results

* Sec. 3.2: `rank_colBilin_le`, `rank_hadamard_le` (`rank (A ⊙ B) ≤ rank A · rank B`),
  `rank_quadField_le`, `rank_burgersField_le` (`rank F(V) ≤ r + r²` for column-wise quadratic
  `F`, e.g. Burgers), `rank_picard_le` (iterates of rank `≤ 3^{2^i-1} r^{2^i}`),
  `rank_sub_le_two_mul` (difference of two rank-`r` iterates has rank `≤ 2r`), and
  `rank_hadamard_self_example` (the rank does grow, `2 → 3`).
* Eq. (19): `specNorm_sub_cur_le` (spectral norm, exactly the printed constant
  `c = min {η_r (1 + η_c), η_c (1 + η_r)}` and `σ̂_{r+1}`), with the sharper one-sided forms
  `specNorm_sub_cur_le_left/right` (`‖V - CUR(V)‖₂ ≤ η_r ‖(I - UUᵀ)V‖₂`); the key identity is
  `cur_eq_obliqueProj_mul` (`CUR(V) = 𝒫_U V` for the DEIM projector of a basis `U` of the selected
  columns) and the spectral DEIM bound `specNorm_sub_obliqueProj_mul_le`.
* Eq. (20): `deim_growth_bound` (`‖U(p,:)⁻¹‖₂ ≤ (1 + √N)^{r-1}/‖u_1‖_∞` for a DEIM selection,
  `IsDEIM`) and `eq20_deim_bound` (the printed factor `1 + √(2N)`); `cur_deim_error_le` combines
  (19) and (20).
* Remark 1: `cur_submatrix_rows`, `cur_submatrix_cols` (no oversampling), `qr_cur_eq`
  (eqs. (21)–(22) equal the pivot form), `lsq_cur_submatrix_cols` (oversampled least squares still
  reproduces the columns), `lsq_cur_rows_ne` (but not the rows).
* Sec. 3.3.1: `cur_residual_cols_eq_zero` (column-wise `F`: zero residual on the selected
  columns), `cur_residual_eq_zero` (also on the selected rows if `F` is row-local there),
  `cur_eq_self_of_rank_le` (CUR is exact on rank-`r` matrices) and `residual_collocation_iff`
  (a rank-`r` matrix has zero residual on the selected rows and columns iff it is `CUR(V^k)`,
  when the implicit equation is uniquely solvable on columns and selected rows).

## False as stated, or under one reading

* Eq. (19) as printed, with `U`, `Y` orthonormal bases spanning `V(:,s)` and `V(p,:)ᵀ`, holds
  (`specNorm_sub_cur_le`).  The text also suggests a second reading, with `U`, `Y` the exact
  singular vectors of `V` (it says that `p`, `s` are DEIM indices of the exact or approximate
  singular vectors and that then `σ̂_{r+1} = σ_{r+1}`; eq. (20) bounds `η_r` through the first
  singular vector).  Under that reading the bound fails: `eq19_false_for_singular_vectors`, a
  `2 × 2` example with `‖V - CUR(V)‖₂ ≈ 712 > c σ_2 ≤ 633`, where `u` does not span `V(:,s)`.
* Sec. 3.3.1 (false as stated), "the CUR approach is equivalent to a residual collocation
  method": with spatial coupling in `F` the residual of `CUR(V^k)` does not vanish on the
  selected rows (`cur_residual_row_ne_zero`, every admissible `1 × 1` cross of a `2 × 2`
  parametric example).  It vanishes on the selected columns for every column-wise `F`, and on the
  rows when `F` is row-local on `p`.  (The paper's Algorithm 1 instead enforces the row equations
  with neighbouring rows estimated from the correction basis, eqs. (33)–(36), which is not
  `CUR(V^k)`.)

## Differences and omissions

* Sec. 3.2 speaks of Newton iterates and of rank `O(r^{2i})`; the rank bound is proved for the
  fixed-point iteration, where it grows like `r^{2^i}`.  For Newton the correction solves
  column-dependent linear systems and no rank bound in `r` follows from this argument.
* `Q(p',:)⁺` is written as `(Q(p',:)ᵀ Q(p',:))⁻¹ Q(p',:)ᵀ`, the pseudo-inverse of a matrix of full
  column rank.  The DEIM selection is characterised by the greedy maximality of the
  interpolation residual (`IsDEIM`), not by an executable algorithm.
* Not formalised: Algorithm 1 with the correction basis `U_δ` (eqs. (26)–(36)), the multistep and
  DIRK residuals (eqs. (37)–(42)) and any time-integration error analysis (the paper gives none).
  The library already contains the algebraic core `Sᵀ (X - 𝒫 X) = 0`
  (`LeanDLRA.ObliqueBUG.transpose_mul_residual_eq_zero`), which is not repeated.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix TensorProduct

namespace LeanDLRA.Literature.P2408_16591

open Matrix Curvature

section RankGrowth

variable {m m' n s : Type*} [Fintype s]

/-- The matrix whose `j`-th column is `T (A_{:j}, B_{:j})`, for a bilinear map `T`
(column-wise evaluation of a bilinear nonlinearity, arXiv 2408.16591, Sec. 3.2). -/
def colBilin (T : (m → ℝ) →ₗ[ℝ] (m' → ℝ) →ₗ[ℝ] (n → ℝ)) (A : Matrix m s ℝ)
    (B : Matrix m' s ℝ) : Matrix n s ℝ :=
  Matrix.of fun i j => T (A.col j) (B.col j) i

/-- **Rank of a column-wise bilinear map** (arXiv 2408.16591, Sec. 3.2, the mechanism behind
`rank F(V̂) = O(r²)`): `rank [T(a_j, b_j)]_j ≤ rank A · rank B`.  The columns lie in the image of
`span(A) ⊗ span(B)` under `T`. -/
theorem rank_colBilin_le (T : (m → ℝ) →ₗ[ℝ] (m' → ℝ) →ₗ[ℝ] (n → ℝ))
    (A : Matrix m s ℝ) (B : Matrix m' s ℝ) : (colBilin T A B).rank ≤ A.rank * B.rank := by
  classical
  have hle : LinearMap.range (colBilin T A B).mulVecLin ≤
      Submodule.map₂ T (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin) := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hA : A.col j ∈ LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin]; exact Submodule.subset_span ⟨j, rfl⟩
    have hB : B.col j ∈ LinearMap.range B.mulVecLin := by
      rw [Matrix.range_mulVecLin]; exact Submodule.subset_span ⟨j, rfl⟩
    have heq : (colBilin T A B).col j = T (A.col j) (B.col j) := by ext i; rfl
    rw [heq]
    exact Submodule.apply_mem_map₂ T hA hB
  rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl] at hle
  calc (colBilin T A B).rank
      = Module.finrank ℝ (LinearMap.range (colBilin T A B).mulVecLin) := rfl
    _ ≤ Module.finrank ℝ (LinearMap.range (TensorProduct.lift T ∘ₗ
          TensorProduct.mapIncl (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))) :=
      Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (LinearMap.range A.mulVecLin ⊗[ℝ] LinearMap.range B.mulVecLin) :=
      LinearMap.finrank_range_le _
    _ = A.rank * B.rank := by rw [Module.finrank_tensorProduct]; rfl

omit [Fintype s] in
/-- The Hadamard product is the column-wise evaluation of pointwise multiplication.
(arXiv 2408.16591, Sec. 3.2.) -/
theorem colBilin_mul (A B : Matrix m s ℝ) :
    colBilin (LinearMap.mul ℝ (m → ℝ)) A B = A ⊙ B := by
  ext i j; simp [colBilin]

/-- **Hadamard-product rank bound** (arXiv 2408.16591, Sec. 3.2; the bound the header asked
for): `rank (A ⊙ B) ≤ rank A · rank B`. -/
theorem rank_hadamard_le (A B : Matrix m s ℝ) : (A ⊙ B).rank ≤ A.rank * B.rank := by
  rw [← colBilin_mul]; exact rank_colBilin_le _ _ _


section Basic

/-- `rank (c • X) ≤ rank X` (auxiliary). (arXiv 2408.16591, Sec. 3.2.) -/
theorem rank_smul_le (c : ℝ) (X : Matrix m s ℝ) : (c • X).rank ≤ X.rank := by
  classical
  have h : c • X = X * (c • (1 : Matrix s s ℝ)) := by rw [Matrix.mul_smul, Matrix.mul_one]
  rw [h]; exact rank_mul_le_left _ _

/-- `rank (X - Y) ≤ rank X + rank Y` (auxiliary). (arXiv 2408.16591, Sec. 3.2.) -/
theorem rank_sub_le (X Y : Matrix m s ℝ) : (X - Y).rank ≤ X.rank + Y.rank := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y]
  exact (EckartYoung.rank_add_le _ _).trans (add_le_add le_rfl (rank_smul_le _ _))

/-- The fixed-point (Picard) iteration `V_{i+1} = V̂^{k-1} + Δt F(V_i)`, `V_0 = V̂^{k-1}`, for
the implicit Euler equation (16) of arXiv 2408.16591. -/
def picard (F : Matrix m s ℝ → Matrix m s ℝ) (Vprev : Matrix m s ℝ) (Δt : ℝ) :
    ℕ → Matrix m s ℝ
  | 0 => Vprev
  | i + 1 => Vprev + Δt • F (picard F Vprev Δt i)

omit [Fintype s] in
/-- `b_{i+1} = 3 b_i²` for `b_i = 3^{2^i - 1} r^{2^i}` (auxiliary). (arXiv 2408.16591, Sec. 3.2.) -/
lemma rankBound_succ (r i : ℕ) :
    3 ^ (2 ^ (i + 1) - 1) * r ^ (2 ^ (i + 1)) = 3 * (3 ^ (2 ^ i - 1) * r ^ (2 ^ i)) ^ 2 := by
  have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h2 : 2 ^ (i + 1) - 1 = 2 * (2 ^ i - 1) + 1 := by rw [pow_succ]; omega
  rw [h2, pow_succ, pow_succ, pow_mul, mul_pow, ← pow_mul, ← pow_mul]
  ring

/-- **Rank growth of the iterates** (arXiv 2408.16591, Sec. 3.2): if the field maps rank `ρ` to
rank `≤ ρ + ρ²` (as every column-wise quadratic field does, `rank_quadField_le`) and
`rank V̂^{k-1} ≤ r`, the `i`-th iterate has rank `≤ 3^{2^i - 1} r^{2^i}`, i.e. the rank bound grows
like `r^{2^i}`.  Difference from the paper: proved for the fixed-point iteration; the paper
speaks of Newton iterates (whose correction solves column-dependent linear systems, so that no
rank bound in terms of `r` follows from this argument), and writes `O(r^{2i})`. -/
theorem rank_picard_le {F : Matrix m s ℝ → Matrix m s ℝ} {Vprev : Matrix m s ℝ} {Δt : ℝ}
    {r : ℕ} (hF : ∀ V, (F V).rank ≤ V.rank + V.rank * V.rank) (hV : Vprev.rank ≤ r) (i : ℕ) :
    (picard F Vprev Δt i).rank ≤ 3 ^ (2 ^ i - 1) * r ^ (2 ^ i) := by
  induction i with
  | zero => simpa [picard] using hV
  | succ i ih =>
    set b := 3 ^ (2 ^ i - 1) * r ^ (2 ^ i) with hb
    have hstep : (picard F Vprev Δt (i + 1)).rank ≤ r + (b + b * b) := by
      calc (picard F Vprev Δt (i + 1)).rank
          ≤ Vprev.rank + (Δt • F (picard F Vprev Δt i)).rank := EckartYoung.rank_add_le _ _
        _ ≤ r + (b + b * b) :=
          add_le_add hV ((rank_smul_le _ _).trans ((hF _).trans
            (add_le_add ih (Nat.mul_le_mul ih ih))))
    rw [rankBound_succ, ← hb]
    refine hstep.trans ?_
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have : b = 0 := by rw [hb]; simp
      simp [this]
    · have h1 : r ≤ r ^ (2 ^ i) := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp Nat.one_le_two_pow) r
      have h3 : 1 ≤ 3 ^ (2 ^ i - 1) := Nat.one_le_pow _ _ (by norm_num)
      have hrb : r ≤ b := h1.trans (Nat.le_mul_of_pos_left _ h3)
      have hb1 : 1 ≤ b := hr.trans_le hrb
      nlinarith

/-- **Difference of iterates** (arXiv 2408.16591, Sec. 3.2): the difference of two rank-`≤ r`
matrices has rank `≤ 2 r`. -/
theorem rank_sub_le_two_mul {X Y : Matrix m s ℝ} {r : ℕ} (hX : X.rank ≤ r)
    (hY : Y.rank ≤ r) :
    (X - Y).rank ≤ 2 * r := by
  have := rank_sub_le X Y; omega

end Basic

section Quadratic

variable [Fintype m]

/-- A **column-wise quadratic field** `F(V) = L V + [T(v_j, v_j)]_j` (linear part `L`, bilinear
part `T`): the semi-discretisation of a random PDE with quadratic nonlinearity, column `j` being
the sample `ξ_j` (arXiv 2408.16591, Sec. 2 and 3.2). -/
def quadField (L : Matrix m m ℝ) (T : (m → ℝ) →ₗ[ℝ] (m → ℝ) →ₗ[ℝ] (m → ℝ))
    (V : Matrix m s ℝ) : Matrix m s ℝ :=
  L * V + colBilin T V V

/-- **`rank F(V̂) = O(r²)` for quadratic `F`** (arXiv 2408.16591, Sec. 3.2):
`rank (L V + [T(v_j, v_j)]_j) ≤ rank V + (rank V)²`. -/
theorem rank_quadField_le (L : Matrix m m ℝ) (T : (m → ℝ) →ₗ[ℝ] (m → ℝ) →ₗ[ℝ] (m → ℝ))
    (V : Matrix m s ℝ) : (quadField L T V).rank ≤ V.rank + V.rank * V.rank :=
  (EckartYoung.rank_add_le _ _).trans
    (add_le_add (rank_mul_le_right _ _) (rank_colBilin_le _ _ _))

/-- The semi-discrete viscous Burgers field `F(V) = ν D₂ V - V ⊙ (D₁ V)`
(`v_t = ν v_xx - v v_x` with difference matrices `D₁ ≈ ∂ₓ`, `D₂ ≈ ∂ₓₓ`, applied to every
sample column; the paper's example of a quadratic nonlinearity). (arXiv 2408.16591, Sec. 3.2.) -/
def burgersField (ν : ℝ) (D₁ D₂ : Matrix m m ℝ) (V : Matrix m s ℝ) : Matrix m s ℝ :=
  ν • (D₂ * V) - V ⊙ (D₁ * V)

/-- **Burgers: `rank F(V) ≤ r + r²`** (arXiv 2408.16591, Sec. 3.2). -/
theorem rank_burgersField_le (ν : ℝ) (D₁ D₂ : Matrix m m ℝ) (V : Matrix m s ℝ) :
    (burgersField ν D₁ D₂ V).rank ≤ V.rank + V.rank * V.rank :=
  (rank_sub_le _ _).trans (add_le_add ((rank_smul_le _ _).trans (rank_mul_le_right _ _))
    ((rank_hadamard_le _ _).trans (Nat.mul_le_mul le_rfl (rank_mul_le_right _ _))))

end Quadratic

/-- **The rank does grow** (arXiv 2408.16591, Sec. 3.2, non-vacuity): `V = (1 + x_i y_j)` with
`x = y = (0, 1, 2)` has rank `≤ 2`, but its Hadamard square has rank `3`. -/
theorem rank_hadamard_self_example :
    (!![1, 1, 1; 1, 2, 3; 1, 3, 5] : Matrix (Fin 3) (Fin 3) ℝ).rank ≤ 2 ∧
      ((!![1, 1, 1; 1, 2, 3; 1, 3, 5] : Matrix (Fin 3) (Fin 3) ℝ) ⊙
        !![1, 1, 1; 1, 2, 3; 1, 3, 5]).rank = 3 := by
  constructor
  · have h : (!![1, 1, 1; 1, 2, 3; 1, 3, 5] : Matrix (Fin 3) (Fin 3) ℝ) =
        (!![1, 0; 1, 1; 1, 2] : Matrix (Fin 3) (Fin 2) ℝ) *
          (!![1, 1, 1; 0, 1, 2] : Matrix (Fin 2) (Fin 3) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    rw [h]
    exact (rank_mul_le_left _ _).trans (rank_le_width _)
  · have hd : IsUnit ((!![1, 1, 1; 1, 2, 3; 1, 3, 5] : Matrix (Fin 3) (Fin 3) ℝ) ⊙
        !![1, 1, 1; 1, 2, 3; 1, 3, 5]) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_three]
      simp [Matrix.hadamard]
      norm_num
    simpa using rank_of_isUnit _ hd

end RankGrowth

section CUR

variable {m n k : Type*}

open scoped Matrix.Norms.L2Operator in
/-- `‖c A‖₂ = |c| ‖A‖₂`. (arXiv 2408.16591, eq. (19).) -/
theorem specNorm_smul {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (c : ℝ)
    (A : Matrix m n ℝ) : specNorm (c • A) = |c| * specNorm A := by
  rw [specNorm_eq_l2, specNorm_eq_l2, norm_smul, Real.norm_eq_abs]

/-- The inverse of a nonzero `1 × 1` matrix. (arXiv 2408.16591, eq. (19).) -/
theorem inv_fin_one {a : ℝ} (ha : a ≠ 0) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![a⁻¹] :=
  Matrix.inv_eq_right_inv (by ext i j; fin_cases i; fin_cases j; simp [ha])


/-- The **CUR (cross) approximation** of eq. (18) of arXiv 2408.16591:
`CUR(V) = V(:,s) V(p,s)⁻¹ V(p,:)`. -/
noncomputable def cur [Fintype k] [DecidableEq k] (V : Matrix m n ℝ) (p : k → m) (s : k → n) :
    Matrix m n ℝ :=
  V.submatrix id s * (V.submatrix p s)⁻¹ * V.submatrix p id

/-- The selection matrix `I(:,p)` (columns `p` of the identity). (arXiv 2408.16591, eq. (19).) -/
def sel [DecidableEq m] (p : k → m) : Matrix m k ℝ := (1 : Matrix m m ℝ).submatrix id p

/-- `I(:,p)ᵀ V = V(p,:)`. (arXiv 2408.16591, eq. (19).) -/
theorem sel_transpose_mul [Fintype m] [DecidableEq m] (p : k → m) (V : Matrix m n ℝ) :
    (sel p)ᵀ * V = V.submatrix p id := by
  ext a j; simp [sel, Matrix.mul_apply, Matrix.one_apply]

/-- `V I(:,s) = V(:,s)`. (arXiv 2408.16591, eq. (19).) -/
theorem mul_sel [Fintype n] [DecidableEq n] (V : Matrix m n ℝ) (s : k → n) :
    V * sel s = V.submatrix id s := by
  ext i a; simp [sel, Matrix.mul_apply, Matrix.one_apply]

/-- A selection with distinct indices has orthonormal columns. (arXiv 2408.16591, eq. (19).) -/
theorem sel_orthonormal [Fintype m] [DecidableEq m] [DecidableEq k] {p : k → m}
    (hp : Function.Injective p) :
    (sel p)ᵀ * sel p = 1 := by
  rw [sel_transpose_mul]
  ext a b; simp [sel, Matrix.one_apply, hp.eq_iff]

/-- Distinct indices are forced by an invertible cross: if `V(p,s)` is invertible, `p` is
injective. (arXiv 2408.16591, eq. (19).) -/
theorem injective_of_isUnit_det [Fintype k] [DecidableEq k] {V : Matrix m n ℝ} {p : k → m}
    {s : k → n} (hW : IsUnit (V.submatrix p s).det) : Function.Injective p := by
  intro a b hab
  by_contra hne
  exact hW.ne_zero (Matrix.det_zero_of_row_eq hne (by ext j; simp [hab]))

/-- If `V(p,s)` is invertible, `s` is injective. (arXiv 2408.16591, eq. (19).) -/
theorem injective_of_isUnit_det' [Fintype k] [DecidableEq k] {V : Matrix m n ℝ} {p : k → m}
    {s : k → n} (hW : IsUnit (V.submatrix p s).det) : Function.Injective s := by
  have hWt : IsUnit (Vᵀ.submatrix s p).det := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact hW
  exact injective_of_isUnit_det hWt

/-- `cur Vᵀ s p = (cur V p s)ᵀ`. (arXiv 2408.16591, eq. (19).) -/
theorem cur_transpose [Fintype k] [DecidableEq k] (V : Matrix m n ℝ) (p : k → m) (s : k → n) :
    cur Vᵀ s p = (cur V p s)ᵀ := by
  simp only [cur, Matrix.transpose_mul, ← Matrix.transpose_submatrix,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

/-- **CUR is a one-sided interpolatory projection.**  If the orthonormal `U` spans the selected
columns (`V(:,s) = U M`) and the cross `V(p,s)` is invertible, then `U(p,:)` is invertible and
`CUR(V) = 𝒫_U V` with the DEIM projector `𝒫_U = U (U(p,:))⁻¹ I(p,:)`.
(arXiv 2408.16591, eq. (19).) -/
theorem cur_eq_obliqueProj_mul [Fintype m] [Fintype k] [DecidableEq k] [DecidableEq m]
    {V : Matrix m n ℝ} {p : k → m} {s : k → n} {U : Matrix m k ℝ}
    (hW : IsUnit (V.submatrix p s).det)
    (hC : ∃ M : Matrix k k ℝ, V.submatrix id s = U * M) :
    IsUnit ((sel p)ᵀ * U).det ∧ cur V p s = obliqueProj U (sel p) * V := by
  obtain ⟨M, hM⟩ := hC
  have hWeq : V.submatrix p s = (sel p)ᵀ * U * M := by
    rw [Matrix.mul_assoc, ← hM, sel_transpose_mul]; rfl
  have hdet : IsUnit (((sel p)ᵀ * U).det * M.det) := by
    rw [← Matrix.det_mul, ← hWeq]; exact hW
  have hSU : IsUnit ((sel p)ᵀ * U).det := isUnit_of_mul_isUnit_left hdet
  have hMu : IsUnit M.det := isUnit_of_mul_isUnit_right hdet
  refine ⟨hSU, ?_⟩
  rw [cur, hWeq, hM, Matrix.mul_inv_rev, obliqueProj, ← sel_transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc M M⁻¹, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul]

/-- The matrix projectors `𝒫 = U (SᵀU)⁻¹ Sᵀ` and `U Uᵀ` act on `EuclideanSpace` as an
oblique projector onto an orthogonal one. (arXiv 2408.16591, eq. (19).) -/
theorem isObliqueProj_euclid [Fintype m] [Fintype k] [DecidableEq k] [DecidableEq m]
    {U S : Matrix m k ℝ} (hU : Uᵀ * U = 1) (hSU : IsUnit (Sᵀ * U).det) :
    IsObliqueProj (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (obliqueProj U S)))
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (U * Uᵀ))) :=
  { orth := (isOrthProjMat_mul_transpose hU).toIsOrthProj
    fix := fun x => by
      change Matrix.toEuclideanLin _ (Matrix.toEuclideanLin _ x) = Matrix.toEuclideanLin _ x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, obliqueProj_mul_proj hSU]
    range := fun x => by
      change Matrix.toEuclideanLin _ (Matrix.toEuclideanLin _ x) = Matrix.toEuclideanLin _ x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, proj_mul_obliqueProj hU] }

/-- `A ↦ (x ↦ A x)` (as a continuous linear map on `EuclideanSpace`) is injective.
(arXiv 2408.16591, eq. (19).) -/
theorem toCLM_toEuclideanLin_injective {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℝ}
    (h : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) =
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)) : A = B :=
  Matrix.toEuclideanLin.injective (LinearMap.toContinuousLinearMap.injective h)

/-- The (vector) DEIM bound in the **spectral norm**: for orthonormal `U` (`k` nonempty) and an
interpolatory projector `𝒫 = U (SᵀU)⁻¹ Sᵀ`,
`‖X - 𝒫 X‖₂ ≤ ‖𝒫‖₂ ‖X - U Uᵀ X‖₂`. (arXiv 2408.16591, eq. (19).) -/
theorem specNorm_sub_obliqueProj_mul_le [Fintype m] [Fintype n] [Fintype k] [DecidableEq k]
    [DecidableEq m] [DecidableEq n] [Nonempty k]
    {U S : Matrix m k ℝ} (hU : Uᵀ * U = 1) (hSU : IsUnit (Sᵀ * U).det) (X : Matrix m n ℝ) :
    specNorm (X - obliqueProj U S * X) ≤
      specNorm (obliqueProj U S) * specNorm (X - U * Uᵀ * X) := by
  set P : EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (obliqueProj U S)) with hPdef
  set Q : EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (U * Uᵀ)) with hQdef
  have hPQ : IsObliqueProj P Q := isObliqueProj_euclid hU hSU
  have hQ0 : Q ≠ 0 := by
    intro hQ
    have h2 : U * Uᵀ = 0 := toCLM_toEuclideanLin_injective (by rw [← hQdef, hQ]; simp)
    have h3 : Uᵀ * (U * Uᵀ) * U = 1 := by
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul, hU]
    rw [h2, Matrix.mul_zero, Matrix.zero_mul] at h3
    have := congrFun (congrFun h3 (Classical.arbitrary k)) (Classical.arbitrary k)
    simp at this
  refine specNorm_le_of (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) fun x => ?_
  set y := Matrix.toEuclideanLin X x
  have e1 : Matrix.toEuclideanLin (X - obliqueProj U S * X) x = y - P y := by
    simp only [map_sub, LinearMap.sub_apply, y, hPdef, LinearMap.coe_toContinuousLinearMap',
      Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  have e2 : Matrix.toEuclideanLin (X - U * Uᵀ * X) x = y - Q y := by
    simp only [map_sub, LinearMap.sub_apply, y, hQdef, LinearMap.coe_toContinuousLinearMap',
      Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [e1]
  calc ‖y - P y‖ ≤ ‖P‖ * ‖y - Q y‖ := hPQ.norm_sub_le_opNorm hQ0 y
    _ = specNorm (obliqueProj U S) * ‖Matrix.toEuclideanLin (X - U * Uᵀ * X) x‖ := by
      rw [e2]; rfl
    _ ≤ specNorm (obliqueProj U S) * (specNorm (X - U * Uᵀ * X) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- Szyld's inequality `‖𝒫‖₂ ≤ ‖I - 𝒫‖₂` in the spectral norm, for `U Uᵀ ≠ I` (from the
abstract `IsObliqueProj.opNorm_le_opNorm_one_sub`). (arXiv 2408.16591, eq. (19).) -/
theorem specNorm_obliqueProj_le_one_sub [Fintype m] [Fintype k] [DecidableEq k] [DecidableEq m]
    {U S : Matrix m k ℝ} (hU : Uᵀ * U = 1) (hSU : IsUnit (Sᵀ * U).det) (hQ : U * Uᵀ ≠ 1) :
    specNorm (obliqueProj U S) ≤ specNorm (1 - obliqueProj U S) := by
  have hQ1 : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (U * Uᵀ)) ≠ 1 := by
    intro h
    exact hQ (toCLM_toEuclideanLin_injective (by rw [h]; ext x; simp))
  have h := (isObliqueProj_euclid (S := S) hU hSU).opNorm_le_opNorm_one_sub hQ1
  have e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (1 - obliqueProj U S)) =
      1 - LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (obliqueProj U S)) := by
    ext x; simp
  unfold specNorm
  rw [e]; exact h

/-- **Sharp one-sided form of eq. (19)** (arXiv 2408.16591): if the orthonormal `U` spans the
selected columns, `‖V - CUR(V)‖₂ ≤ η_r ‖(I - U Uᵀ) V‖₂` with `η_r = ‖U(p,:)⁻¹‖₂`. -/
theorem specNorm_sub_cur_le_left [Fintype m] [Fintype n] [Fintype k] [DecidableEq m]
    [DecidableEq n] [DecidableEq k] [Nonempty k] {V : Matrix m n ℝ} {p : k → m} {s : k → n}
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (hW : IsUnit (V.submatrix p s).det)
    (hUC : ∃ M : Matrix k k ℝ, V.submatrix id s = U * M) :
    specNorm (V - cur V p s) ≤
      specNorm (U.submatrix p id)⁻¹ * specNorm ((1 - U * Uᵀ) * V) := by
  obtain ⟨hSU, hcur⟩ := cur_eq_obliqueProj_mul hW hUC
  have h1 := specNorm_sub_obliqueProj_mul_le hU hSU V
  have h2 :=
    specNorm_obliqueProj_le_of_orthonormal hU (sel_orthonormal (injective_of_isUnit_det hW))
  rw [sel_transpose_mul] at h2
  rw [hcur, Matrix.sub_mul, Matrix.one_mul]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (specNorm_nonneg _))

/-- **Sharp one-sided form of eq. (19)** (arXiv 2408.16591): if the orthonormal `Y` spans the
selected rows, `‖V - CUR(V)‖₂ ≤ η_c ‖V (I - Y Yᵀ)‖₂` with `η_c = ‖Y(s,:)⁻¹‖₂`. -/
theorem specNorm_sub_cur_le_right [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]
    [DecidableEq k] [Nonempty k] {V : Matrix m n ℝ} {p : k → m} {s : k → n}
    {Y : Matrix n k ℝ} (hY : Yᵀ * Y = 1) (hW : IsUnit (V.submatrix p s).det)
    (hYR : ∃ N : Matrix k k ℝ, (V.submatrix p id)ᵀ = Y * N) :
    specNorm (V - cur V p s) ≤
      specNorm (Y.submatrix s id)⁻¹ * specNorm (V * (1 - Y * Yᵀ)) := by
  have hW' : IsUnit (Vᵀ.submatrix s p).det := by
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]; exact hW
  have hYR' : ∃ N : Matrix k k ℝ, Vᵀ.submatrix id p = Y * N := by
    obtain ⟨N, hN⟩ := hYR; exact ⟨N, by rw [← hN, Matrix.transpose_submatrix]⟩
  classical
  have h := specNorm_sub_cur_le_left hY hW' hYR'
  have e1 : Vᵀ - cur Vᵀ s p = (V - cur V p s)ᵀ := by
    rw [cur_transpose, Matrix.transpose_sub]
  have e2 : (1 - Y * Yᵀ) * Vᵀ = (V * (1 - Y * Yᵀ))ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rwa [e1, e2, specNorm_transpose, specNorm_transpose] at h

/-- **Eq. (19), CUR-DEIM bound** (arXiv 2408.16591, Sec. 3.3, citing [15, Thm. 2.8]), in the
spectral norm: if `U`, `Y` are orthonormal bases whose spans contain the selected columns
`V(:,s)` and rows `V(p,:)ᵀ` and the cross `V(p,s)` is invertible, then
`‖V - CUR(V)‖₂ ≤ c σ̂_{r+1}`, `c = min {η_r (1 + η_c), η_c (1 + η_r)}`, `η_r = ‖U(p,:)⁻¹‖₂`,
`η_c = ‖Y(s,:)⁻¹‖₂`, `σ̂_{r+1} = max {‖(I - U Uᵀ) V‖₂, ‖V (I - Y Yᵀ)‖₂}`.  No condition on how
`p`, `s` are chosen.  (With the invertible cross, the spans are then equal to those of `V(:,s)`
and `V(p,:)ᵀ`; for `U`, `Y` the singular vectors of `V` the bound fails,
`eq19_false_for_singular_vectors`.) -/
theorem specNorm_sub_cur_le [Fintype m] [Fintype n] [Fintype k] [DecidableEq m]
    [DecidableEq n] [DecidableEq k] [Nonempty k] {V : Matrix m n ℝ} {p : k → m} {s : k → n}
    {U : Matrix m k ℝ} {Y : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hY : Yᵀ * Y = 1)
    (hW : IsUnit (V.submatrix p s).det) (hUC : ∃ M : Matrix k k ℝ, V.submatrix id s = U * M)
    (hYR : ∃ N : Matrix k k ℝ, (V.submatrix p id)ᵀ = Y * N) :
    specNorm (V - cur V p s) ≤
      min (specNorm (U.submatrix p id)⁻¹ * (1 + specNorm (Y.submatrix s id)⁻¹))
          (specNorm (Y.submatrix s id)⁻¹ * (1 + specNorm (U.submatrix p id)⁻¹)) *
        max (specNorm ((1 - U * Uᵀ) * V)) (specNorm (V * (1 - Y * Yᵀ))) := by
  set ηr := specNorm (U.submatrix p id)⁻¹
  set ηc := specNorm (Y.submatrix s id)⁻¹
  set a := specNorm ((1 - U * Uᵀ) * V)
  set b := specNorm (V * (1 - Y * Yᵀ))
  have hl := specNorm_sub_cur_le_left hU hW hUC
  have hr := specNorm_sub_cur_le_right hY hW hYR
  have hηr : 0 ≤ ηr := specNorm_nonneg _
  have hηc : 0 ≤ ηc := specNorm_nonneg _
  have ha : a ≤ max a b := le_max_left _ _
  have hb : b ≤ max a b := le_max_right _ _
  have h0 : 0 ≤ max a b := (specNorm_nonneg _).trans ha
  rw [min_mul_of_nonneg _ _ h0]
  refine le_min ?_ ?_
  · calc specNorm (V - cur V p s) ≤ ηr * a := hl
      _ ≤ ηr * max a b := mul_le_mul_of_nonneg_left ha hηr
      _ ≤ ηr * (1 + ηc) * max a b := by nlinarith [mul_nonneg (mul_nonneg hηr hηc) h0]
  · calc specNorm (V - cur V p s) ≤ ηc * b := hr
      _ ≤ ηc * max a b := mul_le_mul_of_nonneg_left hb hηc
      _ ≤ ηc * (1 + ηr) * max a b := by nlinarith [mul_nonneg (mul_nonneg hηc hηr) h0]

/-- The hypotheses of `specNorm_sub_cur_le` hold (arXiv 2408.16591, eq. (19), non-vacuity):
`V = [3 4; 4 1]` (rank 2), `p = s = {0}`, `U = Y = (3/5, 4/5)`. -/
example :
    let V : Matrix (Fin 2) (Fin 2) ℝ := !![3, 4; 4, 1]
    let U : Matrix (Fin 2) (Fin 1) ℝ := !![3/5; 4/5]
    let p : Fin 1 → Fin 2 := fun _ => 0
    Uᵀ * U = 1 ∧ IsUnit (V.submatrix p p).det ∧
      (∃ M : Matrix (Fin 1) (Fin 1) ℝ, V.submatrix id p = U * M) ∧
      ∃ M : Matrix (Fin 1) (Fin 1) ℝ, (V.submatrix p id)ᵀ = U * M := by
  intro V U p
  refine ⟨?_, ?_, ⟨!![5], ?_⟩, ⟨!![5], ?_⟩⟩
  · ext i j; fin_cases i; fin_cases j; simp [U, Matrix.mul_apply]; norm_num
  · have hW : V.submatrix p p = !![3] := by
      ext i j; fin_cases i; fin_cases j; simp [V, p]
    rw [hW, Matrix.det_fin_one_of]; norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [V, U, p]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [V, U, p]

/-! ### Remark 1: interpolation property -/

/-- **Remark 1** (arXiv 2408.16591), rows, no oversampling: `CUR(V)(p,:) = V(p,:)`.  (The
projector form `Sᵀ 𝒫 = Sᵀ` is `LeanDLRA.transpose_mul_obliqueProj`.) -/
theorem cur_submatrix_rows [Fintype k] [DecidableEq k] {V : Matrix m n ℝ} {p : k → m}
    {s : k → n} (hW : IsUnit (V.submatrix p s).det) :
    (cur V p s).submatrix p id = V.submatrix p id := by
  rw [cur, Matrix.submatrix_mul _ _ p id id Function.bijective_id,
    Matrix.submatrix_mul _ _ p id id Function.bijective_id, Matrix.submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp, Matrix.submatrix_id_id]
  rw [Matrix.mul_nonsing_inv _ hW, Matrix.one_mul]

/-- **Remark 1** (arXiv 2408.16591), columns, no oversampling: `CUR(V)(:,s) = V(:,s)`. -/
theorem cur_submatrix_cols [Fintype k] [DecidableEq k] {V : Matrix m n ℝ} {p : k → m}
    {s : k → n} (hW : IsUnit (V.submatrix p s).det) :
    (cur V p s).submatrix id s = V.submatrix id s := by
  rw [cur, Matrix.submatrix_mul _ _ id id s Function.bijective_id, Matrix.submatrix_id_id,
    Matrix.submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW, Matrix.mul_one]

/-- **Eqs. (21)–(22)** (arXiv 2408.16591) without oversampling: the stable form
`Q Q(p,:)⁻¹ V(p,:)`, with `V(:,s) = Q R₀` (e.g. a QR factorisation; `R₀` is then invertible),
equals `CUR(V)`.  So Remark 1 applies to Algorithm 2 without oversampling. -/
theorem qr_cur_eq [Fintype k] [DecidableEq k] {V : Matrix m n ℝ} {p : k → m} {s : k → n}
    {Q : Matrix m k ℝ} {R₀ : Matrix k k ℝ} (hW : IsUnit (V.submatrix p s).det)
    (hQR : V.submatrix id s = Q * R₀) :
    Q * ((Q.submatrix p id)⁻¹ * V.submatrix p id) = cur V p s := by
  have hWeq : V.submatrix p s = Q.submatrix p id * R₀ := by
    have h := congrArg (fun A => A.submatrix p id) hQR
    simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at h
    rw [h, Matrix.submatrix_mul _ _ p id id Function.bijective_id, Matrix.submatrix_id_id]
  have hdet : IsUnit ((Q.submatrix p id).det * R₀.det) := by
    rw [← Matrix.det_mul, ← hWeq]; exact hW
  have hRu : IsUnit R₀.det := isUnit_of_mul_isUnit_right hdet
  rw [cur, hWeq, hQR, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R₀ R₀⁻¹, Matrix.mul_nonsing_inv _ hRu, Matrix.one_mul]

/-- **Remark 1, oversampled case** (arXiv 2408.16591, eqs. (21)–(22), Algorithm 2): with `k'`
selected rows `p'` and the least-squares coefficients `Z = Q(p',:)⁺ V(p',:)`, written as
`Q(p',:)⁺ = (Q(p',:)ᵀ Q(p',:))⁻¹ Q(p',:)ᵀ` (full column rank), the approximation `Q Z` still
reproduces the selected columns, `(Q Z)(:,s) = V(:,s)`, whenever `V(:,s) = Q R₀`. -/
theorem lsq_cur_submatrix_cols [Fintype k] [DecidableEq k] {k' : Type*} [Fintype k']
    {V : Matrix m n ℝ} {p' : k' → m} {s : k → n} {Q : Matrix m k ℝ} {R₀ : Matrix k k ℝ}
    (hG : IsUnit ((Q.submatrix p' id)ᵀ * Q.submatrix p' id).det)
    (hQR : V.submatrix id s = Q * R₀) :
    (Q * (((Q.submatrix p' id)ᵀ * Q.submatrix p' id)⁻¹ * (Q.submatrix p' id)ᵀ *
      V.submatrix p' id)).submatrix id s = V.submatrix id s := by
  have h1 : (V.submatrix p' id).submatrix id s = Q.submatrix p' id * R₀ := by
    have h := congrArg (fun A => A.submatrix p' id) hQR
    simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at h
    simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
    rw [h, Matrix.submatrix_mul _ _ p' id id Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.submatrix_mul _ _ id id s Function.bijective_id, Matrix.submatrix_id_id,
    Matrix.submatrix_mul _ _ id id s Function.bijective_id, Matrix.submatrix_id_id, h1, hQR]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Q.submatrix p' id)ᵀ, ← Matrix.mul_assoc _ (_ * _),
    Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

/-- **Remark 1, oversampled case, rows** (arXiv 2408.16591): the least-squares CUR need not
reproduce the selected rows: `V = I₂` (rank `2 > r = 1`), `s = {0}`, `Q = e₁`, both rows
selected. -/
theorem lsq_cur_rows_ne :
    let V : Matrix (Fin 2) (Fin 2) ℝ := 1
    let Q : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let p' : Fin 2 → Fin 2 := id
    V.submatrix id (fun _ : Fin 1 => 0) = Q * (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
      IsUnit ((Q.submatrix p' id)ᵀ * Q.submatrix p' id).det ∧
      (Q * (((Q.submatrix p' id)ᵀ * Q.submatrix p' id)⁻¹ * (Q.submatrix p' id)ᵀ *
        V.submatrix p' id)).submatrix p' id ≠ V.submatrix p' id := by
  intro V Q p'
  have hG : (Q.submatrix p' id)ᵀ * Q.submatrix p' id = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [Q, p', Matrix.mul_apply]
  refine ⟨?_, by rw [hG]; simp, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [V, Q, Matrix.one_apply]
  · rw [hG, inv_one, Matrix.one_mul]
    intro h
    have h11 := congrFun (congrFun h 1) 1
    simp [V, Q, p', Matrix.vecMul, dotProduct] at h11


end CUR

section DEIM

variable {N r : ℕ}

/-- **DEIM index selection** (Chaturantabut–Sorensen; used in eqs. (19), (20), (25), (32) of
arXiv 2408.16591): `p` is a DEIM selection for the columns `u_l = U(:,l)` if, for every `l`,
`p_l` maximises `|u_l - w|`, where `w = U c` (`c` supported on the first `l` columns) interpolates
`u_l` at the previously selected rows `p_0, …, p_{l-1}`.  (In DEIM this interpolant is unique,
so quantifying over all such `c` is the greedy rule itself.) -/
def IsDEIM (U : Matrix (Fin N) (Fin r) ℝ) (p : Fin r → Fin N) : Prop :=
  ∀ l : Fin r, ∀ c : Fin r → ℝ, (∀ j, l ≤ j → c j = 0) →
    (∀ j, j < l → (U *ᵥ c) (p j) = U (p j) l) →
    ∀ i, |U i l - (U *ᵥ c) i| ≤ |U (p l) l - (U *ᵥ c) (p l)|

/-- One DEIM update of the interpolation projector: with the residual `ρ = u - Π u`,
`Π⁺ = Π + ρ(q)⁻¹ ρ e_qᵀ (I - Π)`. (arXiv 2408.16591, eq. (20).) -/
noncomputable def deimStep (P : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) (q : Fin N) :
    Matrix (Fin N) (Fin N) ℝ :=
  P + ((u - P *ᵥ u) q)⁻¹ • (vecMulVec (u - P *ᵥ u) (Pi.single q 1) * (1 - P))

/-- The DEIM interpolation projectors of the first `l` columns and indices.
(arXiv 2408.16591, eq. (20).) -/
noncomputable def deimProj (U : Matrix (Fin N) (Fin r) ℝ) (p : Fin r → Fin N) :
    ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 0
  | l + 1 => if h : l < r then deimStep (deimProj U p l) (fun i => U i ⟨l, h⟩) (p ⟨l, h⟩)
      else deimProj U p l

/-- `(a e_qᵀ M)_{ij} = a_i M_{qj}` (auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem vecMulVec_single_mul {ι : Type*} (a : ι → ℝ) (q : Fin N)
    (M : Matrix (Fin N) (Fin N) ℝ) (i : ι) (j : Fin N) :
    (vecMulVec a (Pi.single q 1) * M) i j = a i * M q j := by
  simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply]

/-- `I - Π⁺ = (I - ρ(q)⁻¹ ρ e_qᵀ)(I - Π)`. (arXiv 2408.16591, eq. (20).) -/
theorem one_sub_deimStep (P : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) (q : Fin N) :
    1 - deimStep P u q =
      (1 - ((u - P *ᵥ u) q)⁻¹ • vecMulVec (u - P *ᵥ u) (Pi.single q 1)) * (1 - P) := by
  rw [deimStep, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  abel

/-- Entries of the DEIM update. (arXiv 2408.16591, eq. (20).) -/
theorem deimStep_apply (P : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) (q a i : Fin N) :
    deimStep P u q a i =
      P a i + ((u - P *ᵥ u) q)⁻¹ * ((u - P *ᵥ u) a * (1 - P) q i) := by
  simp only [deimStep, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_single_mul]

/-- The invariant of the DEIM recursion: `Π_l = U C` with `C` supported on the first `l`
rows, and `Π_l` interpolates at `p_0, …, p_{l-1}`. (arXiv 2408.16591, eq. (20).) -/
def DeimInv (U : Matrix (Fin N) (Fin r) ℝ) (p : Fin r → Fin N) (l : ℕ) : Prop :=
  (∃ C : Matrix (Fin r) (Fin N) ℝ, (∀ j : Fin r, l ≤ j.val → ∀ x, C j x = 0) ∧
      deimProj U p l = U * C) ∧
    ∀ j : Fin r, j.val < l → ∀ i,
      deimProj U p l (p j) i = (1 : Matrix (Fin N) (Fin N) ℝ) (p j) i

/-- The invariant holds for `Π_0 = 0`. (arXiv 2408.16591, eq. (20).) -/
theorem deimInv_zero (U : Matrix (Fin N) (Fin r) ℝ) (p : Fin r → Fin N) : DeimInv U p 0 :=
  ⟨⟨0, fun _ _ _ => rfl, by simp [deimProj]⟩, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/-- Facts on the residual of step `l`: it vanishes at the old indices, is maximal in modulus at
`p_l`, and is nonzero there. (arXiv 2408.16591, eq. (20).) -/
theorem deim_res_facts {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} (hU : Uᵀ * U = 1)
    (hp : IsDEIM U p) {l : ℕ} (hl : l < r) (hinv : DeimInv U p l) :
    (∀ j : Fin r, j.val < l →
      ((fun i => U i ⟨l, hl⟩) - deimProj U p l *ᵥ (fun i => U i ⟨l, hl⟩)) (p j) = 0) ∧
    (∀ i, |((fun i => U i ⟨l, hl⟩) - deimProj U p l *ᵥ (fun i => U i ⟨l, hl⟩)) i| ≤
      |((fun i => U i ⟨l, hl⟩) - deimProj U p l *ᵥ (fun i => U i ⟨l, hl⟩))
        (p ⟨l, hl⟩)|) ∧
    ((fun i => U i ⟨l, hl⟩) - deimProj U p l *ᵥ (fun i => U i ⟨l, hl⟩))
      (p ⟨l, hl⟩) ≠ 0 := by
  obtain ⟨⟨C, hC0, hC⟩, hB⟩ := hinv
  set u : Fin N → ℝ := fun i => U i ⟨l, hl⟩ with hu
  set res := u - deimProj U p l *ᵥ u with hres
  have hinterp : ∀ j : Fin r, j.val < l → (deimProj U p l *ᵥ u) (p j) = u (p j) := by
    intro j hj
    simp only [Matrix.mulVec, dotProduct, hB j hj, Matrix.one_apply]
    simp
  have h1 : ∀ j : Fin r, j.val < l → res (p j) = 0 := by
    intro j hj; simp only [hres, Pi.sub_apply, hinterp j hj, sub_self]
  have h2 : ∀ i, |res i| ≤ |res (p ⟨l, hl⟩)| := by
    have hc : ∀ j : Fin r, (⟨l, hl⟩ : Fin r) ≤ j → (C *ᵥ u) j = 0 := by
      intro j hj
      simp only [Matrix.mulVec, dotProduct, hC0 j hj, zero_mul, Finset.sum_const_zero]
    have hw : U *ᵥ (C *ᵥ u) = deimProj U p l *ᵥ u := by rw [Matrix.mulVec_mulVec, hC]
    have := hp ⟨l, hl⟩ (C *ᵥ u) hc (fun j hj => by rw [hw]; exact hinterp j hj)
    simpa only [hw, hres, Pi.sub_apply] using this
  have hne : res ≠ 0 := by
    intro h0
    have hUt : (Uᵀ *ᵥ res) ⟨l, hl⟩ = 1 := by
      have e1 : Uᵀ *ᵥ u = fun j => (1 : Matrix (Fin r) (Fin r) ℝ) j ⟨l, hl⟩ := by
        funext j; rw [← hU]; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hu]
      have e2 : Uᵀ *ᵥ (deimProj U p l *ᵥ u) = C *ᵥ u := by
        rw [hC, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hU, Matrix.one_mul]
      rw [hres, Matrix.mulVec_sub, e2, e1]
      simp [Matrix.mulVec, dotProduct, hC0 ⟨l, hl⟩ le_rfl]
    rw [h0, Matrix.mulVec_zero] at hUt
    simp at hUt
  refine ⟨h1, h2, fun h0 => hne ?_⟩
  funext i
  have := h2 i
  rw [h0, abs_zero] at this
  exact abs_nonpos_iff.mp this

/-- `(U c) eᵀ = U (c eᵀ)` (auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem vecMulVec_mulVec_left (U : Matrix (Fin N) (Fin r) ℝ) (c : Fin r → ℝ)
    (e : Fin N → ℝ) :
    vecMulVec (U *ᵥ c) e = U * vecMulVec c e := by
  ext i j
  simp [vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- Unfolding the DEIM recursion. (arXiv 2408.16591, eq. (20).) -/
theorem deimProj_succ (U : Matrix (Fin N) (Fin r) ℝ) (p : Fin r → Fin N) {l : ℕ}
    (hl : l < r) :
    deimProj U p (l + 1) =
      deimStep (deimProj U p l) (fun i => U i ⟨l, hl⟩) (p ⟨l, hl⟩) := by
  simp [deimProj, hl]

/-- The invariant is preserved by a DEIM step. (arXiv 2408.16591, eq. (20).) -/
theorem deimInv_succ {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} (hU : Uᵀ * U = 1)
    (hp : IsDEIM U p) {l : ℕ} (hl : l < r) (hinv : DeimInv U p l) : DeimInv U p (l + 1) := by
  obtain ⟨h1, -, h3⟩ := deim_res_facts hU hp hl hinv
  obtain ⟨⟨C, hC0, hC⟩, hB⟩ := hinv
  set u : Fin N → ℝ := fun i => U i ⟨l, hl⟩ with hu
  set res := u - deimProj U p l *ᵥ u with hres
  refine ⟨?_, ?_⟩
  · set c' : Fin r → ℝ := Pi.single ⟨l, hl⟩ 1 - C *ᵥ u with hc'
    have hrc : res = U *ᵥ c' := by
      rw [hres, hc', Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hC]
      congr 1
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply, hu]
    refine ⟨C + (res (p ⟨l, hl⟩))⁻¹ •
      (vecMulVec c' (Pi.single (p ⟨l, hl⟩) 1) * (1 - deimProj U p l)), ?_, ?_⟩
    · intro j hj x
      have hj' : l ≤ j.val := by omega
      have hjl : j ≠ ⟨l, hl⟩ := by intro h; rw [h] at hj; simp at hj
      have hcj : c' j = 0 := by
        simp [hc', hjl, Matrix.mulVec, dotProduct, hC0 j hj']
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hC0 j hj' x,
        vecMulVec_single_mul, hcj, zero_mul, mul_zero, add_zero]
    · rw [deimProj_succ U p hl, deimStep, ← hu, ← hres, hrc, vecMulVec_mulVec_left,
        Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, ← hC]
  · intro j hj i
    rw [deimProj_succ U p hl, deimStep_apply, ← hu, ← hres]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjl | hjl
    · rw [h1 j hjl, zero_mul, mul_zero, add_zero, hB j hjl]
    · have hj' : j = ⟨l, hl⟩ := Fin.ext hjl
      subst hj'
      rw [Matrix.sub_apply]
      field_simp
      ring

/-- The invariant holds for all `l ≤ r`. (arXiv 2408.16591, eq. (20).) -/
theorem deimInv_of_le {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} (hU : Uᵀ * U = 1)
    (hp : IsDEIM U p) : ∀ l, l ≤ r → DeimInv U p l
  | 0, _ => deimInv_zero U p
  | l + 1, h => deimInv_succ hU hp (by omega) (deimInv_of_le hU hp l (by omega))

open scoped Matrix.Norms.L2Operator in
/-- `‖A - B‖₂ ≤ ‖A‖₂ + ‖B‖₂` (auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem specNorm_sub_le' {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℝ) : specNorm (A - B) ≤ specNorm A + specNorm B := by
  rw [specNorm_eq_l2, specNorm_eq_l2, specNorm_eq_l2]; exact norm_sub_le _ _

/-- `‖a e_qᵀ‖₂ ≤ ‖a‖₂` (auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem specNorm_vecMulVec_single_le (a : Fin N → ℝ) (q : Fin N) :
    specNorm (vecMulVec a (Pi.single q 1)) ≤
      ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin N))‖ := by
  refine specNorm_le_of (norm_nonneg _) fun x => ?_
  have hx : Matrix.toEuclideanLin (vecMulVec a (Pi.single q 1)) x =
      x q • (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin N)) := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.single_apply,
      mul_comm]
  rw [hx, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x q) (norm_nonneg _)

/-- `‖a‖₂ ≤ √N ‖a‖_∞` (auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem euclid_norm_le_sqrt (a : Fin N → ℝ) (q : Fin N) (h : ∀ i, |a i| ≤ |a q|) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin N))‖ ≤ √N * |a q| := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin N)) i‖ ^ 2
        ≤ ∑ _i : Fin N, a q ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [Real.norm_eq_abs]
        rw [← sq_abs (a q)]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = N * a q ^ 2 := by simp

/-- One DEIM step amplifies `‖I - Π‖₂` by at most `1 + √N`. (arXiv 2408.16591, eq. (20).) -/
theorem specNorm_deim_factor_le (a : Fin N → ℝ) (q : Fin N) (h : ∀ i, |a i| ≤ |a q|)
    (hq : a q ≠ 0) : specNorm (1 - (a q)⁻¹ • vecMulVec a (Pi.single q 1)) ≤ 1 + √N := by
  refine (specNorm_sub_le' _ _).trans (add_le_add specNorm_one_le ?_)
  rw [specNorm_smul, abs_inv]
  have hpos : 0 < |a q| := abs_pos.mpr hq
  calc |a q|⁻¹ * specNorm (vecMulVec a (Pi.single q 1)) ≤ |a q|⁻¹ * (√N * |a q|) :=
        mul_le_mul_of_nonneg_left ((specNorm_vecMulVec_single_le a q).trans
          (euclid_norm_le_sqrt a q h)) (inv_nonneg.mpr hpos.le)
    _ = √N := by field_simp

/-- The norm chain: `‖I - Π_l‖₂ ≤ (1 + √N)^{l-1} ‖I - Π_1‖₂` for `1 ≤ l ≤ r`
(auxiliary). (arXiv 2408.16591, eq. (20).) -/
theorem specNorm_one_sub_deimProj_le {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N}
    (hU : Uᵀ * U = 1) (hp : IsDEIM U p) :
    ∀ l, 1 ≤ l → l ≤ r →
      specNorm (1 - deimProj U p l) ≤ (1 + √N) ^ (l - 1) * specNorm (1 - deimProj U p 1) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => intro _; simp
  | succ l hl ih =>
    intro hlr
    have hlr' : l < r := by omega
    obtain ⟨-, h2, h3⟩ := deim_res_facts hU hp hlr' (deimInv_of_le hU hp l hlr'.le)
    rw [deimProj_succ U p hlr', one_sub_deimStep]
    set u : Fin N → ℝ := fun i => U i ⟨l, hlr'⟩
    set a := u - deimProj U p l *ᵥ u
    set q := p ⟨l, hlr'⟩
    have hf := specNorm_deim_factor_le a q h2 h3
    have hih := ih hlr'.le
    have h0 : 0 ≤ specNorm (1 - deimProj U p l) := specNorm_nonneg _
    have hs : 0 ≤ 1 + √(N : ℝ) := by positivity
    calc _ ≤ specNorm (1 - (a q)⁻¹ • vecMulVec a (Pi.single q 1)) *
            specNorm (1 - deimProj U p l) := specNorm_mul_le _ _
      _ ≤ (1 + √N) * ((1 + √N) ^ (l - 1) * specNorm (1 - deimProj U p 1)) :=
          mul_le_mul hf hih h0 hs
      _ = (1 + √N) ^ (l + 1 - 1) * specNorm (1 - deimProj U p 1) := by
          rw [← mul_assoc, ← pow_succ']
          congr 2
          omega

/-- The first DEIM projector `Π_1 = u_0 e_{p_0}ᵀ / u_0(p_0)` satisfies
`‖I - Π_1‖₂ ≤ 1 / |u_0(p_0)|`. (arXiv 2408.16591, eq. (20).) -/
theorem specNorm_one_sub_deimProj_one_le {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N}
    (hr : 0 < r) (hU : Uᵀ * U = 1) (hp : IsDEIM U p) :
    U (p ⟨0, hr⟩) ⟨0, hr⟩ ≠ 0 ∧
      specNorm (1 - deimProj U p 1) ≤ |U (p ⟨0, hr⟩) ⟨0, hr⟩|⁻¹ := by
  set z : Fin r := ⟨0, hr⟩
  set ρ := U (p z) z with hρdef
  have hρ : ρ ≠ 0 := by
    have := (deim_res_facts hU hp hr (deimInv_zero U p)).2.2
    simpa [deimProj] using this
  refine ⟨hρ, ?_⟩
  set U1 : Matrix (Fin N) (Fin 1) ℝ := Matrix.of fun i _ => U i z
  set S1 : Matrix (Fin N) (Fin 1) ℝ := Matrix.of fun i _ => if i = p z then 1 else 0
  have hU1 : U1ᵀ * U1 = 1 := by
    have h := congrFun (congrFun hU z) z
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    ext a b; fin_cases a; fin_cases b; simpa [U1, Matrix.mul_apply] using h
  have hS1 : S1ᵀ * S1 = 1 := by
    ext a b; fin_cases a; fin_cases b; simp [S1, Matrix.mul_apply]
  have hW : S1ᵀ * U1 = !![ρ] := by
    ext a b; fin_cases a; fin_cases b; simp [S1, U1, Matrix.mul_apply, hρdef]
  have hSU : IsUnit (S1ᵀ * U1).det := by
    rw [hW, Matrix.det_fin_one_of]; exact isUnit_iff_ne_zero.mpr hρ
  have hPi : deimProj U p 1 = obliqueProj U1 S1 := by
    rw [deimProj_succ U p hr]
    ext i j
    rw [deimStep_apply, obliqueProj, hW, inv_fin_one hρ]
    simp [deimProj, U1, S1, Matrix.mul_apply, Matrix.one_apply, hρdef, eq_comm]
    by_cases hj : j = p z <;> simp [hj, z, mul_comm]
  have h1 := specNorm_sub_obliqueProj_mul_le hU1 hSU (1 : Matrix (Fin N) (Fin N) ℝ)
  rw [Matrix.mul_one, Matrix.mul_one] at h1
  have h2 : specNorm (1 - U1 * U1ᵀ) ≤ 1 :=
    (isOrthProjMat_mul_transpose hU1).compl.specNorm_le_one
  have h3 := specNorm_obliqueProj_le_of_orthonormal hU1 hS1
  rw [hW, inv_fin_one hρ] at h3
  have h4 : specNorm (!![ρ⁻¹] : Matrix (Fin 1) (Fin 1) ℝ) ≤ |ρ|⁻¹ := by
    have : (!![ρ⁻¹] : Matrix (Fin 1) (Fin 1) ℝ) = ρ⁻¹ • 1 := by
      ext a b; fin_cases a; fin_cases b; simp
    rw [this, specNorm_smul, abs_inv]
    have := specNorm_one_le (n := Fin 1)
    have : 0 ≤ |ρ|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
    nlinarith
  rw [hPi]
  calc specNorm (1 - obliqueProj U1 S1)
        ≤ specNorm (obliqueProj U1 S1) * specNorm (1 - U1 * U1ᵀ) := h1
    _ ≤ specNorm (obliqueProj U1 S1) * 1 :=
        mul_le_mul_of_nonneg_left h2 (specNorm_nonneg _)
    _ ≤ |ρ|⁻¹ := by rw [mul_one]; exact h3.trans h4

/-- **DEIM growth bound** (arXiv 2408.16591, eq. (20), citing Chaturantabut–Sorensen; here with
the sharper factor `1 + √N` in place of `1 + √(2N)`): for orthonormal `U ∈ ℝ^{N×r}` (`r ≥ 1`) and
DEIM indices `p`, the matrix `U(p,:)` is invertible and
`‖U(p,:)⁻¹‖₂ ≤ (1 + √N)^{r-1} / ‖u_1‖_∞`.  Proof: the DEIM projectors satisfy
`I - Π_{l+1} = (I - ρ_l e_{p_l}ᵀ / ρ_l(p_l)) (I - Π_l)` with `‖ρ_l‖₂ ≤ √N |ρ_l(p_l)|`,
`Π_r = U (U(p,:))⁻¹ I(p,:)`, and Szyld's identity. -/
theorem deim_growth_bound {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} (hr : 0 < r)
    (hU : Uᵀ * U = 1) (hp : IsDEIM U p) :
    IsUnit (U.submatrix p id).det ∧
      specNorm (U.submatrix p id)⁻¹ ≤
        (1 + √N) ^ (r - 1) / ‖fun i => U i ⟨0, hr⟩‖ := by
  set z : Fin r := ⟨0, hr⟩
  obtain ⟨hρ, hbase⟩ := specNorm_one_sub_deimProj_one_le hr hU hp
  -- the sup norm of the first column is attained at `p_0`
  have hsup : ‖fun i => U i z‖ = |U (p z) z| := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_) ?_
    · have := hp z 0 (fun _ _ => rfl) (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _)) i
      simpa using this
    · have := norm_le_pi_norm (fun i => U i z) (p z)
      simpa using this
  have hcolnorm : ∀ i, |U i z| ≤ 1 := by
    intro i
    have h := congrFun (congrFun hU z) z
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have hle : U i z * U i z ≤ ∑ x, U x z * U x z :=
      Finset.single_le_sum (f := fun x => U x z * U x z) (fun x _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [h] at hle
    rw [abs_le]; constructor <;> nlinarith
  -- injectivity of `p`
  have hinj : Function.Injective p := by
    have key : ∀ a b : Fin r, a < b → p a ≠ p b := by
      intro a b hab h
      obtain ⟨h1, -, h3⟩ := deim_res_facts hU hp b.isLt (deimInv_of_le hU hp b b.isLt.le)
      have := h1 a hab
      rw [h] at this
      exact h3 this
    intro a b h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd h (key a b hab)
    · exact hab
    · exact absurd h.symm (key b a hab)
  -- the final projector is the DEIM projector `U (PᵀU)⁻¹ Pᵀ`
  obtain ⟨⟨C, -, hC⟩, hB⟩ := deimInv_of_le hU hp r le_rfl
  have hSPi : (sel p)ᵀ * (U * C) = (sel p)ᵀ * (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [sel_transpose_mul, sel_transpose_mul, ← hC]
    ext j i; exact hB j j.isLt i
  have hSU : IsUnit ((sel p)ᵀ * U).det := by
    refine Matrix.isUnit_det_of_right_inverse (B := C * sel p) ?_
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ U C, hSPi, Matrix.mul_one, sel_orthonormal hinj]
  have hPi : deimProj U p r = obliqueProj U (sel p) := by
    rw [hC, eq_obliqueProj_mul hSU hSPi, Matrix.mul_one]
  rw [sel_transpose_mul] at hSU
  refine ⟨hSU, ?_⟩
  have hη : specNorm (U.submatrix p id)⁻¹ ≤ specNorm (obliqueProj U (sel p)) := by
    have e : (U.submatrix p id)⁻¹ = Uᵀ * obliqueProj U (sel p) * sel p := by
      rw [obliqueProj, sel_transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [← sel_transpose_mul, sel_orthonormal hinj, Matrix.mul_one, ← Matrix.mul_assoc, hU,
        Matrix.one_mul]
    rw [e]
    have hUt : specNorm Uᵀ ≤ 1 := by
      rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU
    have hS : specNorm (sel p) ≤ 1 := specNorm_le_one_of_orthonormal (sel_orthonormal hinj)
    have := specNorm_nonneg (obliqueProj U (sel p))
    have := specNorm_nonneg Uᵀ
    calc specNorm (Uᵀ * obliqueProj U (sel p) * sel p)
        ≤ specNorm (Uᵀ * obliqueProj U (sel p)) * specNorm (sel p) := specNorm_mul_le _ _
      _ ≤ specNorm Uᵀ * specNorm (obliqueProj U (sel p)) * 1 := by
          gcongr
          · exact specNorm_nonneg _
          · exact specNorm_mul_le _ _
      _ ≤ 1 * specNorm (obliqueProj U (sel p)) * 1 := by gcongr
      _ = _ := by ring
  have hpos : 0 < |U (p z) z| := abs_pos.mpr hρ
  have hpow : 1 ≤ (1 + √(N : ℝ)) ^ (r - 1) :=
    one_le_pow₀ (by have := Real.sqrt_nonneg (N : ℝ); linarith)
  rw [hsup]
  refine hη.trans ?_
  by_cases hQ : U * Uᵀ = 1
  · have hP1 : obliqueProj U (sel p) = 1 := by
      have := obliqueProj_mul_proj (S := sel p) (by rwa [sel_transpose_mul])
      rwa [hQ, Matrix.mul_one] at this
    rw [hP1]
    refine specNorm_one_le.trans ?_
    rw [le_div_iff₀ hpos]
    calc 1 * |U (p z) z| ≤ 1 * 1 := by gcongr; exact hcolnorm _
      _ ≤ _ := by rw [one_mul]; exact hpow
  · have hsz := specNorm_obliqueProj_le_one_sub hU (by rwa [sel_transpose_mul]) hQ
    have hchain := specNorm_one_sub_deimProj_le hU hp r hr le_rfl
    rw [hPi] at hchain
    calc specNorm (obliqueProj U (sel p)) ≤ specNorm (1 - obliqueProj U (sel p)) := hsz
      _ ≤ (1 + √N) ^ (r - 1) * specNorm (1 - deimProj U p 1) := hchain
      _ ≤ (1 + √N) ^ (r - 1) * |U (p z) z|⁻¹ :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by rw [div_eq_mul_inv]

/-- **Eq. (20)** (arXiv 2408.16591) in the form printed in the paper, `n₁ = N` rows:
`η_r = ‖U(p,:)⁻¹‖₂ ≤ (1 + √(2N))^{r-1} / ‖u_1‖_∞` for orthonormal `U` and DEIM indices `p`. -/
theorem eq20_deim_bound {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} (hr : 0 < r)
    (hU : Uᵀ * U = 1) (hp : IsDEIM U p) :
    specNorm (U.submatrix p id)⁻¹ ≤
      (1 + √(2 * N)) ^ (r - 1) / ‖fun i => U i ⟨0, hr⟩‖ := by
  refine (deim_growth_bound hr hU hp).2.trans ?_
  have hn : 0 ≤ ‖fun i => U i ⟨0, hr⟩‖ := norm_nonneg _
  refine div_le_div_of_nonneg_right ?_ hn
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have : √(N : ℝ) ≤ √(2 * N) :=
    Real.sqrt_le_sqrt (by have := (Nat.cast_nonneg N : (0:ℝ) ≤ N); linarith)
  linarith

/-- **Eqs. (19) and (20) combined** (arXiv 2408.16591, Sec. 3.3): if the orthonormal
`U ∈ ℝ^{N×r}` spans the selected columns `V(:,s)`, `p` are DEIM indices of `U` and the cross
`V(p,s)` is invertible, then
`‖V - CUR(V)‖₂ ≤ (1 + √(2N))^{r-1} / ‖u_1‖_∞ · ‖(I - U Uᵀ) V‖₂`. -/
theorem cur_deim_error_le {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix (Fin N) n ℝ}
    {U : Matrix (Fin N) (Fin r) ℝ} {p : Fin r → Fin N} {s : Fin r → n} (hr : 0 < r)
    (hU : Uᵀ * U = 1) (hp : IsDEIM U p) (hW : IsUnit (V.submatrix p s).det)
    (hUC : ∃ M : Matrix (Fin r) (Fin r) ℝ, V.submatrix id s = U * M) :
    specNorm (V - cur V p s) ≤
      (1 + √(2 * N)) ^ (r - 1) / ‖fun i => U i ⟨0, hr⟩‖ * specNorm ((1 - U * Uᵀ) * V) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact (specNorm_sub_cur_le_left hU hW hUC).trans
    (mul_le_mul_of_nonneg_right (eq20_deim_bound hr hU hp) (specNorm_nonneg _))

end DEIM

section Counterexample

/-- **Eq. (19) fails when `η_r`, `η_c` come from the exact singular vectors.**  The paper
states that `p`, `s` are DEIM indices of the (exact or approximate) left and right singular
vectors, and that `σ̂_{r+1} = σ_{r+1}` when `U`, `Y` are the exact singular vectors.  For
`V = [79 228; 228 -54] = 250 u uᵀ - 225 w wᵀ`, `u = (4/5, 3/5)`, `w = (-3/5, 4/5)` (an SVD with
`σ₁ = 250 > σ₂ = 225`, `U = Y = u`), DEIM selects `p = s = 0` (`|u₀| > |u₁|`), and
`‖V - CUR(V)‖₂ = 56250/79 ≈ 712 > c σ̂₂ ≤ (45/16)·225 ≈ 633`. (arXiv 2408.16591, eq. (19).)
Here `u` does not span the selected column `V(:,0)`, as the printed definition of `U` requires;
under that definition (19) holds (`specNorm_sub_cur_le`).  This refutes only the reading of (19)
with `U`, `Y` the singular vectors. -/
theorem eq19_false_for_singular_vectors :
    let V : Matrix (Fin 2) (Fin 2) ℝ := !![79, 228; 228, -54]
    let u : Matrix (Fin 2) (Fin 1) ℝ := !![4/5; 3/5]
    let w : Matrix (Fin 2) (Fin 1) ℝ := !![-3/5; 4/5]
    let p : Fin 1 → Fin 2 := fun _ => 0
    (uᵀ * u = 1 ∧ wᵀ * w = 1 ∧ uᵀ * w = 0 ∧
      V = (250 : ℝ) • (u * uᵀ) + (225 : ℝ) • (w * (-w)ᵀ) ∧ IsDEIM u p ∧ |u 1 0| < |u 0 0|) ∧
    min (specNorm (u.submatrix p id)⁻¹ * (1 + specNorm (u.submatrix p id)⁻¹))
        (specNorm (u.submatrix p id)⁻¹ * (1 + specNorm (u.submatrix p id)⁻¹)) *
      max (specNorm ((1 - u * uᵀ) * V)) (specNorm (V * (1 - u * uᵀ))) <
      specNorm (V - cur V p p) := by
  intro V u w p
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [u, Matrix.mul_apply]; norm_num
  · ext i j; fin_cases i; fin_cases j; simp [w, Matrix.mul_apply]; norm_num
  · ext i j; fin_cases i; fin_cases j; simp [u, w, Matrix.mul_apply]; norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [V, u, w, Matrix.vecMul, dotProduct] <;> norm_num
  · intro l c hc _ i
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    have hc0 : c = 0 := funext fun j => by
      rw [Subsingleton.elim j 0]; exact hc 0 le_rfl
    subst hc0
    fin_cases i <;> simp [u, p]
    norm_num [abs_of_pos]
  · rw [show u 1 0 = 3/5 from rfl, show u 0 0 = 4/5 from rfl, abs_of_pos (by norm_num),
      abs_of_pos (by norm_num)]
    norm_num
  -- the entries
  have hww : wᵀ * w = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [w, Matrix.mul_apply]; norm_num
  have hW : V.submatrix p p = !![79] := by
    ext i j; fin_cases i; fin_cases j; simp [V, p]
  have hcur : V - cur V p p = !![0, 0; 0, -56250/79] := by
    rw [cur, hW, inv_fin_one (by norm_num)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [V, p, Matrix.mul_apply]
    norm_num
  have hleft : (1 - u * uᵀ) * V = (-225 : ℝ) • (w * wᵀ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, u, w, Matrix.mul_apply, Matrix.one_apply, Matrix.vecMul, dotProduct] <;> norm_num
  have hright : V * (1 - u * uᵀ) = (-225 : ℝ) • (w * wᵀ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, u, w, Matrix.mul_apply, Matrix.one_apply, Matrix.vecMul, dotProduct] <;> norm_num
  have hproj : specNorm (w * wᵀ) ≤ 1 := (isOrthProjMat_mul_transpose hww).specNorm_le_one
  have hσ : specNorm ((-225 : ℝ) • (w * wᵀ)) ≤ 225 := by
    rw [specNorm_smul]; norm_num; linarith
  have hu : u.submatrix p id = !![4/5] := by
    ext i j; fin_cases i; fin_cases j; simp [u, p]
  have hη : specNorm (u.submatrix p id)⁻¹ ≤ 5/4 := by
    rw [hu, inv_fin_one (by norm_num)]
    have : (!![(4/5 : ℝ)⁻¹] : Matrix (Fin 1) (Fin 1) ℝ) = (5/4 : ℝ) • 1 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this, specNorm_smul]
    have := specNorm_one_le (n := Fin 1)
    rw [abs_of_pos (by norm_num)]; linarith
  have hlow : 56250/79 ≤ specNorm (V - cur V p p) := by
    rw [hcur]
    have h := norm_toEuclideanLin_le (!![0, 0; 0, -56250/79] : Matrix (Fin 2) (Fin 2) ℝ)
      (EuclideanSpace.single 1 1)
    rw [PiLp.norm_single, norm_one, mul_one] at h
    refine le_trans ?_ h
    have h1 := PiLp.norm_apply_le (Matrix.toEuclideanLin
      (!![0, 0; 0, -56250/79] : Matrix (Fin 2) (Fin 2) ℝ) (EuclideanSpace.single 1 1)) 1
    refine le_trans ?_ h1
    simp [Matrix.toLpLin_apply]
  have hη0 : 0 ≤ specNorm (u.submatrix p id)⁻¹ := specNorm_nonneg _
  rw [hleft, hright, max_self, min_self]
  have h0 : 0 ≤ specNorm ((-225 : ℝ) • (w * wᵀ)) := specNorm_nonneg _
  calc specNorm (u.submatrix p id)⁻¹ * (1 + specNorm (u.submatrix p id)⁻¹) *
        specNorm ((-225 : ℝ) • (w * wᵀ)) ≤ 5/4 * (1 + 5/4) * 225 := by gcongr
    _ < 56250/79 := by norm_num
    _ ≤ _ := hlow

end Counterexample

section Collocation

variable {m n k : Type*}

/-- `F` acts **column by column** (the parametric PDE is solved sample by sample): column `j` of
`F(X)` depends only on column `j` of `X`. (arXiv 2408.16591, Sec. 3.3.1.) -/
def IsColumnwise (F : Matrix m n ℝ → Matrix m n ℝ) : Prop :=
  ∀ X Y : Matrix m n ℝ, ∀ j, (∀ i, X i j = Y i j) → ∀ i, F X i j = F Y i j

/-- The rows `p` of `F(X)` depend only on the rows `p` of `X` (no spatial coupling into the
selected rows, e.g. a pointwise reaction term). (arXiv 2408.16591, Sec. 3.3.1.) -/
def IsRowLocal (F : Matrix m n ℝ → Matrix m n ℝ) (p : k → m) : Prop :=
  ∀ X Y : Matrix m n ℝ, (∀ a j, X (p a) j = Y (p a) j) → ∀ a j, F X (p a) j = F Y (p a) j

/-- The time-discrete residual of implicit Euler, eq. (23):
`𝓡(X) = X - V̂^{k-1} - Δt F(X)`. (arXiv 2408.16591, Sec. 3.3.1.) -/
def residual (F : Matrix m n ℝ → Matrix m n ℝ) (Vprev : Matrix m n ℝ) (Δt : ℝ)
    (X : Matrix m n ℝ) : Matrix m n ℝ :=
  X - Vprev - Δt • F X

/-- Entries of the residual. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem residual_apply (F : Matrix m n ℝ → Matrix m n ℝ) (Vprev : Matrix m n ℝ) (Δt : ℝ)
    (X : Matrix m n ℝ) (i : m) (j : n) :
    residual F Vprev Δt X i j = X i j - Vprev i j - Δt * F X i j := rfl

/-- The residual vanishes on every column on which `X` agrees with the implicit Euler solution
`V` (`𝓡(V) = 0`), for a column-wise `F`. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem residual_col_eq_zero {F : Matrix m n ℝ → Matrix m n ℝ} (hF : IsColumnwise F)
    {Vprev V X : Matrix m n ℝ} {Δt : ℝ} (hV : residual F Vprev Δt V = 0) {j : n}
    (hX : ∀ i, X i j = V i j) (i : m) : residual F Vprev Δt X i j = 0 := by
  have h := congrFun (congrFun hV i) j
  rw [residual_apply] at h ⊢
  rw [hX i, hF X V j hX i]; exact h

/-- The residual vanishes on the rows `p` on which `X` agrees with `V`, for `F` row-local on
`p`. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem residual_row_eq_zero {F : Matrix m n ℝ → Matrix m n ℝ} {p : k → m}
    (hF : IsRowLocal F p) {Vprev V X : Matrix m n ℝ} {Δt : ℝ}
    (hV : residual F Vprev Δt V = 0) (hX : ∀ a j, X (p a) j = V (p a) j) (a : k) (j : n) :
    residual F Vprev Δt X (p a) j = 0 := by
  have h := congrFun (congrFun hV (p a)) j
  rw [residual_apply] at h ⊢
  rw [hX a j, hF X V hX a j]; exact h

variable [Fintype k] [DecidableEq k]

/-- **Sec. 3.3.1, columns**: for column-wise `F`, `V̂^k = CUR(V^k)` of the implicit Euler solution
`V^k = V̂^{k-1} + Δt F(V^k)` has zero time-discrete residual on the selected columns `s`.
(arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_residual_cols_eq_zero {F : Matrix m n ℝ → Matrix m n ℝ} (hF : IsColumnwise F)
    {Vprev V : Matrix m n ℝ} {Δt : ℝ} {p : k → m} {s : k → n}
    (hV : residual F Vprev Δt V = 0) (hW : IsUnit (V.submatrix p s).det) (a : k) (i : m) :
    residual F Vprev Δt (cur V p s) i (s a) = 0 :=
  residual_col_eq_zero hF hV (fun i => congrFun (congrFun (cur_submatrix_cols hW) i) a) i

/-- **Sec. 3.3.1, rows and columns**: if moreover `F` is row-local on `p`, the residual of
`CUR(V^k)` also vanishes on the selected rows `p`. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_residual_eq_zero {F : Matrix m n ℝ → Matrix m n ℝ} {p : k → m} {s : k → n}
    (hcol : IsColumnwise F) (hrow : IsRowLocal F p) {Vprev V : Matrix m n ℝ} {Δt : ℝ}
    (hV : residual F Vprev Δt V = 0) (hW : IsUnit (V.submatrix p s).det) :
    (∀ a i, residual F Vprev Δt (cur V p s) i (s a) = 0) ∧
      (∀ a j, residual F Vprev Δt (cur V p s) (p a) j = 0) :=
  ⟨cur_residual_cols_eq_zero hcol hV hW,
    residual_row_eq_zero hrow hV (fun a j => congrFun (congrFun (cur_submatrix_rows hW) a) j)⟩

/-- `CUR(X)` only depends on the selected cross: matrices that agree on the selected rows and
columns have the same CUR approximation. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_congr {X V : Matrix m n ℝ} {p : k → m} {s : k → n}
    (hc : X.submatrix id s = V.submatrix id s) (hr : X.submatrix p id = V.submatrix p id) :
    cur X p s = cur V p s := by
  have hW : X.submatrix p s = V.submatrix p s := by
    have h := congrArg (fun A => A.submatrix p id) hc
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using h
  rw [cur, cur, hc, hr, hW]

/-- **CUR is exact on rank-`r` matrices**: if `rank X ≤ r = |k|` and the cross `X(p,s)` is
invertible, then `X = X(:,s) X(p,s)⁻¹ X(p,:)`. (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_eq_self_of_rank_le [Finite m] [Fintype n] {X : Matrix m n ℝ} {p : k → m}
    {s : k → n} (hrank : X.rank ≤ Fintype.card k) (hW : IsUnit (X.submatrix p s).det) :
    cur X p s = X := by
  classical
  have := Fintype.ofFinite m
  set C := X.submatrix id s with hCdef
  have hCX : C = X * (1 : Matrix n n ℝ).submatrix id s := by
    ext i a; simp [C, Matrix.mul_apply, Matrix.one_apply]
  have hWC : X.submatrix p s = (1 : Matrix m m ℝ).submatrix p id * C := by
    ext a b; simp [C, Matrix.mul_apply, Matrix.one_apply]
  have hWrank : (X.submatrix p s).rank = Fintype.card k :=
    rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hW)
  have hCrank : Fintype.card k ≤ C.rank := by
    rw [← hWrank, hWC]; exact rank_mul_le_right _ _
  have hle : LinearMap.range C.mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [hCX, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range C.mulVecLin = LinearMap.range X.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle)
      (hrank.trans hCrank))
  have hcol : ∀ j, ∃ y : k → ℝ, C *ᵥ y = X.col j := by
    intro j
    have : X.col j ∈ LinearMap.range C.mulVecLin := by
      rw [heq, Matrix.range_mulVecLin]; exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  choose y hy using hcol
  set M : Matrix k n ℝ := Matrix.of fun a j => y j a
  have hXM : X = C * M := by
    ext i j
    have := congrFun (hy j) i
    simp only [Matrix.mulVec, dotProduct, Matrix.col_apply] at this
    simp only [Matrix.mul_apply, M, Matrix.of_apply]
    exact this.symm
  have hR : X.submatrix p id = X.submatrix p s * M := by
    conv_lhs => rw [hXM]
    rw [Matrix.submatrix_mul _ _ p id id Function.bijective_id, Matrix.submatrix_id_id]
    rfl
  rw [cur, hR, ← hCdef, ← Matrix.mul_assoc, Matrix.mul_assoc C, Matrix.nonsing_inv_mul _ hW,
    Matrix.mul_one, ← hXM]

/-- Uniqueness for one implicit Euler equation: `e = Δt g`, `‖g‖ ≤ L ‖e‖` and `Δt L < 1`
force `e = 0` (auxiliary). (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem eq_zero_of_implicit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {e g : E}
    {Δt L : ℝ} (hΔt : 0 ≤ Δt) (hL : Δt * L < 1) (he : e = Δt • g)
    (hg : ‖g‖ ≤ L * ‖e‖) :
    e = 0 := by
  have h1 : ‖e‖ ≤ Δt * (L * ‖e‖) := by
    calc ‖e‖ = ‖Δt • g‖ := by rw [← he]
      _ = Δt * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔt]
      _ ≤ Δt * (L * ‖e‖) := mul_le_mul_of_nonneg_left hg hΔt
  have h2 : ‖e‖ = 0 := by nlinarith [norm_nonneg e]
  exact norm_eq_zero.mp h2

/-- **Sec. 3.3.1: CUR is residual collocation** (arXiv 2408.16591, "the CUR approach is
equivalent to a residual collocation method").  Let the implicit Euler equation be uniquely
solvable column by column and on the selected rows: `F` is `L`-Lipschitz on every column and on
the rows `p` (sup norms), `0 ≤ Δt`, `Δt L < 1`.  Let `V^k` solve `𝓡(V^k) = 0` and let the cross
`V^k(p,s)` be invertible.  Then a matrix `X` of rank `≤ r = |k|` has zero residual on the selected
columns `s` and rows `p` iff `X = CUR(V^k)`. -/
theorem residual_collocation_iff [Fintype m] [Fintype n] {F : Matrix m n ℝ → Matrix m n ℝ}
    {Vprev V : Matrix m n ℝ} {Δt L : ℝ} {p : k → m} {s : k → n} (hΔt : 0 ≤ Δt)
    (hL : Δt * L < 1)
    (hcol : ∀ (X Y : Matrix m n ℝ) (j : n),
      ‖fun i => F X i j - F Y i j‖ ≤ L * ‖fun i => X i j - Y i j‖)
    (hrow : ∀ X Y : Matrix m n ℝ,
      ‖fun a j => F X (p a) j - F Y (p a) j‖ ≤ L * ‖fun a j => X (p a) j - Y (p a) j‖)
    (hV : residual F Vprev Δt V = 0) (hW : IsUnit (V.submatrix p s).det) {X : Matrix m n ℝ}
    (hX : X.rank ≤ Fintype.card k) :
    ((∀ a i, residual F Vprev Δt X i (s a) = 0) ∧
        (∀ a j, residual F Vprev Δt X (p a) j = 0)) ↔ X = cur V p s := by
  have hcw : IsColumnwise F := by
    intro X Y j hXY i
    have h0 : (fun i => X i j - Y i j) = 0 := funext fun i => by simp [hXY i]
    have h := hcol X Y j
    rw [h0, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (congrFun (norm_le_zero_iff.mp h) i)
  have hrl : IsRowLocal F p := by
    intro X Y hXY a j
    have h0 : (fun a j => X (p a) j - Y (p a) j) = 0 := funext fun a => funext fun j => by
      simp [hXY a j]
    have h := hrow X Y
    rw [h0, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (congrFun (congrFun (norm_le_zero_iff.mp h) a) j)
  constructor
  · rintro ⟨hc, hr⟩
    have hcols : ∀ a i, X i (s a) = V i (s a) := by
      intro a
      have he := eq_zero_of_implicit (e := fun i => X i (s a) - V i (s a))
        (g := fun i => F X i (s a) - F V i (s a)) hΔt hL (funext fun i => by
          have h1 := hc a i
          have h2 := congrFun (congrFun hV i) (s a)
          rw [residual_apply] at h1 h2
          simp only [Matrix.zero_apply] at h2
          simp only [Pi.smul_apply, smul_eq_mul]
          linarith) (hcol X V (s a))
      intro i
      exact sub_eq_zero.mp (congrFun he i)
    have hrows : ∀ a j, X (p a) j = V (p a) j := by
      have he := eq_zero_of_implicit (e := fun a j => X (p a) j - V (p a) j)
        (g := fun a j => F X (p a) j - F V (p a) j) hΔt hL (funext fun a => funext fun j => by
          have h1 := hr a j
          have h2 := congrFun (congrFun hV (p a)) j
          rw [residual_apply] at h1 h2
          simp only [Matrix.zero_apply] at h2
          simp only [Pi.smul_apply, smul_eq_mul]
          linarith) (hrow X V)
      intro a j
      exact sub_eq_zero.mp (congrFun (congrFun he a) j)
    have hcs : X.submatrix id s = V.submatrix id s := by
      ext i a; exact hcols a i
    have hrs : X.submatrix p id = V.submatrix p id := by
      ext a j; exact hrows a j
    have hWX : IsUnit (X.submatrix p s).det := by
      have : X.submatrix p s = V.submatrix p s := by
        ext a b; exact hcols b (p a)
      rwa [this]
    rw [← cur_eq_self_of_rank_le hX hWX, cur_congr hcs hrs]
  · rintro rfl
    exact cur_residual_eq_zero hcw hrl hV hW

/-- The hypotheses of `residual_collocation_iff` hold for the pointwise decay field `F(X) = -X`
(`L = 1`, `Δt = 1/2`). (arXiv 2408.16591, Sec. 3.3.1.) -/
example [Fintype m] [Fintype n] (p : k → m) :
    (∀ (X Y : Matrix m n ℝ) (j : n),
      ‖fun i => (-X) i j - (-Y) i j‖ ≤ 1 * ‖fun i => X i j - Y i j‖) ∧
    (∀ X Y : Matrix m n ℝ,
      ‖fun a j => (-X) (p a) j - (-Y) (p a) j‖ ≤
        1 * ‖fun a j => X (p a) j - Y (p a) j‖) ∧
    (1 / 2 : ℝ) * 1 < 1 := by
  refine ⟨fun X Y j => ?_, fun X Y => ?_, by norm_num⟩
  · have : (fun i => (-X) i j - (-Y) i j) = -(fun i => X i j - Y i j) := by
      funext i; simp only [Matrix.neg_apply, Pi.neg_apply]; ring
    rw [this, norm_neg, one_mul]
  · have : (fun a j => (-X) (p a) j - (-Y) (p a) j) = -(fun a j => X (p a) j - Y (p a) j) := by
      funext a j; simp only [Matrix.neg_apply, Pi.neg_apply]; ring
    rw [this, norm_neg, one_mul]

/-- The `1 × 1` cross: `CUR(V)_{ij} = V_{i j₀} V_{i₀ j₀}⁻¹ V_{i₀ j}`.
(arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_fin_one_apply {V : Matrix m n ℝ} {i₀ : m} {j₀ : n} (h : V i₀ j₀ ≠ 0) (i : m)
    (j : n) :
    cur V (fun _ : Fin 1 => i₀) (fun _ => j₀) i j = V i j₀ * (V i₀ j₀)⁻¹ * V i₀ j := by
  have hW : V.submatrix (fun _ : Fin 1 => i₀) (fun _ => j₀) = !![V i₀ j₀] := by
    ext a b; fin_cases a; fin_cases b; rfl
  rw [cur, hW, inv_fin_one h]
  simp [Matrix.mul_apply]

/-- **Sec. 3.3.1 fails with spatial coupling**: for the column-wise parametric field
`F(X)_{:j} = κ_j L X_{:j}` (sample-dependent coefficient `κ = (2, 3)`, nearest-neighbour coupling
`L = [0 1; 1 0]`), `Δt = 1`, the rank-one `V̂^{k-1} = [-3 -8; 0 0]` and the implicit Euler
solution `V^k = [1 1; 2 3]`, every admissible `1 × 1` cross `(p, s)` gives a CUR approximation
whose residual does **not** vanish on the selected row `p`.  (It does vanish on the selected
column, `cur_residual_cols_eq_zero`.) (arXiv 2408.16591, Sec. 3.3.1.) -/
theorem cur_residual_row_ne_zero :
    let F : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
      fun X => !![0, 1; 1, 0] * X * Matrix.diagonal ![2, 3]
    let Vprev : Matrix (Fin 2) (Fin 2) ℝ := !![-3, -8; 0, 0]
    let V : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 2, 3]
    IsColumnwise F ∧ Vprev.rank ≤ 1 ∧ residual F Vprev 1 V = 0 ∧
      ∀ i₀ j₀ : Fin 2, IsUnit (V.submatrix (fun _ : Fin 1 => i₀) (fun _ => j₀)).det ∧
        ∃ j, residual F Vprev 1 (cur V (fun _ : Fin 1 => i₀) (fun _ => j₀)) i₀ j ≠ 0 := by
  intro F Vprev V
  have hF : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, ∀ i j,
      F X i j = (∑ l, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) i l * X l j) * ![2, 3] j := by
    intro X i j; simp only [F]; rw [Matrix.mul_diagonal, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y j hXY i
    rw [hF, hF]
    simp only [hXY]
  · have : Vprev =
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![-3, -8] : Matrix (Fin 1) (Fin 2) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Vprev]
    rw [this]
    exact (rank_mul_le_left _ _).trans (rank_le_width _)
  · ext i j
    rw [residual_apply, hF]
    fin_cases i <;> fin_cases j <;> simp [V, Vprev, Fin.sum_univ_two] <;> norm_num
  · intro i₀ j₀
    have hne : V i₀ j₀ ≠ 0 := by fin_cases i₀ <;> fin_cases j₀ <;> simp [V]
    refine ⟨?_, 1 - j₀, ?_⟩
    · have hW : V.submatrix (fun _ : Fin 1 => i₀) (fun _ => j₀) = !![V i₀ j₀] := by
        ext a b; fin_cases a; fin_cases b; rfl
      rw [hW, Matrix.det_fin_one_of]
      exact isUnit_iff_ne_zero.mpr hne
    · rw [residual_apply, hF]
      simp only [Fin.sum_univ_two, cur_fin_one_apply hne]
      fin_cases i₀ <;> fin_cases j₀ <;> simp [V, Vprev] <;> norm_num

end Collocation

end LeanDLRA.Literature.P2408_16591
