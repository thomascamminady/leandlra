import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation

/-!
# Results of arXiv 2402.18721: Collocation (cross-interpolation) methods on low-rank manifolds

This module proves the cross-interpolation property of the interpolatory tangent-space projector
(eq. (5) of arXiv 2402.18721) for the matrix oblique projector `𝒫 = U (Sᵀ U)⁻¹ Sᵀ`, where the
interpolation matrices `S_U`, `S_V` are selection matrices of index sets `I`, `J`:

* `obliqueTangentProj_eq_of_mem_range` (**Eq. (5)**, cross property): for `Z` and the oblique
  tangent projector `P_Y Z = 𝒫_U Z + Z 𝒫_Vᵀ − 𝒫_U Z 𝒫_Vᵀ`, the entry `(P_Y Z)(i, j)` equals
  `Z(i, j)` whenever `i ∈ I` or `j ∈ J`. The selection is encoded by the hypotheses
  `S_U i a = [i = I a]` and `S_V j b = [j = J b]`, and the nonsingularity of `S_Uᵀ U` and `S_Vᵀ V`.
  The proof uses only the interpolation identities `Sᵀ 𝒫 X = Sᵀ X` and `X 𝒫ᵀ S = X S`.
  Differences from the paper: the orthonormality of `U`, `V` is not assumed, since the result
  holds for every `U`, `V` with nonsingular interpolation matrices (a stronger statement).
  `example_obliqueTangentProj_cross` shows that the hypotheses are satisfiable for a nontrivial
  instance (`2 × 1` bases with `I = {0}`, `J = {0}`).

Not formalized from arXiv 2402.18721 (left out, not claimed):

* Eqs. (6)–(8) (matrix cross integrator): only the reconstruction identity is in the library; the
  closed ODEs for the sampled rows and columns are not proved here.
* Theorem 5.1 / Corollary 5.1 (TT-cross-DEIM, nested indices with invertible `M_j`, `N_j`): no TT
  layer is available in the library.
* Theorem 6.1 (exact solvability of the Lie–Trotter substeps with frozen interpolatory
  projectors): not attempted in this module.
* Proposition 4.1 (TT oblique tangent projector, idempotence of the alternating sum): not attempted;
  there is no TT layer.
* Lemma 4.1 / Theorem 4.1 (nested cross interpolation on fibres) belong to the companion slice
  `wip/Lit2402_18721b.lean` and are not part of this module.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2402_18721

/-- Row selection: `Sᵀ X` is the matrix of the rows of `X` indexed by `I`. -/
private lemma transpose_mul_apply_sel {m n k : Type*} [Fintype m] [DecidableEq m]
    (SU : Matrix m k ℝ) (I : k → m)
    (hI : ∀ i a, SU i a = if i = I a then 1 else 0) (X : Matrix m n ℝ) (a : k) (j : n) :
    (SUᵀ * X) a j = X (I a) j := by
  simp [Matrix.mul_apply, hI, ite_mul]

/-- Column selection: `X S` is the matrix of the columns of `X` indexed by `J`. -/
private lemma mul_apply_sel {m n l : Type*} [Fintype n] [DecidableEq n]
    (SV : Matrix n l ℝ) (J : l → n)
    (hJ : ∀ j b, SV j b = if j = J b then 1 else 0) (X : Matrix m n ℝ) (i : m) (b : l) :
    (X * SV) i b = X i (J b) := by
  simp [Matrix.mul_apply, hJ, mul_ite]

section Cross

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq l]

/-- **Eq. (5) of arXiv 2402.18721 (cross property).** With selection matrices `S_U`, `S_V` of the
index sets `I`, `J` (via `S_U i a = [i = I a]`, `S_V j b = [j = J b]`) and nonsingular
`S_Uᵀ U`, `S_Vᵀ V`, the oblique tangent-space projector
`P_Y Z = 𝒫_U Z + Z 𝒫_Vᵀ − 𝒫_U Z 𝒫_Vᵀ` reproduces `Z` on every row in `I` and every column in
`J`: `(P_Y Z)(i, j) = Z(i, j)` whenever `i ∈ I` or `j ∈ J`. -/
theorem obliqueTangentProj_eq_of_mem_range (U SU : Matrix m k ℝ) (V SV : Matrix n l ℝ)
    (I : k → m) (J : l → n)
    (hI : ∀ i a, SU i a = if i = I a then 1 else 0)
    (hJ : ∀ j b, SV j b = if j = J b then 1 else 0)
    (hSU : IsUnit (SUᵀ * U).det) (hSV : IsUnit (SVᵀ * V).det) (Z : Matrix m n ℝ)
    (i : m) (j : n) (h : i ∈ Set.range I ∨ j ∈ Set.range J) :
    LeanDLRA.obliqueTangentProj U SU V SV Z i j = Z i j := by
  have hR : SUᵀ * LeanDLRA.obliqueTangentProj U SU V SV Z = SUᵀ * Z := by
    have h1 : ∀ X : Matrix m n ℝ, SUᵀ * (LeanDLRA.obliqueProj U SU * X) = SUᵀ * X :=
      fun X => LeanDLRA.transpose_mul_obliqueProj_mul hSU X
    rw [LeanDLRA.obliqueTangentProj_apply]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc, h1]
    abel
  have hC : LeanDLRA.obliqueTangentProj U SU V SV Z * SV = Z * SV := by
    have h2 : ∀ X : Matrix m n ℝ, X * ((LeanDLRA.obliqueProj V SV)ᵀ * SV) = X * SV :=
      fun X => by rw [LeanDLRA.obliqueProj_transpose_mul hSV]
    rw [LeanDLRA.obliqueTangentProj_apply]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, h2]
    abel
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have := congrFun (congrFun hR a) j
    rw [transpose_mul_apply_sel SU I hI, transpose_mul_apply_sel SU I hI] at this
    exact this
  · have := congrFun (congrFun hC i) b
    rw [mul_apply_sel SV J hJ, mul_apply_sel SV J hJ] at this
    exact this

/-- Non-vacuity: for `U = V = (1, 0)ᵀ` and `I = J = {0}` the hypotheses hold (`S_U = U`,
`S_V = V`, so `S_Uᵀ U = 1`), and the cross property applies. -/
example (Z : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) (j : Fin 2) (h : i = 0 ∨ j = 0) :
    LeanDLRA.obliqueTangentProj (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) !![1; 0]
      (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) !![1; 0] Z i j = Z i j := by
  refine obliqueTangentProj_eq_of_mem_range _ _ _ _ (fun _ => 0) (fun _ => 0) ?_ ?_ ?_ ?_ Z i j ?_
  · intro i a
    fin_cases i <;> fin_cases a <;> simp
  · intro j b
    fin_cases j <;> fin_cases b <;> simp
  · norm_num [Matrix.det_unique, Matrix.mul_apply, Fin.sum_univ_two, isUnit_iff_ne_zero]
  · norm_num [Matrix.det_unique, Matrix.mul_apply, Fin.sum_univ_two, isUnit_iff_ne_zero]
  · rcases h with h | h
    · exact Or.inl ⟨0, h.symm⟩
    · exact Or.inr ⟨0, h.symm⟩

end Cross

end LeanDLRA.Literature.P2402_18721
