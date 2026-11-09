import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2608.16994: BUG time integration in canonical MPS form

This module formalizes the two elementary matrix facts of arXiv 2608.16994 that the MPS
integrator rests on: `prop1_range_eq_iff` (Prop. 1, retention of the old block space: the
centre enlargement `S B0` keeps the row space of `B0` iff `rank S = r`) and
`prop2_overlap_transport` (Prop. 2, contractive overlap transport: `‖X B0 B̂ᵀ‖² = ‖X‖² −
‖X B0 (I − B̂ᵀB̂)‖²`, with isometry iff `range(B0ᵀ) ⊆ range(B̂ᵀ)`). Both are proved for real
matrices with the Frobenius norm, using the orthonormal-row hypotheses `B0 B0ᵀ = I` and
`B̂ B̂ᵀ = I` of the paper's setting. `prop2_le_and_eq_iff` adds the inequality of (24) and the
equality case for one `X`.

Deviations from the printed statements (PDF p. 6): the paper works over `ℂ` with conjugate
transposes `†`; here everything is real and `†` is the transpose. In Prop. 1 the paper's
consequence for the stacked spaces `V_c`, `V_e` of (20) and the rank condition (22) are not
formalized, only the range equivalence (21). In Prop. 2 the reformulation (26) `O O† = I` and the
consequence `B0 = O B̂` are not formalized, and the norm-preservation equivalence assumes at
least one row (`0 < m`; for `m = 0` the left side holds vacuously).

Not formalized: Thm. 4 (the alternating-endpoint robust
bound, which needs the TTN-BUG local error and the half-sweep composition, neither in the
library), Cor. 5 (norm and energy conservation of the MPS half-sweep; only the augmented
Galerkin step is in `LeanDLRA`), and Prop. 3 (identification with the endpoint-rooted
TTN-BUG on a comb tree, which needs TTN bookkeeping absent from the library).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2608_16994

/-- **Prop. 1 (retention of the old block space)** of arXiv 2608.16994.

Let `B0 : ℝ^{r×n}` have orthonormal rows (`B0 B0ᵀ = I`, the row-isometric convention of the
paper), and let the old centre be `C0 = S B0` with `S ∈ ℝ^{m×r}`. Then the row spaces
`range(C0ᵀ)` and `range(B0ᵀ)` (subspaces of `ℝ^n`) coincide iff `rank S = r`; this is (21).
Ranges are taken as `LinearMap.range` of `Matrix.toLin'`. The paper works over `ℂ`; this is the
real case. The predictor part of the paper's statement (`V_c = V_e` for every predictor, and
(22)) is not formalized; this is the matrix range fact it rests on. -/
theorem prop1_range_eq_iff {r n m : ℕ} (B0 : Matrix (Fin r) (Fin n) ℝ) (hB0 : B0 * B0ᵀ = 1)
    (S : Matrix (Fin m) (Fin r) ℝ) :
    LinearMap.range (Matrix.toLin' (S * B0)ᵀ) = LinearMap.range (Matrix.toLin' B0ᵀ) ↔
      S.rank = r := by
  have hf : Function.Injective (Matrix.toLin' B0ᵀ) := by
    intro x y hxy
    have hx : ∀ z : Fin r → ℝ, B0 *ᵥ (B0ᵀ *ᵥ z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, hB0, Matrix.one_mulVec]
    simp only [Matrix.toLin'_apply] at hxy
    calc x = B0 *ᵥ (B0ᵀ *ᵥ x) := (hx x).symm
      _ = B0 *ᵥ (B0ᵀ *ᵥ y) := by rw [hxy]
      _ = y := hx y
  rw [Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.range_comp,
    LinearMap.range_eq_map (Matrix.toLin' B0ᵀ), (Submodule.map_injective_of_injective hf).eq_iff,
    Submodule.eq_top_iff_finrank_eq]
  have hrank : S.rank = Module.finrank ℝ (LinearMap.range (Matrix.toLin' Sᵀ)) := by
    rw [← Matrix.rank_transpose]
    rfl
  rw [hrank, Module.finrank_fin_fun]

/-- **Prop. 2 (contractive overlap transport)** of arXiv 2608.16994.

Let `B0 ∈ ℝ^{r×n}` and `B̂ ∈ ℝ^{r'×n}` have orthonormal rows, `B0 B0ᵀ = I` and `B̂ B̂ᵀ = I`, and
set `O = B0 B̂ᵀ` and the orthogonal projector `P = B̂ᵀ B̂` on `ℝ^n`. Then (Frobenius norm)

* `‖X O‖² = ‖X‖² − ‖X B0 (I − P)‖²` for every `X ∈ ℝ^{m×r}` (the identity in (24)), and
* for every fixed row count `m ≥ 1`: `‖X O‖ = ‖X‖` for all `X ∈ ℝ^{m×r}` iff
  `range(B0ᵀ) ⊆ range(B̂ᵀ)` (as subspaces of `ℝ^n`), which is (25).

The paper works over `ℂ`; this is the real case. The paper's `k` is `m` here; `m ≥ 1` is needed
because for `m = 0` the norm preservation holds vacuously. The equivalent form (26) and
`B0 = O B̂` are not formalized. -/
theorem prop2_overlap_transport {r r' n : ℕ} (B0 : Matrix (Fin r) (Fin n) ℝ)
    (hB0 : B0 * B0ᵀ = 1) (Bh : Matrix (Fin r') (Fin n) ℝ) (hBh : Bh * Bhᵀ = 1) :
    (∀ (m : ℕ) (X : Matrix (Fin m) (Fin r) ℝ),
        ‖X * (B0 * Bhᵀ)‖ ^ 2 = ‖X‖ ^ 2 - ‖X * B0 * (1 - Bhᵀ * Bh)‖ ^ 2) ∧
      ∀ m : ℕ, 0 < m → ((∀ X : Matrix (Fin m) (Fin r) ℝ, ‖X * (B0 * Bhᵀ)‖ = ‖X‖) ↔
        LinearMap.range (Matrix.toLin' B0ᵀ) ≤ LinearMap.range (Matrix.toLin' Bhᵀ)) := by
  have hV : (Bhᵀ)ᵀ * Bhᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hBh
  have hW : (B0ᵀ)ᵀ * B0ᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hB0
  have hid : ∀ (m : ℕ) (X : Matrix (Fin m) (Fin r) ℝ),
      ‖X * (B0 * Bhᵀ)‖ ^ 2 = ‖X‖ ^ 2 - ‖X * B0 * (1 - Bhᵀ * Bh)‖ ^ 2 := by
    intro m X
    have hP := LeanDLRA.isOrthProj_rightProj (m := Fin m) hV
    have hY : ‖X * B0‖ = ‖X‖ := by
      have := LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hW X
      rwa [Matrix.transpose_transpose] at this
    have hpy := hP.norm_sq_add (X * B0)
    have e1 : rightProj Bhᵀ (X * B0) = X * B0 * Bhᵀ * Bh := by
      rw [rightProj_apply, Matrix.transpose_transpose]
    have e2 : X * B0 - X * B0 * Bhᵀ * Bh = X * B0 * (1 - Bhᵀ * Bh) := by
      simp [Matrix.mul_sub, Matrix.mul_assoc]
    rw [e1, e2] at hpy
    have hZ := LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV (X * B0 * Bhᵀ)
    rw [Matrix.transpose_transpose] at hZ
    have hO : X * (B0 * Bhᵀ) = X * B0 * Bhᵀ := by rw [Matrix.mul_assoc]
    rw [hZ, hY] at hpy
    rw [hO]
    linarith
  refine ⟨hid, fun m hm => ⟨fun h => ?_, fun hle X => ?_⟩⟩
  · -- equality for all X forces `B0 (I - P) = 0`: test with `X` whose rows are all `e_jᵀ`
    have h3 : B0 * (1 - Bhᵀ * Bh) = 0 := by
      ext j l
      have h1 := hid m (Matrix.of fun (_ : Fin m) (l' : Fin r) => if l' = j then (1 : ℝ) else 0)
      rw [h _] at h1
      have h0 : (Matrix.of fun (_ : Fin m) (l' : Fin r) => if l' = j then (1 : ℝ) else 0) * B0
          * (1 - Bhᵀ * Bh) = 0 := by
        have : ‖(Matrix.of fun (_ : Fin m) (l' : Fin r) => if l' = j then (1 : ℝ) else 0) * B0
            * (1 - Bhᵀ * Bh)‖ ^ 2 = 0 := by linarith
        exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
      have hent := congrFun (congrFun h0 ⟨0, hm⟩) l
      rw [Matrix.mul_assoc, Matrix.mul_apply] at hent
      simpa using hent
    have hPB : B0 * (Bhᵀ * Bh) = B0 := by
      have e : B0 * (1 - Bhᵀ * Bh) = B0 - B0 * (Bhᵀ * Bh) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
      rw [e, sub_eq_zero] at h3
      exact h3.symm
    have hPt : (Bhᵀ * Bh)ᵀ = Bhᵀ * Bh := by simp [Matrix.transpose_mul]
    have hcolmat : Bhᵀ * Bh * B0ᵀ = B0ᵀ := by
      calc Bhᵀ * Bh * B0ᵀ = (B0 * (Bhᵀ * Bh))ᵀ := by rw [Matrix.transpose_mul, hPt]
        _ = B0ᵀ := by rw [hPB]
    intro v hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨Bh *ᵥ (B0ᵀ *ᵥ w), ?_⟩
    simp only [Matrix.toLin'_apply]
    calc Bhᵀ *ᵥ (Bh *ᵥ (B0ᵀ *ᵥ w)) = (Bhᵀ * Bh * B0ᵀ) *ᵥ w := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = B0ᵀ *ᵥ w := by rw [hcolmat]
  · -- inclusion gives `B0 (I - P) = 0`, hence isometry
    have hcol : ∀ w : Fin r → ℝ, Bhᵀ *ᵥ (Bh *ᵥ (B0ᵀ *ᵥ w)) = B0ᵀ *ᵥ w := by
      intro w
      obtain ⟨y, hy⟩ := hle (LinearMap.mem_range_self _ w)
      simp only [Matrix.toLin'_apply] at hy
      have hy2 : Bh *ᵥ (Bhᵀ *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hBh, Matrix.one_mulVec]
      rw [← hy, hy2]
    have hcolmat : Bhᵀ * Bh * B0ᵀ = B0ᵀ := by
      ext i j
      have key : (Bhᵀ * Bh * B0ᵀ) *ᵥ Pi.single j 1 = B0ᵀ *ᵥ Pi.single j 1 := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hcol _
      have := congrFun key i
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
      exact this
    have ht := congrArg Matrix.transpose hcolmat
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
    have hz : B0 * (1 - Bhᵀ * Bh) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ht, sub_self]
    have h0 : X * B0 * (1 - Bhᵀ * Bh) = 0 := by rw [Matrix.mul_assoc, hz, Matrix.mul_zero]
    have h1 := hid m X
    rw [h0, norm_zero] at h1
    have h2 : ‖X * (B0 * Bhᵀ)‖ ^ 2 = ‖X‖ ^ 2 := by simpa using h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- The rest of (24) of arXiv 2608.16994: `‖X O‖ ≤ ‖X‖`, with equality for this particular `X`
iff `X B0 (I − P) = 0` (real case, Frobenius norm). -/
theorem prop2_le_and_eq_iff {r r' n m : ℕ} (B0 : Matrix (Fin r) (Fin n) ℝ)
    (hB0 : B0 * B0ᵀ = 1) (Bh : Matrix (Fin r') (Fin n) ℝ) (hBh : Bh * Bhᵀ = 1)
    (X : Matrix (Fin m) (Fin r) ℝ) :
    ‖X * (B0 * Bhᵀ)‖ ≤ ‖X‖ ∧ (‖X * (B0 * Bhᵀ)‖ = ‖X‖ ↔ X * B0 * (1 - Bhᵀ * Bh) = 0) := by
  have h := (prop2_overlap_transport B0 hB0 Bh hBh).1 m X
  have hsq : ‖X * (B0 * Bhᵀ)‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    nlinarith [sq_nonneg ‖X * B0 * (1 - Bhᵀ * Bh)‖]
  refine ⟨(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq, ?_⟩
  constructor
  · intro he
    rw [he] at h
    have : ‖X * B0 * (1 - Bhᵀ * Bh)‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  · intro hz
    rw [hz, norm_zero] at h
    have h2 : ‖X * (B0 * Bhᵀ)‖ ^ 2 = ‖X‖ ^ 2 := by simpa using h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-! Non-vacuity: a concrete row-orthonormal `B0 ∈ ℝ^{2×3}` satisfies the hypotheses. -/

private def B0ex : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0]

private theorem B0ex_orthonormal : B0ex * B0exᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [B0ex, Matrix.mul_apply, Fin.sum_univ_three]

/-- Prop. 1 applies to `B0ex` with `S = I` (full rank), so the row spaces agree. -/
example : LinearMap.range (Matrix.toLin' ((1 : Matrix (Fin 2) (Fin 2) ℝ) * B0ex)ᵀ) =
    LinearMap.range (Matrix.toLin' B0exᵀ) :=
  (prop1_range_eq_iff B0ex B0ex_orthonormal (1 : Matrix (Fin 2) (Fin 2) ℝ)).2
    (by simp [Matrix.rank_one])

/-- Prop. 2 applies to `B0ex` and `B̂ = B0ex`: the overlap is an isometry. -/
example : ∀ X : Matrix (Fin 1) (Fin 2) ℝ, ‖X * (B0ex * B0exᵀ)‖ = ‖X‖ :=
  ((prop2_overlap_transport B0ex B0ex_orthonormal B0ex B0ex_orthonormal).2 1 one_pos).2
    (le_refl _)

end LeanDLRA.Literature.P2608_16994
