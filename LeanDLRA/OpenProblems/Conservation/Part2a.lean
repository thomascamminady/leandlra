import LeanDLRA.OpenProblems.Conservation.Part2Defs
import LeanDLRA.Stability.Conservation
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Interpolation
import LeanDLRA.OpenProblems.Conservation.Part1Defs

/-!
# Open problems OP-CO-12, OP-CO-13, OP-CO-14
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Conservation

section APLimit

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r] [DecidableEq r]

/-- **OP-CO-12 (a)** (arXiv 2212.12012, proof of Thm 4.1).  In the limit `ε → 0` the L-step of
the DLRA IMEX scheme forces `L^{n+1} ⟨X Xᵀ σ⟩ = -a cᵀ` with `c = ⟨∂ₓρⁿ, X⟩`, a matrix of rank
at most one.  Hence for `r ≥ 2` the hypothesis of the published AP proof, invertibility of
`S_L ⟨X Xᵀ σ⟩` for `L^{n+1} = V^{n+1} S_L` with orthonormal `V^{n+1}`, can never hold. -/
theorem ap_limit_core_singular {V : Matrix nv r ℝ} (hV : Vᵀ * V = 1) {SL M : Matrix r r ℝ}
    {L : Matrix nv r ℝ} (hL : L = V * SL) {a : nv → ℝ} {c : r → ℝ}
    (hLM : L * M = -Matrix.vecMulVec a c) (hr : 2 ≤ Fintype.card r) : (SL * M).det = 0 := by
  have : Nontrivial r := Fintype.one_lt_card_iff_nontrivial.mp hr
  have h1 : SL * M = -Matrix.vecMulVec (Vᵀ *ᵥ a) c := by
    calc SL * M = Vᵀ * (V * SL) * M := by rw [← Matrix.mul_assoc Vᵀ V SL, hV, Matrix.one_mul]
      _ = Vᵀ * (L * M) := by rw [hL, Matrix.mul_assoc]
      _ = -Matrix.vecMulVec (Vᵀ *ᵥ a) c := by
        rw [hLM, Matrix.mul_neg, Matrix.mul_vecMulVec]
  rw [h1, Matrix.det_neg, Matrix.det_vecMulVec, mul_zero]

/-- **OP-CO-12 (b), corrected AP theorem** (arXiv 2212.12012, Thm 4.1, corrected).  In the
limit, `K^{n+1} = -d (Vⁿᵀ a)ᵀ` with `d = σ⁻¹ ∂ₓρⁿ ≠ 0`, so `d ∈ range K^{n+1}` iff
`Vⁿᵀ a ≠ 0` (otherwise `K^{n+1} = 0` and AP fails); `L^{n+1} M = -a cᵀ` with invertible `M` and
`c ≠ 0` puts `a ∈ range L^{n+1}`; and if the new bases capture `d` and `a`, the S-limit
`S = -(Xᵀ d)(Vᵀ a)ᵀ` gives `g^{n+1} = X S Vᵀ = -d aᵀ`, the diffusion limit.  The observation
that a very small rank suffices near the limit, uniformly in `ε`, is not formalizable as stated. -/
theorem ap_limit_capture {K : Matrix nx r ℝ} {V : Matrix nv r ℝ} {a : nv → ℝ} {d : nx → ℝ}
    (hd : d ≠ 0) (hK : K = -Matrix.vecMulVec d (Vᵀ *ᵥ a)) {L : Matrix nv r ℝ}
    {M : Matrix r r ℝ} {c : r → ℝ} (hM : IsUnit M.det) (hc : c ≠ 0)
    (hLM : L * M = -Matrix.vecMulVec a c) {X : Matrix nx r ℝ} {V₁ : Matrix nv r ℝ}
    (hXd : X *ᵥ (Xᵀ *ᵥ d) = d) (hVa : V₁ *ᵥ (V₁ᵀ *ᵥ a) = a) :
    ((∃ w, K *ᵥ w = d) ↔ Vᵀ *ᵥ a ≠ 0) ∧ (∃ w, L *ᵥ w = a) ∧
      X * (-Matrix.vecMulVec (Xᵀ *ᵥ d) (V₁ᵀ *ᵥ a)) * V₁ᵀ = -Matrix.vecMulVec d a := by
  have _ := hM
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro h hu
    obtain ⟨w, hw⟩ := h
    apply hd
    rw [← hw, hK, hu]
    ext i
    simp [Matrix.mulVec]
  · intro hu
    have hpos : 0 < (Vᵀ *ᵥ a) ⬝ᵥ (Vᵀ *ᵥ a) := by
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm ((dotProduct_self_eq_zero).not.mpr hu))
    refine ⟨-(((Vᵀ *ᵥ a) ⬝ᵥ (Vᵀ *ᵥ a))⁻¹) • (Vᵀ *ᵥ a), ?_⟩
    rw [hK, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec]
    simp [dotProduct_smul, hpos.ne']
  · have hpos : c ⬝ᵥ c ≠ 0 := fun h => hc (dotProduct_self_eq_zero.mp h)
    refine ⟨M *ᵥ (-((c ⬝ᵥ c)⁻¹) • c), ?_⟩
    rw [Matrix.mulVec_mulVec, hLM, Matrix.neg_mulVec, Matrix.vecMulVec_mulVec]
    simp [dotProduct_smul, hpos]
  · rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, hXd, hVa]

end APLimit

section Oblique

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **OP-CO-13** (arXiv 2411.15990 §4; 2512.15703 §5).  A linear map `Π` maps every field with
`⟪c, F⟫ = 0` to one with `⟪c, Π F⟫ = 0` (so `Y₁ = Y₀ + h Π F` and `y' = Π F(y)` conserve
`⟪c, ·⟫` for all such `F`) iff `Πᵀ c` is a multiple of `c`.  The entry's "iff `Πᵀ c = c`" needs
the extra non-degeneracy `Πᵀ c ≠ 0` (for a projector the multiple is `0` or `1`). -/
theorem conserves_iff_adjoint_mul (Pi : E →L[ℝ] E) (c : E) :
    (∀ x, ⟪c, x⟫ = 0 → ⟪c, Pi x⟫ = 0) ↔ ∃ lam : ℝ, ∀ x, ⟪c, Pi x⟫ = lam * ⟪c, x⟫ := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact ⟨0, fun x => by simp [hc]⟩
    · have hcc : ⟪c, c⟫ ≠ 0 := by simpa using hc
      refine ⟨⟪c, Pi c⟫ / ⟪c, c⟫, fun x => ?_⟩
      have hx : ⟪c, x - (⟪c, x⟫ / ⟪c, c⟫) • c⟫ = 0 := by
        rw [inner_sub_right, inner_smul_right]
        field_simp
        ring
      have := h _ hx
      rw [map_sub, map_smul, inner_sub_right, inner_smul_right, sub_eq_zero] at this
      rw [this]
      field_simp
  · rintro ⟨lam, hl⟩ x hx
    rw [hl, hx, mul_zero]

/-- **OP-CO-13, DEIM projector** (arXiv 2411.15990 §4; 2512.15703 §5).  For the oblique (DEIM)
projector `U (Sᵀ U)⁻¹ Sᵀ`, the adjoint fixes `c` iff `c` is a combination of the selection
functionals (`c ∈ range S`); in particular the mass `c = 1` is not conserved unless `1 ∈ range S`.
-/
theorem obliqueProj_transpose_fix_iff {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
    {U S : Matrix m k ℝ} (hSU : IsUnit (Sᵀ * U).det) (c : m → ℝ) :
    (obliqueProj U S)ᵀ *ᵥ c = c ↔ ∃ w, S *ᵥ w = c := by
  rw [obliqueProj_transpose]
  constructor
  · intro h
    exact ⟨(Uᵀ * S)⁻¹ *ᵥ (Uᵀ *ᵥ c), by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact h⟩
  · rintro ⟨w, rfl⟩
    have := obliqueProj_transpose_mul hSU
    rw [obliqueProj_transpose] at this
    rw [Matrix.mulVec_mulVec, this]

end Oblique

section Constrained

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **OP-CO-14 (a)** (arXiv 1803.00499 §5.3; 1807.02338 §§3–4).  If the projected constraint
directions `P c_j` are linearly independent, the Gram system `G λ = (⟪c_j, (1 - P) F⟫)_j` is
solvable and `Y' = P F + Σ λ_j P c_j` lies in `range P`, satisfies the constraints
`⟪c_j, Y'⟫ = ⟪c_j, F⟫` and minimises `‖Y' - F‖` among all such vectors. -/
theorem constrainedDF_solution {k : ℕ} {P : E →L[ℝ] E} (hP : IsOrthProj P) (c : Fin k → E)
    (hli : LinearIndependent ℝ fun j => P (c j)) (F : E) :
    ∃ lam : Fin k → ℝ, (∀ i, ∑ j, ⟪P (c i), P (c j)⟫ * lam j = ⟪c i, F - P F⟫) ∧
      P (P F + ∑ j, lam j • P (c j)) = P F + ∑ j, lam j • P (c j) ∧
      (∀ i, ⟪c i, P F + ∑ j, lam j • P (c j)⟫ = ⟪c i, F⟫) ∧
      ∀ Z, P Z = Z → (∀ i, ⟪c i, Z⟫ = ⟪c i, F⟫) →
        ‖P F + ∑ j, lam j • P (c j) - F‖ ≤ ‖Z - F‖ := by
  -- basic identities
  have hcP : ∀ i j, ⟪c i, P (c j)⟫ = ⟪P (c i), P (c j)⟫ := fun i j => by
    rw [hP.symm (c i) (P (c j)), hP.idem]
  have hPP : ∀ x, P (P x) = P x := hP.idem
  -- Gram matrix
  set G : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => ⟪P (c i), P (c j)⟫ with hG
  have hGinj : ∀ x : Fin k → ℝ, G *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h0 : ⟪∑ i, x i • P (c i), ∑ j, x j • P (c j)⟫ = 0 := by
      have : ⟪∑ i, x i • P (c i), ∑ j, x j • P (c j)⟫ = x ⬝ᵥ (G *ᵥ x) := by
        simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct,
          Matrix.mulVec, hG, Matrix.of_apply]
        simp only [Finset.mul_sum, RCLike.conj_to_real]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_comm (P (c i)) (P (c j))]
        ring
      rw [this, hx, dotProduct_zero]
    have h1 : ∑ i, x i • P (c i) = 0 := inner_self_eq_zero.mp h0
    exact funext fun i => (Fintype.linearIndependent_iff.mp hli x h1) i
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨x, hx0, hx⟩
    exact hx0 (hGinj x hx)
  set b : Fin k → ℝ := fun i => ⟪c i, F - P F⟫ with hb
  refine ⟨G⁻¹ *ᵥ b, ?_⟩
  set lam : Fin k → ℝ := G⁻¹ *ᵥ b with hlam
  have hGl : G *ᵥ lam = b := by
    rw [hlam, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hgram : ∀ i, ∑ j, ⟪P (c i), P (c j)⟫ * lam j = ⟪c i, F - P F⟫ := fun i => by
    have := congrFun hGl i
    simpa [Matrix.mulVec, dotProduct, hG, hb] using this
  have hPY : P (P F + ∑ j, lam j • P (c j)) = P F + ∑ j, lam j • P (c j) := by
    rw [map_add, map_sum, hPP]
    simp only [map_smul, hPP]
  have hcons : ∀ i, ⟪c i, P F + ∑ j, lam j • P (c j)⟫ = ⟪c i, F⟫ := fun i => by
    rw [inner_add_right, inner_sum]
    simp only [inner_smul_right, hcP]
    have := hgram i
    simp only [mul_comm (lam _)] at this ⊢
    rw [this, inner_sub_right]
    ring
  refine ⟨hgram, hPY, hcons, ?_⟩
  intro Z hZ hZc
  set Y : E := P F + ∑ j, lam j • P (c j) with hY
  have hD : P (Z - Y) = Z - Y := by rw [map_sub, hZ, hPY]
  have horth1 : ∀ j, ⟪Z - Y, P (c j)⟫ = 0 := fun j => by
    rw [← hP.symm, hD, inner_sub_left, real_inner_comm (c j) Z, real_inner_comm (c j) Y, hZc j,
      hcons j, sub_self]
  have horth2 : ⟪Z - Y, Y - F⟫ = 0 := by
    have e : Y - F = (P F - F) + ∑ j, lam j • P (c j) := by rw [hY]; abel
    have h3 : ⟪Z - Y, P F - F⟫ = 0 := by
      rw [← hD, hP.symm, map_sub, hPP, sub_self, inner_zero_right]
    rw [e, inner_add_right, h3, inner_sum]
    simp only [inner_smul_right, horth1, mul_zero, Finset.sum_const_zero, add_zero]
  have hsplit : Z - F = (Z - Y) + (Y - F) := by abel
  have hn : ‖Z - F‖ ^ 2 = ‖Z - Y‖ ^ 2 + ‖Y - F‖ ^ 2 := by
    rw [hsplit, sq, sq, sq]; exact norm_add_sq_eq_norm_sq_add_norm_sq_real horth2
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖Z - Y‖]) (norm_nonneg _)

end Constrained

section MassCounterexample

open scoped LeanDLRA.Frobenius

end MassCounterexample

section VPEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end VPEnergy

section PositivityFeasibility

open scoped LeanDLRA.Frobenius

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r] [DecidableEq r]

end PositivityFeasibility

section Nonnegativity

open scoped LeanDLRA.Frobenius

end Nonnegativity

section AugmentedTypes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end AugmentedTypes

section Involutions

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

end Involutions

end LeanDLRA.OpenProblems.Conservation
