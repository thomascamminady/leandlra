import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Energy

/-!
# Results of arXiv 2311.15143: RAIL implicit low-rank integrators

Theorem 2 of arXiv 2311.15143 (Sec. 3.4.2): for symmetric negative semidefinite `Fx`, `Fy`,
the first-order RAIL scheme with backward Euler is unconditionally stable in `L²`.  It is
formalized in finite dimensions: matrices with the Frobenius norm, the diffusion field
`U ↦ Fx U + U Fyᵀ`, and one step consisting of the S-step Sylvester equation (3.9) followed by
the SVD-type truncation.

The theorem `rail_firstOrder_L2_stable` has two conclusions.  The first bounds the untruncated
S-step solution `Vx S Vyᵀ`.  The second bounds the truncated solution
`(Vx Ar) (Arᵀ S Br) (Vy Br)ᵀ`, where `Ar`, `Br` have orthonormal columns.  The SVD truncation of
the paper is the case where these are the leading singular vectors of `S`.  The S-step
equation (3.9) is a hypothesis, since it defines the step.  The Galerkin form
`U₁ = Π U₀ + h Π F(U₁)` is derived inside the proof, and the contraction is the library's
`implicitGalerkin_norm_le` (`LeanDLRA.Stability.Energy`).

Core definitions used: `leftProj`, `rightProj`, `isOrthProj_leftProj_mul_rightProj`,
`leftProj_rightProj_apply`, `IsOrthProj`, `Frobenius.inner_def`, and the Frobenius norm lemmas.
Local additions: `inner_diffusion_nonpos` (dissipativity of the diffusion field under the
Frobenius inner product) and a non-vacuity example.

Differences from the paper: the K and L steps, the reduced augmentation with tolerance 10⁻¹²,
and the QR and SVD constructions that produce the bases are not formalized.  The bases are
arbitrary orthonormal matrices, which is all the theorem needs.  The symmetry hypotheses are
stated as in the paper, but the proof uses only negative semidefiniteness.  The proof is a
Galerkin contraction argument, not the paper's eigenbasis argument.  Only `L²` stability is
formalized, not the consistency results of Sec. 3.4.1 or the high-order scheme.
-/

open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2311_15143

variable {m n : ℕ}

/-- The diffusion field `U ↦ Fx U + U Fyᵀ` is dissipative for the Frobenius inner product
when `Fx` and `Fy` are negative semidefinite: `⟪Fx U + U Fyᵀ, U⟫ ≤ 0`. -/
lemma inner_diffusion_nonpos (Fx : Matrix (Fin m) (Fin m) ℝ) (Fy : Matrix (Fin n) (Fin n) ℝ)
    (hFx : ∀ x : Fin m → ℝ, ∑ i, ∑ j, x i * Fx i j * x j ≤ 0)
    (hFy : ∀ x : Fin n → ℝ, ∑ i, ∑ j, x i * Fy i j * x j ≤ 0)
    (U : Matrix (Fin m) (Fin n) ℝ) : ⟪Fx * U + U * Fyᵀ, U⟫ ≤ 0 := by
  have key : ⟪Fx * U + U * Fyᵀ, U⟫ = (∑ i, ∑ j, (∑ k, Fx i k * U k j) * U i j) +
      ∑ i, ∑ j, (∑ k, U i k * Fy j k) * U i j := by
    simp only [Frobenius.inner_def, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      add_mul, Finset.sum_add_distrib]
  have hA : ∑ i, ∑ j, (∑ k, Fx i k * U k j) * U i j ≤ 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_nonpos fun j _ => ?_
    have h1 := hFx (fun i => U i j)
    calc ∑ i, (∑ k, Fx i k * U k j) * U i j = ∑ i, ∑ k, U i j * Fx i k * U k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ 0 := h1
  have hB : ∑ i, ∑ j, (∑ k, U i k * Fy j k) * U i j ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    calc ∑ j, (∑ k, U i k * Fy j k) * U i j = ∑ j, ∑ k, U i j * Fy j k * U i k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ 0 := hFy (fun k => U i k)
  rw [key]
  exact add_nonpos hA hB

/-- **Theorem 2 of arXiv 2311.15143 (first-order RAIL, backward Euler, `L²` stability), in
matrix form.**  Let `Fx`, `Fy` be symmetric negative semidefinite and `h > 0`.  Let
`Un = Vx0 S0 Vy0ᵀ` be the previous solution, and let `Vx`, `Vy` have orthonormal columns.  If
`S` solves the S-step Sylvester equation (3.9), `(I - h Vxᵀ Fx Vx) S - S h (Fy Vy)ᵀ Vy =
Vxᵀ Un Vy`, then the untruncated solution satisfies `‖Vx S Vyᵀ‖ ≤ ‖Un‖`.  The truncation
to the leading `r` singular vectors, with orthonormal `Ar`, `Br` and core `Arᵀ S Br`, satisfies
the same bound.  The Frobenius norm is used throughout. -/
theorem rail_firstOrder_L2_stable {p q k l r r' : ℕ}
    (Fx : Matrix (Fin m) (Fin m) ℝ) (Fy : Matrix (Fin n) (Fin n) ℝ)
    (_hFxs : Fxᵀ = Fx) (_hFys : Fyᵀ = Fy)
    (hFx : ∀ x : Fin m → ℝ, ∑ i, ∑ j, x i * Fx i j * x j ≤ 0)
    (hFy : ∀ x : Fin n → ℝ, ∑ i, ∑ j, x i * Fy i j * x j ≤ 0)
    {h : ℝ} (hh : 0 < h)
    (Vx0 : Matrix (Fin m) (Fin p) ℝ) (S0 : Matrix (Fin p) (Fin q) ℝ)
    (Vy0 : Matrix (Fin n) (Fin q) ℝ)
    (Vx : Matrix (Fin m) (Fin k) ℝ) (Vy : Matrix (Fin n) (Fin l) ℝ)
    (hVx : Vxᵀ * Vx = 1) (hVy : Vyᵀ * Vy = 1)
    (S : Matrix (Fin k) (Fin l) ℝ)
    (hS : (1 - h • (Vxᵀ * Fx * Vx)) * S - S * (h • ((Fy * Vy)ᵀ * Vy)) =
      Vxᵀ * (Vx0 * S0 * Vy0ᵀ) * Vy)
    (Ar : Matrix (Fin k) (Fin r) ℝ) (Br : Matrix (Fin l) (Fin r') ℝ)
    (hAr : Arᵀ * Ar = 1) (hBr : Brᵀ * Br = 1) :
    ‖Vx * S * Vyᵀ‖ ≤ ‖Vx0 * S0 * Vy0ᵀ‖ ∧
      ‖(Vx * Ar) * (Arᵀ * S * Br) * (Vy * Br)ᵀ‖ ≤ ‖Vx0 * S0 * Vy0ᵀ‖ := by
  set U0 : Matrix (Fin m) (Fin n) ℝ := Vx0 * S0 * Vy0ᵀ with hU0
  set P : Matrix (Fin m) (Fin n) ℝ →L[ℝ] Matrix (Fin m) (Fin n) ℝ :=
    leftProj Vx * rightProj Vy with hPdef
  have hPapply : ∀ X : Matrix (Fin m) (Fin n) ℝ, P X = Vx * (Vxᵀ * X * Vy) * Vyᵀ :=
    fun X => leftProj_rightProj_apply Vx Vy X
  have hP : IsOrthProj P := isOrthProj_leftProj_mul_rightProj hVx hVy
  set U1 : Matrix (Fin m) (Fin n) ℝ := Vx * S * Vyᵀ with hU1
  -- the Galerkin projection of the diffusion field of the new solution
  have hc2 : Vxᵀ * (Fx * U1 + U1 * Fyᵀ) * Vy =
      (Vxᵀ * Fx * Vx) * S + S * ((Fy * Vy)ᵀ * Vy) := by
    rw [hU1]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.transpose_mul]
    rw [← Matrix.mul_assoc Vxᵀ Vx, hVx, Matrix.one_mul, hVy, Matrix.mul_one]
  -- the Galerkin form `U₁ = Π U₀ + h Π F(U₁)` of the S-step
  have hG : U1 = P U0 + h • P (Fx * U1 + U1 * Fyᵀ) := by
    rw [hPapply, hPapply, hc2, ← hS, hU1]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
    module
  have hF : ⟪Fx * U1 + U1 * Fyᵀ, U1⟫ ≤ 0 := inner_diffusion_nonpos Fx Fy hFx hFy U1
  have hGal := LeanDLRA.implicitGalerkin_norm_le (F := fun U => Fx * U + U * Fyᵀ) hP hh.le
    (hP.idem U0) hG hF
  have part1 : ‖U1‖ ≤ ‖U0‖ := hGal.2.trans (hP.norm_le U0)
  have hnorm1 : ‖U1‖ = ‖S‖ := by
    rw [hU1, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hVx,
      Frobenius.norm_mul_transpose_of_orthonormal hVy]
  have hT : (Vx * Ar) * (Arᵀ * S * Br) * (Vy * Br)ᵀ =
      Vx * ((Ar * (Arᵀ * S * Br)) * Brᵀ) * Vyᵀ := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hTn : ‖(Vx * Ar) * (Arᵀ * S * Br) * (Vy * Br)ᵀ‖ =
      ‖(Ar * (Arᵀ * S * Br)) * Brᵀ‖ := by
    rw [hT, Matrix.mul_assoc Vx, Frobenius.norm_mul_of_orthonormal hVx,
      Frobenius.norm_mul_transpose_of_orthonormal hVy]
  have hZ : ‖(Ar * (Arᵀ * S * Br)) * Brᵀ‖ ≤ ‖S‖ := by
    calc ‖(Ar * (Arᵀ * S * Br)) * Brᵀ‖ = ‖Ar * (Arᵀ * S * Br) * Brᵀ‖ := rfl
      _ = ‖Arᵀ * S * Br‖ := by
          rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hAr,
            Frobenius.norm_mul_transpose_of_orthonormal hBr]
      _ = ‖Arᵀ * (S * Br)‖ := by rw [Matrix.mul_assoc]
      _ ≤ ‖S * Br‖ := norm_transpose_mul_le hAr _
      _ ≤ ‖S‖ := norm_mul_le_of_orthonormal hBr S
  refine ⟨part1, ?_⟩
  calc ‖(Vx * Ar) * (Arᵀ * S * Br) * (Vy * Br)ᵀ‖
        = ‖(Ar * (Arᵀ * S * Br)) * Brᵀ‖ := hTn
    _ ≤ ‖S‖ := hZ
    _ = ‖U1‖ := hnorm1.symm
    _ ≤ ‖U0‖ := part1

/-- Non-vacuity: with `Fx = Fy = -1`, `h = 1`, unit bases and `Un = 1`, the S-step equation
has the solution `S = 1/3`, so the hypotheses of `rail_firstOrder_L2_stable` are jointly
satisfiable. -/
example : ‖!![(1 : ℝ)] * !![(1 / 3 : ℝ)] * !![(1 : ℝ)]ᵀ‖ ≤
    ‖!![(1 : ℝ)] * !![(1 : ℝ)] * !![(1 : ℝ)]ᵀ‖ := by
  have hU : (!![(1 : ℝ)])ᵀ * !![(1 : ℝ)] = 1 := by
    ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  have hsym : (!![(-1 : ℝ)])ᵀ = !![(-1 : ℝ)] := by
    ext i j; fin_cases i; fin_cases j; norm_num
  have hneg : ∀ x : Fin 1 → ℝ, ∑ i, ∑ j, x i * !![(-1 : ℝ)] i j * x j ≤ 0 := by
    intro x
    simp
    nlinarith [mul_self_nonneg (x 0)]
  have hS : (1 - (1 : ℝ) • ((!![(1 : ℝ)])ᵀ * !![(-1 : ℝ)] * !![(1 : ℝ)])) *
      !![(1 / 3 : ℝ)] - !![(1 / 3 : ℝ)] *
      ((1 : ℝ) • ((!![(-1 : ℝ)] * !![(1 : ℝ)])ᵀ * !![(1 : ℝ)])) =
      (!![(1 : ℝ)])ᵀ * (!![(1 : ℝ)] * !![(1 : ℝ)] * (!![(1 : ℝ)])ᵀ) * !![(1 : ℝ)] := by
    ext i j; fin_cases i; fin_cases j
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct]
  exact (rail_firstOrder_L2_stable (m := 1) (n := 1) (p := 1) (q := 1) (k := 1) (l := 1)
    (r := 1) (r' := 1) !![(-1 : ℝ)] !![(-1 : ℝ)] hsym hsym hneg hneg
    (by norm_num : (0 : ℝ) < 1) !![(1 : ℝ)] !![(1 : ℝ)] !![(1 : ℝ)] !![(1 : ℝ)] !![(1 : ℝ)]
    hU hU !![(1 / 3 : ℝ)] hS !![(1 : ℝ)] !![(1 : ℝ)] hU hU).1

end LeanDLRA.Literature.P2311_15143
