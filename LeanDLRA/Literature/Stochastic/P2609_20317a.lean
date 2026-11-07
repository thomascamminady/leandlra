import Mathlib
import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2609.20317: DLRA of SDEs II: stochastic discretisation

Formalized here: **Lemma B.2** of arXiv 2609.20317 (Kazashi, Nobile, Zoccolan), the regularised
empirical projector is a contraction in the empirical Frobenius norm. In matrix form, with
`U ∈ ℝ^{d×r}` satisfying `Uᵀ U = 1` (so `U Uᵀ` is the orthogonal projector `P_U`), `Y ∈ ℝ^{r×M}`,
`α > 0`, and `f ∈ ℝ^{d×M}` with columns `f^i`, the map

  `P^α[f] = P_U f + P_U^⊥ f H`,  `H = Yᵀ (Y Yᵀ / M + α I)⁻¹ Y / M`,

satisfies `(1/M) Σ_i |P^α[f]^i|² ≤ (1/M) Σ_i |f^i|²`. The paper's `Ū` has orthonormal rows and
`P_U = ŪᵀŪ`; here `U = Ūᵀ`. The paper's `Ỹ^i_{n+1}` and `Ū_n` play the roles of `Y` and `U`.
The sample count `M` is `Fintype.card N`. The Euclidean norm of a column `f^i` is written as the
sum of squares of its entries.

Core definitions used: `LeanDLRA.Frobenius` (Frobenius norm and inner product on matrices, via
`norm_sq_eq_sum` and `inner_eq_trace`). The orthogonal projector is the matrix `U * Uᵀ`, the same
object as `LeanDLRA.leftProj U`. The only local definition is `regCoef Y α`, the coefficient `H`
above, because the core has no regularised empirical projector. The file proves the properties
it needs: `H` is symmetric, and `‖H x‖ ≤ ‖x‖` on vectors, from which the Frobenius contraction
`‖A H‖_F ≤ ‖A‖_F` follows. The hypotheses are satisfiable: any `U` with orthonormal columns
(for example `U = 1`) and any `Y` with `α > 0` qualify.

Not formalized (out of scope here):

* Lemmas 3.8, 3.9, 3.10 (L²/L^p projector perturbation bounds with Monte Carlo rates, constants
  `G₁, G₂, G₃`, and sample-size dependence `1/√M`). Their proofs are deferred to the paper's
  Appendix C, which is not formalized here. Lemmas 3.13 and 3.16 were not read verbatim and are
  not formalized.
* The deterministic bound `‖XG_x − YG_y‖ ≤ (‖G_x‖ + ‖G_y‖)‖X − Y‖` is not a stated result of the
  paper that I could read, so it is not formalized.
* The probabilistic statements of Appendix B (Lemma B.1, Proposition 3.6), which involve
  expectations and random matrices.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2609_20317

/-- The regularised empirical coefficient `H = Yᵀ (Y Yᵀ / M + α I)⁻¹ Y / M` of Lemma B.2,
with `M = Fintype.card N` the number of samples. -/
noncomputable def regCoef {r N : Type*} [Fintype r] [DecidableEq r] [Fintype N]
    (Y : Matrix r N ℝ) (α : ℝ) : Matrix N N ℝ :=
  ((Fintype.card N : ℝ)⁻¹) • (Yᵀ * ((Fintype.card N : ℝ)⁻¹ • (Y * Yᵀ) +
    α • (1 : Matrix r r ℝ))⁻¹ * Y)

/-- A matrix `t • Z Zᵀ` (with `t ≥ 0`) shifted by `c • I` with `c > 0` is invertible. -/
private lemma isUnit_gram_add {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    (Z : Matrix a b ℝ) {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    IsUnit (t • (Z * Zᵀ) + c • (1 : Matrix a a ℝ)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ x : a → ℝ, (t • (Z * Zᵀ) + c • (1 : Matrix a a ℝ)) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h1 : x ⬝ᵥ ((t • (Z * Zᵀ) + c • (1 : Matrix a a ℝ)) *ᵥ x) = 0 := by
      rw [hx, dotProduct_zero]
    have h2 : x ⬝ᵥ ((t • (Z * Zᵀ) + c • (1 : Matrix a a ℝ)) *ᵥ x) =
        t * ((Zᵀ *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ x)) + c * (x ⬝ᵥ x) := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
        ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, smul_eq_mul,
        smul_eq_mul]
    have hn1 : 0 ≤ (Zᵀ *ᵥ x) ⬝ᵥ (Zᵀ *ᵥ x) := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hn2 : 0 ≤ x ⬝ᵥ x := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h3 : x ⬝ᵥ x = 0 := by
      have : c * (x ⬝ᵥ x) ≤ 0 := by nlinarith [mul_nonneg ht hn1]
      nlinarith
    exact dotProduct_self_eq_zero.mp h3
  intro x y hxy
  exact sub_eq_zero.mp (key (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self]))

/-- A symmetric matrix `H` with `‖H x‖ ≤ ‖x‖` on vectors satisfies `‖A H‖_F ≤ ‖A‖_F`. -/
private lemma frob_mul_le_of_contraction {d N : Type*} [Fintype d] [Fintype N]
    (H : Matrix N N ℝ) (hsym : Hᵀ = H)
    (hH : ∀ x : N → ℝ, (H *ᵥ x) ⬝ᵥ (H *ᵥ x) ≤ x ⬝ᵥ x) (A : Matrix d N ℝ) :
    ‖A * H‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have hHt : ∀ i j, H i j = H j i := fun i j => by
    have := congrFun (congrFun hsym j) i
    simpa using this
  have hrow : ∀ a, ∑ j, (A * H) a j ^ 2 ≤ ∑ l, A a l ^ 2 := by
    intro a
    have h1 : ∀ j, (A * H) a j = (H *ᵥ (fun l => A a l)) j := by
      intro j
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun l _ => by rw [hHt l j, mul_comm]
    have h2 := hH (fun l => A a l)
    unfold dotProduct at h2
    simp only [h1]
    simpa [sq] using h2
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum, LeanDLRA.Frobenius.norm_sq_eq_sum]
  exact Finset.sum_le_sum fun a _ => hrow a

/-- For a symmetric idempotent `P`, the Frobenius inner product of `P X` and `(1 - P) Y` is zero. -/
private lemma inner_proj_compl {d N : Type*} [Fintype d] [DecidableEq d] [Fintype N]
    (P : Matrix d d ℝ) (hPt : Pᵀ = P) (hPP : P * P = P) (X Y : Matrix d N ℝ) :
    ⟪P * X, (1 - P) * Y⟫ = 0 := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  rw [LeanDLRA.Frobenius.inner_eq_trace]
  have : (P * X)ᵀ * ((1 - P) * Y) = 0 := by
    rw [Matrix.transpose_mul, hPt, Matrix.mul_assoc, ← Matrix.mul_assoc P (1 - P), hPQ,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [this, Matrix.trace_zero]

/-- **Lemma B.2 (arXiv 2609.20317, regularised empirical projector is a contraction).**
For `U ∈ ℝ^{d×r}` with `Uᵀ U = 1` (so `P_U = U Uᵀ` is an orthogonal projector), `Y ∈ ℝ^{r×M}`,
`α > 0`, and `f ∈ ℝ^{d×M}` with columns `f^i`, one has

  `(1/M) Σ_i |P_U f^i + P_U^⊥ f Yᵀ (Y Yᵀ/M + αI)⁻¹ Y/M|² ≤ (1/M) Σ_i |f^i|²`,

where `P_U^⊥ = 1 - U Uᵀ`, `M = Fintype.card N`, and `|·|` is the Euclidean norm of a column. The
paper states this for `Ū` with orthonormal rows, `P_U = ŪᵀŪ`; this is the same statement with
`U = Ūᵀ`. Here `P^α[f]` is `U * Uᵀ * f + (1 - U * Uᵀ) * f * regCoef Y α`. -/
theorem regularised_projector_contraction {d r N : Type*} [Fintype d] [DecidableEq d]
    [Fintype r] [DecidableEq r] [Fintype N]
    (U : Matrix d r ℝ) (hU : Uᵀ * U = 1) (Y : Matrix r N ℝ) {α : ℝ} (hα : 0 < α)
    (f : Matrix d N ℝ) :
    (Fintype.card N : ℝ)⁻¹ * ∑ i, ∑ a,
        (U * Uᵀ * f + (1 - U * Uᵀ) * f * regCoef Y α : Matrix d N ℝ) a i ^ 2 ≤
      (Fintype.card N : ℝ)⁻¹ * ∑ i, ∑ a, f a i ^ 2 := by
  classical
  set P : Matrix d d ℝ := U * Uᵀ with hPdef
  have hPt : Pᵀ = P := by rw [hPdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hPP : P * P = P := by
    rw [hPdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U Uᵀ, hU, Matrix.one_mul]
  set H : Matrix N N ℝ := regCoef Y α with hHdef
  set c : ℝ := (Fintype.card N : ℝ)⁻¹ with hcdef
  have hc : (0 : ℝ) ≤ c := by positivity
  set S : Matrix N N ℝ := c • (Yᵀ * Y) with hS
  set R : Matrix r r ℝ := c • (Y * Yᵀ) with hR
  have hST : Sᵀ = S := by
    rw [hS, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hSU : IsUnit (S + α • (1 : Matrix N N ℝ)) := by
    have h := isUnit_gram_add Yᵀ hc hα
    rw [Matrix.transpose_transpose] at h
    exact h
  have hRU : IsUnit (R + α • (1 : Matrix r r ℝ)) := isUnit_gram_add Y hc hα
  set G : Matrix N N ℝ := (S + α • (1 : Matrix N N ℝ))⁻¹ with hGdef
  set B : Matrix r r ℝ := (R + α • (1 : Matrix r r ℝ))⁻¹ with hBdef
  have hGL : G * (S + α • (1 : Matrix N N ℝ)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hSU)
  have hGR : (S + α • (1 : Matrix N N ℝ)) * G = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hSU)
  have hBR : (R + α • (1 : Matrix r r ℝ)) * B = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hRU)
  have hPT : (S + α • (1 : Matrix N N ℝ)) * Yᵀ = Yᵀ * (R + α • (1 : Matrix r r ℝ)) := by
    rw [hS, hR]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  have hYB : Yᵀ * B = G * Yᵀ := by
    calc Yᵀ * B = (G * (S + α • (1 : Matrix N N ℝ))) * (Yᵀ * B) := by rw [hGL, Matrix.one_mul]
      _ = G * ((S + α • (1 : Matrix N N ℝ)) * Yᵀ) * B := by simp only [Matrix.mul_assoc]
      _ = G * (Yᵀ * (R + α • (1 : Matrix r r ℝ))) * B := by rw [hPT]
      _ = G * Yᵀ * ((R + α • (1 : Matrix r r ℝ)) * B) := by simp only [Matrix.mul_assoc]
      _ = G * Yᵀ := by rw [hBR, Matrix.mul_one]
  have hHGS : H = G * S := by
    change c • (Yᵀ * B * Y) = G * S
    rw [hYB]
    simp only [hS, Matrix.mul_smul, Matrix.mul_assoc]
  have hGT : Gᵀ = G := by
    rw [hGdef, Matrix.transpose_nonsing_inv, Matrix.transpose_add, hST, Matrix.transpose_smul,
      Matrix.transpose_one]
  have hGS : G * S = S * G := by
    have hcomm : S * (S + α • (1 : Matrix N N ℝ)) = (S + α • (1 : Matrix N N ℝ)) * S := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
    calc G * S = G * S * ((S + α • (1 : Matrix N N ℝ)) * G) := by rw [hGR, Matrix.mul_one]
      _ = G * (S * (S + α • (1 : Matrix N N ℝ))) * G := by simp only [Matrix.mul_assoc]
      _ = G * ((S + α • (1 : Matrix N N ℝ)) * S) * G := by rw [hcomm]
      _ = S * G := by
        rw [← Matrix.mul_assoc G (S + α • (1 : Matrix N N ℝ)) S, hGL, Matrix.one_mul]
  have hsym : Hᵀ = H := by
    rw [hHGS, Matrix.transpose_mul, hST, hGT]
    exact hGS.symm
  have hvec : ∀ x : N → ℝ, (H *ᵥ x) ⬝ᵥ (H *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hx : x = (S + α • (1 : Matrix N N ℝ)) *ᵥ (G *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hGR, Matrix.one_mulVec]
    obtain ⟨w, rfl⟩ : ∃ w, x = (S + α • (1 : Matrix N N ℝ)) *ᵥ w := ⟨G *ᵥ x, hx⟩
    have hcomm : S * (S + α • (1 : Matrix N N ℝ)) = (S + α • (1 : Matrix N N ℝ)) * S := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
    have hHx : H *ᵥ ((S + α • (1 : Matrix N N ℝ)) *ᵥ w) = S *ᵥ w := by
      rw [hHGS]
      calc (G * S) *ᵥ ((S + α • (1 : Matrix N N ℝ)) *ᵥ w)
          = G *ᵥ (S *ᵥ ((S + α • (1 : Matrix N N ℝ)) *ᵥ w)) :=
            (Matrix.mulVec_mulVec _ _ _).symm
        _ = G *ᵥ ((S + α • (1 : Matrix N N ℝ)) *ᵥ (S *ᵥ w)) := by
            congr 1
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
        _ = (G * (S + α • (1 : Matrix N N ℝ))) *ᵥ (S *ᵥ w) := by
            rw [Matrix.mulVec_mulVec]
        _ = S *ᵥ w := by rw [hGL, Matrix.one_mulVec]
    have hSw : (S *ᵥ w) ⬝ᵥ w = c * ((Y *ᵥ w) ⬝ᵥ (Y *ᵥ w)) := by
      rw [hS, Matrix.smul_mulVec, smul_dotProduct, smul_eq_mul, ← Matrix.mulVec_mulVec,
        dotProduct_comm (Yᵀ *ᵥ (Y *ᵥ w)) w, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have hSw_nonneg : 0 ≤ (S *ᵥ w) ⬝ᵥ w := by
      rw [hSw]
      have : 0 ≤ (Y *ᵥ w) ⬝ᵥ (Y *ᵥ w) := by
        unfold dotProduct
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      exact mul_nonneg hc this
    have hww : 0 ≤ w ⬝ᵥ w := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h1 : (α • (1 : Matrix N N ℝ)) *ᵥ w = α • w := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hadd : (S + α • (1 : Matrix N N ℝ)) *ᵥ w = S *ᵥ w + α • w := by
      rw [Matrix.add_mulVec, h1]
    rw [hHx, hadd]
    have e : (S *ᵥ w + α • w) ⬝ᵥ (S *ᵥ w + α • w) =
        (S *ᵥ w) ⬝ᵥ (S *ᵥ w) + 2 * α * ((S *ᵥ w) ⬝ᵥ w) + α ^ 2 * (w ⬝ᵥ w) := by
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        dotProduct_comm w (S *ᵥ w)]
      ring
    rw [e]
    nlinarith [mul_nonneg hα.le hSw_nonneg, mul_nonneg (sq_nonneg α) hww]
  have hvecH : ∀ x : N → ℝ, (H *ᵥ x) ⬝ᵥ (H *ᵥ x) ≤ x ⬝ᵥ x := hvec
  have hH_sq : ‖(1 - P) * f * H‖ ^ 2 ≤ ‖(1 - P) * f‖ ^ 2 :=
    frob_mul_le_of_contraction H hsym hvecH ((1 - P) * f)
  set g : Matrix d N ℝ := P * f + (1 - P) * f * H with hg
  have hi1 : ⟪P * f, (1 - P) * f * H⟫ = 0 := by
    have h := inner_proj_compl P hPt hPP f (f * H)
    rw [← Matrix.mul_assoc (1 - P) f H] at h
    exact h
  have hi2 : ⟪P * f, (1 - P) * f⟫ = 0 := inner_proj_compl P hPt hPP f f
  have hgnorm : ‖g‖ ^ 2 = ‖P * f‖ ^ 2 + ‖(1 - P) * f * H‖ ^ 2 := by
    rw [hg, norm_add_sq_real, hi1]
    ring
  have hf : f = P * f + (1 - P) * f := by
    rw [← Matrix.add_mul]
    simp
  have hfnorm : ‖f‖ ^ 2 = ‖P * f‖ ^ 2 + ‖(1 - P) * f‖ ^ 2 := by
    conv_lhs => rw [hf]
    rw [norm_add_sq_real, hi2]
    ring
  have hgf : ‖g‖ ^ 2 ≤ ‖f‖ ^ 2 := by linarith
  have e1 : ∑ i, ∑ a, g a i ^ 2 = ‖g‖ ^ 2 := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  have e2 : ∑ i, ∑ a, f a i ^ 2 = ‖f‖ ^ 2 := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum, Finset.sum_comm]
  rw [← e1, ← e2] at hgf
  exact mul_le_mul_of_nonneg_left hgf hc

end LeanDLRA.Literature.P2609_20317
