import LeanDLRA.Matrix.Frobenius
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Results of arXiv 2609.20307: Existence of DLRA for SDEs with locally Lipschitz coefficients

This module formalizes the deterministic part of Lemma 2.1 (Kazashi–Nobile–Zoccolan,
arXiv 2609.20307): if a curve `U : [0, T] → ℝ^{k×d}` is absolutely continuous, has
orthonormal rows at `t = 0`, and satisfies `U_t U̇_tᵀ = 0` for a.e. `t` (the orthogonality
condition of a strong DO solution, Definition 1.1, items 1–2), then `U_t Uᵀ_t = I_k` for all
`t ∈ [0, T]` and `‖U_t‖_F = √k`.  The proof shows that `t ↦ U_t Uᵀ_t` is absolutely
continuous with a.e. zero derivative, hence constant (Mathlib's
`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`).

Not formalized: the moment bound
`E sup_t |Y_t|^{2+ε} ≤ C_{T,ε}(1 + E|Y₀|^{2+ε})` of Lemma 2.1,
since it concerns stochastic integrals and the stochastic basis `Y`.

Proposition 2.2 (Gram-inverse ball) is not reproved here: the library proves its main claim
(`‖C_Z⁻¹‖_F ≤ 2γ` on `B_η(Z₀)`) as `LeanDLRA.gramMatrix_inv_ball`
(`LeanDLRA/Foundations/Localization.lean`).  The paper's hypothesis "linearly independent
components" is there replaced by invertibility of the Gram matrix, which is equivalent for `Z₀`
in `[H]^k`.  The last claim of Proposition 2.2, that `η(ρ, γ)` is decreasing in `ρ` and `γ`, is
not formalized.

Core definitions used: the Frobenius norm and scoped instances of `LeanDLRA.Frobenius`
(`norm_def`, `hasDerivAt_mul`, `hasDerivAt_transpose`).  No local definitions are added.
-/

open scoped LeanDLRA.Frobenius Matrix
open MeasureTheory Set

namespace LeanDLRA.Literature.P2609_20307

variable {k d : ℕ}

/-- Entries of an absolutely continuous matrix-valued curve are absolutely continuous. -/
lemma ac_entry {U : ℝ → Matrix (Fin k) (Fin d) ℝ} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) (i : Fin k) (l : Fin d) :
    AbsolutelyContinuousOnInterval (fun t => U t i l) a b := by
  have hL : LipschitzWith 1 (fun M : Matrix (Fin k) (Fin d) ℝ => M i l) := by
    refine LipschitzWith.of_dist_le_mul fun M N => ?_
    have h := LeanDLRA.Frobenius.abs_apply_le_norm (M - N) i l
    rw [Matrix.sub_apply] at h
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact h
  exact hL.comp_absolutelyContinuousOnInterval hU

/-- Constant real functions are absolutely continuous. -/
lemma ac_real_const (c : ℝ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

/-- Constant matrix-valued curves are absolutely continuous. -/
lemma ac_const (c : Matrix (Fin k) (Fin d) ℝ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

/-- Entries of `t ↦ U_t Uᵀ_t` are absolutely continuous. -/
lemma ac_gram_entry {U : ℝ → Matrix (Fin k) (Fin d) ℝ} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) (i j : Fin k) :
    AbsolutelyContinuousOnInterval (fun t => (U t * (U t)ᵀ) i j) a b := by
  have key : ∀ s : Finset (Fin d),
      AbsolutelyContinuousOnInterval (fun t => ∑ l ∈ s, U t i l * U t j l) a b := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using ac_real_const 0 a b
    | insert l s hl ih =>
      simp only [Finset.sum_insert hl]
      exact ((ac_entry hU i l).mul (ac_entry hU j l)).add ih
  have e : (fun t => (U t * (U t)ᵀ) i j) = fun t => ∑ l, U t i l * U t j l := by
    funext t
    simp [Matrix.mul_apply]
  rw [e]
  exact key Finset.univ

/-- **Orthonormality of the rows is preserved** (Lemma 2.1, first part, arXiv 2609.20307).
Let `U : [0, T] → ℝ^{k×d}` be absolutely continuous with `U_0 U_0ᵀ = I_k`, differentiable
a.e. with derivative `U'`, and `U_t U'_tᵀ = 0` for a.e. `t`.  Then `U_t Uᵀ_t = I_k` on
`[0, T]`.  The paper's equation (2) enters only through the orthogonality `U_t U̇_tᵀ = 0`
of Definition 1.1, item 2 (the paper's proof derives the equivalent `U̇_t U_tᵀ = 0` from (2)).
The a.e. differentiability is assumed explicitly (`hder`); the paper infers it from absolute
continuity.  Assumptions 1 and 3 of Lemma 2.1 and the stochastic basis `Y` are not needed. -/
theorem rows_orthonormal_const {U U' : ℝ → Matrix (Fin k) (Fin d) ℝ} {T : ℝ}
    (hU : AbsolutelyContinuousOnInterval U 0 T)
    (hder : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → HasDerivAt U (U' t) t)
    (hort : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → U t * (U' t)ᵀ = 0)
    (hU0 : U 0 * (U 0)ᵀ = 1) :
    ∀ t ∈ uIcc 0 T, U t * (U t)ᵀ = 1 := by
  have hcst : ∀ i j : Fin k, ∀ t ∈ uIcc 0 T, (U t * (U t)ᵀ) i j = (U 0 * (U 0)ᵀ) i j := by
    intro i j
    have hz : ∀ᵐ t ∂volume, t ∈ uIcc 0 T →
        HasDerivAt (fun t => (U t * (U t)ᵀ) i j) 0 t := by
      filter_upwards [hder, hort] with t h1 h2 ht
      have hE : ∀ p q, HasDerivAt (fun s => U s p q) (U' t p q) t := fun p q =>
        hasDerivAt_pi.1 (hasDerivAt_pi.1 (h1 ht) p) q
      have hsum := HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun l s => U s i l * U s j l)
        (A' := fun l => U' t i l * U t j l + U t i l * U' t j l)
        (x := t) (fun l _ => (hE i l).mul (hE j l))
      have e1 : ∑ l, U t i l * U' t j l = 0 := by
        have h := congrFun (congrFun (h2 ht) i) j
        simpa [Matrix.mul_apply] using h
      have e2 : ∑ l, U t j l * U' t i l = 0 := by
        have h := congrFun (congrFun (h2 ht) j) i
        simpa [Matrix.mul_apply] using h
      have e2' : ∑ l, U' t i l * U t j l = ∑ l, U t j l * U' t i l :=
        Finset.sum_congr rfl fun l _ => mul_comm _ _
      convert hsum using 1
      · funext s
        simp [Matrix.mul_apply]
      · simp only [Finset.sum_add_distrib, e2', e2, e1, add_zero]
    obtain ⟨C, hC⟩ := (ac_gram_entry hU i j).const_of_ae_hasDerivAt_zero hz
    intro t ht
    have h0 : (0 : ℝ) ∈ uIcc 0 T := left_mem_uIcc
    exact (hC t ht).trans (hC 0 h0).symm
  intro t ht
  ext i j
  rw [hcst i j t ht, hU0]

/-- **Frobenius norm of the DLRA basis** (Lemma 2.1, first part, arXiv 2609.20307):
`‖U_t‖_F = √k` for all `t ∈ [0, T]`, under the hypotheses of `rows_orthonormal_const`. -/
theorem frobenius_norm_of_rows_orthonormal {U U' : ℝ → Matrix (Fin k) (Fin d) ℝ} {T : ℝ}
    (hU : AbsolutelyContinuousOnInterval U 0 T)
    (hder : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → HasDerivAt U (U' t) t)
    (hort : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → U t * (U' t)ᵀ = 0)
    (hU0 : U 0 * (U 0)ᵀ = 1) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖U t‖ = √(k : ℝ) := by
  intro t ht
  have hUU := rows_orthonormal_const hU hder hort hU0 t (Icc_subset_uIcc ht)
  rw [LeanDLRA.Frobenius.norm_def]
  congr 1
  have hdiag : ∑ i, ∑ j, U t i j ^ 2 = ∑ i : Fin k, (U t * (U t)ᵀ) i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_apply, sq]
  rw [hdiag, hUU]
  simp

/-- Non-vacuity: the constant curve `U_t = Id_k` (with `d = k`) satisfies the hypotheses. -/
example (k : ℕ) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 : Matrix (Fin k) (Fin k) ℝ)‖ = √(k : ℝ) :=
  frobenius_norm_of_rows_orthonormal (U := fun _ => (1 : Matrix (Fin k) (Fin k) ℝ))
    (U' := fun _ => 0) (ac_const _ 0 1)
    (Filter.Eventually.of_forall fun t _ => hasDerivAt_const t _)
    (Filter.Eventually.of_forall fun t _ => by simp) (by simp)

end LeanDLRA.Literature.P2609_20307
