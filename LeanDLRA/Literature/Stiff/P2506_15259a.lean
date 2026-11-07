import Mathlib
import LeanDLRA.Matrix.Projectors

/-!
# Stiff matrix ODEs: exact flow, variation of constants, low-rank splittings (arXiv 2506.15259)

For `Ẋ = AX + XAᵀ + F(t,X)` with square `A` (the paper's linear term only typechecks for square
`A`), this module formalizes Sec. 2 of arXiv 2506.15259: the exact flow
`Φ^A_τ(M) = e^{τA} M e^{τAᵀ}` of the stiff subproblem, its rank preservation, its tangent-space
property, the variation-of-constants formula, and the low-rank Lie–Trotter and Strang splittings of
Eq. (4), which keep rank `r` whenever the non-stiff low-rank integrator does.

Proved (arXiv 2506.15259):
* `rank_linFlow`: `rank (e^{τA} M e^{τAᵀ}) = rank M` (Sec. 2.2).
* `linFlow_mem_tangent`: the tangent projector at `Y = U S Vᵀ` fixes `AY + YAᵀ` (Sec. 2.2).
* `hasDerivAt_linFlow`: `s ↦ Φ^A_{s-t₀}(M₀)` solves `Ṁ = AM + MAᵀ` (Eq. (2)).
* `variation_of_constants`: the variation-of-constants formula (Sec. 2). Its integrability
  hypothesis is continuity of `s ↦ F(s, X(s))` on `[t₀, t]`; the paper does not state it.
* `variation_of_constants_nonvacuous`: the hypotheses of that formula are satisfiable (`F = 0`).
* `lowRankLie_rank`, `lowRankStrang_rank`: if `Φ̃^F_τ` maps into rank-`r` matrices, then `L̃_τ` and
  `S̃_τ` do too (Eq. (4), Sec. 2.2 "rank-r approximation"). `lowRankLie_rank_nonvacuous` exhibits an
  instance.

Definitions: `linFlow` (`Φ^A_τ`), `lowRankLie` (`L̃_τ`), `lowRankStrang` (`S̃_τ`), as in Eq. (4).
Core definitions used: `LeanDLRA.tangentProj` and its characterization `tangentProj_eq_self_iff`
(`LeanDLRA/Matrix/Projectors.lean`). Nothing else from the core is needed.
The non-stiff integrator `Φ̃^F_τ` is an arbitrary map `G`; the DRSVD/DGN construction is not
formalized. The derivative lemmas use the `Matrix.linftyOp*` norm, supplied by the local
instances below.

Not formalized, with reason:
* Convergence orders of Lie–Trotter (first order) and Strang (second order), and stability claims:
  cited in the paper, not proved there, and they need a stiff local error analysis.
* The DRSVD/DGN integrator and its rank-adaptive variants (Sec. 2.3, Algorithms A.1 onward): the
  paper cites them from Carrel; `Φ̃^F_τ` is abstract here.
* The DRSVD reconstruction-exactness claim (Sec. 2.3.1): not stated as a theorem in this paper.
* The QR factorization `W_τ = Ũ S̃ Ṽᵀ` (Sec. 2.2): algorithmic, not a result.
-/

open Set Filter Topology Finset MeasureTheory
open scoped Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace LeanDLRA.Literature.P2506_15259

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact flow `Φ^A_τ(M) = e^{τA} M e^{τAᵀ}` of the stiff subproblem `Ṁ = AM + MAᵀ`
(paper Sec. 2.1, Eq. (2)). -/
noncomputable def linFlow (A : Matrix n n ℝ) (τ : ℝ) (M : Matrix n n ℝ) : Matrix n n ℝ :=
  NormedSpace.exp (τ • A) * M * NormedSpace.exp (τ • Aᵀ)

/-- Low-rank Lie–Trotter step `L̃_τ = Φ^A_τ ∘ Φ̃^F_τ` (paper Eq. (4)). -/
noncomputable def lowRankLie (A : Matrix n n ℝ) (τ : ℝ) (G : Matrix n n ℝ → Matrix n n ℝ)
    (Y : Matrix n n ℝ) : Matrix n n ℝ :=
  linFlow A τ (G Y)

/-- Low-rank Strang step `S̃_τ = Φ^A_{τ/2} ∘ Φ̃^F_τ ∘ Φ^A_{τ/2}` (paper Eq. (4)). -/
noncomputable def lowRankStrang (A : Matrix n n ℝ) (τ : ℝ) (G : Matrix n n ℝ → Matrix n n ℝ)
    (Y : Matrix n n ℝ) : Matrix n n ℝ :=
  linFlow A (τ / 2) (G (linFlow A (τ / 2) Y))

/-- Helper for `rank_linFlow` (arXiv 2506.15259, Sec. 2.1): `e^{τA}` has inverse `e^{-τA}`. -/
lemma exp_smul_mul_exp_neg_smul (A : Matrix n n ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • A) * NormedSpace.exp (-(τ • A)) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (τ • A)).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

/-- Helper for `rank_linFlow` (arXiv 2506.15259, Sec. 2.1): `det e^{τA}` is a unit. -/
lemma isUnit_det_exp_smul (A : Matrix n n ℝ) (τ : ℝ) :
    IsUnit (NormedSpace.exp (τ • A)).det :=
  Matrix.isUnit_det_of_right_inverse (exp_smul_mul_exp_neg_smul A τ)

/-- **Sec. 2.2 (rank preservation of the exact stiff flow), arXiv 2506.15259.**
The exact solution of `Ṁ = AM + MAᵀ` keeps the rank: `rank(e^{τA} M e^{τAᵀ}) = rank M`. -/
theorem rank_linFlow (A : Matrix n n ℝ) (τ : ℝ) (M : Matrix n n ℝ) :
    (linFlow A τ M).rank = M.rank := by
  have hT : NormedSpace.exp (τ • Aᵀ) = (NormedSpace.exp (τ • A))ᵀ := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  have hU : IsUnit (NormedSpace.exp (τ • Aᵀ)).det := by
    rw [hT, Matrix.det_transpose]
    exact isUnit_det_exp_smul A τ
  unfold linFlow
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hU,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_exp_smul A τ)]

omit [DecidableEq n] in
/-- **Sec. 2.2 (tangent space), arXiv 2506.15259.** For `Y = U S Vᵀ` with orthonormal `U`, `V`, the
matrix `AY + YAᵀ` is fixed by the tangent-space projector at `Y`, i.e. lies in the tangent space
`{U B + C Vᵀ}` of the rank-`r` manifold. -/
theorem linFlow_mem_tangent {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] (A : Matrix n n ℝ) {U : Matrix n k ℝ} {V : Matrix n k' ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (S : Matrix k k' ℝ) :
    LeanDLRA.tangentProj U V (A * (U * S * Vᵀ) + (U * S * Vᵀ) * Aᵀ) =
      A * (U * S * Vᵀ) + (U * S * Vᵀ) * Aᵀ := by
  refine (LeanDLRA.tangentProj_eq_self_iff hU hV _).2 ⟨S * Vᵀ * Aᵀ, A * U * S, ?_⟩
  simp only [Matrix.mul_assoc]
  exact add_comm _ _

/-- **Sec. 2.2 (rank of the low-rank splittings), arXiv 2506.15259, Eq. (4).** If the non-stiff
low-rank integrator `Φ̃^F_τ = G` maps every matrix to a rank-`r` matrix, then so do the low-rank
Lie–Trotter step `L̃_τ` and the Strang step `S̃_τ`. -/
theorem lowRankLie_rank (A : Matrix n n ℝ) (τ : ℝ) (G : Matrix n n ℝ → Matrix n n ℝ) (r : ℕ)
    (hG : ∀ N, (G N).rank = r) (Y : Matrix n n ℝ) : (lowRankLie A τ G Y).rank = r := by
  unfold lowRankLie
  rw [rank_linFlow, hG]

/-- **Sec. 2.2 (rank of the low-rank splittings), arXiv 2506.15259, Eq. (4).** Strang version of
`lowRankLie_rank`: the step `S̃_τ` has rank `r` whenever `Φ̃^F_τ = G` has rank `r`. -/
theorem lowRankStrang_rank (A : Matrix n n ℝ) (τ : ℝ) (G : Matrix n n ℝ → Matrix n n ℝ) (r : ℕ)
    (hG : ∀ N, (G N).rank = r) (Y : Matrix n n ℝ) : (lowRankStrang A τ G Y).rank = r := by
  unfold lowRankStrang
  rw [rank_linFlow, hG]

/-- Helper for `variation_of_constants` (arXiv 2506.15259, Sec. 2). The algebraic identity behind
the product rule for `e^{(t-s)A} X(s) e^{(t-s)Aᵀ}`: the two
derivative terms `∓ e^{(t-s)A} A X …` and `… Aᵀ e^{(t-s)Aᵀ}` cancel, leaving `E F Eᵀ`. -/
lemma prod_rule_algebra {R : Type*} [Ring R] (E A X B Et F : R) :
    (-(E * A) * X + E * (A * X + X * B + F)) * Et + E * X * -(B * Et) = E * F * Et := by
  simp only [add_mul, mul_add, neg_mul, mul_neg, mul_assoc]
  abel

/-- **Sec. 2 (variation-of-constants formula), arXiv 2506.15259.** For `Ẋ = AX + XAᵀ + F(t,X)` on
`[t₀, t]` with `X(t₀) = X₀`,
`X(t) = e^{(t−t₀)A} X₀ e^{(t−t₀)Aᵀ} + ∫_{t₀}^{t} e^{(t−s)A} F(s,X(s)) e^{(t−s)Aᵀ} ds`.
Hypotheses: `X` solves the ODE on `[t₀, t]`, and `s ↦ F(s, X(s))` is continuous there (needed so
that the integral exists; the paper does not state this regularity). -/
theorem variation_of_constants (A : Matrix n n ℝ) (F : ℝ → Matrix n n ℝ → Matrix n n ℝ)
    (X : ℝ → Matrix n n ℝ) {t₀ t : ℝ} (ht : t₀ ≤ t) (X₀ : Matrix n n ℝ) (hinit : X t₀ = X₀)
    (hODE : ∀ s ∈ Icc t₀ t, HasDerivAt X (A * X s + X s * Aᵀ + F s (X s)) s)
    (hF : ContinuousOn (fun s => F s (X s)) (Icc t₀ t)) :
    X t = NormedSpace.exp ((t - t₀) • A) * X₀ * NormedSpace.exp ((t - t₀) • Aᵀ)
      + ∫ s in t₀..t,
        NormedSpace.exp ((t - s) • A) * F s (X s) * NormedSpace.exp ((t - s) • Aᵀ) := by
  have hE : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp ((t - s) • A))
      (-(NormedSpace.exp ((t - s) • A) * A)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h2 := (hasDerivAt_exp_smul_const A (t - s)).scomp s h1
    exact h2.congr_deriv (neg_one_smul ℝ _)
  have hEt : ∀ s : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp ((t - s) • Aᵀ))
      (-(Aᵀ * NormedSpace.exp ((t - s) • Aᵀ))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h2 := (hasDerivAt_exp_smul_const' Aᵀ (t - s)).scomp s h1
    exact h2.congr_deriv (neg_one_smul ℝ _)
  have hg : ∀ s ∈ Icc t₀ t,
      HasDerivAt (fun s : ℝ => NormedSpace.exp ((t - s) • A) * X s *
        NormedSpace.exp ((t - s) • Aᵀ))
        (NormedSpace.exp ((t - s) • A) * F s (X s) * NormedSpace.exp ((t - s) • Aᵀ)) s := by
    intro s hs
    have h := ((hE s).fun_mul (hODE s hs)).fun_mul (hEt s)
    exact h.congr_deriv (prod_rule_algebra (R := Matrix n n ℝ) _ _ _ _ _ _)
  have hcont : ContinuousOn (fun s => NormedSpace.exp ((t - s) • A) * F s (X s) *
      NormedSpace.exp ((t - s) • Aᵀ)) (Icc t₀ t) :=
    ContinuousOn.mul (ContinuousOn.mul (fun s _ => (hE s).continuousAt.continuousWithinAt) hF)
      (fun s _ => (hEt s).continuousAt.continuousWithinAt)
  have hint := hcont.intervalIntegrable_of_Icc (μ := (volume : Measure ℝ)) ht
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hg s (by rwa [uIcc_of_le ht] at hs)) hint
  rw [hftc, hinit]
  simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  abel

/-- **Sec. 2.1 (exact stiff subproblem), arXiv 2506.15259, Eq. (2).** The exact flow solves
`Ṁ = AM + MAᵀ`: `s ↦ Φ^A_{s-t₀}(M₀)` has derivative `A M(s) + M(s) Aᵀ`. -/
theorem hasDerivAt_linFlow (A : Matrix n n ℝ) (t₀ : ℝ) (M₀ : Matrix n n ℝ) (s : ℝ) :
    HasDerivAt (fun s => linFlow A (s - t₀) M₀)
      (A * linFlow A (s - t₀) M₀ + linFlow A (s - t₀) M₀ * Aᵀ) s := by
  have hE : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s - t₀) • A))
      (NormedSpace.exp ((s - t₀) • A) * A) s := by
    have h1 : HasDerivAt (fun s : ℝ => s - t₀) 1 s := (hasDerivAt_id' s).sub_const t₀
    exact ((hasDerivAt_exp_smul_const A (s - t₀)).scomp s h1).congr_deriv (one_smul ℝ _)
  have hEt : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s - t₀) • Aᵀ))
      (NormedSpace.exp ((s - t₀) • Aᵀ) * Aᵀ) s := by
    have h1 : HasDerivAt (fun s : ℝ => s - t₀) 1 s := (hasDerivAt_id' s).sub_const t₀
    exact ((hasDerivAt_exp_smul_const Aᵀ (s - t₀)).scomp s h1).congr_deriv (one_smul ℝ _)
  have hc : A * NormedSpace.exp ((s - t₀) • A) = NormedSpace.exp ((s - t₀) • A) * A :=
    (((Commute.refl A).smul_right (s - t₀)).exp_right).eq
  have h := (hE.mul_const M₀).fun_mul hEt
  refine h.congr_deriv ?_
  unfold linFlow
  rw [← hc]
  simp only [Matrix.mul_assoc]

/-- **Sec. 2 (non-vacuity of the variation-of-constants formula), arXiv 2506.15259.** For every
`X₀` and `t` there are `F` and `X` satisfying the hypotheses of `variation_of_constants` (with
`F = 0` and `X(s) = Φ^A_{s-t₀}(X₀)`), and the solution at time `t` is `Φ^A_{t-t₀}(X₀)`. -/
theorem variation_of_constants_nonvacuous (A : Matrix n n ℝ) {t₀ t : ℝ}
    (X₀ : Matrix n n ℝ) :
    ∃ (F : ℝ → Matrix n n ℝ → Matrix n n ℝ) (X : ℝ → Matrix n n ℝ),
      X t₀ = X₀ ∧
      (∀ s ∈ Icc t₀ t, HasDerivAt X (A * X s + X s * Aᵀ + F s (X s)) s) ∧
      ContinuousOn (fun s => F s (X s)) (Icc t₀ t) ∧
      X t = linFlow A (t - t₀) X₀ :=
  ⟨fun _ _ => 0, fun s => linFlow A (s - t₀) X₀, by simp [linFlow],
    fun s _ => (hasDerivAt_linFlow A t₀ X₀ s).congr_deriv (add_zero _).symm,
    continuousOn_const, rfl⟩

omit [DecidableEq n] in
/-- Non-vacuity of `lowRankLie_rank`: the rank hypothesis holds for `G = 1` at full rank `r = n`. -/
lemma lowRankLie_rank_nonvacuous :
    ∃ (G : Matrix n n ℝ → Matrix n n ℝ), ∀ N, (G N).rank = Fintype.card n := by
  classical
  exact ⟨fun _ => 1, fun _ => Matrix.rank_one⟩

end LeanDLRA.Literature.P2506_15259
