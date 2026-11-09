import LeanDLRA.Matrix.Interpolation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Results of arXiv 2402.03586: Error estimates for SUPG-stabilised DLRA

Nobile and Trigo Trindade, *Error estimates for SUPG-stabilised Dynamical Low Rank
Approximations*. This module formalizes the abstract linear-algebra core of Section 3 only.

## Proved

* `supg_oblique_opNorm_le` (**Lemma 3.1**, arXiv 2402.03586, eq. (14)): in a finite-dimensional real
  inner product space `E` (the discrete space `V_h ⊗ L²_µ̂` is finite-dimensional), let `T` be a
  subspace (the tangent space `T_u M_R`), `H* = 1 + K` with `K` skew (`⟪x, K x⟫ = 0`; the paper's
  `K = -δ b·∇` with `div b = 0`), and `‖H*‖ ≤ 2`. Let `P` be an oblique projection onto `T` in the
  sense of (12): `P x ∈ T` and `⟪P x, H* w⟫ = ⟪x, H* w⟫` for all `w ∈ T`. Then `‖P‖ ≤ 3`, and
  `‖I - P‖ = ‖P‖` whenever `T ≠ ⊥` and `T ≠ ⊤` (Szyld's identity, taken from
  `LeanDLRA.IsObliqueProj.opNorm_one_sub_eq`). The two conditions exclude the degenerate cases:
  for `T = ⊤` one has `P = I` and `‖I - P‖ = 0 ≠ 1 = ‖P‖`.
* `supg_oblique_opNorm_le_orth`: an instance with `K = 0` and `P` the orthogonal projector onto `T`,
  so the hypotheses are satisfiable for every `T`.

## Differences from the paper

* The paper's `H* = I - δb·∇` is abstracted to `1 + K` with `K` skew. Only skewness and the bound
  `‖H*‖ ≤ 2` enter the proof. The paper gets `‖H*‖ ≤ 2` from its step-size condition (5) and the
  inverse inequality; that is a PDE fact, so it is kept as the hypothesis `hG`, and the lemma is
  conditional on it.
* The paper's `P_{H*}` is characterised by (12); here it is any `P` with the same two properties.
  Uniqueness is not needed.

## Not formalized

* Proposition 2.1 (the discrete Petrov–Galerkin identity of Algorithm 1) and Proposition 2.2
  (norm stability), both taken from the companion paper [11] of the authors. They need the
  stochastic update of Algorithm 1 on `V_h ⊗ L²_µ̂` and the bilinear bounds of Lemma 2.1, which
  are PDE statements.
* Lemma 2.1 (continuity and coercivity of `a_SUPG`) and Lemma 3.2 (the stochastic-mode energy
  identity). Lemma 3.2 needs the tensor model `V_h ⊗ L²_µ̂` and the stochastic step (9) of
  Algorithm 1.
* Assumptions 3.1 (model error) and 3.2 (local inverse inequality), and Theorem 3.1 (error estimate
  with hidden constants). Theorem 3.1 depends on the elliptic projection, interpolation estimates,
  and the regularity hypotheses on `u`.
* Section 4 (numerical experiments).
-/

open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2402_03586

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lemma 3.1 of arXiv 2402.03586** (oblique projector bound). Let `T` be a subspace, `H* = 1 + K`
with `K` skew and `‖H*‖ ≤ 2`, and `P` an oblique projection onto `T` in the sense of eq. (12):
`P x ∈ T` and `⟪P x, H* w⟫ = ⟪x, H* w⟫` for every `w ∈ T`. Then `‖P‖ ≤ 3`, and `‖I - P‖ = ‖P‖`
when `0 ≠ T ≠ ⊤` (Szyld's identity; the paper states the equality without these two conditions).
The result is conditional on `‖H*‖ ≤ 2` (hypothesis `hG`), which the paper derives from its
condition (5) on `δ`. See the module docstring for the differences from the paper. -/
theorem supg_oblique_opNorm_le (T : Submodule ℝ E) (K : E →L[ℝ] E)
    (hK : ∀ x : E, ⟪x, K x⟫ = 0) (hG : ‖(1 : E →L[ℝ] E) + K‖ ≤ 2)
    (P : E →L[ℝ] E) (hPT : ∀ x, P x ∈ T)
    (hP : ∀ x, ∀ w ∈ T, ⟪P x, ((1 : E →L[ℝ] E) + K) w⟫ = ⟪x, ((1 : E →L[ℝ] E) + K) w⟫) :
    ‖P‖ ≤ 3 ∧ (T ≠ ⊥ → T ≠ ⊤ → ‖(1 : E →L[ℝ] E) - P‖ = ‖P‖) := by
  -- the orthogonal projector Q onto T
  set Q : E →L[ℝ] E := T.starProjection with hQdef
  have hQmem : ∀ x, Q x ∈ T := fun x => T.starProjection_apply_mem x
  have hQfix : ∀ w ∈ T, Q w = w := fun w hw => T.starProjection_eq_self_iff.2 hw
  have hQ : IsOrthProj Q :=
    { idem := fun x => hQfix _ (hQmem x)
      symm := fun x y => T.inner_starProjection_left_eq_right x y }
  -- coercivity of H*: ⟪z, H* z⟫ = ‖z‖²
  have hcoer : ∀ z : E, ⟪z, ((1 : E →L[ℝ] E) + K) z⟫ = ‖z‖ ^ 2 := by
    intro z
    simp [inner_add_right, hK]
  -- P fixes T pointwise
  have hPfix : ∀ w ∈ T, P w = w := by
    intro w hw
    have hz : P w - w ∈ T := T.sub_mem (hPT w) hw
    have h0 : ⟪P w - w, ((1 : E →L[ℝ] E) + K) (P w - w)⟫ = 0 := by
      rw [inner_sub_left, hP w _ hz, sub_self]
    rw [hcoer] at h0
    exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))
  -- the key estimate: ‖P x - Q x‖ ≤ 2 ‖x - Q x‖
  have hkey : ∀ x : E, ‖P x - Q x‖ ≤ 2 * ‖x - Q x‖ := by
    intro x
    have hz : P x - Q x ∈ T := T.sub_mem (hPT x) (hQmem x)
    have h1 : ‖P x - Q x‖ ^ 2 = ⟪x - Q x, ((1 : E →L[ℝ] E) + K) (P x - Q x)⟫ := by
      rw [← hcoer (P x - Q x), inner_sub_left, inner_sub_left, hP x _ hz]
    have h2 : ‖((1 : E →L[ℝ] E) + K) (P x - Q x)‖ ≤ 2 * ‖P x - Q x‖ :=
      calc ‖((1 : E →L[ℝ] E) + K) (P x - Q x)‖
          ≤ ‖(1 : E →L[ℝ] E) + K‖ * ‖P x - Q x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 2 * ‖P x - Q x‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    have h3 : ‖P x - Q x‖ ^ 2 ≤ ‖x - Q x‖ * (2 * ‖P x - Q x‖) := by
      rw [h1]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    nlinarith [norm_nonneg (P x - Q x), norm_nonneg (x - Q x)]
  -- ‖P‖ ≤ 3
  have hnorm : ‖P‖ ≤ 3 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
    have e : ‖P x‖ ≤ ‖P x - Q x‖ + ‖Q x‖ := by
      calc ‖P x‖ = ‖(P x - Q x) + Q x‖ := by rw [sub_add_cancel]
        _ ≤ ‖P x - Q x‖ + ‖Q x‖ := norm_add_le _ _
    have f1 : ‖x - Q x‖ ≤ ‖x‖ := hQ.norm_sub_le x
    have f2 : ‖Q x‖ ≤ ‖x‖ := hQ.norm_le x
    have f3 := hkey x
    linarith
  refine ⟨hnorm, fun hT0 hT1 => ?_⟩
  -- P is an oblique projector onto Q in the sense of the library, so Szyld's identity applies
  have hobl : IsObliqueProj P Q :=
    { orth := hQ
      fix := fun x => hPfix _ (hQmem x)
      range := fun x => hQfix _ (hPT x) }
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hT0
    rw [eq_bot_iff]
    intro w hw
    have h' := hQfix w hw
    rw [h, zero_apply] at h'
    exact (Submodule.mem_bot ℝ).2 h'.symm
  have hQ1 : Q ≠ 1 := by
    intro h
    apply hT1
    rw [eq_top_iff]
    intro x _
    have hx : Q x = x := by simp [h]
    have h' := hQmem x
    rwa [hx] at h'
  exact hobl.opNorm_one_sub_eq hQ0 hQ1

/-- Instance of `supg_oblique_opNorm_le` with `K = 0` (so `H* = 1`) and `P` the orthogonal projector
onto `T`: the hypotheses hold for every subspace `T`, so the statement is not vacuous. -/
theorem supg_oblique_opNorm_le_orth (T : Submodule ℝ E) : ‖T.starProjection‖ ≤ 3 := by
  have hK : ∀ x : E, ⟪x, (0 : E →L[ℝ] E) x⟫ = 0 := fun x => by simp
  have hG : ‖(1 : E →L[ℝ] E) + 0‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
    simp only [add_zero, one_apply_eq_self]
    linarith [norm_nonneg x]
  have hP : ∀ x, ∀ w ∈ T, ⟪T.starProjection x, ((1 : E →L[ℝ] E) + 0) w⟫ =
      ⟪x, ((1 : E →L[ℝ] E) + 0) w⟫ := by
    intro x w hw
    simp only [add_zero, one_apply_eq_self]
    rw [T.inner_starProjection_left_eq_right, T.starProjection_eq_self_iff.2 hw]
  exact (supg_oblique_opNorm_le T 0 hK hG T.starProjection
    (fun x => T.starProjection_apply_mem x) hP).1

end LeanDLRA.Literature.P2402_03586
