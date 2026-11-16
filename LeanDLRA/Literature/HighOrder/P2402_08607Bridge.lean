import LeanDLRA.Literature.HighOrder.P2402_08607a
import LeanDLRA.HighOrder.MidpointBUGStep

/-!
# The midpoint BUG (4r) step of arXiv:2402.08607 as a step of the core relation

The catalogue structure `Literature.P2402_08607.IsMidpoint4rStep` states one step of the midpoint
BUG integrator (Ceruti, Einkemmer, Kusch and Lubich, arXiv:2402.08607, §3, Algorithm 1, 4r) with
a step size `h`, one number of columns for both Galerkin bases, and the capture of
`h F(t½, Ŷ½) V̂` and `h F(t½, Ŷ½)ᵀ Û`. The core states the same step as
`MatrixMidpointBUG.IsStep` over `[t₀, t₁]`. This file shows that for `h > 0` every catalogue step
is a core step, so that the run theorems of the core
(`MatrixMidpointBUG.exists_run_norm_sub_le`, `MatrixMidpointBUG.IsRun.norm_sub_le`) apply to the
steps of the paper.

## Main results

* `Literature.P2402_08607.IsMidpoint4rStep.isStep`: a catalogue step with `h > 0` is a step
  `MatrixMidpointBUG.IsStep F t₀ (t₀ + h)`.
* `Literature.P2402_08607.IsMidpoint4rStep.augmentedRel`: with `2 r` columns in the half step and
  at most `4 r` columns in the Galerkin bases, its result is a step of
  `MatrixMidpointBUG.augmentedRel F r`.

## References

* G. Ceruti, L. Einkemmer, J. Kusch, Ch. Lubich, *A robust second-order low-rank BUG integrator
  based on the midpoint rule*, arXiv:2402.08607.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2402_08607

variable {m n : Type*} [Fintype m] [Fintype n] {r rh rb : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ h : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m (Fin rh) ℝ}
  {Vh : Matrix n (Fin rh) ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {Sh : ℝ → Matrix (Fin rh) (Fin rh) ℝ} {Ub : Matrix m (Fin rb) ℝ} {Vb : Matrix n (Fin rb) ℝ}
  {Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ}

/-- **A catalogue midpoint BUG (4r) step is a core factor step.** For `h > 0` the step
`IsMidpoint4rStep F t₀ h …` of arXiv:2402.08607 is a step `MatrixMidpointBUG.IsStep` over
`[t₀, t₀ + h]` with the same factors: the midpoint `t₀ + h / 2` is `(t₀ + (t₀ + h)) / 2`, and
the capture of `h F(t½, Ŷ½) V̂` is the capture of `F(t½, Ŷ½) V̂` (`IsGalerkinPart.capF'`). -/
theorem IsMidpoint4rStep.isStep (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hh : 0 < h) : MatrixMidpointBUG.IsStep F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb := by
  have e : (t₀ + (t₀ + h)) / 2 = t₀ + h / 2 := by ring
  refine ⟨?_, hs.galerkin.orthUb, hs.galerkin.orthVb, hs.galerkin.capU, hs.galerkin.capV, ?_, ?_,
    hs.galerkin.sSol, hs.galerkin.sStart⟩
  · rw [e]
    exact hs.half
  · rw [e]
    exact hs.galerkin.capF' hh
  · rw [e]
    exact hs.galerkin.capFt' hh

/-- **The result of a catalogue midpoint BUG (4r) step is a step of the core relation.** If the
half step has `2 r` columns, the Galerkin bases have at most `4 r` columns and `h > 0`, then
`Ub Sb(t₀ + h) Vbᵀ` is a result of `MatrixMidpointBUG.augmentedRel F r` from `U₀ S₀ V₀ᵀ` over
`[t₀, t₀ + h]`. -/
theorem IsMidpoint4rStep.augmentedRel {Uh : Matrix m (Fin (2 * r)) ℝ}
    {Vh : Matrix n (Fin (2 * r)) ℝ} {Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ}
    (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) (hh : 0 < h)
    (hrb : rb ≤ 4 * r) :
    MatrixMidpointBUG.augmentedRel F r t₀ (t₀ + h) (U₀ * S₀ * V₀ᵀ) (Ub * Sb (t₀ + h) * Vbᵀ) :=
  (hs.isStep hh).augmentedRel hrb hrb

/-- **Non-vacuity.** For a Lipschitz, bounded field that is continuous in time, `4 r ≤ m`,
`4 r ≤ n` and `h > 0`, every factorization with orthonormal `U₀`, `V₀` starts a catalogue step
(`exists_isMidpoint4rStep`), and its result is a step of the core relation
`MatrixMidpointBUG.augmentedRel F r`. -/
example {L B : ℝ} (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hh : 0 < h) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hm : 4 * r ≤ Fintype.card m)
    (hn : 4 * r ≤ Fintype.card n) :
    ∃ Y₁, MatrixMidpointBUG.augmentedRel F r t₀ (t₀ + h) (U₀ * S₀ * V₀ᵀ) Y₁ := by
  obtain ⟨Uh, Vh, K, Lf, Sh, Ub, Vb, Sb, hs⟩ :=
    exists_isMidpoint4rStep hF hB hc (t₀ := t₀) hh.le S₀ hU₀ hV₀ hm hn
  exact ⟨_, hs.augmentedRel hh le_rfl⟩

end LeanDLRA.Literature.P2402_08607
