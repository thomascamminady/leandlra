import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# Growth of the distance to the matrices of rank at most `r` along the exact flow

`distLR r X` is the Frobenius distance of `X` to the matrices of rank at most `r`. For an
`L`-Lipschitz, bounded field whose normal part at factored matrices of rank `r` is at most `ε`
(`MatrixBUG.FactoredNormalBound F r ε`), this distance satisfies along every exact solution a bound
of Grönwall type with the constant one in front of `ε`, without a condition on the rank of the
starting value. The bound is `LeanDLRA.distLR_flow_le_exp_mul_add` in
`LeanDLRA/Matrix/LowRankDistance.lean`; this file keeps the recorded form of the statement.

## Main results

* `distLR_flow_le_sharp`: for an exact solution `A` on `[t₀, t₁]`,
  `distLR r (A t) ≤ e^{L (t - t₀)} distLR r (A t₀) + ε (t - t₀) e^{L (t - t₀)}`, with the
  additional hypothesis that the field is continuous in time.

## Implementation notes

The bound is an upper bound, and continuity of the field in time is not needed for it. For a
start of rank at most `r` it gives `h ε e^{L h}` after time `h` (`distLR_flow_le_exp`). That the
constant in front of `ε` cannot be lowered is not proved here: for the constant field
`F ≡ [[0, 1], [1, 0]]` (`L = 0`, `r = 1`) the library certifies the lower bound `t / 3` for the
distance of `A t = t F` (`le_distLR_cx`), not its exact value. For `0 < L` and a start of rank at
most `r`, `LeanDLRA.OpenProblems.RankAdaptivity.distLR_flow_le_dini_local` proves the smaller
expression `ε (e^{L τ} - 1) / L` in the place of `ε τ e^{L τ}`, with `ε` assumed only near the
exact solution; the form stated here needs no separate case `L = 0` and no condition on the rank
of the start.
-/

open Set Finset Matrix

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n]

end Truncation

section Tie

open EckartYoung

end Tie

section Distance

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

/-- **Growth of the distance to `M_{≤ r}` with the constant one in front of `ε`.** Along every
exact solution, starting anywhere,
`dist(A(t), M_{≤ r}) ≤ e^{L(t - t₀)} dist(A(t₀), M_{≤ r}) + ε (t - t₀) e^{L(t - t₀)}`, with `ε`
the factored normal-component bound. This is an upper bound. For `F ≡ [[0,1],[1,0]]` (`L = 0`,
`r = 1`) and the solution `A(t) = t F` from `0`, `le_distLR_cx` with `δ = 0` certifies the lower
bound `t/3` for the distance to `M_{≤ 1}`; its exact value is not formalised, so the constant is
not proved to be optimal. For `0 < L` and a start of rank at most `r` the smaller expression
`ε (e^{L τ} - 1)/L` is `LeanDLRA.OpenProblems.RankAdaptivity.distLR_flow_le_dini_local`; the form
stated needs no separate case `L = 0`.
This is the recorded form of the statement, with the redundant hypothesis that the field is
continuous in time; `distLR_flow_le_exp_mul_add` is the same statement without it. -/
theorem distLR_flow_le_sharp (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) (hε : MatrixBUG.FactoredNormalBound F r ε)
    (hA : ODESolution F A t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, distLR r (A t) ≤
      Real.exp (L * (t - t₀)) * distLR r (A t₀) + ε * (t - t₀) * Real.exp (L * (t - t₀)) := by
  have _ := hc
  exact distLR_flow_le_exp_mul_add hF hL hB hε0 hε hA

/-- The hypotheses of `distLR_flow_le_exp_mul_add` hold for the constant field
`F ≡ [[0, 1], [1, 0]]` (`L = 0`, `B = ε = ‖F‖`, `r = 1`) and the solution `A t = Y₀ + t F` from
`Y₀ = diag(δ, 0)`. -/
example (δ h : ℝ) : ∀ t ∈ Icc (0 : ℝ) h,
    distLR 1 (cxY₀ δ + (t - 0) • swapMat) ≤
      Real.exp (0 * (t - 0)) * distLR 1 (cxY₀ δ + ((0 : ℝ) - 0) • swapMat) +
        ‖swapMat‖ * (t - 0) * Real.exp (0 * (t - 0)) := by
  have hA : ODESolution (fun _ _ => swapMat) (fun t => cxY₀ δ + (t - 0) • swapMat) 0 h :=
    MatrixBUG.odeSolution_affine (cxY₀ δ) swapMat 0 h
  have hFL : IsLipschitzField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 0 :=
    fun _ _ _ => by simp
  have hFB : IsBoundedField (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) ‖swapMat‖ :=
    fun _ _ => le_rfl
  have hε : MatrixBUG.FactoredNormalBound
      (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) => swapMat) 1 ‖swapMat‖ :=
    MatrixBUG.factoredNormalBound_const swapMat 1
  have key := distLR_flow_le_exp_mul_add hFL le_rfl hFB (norm_nonneg _) hε hA
  exact key

end Distance

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L t₀ t₁ : ℝ} {A : ℝ → E}

end Galerkin

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L B ε : ℝ}

end RankAdaptive

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end QuasiOptimal

end LeanDLRA
