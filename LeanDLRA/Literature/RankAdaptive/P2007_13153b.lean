import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# Results of arXiv 2007.13153: Rank-adaptive symplectic DLR model reduction of Hamiltonian systems

The time-integral a posteriori error bound of Sec. 6.4, eq. (6.7): for a reduced flow
`Ṙ = P(t) X_H(R)` with an arbitrary (not necessarily orthogonal) linear map `P(t)` and an
`L`-Lipschitz Hamiltonian vector field `X_H`, the error to the exact solution is bounded by
`e^{L(t-t₀)} ‖e(t₀)‖ + ∫_{t₀}^t e^{L(t-s)} ‖(I - P(s)) X_H(R(s))‖ ds`, with a variable defect
(the library's `ContinuousDLRA` only has the uniform-defect version).  This is the Grönwall bound of
the paper's derivation; the printed (6.7) has `e^{L t}` and the integral over all of `𝒯_τ`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2007_13153

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **arXiv 2007.13153, Sec. 6.4, eq. (6.7).**  Let `X : E → E` (the Hamiltonian vector field
`X_H`) be `L`-Lipschitz, `x` an exact solution of `ẋ = X(x)` on `[t₀, b]`, and `R` a solution of
the reduced equation `Ṙ = P(t) X(R)` where `P(t)` is an *arbitrary* continuous linear map (no
orthogonality, no symplecticity needed).  If the defect `s ↦ ‖(1 - P(s)) X(R(s))‖` is continuous on
`[t₀, b]`, then for all `t ∈ [t₀, b]`
`‖R t - x t‖ ≤ e^{L(t-t₀)} ‖R t₀ - x t₀‖ + ∫_{t₀}^t e^{L(t-s)} ‖(1 - P(s)) X(R(s))‖ ds`.
Differences from the paper: the abstract inner product space `E` replaces `ℝ^{2N × p}` with the
Frobenius norm; `P(t)` stands for the paper's state-dependent map `P^ε_{R(t)}` along the reduced
trajectory; the symplectic structure is not used (only the Lipschitz property of `X_H`); solutions
are required only to have right derivatives; and the defect is assumed continuous (so that the
integral is a Riemann integral).  The printed (6.7) reads
`‖e(t)‖ ≤ ‖e(t₀)‖ e^{L t} + ∫_{t^{τ-1}}^{t^τ} e^{L(t-s)} ‖(I - P) X_H(R)‖ ds`; the bound here has
the exponent `L (t - t₀)` and the integral up to `t`, which is the Grönwall bound of the paper's
derivation and implies the printed form when `L ≥ 0`, `t₀ = t^{τ-1} ≥ 0` and `t ≤ t^τ`. -/
theorem error_bound_integral {X : E → E} {L : ℝ} (hX : IsLipschitzField (fun _ => X) L)
    {P : ℝ → E →L[ℝ] E} {x R : ℝ → E} {t₀ b : ℝ}
    (hx : ODESolution (fun _ y => X y) x t₀ b)
    (hR : ODESolution (fun t y => P t (X y)) R t₀ b)
    (hdef : ContinuousOn (fun s => ‖(1 - P s) (X (R s))‖) (Icc t₀ b)) :
    ∀ t ∈ Icc t₀ b, ‖R t - x t‖ ≤ Real.exp (L * (t - t₀)) * ‖R t₀ - x t₀‖ +
      ∫ s in t₀..t, Real.exp (L * (t - s)) * ‖(1 - P s) (X (R s))‖ := by
  intro t ht
  have hab : t₀ ≤ b := ht.1.trans ht.2
  have hclamp : ∀ s ∈ Icc t₀ b, max t₀ (min s b) = s := fun s hs => by
    rw [min_eq_left hs.2, max_eq_right hs.1]
  set η : ℝ → ℝ := fun s => ‖(1 - P (max t₀ (min s b))) (X (R (max t₀ (min s b))))‖ with hη
  have hproj : Continuous fun s : ℝ => max t₀ (min s b) := by fun_prop
  have hηc : Continuous η :=
    hdef.comp_continuous hproj fun s => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hηe : ∀ s ∈ Icc t₀ b, η s = ‖(1 - P s) (X (R s))‖ := fun s hs => by
    simp only [hη, hclamp s hs]
  have hmain := norm_le_gronwallIntegralBound (f := fun s => R s - x s)
    (f' := fun s => P s (X (R s)) - X (x s)) (δ := ‖R t₀ - x t₀‖) (K := L) (a := t₀) (b := b)
    (η := η) hηc (hR.cont.sub hx.cont) (fun s hs => (hR.deriv s hs).sub (hx.deriv s hs))
    le_rfl (fun s hs => by
      have h1 := hX s (R s) (x s)
      have h2 : P s (X (R s)) - X (x s) =
          (X (R s) - X (x s)) - (1 - P s) (X (R s)) := by simp
      rw [h2, hηe s ⟨hs.1, hs.2.le⟩]
      exact (norm_sub_le _ _).trans (add_le_add (by simpa using h1) le_rfl))
    t ht
  refine hmain.trans (le_of_eq ?_)
  unfold gronwallIntegralBound
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  rw [← mul_assoc, ← Real.exp_add, hηe s ⟨hs.1, hs.2.trans ht.2⟩]
  congr 2
  ring

/-- Non-vacuity: the hypotheses of `error_bound_integral` hold for the zero field with `P = 1`
and constant solutions. -/
example : ∀ t ∈ Icc (0 : ℝ) 1, ‖(fun _ : ℝ => (0 : ℝ)) t - (fun _ : ℝ => (0 : ℝ)) t‖ ≤
    Real.exp (0 * (t - 0)) * ‖(fun _ : ℝ => (0 : ℝ)) 0 - (fun _ : ℝ => (0 : ℝ)) 0‖ +
      ∫ s in (0 : ℝ)..t, Real.exp (0 * (t - s)) *
        ‖(1 - (1 : ℝ →L[ℝ] ℝ)) ((fun _ : ℝ => (0 : ℝ)) ((fun _ : ℝ => (0 : ℝ)) s))‖ :=
  error_bound_integral (X := fun _ => (0 : ℝ)) (L := 0) (P := fun _ => 1)
    (x := fun _ => 0) (R := fun _ => 0) (t₀ := 0) (b := 1)
    (fun _ _ _ => by simp)
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)⟩
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ)⟩
    (by simpa using continuousOn_const)

end LeanDLRA.Literature.P2007_13153
