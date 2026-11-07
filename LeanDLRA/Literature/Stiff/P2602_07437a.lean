import LeanDLRA.Foundations.Gronwall

/-!
# Results of arXiv 2602.07437: Convergence of a low-rank Strang splitting for stiff matrix ODEs

**Proved here.** The stability part of Proposition 2 of Scalone–Guglielmi (arXiv 2602.07437,
the sentence "S_τ is e^{(L+ω)τ}-Lipschitz" in its proof), for the full-rank Strang map
`S_τ = Φ^A_{τ/2} ∘ Φ^G_τ ∘ Φ^A_{τ/2}` of their equation (5). Theorem
`strang_stability_lipschitz`.

**Abstraction and deviations from the paper.**
* The paper works on `ℂ^{m×m}` with the Frobenius norm and `Φ^A_t(Z) = e^{tA} Z e^{tA*}`.
  Here `E` is an arbitrary real normed space and the linear flow is an abstract family
  `Φ : ℝ → E →L[ℝ] E`. The only property of `Φ^A` used is the bound `‖Φ_t Z‖ ≤ e^{ωt}‖Z‖`
  for `t > 0`, which is Assumption 1(a), inequality (10), read on `Z ↦ e^{tA}Ze^{tA*}`.
  The matrix instance is not proved here.
* The paper's Assumption 1(b) makes `G` Lipschitz only in a neighbourhood of the exact
  solution. Here `G` is assumed globally `L`-Lipschitz, uniformly in time
  (`IsLipschitzField`). This is a stronger hypothesis, so the theorem is weaker than the
  paper's local statement.
* The nonlinear subflow `Φ^G_τ` is not defined through an existence theorem. The theorem
  takes any two exact solutions `w`, `v` of `ẇ = G(t,w)` on `[t₀, t₀+τ]` with initial
  values `Φ_{τ/2} Y` and `Φ_{τ/2} Z`. No existence is assumed.

**Left out (not proved).**
* Lemma 1 (local error `‖S_τ(Y^{n-1}) − S̃_τ(Y^{n-1})‖ ≤ Cτ(τ²+ε)`) and Proposition 2
  (the low-rank error bound `‖E^n_lr‖ ≤ C₁ετ + C₂τ²`). Their proofs cite the midpoint BUG2
  local error bound of Ceruti–Lubich ([5] in the paper) as a black box. That bound is a key
  step of the paper and is not in LeanDLRA, so it cannot be assumed here. The low-rank map
  S̃_τ is not defined in this module. The prefactor `τ` in `C₁ετ` is not checked: the paper's
  own Gronwall sum over `n ≤ T/τ` steps of a local error `Cτε` appears to give `Cε`, not
  `Cετ`. This is only a remark, not a verified counterexample.
* Theorem 1 (global error `‖X(t₀+nτ) − S̃ⁿ_τ(Y⁰)‖ ≤ c₀τ²(1+|log τ|) + c₁δ + c₂τε`). It depends
  on Lemma 1, Proposition 2, and Proposition 1 below.
* Proposition 1 (full-rank Strang convergence `‖X(t₀+nτ) − Sⁿ_τ(X⁰)‖ ≤ Cτ²(1+|log τ|)`).
  Its proof uses the Peano kernel expansion, the parabolic smoothing bound (11), and a
  weakly singular discrete Grönwall inequality. The paper's own proof states several `O(τ³)`
  terms without detail, so the argument is not carried out here.

**Core definitions used.** `IsLipschitzField` and `ODESolution` from
`LeanDLRA.Foundations.ODE`, and the flow-stability lemma `ODESolution.norm_sub_le_exp` from
`LeanDLRA.Foundations.Gronwall`. No new structures or substep definitions are introduced.
-/

namespace LeanDLRA.Literature.P2602_07437

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Stability of the full-rank Strang map** (arXiv 2602.07437, Proposition 2, stability
part: the claim that `S_τ` is `e^{(L+ω)τ}`-Lipschitz).

Setting: `S_τ(Y) = Φ_{τ/2} (W(t₀+τ))`, where `W` solves `ẇ = G(t,w)` on `[t₀, t₀+τ]` with
`W(t₀) = Φ_{τ/2} Y`. The linear flow satisfies `‖Φ_t Z‖ ≤ e^{ωt}‖Z‖` for `t > 0`
(paper's Assumption 1(a), eq. (10)). `G` is `L`-Lipschitz, globally in this version; the
paper assumes it locally (Assumption 1(b)). Conclusion:
`‖S_τ(Y) − S_τ(Z)‖ ≤ e^{(L+ω)τ}‖Y − Z‖`. -/
theorem strang_stability_lipschitz
    {G : ℝ → E → E} {L ω t₀ τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hΦ : ∀ t, 0 < t → ∀ Z : E, ‖Φ t Z‖ ≤ Real.exp (ω * t) * ‖Z‖)
    {Y Z : E} {w v : ℝ → E}
    (hw : ODESolution G w t₀ (t₀ + τ)) (hv : ODESolution G v t₀ (t₀ + τ))
    (hwY : w t₀ = Φ (τ / 2) Y) (hvZ : v t₀ = Φ (τ / 2) Z) :
    ‖Φ (τ / 2) (w (t₀ + τ)) - Φ (τ / 2) (v (t₀ + τ))‖ ≤
      Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
  have h2 : 0 < τ / 2 := by linarith
  -- stability of the nonlinear subflow on [t₀, t₀ + τ]
  have h1 : ‖w (t₀ + τ) - v (t₀ + τ)‖ ≤ Real.exp (L * τ) * ‖w t₀ - v t₀‖ := by
    have h := hw.norm_sub_le_exp hG hL hv (t₀ + τ) ⟨by linarith, le_rfl⟩
    have e : t₀ + τ - t₀ = τ := by ring
    rwa [e] at h
  -- the initial gap is a linear image of `Y - Z`
  have hd : ‖w t₀ - v t₀‖ ≤ Real.exp (ω * (τ / 2)) * ‖Y - Z‖ := by
    rw [hwY, hvZ, ← map_sub]
    exact hΦ _ h2 _
  -- outer linear half step
  calc ‖Φ (τ / 2) (w (t₀ + τ)) - Φ (τ / 2) (v (t₀ + τ))‖
      = ‖Φ (τ / 2) (w (t₀ + τ) - v (t₀ + τ))‖ := by rw [map_sub]
    _ ≤ Real.exp (ω * (τ / 2)) * ‖w (t₀ + τ) - v (t₀ + τ)‖ := hΦ _ h2 _
    _ ≤ Real.exp (ω * (τ / 2)) * (Real.exp (L * τ) * ‖w t₀ - v t₀‖) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (ω * (τ / 2)) * (Real.exp (L * τ) *
          (Real.exp (ω * (τ / 2)) * ‖Y - Z‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
        rw [show (L + ω) * τ = ω * (τ / 2) + L * τ + ω * (τ / 2) by ring,
          Real.exp_add, Real.exp_add]
        ring

/-- Non-vacuity: the hypotheses of `strang_stability_lipschitz` hold for `G = 0`, `Φ = id`
(so `ω = 0`, `L = 0`) and constant solutions. -/
example (y₀ : E) (t₀ τ : ℝ) (hτ : 0 < τ) :
    ‖ContinuousLinearMap.id ℝ E ((fun _ : ℝ => y₀) (t₀ + τ)) -
        ContinuousLinearMap.id ℝ E ((fun _ : ℝ => y₀) (t₀ + τ))‖ ≤
      Real.exp ((0 + 0) * τ) * ‖y₀ - y₀‖ :=
  strang_stability_lipschitz (G := fun _ _ => (0 : E)) (L := 0) (ω := 0)
    (Φ := fun _ => ContinuousLinearMap.id ℝ E) (t₀ := t₀)
    (fun t x y => by simp) le_rfl hτ (fun t _ Z => by simp)
    (w := fun _ => y₀) (v := fun _ => y₀) (Y := y₀) (Z := y₀)
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const _ _ _⟩
    (by simp) (by simp)

end LeanDLRA.Literature.P2602_07437
