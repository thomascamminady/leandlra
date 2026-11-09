import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.Localization
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2602.07437: Convergence of a low-rank Strang splitting for stiff matrix ODEs

Scalone–Guglielmi split `Ẋ = AX + XA* + G(t, X)` into the linear flow
`Φ^A_t(Z) = e^{tA} Z e^{tA*}` and the nonlinear flow `Φ^G_τ`, and study the full-rank Strang map
`S_τ = Φ^A_{τ/2} ∘ Φ^G_τ ∘ Φ^A_{τ/2}` (their (5)) and its low-rank version
`S̃_τ = Φ^A_{τ/2} ∘ Φ̃^G_τ ∘ Φ^A_{τ/2}` with the midpoint BUG integrator `Φ̃^G_τ` (their (6)).

## Main definitions

* `IsStrangStep G Φ t τ Y Y' w`: `Y' = S_τ(Y)`, computed along the trajectory `w` of
  `ẇ = G(s, w)` on `[t, t + τ]` started at `Φ_{τ/2} Y` (a core `ODESolution`). With `Φ = id` it
  is a step of the exact flow (`isStrangStep_id_iff`).

## Main results

* `strang_stability_localLipschitz` (faithful form of the stability claim in the proof of
  Proposition 2): with `G` Lipschitz only on the tube `‖X₁ - X(t)‖ ≤ γ` of Assumption 1(b)
  (core `IsLipschitzOnTube`) and both nonlinear trajectories in that tube,
  `‖S_τ(Ŷ) - S_τ(Ỹ)‖ ≤ e^{(L+ω)τ}‖Ŷ - Ỹ‖`. Step form `IsStrangStep.norm_sub_le`.
  `strang_stability_lipschitz` (the first version of this module) is the special case of a
  globally Lipschitz `G`.
* `strang_iterates_norm_sub_le`, `strang_initial_error_le`: the bound
  `‖Sⁿ_τ(X⁰) - Sⁿ_τ(Y⁰)‖ ≤ e^{(L+ω)(T-t₀)}‖X⁰ - Y⁰‖` of the proof of Theorem 1 (`E_δ`).
* `strang_local_error_le`: Lemma 1, conditional on the BUG2 local error bound of [5].
* `strang_lowRank_error_le`: Proposition 2 in corrected form `‖Eⁿ_lr‖ ≤ C₁ε + C₂τ²`,
  conditional on Lemma 1.
* `strang_global_error_le`: Theorem 1 in corrected form
  `‖X(t₀+nτ) - S̃ⁿ_τ(Y⁰)‖ ≤ c₀τ²(1+|log τ|) + c₁δ + c₂ε`, conditional on Proposition 1 and
  Lemma 1.
* Counterexamples to the printed statements: `strang_stability_half_exponent_fails` (the printed
  exponent `(L+ω)τ/2`), `lowRank_error_le_eps_mul_tau_fails` (Proposition 2 with `C₁ετ`) and
  `global_error_le_tau_mul_eps_fails` (Theorem 1 with `c₂τε`).
* Helpers: `odeSolution_const_field`, `IsStrangStep.eq_of_const`, `strang_iterates_const`,
  `isStrangStep_const_iterates` (closed form of `S_τ` for a constant `G`),
  `one_le_norm_one_sub_of_rank_lt` (a rank-deficient complex matrix is at Frobenius distance
  `≥ 1` from `I`), `diag_mul_diag_eq_zero_and_norm_eq_one` (Assumption 1(c) for the
  counterexample data).

## Setting and deviations from the paper

* The paper works on `ℂ^{m×m}` with the Frobenius norm and `Φ^A_t(Z) = e^{tA}Ze^{tA*}`. Here `E`
  is any real normed space and the linear flow is an abstract family `Φ : ℝ → E →L[ℝ] E`; the
  only property used is `‖Φ_t Z‖ ≤ e^{ωt}‖Z‖` for `t > 0`, which is Assumption 1(a), (10). The
  counterexamples are stated on `ℂ^{2×2}` with the Frobenius norm and `A = 0`.
* Assumption 1(b), (12), is the core predicate `IsLipschitzOnTube G X t₀ T γ L`, with `X` any
  curve (the exact solution in the paper). It only gives Lipschitz bounds inside the tube, so
  every stability statement assumes that the nonlinear trajectories it uses stay in the tube.
  The paper asserts this (Section 2.2, p. 9: all approximations stay in a neighbourhood `U` for
  `τ ≤ τ₀`, "this follows recursively from the given proofs") but does not prove it. The
  results that use it are conditional on it, and their docstrings say so.
* The nonlinear flow `Φ^G_τ` is not defined through an existence theorem: the results take the
  trajectories as data (`IsStrangStep`). The low-rank map `S̃_τ` is not defined either: its
  iterates are an arbitrary sequence, linked to `S_τ` only through the local error bound of
  Lemma 1, which is a hypothesis (the midpoint BUG local error bound of [5] is not in LeanDLRA).
* The bounds with `T - t₀` in the exponent need `L + ω ≥ 0` (for `n = 0` and `L + ω < 0` the
  printed `E_δ` bound fails). This costs nothing: (10) stays true when `ω` is increased.

## Errors in the printed statements (checked in the PDF, p. 9 and p. 14)

* Proof of Proposition 2: the printed stability bound `e^{(L+ω)τ/2}` is a typo; the next line
  of the proof uses `e^{(L+ω)τ}`, which is what holds (`strang_stability_half_exponent_fails`).
* Proposition 2 (`‖Eⁿ_lr‖ ≤ C₁ετ + C₂τ²`) and Theorem 1 (`… + c₂τε`) are false as printed: the
  factor `τ` at `ε` must go. With `A = 0`, `G ≡ diag(0,1)`, `Y⁰ = X⁰ = diag(1,0)` and rank
  `r = 1`, every rank-1 matrix is at Frobenius distance `≥ 1` from `X(1) = Sⁿ_τ(Y⁰) = I`, while
  the printed right-hand sides tend to `0` as `τ → 0`. The paper's own proof (Lemma 1 plus a
  discrete Grönwall over `n ≤ T/τ` steps) gives `C₁ε + C₂τ²`, which is proved here; the
  Lie–Trotter analysis it builds on (arXiv 1803.10473, Theorem 1) also has `c₂ε`.
* Lemma 1 (p. 14): the argument of `S̃_τ` is missing on the left, and the proof applies the BUG2
  error at `Yⁿ⁻¹` instead of `Φ^A_{τ/2}(Yⁿ⁻¹)`; both are typos.
* Proof of Proposition 2: `Ŷ, Ỹ ∈ M` is assumed, but the bound is applied at the full-rank
  iterate `Sⁿ⁻¹_τ(Y⁰)`; the rank assumption is not needed (the results here do not use it).

## Not formalized

* Proposition 1 (full-rank Strang convergence `Cτ²(1+|log τ|)`): needs the variation-of-constants
  formula for `e^{tA}`, the Peano kernel of the midpoint rule, parabolic smoothing (11) and a
  weakly singular discrete Grönwall inequality; the paper leaves several `O(τ³)` terms implicit.
  It enters `strang_global_error_le` as a hypothesis.
* The BUG2 local error bound of [5] (Ceruti–Einkemmer–Kusch–Lubich), behind Lemma 1.
* The claim that all approximations stay in the tube (see above).

## Core definitions used

`ODESolution`, `IsLipschitzField`, `IsLipschitzOnTube` (Assumption 1(b)) with its bridge
`IsLipschitzField.isLipschitzOnTube`, the stability lemma `ODESolution.norm_sub_le_exp`,
uniqueness `ODESolution.eqOn`, the discrete Grönwall inequalities `discrete_gronwall_le`,
`discrete_gronwall_exp_le`, and the Frobenius norm of `LeanDLRA.Frobenius`. The local Grönwall
step uses Mathlib's `dist_le_of_trajectories_ODE_of_mem`. The only new definition is
`IsStrangStep` (one step of (5); there is no splitting step in the core), with the bridge
`isStrangStep_id_iff` to the exact-flow steps of `lady_windermere`.
-/

open Set

namespace LeanDLRA.Literature.P2602_07437

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The composition step behind the stability of `S_τ`: if the nonlinear flow over `[t, t+τ]`
is `e^{Lτ}`-Lipschitz on the two trajectories and `‖Φ_s Z‖ ≤ e^{ωs}‖Z‖` (paper's (10)), the two
outer half steps add `e^{ωτ/2}` each. -/
private theorem strang_stability_of_flow
    {L ω t τ : ℝ} {Φ : ℝ → E →L[ℝ] E} (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {Y Z : E} {w v : ℝ → E}
    (h1 : ‖w (t + τ) - v (t + τ)‖ ≤ Real.exp (L * τ) * ‖w t - v t‖)
    (hwY : w t = Φ (τ / 2) Y) (hvZ : v t = Φ (τ / 2) Z) :
    ‖Φ (τ / 2) (w (t + τ)) - Φ (τ / 2) (v (t + τ))‖ ≤
      Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
  have h2 : 0 < τ / 2 := by linarith
  have hd : ‖w t - v t‖ ≤ Real.exp (ω * (τ / 2)) * ‖Y - Z‖ := by
    rw [hwY, hvZ, ← map_sub]
    exact hΦ _ h2 _
  calc ‖Φ (τ / 2) (w (t + τ)) - Φ (τ / 2) (v (t + τ))‖
      = ‖Φ (τ / 2) (w (t + τ) - v (t + τ))‖ := by rw [map_sub]
    _ ≤ Real.exp (ω * (τ / 2)) * ‖w (t + τ) - v (t + τ)‖ := hΦ _ h2 _
    _ ≤ Real.exp (ω * (τ / 2)) * (Real.exp (L * τ) * ‖w t - v t‖) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ ≤ Real.exp (ω * (τ / 2)) * (Real.exp (L * τ) *
          (Real.exp (ω * (τ / 2)) * ‖Y - Z‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
        rw [show (L + ω) * τ = ω * (τ / 2) + L * τ + ω * (τ / 2) by ring,
          Real.exp_add, Real.exp_add]
        ring

/-- **Stability of the full-rank Strang map, globally Lipschitz special case**
(arXiv 2602.07437, proof of Proposition 2, stability claim).

Setting: `S_τ(Y) = Φ_{τ/2} (W(t₀+τ))`, where `W` solves `ẇ = G(t,w)` on `[t₀, t₀+τ]` with
`W(t₀) = Φ_{τ/2} Y`. The linear flow satisfies `‖Φ_t Z‖ ≤ e^{ωt}‖Z‖` for `t > 0`
(paper's Assumption 1(a), eq. (10)). Conclusion: `‖S_τ(Y) − S_τ(Z)‖ ≤ e^{(L+ω)τ}‖Y − Z‖`.

Deviations: `G` is `L`-Lipschitz on all of `E` (`IsLipschitzField`), while the paper's
Assumption 1(b) gives Lipschitz bounds only on a tube around the exact solution; the faithful
version is `strang_stability_localLipschitz`. The paper prints the exponent `(L+ω)τ/2`, a typo:
the next line of its proof uses `e^{(L+ω)τ}`, and the `τ/2` version fails
(`strang_stability_half_exponent_fails`). The nonlinear trajectories are data; no existence
theorem is used. -/
theorem strang_stability_lipschitz
    {G : ℝ → E → E} {L ω t₀ τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzField G L) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hΦ : ∀ t, 0 < t → ∀ Z : E, ‖Φ t Z‖ ≤ Real.exp (ω * t) * ‖Z‖)
    {Y Z : E} {w v : ℝ → E}
    (hw : ODESolution G w t₀ (t₀ + τ)) (hv : ODESolution G v t₀ (t₀ + τ))
    (hwY : w t₀ = Φ (τ / 2) Y) (hvZ : v t₀ = Φ (τ / 2) Z) :
    ‖Φ (τ / 2) (w (t₀ + τ)) - Φ (τ / 2) (v (t₀ + τ))‖ ≤
      Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
  have h1 : ‖w (t₀ + τ) - v (t₀ + τ)‖ ≤ Real.exp (L * τ) * ‖w t₀ - v t₀‖ := by
    have h := hw.norm_sub_le_exp hG hL hv (t₀ + τ) ⟨by linarith, le_rfl⟩
    rwa [show t₀ + τ - t₀ = τ by ring] at h
  exact strang_stability_of_flow hτ hΦ h1 hwY hvZ

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

/-- **One step of the full-rank Strang splitting** (arXiv 2602.07437, eq. (5)):
`Y' = S_τ(Y) = Φ_{τ/2}(w(t+τ))`, where `w` solves the nonlinear subproblem (3), `ẇ = G(s, w)`, on
`[t, t+τ]` (core `ODESolution`) with `w(t) = Φ_{τ/2}(Y)`. The linear flow `Φ` is abstract (in the
paper `Φ_s Z = e^{sA} Z e^{sA*}`). The trajectory `w` is part of the data, so tube conditions on
it can be stated; for a field that is Lipschitz near `w` it is unique (`ODESolution.eqOn`). -/
structure IsStrangStep (G : ℝ → E → E) (Φ : ℝ → E →L[ℝ] E) (t τ : ℝ) (Y Y' : E)
    (w : ℝ → E) : Prop where
  sol : ODESolution G w t (t + τ)
  init : w t = Φ (τ / 2) Y
  out : Y' = Φ (τ / 2) (w (t + τ))

/-- Bridging lemma: with trivial linear part (`A = 0`, so `Φ = id`) a Strang step is a step of
the exact flow of `ẏ = G(t, y)` in the core sense (`ODESolution` started at `Y`, as in
`lady_windermere`). -/
theorem isStrangStep_id_iff {G : ℝ → E → E} {t τ : ℝ} {Y Y' : E} {w : ℝ → E} :
    IsStrangStep G (fun _ => ContinuousLinearMap.id ℝ E) t τ Y Y' w ↔
      ODESolution G w t (t + τ) ∧ w t = Y ∧ Y' = w (t + τ) :=
  ⟨fun h => ⟨h.sol, h.init, h.out⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- For a constant field `G ≡ Q` the affine curve `s ↦ Y + (s - t)Q` solves `ẏ = Q` on every
interval (core `ODESolution`). -/
theorem odeSolution_const_field (Q Y : E) (t a b : ℝ) :
    ODESolution (fun _ _ => Q) (fun s => Y + (s - t) • Q) a b := by
  refine ⟨(continuous_const.add ((continuous_id.sub continuous_const).smul
    continuous_const)).continuousOn, fun s _ => ?_⟩
  have := (((hasDerivAt_id s).sub_const t).smul_const Q).const_add Y
  simpa using this.hasDerivWithinAt

/-- **Closed form for a constant nonlinearity**: if `G ≡ Q`, the nonlinear flow is
`Z ↦ Z + τQ`, so `S_τ(Y) = Φ_{τ/2}(Φ_{τ/2} Y + τQ)` (uniqueness from `ODESolution.eqOn`). -/
theorem IsStrangStep.eq_of_const {Q : E} {Φ : ℝ → E →L[ℝ] E} {t τ : ℝ} (hτ : 0 ≤ τ)
    {Y Y' : E} {w : ℝ → E} (h : IsStrangStep (fun _ _ => Q) Φ t τ Y Y' w) :
    Y' = Φ (τ / 2) (Φ (τ / 2) Y + τ • Q) := by
  have hu := odeSolution_const_field Q (Φ (τ / 2) Y) t t (t + τ)
  have hL : IsLipschitzField (fun (_ : ℝ) (_ : E) => Q) 0 := fun _ _ _ => by simp
  have heq := h.sol.eqOn hu hL le_rfl (by simp [h.init])
  have hend := heq (show t + τ ∈ Icc t (t + τ) from ⟨by linarith, le_rfl⟩)
  rw [h.out, hend]
  simp

/-- Iterating `IsStrangStep.eq_of_const` with `Φ = id` (no stiff part): the Strang iterates for
`G ≡ Q` are `xₙ = x₀ + (nτ)Q`, the exact solution. -/
theorem strang_iterates_const {Q : E} {t₀ τ : ℝ} (hτ : 0 ≤ τ) {N : ℕ} {x : ℕ → E}
    {w : ℕ → ℝ → E}
    (hx : ∀ n < N, IsStrangStep (fun _ _ => Q) (fun _ => ContinuousLinearMap.id ℝ E)
      (t₀ + n * τ) τ (x n) (x (n + 1)) (w n)) :
    ∀ n ≤ N, x n = x 0 + ((n : ℝ) * τ) • Q := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [(hx n (by omega)).eq_of_const hτ, ih (by omega)]
    simp only [ContinuousLinearMap.id_apply]
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- Existence for `strang_iterates_const`: with `Φ = id` and `G ≡ Q`, the points
`xₙ = x₀ + (nτ)Q` with the affine trajectories `s ↦ xₙ + (s - tₙ)Q` are Strang steps. -/
theorem isStrangStep_const_iterates (Q x₀ : E) (t₀ τ : ℝ) (n : ℕ) :
    IsStrangStep (fun _ _ => Q) (fun _ => ContinuousLinearMap.id ℝ E) (t₀ + n * τ) τ
      (x₀ + ((n : ℝ) * τ) • Q) (x₀ + (((n + 1 : ℕ) : ℝ) * τ) • Q)
      (fun s => x₀ + ((n : ℝ) * τ) • Q + (s - (t₀ + n * τ)) • Q) where
  sol := odeSolution_const_field _ _ _ _ _
  init := by simp
  out := by
    simp only [ContinuousLinearMap.id_apply]
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- **Lemma 1 of arXiv 2602.07437, conditional on the BUG2 local error bound.**
If `Y' = S_τ(Y)` (`IsStrangStep`) and `Ylr' = Φ_{τ/2}(ψ)` (that is `S̃_τ(Y)`), where
`ψ = Φ̃^G_τ(Φ_{τ/2} Y)` is the output of the nonlinear low-rank integrator, and that integrator
has local error `‖Φ^G_τ(Φ_{τ/2}Y) - ψ‖ ≤ Cτ(τ² + ε)` (hypothesis `hbug`), then
`‖S_τ(Y) - S̃_τ(Y)‖ ≤ e^{ωτ/2} Cτ(τ² + ε)`.

Conditional: `hbug` is the local error bound of the midpoint BUG integrator of [5]
(Ceruti–Einkemmer–Kusch–Lubich), which the paper cites and which is not in LeanDLRA; the proof
here is the paper's reduction to it through (10). The paper writes the BUG2 error at `Y` instead
of at `Φ_{τ/2}(Y)`, and omits the argument of `S̃_τ`; both are typos. -/
theorem strang_local_error_le {G : ℝ → E → E} {Φ : ℝ → E →L[ℝ] E} {ω t τ C ε : ℝ}
    (hτ : 0 < τ) (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {Y Y' Ylr' ψ : E} {w : ℝ → E} (h : IsStrangStep G Φ t τ Y Y' w)
    (hlr : Ylr' = Φ (τ / 2) ψ) (hbug : ‖w (t + τ) - ψ‖ ≤ C * τ * (τ ^ 2 + ε)) :
    ‖Y' - Ylr'‖ ≤ Real.exp (ω * τ / 2) * (C * τ * (τ ^ 2 + ε)) := by
  rw [h.out, hlr, ← map_sub]
  calc ‖Φ (τ / 2) (w (t + τ) - ψ)‖ ≤ Real.exp (ω * (τ / 2)) * ‖w (t + τ) - ψ‖ :=
        hΦ _ (by linarith) _
    _ ≤ Real.exp (ω * τ / 2) * (C * τ * (τ ^ 2 + ε)) := by
        rw [show ω * (τ / 2) = ω * τ / 2 by ring]
        exact mul_le_mul_of_nonneg_left hbug (Real.exp_pos _).le

/-! ### Stability under the local Lipschitz condition of Assumption 1(b) -/

/-- **Stability of the full-rank Strang map** (arXiv 2602.07437, the stability bound in the proof
of Proposition 2), with the paper's local Lipschitz condition.

Hypotheses: Assumption 1(b), (12): `‖G(s, X₁) - G(s, X₂)‖ ≤ L‖X₁ - X₂‖` whenever `s ∈ [a, b]`
and `‖X₁ - X(s)‖, ‖X₂ - X(s)‖ ≤ γ` (`IsLipschitzOnTube`, `X` the exact solution in the paper);
Assumption 1(a), (10), for the linear flow. `S_τ(Y) = Φ_{τ/2}(w(t+τ))`, `S_τ(Z) = Φ_{τ/2}(v(t+τ))`
with `w`, `v` solving `ẇ = G(s, w)` on `[t, t+τ] ⊆ [a, b]`, `w(t) = Φ_{τ/2} Y`,
`v(t) = Φ_{τ/2} Z`. Conclusion: `‖S_τ(Y) - S_τ(Z)‖ ≤ e^{(L+ω)τ}‖Y - Z‖`.

Conditional on the tube property: `w` and `v` stay in the tube on `[t, t+τ)` (`hwX`, `hvX`).
The paper uses (12) at these trajectories without checking this; it claims in Section 2.2 that
all approximations stay in a neighbourhood of the exact solution for small `τ`.
Deviations: the printed exponent is `(L+ω)τ/2`, a typo (the proof's next line uses
`e^{(L+ω)τ}`, and `strang_stability_half_exponent_fails` refutes `τ/2`); the paper takes
`Ŷ, Ỹ` of rank `r`, which is not needed. -/
theorem strang_stability_localLipschitz
    {G : ℝ → E → E} {X : ℝ → E} {a b γ L ω t τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X a b γ L) (hL : 0 ≤ L) (hτ : 0 < τ) (ha : a ≤ t)
    (hb : t + τ ≤ b) (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {Y Z : E} {w v : ℝ → E}
    (hw : ODESolution G w t (t + τ)) (hv : ODESolution G v t (t + τ))
    (hwY : w t = Φ (τ / 2) Y) (hvZ : v t = Φ (τ / 2) Z)
    (hwX : ∀ s ∈ Ico t (t + τ), ‖w s - X s‖ ≤ γ) (hvX : ∀ s ∈ Ico t (t + τ), ‖v s - X s‖ ≤ γ) :
    ‖Φ (τ / 2) (w (t + τ)) - Φ (τ / 2) (v (t + τ))‖ ≤
      Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
  have hlip : ∀ s ∈ Ico t (t + τ),
      LipschitzOnWith ⟨L, hL⟩ (G s) (Metric.closedBall (X s) γ) := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hx hy
    rw [dist_eq_norm, dist_eq_norm]
    exact hG s ⟨ha.trans hs.1, hs.2.le.trans hb⟩ x y hx hy
  have hd := dist_le_of_trajectories_ODE_of_mem (s := fun s => Metric.closedBall (X s) γ)
    hlip hw.cont hw.deriv
    (fun s hs => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hwX s hs)
    hv.cont hv.deriv (fun s hs => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hvX s hs)
    le_rfl (t + τ) ⟨by linarith, le_rfl⟩
  have h1 : ‖w (t + τ) - v (t + τ)‖ ≤ Real.exp (L * τ) * ‖w t - v t‖ := by
    have e : t + τ - t = τ := by ring
    simp only [dist_eq_norm, e] at hd
    exact hd.trans_eq (mul_comm _ _)
  exact strang_stability_of_flow hτ hΦ h1 hwY hvZ

/-- Step form of `strang_stability_localLipschitz`: two Strang steps whose nonlinear
trajectories stay in the tube of Assumption 1(b) satisfy `‖Y' - Z'‖ ≤ e^{(L+ω)τ}‖Y - Z‖`
(arXiv 2602.07437, proof of Proposition 2). Conditional on the tube property (`hwX`, `hvX`). -/
theorem IsStrangStep.norm_sub_le
    {G : ℝ → E → E} {X : ℝ → E} {a b γ L ω t τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X a b γ L) (hL : 0 ≤ L) (hτ : 0 < τ) (ha : a ≤ t)
    (hb : t + τ ≤ b) (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {Y Y' Z Z' : E} {w v : ℝ → E}
    (h₁ : IsStrangStep G Φ t τ Y Y' w) (h₂ : IsStrangStep G Φ t τ Z Z' v)
    (hwX : ∀ s ∈ Ico t (t + τ), ‖w s - X s‖ ≤ γ) (hvX : ∀ s ∈ Ico t (t + τ), ‖v s - X s‖ ≤ γ) :
    ‖Y' - Z'‖ ≤ Real.exp ((L + ω) * τ) * ‖Y - Z‖ := by
  rw [h₁.out, h₂.out]
  exact strang_stability_localLipschitz hG hL hτ ha hb hΦ h₁.sol h₂.sol h₁.init h₂.init hwX hvX

/-- Non-vacuity of the local stability theorem: `G = 0`, `X = 0`, `Φ = id`, constant
trajectories in the unit tube. -/
example (y₀ : E) (hy₀ : ‖y₀‖ ≤ 1) :
    ‖ContinuousLinearMap.id ℝ E y₀ - ContinuousLinearMap.id ℝ E y₀‖ ≤
      Real.exp ((0 + 0) * 1) * ‖y₀ - y₀‖ :=
  strang_stability_localLipschitz (G := fun _ _ => (0 : E)) (X := fun _ => 0) (a := 0) (b := 1)
    (γ := 1) (L := 0) (ω := 0) (t := 0) (τ := 1) (Φ := fun _ => ContinuousLinearMap.id ℝ E)
    (fun _ _ _ _ _ _ => by simp) le_rfl one_pos le_rfl (by norm_num) (fun _ _ _ => by simp)
    (w := fun _ => y₀) (v := fun _ => y₀)
    ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩
    ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩ (by simp) (by simp)
    (fun _ _ => by simpa using hy₀) (fun _ _ => by simpa using hy₀)

/-- One step of the error recursion shared by the multi-step bounds: if `x (n+1) = S_τ(x n)`,
`z n = S_τ(y n)` with nonlinear trajectories in the tube, then
`‖x(n+1) - y(n+1)‖ ≤ e^{(L+ω)τ}‖x n - y n‖ + ‖z n - y(n+1)‖`. -/
private theorem strang_error_step
    {G : ℝ → E → E} {X : ℝ → E} {t₀ T γ L ω τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X t₀ T γ L) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {N : ℕ} (hN : t₀ + N * τ ≤ T) {x y z : ℕ → E} {w v : ℕ → ℝ → E}
    (hx : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (x n) (x (n + 1)) (w n))
    (hz : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (y n) (z n) (v n))
    (hwX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖w n s - X s‖ ≤ γ)
    (hvX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖v n s - X s‖ ≤ γ)
    {n : ℕ} (hn : n < N) :
    ‖x (n + 1) - y (n + 1)‖ ≤
      Real.exp ((L + ω) * τ) * ‖x n - y n‖ + ‖z n - y (n + 1)‖ := by
  have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have hnτ : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
  have hb : t₀ + n * τ + τ ≤ T := by
    have := mul_le_mul_of_nonneg_right hn' hτ.le
    linarith
  have hstab := (hx n hn).norm_sub_le hG hL hτ (by linarith) hb hΦ (hz n hn) (hwX n hn)
    (hvX n hn)
  calc ‖x (n + 1) - y (n + 1)‖ ≤ ‖x (n + 1) - z n‖ + ‖z n - y (n + 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp ((L + ω) * τ) * ‖x n - y n‖ + ‖z n - y (n + 1)‖ := by gcongr

/-- **Propagation of a perturbation by the Strang iterates** (arXiv 2602.07437, proof of
Theorem 1, bound on `E_δ`), exponential form: if `x`, `y` are Strang iterates on the grid
`tₙ = t₀ + nτ ≤ T` whose nonlinear trajectories stay in the tube of Assumption 1(b), then
`‖xₙ - yₙ‖ ≤ e^{(L+ω)nτ}‖x₀ - y₀‖`. Conditional on the tube property (`hwX`, `hvX`). -/
theorem strang_iterates_norm_sub_le
    {G : ℝ → E → E} {X : ℝ → E} {t₀ T γ L ω τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X t₀ T γ L) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {N : ℕ} (hN : t₀ + N * τ ≤ T) {x y : ℕ → E} {w v : ℕ → ℝ → E}
    (hx : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (x n) (x (n + 1)) (w n))
    (hy : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (y n) (y (n + 1)) (v n))
    (hwX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖w n s - X s‖ ≤ γ)
    (hvX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖v n s - X s‖ ≤ γ) :
    ∀ n ≤ N, ‖x n - y n‖ ≤ Real.exp ((L + ω) * (n * τ)) * ‖x 0 - y 0‖ := by
  have key := discrete_gronwall_le (e := fun n => ‖x n - y n‖) (b := fun _ => 0)
    (Real.exp_pos ((L + ω) * τ)).le fun n hn => by
      simpa using strang_error_step hG hL hτ hΦ hN hx hy hwX hvX hn
  intro n hn
  have h := key n hn
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [← Real.exp_nat_mul] at h
  calc ‖x n - y n‖ ≤ Real.exp (n * ((L + ω) * τ)) * ‖x 0 - y 0‖ := h
    _ = Real.exp ((L + ω) * (n * τ)) * ‖x 0 - y 0‖ := by
        rw [show (n : ℝ) * ((L + ω) * τ) = (L + ω) * (n * τ) by ring]

/-- **Propagation of the initial error, `E_δ`** (arXiv 2602.07437, proof of Theorem 1):
`‖Sⁿ_τ(X⁰) - Sⁿ_τ(Y⁰)‖ ≤ e^{(L+ω)(T-t₀)}‖X⁰ - Y⁰‖` for `t₀ + nτ ≤ T`.
Conditional on the tube property (`hwX`, `hvX`). Deviation: needs `L + ω ≥ 0`, which the paper
leaves implicit (for `n = 0`, `T > t₀` and `L + ω < 0` the printed bound fails; since (10)
persists when `ω` grows, this is no restriction). -/
theorem strang_initial_error_le
    {G : ℝ → E → E} {X : ℝ → E} {t₀ T γ L ω τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X t₀ T γ L) (hL : 0 ≤ L) (hLω : 0 ≤ L + ω) (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {N : ℕ} (hN : t₀ + N * τ ≤ T) {x y : ℕ → E} {w v : ℕ → ℝ → E}
    (hx : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (x n) (x (n + 1)) (w n))
    (hy : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (y n) (y (n + 1)) (v n))
    (hwX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖w n s - X s‖ ≤ γ)
    (hvX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖v n s - X s‖ ≤ γ) :
    ∀ n ≤ N, ‖x n - y n‖ ≤ Real.exp ((L + ω) * (T - t₀)) * ‖x 0 - y 0‖ := by
  intro n hn
  have hnN : (n : ℝ) * τ ≤ N * τ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ.le
  refine (strang_iterates_norm_sub_le hG hL hτ hΦ hN hx hy hwX hvX n hn).trans ?_
  gcongr
  linarith

/-- **Proposition 2 of arXiv 2602.07437, corrected, conditional on Lemma 1.**
Let `xₙ = Sⁿ_τ(Y⁰)` (full-rank Strang iterates) and `yₙ = S̃ⁿ_τ(Y⁰)` (any sequence, the low-rank
iterates), with `y₀ = x₀`, and let `zₙ = S_τ(yₙ)`. If the local errors satisfy Lemma 1,
`‖S_τ(yₙ) - y_{n+1}‖ ≤ Cτ(τ² + ε)` (hypothesis `hloc`), then for `t₀ + nτ ≤ T`
`‖Eⁿ_lr‖ = ‖xₙ - yₙ‖ ≤ C₁ε + C₂τ²` with `C₁ = C₂ = (T - t₀)e^{(L+ω)(T-t₀)}C`.

Conditional on Lemma 1 (`hloc`, see `strang_local_error_le`, itself conditional on the BUG2 local
error bound) and on the tube property for the trajectories of `S_τ(xₙ)` and `S_τ(yₙ)` (`hwX`,
`hvX`). Deviation: the paper states `C₁ετ + C₂τ²`, which is false
(`lowRank_error_le_eps_mul_tau_fails`); its own proof (this one: stability plus discrete Grönwall
over `n ≤ (T - t₀)/τ` steps) gives `C₁ε + C₂τ²`. Also needs `L + ω ≥ 0` (no loss, see
`strang_initial_error_le`). -/
theorem strang_lowRank_error_le
    {G : ℝ → E → E} {X : ℝ → E} {t₀ T γ L ω τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X t₀ T γ L) (hL : 0 ≤ L) (hLω : 0 ≤ L + ω) (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {N : ℕ} (hN : t₀ + N * τ ≤ T) {x y z : ℕ → E} {w v : ℕ → ℝ → E}
    (hx : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (x n) (x (n + 1)) (w n))
    (hz : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (y n) (z n) (v n))
    (hwX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖w n s - X s‖ ≤ γ)
    (hvX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖v n s - X s‖ ≤ γ)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hloc : ∀ n < N, ‖z n - y (n + 1)‖ ≤ C * τ * (τ ^ 2 + ε)) (h0 : x 0 = y 0) :
    ∀ n ≤ N, ‖x n - y n‖ ≤
      (T - t₀) * Real.exp ((L + ω) * (T - t₀)) * C * ε +
        (T - t₀) * Real.exp ((L + ω) * (T - t₀)) * C * τ ^ 2 := by
  set ℓ := C * τ * (τ ^ 2 + ε) with hℓ
  have hℓ0 : 0 ≤ ℓ := mul_nonneg (mul_nonneg hC hτ.le) (add_nonneg (sq_nonneg τ) hε)
  have key := discrete_gronwall_exp_le (e := fun n => ‖x n - y n‖) (b := ℓ) hLω hτ.le hℓ0
    fun n hn => by
      have h1 := strang_error_step hG hL hτ hΦ hN hx hz hwX hvX hn
      have h2 := hloc n hn
      linarith
  intro n hn
  have h := key n hn
  simp only [h0, sub_self, norm_zero, zero_add] at h
  have hnN : (n : ℝ) * τ ≤ T - t₀ := by
    have : (n : ℝ) * τ ≤ N * τ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hτ.le
    linarith
  have hnτ : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
  have hexp : Real.exp ((L + ω) * (n * τ)) ≤ Real.exp ((L + ω) * (T - t₀)) := by
    gcongr
  have hnℓ : (n : ℝ) * ℓ = (n * τ) * (C * (τ ^ 2 + ε)) := by rw [hℓ]; ring
  have hnℓ' : (n : ℝ) * ℓ ≤ (T - t₀) * (C * (τ ^ 2 + ε)) := by
    rw [hnℓ]; exact mul_le_mul_of_nonneg_right hnN (mul_nonneg hC (add_nonneg (sq_nonneg τ) hε))
  calc ‖x n - y n‖ ≤ Real.exp ((L + ω) * (n * τ)) * (n * ℓ) := h
    _ ≤ Real.exp ((L + ω) * (T - t₀)) * ((T - t₀) * (C * (τ ^ 2 + ε))) :=
        mul_le_mul hexp hnℓ' (mul_nonneg (Nat.cast_nonneg n) hℓ0) (Real.exp_pos _).le
    _ = _ := by ring

/-- **Theorem 1 of arXiv 2602.07437, corrected, conditional on Proposition 1 and Lemma 1.**
Data: the exact solution `X_ex`, the full-rank Strang iterates `xXₙ = Sⁿ_τ(X⁰)` and
`xYₙ = Sⁿ_τ(Y⁰)`, the low-rank iterates `yₙ = S̃ⁿ_τ(Y⁰)` (`y₀ = Y⁰`) and `zₙ = S_τ(yₙ)`.
If Proposition 1 holds (`hsp`: `‖X_ex(t₀+nτ) - Sⁿ_τ(X⁰)‖ ≤ C_sp τ²(1+|log τ|)`), Lemma 1 holds
(`hloc`) and `‖X⁰ - Y⁰‖ ≤ δ` (eq. (9)), then for `t₀ + nτ ≤ T`
`‖X_ex(t₀+nτ) - S̃ⁿ_τ(Y⁰)‖ ≤ c₀τ²(1+|log τ|) + c₁δ + c₂ε` with `c₀ = C_sp + c₂`,
`c₁ = e^{(L+ω)(T-t₀)}`, `c₂ = (T-t₀)e^{(L+ω)(T-t₀)}C`. This is the paper's proof: error
splitting `E_sp + E_δ + E_lr`, `strang_initial_error_le` and `strang_lowRank_error_le`.
`X_ex` enters only through `hsp`.

Conditional on Proposition 1 (`hsp`, not formalized), on Lemma 1 (`hloc`) and on the tube
property for all nonlinear trajectories used (`hwX`, `hwY`, `hvX`). Deviation: the paper
states `c₂τε`, which is false (`global_error_le_tau_mul_eps_fails`); the argument gives `c₂ε`.
Also needs `L + ω ≥ 0` (no loss). -/
theorem strang_global_error_le
    {G : ℝ → E → E} {X : ℝ → E} {t₀ T γ L ω τ : ℝ} {Φ : ℝ → E →L[ℝ] E}
    (hG : IsLipschitzOnTube G X t₀ T γ L) (hL : 0 ≤ L) (hLω : 0 ≤ L + ω) (hτ : 0 < τ)
    (hΦ : ∀ s, 0 < s → ∀ Z : E, ‖Φ s Z‖ ≤ Real.exp (ω * s) * ‖Z‖)
    {N : ℕ} (hN : t₀ + N * τ ≤ T) {Xex : ℝ → E} {xX xY y z : ℕ → E}
    {wX wY v : ℕ → ℝ → E}
    (hxX : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (xX n) (xX (n + 1)) (wX n))
    (hxY : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (xY n) (xY (n + 1)) (wY n))
    (hz : ∀ n < N, IsStrangStep G Φ (t₀ + n * τ) τ (y n) (z n) (v n))
    (hwX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖wX n s - X s‖ ≤ γ)
    (hwY : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖wY n s - X s‖ ≤ γ)
    (hvX : ∀ n < N, ∀ s ∈ Ico (t₀ + n * τ) (t₀ + n * τ + τ), ‖v n s - X s‖ ≤ γ)
    {Csp C ε δ : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hsp : ∀ n ≤ N, ‖Xex (t₀ + n * τ) - xX n‖ ≤ Csp * τ ^ 2 * (1 + |Real.log τ|))
    (hloc : ∀ n < N, ‖z n - y (n + 1)‖ ≤ C * τ * (τ ^ 2 + ε))
    (hδ : ‖xX 0 - xY 0‖ ≤ δ) (hy0 : y 0 = xY 0) :
    ∀ n ≤ N, ‖Xex (t₀ + n * τ) - y n‖ ≤
      (Csp + (T - t₀) * Real.exp ((L + ω) * (T - t₀)) * C) * τ ^ 2 * (1 + |Real.log τ|) +
        Real.exp ((L + ω) * (T - t₀)) * δ +
          (T - t₀) * Real.exp ((L + ω) * (T - t₀)) * C * ε := by
  intro n hn
  have hT : 0 ≤ T - t₀ := by
    have : 0 ≤ (N : ℝ) * τ := mul_nonneg (Nat.cast_nonneg N) hτ.le
    linarith
  have hsp' := hsp n hn
  have hδ' := strang_initial_error_le hG hL hLω hτ hΦ hN hxX hxY hwX hwY n hn
  have hlr := strang_lowRank_error_le hG hL hLω hτ hΦ hN hxY hz hwY hvX hC hε hloc hy0.symm n hn
  set c₂ := (T - t₀) * Real.exp ((L + ω) * (T - t₀)) * C with hc₂
  have hc₂0 : 0 ≤ c₂ := mul_nonneg (mul_nonneg hT (Real.exp_pos _).le) hC
  have hlog : τ ^ 2 ≤ τ ^ 2 * (1 + |Real.log τ|) :=
    le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg (Real.log τ)])
  have h1 : Real.exp ((L + ω) * (T - t₀)) * ‖xX 0 - xY 0‖ ≤ Real.exp ((L + ω) * (T - t₀)) * δ :=
    mul_le_mul_of_nonneg_left hδ (Real.exp_pos _).le
  calc ‖Xex (t₀ + n * τ) - y n‖
      ≤ ‖Xex (t₀ + n * τ) - xX n‖ + ‖xX n - xY n‖ + ‖xY n - y n‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (Xex (t₀ + n * τ)) (xX n) (y n)
        have := norm_sub_le_norm_sub_add_norm_sub (xX n) (xY n) (y n)
        linarith
    _ ≤ Csp * τ ^ 2 * (1 + |Real.log τ|) + Real.exp ((L + ω) * (T - t₀)) * δ +
          (c₂ * ε + c₂ * τ ^ 2) := by
        have := hδ'.trans h1
        linarith
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlog hc₂0]

/-- Non-vacuity of `strang_initial_error_le`, `strang_lowRank_error_le` and
`strang_global_error_le` on a nontrivial instance: `E = ℝ`, `G ≡ 1`, `Φ = id` (`ω = 0`), `L = 0`,
`τ = 1/2`, two steps up to `T = 1`, tube of radius `1` around `X(s) = s`. The full-rank iterates
`xₙ = n/2` are exact, so Proposition 1 holds with `C_sp = 0`; the "low-rank" iterates stay at `0`
and Lemma 1 holds with `C = ε = 1` (local error `1/2`). -/
example : True := by
  have hstep := fun n : ℕ => isStrangStep_const_iterates (1 : ℝ) 0 0 (1 / 2) n
  have hz : ∀ n : ℕ, IsStrangStep (fun _ _ => (1 : ℝ)) (fun _ => ContinuousLinearMap.id ℝ ℝ)
      (0 + n * (1 / 2)) (1 / 2) 0 (1 / 2) (fun s => 0 + (s - (0 + n * (1 / 2))) • (1 : ℝ)) :=
    fun n => ⟨odeSolution_const_field 1 0 _ _ _, by simp, by simp⟩
  have hn1 : ∀ n : ℕ, n < 2 → (n : ℝ) ≤ 1 := fun n hn => by exact_mod_cast Nat.lt_succ_iff.1 hn
  have := strang_global_error_le (G := fun _ _ => (1 : ℝ)) (X := fun s => s) (t₀ := 0) (T := 1)
    (γ := 1) (L := 0) (ω := 0) (τ := 1 / 2) (Φ := fun _ => ContinuousLinearMap.id ℝ ℝ) (N := 2)
    (IsLipschitzField.isLipschitzOnTube (fun _ _ _ => by simp) _ _ _ _) le_rfl (by norm_num)
    (by norm_num) (fun _ _ _ => by simp) (by norm_num) (Xex := fun s => s)
    (y := fun _ => 0) (z := fun _ => 1 / 2) (fun n _ => hstep n) (fun n _ => hstep n)
    (fun n _ => hz n) (fun n _ s _ => by simp) (fun n _ s _ => by simp)
    (fun n hn s _ => by
      have := hn1 n hn
      simp only [zero_add, smul_eq_mul, mul_one, Real.norm_eq_abs]
      rw [show s - n * (1 / 2) - s = -(n * (1 / 2)) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
      linarith)
    (C := 1) (ε := 1) (Csp := 0) (δ := 0) zero_le_one zero_le_one
    (fun n _ => by simp) (fun n _ => by norm_num) (by simp) (by simp)
  trivial

end General

/-! ### Counterexamples to the printed statements -/

/-- **The printed stability exponent `(L+ω)τ/2` is wrong** (arXiv 2602.07437, proof of
Proposition 2, p. 14). Take `E = ℝ` (that is `m = 1`, `A = ω/2` with `ω = 1`, so
`Φ_t Z = e^{tA}Ze^{tA*} = e^t Z`), `G = 0` (Lipschitz with `L = 0` on every tube), `τ = 1`. Then
(10) holds with equality and every pair of Strang steps from `1` and `0` satisfies
`e^{(L+ω)τ/2}‖1 - 0‖ = e^{1/2} < e = ‖S_τ(1) - S_τ(0)‖`. The correct exponent `(L+ω)τ`, used in
the next line of the paper, is `strang_stability_localLipschitz`. -/
theorem strang_stability_half_exponent_fails :
    (∀ s, 0 < s → ∀ Z : ℝ,
      ‖(Real.exp s • ContinuousLinearMap.id ℝ ℝ) Z‖ ≤ Real.exp (1 * s) * ‖Z‖) ∧
    IsLipschitzField (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) 0 ∧
    (∃ (Y' Z' : ℝ) (w v : ℝ → ℝ),
      IsStrangStep (fun _ _ => 0) (fun s => Real.exp s • ContinuousLinearMap.id ℝ ℝ) 0 1 1 Y' w ∧
      IsStrangStep (fun _ _ => 0) (fun s => Real.exp s • ContinuousLinearMap.id ℝ ℝ) 0 1 0 Z' v) ∧
    ∀ {Y' Z' : ℝ} {w v : ℝ → ℝ},
      IsStrangStep (fun _ _ => 0) (fun s => Real.exp s • ContinuousLinearMap.id ℝ ℝ) 0 1 1 Y' w →
      IsStrangStep (fun _ _ => 0) (fun s => Real.exp s • ContinuousLinearMap.id ℝ ℝ) 0 1 0 Z' v →
      Real.exp ((0 + 1) * 1 / 2) * ‖(1 : ℝ) - 0‖ < ‖Y' - Z'‖ := by
  refine ⟨fun s _ Z => by simp [abs_of_pos (Real.exp_pos s)], fun _ _ _ => by simp,
    ⟨_, _, _, _, ⟨odeSolution_const_field 0 (Real.exp (1 / 2)) 0 0 (0 + 1), by simp, rfl⟩,
      ⟨odeSolution_const_field 0 0 0 0 (0 + 1), by simp, rfl⟩⟩, ?_⟩
  intro Y' Z' w v hw hv
  rw [hw.eq_of_const zero_le_one, hv.eq_of_const zero_le_one]
  simp only [add_zero, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
    mul_zero, sub_zero, norm_one]
  rw [← Real.exp_add, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_exp.2 (by norm_num)

section Matrix

open scoped Matrix LeanDLRA.Frobenius

/-- A complex square matrix of rank `< m` is at Frobenius distance at least `1` from the
identity (it has a kernel vector `v`, and `‖v‖ = ‖(I - Z)v‖ ≤ ‖I - Z‖_F ‖v‖`). Used for the
counterexamples below; the real analogue is `le_distLR_diagonal`. -/
theorem one_le_norm_one_sub_of_rank_lt {m : Type*} [Fintype m] [DecidableEq m]
    (Z : Matrix m m ℂ) (hZ : Z.rank < Fintype.card m) : 1 ≤ ‖(1 : Matrix m m ℂ) - Z‖ := by
  have hdet : Z.det = 0 := by
    by_contra h
    have hu : IsUnit Z := (Matrix.isUnit_iff_isUnit_det Z).2 (isUnit_iff_ne_zero.2 h)
    have := Matrix.rank_of_isUnit Z hu
    omega
  obtain ⟨v, hv0, hZv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : Nonempty m := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨j₀⟩ := hne
  set B : Matrix m m ℂ := Matrix.of fun i _ => v i with hB
  have hZB : Z * B = 0 := by
    ext i j
    have := congrFun hZv i
    simpa [hB, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hIB : (1 - Z) * B = B := by rw [Matrix.sub_mul, Matrix.one_mul, hZB, sub_zero]
  have hBpos : 0 < ‖B‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hv0
    ext i
    have := congrFun (congrFun h0 i) j₀
    simpa [hB] using this
  have hmul : ‖(1 - Z) * B‖ ≤ ‖1 - Z‖ * ‖B‖ := Matrix.frobenius_norm_mul (1 - Z) B
  rw [hIB] at hmul
  nlinarith

/-- `Y⁰ = diag(1, 0) + diag(0, 1) = I`: the counterexample's exact solution at `t = 1`. -/
private theorem diag_one_zero_add_diag_zero_one :
    (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) + Matrix.diagonal ![0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The data of the counterexamples satisfy Assumption 1(c) with `ε = 1`: for `Y⁰ = diag(1, 0)`
`= e₁e₁*` and `Q = diag(0, 1)`, `Y⁰Q = QY⁰ = 0` and `‖Q‖_F = 1`. The tangent projection at `Y⁰`
(with `U = V = e₁`) is `P(Y⁰)Z = Y⁰Z + ZY⁰ - Y⁰ZY⁰`, so `P(Y⁰)Q = 0`: the rank-1 approximation
`Y(t) ≡ Y⁰` of Section 2.1 exists, and `G(t, Y(t)) = M + R` with `M = 0`, `R = Q`, `‖R‖ = 1`. -/
theorem diag_mul_diag_eq_zero_and_norm_eq_one :
    (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![0, 1] = 0 ∧
    (Matrix.diagonal ![0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal ![1, 0] = 0 ∧
    ‖(Matrix.diagonal ![0, 1] : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [Matrix.frobenius_norm_def]
    simp [Fin.sum_univ_two, Matrix.diagonal_apply]

/-- For every `K` and `τ₀ > 0` there is `N ≥ 1` with `1/N ≤ τ₀` and `K/N < 1`. -/
private theorem exists_nat_step (K τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 / (N : ℝ) ≤ τ₀ ∧ K * (1 / (N : ℝ)) < 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (|K|) (1 / τ₀))
  have hmax := le_max_left (|K|) (1 / τ₀)
  have hmax' := le_max_right (|K|) (1 / τ₀)
  have h1τ : 0 < 1 / τ₀ := by positivity
  have hNpos : (0 : ℝ) < N := by linarith
  refine ⟨N, Nat.succ_le_of_lt (Nat.cast_pos.1 hNpos), ?_, ?_⟩
  · rw [div_le_iff₀ hNpos]
    have : 1 / τ₀ < N := by linarith
    rw [div_lt_iff₀ hτ₀] at this
    linarith
  · rw [mul_one_div, div_lt_one hNpos]
    linarith [le_abs_self K]

/-- **Proposition 2 of arXiv 2602.07437 is false as printed** (`‖Eⁿ_lr‖ ≤ C₁ετ + C₂τ²`).
Take `m = 2`, `r = 1`, `t₀ = 0`, `T = 1`, `A = 0` (so `Φ^A = id`; Assumption 1(a) holds with
`ω = 0`, and (11), 1(d) trivially), `G ≡ Q = diag(0, 1)` (Assumption 1(b) with `L = 0`,
`B = 1`), `Y⁰ = diag(1, 0)`. Then `QY⁰ = Y⁰Q = 0`, so `P(Y⁰)Q = 0`, the rank-1 approximation
of the paper is `Y(t) ≡ Y⁰` and Assumption 1(c) holds with `M = 0`, `R = Q`, `ε = ‖Q‖ = 1`.

The statement: for all `C₁, C₂, ε` and `τ₀ > 0` there are `0 < τ ≤ τ₀` and `n ≥ 1` with `nτ = 1`
such that every sequence of full-rank Strang iterates `xₖ = Sᵏ_τ(Y⁰)` (`IsStrangStep`) satisfies
`C₁ετ + C₂τ² < ‖xₙ - Ỹ‖` for every `Ỹ` of rank `≤ 1`, in particular for `Ỹ = S̃ⁿ_τ(Y⁰)`, whatever
the low-rank integrator. Reason: `xₙ = Y⁰ + nτQ = I`. The paper's proof gives `C₁ε + C₂τ²`
(`strang_lowRank_error_le`). -/
theorem lowRank_error_le_eps_mul_tau_fails (C₁ C₂ ε τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * τ = 1 ∧
      (∃ (x : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (w : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ),
        x 0 = Matrix.diagonal ![1, 0] ∧
        ∀ k < n, IsStrangStep (fun _ _ => Matrix.diagonal ![0, 1])
          (fun _ => ContinuousLinearMap.id ℝ _) (0 + k * τ) τ (x k) (x (k + 1)) (w k)) ∧
      ∀ (x : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (w : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ),
        x 0 = Matrix.diagonal ![1, 0] →
        (∀ k < n, IsStrangStep (fun _ _ => Matrix.diagonal ![0, 1])
          (fun _ => ContinuousLinearMap.id ℝ _) (0 + k * τ) τ (x k) (x (k + 1)) (w k)) →
        ∀ Ylr : Matrix (Fin 2) (Fin 2) ℂ, Ylr.rank ≤ 1 → C₁ * ε * τ + C₂ * τ ^ 2 < ‖x n - Ylr‖ := by
  obtain ⟨N, hN1, hNτ, hNK⟩ := exists_nat_step (|C₁ * ε| + |C₂|) τ₀ hτ₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hτpos : (0 : ℝ) < 1 / N := div_pos one_pos hNpos
  have hτ1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact_mod_cast hN1
  have hNτ1 : (N : ℝ) * (1 / N) = 1 := mul_one_div_cancel hNpos.ne'
  refine ⟨1 / N, hτpos, hNτ, N, hN1, hNτ1,
    ⟨_, _, by simp, fun k _ => isStrangStep_const_iterates (Matrix.diagonal ![0, 1])
      (Matrix.diagonal ![1, 0]) 0 (1 / N) k⟩, fun x w hx0 hx Ylr hYlr => ?_⟩
  have hxN := strang_iterates_const hτpos.le hx N le_rfl
  rw [hx0, hNτ1, one_smul, diag_one_zero_add_diag_zero_one] at hxN
  rw [hxN]
  have hlow := one_le_norm_one_sub_of_rank_lt Ylr (by rw [Fintype.card_fin]; omega)
  have hb1 : C₁ * ε * (1 / N) ≤ |C₁ * ε| * (1 / N) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hτpos.le
  have hb2 : C₂ * (1 / (N : ℝ)) ^ 2 ≤ |C₂| * (1 / N) := by
    have hsq : (1 / (N : ℝ)) ^ 2 ≤ 1 / N := by
      rw [sq]; exact mul_le_of_le_one_left hτpos.le hτ1
    calc C₂ * (1 / (N : ℝ)) ^ 2 ≤ |C₂| * (1 / (N : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₂| * (1 / N) := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  nlinarith

/-- **Theorem 1 of arXiv 2602.07437 is false as printed**
(`‖X(t₀+nτ) - S̃ⁿ_τ(Y⁰)‖ ≤ c₀τ²(1+|log τ|) + c₁δ + c₂τε`). Same problem as in
`lowRank_error_le_eps_mul_tau_fails`, with `X⁰ = Y⁰ = diag(1, 0)`, so `δ = ‖X⁰ - Y⁰‖ = 0` is
admissible in (9). Every solution `X` of (1) (`Ẋ = AX + XA* + G` with `A = 0`, `G ≡ diag(0,1)`)
from `X⁰` satisfies `X(1) = I`, so for all `c₀, c₁, c₂, ε` and `τ₀ > 0` there are `0 < τ ≤ τ₀`
and `n ≥ 1` with `nτ = 1` such that every `Ỹ` of rank `≤ 1` (in particular `S̃ⁿ_τ(Y⁰)`) violates
the printed bound. The paper's argument gives `c₂ε` (`strang_global_error_le`). -/
theorem global_error_le_tau_mul_eps_fails (c₀ c₁ c₂ ε τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧ ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * τ = 1 ∧
      (∃ X : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
        ODESolution (fun _ Z => (0 : Matrix (Fin 2) (Fin 2) ℂ) * Z + Z * (0 : Matrix _ _ ℂ)ᴴ +
          Matrix.diagonal ![0, 1]) X 0 1 ∧ X 0 = Matrix.diagonal ![1, 0]) ∧
      ∀ X : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
        ODESolution (fun _ Z => (0 : Matrix (Fin 2) (Fin 2) ℂ) * Z + Z * (0 : Matrix _ _ ℂ)ᴴ +
          Matrix.diagonal ![0, 1]) X 0 1 →
        X 0 = Matrix.diagonal ![1, 0] →
        ∀ Ylr : Matrix (Fin 2) (Fin 2) ℂ, Ylr.rank ≤ 1 →
          c₀ * τ ^ 2 * (1 + |Real.log τ|) + c₁ * ‖X 0 - Matrix.diagonal ![1, 0]‖ +
            c₂ * τ * ε < ‖X (0 + n * τ) - Ylr‖ := by
  obtain ⟨N, hN1, hNτ, hNK⟩ := exists_nat_step (|c₀| + |c₂ * ε|) τ₀ hτ₀
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hτpos : (0 : ℝ) < 1 / N := div_pos one_pos hNpos
  have hNτ1 : (N : ℝ) * (1 / N) = 1 := mul_one_div_cancel hNpos.ne'
  -- the solution of (1) is `X(t) = Y⁰ + t Q`
  have hu : ODESolution (fun _ Z => (0 : Matrix (Fin 2) (Fin 2) ℂ) * Z +
      Z * (0 : Matrix _ _ ℂ)ᴴ + Matrix.diagonal ![0, 1])
      (fun s => Matrix.diagonal ![1, 0] + s • Matrix.diagonal ![0, 1]) 0 1 := by
    refine ⟨(continuous_const.add (continuous_id.smul continuous_const)).continuousOn,
      fun s _ => ?_⟩
    have := ((hasDerivAt_id s).smul_const
      (Matrix.diagonal ![0, 1] : Matrix (Fin 2) (Fin 2) ℂ)).const_add
      (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
    simpa using this.hasDerivWithinAt
  refine ⟨1 / N, hτpos, hNτ, N, hN1, hNτ1, ⟨_, hu, by simp⟩, fun X hX hX0 Ylr hYlr => ?_⟩
  set Q : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, 1] with hQ
  have hL : IsLipschitzField (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℂ) =>
      (0 : Matrix (Fin 2) (Fin 2) ℂ) * Z + Z * (0 : Matrix _ _ ℂ)ᴴ + Q) 0 :=
    fun _ _ _ => by simp
  have heq := hX.eqOn hu hL le_rfl (by simp [hX0])
  have hX1 : X (0 + N * (1 / N)) = 1 := by
    rw [zero_add, hNτ1, heq (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
    change Matrix.diagonal ![1, 0] + (1 : ℝ) • Q = 1
    rw [one_smul, hQ, diag_one_zero_add_diag_zero_one]
  rw [hX1, hX0, sub_self, norm_zero, mul_zero, add_zero]
  have hlow := one_le_norm_one_sub_of_rank_lt Ylr (by rw [Fintype.card_fin]; omega)
  -- `τ²(1 + |log τ|) ≤ τ` for `τ = 1/N`, since `log N ≤ N - 1`
  have hlogN : |Real.log (1 / (N : ℝ))| ≤ N - 1 := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN1))]
    exact Real.log_le_sub_one_of_pos hNpos
  have hsq : (1 / (N : ℝ)) ^ 2 * (1 + |Real.log (1 / N)|) ≤ 1 / N := by
    calc (1 / (N : ℝ)) ^ 2 * (1 + |Real.log (1 / N)|) ≤ (1 / (N : ℝ)) ^ 2 * N :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / N := by field_simp
  have hb1 : c₀ * (1 / (N : ℝ)) ^ 2 * (1 + |Real.log (1 / N)|) ≤ |c₀| * (1 / N) := by
    rw [mul_assoc]
    calc c₀ * ((1 / (N : ℝ)) ^ 2 * (1 + |Real.log (1 / N)|))
        ≤ |c₀| * ((1 / (N : ℝ)) ^ 2 * (1 + |Real.log (1 / N)|)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |c₀| * (1 / N) := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  have hb2 : c₂ * (1 / (N : ℝ)) * ε ≤ |c₂ * ε| * (1 / N) := by
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hτpos.le
  nlinarith

end Matrix

end LeanDLRA.Literature.P2602_07437
