import LeanDLRA.Foundations.OneSided
import LeanDLRA.Stiff.ImplicitSolvability

/-!
# arXiv 2611.04360, Section 5.3: propagation of the errors of a step

Lemma 5.3 in the paper's form, Lemma 5.4 and Proposition 5.3 of arXiv 2611.04360, on an abstract
finite-dimensional inner product space `E` whose norm is the energy norm `‖·‖_E`. The proof of
Lemma 5.3 in the paper makes this reduction itself ("`⟨x, y⟩_E = xᵀ W V⁻¹ y` is an inner product
with norm `‖·‖_E`, and `xᵀ W y = ⟨x, V y⟩_E`"); module (a) realizes it for the matrices of the
scheme (`EnergySpace`, `energy_inner_ge`). The operators are linear maps `V⁻¹`, `V`, `𝒜` with
`V V⁻¹ = I`; `stepK`, `stepB` are `K`, `B` of (4.13), `stepInv` is `K⁻¹`, `amplification` is
`ϑ = (1 + (1 - θ) γ Δt) / (1 - θ γ Δt)`.

* The energy inequality `⟨z, V 𝒜 z⟩_E ≥ -γ ‖z‖²_E` is the paper's own hypothesis of Lemma 5.3
  and Proposition 5.3 ("with `γ` satisfying the energy inequality above"); Lemma 5.2 proves it for
  isotropic scattering (module (a), `energy_inequality`). The results here are therefore not
  conditional on an unproved step. `energyInequality_iff_isOneSidedLipschitzField` shows that
  it is the core `LeanDLRA.IsOneSidedLipschitzField` for `z ↦ -V 𝒜 z`, and
  `isOneSidedLipschitzField_semidiscrete` applies this to the semi-discrete system (4.11).
* Lemma 5.3: `stepK_bijective`, `norm_stepInv_le` (i), `norm_stepInv_stepB_le` (ii) and
  `norm_stepInv_stepB_pow_le`, from the core `LeanDLRA.thetaMethod_resolvent` and
  `LeanDLRA.thetaMethod_step_le`.
* Lemma 5.4: `deliveredResidual` (`ρ̂ⁿ`), `stepResidual` (`ρⁿ`, (5.23)), `stepResidual_eq`
  (`ρⁿ = ρ̂ⁿ + K (rⁿ + pⁿ)`), `error_succ_of_stepResidual` and `error_eq_sum_stepResidual`
  ((5.24)), `error_succ` ((5.25)) and `error_eq_sum` ((5.26)).
* Proposition 5.3: `norm_error_le` ((5.27)).

Differences from the printed statements: `γ ≥ 0` is assumed in Lemma 5.3 (ii) and
Proposition 5.3 (it holds for the `γ` of Lemma 5.2 and of Appendix E, both maxima with `0`, and
the proof of (ii) uses it), `Δt ≥ 0`, and `E` is finite-dimensional (for the invertibility of
`K`). Lemma 5.3 (i) is proved for every `θ ≥ 0`, not only `1/2 ≤ θ ≤ 1`. Lemma 5.4 needs only that
`K` is invertible (hypothesis `hK`, supplied by `stepK_bijective`). Not formalized: the split of
`ρⁿ` into compression terms, the group balance projection and the TT-BUG remarks.

Core definitions used: `LeanDLRA.IsOneSidedLipschitzField`, `LeanDLRA.thetaMethod_resolvent`,
`LeanDLRA.thetaMethod_step_le`. Local definitions: `stepK`, `stepB`, `stepInv`, `amplification`,
`deliveredResidual`, `stepResidual` (the core has no θ-method step structure).
-/

open Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2611_04360

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The θ-method step and the energy inequality -/

/-- The physics matrix `K = V⁻¹ + θ Δt 𝒜` of the θ-method step (4.13) of arXiv 2611.04360. -/
def stepK (Vi A : E →ₗ[ℝ] E) (θ Δt : ℝ) : E →ₗ[ℝ] E := Vi + (θ * Δt) • A

/-- The right-hand matrix `B = V⁻¹ - (1 - θ) Δt 𝒜` of the θ-method step (4.13). -/
def stepB (Vi A : E →ₗ[ℝ] E) (θ Δt : ℝ) : E →ₗ[ℝ] E := Vi - ((1 - θ) * Δt) • A

/-- The inverse `K⁻¹` of the physics matrix when `K` is bijective (Lemma 5.3 (i) of
arXiv 2611.04360 shows that it is), and `0` otherwise. -/
noncomputable def stepInv (Vi A : E →ₗ[ℝ] E) (θ Δt : ℝ) : E →ₗ[ℝ] E := by
  classical
  exact if h : Function.Bijective (stepK Vi A θ Δt) then
    ((LinearEquiv.ofBijective (stepK Vi A θ Δt) h).symm : E ≃ₗ[ℝ] E).toLinearMap
  else 0

/-- The amplification factor `ϑ = (1 + (1 - θ) γ Δt) / (1 - θ γ Δt)` of one step
(Section 5.3 of arXiv 2611.04360). -/
noncomputable def amplification (γ θ Δt : ℝ) : ℝ := (1 + (1 - θ) * γ * Δt) / (1 - θ * γ * Δt)

lemma stepK_stepInv {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ} (hK : Function.Bijective (stepK Vi A θ Δt))
    (y : E) : stepK Vi A θ Δt (stepInv Vi A θ Δt y) = y := by
  simp only [stepInv, hK, dite_true]
  exact (LinearEquiv.ofBijective (stepK Vi A θ Δt) hK).apply_symm_apply y

lemma stepInv_stepK {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ} (hK : Function.Bijective (stepK Vi A θ Δt))
    (z : E) : stepInv Vi A θ Δt (stepK Vi A θ Δt z) = z := by
  simp only [stepInv, hK, dite_true]
  exact (LinearEquiv.ofBijective (stepK Vi A θ Δt) hK).symm_apply_apply z

/-- The energy inequality `xᵀ W 𝒜 x ≥ -γ ‖x‖²_E` of arXiv 2611.04360 (Lemma 5.2, Appendix E),
written in the energy inner product as `⟨x, V 𝒜 x⟩_E ≥ -γ ‖x‖²_E`, is the statement that the
field `x ↦ -V 𝒜 x` of the semi-discrete system (4.11) is one-sided Lipschitz with constant `γ`
in the energy norm (the core `LeanDLRA.IsOneSidedLipschitzField`). -/
theorem energyInequality_iff_isOneSidedLipschitzField (V A : E →ₗ[ℝ] E) (γ : ℝ) :
    (∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) ↔
      IsOneSidedLipschitzField (fun _ z => -(V (A z))) γ := by
  constructor
  · intro h t x y
    have := h (x - y)
    rw [← neg_sub', ← map_sub, ← map_sub, inner_neg_left, real_inner_comm]
    linarith
  · intro h z
    have := h 0 z 0
    simp only [map_zero, neg_zero, sub_zero, inner_neg_left, real_inner_comm] at this
    linarith

/-- The semi-discrete system (4.11) of arXiv 2611.04360, `V⁻¹ Ψ' + 𝒜 Ψ = Q(t)`, written as
`Ψ' = V Q(t) - V 𝒜 Ψ`: under the energy inequality its right-hand side is one-sided Lipschitz with
constant `γ` in the energy norm, so the core stability results for one-sided Lipschitz fields
(`LeanDLRA.norm_sub_le_exp_of_oneSided`, ...) apply to it. -/
theorem isOneSidedLipschitzField_semidiscrete (V A : E →ₗ[ℝ] E) (Q : ℝ → E) {γ : ℝ}
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) :
    IsOneSidedLipschitzField (fun t Ψ => -(V (A Ψ)) + V (Q t)) γ :=
  ((energyInequality_iff_isOneSidedLipschitzField V A γ).1 hγ).add_forcing fun t => V (Q t)

/-! ### Lemma 5.4: the errors of a computed step -/

/-- The residual `ρ̂ⁿ = K Ψ̂ⁿ⁺¹ - B Ψ̃ⁿ - qⁿ` of the state `Ψ̂ⁿ⁺¹` that the linear solver delivers
(Section 5.3 of arXiv 2611.04360; `Ψ̃ⁿ` is the carried state, `qⁿ` the source). -/
def deliveredResidual (Vi A : E →ₗ[ℝ] E) (θ Δt : ℝ) (Ψh Ψt q : ℕ → E) (n : ℕ) : E :=
  stepK Vi A θ Δt (Ψh (n + 1)) - stepB Vi A θ Δt (Ψt n) - q n

/-- The residual `ρⁿ = K Ψ̃ⁿ⁺¹ - B Ψ̃ⁿ - qⁿ` of the computed step, (5.23) of arXiv 2611.04360. -/
def stepResidual (Vi A : E →ₗ[ℝ] E) (θ Δt : ℝ) (Ψt q : ℕ → E) (n : ℕ) : E :=
  stepK Vi A θ Δt (Ψt (n + 1)) - stepB Vi A θ Δt (Ψt n) - q n

/-- The split of the residual (Section 5.3 of arXiv 2611.04360): with the carried state
`Ψ̃ⁿ⁺¹ = Ψ̂ⁿ⁺¹ + rⁿ + pⁿ` (rounding `rⁿ`, balance projection `pⁿ`), `ρⁿ = ρ̂ⁿ + K (rⁿ + pⁿ)`. -/
theorem stepResidual_eq {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ} {Ψh Ψt q r p : ℕ → E}
    (hcarry : ∀ n, Ψt (n + 1) = Ψh (n + 1) + r n + p n) (n : ℕ) :
    stepResidual Vi A θ Δt Ψt q n =
      deliveredResidual Vi A θ Δt Ψh Ψt q n + stepK Vi A θ Δt (r n + p n) := by
  rw [stepResidual, deliveredResidual, hcarry, add_assoc, map_add, map_add]
  abel

/-- Subtracting the exact step from (5.23) (arXiv 2611.04360): if `K` is invertible and the exact
θ-method states satisfy `K Ψⁿ⁺¹ = B Ψⁿ + qⁿ`, the errors `eⁿ = Ψ̃ⁿ - Ψⁿ` satisfy
`eⁿ⁺¹ = K⁻¹ B eⁿ + K⁻¹ ρⁿ`. -/
theorem error_succ_of_stepResidual {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ}
    (hK : Function.Bijective (stepK Vi A θ Δt)) {Ψ Ψt q : ℕ → E}
    (hΨ : ∀ n, stepK Vi A θ Δt (Ψ (n + 1)) = stepB Vi A θ Δt (Ψ n) + q n) (n : ℕ) :
    Ψt (n + 1) - Ψ (n + 1) = stepInv Vi A θ Δt (stepB Vi A θ Δt (Ψt n - Ψ n)) +
      stepInv Vi A θ Δt (stepResidual Vi A θ Δt Ψt q n) := by
  rw [← map_add, stepResidual, map_sub]
  have h : stepB Vi A θ Δt (Ψt n) - stepB Vi A θ Δt (Ψ n) +
      (stepK Vi A θ Δt (Ψt (n + 1)) - stepB Vi A θ Δt (Ψt n) - q n) =
      stepK Vi A θ Δt (Ψt (n + 1) - Ψ (n + 1)) := by
    rw [map_sub, hΨ]
    abel
  rw [h, stepInv_stepK hK]

/-- **Lemma 5.4 of arXiv 2611.04360, equation (5.25)**: if `K` is invertible (Lemma 5.3 (i)), the
exact θ-method states satisfy `K Ψⁿ⁺¹ = B Ψⁿ + qⁿ` and the carried states are
`Ψ̃ⁿ⁺¹ = Ψ̂ⁿ⁺¹ + rⁿ + pⁿ`, then the errors `eⁿ = Ψ̃ⁿ - Ψⁿ` satisfy
`eⁿ⁺¹ = K⁻¹ B eⁿ + K⁻¹ ρ̂ⁿ + rⁿ + pⁿ`. -/
theorem error_succ {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ} (hK : Function.Bijective (stepK Vi A θ Δt))
    {Ψ Ψh Ψt q r p : ℕ → E}
    (hΨ : ∀ n, stepK Vi A θ Δt (Ψ (n + 1)) = stepB Vi A θ Δt (Ψ n) + q n)
    (hcarry : ∀ n, Ψt (n + 1) = Ψh (n + 1) + r n + p n) (n : ℕ) :
    Ψt (n + 1) - Ψ (n + 1) = stepInv Vi A θ Δt (stepB Vi A θ Δt (Ψt n - Ψ n)) +
      stepInv Vi A θ Δt (deliveredResidual Vi A θ Δt Ψh Ψt q n) + r n + p n := by
  rw [error_succ_of_stepResidual hK hΨ n, stepResidual_eq hcarry n, map_add, stepInv_stepK hK]
  abel

/-- Unrolling a linear error recursion `eⁿ⁺¹ = T eⁿ + dⁿ` with `e⁰ = 0`:
`e^N = Σ_{n < N} T^{N-1-n} dⁿ`. -/
lemma eq_sum_pow_of_succ (T : E →ₗ[ℝ] E) {e d : ℕ → E} (h0 : e 0 = 0)
    (he : ∀ n, e (n + 1) = T (e n) + d n) (N : ℕ) :
    e N = ∑ n ∈ range N, (T ^ (N - 1 - n)) (d n) := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [he, ih, map_sum, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      Module.End.one_apply]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn : n < N := mem_range.1 hn
    rw [← Module.End.mul_apply, ← pow_succ']
    congr 3
    omega

/-- **Lemma 5.4 of arXiv 2611.04360, equation (5.26)**: in the setting of `error_succ`, with
`e⁰ = 0`, `e^{N_t} = Σ_{n < N_t} (K⁻¹ B)^{N_t - 1 - n} (K⁻¹ ρ̂ⁿ + rⁿ + pⁿ)`. -/
theorem error_eq_sum {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ} (hK : Function.Bijective (stepK Vi A θ Δt))
    {Ψ Ψh Ψt q r p : ℕ → E}
    (hΨ : ∀ n, stepK Vi A θ Δt (Ψ (n + 1)) = stepB Vi A θ Δt (Ψ n) + q n)
    (hcarry : ∀ n, Ψt (n + 1) = Ψh (n + 1) + r n + p n) (h0 : Ψt 0 - Ψ 0 = 0) (Nt : ℕ) :
    Ψt Nt - Ψ Nt = ∑ n ∈ range Nt, ((stepInv Vi A θ Δt ∘ₗ stepB Vi A θ Δt) ^ (Nt - 1 - n))
      (stepInv Vi A θ Δt (deliveredResidual Vi A θ Δt Ψh Ψt q n) + r n + p n) :=
  eq_sum_pow_of_succ (e := fun n => Ψt n - Ψ n) _ h0 (fun n => by
    rw [error_succ hK hΨ hcarry n, LinearMap.comp_apply]
    abel) Nt

/-- Equation (5.24) of arXiv 2611.04360: with `e⁰ = 0`,
`e^{N_t} = Σ_{n < N_t} (K⁻¹ B)^{N_t - 1 - n} K⁻¹ ρⁿ` for the residuals `ρⁿ` of (5.23). -/
theorem error_eq_sum_stepResidual {Vi A : E →ₗ[ℝ] E} {θ Δt : ℝ}
    (hK : Function.Bijective (stepK Vi A θ Δt)) {Ψ Ψt q : ℕ → E}
    (hΨ : ∀ n, stepK Vi A θ Δt (Ψ (n + 1)) = stepB Vi A θ Δt (Ψ n) + q n)
    (h0 : Ψt 0 - Ψ 0 = 0) (Nt : ℕ) :
    Ψt Nt - Ψ Nt = ∑ n ∈ range Nt, ((stepInv Vi A θ Δt ∘ₗ stepB Vi A θ Δt) ^ (Nt - 1 - n))
      (stepInv Vi A θ Δt (stepResidual Vi A θ Δt Ψt q n)) :=
  eq_sum_pow_of_succ (e := fun n => Ψt n - Ψ n) _ h0 (fun n => by
    rw [error_succ_of_stepResidual hK hΨ n, LinearMap.comp_apply]) Nt

variable [FiniteDimensional ℝ E]

/-! ### Lemma 5.3 -/

/-- **Lemma 5.3 (i) of arXiv 2611.04360**, invertibility: for `θ, Δt ≥ 0` with `θ γ Δt < 1` and
the energy inequality `⟨z, V 𝒜 z⟩_E ≥ -γ ‖z‖²_E` (with `V V⁻¹ = I`), `K` is invertible. From the
core `LeanDLRA.thetaMethod_resolvent`. -/
theorem stepK_bijective {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt) (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫)
    (hs : θ * γ * Δt < 1) : Function.Bijective (stepK Vi A θ Δt) :=
  (LeanDLRA.thetaMethod_resolvent hVVi hθ hΔt hγ hs).1

/-- **Lemma 5.3 (i) of arXiv 2611.04360**, the bound: `‖K⁻¹ y‖_E ≤ ‖V y‖_E / (1 - θ γ Δt)`. -/
theorem norm_stepInv_le {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 0 ≤ θ) (hΔt : 0 ≤ Δt) (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫)
    (hs : θ * γ * Δt < 1) (y : E) :
    ‖stepInv Vi A θ Δt y‖ ≤ ‖V y‖ / (1 - θ * γ * Δt) := by
  obtain ⟨hK, hbd⟩ := LeanDLRA.thetaMethod_resolvent hVVi hθ hΔt hγ hs
  rw [le_div_iff₀ (by linarith), mul_comm]
  exact hbd y _ (stepK_stepInv hK y)

/-- **Lemma 5.3 (ii) of arXiv 2611.04360**: for `1/2 ≤ θ ≤ 1`, `γ ≥ 0` (as for the `γ` of
Lemma 5.2 and Appendix E), `Δt ≥ 0`, `θ γ Δt < 1` and the energy inequality,
`‖K⁻¹ B x‖_E ≤ ϑ ‖x‖_E`. From the core `LeanDLRA.thetaMethod_step_le`. -/
theorem norm_stepInv_stepB_le {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hγ0 : 0 ≤ γ) (hΔt : 0 ≤ Δt)
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) (hs : θ * γ * Δt < 1) (x : E) :
    ‖stepInv Vi A θ Δt (stepB Vi A θ Δt x)‖ ≤ amplification γ θ Δt * ‖x‖ := by
  have hK := stepK_bijective hVVi (by linarith) hΔt hγ hs
  have hz := stepK_stepInv hK (stepB Vi A θ Δt x)
  have h := LeanDLRA.thetaMethod_step_le hVVi hθ hθ1 hγ0 hΔt hγ hs
    (x := x) (z := stepInv Vi A θ Δt (stepB Vi A θ Δt x)) (by simpa [stepK, stepB] using hz)
  rw [amplification, div_mul_eq_mul_div, le_div_iff₀ (by linarith), mul_comm]
  exact h

/-- Powers of the step propagator: `‖(K⁻¹ B)^k x‖_E ≤ ϑ^k ‖x‖_E` (proof of Proposition 5.3 of
arXiv 2611.04360, "Lemma 5.3 (ii) once for each of the factors `K⁻¹ B`"). -/
theorem norm_stepInv_stepB_pow_le {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hγ0 : 0 ≤ γ) (hΔt : 0 ≤ Δt)
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) (hs : θ * γ * Δt < 1) (k : ℕ) (x : E) :
    ‖((stepInv Vi A θ Δt ∘ₗ stepB Vi A θ Δt) ^ k) x‖ ≤ amplification γ θ Δt ^ k * ‖x‖ := by
  have hϑ : 0 ≤ amplification γ θ Δt := by
    rw [amplification]
    apply div_nonneg
    · have : 0 ≤ (1 - θ) * γ * Δt := mul_nonneg (mul_nonneg (by linarith) hγ0) hΔt
      linarith
    · linarith
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.comp_apply, pow_succ', mul_assoc]
    exact (norm_stepInv_stepB_le hVVi hθ hθ1 hγ0 hΔt hγ hs _).trans
      (mul_le_mul_of_nonneg_left ih hϑ)

/-! ### Proposition 5.3 -/

/-- **Proposition 5.3 of arXiv 2611.04360, equation (5.27)**: let `1/2 ≤ θ ≤ 1`, `θ γ Δt < 1`
and `e⁰ = 0`, with `γ ≥ 0` satisfying the energy inequality `⟨z, V 𝒜 z⟩_E ≥ -γ ‖z‖²_E` (the
paper's standing assumption of Section 5.3, proved for isotropic scattering in Lemma 5.2) and
`V V⁻¹ = I`. If the exact θ-method states satisfy `K Ψⁿ⁺¹ = B Ψⁿ + qⁿ` and the carried states
are `Ψ̃ⁿ⁺¹ = Ψ̂ⁿ⁺¹ + rⁿ + pⁿ`, then
`‖e^{N_t}‖_E ≤ Σ_{n < N_t} ϑ^{N_t - 1 - n} (‖rⁿ‖_E + ‖pⁿ‖_E + ‖V ρ̂ⁿ‖_E / (1 - θ γ Δt))`.
The norm is that of the inner product space `E` (the energy norm), which is how the paper's proof
of Lemma 5.3 reads `‖·‖_E`; `ρ̂ⁿ` is `deliveredResidual`. -/
theorem norm_error_le {Vi V A : E →ₗ[ℝ] E} (hVVi : ∀ z, V (Vi z) = z) {γ θ Δt : ℝ}
    (hθ : 1 / 2 ≤ θ) (hθ1 : θ ≤ 1) (hγ0 : 0 ≤ γ) (hΔt : 0 ≤ Δt)
    (hγ : ∀ z, -γ * ‖z‖ ^ 2 ≤ ⟪z, V (A z)⟫) (hs : θ * γ * Δt < 1) {Ψ Ψh Ψt q r p : ℕ → E}
    (hΨ : ∀ n, stepK Vi A θ Δt (Ψ (n + 1)) = stepB Vi A θ Δt (Ψ n) + q n)
    (hcarry : ∀ n, Ψt (n + 1) = Ψh (n + 1) + r n + p n) (h0 : Ψt 0 - Ψ 0 = 0) (Nt : ℕ) :
    ‖Ψt Nt - Ψ Nt‖ ≤ ∑ n ∈ range Nt, amplification γ θ Δt ^ (Nt - 1 - n) *
      (‖r n‖ + ‖p n‖ + ‖V (deliveredResidual Vi A θ Δt Ψh Ψt q n)‖ / (1 - θ * γ * Δt)) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hK := stepK_bijective hVVi hθ0 hΔt hγ hs
  have hϑ : 0 ≤ amplification γ θ Δt := by
    rw [amplification]
    apply div_nonneg
    · have : 0 ≤ (1 - θ) * γ * Δt := mul_nonneg (mul_nonneg (by linarith) hγ0) hΔt
      linarith
    · linarith
  rw [error_eq_sum hK hΨ hcarry h0 Nt]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  refine (norm_stepInv_stepB_pow_le hVVi hθ hθ1 hγ0 hΔt hγ hs _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hϑ _)
  have h1 := norm_stepInv_le hVVi hθ0 hΔt hγ hs (deliveredResidual Vi A θ Δt Ψh Ψt q n)
  calc ‖stepInv Vi A θ Δt (deliveredResidual Vi A θ Δt Ψh Ψt q n) + r n + p n‖
      ≤ ‖stepInv Vi A θ Δt (deliveredResidual Vi A θ Δt Ψh Ψt q n)‖ + ‖r n‖ + ‖p n‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

/-! ### Non-vacuity -/

/-- Non-vacuity of Proposition 5.3 (arXiv 2611.04360): on `E = ℝ` with `V = V⁻¹ = I` and `𝒜 = 0`
(so `γ = 0` and `ϑ = 1`), Crank–Nicolson `θ = 1/2`, exact states `Ψⁿ = 0`, exact solves
`Ψ̂ⁿ⁺¹ = Ψ̃ⁿ` and a rounding `rⁿ = 1` at every step (carried states `Ψ̃ⁿ = n`), the hypotheses
hold and the bound reads `‖e^{N_t}‖ ≤ N_t`. -/
example (Nt : ℕ) :
    ‖(fun n : ℕ => (n : ℝ)) Nt - (fun _ : ℕ => (0 : ℝ)) Nt‖ ≤
      ∑ n ∈ range Nt, amplification 0 (1 / 2) 1 ^ (Nt - 1 - n) *
        (‖(fun _ : ℕ => (1 : ℝ)) n‖ + ‖(fun _ : ℕ => (0 : ℝ)) n‖ +
          ‖(LinearMap.id : ℝ →ₗ[ℝ] ℝ) (deliveredResidual (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 0 (1 / 2) 1
            (fun n : ℕ => (n : ℝ) - 1) (fun n : ℕ => (n : ℝ)) (fun _ => 0) n)‖ /
              (1 - 1 / 2 * 0 * 1)) :=
  norm_error_le (Vi := LinearMap.id) (V := LinearMap.id) (A := 0) (fun _ => rfl) (by norm_num)
    (by norm_num) le_rfl zero_le_one (fun z => by simp) (by norm_num)
    (Ψ := fun _ => 0) (Ψh := fun n : ℕ => (n : ℝ) - 1) (q := fun _ => 0) (p := fun _ => 0)
    (fun n => by simp [stepK, stepB]) (fun n => by push_cast; ring) (by simp) Nt

end LeanDLRA.Literature.P2611_04360
