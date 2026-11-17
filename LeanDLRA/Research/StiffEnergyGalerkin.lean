import LeanDLRA.Stiff.CouplingLocalError

/-!
# Stiff problems: an energy bound for the Galerkin step without coupling numbers

For a stiff linear equation with forcing, `Y' = 𝓛 Y + g(t)`, with a symmetric and dissipative
operator `𝓛` (for example `𝓛 Y = M Y + Y N` with symmetric negative semidefinite `M`, `N`), this
file bounds the error of the Galerkin step of the rank-adaptive BUG integrator, and of a
sequence of steps, against an exact solution `A` given on the whole time interval. The bound
contains neither the norm of `𝓛` nor coupling numbers of `𝓛` with the subspaces of the step
(compare `IsRankAdaptiveBUGStep.stiff_local_error`). The stiff operator enters through one
quantity only, the energy

  `-⟪𝓛 η, η⟫`, `η = A(t) - R A(t)`,

of the part of the exact solution outside the Galerkin space `range R`, `R = P₁ Q₁`. This is the
estimate of the Galerkin method for parabolic problems, applied to the Galerkin step of the
integrator.

## Main results

* `inner_apply_add_le_of_symm_dissipative`: for symmetric dissipative `𝓛`,
  `⟪w, 𝓛 (w + η)⟫ ≤ -⟪𝓛 η, η⟫ / 4`.
* `stiff_galerkin_energy_compare`: if `Y' = R (𝓛 Y + g)` in `range R` and `-⟪𝓛 η, η⟫ ≤ γ` on the
  interval, then `‖R A(t) - Y(t)‖² ≤ ‖R A(a) - Y(a)‖² + (γ / 2) (t - a)`.
* `IsRankAdaptiveBUGStep.stiff_energy_error`: for one step, with `-⟪𝓛 η, η⟫ ≤ γ²` on the step
  and `‖η(t₁)‖ ≤ θ`,
  `‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + γ √(h / 2) + θ + ϑ`.
  The step need not start on the exact solution, and the error at the start enters with the
  factor one.
* `stiff_energy_global_error`: for `N` steps on an arbitrary grid,
  `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (γₙ √(hₙ / 2) + θₙ + ϑₙ)`.

## Remarks on the hypotheses

* The forcing `g` is an arbitrary function of time. The exact solution is a solution in the
  sense of `ODESolution` on every step, so `g` may jump at the grid points.
* Only the Galerkin step, the augmentation and the truncation of the step predicate are used.
  The K-step and the L-step matter through the numbers `γₙ` and `θₙ` alone: these measure how
  well the Galerkin space of step `n` approximates the exact solution, in the energy and in the
  norm. No bound for `γₙ`, `θₙ` in terms of the data is proved here. In particular the file
  does not show that the global error is small for a forcing of bounded variation.
* For the step of `StiffCouplingExample` the bound holds with `γ = 0` and is attained for every
  stiffness `λ` (the first `example` at the end of the file), while the coupling numbers of that
  step grow like `λ`.
* Against the exact solution `decaySol λ` of the same field, which starts at `Y₀ + E₂₂` and
  decays like `e^{-λ t}` in the stiff direction outside the Galerkin space, the hypotheses hold
  with `γ = √λ`, so the energy term is not zero (the second `example`).

## Relation to the literature

Error bounds for low-rank splitting integrators applied to stiff equations with a symmetric
dissipative operator are in [OstermannPiazzolaWalach2019]; they treat the stiff part exactly.
The step considered here is the unsplit Galerkin step of [CerutiKuschLubich2022]. Low-rank
integrators for stiff problems are discussed in [CarrelVandereycken2023, §2.3].
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a symmetric dissipative operator `𝓛`, `⟪w, 𝓛 (w + η)⟫ ≤ -⟪𝓛 η, η⟫ / 4`: the
dissipation of `w` absorbs the coupling with `η` up to a quarter of the energy of `η`. -/
lemma inner_apply_add_le_of_symm_dissipative {𝓛 : E →L[ℝ] E}
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (w η : E) :
    ⟪w, 𝓛 (w + η)⟫ ≤ -⟪𝓛 η, η⟫ / 4 := by
  have h := hdiss (w + (1 / 2 : ℝ) • η)
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h
  have h1 : ⟪𝓛 w, η⟫ = ⟪w, 𝓛 η⟫ := hsym w η
  have h2 : ⟪𝓛 η, w⟫ = ⟪w, 𝓛 η⟫ := real_inner_comm _ _
  have h3 : ⟪𝓛 w, w⟫ = ⟪w, 𝓛 w⟫ := real_inner_comm _ _
  rw [map_add, inner_add_right]
  rw [h1, h2, h3] at h
  linarith

/-- **Energy comparison for the Galerkin equation of a stiff field.** Let `F(t, x) = 𝓛 x + g(t)`
with a symmetric dissipative operator `𝓛`, and let `P` be an orthogonal projector. If
`Y' = P F(t, Y)` in the range of `P`, `A` is an exact solution, and the part of `A` outside the
range of `P` has energy `-⟪𝓛 η, η⟫ ≤ γ`, `η = A - P A`, on the interval, then

`‖P A(t) - Y(t)‖² ≤ ‖P A(a) - Y(a)‖² + (γ / 2) (t - a)`.

Neither the norm of `𝓛` nor a coupling number of `𝓛` with `P` enters. -/
theorem stiff_galerkin_energy_compare {F : ℝ → E → E} {g : ℝ → E} {𝓛 P : E →L[ℝ] E} {γ : ℝ}
    {A Y : ℝ → E} {a b : ℝ} (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (hP : IsOrthProj P)
    (hA : ODESolution F A a b) (hY : ODESolution (fun t x => P (F t x)) Y a b)
    (hYP : ∀ t ∈ Ico a b, P (Y t) = Y t)
    (hγ : ∀ t ∈ Ico a b, -⟪𝓛 (A t - P (A t)), A t - P (A t)⟫ ≤ γ) :
    ∀ t ∈ Icc a b, ‖P (A t) - Y t‖ ^ 2 ≤ ‖P (A a) - Y a‖ ^ 2 + γ / 2 * (t - a) := by
  have hcont : ContinuousOn (fun s => ‖P (A s) - Y s‖ ^ 2) (Icc a b) :=
    (((P.continuous.comp_continuousOn hA.cont).sub hY.cont).norm).pow 2
  have hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => ‖P (A s) - Y s‖ ^ 2)
      (2 * ⟪P (A t) - Y t, P (F t (A t)) - P (F t (Y t))⟫) (Ici t) t := fun t ht =>
    ((P.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)).sub (hY.deriv t ht)).norm_sq
  have hB : ∀ t : ℝ, HasDerivAt (fun s => ‖P (A a) - Y a‖ ^ 2 + γ / 2 * (s - a)) (γ / 2) t := by
    intro t
    have h0 := ((hasDerivAt_id t).sub_const a).const_mul (γ / 2)
    simpa using h0.const_add (‖P (A a) - Y a‖ ^ 2)
  have hbound : ∀ t ∈ Ico a b,
      2 * ⟪P (A t) - Y t, P (F t (A t)) - P (F t (Y t))⟫ ≤ γ / 2 := by
    intro t ht
    have hw : P (P (A t) - Y t) = P (A t) - Y t := by
      rw [map_sub, hP.idem, hYP t ht]
    have e1 : P (F t (A t)) - P (F t (Y t)) = P (𝓛 (A t - Y t)) := by
      rw [hsplit, hsplit]
      simp only [map_sub, map_add]
      abel
    have e2 : A t - Y t = (P (A t) - Y t) + (A t - P (A t)) := by abel
    rw [e1, hP.inner_apply_right_of_mem _ hw, e2]
    have h1 := inner_apply_add_le_of_symm_dissipative hsym hdiss (P (A t) - Y t)
      (A t - P (A t))
    have h2 := hγ t ht
    linarith
  intro t ht
  have h := image_le_of_deriv_right_le_deriv_boundary hcont hderiv
    (B := fun s => ‖P (A a) - Y a‖ ^ 2 + γ / 2 * (s - a)) (B' := fun _ => γ / 2)
    (by simp) (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt) hbound ht
  exact h

/-- **Energy bound for one rank-adaptive BUG step for a stiff field.** Let
`F(t, x) = 𝓛 x + g(t)` with a symmetric dissipative operator `𝓛`, and let `A` be an exact
solution on the step, not necessarily with `A(t₀) = Y₀`. If the part `η = A - P₁ Q₁ A` of the
exact solution outside the Galerkin space has energy `-⟪𝓛 η, η⟫ ≤ γ²` on the step and norm
`‖η(t₁)‖ ≤ θ` at its end, then

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + γ √((t₁ - t₀) / 2) + θ + ϑ`

with the truncation tolerance `ϑ` of the step. -/
theorem IsRankAdaptiveBUGStep.stiff_energy_error {F : ℝ → E → E} {g : ℝ → E}
    {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ γ θ : ℝ} {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ : ℝ}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0) (hle : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁) (hγ0 : 0 ≤ γ)
    (hγ : ∀ t ∈ Ico t₀ t₁,
      -⟪𝓛 (A t - (P₁ * Q₁) (A t)), A t - (P₁ * Q₁) (A t)⟫ ≤ γ ^ 2)
    (hθ : ‖A t₁ - (P₁ * Q₁) (A t₁)‖ ≤ θ) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + γ * √((t₁ - t₀) / 2) + θ + ϑ := by
  have hR := hs.galerkinProj
  have hmem : ∀ t ∈ Icc t₀ t₁, (P₁ * Q₁) (YS t) = YS t := hs.mem_range
  have h1 := stiff_galerkin_energy_compare hsplit hsym hdiss hR hA hs.sSol'
    (fun t ht => hmem t (Ico_subset_Icc_self ht)) hγ t₁ ⟨hle, le_rfl⟩
  have hh : 0 ≤ (t₁ - t₀) / 2 := by linarith
  have hsq : √((t₁ - t₀) / 2) ^ 2 = (t₁ - t₀) / 2 := Real.sq_sqrt hh
  have hr0 : 0 ≤ √((t₁ - t₀) / 2) := Real.sqrt_nonneg _
  have h0 : ‖(P₁ * Q₁) (A t₀) - YS t₀‖ ≤ ‖Y₀ - A t₀‖ := by
    have e : (P₁ * Q₁) (A t₀) - YS t₀ = (P₁ * Q₁) (A t₀ - Y₀) := by
      rw [map_sub, hs.start_eq]
      congr 1
      exact hs.galerkin_fix.symm
    rw [e, norm_sub_rev Y₀]
    exact hR.norm_le _
  have hw : ‖(P₁ * Q₁) (A t₁) - YS t₁‖ ≤ ‖Y₀ - A t₀‖ + γ * √((t₁ - t₀) / 2) := by
    by_contra hc
    rw [not_le] at hc
    have hn0 := norm_nonneg (Y₀ - A t₀)
    have hn1 := norm_nonneg ((P₁ * Q₁) (A t₀) - YS t₀)
    have hp : 0 ≤ γ * √((t₁ - t₀) / 2) := mul_nonneg hγ0 hr0
    have h2 : ‖(P₁ * Q₁) (A t₀) - YS t₀‖ ^ 2 ≤ ‖Y₀ - A t₀‖ ^ 2 := by
      nlinarith
    have h3 : (‖Y₀ - A t₀‖ + γ * √((t₁ - t₀) / 2)) ^ 2
        < ‖(P₁ * Q₁) (A t₁) - YS t₁‖ ^ 2 := by
      nlinarith
    have h4 : (γ * √((t₁ - t₀) / 2)) ^ 2 = γ ^ 2 / 2 * (t₁ - t₀) := by
      rw [mul_pow, hsq]
      ring
    nlinarith [mul_nonneg hn0 hp]
  have e : Y₁ - A t₁ = (Y₁ - YS t₁) - ((P₁ * Q₁) (A t₁) - YS t₁)
      - (A t₁ - (P₁ * Q₁) (A t₁)) := by abel
  rw [e]
  have h5 := _root_.norm_sub_le ((Y₁ - YS t₁) - ((P₁ * Q₁) (A t₁) - YS t₁))
    (A t₁ - (P₁ * Q₁) (A t₁))
  have h6 := _root_.norm_sub_le (Y₁ - YS t₁) ((P₁ * Q₁) (A t₁) - YS t₁)
  have h7 := hs.trunc
  linarith

/-- **Global energy bound for the rank-adaptive BUG integrator for a stiff field.** Let
`F(t, x) = 𝓛 x + g(t)` with a symmetric dissipative operator `𝓛` and let `A` be an exact
solution on every step of a grid `τ₀ ≤ τ₁ ≤ … ≤ τ_N`. If in step `n` the part
`η = A - P̂ₙ Q̂ₙ A` of the exact solution outside the Galerkin space has energy
`-⟪𝓛 η, η⟫ ≤ γₙ²` on the step and norm at most `θₙ` at its end, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (γₙ √((τₙ₊₁ - τₙ) / 2) + θₙ + ϑₙ)`.

The errors of the steps add up without an amplification factor, and the stiff operator enters
through the energies `γₙ²` only. -/
theorem stiff_energy_global_error {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε : ℝ}
    {ϑ γ θ : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1))) (hγ0 : ∀ n < N, 0 ≤ γ n)
    (hγ : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)),
      -⟪𝓛 (A t - (Pa n * Qa n) (A t)), A t - (Pa n * Qa n) (A t)⟫ ≤ γ n ^ 2)
    (hθ : ∀ n < N, ‖A (τ (n + 1)) - (Pa n * Qa n) (A (τ (n + 1)))‖ ≤ θ n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (γ n * √((τ (n + 1) - τ n) / 2) + θ n + ϑ n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : N < N + 1 := Nat.lt_succ_self N
    have h1 := ih (fun n hn => hstep n (hn.trans hN)) (fun n hn => hτ n (hn.trans hN))
      (fun n hn => hA n (hn.trans hN)) (fun n hn => hγ0 n (hn.trans hN))
      (fun n hn => hγ n (hn.trans hN)) (fun n hn => hθ n (hn.trans hN))
    have h2 := (hstep N hN).stiff_energy_error hsplit hsym hdiss (hτ N hN) (hA N hN)
      (hγ0 N hN) (hγ N hN) (hθ N hN)
    rw [Finset.sum_range_succ]
    linarith

namespace StiffCouplingExample

open scoped Matrix LeanDLRA.Frobenius

/-- The stiff operator of the example is symmetric. -/
lemma stiffOp_symm (lam : ℝ) (x y : Matrix (Fin 2) (Fin 3) ℝ) :
    ⟪stiffOp lam x, y⟫ = ⟪x, stiffOp lam y⟫ := by
  change ⟪x * (lam • N₁), y⟫ = ⟪x, y * (lam • N₁)⟫
  rw [Frobenius.inner_def, Frobenius.inner_def]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, N₁]
  ring

/-- The stiff operator of the example is dissipative for `λ ≥ 0`. -/
lemma stiffOp_dissipative {lam : ℝ} (hlam : 0 ≤ lam) (x : Matrix (Fin 2) (Fin 3) ℝ) :
    ⟪stiffOp lam x, x⟫ ≤ 0 := by
  change ⟪x * (lam • N₁), x⟫ ≤ 0
  rw [Matrix.mul_smul, real_inner_smul_left, inner_mul_N₁]
  nlinarith [mul_nonneg hlam (mul_self_nonneg (x 0 1)),
    mul_nonneg hlam (mul_self_nonneg (x 1 1))]

/-- Non-vacuity of `IsRankAdaptiveBUGStep.stiff_energy_error` with nonzero data: for the step
`step` of the example, every stiffness `λ ≥ 0` and every `h ≥ 0`, the hypotheses hold with
`γ = 0` (the part of the exact solution outside the Galerkin space is `t (D - W)`, in the kernel
of the stiff operator), `θ = 4 h` and `ϑ = 0`. By `error_eq` the left-hand side equals `4 h`:
the bound is attained, for every `λ`. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 ≤ h) :
    ‖(Y₀ + h • W) - (Y₀ + h • D)‖
      ≤ ‖Y₀ - (Y₀ + (0 : ℝ) • D)‖ + 0 * √((h - 0) / 2) + 4 * h + 0 := by
  have hη : ∀ t : ℝ, (Y₀ + t • D) - (leftProj U₀ * rightProj Va :
      Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ) (Y₀ + t • D) = t • (D - W) := by
    intro t
    change (Y₀ + t • D) - U₀ * U₀ᵀ * ((Y₀ + t • D) * (Va * Vaᵀ)) = t • (D - W)
    rw [Matrix.add_mul, Matrix.smul_mul, Y₀_mul_Va, D_mul_Va, Matrix.mul_add, Matrix.mul_smul,
      U₀_mul_Y₀, U₀_mul_D, smul_sub]
    abel
  refine (step lam h).stiff_energy_error (g := fun _ => D - Y₀ * (lam • N₁))
    (𝓛 := stiffOp lam) (A := fun t => Y₀ + t • D) (fun _ _ => rfl) (stiffOp_symm lam)
    (stiffOp_dissipative hlam) hh (exactSol lam h) le_rfl (fun t _ => ?_) ?_
  · have e : stiffOp lam (t • (D - W)) = 0 := by
      change (t • (D - W)) * (lam • N₁) = 0
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, D_mul_N₁, W_mul_N₁, sub_zero,
        smul_zero, smul_zero]
    rw [hη, e, inner_zero_left]
    norm_num
  · rw [hη, norm_smul, norm_D_sub_W, Real.norm_of_nonneg hh]
    linarith

/-- The unit matrix `E₂₂` in the stiff column, outside the Galerkin space of `step`. -/
def E₂₂ : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; 0, 1, 0]

/-- The exact solution `A(t) = Y₀ + t D + e^{-λ t} E₂₂` of the field of the example, which starts
off the start value of `step` and decays in the stiff direction. -/
noncomputable def decaySol (lam t : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  Y₀ + t • D + Real.exp (-(lam * t)) • E₂₂

private lemma E₂₂_mul_N₁ : E₂₂ * N₁ = -E₂₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, E₂₂, N₁]

private lemma U₀_transpose_mul_E₂₂ : U₀ᵀ * E₂₂ = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, U₀, E₂₂]

private lemma norm_E₂₂ : ‖E₂₂‖ = 1 := by
  have h1 : ‖E₂₂‖ ^ 2 = 1 ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [E₂₂, Fin.sum_univ_two, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg E₂₂), h1]
  exact Real.sqrt_sq (by norm_num)

/-- `decaySol lam` solves `Y' = Y (λ N₁) + (D - Y₀ (λ N₁))`. -/
theorem odeSolution_decaySol (lam h : ℝ) : ODESolution (field lam) (decaySol lam) 0 h := by
  have hd : ∀ t, HasDerivAt (decaySol lam) (D + (-lam * Real.exp (-(lam * t))) • E₂₂) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(lam * t))) (-lam * Real.exp (-(lam * t))) t :=
      ((hasDerivAt_id t).const_mul lam).neg.exp.congr_deriv
        (by simp only [Pi.neg_apply, id_eq]; ring)
    have h2 := (((hasDerivAt_id t).smul_const D).const_add Y₀).add (h1.smul_const E₂₂)
    rw [one_smul] at h2
    exact h2
  refine ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => ?_⟩
  convert (hd t).hasDerivWithinAt using 1
  change decaySol lam t * (lam • N₁) + (D - Y₀ * (lam • N₁)) = _
  rw [decaySol]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, D_mul_N₁, E₂₂_mul_N₁, smul_zero,
    add_zero]
  module

/-- **Non-vacuity of `IsRankAdaptiveBUGStep.stiff_energy_error` with `γ > 0`.** For the step
`step` of the example, every stiffness `λ ≥ 0` and every `h ≥ 0`, against the exact solution
`decaySol λ`, which starts at `Y₀ + E₂₂` and has the component `e^{-λ t} E₂₂` in the stiff
direction outside the Galerkin space: the hypotheses hold with the energy
`-⟪𝓛 η, η⟫ = λ e^{-2 λ t} ≤ λ = γ²`, `θ = 4 h + 1` and `ϑ = 0`. -/
example {lam h : ℝ} (hlam : 0 ≤ lam) (hh : 0 ≤ h) :
    ‖(Y₀ + h • W) - decaySol lam h‖
      ≤ ‖Y₀ - decaySol lam 0‖ + √lam * √((h - 0) / 2) + (4 * h + 1) + 0 := by
  have hE : U₀ * U₀ᵀ * (E₂₂ * (Va * Vaᵀ)) = 0 := by
    rw [Matrix.mul_assoc U₀, ← Matrix.mul_assoc U₀ᵀ, U₀_transpose_mul_E₂₂, Matrix.zero_mul,
      Matrix.mul_zero]
  have hη : ∀ t : ℝ, decaySol lam t - (leftProj U₀ * rightProj Va :
      Matrix (Fin 2) (Fin 3) ℝ →L[ℝ] Matrix (Fin 2) (Fin 3) ℝ) (decaySol lam t) =
      t • (D - W) + Real.exp (-(lam * t)) • E₂₂ := by
    intro t
    change decaySol lam t - U₀ * U₀ᵀ * (decaySol lam t * (Va * Vaᵀ)) = _
    rw [decaySol, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Y₀_mul_Va,
      D_mul_Va, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, U₀_mul_Y₀,
      U₀_mul_D, hE, smul_zero, add_zero, smul_sub]
    abel
  refine (step lam h).stiff_energy_error (g := fun _ => D - Y₀ * (lam • N₁))
    (𝓛 := stiffOp lam) (A := decaySol lam) (fun _ _ => rfl) (stiffOp_symm lam)
    (stiffOp_dissipative hlam) hh (odeSolution_decaySol lam h) (Real.sqrt_nonneg _)
    (fun t ht => ?_) ?_
  · rw [hη]
    change -⟪(t • (D - W) + Real.exp (-(lam * t)) • E₂₂) * (lam • N₁),
      t • (D - W) + Real.exp (-(lam * t)) • E₂₂⟫ ≤ √lam ^ 2
    rw [Matrix.mul_smul, real_inner_smul_left, inner_mul_N₁, Real.sq_sqrt hlam]
    have he0 : 0 ≤ Real.exp (-(lam * t)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(lam * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hlam ht.1))
    simp [D, W, E₂₂]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul he1 he1 he0 zero_le_one) hlam]
  · rw [hη]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_D_sub_W, norm_E₂₂, Real.norm_of_nonneg hh,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_one]
    have : Real.exp (-(lam * h)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hlam hh))
    linarith

/-- The start error of the previous example is `‖Y₀ - (Y₀ + E₂₂)‖ = 1`. -/
example (lam : ℝ) : ‖Y₀ - decaySol lam 0‖ = 1 := by
  rw [decaySol, zero_smul, add_zero, mul_zero, neg_zero, Real.exp_zero, one_smul,
    sub_add_cancel_left, norm_neg, norm_E₂₂]

end StiffCouplingExample

end LeanDLRA
