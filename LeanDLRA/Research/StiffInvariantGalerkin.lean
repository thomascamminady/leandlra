import LeanDLRA.Research.StiffOldColumnVariation
import LeanDLRA.Integrators.ProjectorSplitting

/-!
# Stiff problems: the rank-adaptive BUG integrator when the Galerkin space is invariant

For a stiff equation `Y' = 𝓛 Y + f(t, Y)` with a dissipative operator `𝓛` this file bounds the
error of the rank-adaptive BUG integrator when the space of the Galerkin step, the range of
`P₁ Q₁` with the augmented projectors `P₁`, `Q₁`, is invariant under `𝓛`. For matrices and
`𝓛 Y = M Y + Y N` this is the case when the augmented column space is invariant under `M` and
the augmented row space is invariant under `N`; for `𝓛 Y = Y N` only the row space matters.
The bounds contain neither the norm of `𝓛` nor a coupling number, no quantity of the exact
solution after the start, and no quantity of the K-step or the L-step.

The reason is that on an invariant Galerkin space the Galerkin step is the exact flow of the
equation in which the remaining part `f` is replaced by its projection. The only defect of the
step is therefore the part of `f` outside the Galerkin space, along the Galerkin trajectory.

## Main results

* `IsRankAdaptiveBUGStep.swap`: the step predicate is symmetric under the exchange of the left
  and the right projectors, together with the K-step and the L-step.
* `IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin`: if `f` satisfies a one-sided
  Lipschitz condition with constant `ℓ` along the Galerkin trajectory and the exact solution,
  and `‖f(t, Ŷ(t)) - P₁ Q₁ f(t, Ŷ(t))‖ ≤ η` on the step, then
  `‖Y₁ - A(t₁)‖ ≤ gronwallBound ‖Y₀ - A(t₀)‖ ℓ η (t₁ - t₀) + ϑ`.
* `IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin_forcing`: for `f(t, Y) = g(t)`,
  `‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + η (t₁ - t₀) + ϑ` with `‖g - P₁ Q₁ g‖ ≤ η`.
* `IsRankAdaptiveBUGStep.norm_forcing_sub_augRight_le`,
  `IsRankAdaptiveBUGStep.norm_forcing_sub_galerkin_le`: for a symmetric `𝓛` that commutes with
  the augmented projectors and a forcing `c` that is constant on the step, `‖c - Q₁ c‖ ≤ ε` and
  `‖c - P₁ Q₁ c‖ ≤ 2 ε` with the bound `ε` for the normal parts.
* `IsRankAdaptiveBUGStep.stiff_error_of_invariant_const`: for such a step,
  `‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ`.
* `stiff_global_error_of_invariant_galerkin`: for `N` steps on an arbitrary grid and an
  arbitrary forcing, `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ηₙ (τₙ₊₁ - τₙ) + ϑₙ)`.
* `stiff_global_error_of_invariant_piecewise_const`: for a forcing that is constant on the
  steps, `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + 2 ε (τ_N - τ₀) + ∑ₙ ϑₙ`.

## Remarks on the hypotheses

* The invariance is a hypothesis on the augmented bases of every step. It is not shown that the
  integrator produces invariant bases. For `𝓛 Y = Y N` it holds, for instance, if the rows of
  the starting value and of the forcing seen by the L-step lie in an invariant subspace of `N`
  whose dimension is the rank of the approximation. Without it the bounds of
  `StiffOldColumnGalerkin` contain the difference between the Galerkin result and the result of
  the L-step, which is not bounded here.
* In the last bound the forcing may jump at every grid point. Neither its variation nor the
  columns lost by the truncation enter, in contrast to
  `stiff_global_error_of_piecewise_const_uniform`.
* In the first bound the operator `𝓛` need not be symmetric and the projectors need not commute
  with it; only the range of `P₁ Q₁` has to be invariant. The part `f` may depend on the state.
  No bound for `η` in terms of `ε` is proved for a part `f` that depends on the state.
* For the example at the end of the file (`StiffInvariantExample`) the error after the time
  `t` is `|b| t` for every stiffness, and the last bound is `2 |b| t`.

## Relation to the literature

The integrator is the one of [CerutiKuschLubich2022]; its error bound there depends on the
Lipschitz constant of the whole right-hand side.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsRankAdaptiveBUGStep

variable {F f : ℝ → E → E} {g : ℝ → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ η ℓ : ℝ}
  {A YK YL YS : ℝ → E} {Y₀ Y₁ c : E} {t₀ t₁ : ℝ}

/-- A rank-adaptive BUG step remains one when the left and the right projectors are exchanged
together with the K-step and the L-step. For matrices this is the step for the transposed
equation. -/
theorem swap (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    IsRankAdaptiveBUGStep F ε ϑ Q₀ P₀ Q₁ P₁ t₀ t₁ Y₀ YL YK YS Y₁ :=
  { projP₀ := hs.projQ₀
    projQ₀ := hs.projP₀
    projP₁ := hs.projQ₁
    projQ₁ := hs.projP₁
    comm₁ := fun x => (hs.comm₁ x).symm
    kSol := hs.lSol
    kStart := hs.lStart
    kCap := hs.lCap
    kNormal := hs.lNormal
    lSol := hs.kSol
    lStart := hs.kStart
    lCap := hs.kCap
    lNormal := hs.kNormal
    sSol := ⟨hs.sSol.cont, fun t ht => by
      have h := hs.sSol.deriv t ht
      change HasDerivWithinAt YS (P₁ (Q₁ (F t (YS t)))) (Ici t) t at h
      rw [hs.comm₁] at h
      exact h⟩
    sStart := by
      rw [← hs.comm₁]
      exact hs.sStart
    augP := hs.augQ
    augQ := hs.augP
    trunc := hs.trunc }

/-- **Error of one rank-adaptive BUG step when the Galerkin space is invariant.** Let
`F(t, x) = 𝓛 x + f(t, x)` with a dissipative operator `𝓛` that maps the range of `P₁ Q₁` into
itself, and let `f` satisfy a one-sided Lipschitz condition with constant `ℓ` along the Galerkin
trajectory `Ŷ = YS` and an exact solution `A`, not necessarily with `A(t₀) = Y₀`. If the part
of `f(t, Ŷ(t))` outside the Galerkin space is at most `η` on the step, then

`‖Y₁ - A(t₁)‖ ≤ gronwallBound ‖Y₀ - A(t₀)‖ ℓ η (t₁ - t₀) + ϑ`.

The operator `𝓛` enters only through its sign and the invariance. -/
theorem stiff_error_of_invariant_galerkin
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + f t x) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hf : ∀ t ∈ Ico t₀ t₁, ⟪f t (YS t) - f t (A t), YS t - A t⟫ ≤ ℓ * ‖YS t - A t‖ ^ 2)
    (hinv : ∀ x, P₁ (Q₁ x) = x → P₁ (Q₁ (𝓛 x)) = 𝓛 x) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁)
    (hη : ∀ t ∈ Ico t₀ t₁, ‖f t (YS t) - P₁ (Q₁ (f t (YS t)))‖ ≤ η) :
    ‖Y₁ - A t₁‖ ≤ gronwallBound ‖Y₀ - A t₀‖ ℓ η (t₁ - t₀) + ϑ := by
  have hmem : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t)) = YS t := hs.mem_range
  have h := norm_sub_le_gronwallBound_of_inner_le (F := F) (ℓ := ℓ) (y := YS) (z := A)
    (u := fun t => P₁ (Q₁ (F t (YS t)))) (w := fun t => F t (A t)) (ηy := η) (ηz := 0)
    (δ := ‖Y₀ - A t₀‖) (a := t₀) (b := t₁)
    (fun t ht => by
      have e : F t (YS t) - F t (A t) = 𝓛 (YS t - A t) + (f t (YS t) - f t (A t)) := by
        rw [hsplit, hsplit, map_sub]
        abel
      rw [e, inner_add_left]
      linarith [hdiss (YS t - A t), hf t ht])
    hs.sSol.cont (fun t ht => hs.sSol.deriv t ht)
    (fun t ht => by
      have e : P₁ (Q₁ (F t (YS t))) - F t (YS t)
          = -(f t (YS t) - P₁ (Q₁ (f t (YS t)))) := by
        rw [hsplit, map_add, map_add, hinv _ (hmem t (Ico_subset_Icc_self ht))]
        abel
      rw [e, norm_neg]
      exact hη t ht)
    hA.cont (fun t ht => hA.deriv t ht)
    (fun t _ => by
      rw [sub_self, norm_zero])
    (le_of_eq (by rw [hs.start_eq])) t₁ ⟨hle, le_rfl⟩
  rw [add_zero] at h
  have e : Y₁ - A t₁ = (Y₁ - YS t₁) + (YS t₁ - A t₁) := by abel
  rw [e]
  have h6 := norm_add_le (Y₁ - YS t₁) (YS t₁ - A t₁)
  have h7 := hs.trunc
  linarith

/-- **Error of one rank-adaptive BUG step when the Galerkin space is invariant, forced linear
equation.** Let `F(t, x) = 𝓛 x + g(t)` with a dissipative operator `𝓛` that maps the range of
`P₁ Q₁` into itself. If the part of the forcing outside the Galerkin space is at most `η` on the
step, then for an exact solution `A`

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + η (t₁ - t₀) + ϑ`.

The error at the start enters with the factor one. -/
theorem stiff_error_of_invariant_galerkin_forcing
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hinv : ∀ x, P₁ (Q₁ x) = x → P₁ (Q₁ (𝓛 x)) = 𝓛 x) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) (hη : ∀ t ∈ Ico t₀ t₁, ‖g t - P₁ (Q₁ (g t))‖ ≤ η) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + η * (t₁ - t₀) + ϑ := by
  have h := hs.stiff_error_of_invariant_galerkin (f := fun t _ => g t) (ℓ := 0) hsplit hdiss
    (fun t _ => by simp) hinv hle hA hη
  rw [gronwallBound_K0] at h
  exact h

/-- **A constant forcing outside the augmented row space is a normal part.** Let
`F(t, x) = 𝓛 x + c` with a symmetric operator `𝓛` and a forcing `c` that is constant on the
step, and let the augmented right projector `Q₁` commute with `𝓛` and with the old left
projector `P₀`. Then the part of the forcing outside the range of `Q₁` is at most the bound `ε`
for the normal part at the result of the L-step. -/
theorem norm_forcing_sub_augRight_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + c) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hQ𝓛 : ∀ x, Q₁ (𝓛 x) = 𝓛 (Q₁ x)) (hQP : ∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) (hlt : t₀ < t₁) :
    ‖c - Q₁ c‖ ≤ ε :=
  hs.swap.norm_forcing_sub_augLeft_le hsplit hsym hQ𝓛 hQP hlt

/-- **A constant forcing outside the Galerkin space consists of normal parts.** Let
`F(t, x) = 𝓛 x + c` with a symmetric operator `𝓛` and a forcing `c` that is constant on the
step. If the augmented projectors commute with `𝓛`, `P₁` commutes with `Q₀` and `Q₁` commutes
with `P₀`, then `‖c - P₁ Q₁ c‖ ≤ 2 ε`. -/
theorem norm_forcing_sub_galerkin_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t x, F t x = 𝓛 x + c) (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫)
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hQ𝓛 : ∀ x, Q₁ (𝓛 x) = 𝓛 (Q₁ x))
    (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hQP : ∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) (hlt : t₀ < t₁) :
    ‖c - P₁ (Q₁ c)‖ ≤ 2 * ε := by
  have h1 := hs.norm_forcing_sub_augLeft_le hsplit hsym hP𝓛 hPQ hlt
  have h2 := hs.norm_forcing_sub_augRight_le hsplit hsym hQ𝓛 hQP hlt
  have e : c - P₁ (Q₁ c) = (c - P₁ c) + P₁ (c - Q₁ c) := by
    rw [map_sub]
    abel
  rw [e]
  have h3 := norm_add_le (c - P₁ c) (P₁ (c - Q₁ c))
  have h4 := hs.projP₁.norm_le (c - Q₁ c)
  linarith

/-- **Error of one rank-adaptive BUG step with invariant augmented bases and a forcing that is
constant on the step.** Let `F(t, x) = 𝓛 x + c` on `[t₀, t₁)` with a symmetric dissipative
operator `𝓛` that commutes with the augmented projectors `P₁` and `Q₁`, and let `P₁` commute
with `Q₀` and `Q₁` with `P₀`. Then for an exact solution `A` on the step

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ`

with the bound `ε` for the normal parts and the truncation tolerance `ϑ`. -/
theorem stiff_error_of_invariant_const
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + c)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hQ𝓛 : ∀ x, Q₁ (𝓛 x) = 𝓛 (Q₁ x))
    (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hQP : ∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) (hlt : t₀ < t₁)
    (hA : ODESolution F A t₀ t₁) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + 2 * ε * (t₁ - t₀) + ϑ := by
  have hs' := hs.of_field_eqOn (F' := fun _ x => 𝓛 x + c) hlt hsplit (fun _ _ _ => rfl)
  have hA' : ODESolution (fun _ x => 𝓛 x + c) A t₀ t₁ :=
    ⟨hA.cont, fun t ht => by
      have h := hA.deriv t ht
      rw [hsplit t ht] at h
      exact h⟩
  exact hs'.stiff_error_of_invariant_galerkin_forcing (g := fun _ => c) (fun _ _ => rfl) hdiss
    (fun x hx => by rw [hQ𝓛, hP𝓛, hx]) hlt.le hA'
    (fun _ _ => hs'.norm_forcing_sub_galerkin_le (fun _ _ => rfl) hsym hP𝓛 hQ𝓛 hPQ hQP hlt)

end IsRankAdaptiveBUGStep

/-- **Global error of the rank-adaptive BUG integrator when the Galerkin spaces are invariant.**
Let `F(t, x) = 𝓛 x + g(t)` with a dissipative operator `𝓛` and let `A` be an exact solution on
every step of a grid `τ₀ ≤ τ₁ ≤ … ≤ τ_N`. If in every step `𝓛` maps the range of `P̂ₙ Q̂ₙ` into
itself and the part of the forcing outside this range is at most `ηₙ`, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + ∑ₙ (ηₙ (τₙ₊₁ - τₙ) + ϑₙ)`.

The right-hand side contains neither the norm of `𝓛` nor the exact solution after `τ₀`. -/
theorem stiff_global_error_of_invariant_galerkin {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E}
    {ε : ℝ} {ϑ η : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hinv : ∀ n < N, ∀ x, Pa n (Qa n x) = x → Pa n (Qa n (𝓛 x)) = 𝓛 x)
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1)))
    (hη : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), ‖g t - Pa n (Qa n (g t))‖ ≤ η n) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖
      + ∑ n ∈ Finset.range N, (η n * (τ (n + 1) - τ n) + ϑ n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : N < N + 1 := Nat.lt_succ_self N
    have h1 := ih (fun n hn => hstep n (hn.trans hN)) (fun n hn => hτ n (hn.trans hN))
      (fun n hn => hinv n (hn.trans hN)) (fun n hn => hA n (hn.trans hN))
      (fun n hn => hη n (hn.trans hN))
    have h2 := (hstep N hN).stiff_error_of_invariant_galerkin_forcing hsplit hdiss (hinv N hN)
      (hτ N hN) (hA N hN) (hη N hN)
    rw [Finset.sum_range_succ]
    linarith

/-- **Global error with invariant augmented bases for a forcing that is constant on the
steps.** Let `F(t, x) = 𝓛 x + g(t)` with a symmetric dissipative operator `𝓛` and `g = cₙ` on
step `n` of a grid `τ₀ < τ₁ < … < τ_N`, and let `A` be an exact solution on every step. If in
every step the augmented projectors `P̂ₙ`, `Q̂ₙ` commute with `𝓛`, `P̂ₙ` commutes with `Qₙ` and
`Q̂ₙ` with `Pₙ`, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + 2 ε (τ_N - τ₀) + ∑ₙ ϑₙ`

with the bound `ε` for the normal parts and the truncation tolerances `ϑₙ`. The bound contains
neither the norm of `𝓛` nor the jumps of the forcing. -/
theorem stiff_global_error_of_invariant_piecewise_const {F : ℝ → E → E} {g : ℝ → E}
    {𝓛 : E →L[ℝ] E} {ε : ℝ} {ϑ : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E}
    {Y c : ℕ → E} {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hconst : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), g t = c n)
    (hsym : ∀ x y, ⟪𝓛 x, y⟫ = ⟪x, 𝓛 y⟫) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hPa𝓛 : ∀ n < N, ∀ x, Pa n (𝓛 x) = 𝓛 (Pa n x))
    (hQa𝓛 : ∀ n < N, ∀ x, Qa n (𝓛 x) = 𝓛 (Qa n x))
    (hPaQ : ∀ n < N, ∀ x, Pa n (Q n x) = Q n (Pa n x))
    (hQaP : ∀ n < N, ∀ x, Qa n (P n x) = P n (Qa n x))
    (hA : ∀ n < N, ODESolution F A (τ n) (τ (n + 1))) :
    ‖Y N - A (τ N)‖ ≤ ‖Y 0 - A (τ 0)‖ + 2 * ε * (τ N - τ 0)
      + ∑ n ∈ Finset.range N, ϑ n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : N < N + 1 := Nat.lt_succ_self N
    have h1 := ih (fun n hn => hstep n (hn.trans hN)) (fun n hn => hτ n (hn.trans hN))
      (fun n hn => hconst n (hn.trans hN)) (fun n hn => hPa𝓛 n (hn.trans hN))
      (fun n hn => hQa𝓛 n (hn.trans hN)) (fun n hn => hPaQ n (hn.trans hN))
      (fun n hn => hQaP n (hn.trans hN)) (fun n hn => hA n (hn.trans hN))
    have h2 := (hstep N hN).stiff_error_of_invariant_const (c := c N)
      (fun t ht x => by rw [hsplit, hconst N hN t ht]) hsym hdiss (hPa𝓛 N hN) (hQa𝓛 N hN)
      (hPaQ N hN) (hQaP N hN) (hτ N hN) (hA N hN)
    rw [Finset.sum_range_succ]
    linarith

/-! ### A stiff decay on the complex plane -/

namespace StiffInvariantExample

open KSLExample

/-- The stiff operator `z ↦ -λ (re z)` of the example, with the projector `reProj` onto the
real axis: decay with the rate `λ` on the real axis, no action on the imaginary axis. -/
noncomputable def stiffOp (lam : ℝ) : ℂ →L[ℝ] ℂ := (-lam) • reProj

/-- The field `z ↦ -λ (re z) + b i` of the example, with a constant forcing normal to the real
axis. -/
noncomputable def field (lam b : ℝ) (_ : ℝ) (z : ℂ) : ℂ := stiffOp lam z + (b : ℂ) * Complex.I

/-- The numerical solution of the example: the stiff decay `e^{-λ t}` on the real axis. -/
noncomputable def decay (lam t : ℝ) : ℂ := (Real.exp (-lam * t) : ℝ)

/-- The exact solution `e^{-λ t} + b t i` of the example. -/
noncomputable def exact (lam b t : ℝ) : ℂ := decay lam t + ((b * t : ℝ) : ℂ) * Complex.I

private lemma inner_eq (x y : ℂ) : ⟪x, y⟫ = x.re * y.re + x.im * y.im := by
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma stiffOp_apply (lam : ℝ) (z : ℂ) : stiffOp lam z = ((-lam * z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [stiffOp, reProj]

/-- The stiff operator of the example is symmetric. -/
theorem stiffOp_symm (lam : ℝ) (x y : ℂ) : ⟪stiffOp lam x, y⟫ = ⟪x, stiffOp lam y⟫ := by
  simp only [inner_eq, stiffOp_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The stiff operator of the example is dissipative for `λ ≥ 0`. -/
theorem stiffOp_dissipative {lam : ℝ} (hlam : 0 ≤ lam) (z : ℂ) : ⟪stiffOp lam z, z⟫ ≤ 0 := by
  simp only [inner_eq, stiffOp_apply, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [mul_nonneg hlam (mul_self_nonneg z.re)]

/-- The projector onto the real axis commutes with the stiff operator. -/
theorem reProj_stiffOp (lam : ℝ) (x : ℂ) : reProj (stiffOp lam x) = stiffOp lam (reProj x) := by
  simp only [reProj_apply, stiffOp_apply, Complex.ofReal_re]

private lemma reProj_field (lam b t : ℝ) (z : ℂ) : reProj (field lam b t z) = stiffOp lam z := by
  apply Complex.ext <;> simp [field, reProj_apply, stiffOp_apply]

private lemma reProj_decay (lam t : ℝ) : reProj (decay lam t) = decay lam t := by
  rw [reProj_apply, decay, Complex.ofReal_re]

private lemma normal_field (lam b t : ℝ) (z : ℂ) :
    (1 - reProj) ((1 - reProj) (field lam b t z)) = (b : ℂ) * Complex.I := by
  have h : ∀ w : ℂ, (1 - reProj) w = (w.im : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [reProj_apply]
  rw [h, h]
  simp [field, stiffOp_apply]

private lemma hasDerivAt_decay (lam t : ℝ) :
    HasDerivAt (decay lam) (stiffOp lam (decay lam t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * t) * (-lam * 1)) t :=
    ((hasDerivAt_id t).const_mul (-lam)).exp
  have h2 : HasDerivAt (decay lam) ((Real.exp (-lam * t) * (-lam * 1) : ℝ) : ℂ) t :=
    h1.ofReal_comp
  have e : stiffOp lam (decay lam t) = ((Real.exp (-lam * t) * (-lam * 1) : ℝ) : ℂ) := by
    rw [stiffOp_apply, decay, Complex.ofReal_re]
    congr 1
    ring
  rw [e]
  exact h2

private lemma stiffOp_exact (lam b t : ℝ) :
    stiffOp lam (exact lam b t) = stiffOp lam (decay lam t) := by
  have h : (exact lam b t).re = (decay lam t).re := by simp [exact]
  rw [stiffOp_apply, stiffOp_apply, h]

private lemma hasDerivAt_exact (lam b t : ℝ) :
    HasDerivAt (exact lam b) (field lam b t (exact lam b t)) t := by
  have h := (hasDerivAt_decay lam t).add
    ((((hasDerivAt_id t).const_mul b).ofReal_comp).mul_const Complex.I)
  rw [mul_one] at h
  change HasDerivAt (exact lam b) (stiffOp lam (exact lam b t) + (b : ℂ) * Complex.I) t
  rw [stiffOp_exact]
  exact h

/-- The exact solution of the example solves `z' = -λ (re z) + b i` on every interval. -/
theorem odeSolution_exact (lam b t₀ t₁ : ℝ) :
    ODESolution (field lam b) (exact lam b) t₀ t₁ :=
  ⟨(continuous_iff_continuousAt.2 fun t => (hasDerivAt_exact lam b t).continuousAt).continuousOn,
    fun t _ => (hasDerivAt_exact lam b t).hasDerivWithinAt⟩

/-- The stiff decay is a step of the rank-adaptive BUG integrator on every interval, with all
four projectors equal to the projector onto the real axis, the bound `|b|` for the normal parts
and no truncation. -/
theorem step (lam b t₀ t₁ : ℝ) :
    IsRankAdaptiveBUGStep (field lam b) |b| 0 reProj reProj reProj reProj t₀ t₁ (decay lam t₀)
      (decay lam) (decay lam) (decay lam) (decay lam t₁) :=
  have hc : ContinuousOn (decay lam) (Icc t₀ t₁) :=
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_decay lam t).continuousAt).continuousOn
  have hd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (decay lam)
      (reProj (field lam b t (decay lam t))) (Ici t) t := fun t _ => by
    rw [reProj_field]
    exact (hasDerivAt_decay lam t).hasDerivWithinAt
  have hn : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - reProj) ((1 - reProj) (field lam b t (decay lam t₁)))‖ ≤ |b| := fun t _ => by
    rw [normal_field, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  { projP₀ := isOrthProj_reProj
    projQ₀ := isOrthProj_reProj
    projP₁ := isOrthProj_reProj
    projQ₁ := isOrthProj_reProj
    comm₁ := fun _ => rfl
    kSol := ⟨hc, hd⟩
    kStart := rfl
    kCap := reProj_decay lam t₁
    kNormal := hn
    lSol := ⟨hc, hd⟩
    lStart := rfl
    lCap := reProj_decay lam t₁
    lNormal := hn
    sSol := ⟨hc, fun t ht => by
      change HasDerivWithinAt (decay lam) (reProj (reProj (field lam b t (decay lam t))))
        (Ici t) t
      rw [isOrthProj_reProj.idem]
      exact hd t ht⟩
    sStart := by rw [reProj_decay, reProj_decay]
    augP := reProj_decay lam t₀
    augQ := reProj_decay lam t₀
    trunc := by rw [sub_self, norm_zero] }

/-- The error of the example at the time `t` is `|b| |t|`, for every stiffness. -/
theorem norm_decay_sub_exact (lam b t : ℝ) : ‖decay lam t - exact lam b t‖ = |b| * |t| := by
  rw [exact, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul]

/-- Non-vacuity of `IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin` and of
`IsRankAdaptiveBUGStep.stiff_error_of_invariant_galerkin_forcing` with nonzero data: one step
of the example, for every stiffness `λ ≥ 0`, every `b` and every `h > 0`, with the forcing
`b i` outside the Galerkin space (`η = |b|`). The bound `|b| h` is the error of the step
(`norm_decay_sub_exact`). -/
example {lam b h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖decay lam h - exact lam b h‖ ≤ |b| * h := by
  have hη : ‖(b : ℂ) * Complex.I - reProj (reProj ((b : ℂ) * Complex.I))‖ ≤ |b| := by
    have e : reProj (reProj ((b : ℂ) * Complex.I)) = 0 := by simp [reProj_apply]
    rw [e, sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hinv : ∀ x, reProj (reProj x) = x → reProj (reProj (stiffOp lam x)) = stiffOp lam x :=
    fun x hx => by rw [reProj_stiffOp, reProj_stiffOp, hx]
  have h1 := (step lam b 0 h).stiff_error_of_invariant_galerkin (A := exact lam b)
    (f := fun _ _ => (b : ℂ) * Complex.I) (𝓛 := stiffOp lam) (ℓ := 0) (η := |b|)
    (fun _ _ => rfl) (stiffOp_dissipative hlam) (fun t _ => by simp) hinv hh.le
    (odeSolution_exact lam b 0 h) (fun _ _ => hη)
  have h2 := (step lam b 0 h).stiff_error_of_invariant_galerkin_forcing (A := exact lam b)
    (g := fun _ => (b : ℂ) * Complex.I) (𝓛 := stiffOp lam) (η := |b|)
    (fun _ _ => rfl) (stiffOp_dissipative hlam) hinv hh.le
    (odeSolution_exact lam b 0 h) (fun _ _ => hη)
  have e0 : decay lam 0 - exact lam b 0 = 0 := by simp [exact]
  rw [gronwallBound_K0] at h1
  simp only [e0, norm_zero, zero_add, sub_zero, add_zero] at h1 h2
  exact h2

/-- Non-vacuity of `stiff_global_error_of_invariant_piecewise_const` (and with it of
`IsRankAdaptiveBUGStep.stiff_error_of_invariant_const`, `norm_forcing_sub_galerkin_le` and
`norm_forcing_sub_augRight_le`) with nonzero data: two steps of the example, for every
stiffness `λ ≥ 0`, every `b` and every `h > 0`, with `ε = |b|`. The bound reads
`‖Y₂ - A(2h)‖ ≤ 4 |b| h`; by `norm_decay_sub_exact` the left-hand side equals `2 |b| h`. -/
example {lam b h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖decay lam (2 * h) - exact lam b (2 * h)‖ ≤ 4 * |b| * h := by
  have key := stiff_global_error_of_invariant_piecewise_const (N := 2) (F := field lam b)
    (g := fun _ => (b : ℂ) * Complex.I) (𝓛 := stiffOp lam) (ε := |b|) (ϑ := fun _ => 0)
    (τ := fun n => (n : ℝ) * h) (P := fun _ => reProj) (Q := fun _ => reProj)
    (Pa := fun _ => reProj) (Qa := fun _ => reProj) (Y := fun n => decay lam ((n : ℝ) * h))
    (c := fun _ => (b : ℂ) * Complex.I) (YK := fun _ => decay lam) (YL := fun _ => decay lam)
    (YS := fun _ => decay lam) (A := exact lam b)
    (fun n _ => step lam b _ _)
    (fun n _ => by
      push_cast
      linarith)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) (stiffOp_symm lam) (stiffOp_dissipative hlam)
    (fun _ _ x => reProj_stiffOp lam x) (fun _ _ x => reProj_stiffOp lam x)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => odeSolution_exact lam b _ _)
  have e0 : decay lam 0 - exact lam b 0 = 0 := by simp [exact]
  simp only [Finset.sum_const_zero, add_zero, Nat.cast_zero, Nat.cast_ofNat, zero_mul, sub_zero,
    e0, norm_zero, zero_add] at key
  linarith

/-- Non-vacuity of `IsRankAdaptiveBUGStep.swap`: the exchanged step of the example. -/
example (lam b t₀ t₁ : ℝ) :
    IsRankAdaptiveBUGStep (field lam b) |b| 0 reProj reProj reProj reProj t₀ t₁ (decay lam t₀)
      (decay lam) (decay lam) (decay lam) (decay lam t₁) :=
  IsRankAdaptiveBUGStep.swap (step lam b t₀ t₁)

/-- Non-vacuity of `IsRankAdaptiveBUGStep.norm_forcing_sub_augRight_le` and of
`IsRankAdaptiveBUGStep.norm_forcing_sub_galerkin_le` with nonzero data: for the step of the
example the forcing `b i` has the norm `|b| = ε` and lies outside the real axis. -/
example {lam b h : ℝ} (hh : 0 < h) :
    ‖(b : ℂ) * Complex.I - reProj ((b : ℂ) * Complex.I)‖ ≤ |b|
      ∧ ‖(b : ℂ) * Complex.I - reProj (reProj ((b : ℂ) * Complex.I))‖ ≤ 2 * |b| :=
  ⟨IsRankAdaptiveBUGStep.norm_forcing_sub_augRight_le (step lam b 0 h) (fun _ _ => rfl)
      (stiffOp_symm lam) (reProj_stiffOp lam) (fun _ => rfl) hh,
    IsRankAdaptiveBUGStep.norm_forcing_sub_galerkin_le (step lam b 0 h) (fun _ _ => rfl)
      (stiffOp_symm lam) (reProj_stiffOp lam) (reProj_stiffOp lam) (fun _ => rfl)
      (fun _ => rfl) hh⟩

/-- Non-vacuity of `IsRankAdaptiveBUGStep.stiff_error_of_invariant_const` with nonzero data:
one step of the example, for every stiffness `λ ≥ 0`, every `b` and every `h > 0`. -/
example {lam b h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖decay lam h - exact lam b h‖ ≤ 2 * |b| * h := by
  have h1 := IsRankAdaptiveBUGStep.stiff_error_of_invariant_const (step lam b 0 h)
    (A := exact lam b) (c := (b : ℂ) * Complex.I) (𝓛 := stiffOp lam) (fun _ _ _ => rfl)
    (stiffOp_symm lam) (stiffOp_dissipative hlam) (reProj_stiffOp lam) (reProj_stiffOp lam)
    (fun _ => rfl) (fun _ => rfl) hh (odeSolution_exact lam b 0 h)
  have e0 : decay lam 0 - exact lam b 0 = 0 := by simp [exact]
  simp only [e0, norm_zero, zero_add, sub_zero, add_zero] at h1
  exact h1

/-- Non-vacuity of `stiff_global_error_of_invariant_galerkin` with nonzero data: two steps of
the example with `ηₙ = |b|`, for every stiffness `λ ≥ 0`, every `b` and every `h > 0`. The
bound `2 |b| h` is the error after the two steps (`norm_decay_sub_exact`). -/
example {lam b h : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h) :
    ‖decay lam (2 * h) - exact lam b (2 * h)‖ ≤ 2 * |b| * h := by
  have hη : ‖(b : ℂ) * Complex.I - reProj (reProj ((b : ℂ) * Complex.I))‖ ≤ |b| := by
    have e : reProj (reProj ((b : ℂ) * Complex.I)) = 0 := by simp [reProj_apply]
    rw [e, sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have key := stiff_global_error_of_invariant_galerkin (N := 2) (F := field lam b)
    (g := fun _ => (b : ℂ) * Complex.I) (𝓛 := stiffOp lam) (ε := |b|) (ϑ := fun _ => 0)
    (η := fun _ => |b|) (τ := fun n => (n : ℝ) * h) (P := fun _ => reProj)
    (Q := fun _ => reProj) (Pa := fun _ => reProj) (Qa := fun _ => reProj)
    (Y := fun n => decay lam ((n : ℝ) * h)) (YK := fun _ => decay lam)
    (YL := fun _ => decay lam) (YS := fun _ => decay lam) (A := exact lam b)
    (fun n _ => step lam b _ _)
    (fun n _ => by
      push_cast
      linarith)
    (fun _ _ => rfl) (stiffOp_dissipative hlam)
    (fun _ _ x hx => by rw [reProj_stiffOp, reProj_stiffOp, hx])
    (fun _ _ => odeSolution_exact lam b _ _) (fun _ _ _ _ => hη)
  have e0 : decay lam 0 - exact lam b 0 = 0 := by simp [exact]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_add, Nat.cast_ofNat, zero_mul, zero_add, add_zero, one_mul, sub_zero, e0,
    norm_zero] at key
  linarith

end StiffInvariantExample

end LeanDLRA
