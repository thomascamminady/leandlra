import LeanDLRA.Research.StiffInvariantGalerkin

/-!
# Stiff problems: symmetry of the stiff operator in the invariant-Galerkin bound

`IsRankAdaptiveBUGStep.stiff_error_of_invariant_const` bounds one step of the rank-adaptive BUG
integrator for `Y' = 𝓛 Y + c` with a symmetric dissipative operator `𝓛` that commutes with the
augmented projectors `P₁`, `Q₁`, and a forcing `c` that is constant on the step:

  `‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ`.

Symmetry is used to show that the K-step captures the part `(1 - P₁) Q₀ c` of the forcing
exactly (`IsRankAdaptiveBUGStep.augLeft_apply_right_forcing`, an energy argument). This file
answers whether dissipativity is enough.

* It is not: `StiffSkewExample.exists_isRankAdaptiveBUGStep_lt_norm_sub` is a step for a
  dissipative (skew) operator on `1 × 3` matrices that satisfies all other hypotheses of
  `stiff_error_of_invariant_const`, with `ε = ϑ = 0`, whose error exceeds the bound. The K-step
  turns once around and returns to the old row space while the exact solution drifts along the
  kernel of `𝓛`.
* Symmetry can be traded for commutation of `𝓛` with the old projectors `P₀`, `Q₀`:
  `IsRankAdaptiveBUGStep.stiff_error_of_comm` gives the same bound for a dissipative `𝓛` that
  commutes with `P₀`, `Q₀`, `P₁`, `Q₁` and an arbitrary forcing `g(t)`, not necessarily constant
  on the step. The trajectories of the K-step and of the L-step outside the augmented spaces
  return to zero at the end of the step; adding them to the Galerkin trajectory removes the
  parts `(1 - P₁) Q₀ g` and `P₁ (1 - Q₁) P₀ g` of the forcing from its defect, and what remains
  are the two normal parts, each at most `ε`. `stiff_global_error_of_comm` adds up the steps:
  `‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + 2 ε (τ_N - τ₀) + ∑ₙ ϑₙ` for every forcing.

For matrices and `𝓛 Y = M Y + Y N` the projector `Y ↦ U Uᵀ Y` commutes with `𝓛` when the range
of `U` reduces `M` (it is invariant under `M` and `Mᵀ`), and `Y ↦ Y V Vᵀ` commutes with `𝓛` when
the range of `V` reduces `N`.
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {g : ℝ → E} {𝓛 P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε ϑ : ℝ}
  {A YK YL YS : ℝ → E} {Y₀ Y₁ : E} {t₀ t₁ : ℝ}

/-- **Error of one rank-adaptive BUG step for a stiff linear operator that commutes with all
projectors.** Let `F(t, x) = 𝓛 x + g(t)` on the step with a dissipative operator `𝓛`
(`⟪𝓛 x, x⟫ ≤ 0`, not necessarily symmetric) that commutes with the old projectors `P₀`, `Q₀` and
with the augmented projectors `P₁`, `Q₁`, and let `P₁` commute with `Q₀` and `Q₁` with `P₀`. Then
for an exact solution `A` on the step and every forcing `g`

`‖Y₁ - A(t₁)‖ ≤ ‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ`

with the bound `ε` for the normal parts and the truncation tolerance `ϑ`. Compared with
`stiff_error_of_invariant_const`, symmetry of `𝓛` and constancy of the forcing on the step are
replaced by the commutation of `𝓛` with `P₀` and `Q₀`; without either, the bound fails
(`StiffSkewExample.exists_isRankAdaptiveBUGStep_lt_norm_sub`). -/
theorem stiff_error_of_comm
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hsplit : ∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + g t) (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP₀𝓛 : ∀ x, P₀ (𝓛 x) = 𝓛 (P₀ x)) (hQ₀𝓛 : ∀ x, Q₀ (𝓛 x) = 𝓛 (Q₀ x))
    (hP𝓛 : ∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) (hQ𝓛 : ∀ x, Q₁ (𝓛 x) = 𝓛 (Q₁ x))
    (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) (hQP : ∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) (hle : t₀ ≤ t₁)
    (hA : ODESolution F A t₀ t₁) :
    ‖Y₁ - A t₁‖ ≤ ‖Y₀ - A t₀‖ + 2 * ε * (t₁ - t₀) + ϑ := by
  have hP₀ := hs.projP₀
  have hQ₀ := hs.projQ₀
  have hP₁ := hs.projP₁
  have hQ₁ := hs.projQ₁
  have hmem : ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t)) = YS t := hs.mem_range
  -- the two normal parts of the forcing
  have hn₁ : ∀ t ∈ Ico t₀ t₁, ‖(g t - Q₀ (g t)) - P₁ (g t - Q₀ (g t))‖ ≤ ε := by
    intro t ht
    have h := hs.kNormal t (Ico_subset_Icc_self ht)
    have e : (1 - P₁) ((1 - Q₀) (F t (YK t₁))) = (g t - Q₀ (g t)) - P₁ (g t - Q₀ (g t)) := by
      rw [hsplit t ht]
      simp only [sub_apply, one_apply_eq_self, map_sub, map_add, hQ₀𝓛, hP𝓛, hPQ, hs.kCap]
      abel
    rwa [e] at h
  have hn₂ : ∀ t ∈ Ico t₀ t₁, ‖P₁ ((g t - P₀ (g t)) - Q₁ (g t - P₀ (g t)))‖ ≤ ε := by
    intro t ht
    have h := hs.lNormal t (Ico_subset_Icc_self ht)
    have e : (1 - Q₁) ((1 - P₀) (F t (YL t₁))) = (g t - P₀ (g t)) - Q₁ (g t - P₀ (g t)) := by
      rw [hsplit t ht]
      simp only [sub_apply, one_apply_eq_self, map_sub, map_add, hP₀𝓛, hQ𝓛, hQP, hs.lCap]
      abel
    rw [e] at h
    exact (hP₁.norm_le _).trans h
  -- the Galerkin trajectory corrected by the parts of the K-step and the L-step outside the
  -- augmented spaces
  set y : ℝ → E := fun t => YS t + (Q₀ (YK t) - P₁ (Q₀ (YK t)))
    + (P₁ (P₀ (YL t)) - P₁ (Q₁ (P₀ (YL t)))) with hy
  have hyc : ContinuousOn y (Icc t₀ t₁) := by
    have hK := hs.kSol.cont
    have hL := hs.lSol.cont
    have hS := hs.sSol.cont
    exact (hS.add ((Q₀.continuous.comp_continuousOn hK).sub
      (P₁.continuous.comp_continuousOn (Q₀.continuous.comp_continuousOn hK)))).add
      ((P₁.continuous.comp_continuousOn (P₀.continuous.comp_continuousOn hL)).sub
        (P₁.continuous.comp_continuousOn (Q₁.continuous.comp_continuousOn
          (P₀.continuous.comp_continuousOn hL))))
  set u : ℝ → E := fun t => P₁ (Q₁ (F t (YS t)))
    + (Q₀ (Q₀ (F t (YK t))) - P₁ (Q₀ (Q₀ (F t (YK t)))))
    + (P₁ (P₀ (P₀ (F t (YL t)))) - P₁ (Q₁ (P₀ (P₀ (F t (YL t)))))) with hu
  have hyd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt y (u t) (Ici t) t := by
    intro t ht
    have hK := hs.kSol.deriv t ht
    have hL := hs.lSol.deriv t ht
    have hS := hs.sSol.deriv t ht
    have hQK := Q₀.hasFDerivAt.comp_hasDerivWithinAt t hK
    have hPL := P₀.hasFDerivAt.comp_hasDerivWithinAt t hL
    exact (hS.add (hQK.sub (P₁.hasFDerivAt.comp_hasDerivWithinAt t hQK))).add
      ((P₁.hasFDerivAt.comp_hasDerivWithinAt t hPL).sub (P₁.hasFDerivAt.comp_hasDerivWithinAt t
        (Q₁.hasFDerivAt.comp_hasDerivWithinAt t hPL)))
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖u t - F t (y t)‖ ≤ 2 * ε := by
    intro t ht
    have hSt : P₁ (Q₁ (YS t)) = YS t := hmem t (Ico_subset_Icc_self ht)
    have e : u t - F t (y t) = -(((g t - Q₀ (g t)) - P₁ (g t - Q₀ (g t)))
        + P₁ ((g t - P₀ (g t)) - Q₁ (g t - P₀ (g t)))) := by
      simp only [hu, hy, hsplit t ht, map_add, map_sub, hQ₀𝓛, hP₀𝓛, hP𝓛, hQ𝓛, hQ₀.idem,
        hP₀.idem, hSt]
      abel
    rw [e, norm_neg]
    exact (norm_add_le _ _).trans (by linarith [hn₁ t ht, hn₂ t ht])
  have h := norm_sub_le_gronwallBound_of_inner_le (F := F) (ℓ := 0) (y := y) (z := A)
    (u := u) (w := fun t => F t (A t)) (ηy := 2 * ε) (ηz := 0) (δ := ‖Y₀ - A t₀‖)
    (a := t₀) (b := t₁)
    (fun t ht => by
      rw [hsplit t ht, hsplit t ht, zero_mul]
      have e : 𝓛 (y t) + g t - (𝓛 (A t) + g t) = 𝓛 (y t - A t) := by
        rw [map_sub]
        abel
      rw [e]
      exact hdiss _)
    hyc hyd hdef hA.cont (fun t ht => hA.deriv t ht) (fun t _ => by rw [sub_self, norm_zero])
    (le_of_eq (by
      have h0 : y t₀ = Y₀ := by
        simp only [hy, hs.start_eq, hs.kStart, hs.lStart, hPQ, hs.augP, sub_self, add_zero, hQP,
          hs.augQ]
      rw [h0])) t₁ ⟨hle, le_rfl⟩
  rw [add_zero, gronwallBound_K0] at h
  have h1 : y t₁ = YS t₁ := by
    simp only [hy, hPQ, hs.kCap, sub_self, add_zero, hQP, hs.lCap]
  rw [h1] at h
  have e : Y₁ - A t₁ = (Y₁ - YS t₁) + (YS t₁ - A t₁) := by abel
  rw [e]
  have h6 := norm_add_le (Y₁ - YS t₁) (YS t₁ - A t₁)
  have h7 := hs.trunc
  linarith

end IsRankAdaptiveBUGStep

/-- **Global error of the rank-adaptive BUG integrator for a stiff linear operator that commutes
with all projectors.** Let `F(t, x) = 𝓛 x + g(t)` with a dissipative operator `𝓛` and a forcing
`g` that may vary in time arbitrarily, and let `A` be an exact solution on every step of a grid
`τ₀ ≤ τ₁ ≤ … ≤ τ_N`. If in every step `𝓛` commutes with the old projectors `Pₙ`, `Qₙ` and the
augmented projectors `P̂ₙ`, `Q̂ₙ`, `P̂ₙ` commutes with `Qₙ` and `Q̂ₙ` with `Pₙ`, then

`‖Y_N - A(τ_N)‖ ≤ ‖Y₀ - A(τ₀)‖ + 2 ε (τ_N - τ₀) + ∑ₙ ϑₙ`.

The bound contains neither the norm of `𝓛` nor the forcing; compare
`stiff_global_error_of_invariant_piecewise_const`, which needs a symmetric `𝓛` and a forcing
that is constant on the steps, but no commutation with the old projectors. -/
theorem stiff_global_error_of_comm {F : ℝ → E → E} {g : ℝ → E} {𝓛 : E →L[ℝ] E} {ε : ℝ}
    {ϑ : ℕ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS : ℕ → ℝ → E} {A : ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (τ n)
      (τ (n + 1)) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hsplit : ∀ t x, F t x = 𝓛 x + g t)
    (hdiss : ∀ x, ⟪𝓛 x, x⟫ ≤ 0)
    (hP𝓛 : ∀ n < N, ∀ x, P n (𝓛 x) = 𝓛 (P n x)) (hQ𝓛 : ∀ n < N, ∀ x, Q n (𝓛 x) = 𝓛 (Q n x))
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
      (fun n hn => hP𝓛 n (hn.trans hN)) (fun n hn => hQ𝓛 n (hn.trans hN))
      (fun n hn => hPa𝓛 n (hn.trans hN)) (fun n hn => hQa𝓛 n (hn.trans hN))
      (fun n hn => hPaQ n (hn.trans hN)) (fun n hn => hQaP n (hn.trans hN))
      (fun n hn => hA n (hn.trans hN))
    have h2 := (hstep N hN).stiff_error_of_comm (g := g) (fun t _ x => hsplit t x) hdiss
      (hP𝓛 N hN) (hQ𝓛 N hN) (hPa𝓛 N hN) (hQa𝓛 N hN) (hPaQ N hN) (hQaP N hN) (hτ N hN)
      (hA N hN)
    rw [Finset.sum_range_succ]
    linarith

/-! ### Dissipativity alone is not enough -/

namespace StiffSkewExample

open scoped Matrix LeanDLRA.Frobenius

/-- The skew matrix with `x N = (k × xᵀ)ᵀ` for the row vectors `x` and `k = (2, 2, 1)`. -/
def N : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -2; -1, 0, 2; 2, -2, 0]

/-- The old right basis `[e₁, e₂]`. -/
def V₀ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- The forcing `e₁ᵀ`, constant in time. -/
def c : Matrix (Fin 1) (Fin 3) ℝ := !![1, 0, 0]

/-- The row `e₂ᵀ`. -/
def e₂ : Matrix (Fin 1) (Fin 3) ℝ := !![0, 1, 0]

/-- The value of the exact solution at `t = 0`. -/
noncomputable def a : Matrix (Fin 1) (Fin 3) ℝ := !![0, 1 / 9, -(2 / 9)]

/-- The velocity of the exact solution, a multiple of `kᵀ`. -/
noncomputable def w : Matrix (Fin 1) (Fin 3) ℝ := !![4 / 9, 4 / 9, 2 / 9]

/-- The skew operator `Y ↦ Y N` on `1 × 3` matrices: `⟪Y N, Y⟫ = 0`. -/
noncomputable def skewOp : Matrix (Fin 1) (Fin 3) ℝ →L[ℝ] Matrix (Fin 1) (Fin 3) ℝ :=
  Frobenius.rightMulCLM N

/-- The trajectory of the K-step: one turn around the circle of radius `1` through `0` in the
plane of `e₁ᵀ`, `e₂ᵀ`. -/
noncomputable def kstep (t : ℝ) : Matrix (Fin 1) (Fin 3) ℝ := Real.sin t • c + (1 - Real.cos t) • e₂

/-- The exact solution `a + t w`: it drifts along the kernel of the skew operator. -/
noncomputable def exact (t : ℝ) : Matrix (Fin 1) (Fin 3) ℝ := a + t • w

local macro "entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, N, V₀, c, e₂, a, w] <;> try ring))

lemma orthV₀ : V₀ᵀ * V₀ = 1 := by entries

lemma c_mul_V₀ : c * V₀ * V₀ᵀ = c := by entries

lemma kstep_deriv (t : ℝ) :
    Real.cos t • c + Real.sin t • e₂ = (kstep t * N + c) * (V₀ * V₀ᵀ) := by
  unfold kstep
  entries

lemma exact_deriv (t : ℝ) : w = exact t * N + c := by
  unfold exact
  entries

lemma skewOp_dissipative (x : Matrix (Fin 1) (Fin 3) ℝ) : ⟪skewOp x, x⟫ ≤ 0 := by
  refine le_of_eq ?_
  rw [Frobenius.inner_def]
  simp [skewOp, Matrix.mul_apply, Fin.sum_univ_three, N]
  ring

lemma kstep_zero : kstep 0 = 0 := by simp [kstep]

lemma kstep_two_pi : kstep (2 * Real.pi) = 0 := by simp [kstep]

lemma hasDerivAt_kstep (t : ℝ) : HasDerivAt kstep (Real.cos t • c + Real.sin t • e₂) t := by
  have h1 := (Real.hasDerivAt_sin t).smul_const c
  have h2 := ((Real.hasDerivAt_cos t).const_sub 1).smul_const e₂
  exact (h1.add h2).congr_deriv (by rw [neg_neg])

lemma hasDerivAt_exact (t : ℝ) : HasDerivAt exact w t := by
  have h := ((hasDerivAt_id t).smul_const w).const_add a
  rw [one_smul] at h
  exact h

lemma norm_exact_lt : ‖exact 0‖ < ‖exact (2 * Real.pi)‖ := by
  have h0 : ‖exact 0‖ ^ 2 = 5 / 81 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [exact, a, w, Fin.sum_univ_three]
    norm_num
  have h1 : ‖exact (2 * Real.pi)‖ ^ 2 = (5 + 144 * Real.pi ^ 2) / 81 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [exact, a, w, Fin.sum_univ_three]
    ring
  have hπ := Real.pi_pos
  nlinarith [norm_nonneg (exact 0), norm_nonneg (exact (2 * Real.pi))]

/-- **Symmetry cannot be replaced by dissipativity in
`IsRankAdaptiveBUGStep.stiff_error_of_invariant_const`.** On `1 × 3` matrices there are a skew,
hence dissipative, operator `𝓛` (`⟪𝓛 x, x⟫ = 0`), a constant forcing `c`, projectors and a
step of the rank-adaptive BUG integrator with `ε = ϑ = 0` such that all hypotheses of
`stiff_error_of_invariant_const` except the symmetry of `𝓛` hold, and

  `‖Y₀ - A(t₀)‖ + 2 ε (t₁ - t₀) + ϑ < ‖Y₁ - A(t₁)‖`.

Here `Y₀ = Y₁ = 0`, `P₀ = P₁ = 0`, `Q₁ = 1`, `Q₀ = Y ↦ Y V₀ V₀ᵀ` (the plane of `e₁ᵀ`, `e₂ᵀ`),
`𝓛 Y = Y N`, `c = e₁ᵀ` and `[t₀, t₁] = [0, 2π]`. The K-step `YK' = Q₀ (𝓛 YK + c)` turns once
around a circle and returns to `0`, so the forcing in the old row space is not detected, while the
exact solution `A(t) = a + t w` drifts along the kernel of `𝓛`. The operator `𝓛` does not commute
with `Q₀`, as `IsRankAdaptiveBUGStep.stiff_error_of_comm` requires. -/
theorem exists_isRankAdaptiveBUGStep_lt_norm_sub :
    ∃ (F : ℝ → Matrix (Fin 1) (Fin 3) ℝ → Matrix (Fin 1) (Fin 3) ℝ)
      (𝓛 P₀ Q₀ P₁ Q₁ : Matrix (Fin 1) (Fin 3) ℝ →L[ℝ] Matrix (Fin 1) (Fin 3) ℝ)
      (c Y₀ Y₁ : Matrix (Fin 1) (Fin 3) ℝ) (YK YL YS A : ℝ → Matrix (Fin 1) (Fin 3) ℝ)
      (ε ϑ t₀ t₁ : ℝ),
      IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁ ∧
      (∀ t ∈ Ico t₀ t₁, ∀ x, F t x = 𝓛 x + c) ∧ (∀ x, ⟪𝓛 x, x⟫ ≤ 0) ∧
      (∀ x, P₁ (𝓛 x) = 𝓛 (P₁ x)) ∧ (∀ x, Q₁ (𝓛 x) = 𝓛 (Q₁ x)) ∧
      (∀ x, P₁ (Q₀ x) = Q₀ (P₁ x)) ∧ (∀ x, Q₁ (P₀ x) = P₀ (Q₁ x)) ∧ t₀ < t₁ ∧
      ODESolution F A t₀ t₁ ∧ ‖Y₀ - A t₀‖ + 2 * ε * (t₁ - t₀) + ϑ < ‖Y₁ - A t₁‖ := by
  have hQ₀ : IsOrthProj (rightProj V₀ : Matrix (Fin 1) (Fin 3) ℝ →L[ℝ] Matrix (Fin 1) (Fin 3) ℝ) :=
    isOrthProj_rightProj orthV₀
  refine ⟨fun _ x => skewOp x + c, skewOp, 0, rightProj V₀, 0, 1, c, 0, 0, kstep, fun _ => 0,
    fun _ => 0, exact, 0, 0, 0, 2 * Real.pi, ?_, fun _ _ _ => rfl, skewOp_dissipative,
    fun _ => by simp, fun _ => by simp, fun _ => by simp, fun _ => by simp,
    by positivity, ?_, ?_⟩
  · exact
      { projP₀ := IsOrthProj.zero
        projQ₀ := hQ₀
        projP₁ := IsOrthProj.zero
        projQ₁ := IsOrthProj.one
        comm₁ := fun _ => by simp
        kSol := ⟨fun s _ => (hasDerivAt_kstep s).continuousAt.continuousWithinAt, fun s _ => by
          have h := (hasDerivAt_kstep s).hasDerivWithinAt (s := Ici s)
          rw [kstep_deriv] at h
          exact h⟩
        kStart := kstep_zero
        kCap := by simp [kstep_two_pi]
        kNormal := fun _ _ => by simp [kstep_two_pi, c_mul_V₀]
        lSol := ⟨continuousOn_const, fun s _ => by
          simpa using hasDerivWithinAt_const s (Ici s) (0 : Matrix (Fin 1) (Fin 3) ℝ)⟩
        lStart := rfl
        lCap := by simp
        lNormal := fun _ _ => by simp
        sSol := ⟨continuousOn_const, fun s _ => by
          simpa using hasDerivWithinAt_const s (Ici s) (0 : Matrix (Fin 1) (Fin 3) ℝ)⟩
        sStart := by simp
        augP := by simp
        augQ := by simp
        trunc := by simp }
  · refine ⟨fun s _ => (hasDerivAt_exact s).continuousAt.continuousWithinAt, fun s _ => ?_⟩
    have h := (hasDerivAt_exact s).hasDerivWithinAt (s := Ici s)
    rw [exact_deriv s] at h
    simpa [skewOp] using h
  · simpa using norm_exact_lt


/-- The rotation matrix `R` with `x R = (-x₂, x₁)` for the rows `x = (x₁, x₂)`. -/
def R : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The row `(1, 0)`. -/
def f₁ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

/-- The row `(0, 1)`. -/
def f₂ : Matrix (Fin 1) (Fin 2) ℝ := !![0, 1]

/-- The skew operator `Y ↦ Y R` on `1 × 2` matrices. -/
noncomputable def rotOp : Matrix (Fin 1) (Fin 2) ℝ →L[ℝ] Matrix (Fin 1) (Fin 2) ℝ :=
  Frobenius.rightMulCLM R

/-- The unit circle `t ↦ (cos t, sin t)`, a solution of `Y' = Y R`. -/
noncomputable def circ (t : ℝ) : Matrix (Fin 1) (Fin 2) ℝ := Real.cos t • f₁ + Real.sin t • f₂

lemma rotOp_dissipative (x : Matrix (Fin 1) (Fin 2) ℝ) : ⟪rotOp x, x⟫ ≤ 0 := by
  refine le_of_eq ?_
  rw [Frobenius.inner_def]
  simp [rotOp, Matrix.mul_apply, Fin.sum_univ_two, R]
  ring

lemma circ_deriv (t : ℝ) : -Real.sin t • f₁ + Real.cos t • f₂ = circ t * R := by
  unfold circ
  ext i j
  fin_cases i
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, R, f₁, f₂]

lemma hasDerivAt_circ (t : ℝ) : HasDerivAt circ (-Real.sin t • f₁ + Real.cos t • f₂) t :=
  ((Real.hasDerivAt_cos t).smul_const f₁).add ((Real.hasDerivAt_sin t).smul_const f₂)

/-- The field `F(t, x) = x R + (f₁ - t f₁ R)` of the example: `t ↦ t f₁` solves it. -/
private theorem rot_step (t₀ t₁ : ℝ) :
    IsRankAdaptiveBUGStep (fun t x => rotOp x + (f₁ - rotOp (t • f₁))) 0 0 1 1 1 1 t₀ t₁
      (t₀ • f₁) (fun t => t • f₁) (fun t => t • f₁) (fun t => t • f₁) (t₁ • f₁) := by
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t • f₁) f₁ s := fun s => by
    simpa using (hasDerivAt_id s).smul_const f₁
  have hsol : ∀ P Q : Matrix (Fin 1) (Fin 2) ℝ →L[ℝ] Matrix (Fin 1) (Fin 2) ℝ, P = 1 → Q = 1 →
      ODESolution (fun t x => P (Q (rotOp x + (f₁ - rotOp (t • f₁))))) (fun t => t • f₁) t₀ t₁ :=
    fun P Q hP hQ => ⟨fun s _ => (hlin s).continuousAt.continuousWithinAt, fun s _ => by
      subst hP hQ
      simpa using (hlin s).hasDerivWithinAt (s := Ici s)⟩
  exact
    { projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := by simpa using hsol 1 1 rfl rfl
      kStart := rfl
      kCap := by simp
      kNormal := fun _ _ => by simp
      lSol := by simpa using hsol 1 1 rfl rfl
      lStart := rfl
      lCap := by simp
      lNormal := fun _ _ => by simp
      sSol := hsol 1 1 rfl rfl
      sStart := by simp
      augP := by simp
      augQ := by simp
      trunc := by simp }

/-- The exact solution `t f₁ + (cos t, sin t)` of the field of the example. -/
private theorem rot_sol (t₀ t₁ : ℝ) :
    ODESolution (fun t x => rotOp x + (f₁ - rotOp (t • f₁))) (fun t => t • f₁ + circ t) t₀ t₁ := by
  have hlin : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t • f₁) f₁ s := fun s => by
    simpa using (hasDerivAt_id s).smul_const f₁
  refine ⟨fun s _ => ((hlin s).add (hasDerivAt_circ s)).continuousAt.continuousWithinAt,
    fun s _ => ?_⟩
  have h := ((hlin s).add (hasDerivAt_circ s)).hasDerivWithinAt (s := Ici s)
  rw [circ_deriv] at h
  have e : f₁ + circ s * R = rotOp (s • f₁ + circ s) + (f₁ - rotOp (s • f₁)) := by
    rw [map_add]
    change f₁ + circ s * R = rotOp (s • f₁) + circ s * R + (f₁ - rotOp (s • f₁))
    abel
  rw [e] at h
  exact h

/-- **Non-vacuity of `IsRankAdaptiveBUGStep.stiff_error_of_comm`** with a skew operator and a
forcing that is not constant in time: for `𝓛 Y = Y R` on `1 × 2` matrices, the forcing
`g(t) = f₁ - t f₁ R`, all projectors the identity (`ε = ϑ = 0`), the step trajectories
`t ↦ t f₁` on `[0, t₁]` and the exact solution `A(t) = t f₁ + (cos t, sin t)`, the hypotheses
hold. -/
example (t₁ : ℝ) (h01 : 0 ≤ t₁) :
    ‖t₁ • f₁ - (t₁ • f₁ + circ t₁)‖ ≤
      ‖(0 : ℝ) • f₁ - ((0 : ℝ) • f₁ + circ 0)‖ + 2 * 0 * (t₁ - 0) + 0 :=
  (rot_step 0 t₁).stiff_error_of_comm (g := fun t => f₁ - rotOp (t • f₁)) (𝓛 := rotOp)
    (A := fun t => t • f₁ + circ t)
    (fun _ _ _ => rfl) rotOp_dissipative (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) h01 (rot_sol 0 t₁)

/-- **Non-vacuity of `stiff_global_error_of_comm`**: the steps of the previous example on the
grid `τₙ = n`, for every number of steps `N`. -/
example (N : ℕ) :
    ‖(N : ℝ) • f₁ - ((N : ℝ) • f₁ + circ N)‖ ≤
      ‖((0 : ℕ) : ℝ) • f₁ - (((0 : ℕ) : ℝ) • f₁ + circ ((0 : ℕ) : ℝ))‖
        + 2 * 0 * ((N : ℝ) - ((0 : ℕ) : ℝ)) + ∑ _n ∈ Finset.range N, (0 : ℝ) :=
  stiff_global_error_of_comm (F := fun t x => rotOp x + (f₁ - rotOp (t • f₁)))
    (g := fun t => f₁ - rotOp (t • f₁)) (𝓛 := rotOp) (ε := 0) (ϑ := fun _ => 0)
    (τ := fun n => (n : ℝ)) (P := fun _ => 1) (Q := fun _ => 1) (Pa := fun _ => 1)
    (Qa := fun _ => 1) (Y := fun n => (n : ℝ) • f₁) (YK := fun _ t => t • f₁)
    (YL := fun _ t => t • f₁) (YS := fun _ t => t • f₁) (A := fun t => t • f₁ + circ t)
    (fun _ _ => rot_step _ _) (fun n _ => Nat.cast_le.2 n.le_succ) (fun _ _ => rfl)
    rotOp_dissipative (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ => rot_sol _ _)

end StiffSkewExample

end LeanDLRA
