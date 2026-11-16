import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.EulerBUG
import LeanDLRA.Stability.Energy

/-!
# Projected preconditioned descent and the global error of projected gradient iterations

Statements for the discrete iterations of dynamical low-rank training on an abstract real inner
product space `E` with a loss `ℒ` whose gradient `g` is `β`-Lipschitz, in the conventions of
`Training/Descent.lean`: loss descent of projected preconditioned (Adam-type) steps, and the
distance of a projected stochastic gradient iteration to the full gradient flow.

## Main results

### OP-TR-17: projected preconditioned (Adam-type) steps

* `loss_projPrecondStep_le`: for an orthogonal projector `Π` and any preconditioner `M` with
  `dmin ‖v‖² ≤ ⟪M v, v⟫` and `‖M v‖ ≤ dmax ‖v‖` (no symmetry, no commutation with `Π`), the
  project–precondition–project step `x - h Π M Π ∇ℒ(x)` satisfies
  `ℒ ≤ ℒ(x) - h (dmin - β h dmax² / 2) ‖Π ∇ℒ(x)‖²`.  This is the one-step target of OP-TR-17
  (low-rank Adam of [SchotthoferKleinKusch2025, Alg. 2], with the second moment as a diagonal
  preconditioner in `[dmin, dmax]`).
* `exists_projGrad_sq_le_of_projPrecond` (min-rate `O(1/n)`) and
  `frequently_projGrad_sq_lt_of_projPrecond` (`liminf = 0` under Robbins–Monro step sizes) for
  the iteration with step-dependent projectors and preconditioners.
* `exists_precondThenProj_ascent`: the order matters; precondition-then-project `Π M ∇ℒ` with a
  symmetric positive definite `M` can be an ascent direction for every step size.

### OP-HO-14: robust error bounds for the executed iterations

* `projectedGradient_global_error`: the projected stochastic gradient iteration with tangent
  capture defect `ε`, gradient noise `σ` and truncation `ϑ` tracks the full gradient flow,
  `‖W_n - W(t_n)‖ ≤ e^{β T} (‖W_0 - W(t_0)‖ + T (β B λ / 2 + ε + σ) + n ϑ)`; for `n λ ≤ T` the
  last term is `≤ T ϑ / λ`.  This is the bound `e^{βT}(c ε + c λ + c ϑ / λ)` of
  [SchotthoferEtAl2025, Thm. 3], [KuschSchotthoferWalter2026, Thm. 5.6] and
  [SavostianovaEtAl2023, Thm. 1], now for the discrete iteration, with the factor `e^{βT}` explicit,
  and with the non-vanishing noise term `T σ` for stochastic gradients.
-/

open Set Finset MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace LeanDLRA.GradientFlowConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### OP-TR-17: projected preconditioned steps -/

section Precond

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- The inner product of the gradient with the project–precondition–project direction is
`⟪Π ∇ℒ, M Π ∇ℒ⟫`, hence at least `dmin ‖Π ∇ℒ‖²`. -/
lemma inner_projPrecond_ge {P M : E →L[ℝ] E} (hP : IsOrthProj P) {dmin : ℝ}
    (hmin : ∀ v, dmin * ‖v‖ ^ 2 ≤ ⟪M v, v⟫) (v : E) :
    dmin * ‖P v‖ ^ 2 ≤ ⟪v, P (M (P v))⟫ := by
  rw [real_inner_comm, hP.symm, real_inner_comm]
  rw [real_inner_comm]
  exact hmin (P v)

/-- The project–precondition–project direction is bounded by `dmax ‖Π ∇ℒ‖`. -/
lemma norm_projPrecond_le {P M : E →L[ℝ] E} (hP : IsOrthProj P) {dmax : ℝ}
    (hmax : ∀ v, ‖M v‖ ≤ dmax * ‖v‖) (v : E) : ‖P (M (P v))‖ ≤ dmax * ‖P v‖ :=
  (hP.norm_le _).trans (hmax _)

/-- **Project–precondition–project is a descent step** (OP-TR-17; low-rank Adam,
[SchotthoferKleinKusch2025, Alg. 2], and momentum aligned with the low-rank basis,
[RahamimEtAl2024], Sec. 7). For an orthogonal projector `Π` and a (not necessarily symmetric, not
necessarily commuting) preconditioner `M` with `dmin ‖v‖² ≤ ⟪M v, v⟫` and `‖M v‖ ≤ dmax ‖v‖`, the
step `x - h Π M Π ∇ℒ(x)` satisfies `ℒ ≤ ℒ(x) - h (dmin - β h dmax² / 2) ‖Π ∇ℒ(x)‖²`. For an
entrywise preconditioner `D ∘ ·` with entries in `[dmin, dmax]`, `0 ≤ dmin`, both hypotheses hold.
-/
theorem loss_projPrecondStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P M : E →L[ℝ] E}
    (hP : IsOrthProj P) {dmin dmax : ℝ} (hmin : ∀ v, dmin * ‖v‖ ^ 2 ≤ ⟪M v, v⟫)
    (hmax : ∀ v, ‖M v‖ ≤ dmax * ‖v‖) {h : ℝ} (hh : 0 ≤ h) (x : E) :
    ℒ (x - h • P (M (P (g x)))) ≤ ℒ x - h * (dmin - β * h * dmax ^ 2 / 2) * ‖P (g x)‖ ^ 2 := by
  have hd := descent_lemma hℒ hg x (x - h • P (M (P (g x))))
  have e1 : x - h • P (M (P (g x))) - x = -(h • P (M (P (g x)))) := by abel
  rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_of_nonneg hh,
    mul_pow] at hd
  have h1 := inner_projPrecond_ge hP hmin (g x)
  have h2 := norm_projPrecond_le hP hmax (g x)
  have h3 : ‖P (M (P (g x)))‖ ^ 2 ≤ dmax ^ 2 * ‖P (g x)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : β / 2 * (h ^ 2 * ‖P (M (P (g x)))‖ ^ 2) ≤
      β / 2 * (h ^ 2 * (dmax ^ 2 * ‖P (g x)‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg h)) (by positivity)
  have h5 : h * (dmin * ‖P (g x)‖ ^ 2) ≤ h * ⟪g x, P (M (P (g x)))⟫ :=
    mul_le_mul_of_nonneg_left h1 hh
  nlinarith

/-- **Convergence of projected preconditioned (Adam-type) low-rank training** (OP-TR-17):
with step-dependent projectors `Π_k` and preconditioners `M_k` with uniform bounds, the iteration
`x_{k+1} = x_k - h Π_k M_k Π_k ∇ℒ(x_k)` satisfies
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ_inf) / (n h (dmin - β h dmax² / 2))`. -/
theorem exists_projGrad_sq_le_of_projPrecond (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P M : ℕ → E →L[ℝ] E}
    (hP : ∀ k, IsOrthProj (P k)) {dmin dmax : ℝ} (hmin : ∀ k v, dmin * ‖v‖ ^ 2 ≤ ⟪M k v, v⟫)
    (hmax : ∀ k v, ‖M k v‖ ≤ dmax * ‖v‖) {h ℒinf : ℝ} (hh : 0 < h)
    (hc : 0 < dmin - β * h * dmax ^ 2 / 2) {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = x k - h • P k (M k (P k (g (x k)))))
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) / (n * h * (dmin - β * h * dmax ^ 2 / 2)) := by
  set c := h * (dmin - β * h * dmax ^ 2 / 2) with hcdef
  have hc' : 0 < c := mul_pos hh hc
  have hsum : c * ∑ k ∈ range n, ‖P k (g (x k))‖ ^ 2 ≤ ℒ (x 0) - ℒinf + n * 0 := by
    have hs := LeanDLRA.sum_le_of_le_sub_add (u := fun k => ℒ (x k))
      (a := fun k => c * ‖P k (g (x k))‖ ^ 2) (e := fun _ => 0)
      (fun k => by
        have := loss_projPrecondStep_le hℒ hg hβ (hP k) (hmin k) (hmax k) hh.le (x k)
        rw [← hx k] at this
        simp only [hcdef]
        linarith) n
    rw [← mul_sum, sum_const_zero] at hs
    have := hinf n
    linarith
  obtain ⟨k, hk, hle⟩ := LeanDLRA.exists_le_of_mul_sum_le hc' hn hsum
  refine ⟨k, hk, ?_⟩
  simpa [hcdef, mul_assoc] using hle

/-- **Robbins–Monro convergence of projected preconditioned steps** (OP-TR-17, liminf analogue
of `LeanDLRA.frequently_projGrad_sq_lt`): with learning rates `h_k ≥ 0`, `β h_k dmax² ≤ dmin`,
`∑ h_k = ∞` and the loss bounded below, `liminf_k ‖Π_k ∇ℒ(x_k)‖² = 0`. -/
theorem frequently_projGrad_sq_lt_of_projPrecond (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P M : ℕ → E →L[ℝ] E}
    (hP : ∀ k, IsOrthProj (P k)) {dmin dmax : ℝ} (hdmin : 0 < dmin)
    (hmin : ∀ k v, dmin * ‖v‖ ^ 2 ≤ ⟪M k v, v⟫) (hmax : ∀ k v, ‖M k v‖ ≤ dmax * ‖v‖)
    {h : ℕ → ℝ} {ℒinf : ℝ} (hh0 : ∀ k, 0 ≤ h k) (hh : ∀ k, β * h k * dmax ^ 2 ≤ dmin)
    (hdiv : ¬ Summable h) {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = x k - h k • P k (M k (P k (g (x k)))))
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖P k (g (x k))‖ ^ 2 < ε := by
  have hw : ∀ k, 0 ≤ h k * (dmin / 2) := fun k => mul_nonneg (hh0 k) (by positivity)
  have hwdiv : ¬ Summable fun k => h k * (dmin / 2) := by
    intro hs
    apply hdiv
    have e : h = fun k => h k * (dmin / 2) * (2 / dmin) := by
      funext k; field_simp
    rw [e]
    exact hs.mul_right _
  refine LeanDLRA.exists_lt_of_sum_mul_le hw (fun k => sq_nonneg _) hwdiv
    (C := ℒ (x 0) - ℒinf) (fun n => ?_) hε N
  have hs := LeanDLRA.sum_le_of_le_sub_add (u := fun k => ℒ (x k))
    (a := fun k => h k * (dmin / 2) * ‖P k (g (x k))‖ ^ 2) (e := fun _ => 0)
    (fun k => by
      have := loss_projPrecondStep_le hℒ hg hβ (hP k) (hmin k) (hmax k) (hh0 k) (x k)
      rw [← hx k] at this
      have h1 : h k * (dmin / 2) * ‖P k (g (x k))‖ ^ 2 ≤
          h k * (dmin - β * h k * dmax ^ 2 / 2) * ‖P k (g (x k))‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (hh0 k)
        linarith [hh k]
      linarith) n
  rw [sum_const_zero] at hs
  have := hinf n
  linarith

end Precond

section PrecondExample

open LeanDLRA.EnergyExamples

/-- The symmetric positive definite matrix `[[1, 2], [2, 5]]` as an operator on `ℝ²`. -/
noncomputable def precondM : E2 →L[ℝ] E2 :=
  (innerSL ℝ (e 0) + (2 : ℝ) • innerSL ℝ (e 1)).smulRight (e 0) +
    ((2 : ℝ) • innerSL ℝ (e 0) + (5 : ℝ) • innerSL ℝ (e 1)).smulRight (e 1)

lemma inner_e_left (i : Fin 2) (v : E2) : ⟪e i, v⟫ = v i := by
  simp [e, EuclideanSpace.inner_single_left]

lemma precondM_inner (v w : E2) :
    ⟪precondM v, w⟫ = (v 0 + 2 * v 1) * w 0 + (2 * v 0 + 5 * v 1) * w 1 := by
  simp [precondM, inner_add_left, real_inner_smul_left, inner_e_left]

lemma coord_ne_zero_of_ne_zero {v : E2} (hv : v ≠ 0) : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hv
  ext i; fin_cases i <;> simp [h.1, h.2]

/-- **Precondition-then-project can ascend** (OP-TR-17, OP-TR-29).  In `ℝ²` take
`Π = e₁e₁ᵀ`, `M = [[1, 2], [2, 5]]` (symmetric positive definite) and `c = e₁ - e₂`: then
`Π c ≠ 0` but `⟪c, Π M c⟫ = -1 < 0`, so the step `x - h Π M c` increases the linear loss
`⟪c, ·⟫` for every `h > 0`, whereas the project–precondition–project step never does
(`loss_projPrecondStep_le`). -/
theorem exists_precondThenProj_ascent :
    ∃ (P M : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (c : EuclideanSpace ℝ (Fin 2)),
      IsOrthProj P ∧ (∀ v w, ⟪M v, w⟫ = ⟪v, M w⟫) ∧ (∀ v, v ≠ 0 → 0 < ⟪M v, v⟫) ∧
        P c ≠ 0 ∧ ∀ x, ∀ h : ℝ, 0 < h → ⟪c, x⟫ < ⟪c, x - h • P (M c)⟫ := by
  have he00 : (e 0 : E2) 0 = 1 := by simp [e]
  have he01 : (e 0 : E2) 1 = 0 := by simp [e]
  have he10 : (e 1 : E2) 0 = 0 := by simp [e]
  have he11 : (e 1 : E2) 1 = 1 := by simp [e]
  refine ⟨lineProj 0, precondM, e 0 - e 1, isOrthProj_lineProj 0, fun v w => ?_, fun v hv => ?_,
    ?_, fun x h hh => ?_⟩
  · rw [precondM_inner, real_inner_comm, precondM_inner]; ring
  · rw [precondM_inner]
    rcases coord_ne_zero_of_ne_zero hv with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (v 0 + 2 * v 1), sq_nonneg (v 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (v 0 + 2 * v 1), sq_nonneg (v 1)]
  · intro h
    have := congrArg (fun v : E2 => v 0) h
    simp [lineProj_apply, inner_e_left, he00, he10] at this
  · have key : ⟪e 0 - e 1, lineProj 0 (precondM (e 0 - e 1))⟫ = -1 := by
      rw [← (isOrthProj_lineProj 0).symm, real_inner_comm, precondM_inner, lineProj_apply,
        inner_e_left]
      simp [he00, he01, he10, he11]
      norm_num
    rw [inner_sub_right, inner_smul_right, key]
    linarith

end PrecondExample

/-! ### OP-HO-14: robust global error bounds for the executed iterations -/

section GlobalError

/-- **Robust global error of the executed projected (stochastic) gradient iteration**
(OP-HO-14; DLRT [SavostianovaEtAl2023] Thm 1, GeoLoRA [SchotthoferEtAl2025] Thm 3, augmented
backward-corrected PSI [KuschSchotthoferWalter2026] Thm 5.6, federated DLRT [SchotthoferLaiu2024]
Thm 5). The iteration `W_{n+1} ≈ W_n - λ Π_n g_n` with truncation
`‖W_{n+1} - (W_n - λ Π_n g_n)‖ ≤ ϑ`, gradient estimate `‖g_n - ∇ℒ(W_n)‖ ≤ σ` and tangent capture
defect `‖(1 - Π_n) ∇ℒ(W_n)‖ ≤ ε` (the augmented projector absorbs the tangent gradient, so `ε`
bounds the normal component, `LeanDLRA.norm_apply_le_of_absorbs`) tracks the gradient flow
`W' = -∇ℒ(W)`: `‖W_n - W(t_n)‖ ≤ e^{β T} (‖W_0 - W(t_0)‖ + T (β B λ / 2 + ε + σ) + n ϑ)` for
`n λ ≤ T`. Since `n ≤ T / λ`, this is `e^{βT}(δ + c ε + c λ + c σ + c ϑ / λ)`, the deterministic
bound announced in the papers, but with the factor `e^{βT}` explicit (the papers' claim of constants
independent of `T` is not justified) and with the stochastic term `T σ`, which does not vanish as
`λ → 0`. Compared with `LeanDLRA.projectedGradient_global_error`, the hypotheses `0 ≤ ε` and `0 ≤ σ`
are added: without them the statement is false for `N = 0` (take `ε = -T⁻¹ (1 + δ)`); for `N > 0`
they follow from `hε`, `hσ`. -/
theorem projectedGradient_global_error {G : E → E} {β B ε σ ϑ lr t₀ : ℝ}
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hB : ∀ x, ‖G x‖ ≤ B) (hlr : 0 ≤ lr)
    (hε0 : 0 ≤ ε) (hσ0 : 0 ≤ σ)
    {N : ℕ} {A : ℝ → E} (hA : ODESolution (fun _ x => -G x) A t₀ (t₀ + N * lr))
    {W g : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution (fun _ x => -G x) (Φ n) (t₀ + n * lr) (t₀ + (n + 1) * lr))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * lr) = W n) {Pr : ℕ → E →L[ℝ] E}
    (hPr : ∀ n, IsOrthProj (Pr n)) (hε : ∀ n < N, ‖(1 - Pr n) (G (W n))‖ ≤ ε)
    (hσ : ∀ n < N, ‖g n - G (W n)‖ ≤ σ)
    (hstep : ∀ n < N, ‖W (n + 1) - (W n - lr • Pr n (g n))‖ ≤ ϑ) {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * lr ≤ T → ‖W n - A (t₀ + n * lr)‖ ≤
      Real.exp (β * T) * (‖W 0 - A t₀‖ + T * (β * B * lr / 2 + ε + σ) + n * ϑ) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : E) => -G x) β := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hG x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : E) => -G x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set c : ℝ := β * B * lr / 2 + ε + σ with hc
  have hc0 : 0 ≤ c := by positivity
  have hloc : ∀ n < N, ‖W (n + 1) - Φ n (t₀ + (n + 1) * lr)‖ ≤ ϑ + lr * c := by
    intro n hn
    have hdef := euler_defect_le hF hβ hBF (t₀ := t₀ + n * lr) (t₁ := t₀ + (n + 1) * lr)
      (h := lr) (Lt := 0) (by ring) hlr (hΦ n hn) (fun _ _ => by simp)
    rw [hΦ₀ n hn, norm_sub_rev] at hdef
    have hmid : ‖(W n - lr • Pr n (g n)) - (W n + lr • -G (W n))‖ ≤ lr * (ε + σ) := by
      have e1 : (W n - lr • Pr n (g n)) - (W n + lr • -G (W n)) =
          lr • ((1 - Pr n) (G (W n)) + Pr n (G (W n) - g n)) := by
        have e0 : (1 - Pr n) (G (W n)) = G (W n) - Pr n (G (W n)) := rfl
        rw [e0, map_sub, smul_add, smul_sub, smul_sub, smul_neg]
        abel
      rw [e1, norm_smul, Real.norm_of_nonneg hlr]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hε n hn) ?_)) hlr
      exact ((hPr n).norm_le _).trans (by rw [norm_sub_rev]; exact hσ n hn)
    have t1 := norm_sub_le_norm_sub_add_norm_sub (W (n + 1)) (W n - lr • Pr n (g n))
      (Φ n (t₀ + (n + 1) * lr))
    have t2 := norm_sub_le_norm_sub_add_norm_sub (W n - lr • Pr n (g n)) (W n + lr • -G (W n))
      (Φ n (t₀ + (n + 1) * lr))
    have t3 := hstep n hn
    have t4 : (β * B + 0) * lr ^ 2 / 2 = lr * (β * B * lr / 2) := by ring
    rw [hc]
    linarith
  intro n hn hT
  have h1 := lady_windermere hF hβ hlr hA hΦ hΦ₀ hloc n hn
  have hnl : 0 ≤ (n : ℝ) * lr := mul_nonneg (Nat.cast_nonneg n) hlr
  have hnϑ : 0 ≤ (n : ℝ) * ϑ := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg n)
        ((norm_nonneg _).trans (hstep 0 (lt_of_lt_of_le hpos hn)))
  have hexp : Real.exp (β * (n * lr)) ≤ Real.exp (β * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hβ)
  have hsum : ‖W 0 - A t₀‖ + n * (ϑ + lr * c) ≤ ‖W 0 - A t₀‖ + T * c + n * ϑ := by
    have : (n : ℝ) * lr * c ≤ T * c := mul_le_mul_of_nonneg_right hT hc0
    nlinarith
  have hsum0 : 0 ≤ ‖W 0 - A t₀‖ + n * (ϑ + lr * c) := by
    have : 0 ≤ (n : ℝ) * lr * c := mul_nonneg hnl hc0
    nlinarith [norm_nonneg (W 0 - A t₀)]
  exact h1.trans (mul_le_mul hexp hsum hsum0 (Real.exp_pos _).le)

end GlobalError

end LeanDLRA.GradientFlowConvergence
