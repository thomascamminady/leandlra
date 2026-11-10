import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Training.Defs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Dynamical low-rank training: loss descent and convergence

Dynamical low-rank training (DLRT) trains the weight matrices `W = U S Vᵀ` of a neural network
directly in low-rank form.  One optimisation step of the rank-adaptive DLRT schemes
(GeoLoRA, Schotthöfer–Zangrando–Ceruti–Tudisco–Kusch, arXiv 2410.18720; augmented
backward-corrected PSI, Kusch–Schotthöfer–Walter, arXiv 2502.03006; federated DLRT,
Schotthöfer–Laiu, arXiv 2406.17887; stabilized DLRT, arXiv 2609.32615) has the abstract form

    x̂₁ = x - h Π ∇ℒ(x),          ‖x₁ - x̂₁‖ ≤ ϑ,

where `Π` is an orthogonal projector (the Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` onto the span of
the augmented bases, the left projector `P_Û`, or the tangent projector `P(W)`), `h` is the
learning rate and the second step is the rank truncation with tolerance `ϑ`.  As in the rest of
the library we work on an arbitrary real inner product space `E` with a loss `ℒ : E → ℝ` whose
gradient `g = ∇ℒ` is `β`-Lipschitz (`β`-smooth loss, Assumption A2 of 2502.03006; the constant is
called `L` in 2406.17887 and 2410.18720).  Gradients are expressed as
`HasFDerivAt ℒ (innerSL ℝ (g x)) x`, which is Mathlib's `HasGradientAt ℒ (g x) x` without the
completeness assumption; `HasGradientAt` versions of the headline results are provided.

## Main results

* `descent_lemma` (**descent lemma**, Lemma 5.7 of 2502.03006 = Lemma 4 of 2406.17887 = Lemma 1
  of 2410.18720, all quoting Hnatiuk et al., Lemma 5.2):
  `ℒ y ≤ ℒ x + ⟪∇ℒ(x), y - x⟫ + β/2 ‖y - x‖²`, and its lower counterpart `descent_lemma_lower`.
* `loss_projGradStep_le` (**loss descent of the projected gradient step**, 2502.03006 Thm 5.8,
  2410.18720 eq. (23)–(25)): `ℒ(x - h Π ∇ℒ(x)) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖²`.
* `loss_truncated_projGradStep_le` (**loss descent guarantee of DLRT**, deterministic form of
  2410.18720 Thm 1 and of 2406.17887 Thm 2 for one client and one local step): after a truncation
  `‖x₁ - x̂₁‖ ≤ ϑ`, with `‖∇ℒ‖ ≤ G` between `x̂₁` and `x₁`,
  `ℒ(x₁) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖² + G ϑ`;
  `loss_truncated_projGradStep_le'` gives the smoothness-only variant `+ ‖∇ℒ(x̂₁)‖ ϑ + β ϑ² / 2`.
* `exists_projGrad_sq_le` (**global convergence to tangent stationarity**, the
  "global loss convergence" statement of 2406.17887 Thm 3, here for one client and one local
  step): for `n` truncated projected gradient steps with step-dependent projectors `Π_k`,
  `min_{k < n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ_inf) / (n h (1 - β h / 2)) + G ϑ / (h (1 - β h / 2))`;
  `exists_projGrad_sq_le_of_exact` is the version without truncation.
* `frequently_projGrad_sq_lt` (**convergence under Robbins–Monro step sizes**, deterministic form
  of 2410.18720 Thm 2 and 2502.03006 Thm 5.9): if `∑ h_k = ∞`, `∑ h_k² < ∞`, `β h_k ≤ 2` and the
  accumulated truncation errors are bounded, then `liminf ‖Π_k ∇ℒ(x_k)‖² = 0`;
  `frequently_projGrad_sq_lt_of_summable_sq` drops the restriction `β h_k ≤ 2` (as in 2502.03006).
* `norm_apply_le_of_absorbs`, `loss_projGradStep_le_of_absorbs`: an augmented space that captures
  the tangent gradient (`Q (T ∇ℒ) = T ∇ℒ`, as for the GeoLoRA / augmented BUG bases) gives at least
  the descent of the tangent step, and its stationarity measure controls the Riemannian gradient;
  `frequently_tangentGrad_sq_lt_of_absorbs` is the conclusion `liminf ‖P(Y_k) ∇ℓ(Y_k)‖² = 0` of
  2502.03006 Thm 5.9 for the tangent projectors `P(Y_k)`.
* **Federated DLRT** (Schotthöfer–Laiu, arXiv 2406.17887, §3.2, full variance correction, `C`
  clients with `s⋆` local steps each, shared augmented Galerkin projector):
  `norm_fedClientIter_sub_le_exp` (client drift bound, Thm 1), `loss_fedRound_le` (Thm 8),
  `loss_truncated_fedRound_le` (global loss descent, Thm 2, with the constant `12`),
  `exists_fedGrad_sq_le` and `exists_fedGrad_sq_le_of_lr` (global convergence, Thm 3, eq. (13) with
  the constant `48`).
* `loss_projGradStep_le_energyFraction`, `exists_grad_sq_le_of_energyFraction`: if each projector
  retains a fraction `γ` of the gradient energy (`‖Π g‖² ≥ γ ‖g‖²`, the quantity `γ_g` of
  Thomas, arXiv 2607.05872, eq. (3)), the iterates approach a stationary point of the *full*
  problem, whatever the (possibly non-identifiable) subspaces are.
* `loss_le_of_projGradFlow`, `loss_le_of_stateProjGradFlow`, `loss_le_of_galerkinGradFlow`
  (**continuous version**): along the projected gradient flow `ẏ = -Π(t) ∇ℒ(y)` (fixed Galerkin
  space, or the DLRA gradient flow `Ẇ = -P(W) ∇ℒ(W)` of 2306.01485 eq. (4) and 2410.18720) the
  loss decreases, with rate `α²` if `‖Π ∇ℒ‖ ≥ α`.
* `heavyBall_energy_le` (Schotthöfer–Klein–Kusch, arXiv 2506.17475, Thm 1, energy part): for the
  low-rank heavy-ball flow `Ẇ = P V`, `V̇ = -γ V - P ∇ℒ(W)` the energy `ℒ(W) + ‖V‖²/2` is
  nonincreasing; `naiveMomentum_apply_eq_zero_of_left` is the algebraic core of Thm 4 there (naive
  factor-wise momentum can be stationary although `P(W) ∇ℒ(W) ≠ 0`).
* **GeoLoRA** (arXiv 2410.18720): `geoLoRADir_eq_tangent` / `geoLoRAStep_eq` (the assembled
  augmented `2r × 2r` update is `Ŵ = W₀ - λ P(W₀) ∇ℒ(W₀)`, proof of Thm 1), with the capture
  conditions obtained from the basis augmentation, eq. (7), in `IsGeoLoRABases.of_augmentation`;
  `loss_truncated_geoLoRAStep_le` (Thm 1, deterministic) and `frequently_geoLoRA_tangentGrad_sq_lt`
  (Thm 2, deterministic, without the step size restriction).
* **Stabilized DLRT** (arXiv 2609.32615): augmenting by a compensation buffer can only reduce the
  projection residual (`norm_sub_apply_le_of_absorbs`, Thm 3.3 with `γ = 1`) and keeps the descent
  guarantee (`loss_truncated_projGradStep_le_of_absorbs`), but subspace inclusion gives no uniform
  contraction factor `γ < 1` (`not_exists_contraction_of_absorbs`, a negative result on Step 1 of
  the proof of Thm 3.3).
* **Conditioning** (arXiv 2306.01485 §4, arXiv 2505.08022 Def. 1): `norm_sub_bestMultiple_le` (the
  scale `α_S² = ‖S‖²/r` is the best constant approximation of `SᵀS`), the orthogonality relation
  `inner_sub_bestMultiple_eq_zero`, the conditioning tolerance `div_le_one_add_of_mem_Icc`
  (`ε = τ s/(2 + τ)` gives `cond₂ ≤ 1 + τ`), and `robustDLRT_stability` (long-time stability of
  the regularised least-squares flow, Prop. 3 of 2505.08022, and the sharper
  `robustDLRT_stability_sharp`).

## Conventions and deviations

Everything is deterministic: the stochastic statements of the papers (expectations over
mini-batches) are not formalised.  The truncation tolerance enters as a hypothesis
`‖x₁ - x̂₁‖ ≤ ϑ`; we use a gradient bound `G` where the papers reuse the letter `L` for both the
smoothness constant and the gradient bound.  Coefficient gradients in augmented bases are expressed
through the Galerkin projector: `‖∇_S̃ ℒ(Ũ S̃ Ṽᵀ)‖ = ‖Ũᵀ ∇ℒ Ṽ‖ = ‖Π ∇ℒ‖` for orthonormal `Ũ, Ṽ`.
For FeDLRT the global loss is only required to have a `β`-Lipschitz gradient (it need not be the
client average), and the learning rate restriction `λ ≤ 1/(12 L s⋆)` of the paper is relaxed to
`λ β s⋆ ≤ 1` in the descent estimate.

The step maps `projGradStep`, `geoLoRADir`, `geoLoRAStep`, `fedClientIter`, `fedRound`, `fedDrift`
and the structure `IsGeoLoRABases` are defined in `LeanDLRA/Training/Defs.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Elementary facts about real sequences -/

section Sequences

/-- Telescoping: if `a k ≤ u k - u (k+1) + e k` for all `k`, then
`∑_{k<n} a k ≤ u 0 - u n + ∑_{k<n} e k`. -/
lemma sum_le_of_le_sub_add {u a e : ℕ → ℝ} (h : ∀ k, a k ≤ u k - u (k + 1) + e k) (n : ℕ) :
    ∑ k ∈ range n, a k ≤ u 0 - u n + ∑ k ∈ range n, e k := by
  have h1 : ∑ k ∈ range n, a k ≤ ∑ k ∈ range n, ((u k - u (k + 1)) + e k) :=
    sum_le_sum fun k _ => h k
  have h2 := sum_range_sub' u n
  rw [sum_add_distrib, h2] at h1
  exact h1

/-- The minimum of a finite family is at most its mean: if `c ∑_{k<n} a k ≤ A + n e` with
`c > 0`, some `k < n` has `a k ≤ A / (n c) + e / c`. -/
lemma exists_le_of_mul_sum_le {a : ℕ → ℝ} {c A e : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n)
    (h : c * ∑ k ∈ range n, a k ≤ A + n * e) :
    ∃ k < n, a k ≤ A / (n * c) + e / c := by
  obtain ⟨k, hk, hmin⟩ := exists_min_image (range n) a (nonempty_range_iff.2 hn.ne')
  refine ⟨k, mem_range.1 hk, ?_⟩
  have hsum : (n : ℝ) * a k ≤ ∑ j ∈ range n, a j := by
    have := card_nsmul_le_sum (range n) a (a k) hmin
    rwa [card_range, nsmul_eq_mul] at this
  have hnc : 0 < (n : ℝ) * c := mul_pos (Nat.cast_pos.2 hn) hc
  have e1 : A / (n * c) + e / c = (A + n * e) / (n * c) := by
    rw [div_add_div _ _ hnc.ne' hc.ne', div_eq_div_iff (mul_pos hnc hc).ne' hnc.ne']
    ring
  rw [e1, le_div_iff₀ hnc]
  nlinarith

/-- If `∑ w_k a_k` stays bounded while `∑ w_k = ∞` (`w, a ≥ 0`), then `a_k` is frequently
smaller than any `ε > 0`, i.e. `liminf a_k = 0`. -/
lemma exists_lt_of_sum_mul_le {w a : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) (ha : ∀ k, 0 ≤ a k)
    (hdiv : ¬ Summable w) {C : ℝ} (hC : ∀ n, ∑ k ∈ range n, w k * a k ≤ C) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) : ∃ k, N ≤ k ∧ a k < ε := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  apply hdiv
  refine summable_of_sum_range_le hw (c := ∑ k ∈ range N, w k + C / ε) fun n => ?_
  have hC0 : 0 ≤ C := by simpa using hC 0
  have hCε : 0 ≤ C / ε := div_nonneg hC0 hε.le
  rcases le_total n N with hnN | hNn
  · have : ∑ k ∈ range n, w k ≤ ∑ k ∈ range N, w k :=
      sum_le_sum_of_subset_of_nonneg (range_mono hnN) fun k _ _ => hw k
    linarith
  · rw [← sum_range_add_sum_Ico _ hNn]
    have h1 : ∑ k ∈ Ico N n, w k * ε ≤ ∑ k ∈ Ico N n, w k * a k :=
      sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hcon k (mem_Ico.1 hk).1) (hw k)
    have h2 : ∑ k ∈ Ico N n, w k * a k ≤ ∑ k ∈ range n, w k * a k := by
      rw [← sum_range_add_sum_Ico _ hNn]
      have : 0 ≤ ∑ k ∈ range N, w k * a k := sum_nonneg fun k _ => mul_nonneg (hw k) (ha k)
      linarith
    have h3 : ∑ k ∈ Ico N n, w k ≤ C / ε := by
      rw [le_div_iff₀ hε, sum_mul]
      linarith [hC n]
    linarith

end Sequences

/-! ### The descent lemma -/

section DescentLemma

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- Derivative of the loss along the line `s ↦ x + s d`. -/
lemma hasDerivAt_loss_line (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ℒ (x + s • d)) ⟪g (x + t • d), d⟫ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have h2 := (hℒ (x + t • d)).comp_hasDerivAt t h1
  simpa [innerSL_apply_apply, Function.comp_def] using h2

/-- **Descent lemma** for `β`-smooth losses (Lemma 5.7 of arXiv 2502.03006, Lemma 4 of
arXiv 2406.17887, Lemma 1 of arXiv 2410.18720):
`ℒ y ≤ ℒ x + ⟪∇ℒ(x), y - x⟫ + β/2 ‖y - x‖²`. -/
theorem descent_lemma (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x y : E) :
    ℒ y ≤ ℒ x + ⟪g x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ℒ x + s * ⟪g x, d⟫ + β / 2 * s ^ 2 * ‖d‖ ^ 2)
      (⟪g x, d⟫ + β * t * ‖d‖ ^ 2) t := by
    intro t
    have h := (((hasDerivAt_id' t).mul_const ⟪g x, d⟫).const_add (ℒ x)).add
      (((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖d‖ ^ 2))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ⟪g (x + s • d), d⟫ ≤ ⟪g x, d⟫ + β * s * ‖d‖ ^ 2 := by
    intro s hs
    have h1 : ⟪g (x + s • d) - g x, d⟫ ≤ ‖g (x + s • d) - g x‖ * ‖d‖ := real_inner_le_norm _ _
    have h2 : ‖g (x + s • d) - g x‖ ≤ β * (s * ‖d‖) := by
      have := hg (x + s • d) x
      rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1] at this
    rw [inner_sub_left] at h1
    nlinarith [norm_nonneg d]
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun s : ℝ => ℒ (x + s • d)) (f' := fun s => ⟪g (x + s • d), d⟫)
    (fun s _ => (hasDerivAt_loss_line hℒ x d s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_loss_line hℒ x d s).hasDerivWithinAt)
    (B := fun s => ℒ x + s * ⟪g x, d⟫ + β / 2 * s ^ 2 * ‖d‖ ^ 2)
    (B' := fun s => ⟪g x, d⟫ + β * s * ‖d‖ ^ 2) (by simp)
    (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt) hbound (right_mem_Icc.2 zero_le_one)
  have key' : ℒ (x + (1 : ℝ) • d) ≤ ℒ x + 1 * ⟪g x, d⟫ + β / 2 * 1 ^ 2 * ‖d‖ ^ 2 := key
  have hxd : x + (1 : ℝ) • d = y := by rw [one_smul, hd, add_sub_cancel]
  rw [hxd] at key'
  linarith

/-- **Lower descent lemma**: `ℒ x + ⟪∇ℒ(x), y - x⟫ - β/2 ‖y - x‖² ≤ ℒ y`. -/
theorem descent_lemma_lower (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x y : E) :
    ℒ x + ⟪g x, y - x⟫ - β / 2 * ‖y - x‖ ^ 2 ≤ ℒ y := by
  have hℒ' : ∀ x, HasFDerivAt (fun x => -ℒ x) (innerSL ℝ (-g x)) x := fun x => by
    have := (hℒ x).neg
    rwa [← map_neg] at this
  have hg' : ∀ x y, ‖-g x - -g y‖ ≤ β * ‖x - y‖ := fun x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have h := descent_lemma hℒ' hg' x y
  rw [inner_neg_left] at h
  linarith

/-- Two-sided form of the descent lemma: `|ℒ y - ℒ x - ⟪∇ℒ(x), y - x⟫| ≤ β/2 ‖y - x‖²`. -/
theorem abs_loss_sub_linear_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x y : E) :
    |ℒ y - ℒ x - ⟪g x, y - x⟫| ≤ β / 2 * ‖y - x‖ ^ 2 := by
  have h1 := descent_lemma hℒ hg x y
  have h2 := descent_lemma_lower hℒ hg x y
  rw [abs_le]; constructor <;> linarith

/-- The descent lemma stated with Mathlib's `HasGradientAt`. -/
theorem descent_lemma_of_hasGradientAt [CompleteSpace E] (hℒ : ∀ x, HasGradientAt ℒ (g x) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (x y : E) :
    ℒ y ≤ ℒ x + ⟪g x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 :=
  descent_lemma (hasFDerivAt_of_hasGradientAt hℒ) hg x y

end DescentLemma

/-! ### The projected (Galerkin) gradient step -/

section ProjStep

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ} {P Q T : E →L[ℝ] E}

lemma projGradStep_sub_self (P : E →L[ℝ] E) (g : E → E) (h : ℝ) (x : E) :
    projGradStep P g h x - x = -(h • P (g x)) := by
  simp [projGradStep]

/-- If the current iterate lies in the (augmented) Galerkin space, the projected step is the
projection of the full gradient step and stays in that space. -/
lemma projGradStep_eq_apply (hx : P x = x) (g : E → E) (h : ℝ) :
    projGradStep P g h x = P (x - h • g x) := by
  rw [projGradStep, map_sub, map_smul, hx]

lemma projGradStep_mem_range (hP : IsOrthProj P) (hx : P x = x) (g : E → E) (h : ℝ) :
    P (projGradStep P g h x) = projGradStep P g h x := by
  rw [projGradStep_eq_apply hx, hP.idem]

/-- The projected gradient step is the explicit Euler step of the Galerkin gradient flow
`y' = -Π ∇ℒ(y)` (`projEuler` of `Foundations/Galerkin.lean`). -/
lemma projEuler_neg_eq_projGradStep (g : E → E) (h t : ℝ) (x : E) :
    projEuler P (fun _ x => -g x) h t x = projGradStep P g h x := by
  simp [projEuler, projGradStep, sub_eq_add_neg]

/-- **Loss descent of the projected gradient step** (Kusch–Schotthöfer–Walter, arXiv 2502.03006,
Thm 5.8; Schotthöfer et al., arXiv 2410.18720, eqs. (22)–(25)): for every orthogonal projector
`Π` and every step size `h`,
`ℒ(x - h Π ∇ℒ(x)) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖²`. -/
theorem loss_projGradStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) (h : ℝ) (x : E) :
    ℒ (projGradStep P g h x) ≤ ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 := by
  have hd := descent_lemma hℒ hg x (projGradStep P g h x)
  rw [projGradStep_sub_self, inner_neg_right, inner_smul_right, real_inner_comm,
    hP.inner_self_apply, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hd
  linarith

/-- The projected step is monotone for `0 ≤ h ≤ 2 / β`: `ℒ(x - h Π ∇ℒ(x)) ≤ ℒ(x)`. -/
theorem loss_projGradStep_le_self (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {h : ℝ}
    (hh : 0 ≤ h * (1 - β * h / 2)) (x : E) : ℒ (projGradStep P g h x) ≤ ℒ x := by
  have := loss_projGradStep_le hℒ hg hP h x
  nlinarith [sq_nonneg ‖P (g x)‖]

/-- **Loss descent guarantee of DLRT** (deterministic form of Schotthöfer et al.,
arXiv 2410.18720, Thm 1, and of Schotthöfer–Laiu, arXiv 2406.17887, Thm 2, for one client and
one local step): a projected gradient step followed by a truncation `‖x₁ - x̂₁‖ ≤ ϑ`, with
`‖∇ℒ‖ ≤ G` on the segment `[x̂₁, x₁]`, satisfies
`ℒ(x₁) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖² + G ϑ`. -/
theorem loss_truncated_projGradStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) (h : ℝ) (x : E) {x₁ : E}
    {ϑ G : ℝ} (htr : ‖x₁ - projGradStep P g h x‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ (projGradStep P g h x) x₁, ‖g w‖ ≤ G) :
    ℒ x₁ ≤ ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 + G * ϑ := by
  have h1 := loss_projGradStep_le hℒ hg hP h x
  have h2 := abs_energy_sub_le hℒ hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 : G * ‖x₁ - projGradStep P g h x‖ ≤ G * ϑ := mul_le_mul_of_nonneg_left htr hG0
  have h4 := (abs_le.1 h2).2
  linarith

/-- Variant of `loss_truncated_projGradStep_le` using only smoothness (no gradient bound on the
segment): `ℒ(x₁) ≤ ℒ(x) - h (1 - β h / 2) ‖Π ∇ℒ(x)‖² + ‖∇ℒ(x̂₁)‖ ϑ + β ϑ² / 2`. -/
theorem loss_truncated_projGradStep_le' (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hP : IsOrthProj P) (h : ℝ) (x : E)
    {x₁ : E} {ϑ : ℝ} (htr : ‖x₁ - projGradStep P g h x‖ ≤ ϑ) :
    ℒ x₁ ≤ ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 +
      ‖g (projGradStep P g h x)‖ * ϑ + β / 2 * ϑ ^ 2 := by
  set xh := projGradStep P g h x
  have h1 := loss_projGradStep_le hℒ hg hP h x
  have h2 := descent_lemma hℒ hg xh x₁
  have h3 : ⟪g xh, x₁ - xh⟫ ≤ ‖g xh‖ * ϑ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left htr (norm_nonneg _))
  have h4 : ‖x₁ - xh‖ ^ 2 ≤ ϑ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htr 2
  have h5 : β / 2 * ‖x₁ - xh‖ ^ 2 ≤ β / 2 * ϑ ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
  linarith

/-- Loss descent of the projected step, stated with Mathlib's `HasGradientAt`. -/
theorem loss_projGradStep_le_of_hasGradientAt [CompleteSpace E]
    (hℒ : ∀ x, HasGradientAt ℒ (g x) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (h : ℝ) (x : E) :
    ℒ (projGradStep P g h x) ≤ ℒ x - h * (1 - β * h / 2) * ‖P (g x)‖ ^ 2 :=
  loss_projGradStep_le (hasFDerivAt_of_hasGradientAt hℒ) hg hP h x

/-! #### Augmented spaces -/

/-- **Augmentation does not reduce the stationarity measure**: if the orthogonal projector `Q`
(onto an augmented space) fixes `T v` for an orthogonal projector `T` (e.g. the GeoLoRA / augmented
BUG bases contain the range of the tangent gradient `P(W) ∇ℒ(W)`), then `‖T v‖ ≤ ‖Q v‖`. -/
lemma norm_apply_le_of_absorbs (hT : IsOrthProj T) (hQ : IsOrthProj Q) {v : E}
    (hv : Q (T v) = T v) : ‖T v‖ ≤ ‖Q v‖ := by
  have h1 : ‖T v‖ ^ 2 = ⟪T v, Q v⟫ := by
    rw [← hT.inner_self_apply, ← hQ.symm, hv]
  have h2 : ⟪T v, Q v⟫ ≤ ‖T v‖ * ‖Q v‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg (T v), norm_nonneg (Q v)]

/-- The step with an augmented projector `Q` that captures the tangent gradient `T ∇ℒ(x)` decreases
the loss at least as much as guaranteed for the tangent step:
`ℒ(x - h Q ∇ℒ(x)) ≤ ℒ(x) - h (1 - β h / 2) ‖T ∇ℒ(x)‖²` for `h (1 - β h / 2) ≥ 0`. -/
theorem loss_projGradStep_le_of_absorbs (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hT : IsOrthProj T) (hQ : IsOrthProj Q) {x : E}
    (hx : Q (T (g x)) = T (g x)) {h : ℝ} (hh : 0 ≤ h * (1 - β * h / 2)) :
    ℒ (projGradStep Q g h x) ≤ ℒ x - h * (1 - β * h / 2) * ‖T (g x)‖ ^ 2 := by
  have h1 := loss_projGradStep_le hℒ hg hQ h x
  have h2 : ‖T (g x)‖ ^ 2 ≤ ‖Q (g x)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_absorbs hT hQ hx) 2
  nlinarith

/-! #### Energy fraction of the projector -/

/-- **Descent in terms of the captured gradient energy** (cf. Thomas, arXiv 2607.05872, §4): if
the projector retains a fraction `γ` of the gradient energy, `γ ‖∇ℒ(x)‖² ≤ ‖Π ∇ℒ(x)‖²`
(the quantity `γ_g` of eq. (3) there), then for `h (1 - β h / 2) ≥ 0`
`ℒ(x - h Π ∇ℒ(x)) ≤ ℒ(x) - h (1 - β h / 2) γ ‖∇ℒ(x)‖²`. -/
theorem loss_projGradStep_le_energyFraction (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hP : IsOrthProj P) {x : E} {γ : ℝ}
    (hγ : γ * ‖g x‖ ^ 2 ≤ ‖P (g x)‖ ^ 2) {h : ℝ} (hh : 0 ≤ h * (1 - β * h / 2)) :
    ℒ (projGradStep P g h x) ≤ ℒ x - h * (1 - β * h / 2) * γ * ‖g x‖ ^ 2 := by
  have h1 := loss_projGradStep_le hℒ hg hP h x
  nlinarith

end ProjStep

/-! ### Convergence of projected gradient descent with truncation -/

section Convergence

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Summed loss descent** for truncated projected gradient descent with step-dependent
projectors `Π_k`, step sizes `h_k` and truncation tolerances `ϑ_k`:
`∑_{k<n} h_k (1 - β h_k / 2) ‖Π_k ∇ℒ(x_k)‖² ≤ ℒ(x₀) - ℒ(x_n) + G ∑_{k<n} ϑ_k`
(the telescoping step in the proofs of arXiv 2410.18720, Thm 2, and arXiv 2502.03006,
Thm 5.9). -/
theorem sum_descent_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ϑ : ℕ → ℝ} {G : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g (h k) (x k)‖ ≤ ϑ k)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g (h k) (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (n : ℕ) :
    ∑ k ∈ range n, h k * (1 - β * h k / 2) * ‖P k (g (x k))‖ ^ 2 ≤
      ℒ (x 0) - ℒ (x n) + G * ∑ k ∈ range n, ϑ k := by
  rw [mul_sum]
  exact sum_le_of_le_sub_add (u := fun k => ℒ (x k)) (fun k => by
    have := loss_truncated_projGradStep_le hℒ hg (hP k) (h k) (x k) (htr k) (hG k)
    linarith) n

/-- **Global convergence to tangent stationarity** (Schotthöfer–Laiu, arXiv 2406.17887, Thm 3,
for one client and one local step; the deterministic analogue of arXiv 2410.18720, Thm 2): for
`n > 0` truncated projected gradient steps with constant learning rate `h`,
`h (1 - β h / 2) > 0`, truncation tolerance `ϑ`, `‖∇ℒ‖ ≤ G` near the truncation and a lower
bound `ℒ_inf` on the loss,
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ_inf) / (n h (1 - β h / 2)) + G ϑ / (h (1 - β h / 2))`.
(With `h = 1/β` this is `2 β (ℒ(x₀) - ℒ_inf) / n + 2 β G ϑ`, the form of eq. (13) of
2406.17887 with the constant 48 replaced by 2.) -/
theorem exists_projGrad_sq_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ϑ G ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g h (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g h (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh : 0 < h * (1 - β * h / 2)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) / (n * (h * (1 - β * h / 2))) + G * ϑ / (h * (1 - β * h / 2)) := by
  refine exists_le_of_mul_sum_le hh hn ?_
  have hs := sum_descent_le (h := fun _ => h) (ϑ := fun _ => ϑ) hℒ hg hP htr hG n
  rw [← mul_sum, sum_const, card_range, nsmul_eq_mul] at hs
  have := hinf n
  linarith

/-- **Convergence without truncation**: `n > 0` exact projected gradient steps
`x_{k+1} = x_k - h Π_k ∇ℒ(x_k)` with `h (1 - β h / 2) > 0` satisfy
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ_inf) / (n h (1 - β h / 2))`. -/
theorem exists_projGrad_sq_le_of_exact (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ℒinf : ℝ} (hx : ∀ k, x (k + 1) = projGradStep (P k) g h (x k))
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh : 0 < h * (1 - β * h / 2)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤ (ℒ (x 0) - ℒinf) / (n * (h * (1 - β * h / 2))) := by
  have hsum : h * (1 - β * h / 2) * ∑ k ∈ range n, ‖P k (g (x k))‖ ^ 2 ≤
      ℒ (x 0) - ℒinf + n * 0 := by
    have hs := sum_le_of_le_sub_add (u := fun k => ℒ (x k))
      (a := fun k => h * (1 - β * h / 2) * ‖P k (g (x k))‖ ^ 2) (e := fun _ => 0)
      (fun k => by
        show h * (1 - β * h / 2) * ‖P k (g (x k))‖ ^ 2 ≤ ℒ (x k) - ℒ (x (k + 1)) + 0
        have := loss_projGradStep_le hℒ hg (hP k) h (x k)
        rw [← hx k] at this
        linarith) n
    rw [← mul_sum, sum_const_zero] at hs
    have := hinf n
    linarith
  obtain ⟨k, hk, hle⟩ := exists_le_of_mul_sum_le hh hn hsum
  exact ⟨k, hk, by simpa using hle⟩

/-- **Convergence to a stationary point of the full problem** for projected gradient descent
whose projectors capture a fixed fraction `γ > 0` of the gradient energy
(`γ ‖∇ℒ(x_k)‖² ≤ ‖Π_k ∇ℒ(x_k)‖²`, cf. arXiv 2607.05872, eq. (3) and §4): the subspaces may be
arbitrary (in particular re-drawn at every step), and still
`min_{k<n} ‖∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ_inf) / (n h (1 - β h / 2) γ)`. -/
theorem exists_grad_sq_le_of_energyFraction (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ℒinf γ : ℝ} (hx : ∀ k, x (k + 1) = projGradStep (P k) g h (x k))
    (hγ0 : 0 < γ) (hγ : ∀ k, γ * ‖g (x k)‖ ^ 2 ≤ ‖P k (g (x k))‖ ^ 2)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh : 0 < h * (1 - β * h / 2)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖g (x k)‖ ^ 2 ≤ (ℒ (x 0) - ℒinf) / (n * (h * (1 - β * h / 2)) * γ) := by
  obtain ⟨k, hk, hle⟩ := exists_projGrad_sq_le_of_exact hℒ hg hP hx hinf hh hn
  refine ⟨k, hk, ?_⟩
  have hD : 0 < (n : ℝ) * (h * (1 - β * h / 2)) := mul_pos (Nat.cast_pos.2 hn) hh
  rw [le_div_iff₀ hD] at hle
  rw [le_div_iff₀ (mul_pos hD hγ0)]
  have := mul_le_mul_of_nonneg_right (hγ k) hD.le
  linarith

/-- **Convergence under Robbins–Monro step sizes** (deterministic form of Schotthöfer et al.,
arXiv 2410.18720, Thm 2, and Kusch–Schotthöfer–Walter, arXiv 2502.03006, Thm 5.9): if the
learning rates satisfy `0 ≤ h_k`, `β h_k ≤ 2`, `∑ h_k = ∞`, `∑ h_k² < ∞`, the accumulated
truncation errors are bounded (`∑_{k<n} ϑ_k ≤ D`), `‖∇ℒ‖ ≤ G` near the truncations and the loss
is bounded below, then `liminf_k ‖Π_k ∇ℒ(x_k)‖² = 0`: for all `ε > 0` and `N` there is `k ≥ N`
with `‖Π_k ∇ℒ(x_k)‖² < ε`. -/
theorem frequently_projGrad_sq_lt (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ϑ : ℕ → ℝ} {G D ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g (h k) (x k)‖ ≤ ϑ k)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g (h k) (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hD : ∀ n, ∑ k ∈ range n, ϑ k ≤ D) (hinf : ∀ k, ℒinf ≤ ℒ (x k))
    (hh0 : ∀ k, 0 ≤ h k) (hh2 : ∀ k, β * h k ≤ 2) (hdiv : ¬ Summable h)
    (hsq : Summable fun k => h k ^ 2) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖P k (g (x k))‖ ^ 2 < ε := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 _ (left_mem_segment ℝ _ _))
  have hw : ∀ k, 0 ≤ h k * (1 - β * h k / 2) := fun k =>
    mul_nonneg (hh0 k) (by linarith [hh2 k])
  have hwdiv : ¬ Summable fun k => h k * (1 - β * h k / 2) := by
    intro hs
    apply hdiv
    have e : h = fun k => h k * (1 - β * h k / 2) + β / 2 * h k ^ 2 := by
      funext k; ring
    rw [e]
    exact hs.add (hsq.mul_left (β / 2))
  refine exists_lt_of_sum_mul_le hw (fun k => sq_nonneg _) hwdiv
    (C := ℒ (x 0) - ℒinf + G * D) (fun n => ?_) hε N
  have hs := sum_descent_le hℒ hg hP htr hG n
  have h1 := hinf n
  have h2 : G * ∑ k ∈ range n, ϑ k ≤ G * D := mul_le_mul_of_nonneg_left (hD n) hG0
  linarith

open Filter Topology in
/-- **Robbins–Monro convergence without a step size restriction** (Kusch–Schotthöfer–Walter,
arXiv 2502.03006, Thm 5.9, deterministic form, which only assumes `∑ h_k = ∞`, `∑ h_k² < ∞`):
since `h_k → 0`, the restriction `β h_k ≤ 2` of `frequently_projGrad_sq_lt` holds eventually, and
again `liminf_k ‖Π_k ∇ℒ(x_k)‖² = 0`. -/
theorem frequently_projGrad_sq_lt_of_summable_sq (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    {x : ℕ → E} {h ϑ : ℕ → ℝ} {G D ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g (h k) (x k)‖ ≤ ϑ k)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g (h k) (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hD : ∀ n, ∑ k ∈ range n, ϑ k ≤ D) (hinf : ∀ k, ℒinf ≤ ℒ (x k))
    (hh0 : ∀ k, 0 ≤ h k) (hdiv : ¬ Summable h) (hsq : Summable fun k => h k ^ 2) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖P k (g (x k))‖ ^ 2 < ε := by
  have hlim : Tendsto (fun k => β ^ 2 * h k ^ 2) atTop (𝓝 0) := by
    simpa using hsq.tendsto_atTop_zero.const_mul (β ^ 2)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 4 (by norm_num))
  have hh2 : ∀ k, β * h (N₀ + k) ≤ 2 := fun k => by
    have := hN₀ (N₀ + k) (Nat.le_add_right _ _)
    nlinarith [sq_nonneg (β * h (N₀ + k) - 2)]
  have hϑ0 : ∀ k, 0 ≤ ϑ k := fun k => (norm_nonneg _).trans (htr k)
  have hD' : ∀ n, ∑ k ∈ range n, ϑ (N₀ + k) ≤ D := fun n => by
    have h1 := hD (N₀ + n)
    rw [sum_range_add] at h1
    have h2 : 0 ≤ ∑ k ∈ range N₀, ϑ k := sum_nonneg fun k _ => hϑ0 k
    linarith
  have e : ∀ f : ℕ → ℝ, (fun k => f (N₀ + k)) = fun k => f (k + N₀) :=
    fun f => funext fun k => by rw [Nat.add_comm]
  have hdiv' : ¬ Summable fun k => h (N₀ + k) := by
    rw [e]
    exact fun hs => hdiv ((summable_nat_add_iff N₀).1 hs)
  have hsq' : Summable fun k => h (N₀ + k) ^ 2 := by
    rw [e fun k => h k ^ 2]
    exact (summable_nat_add_iff N₀).2 hsq
  obtain ⟨k, hk, hlt⟩ := frequently_projGrad_sq_lt hℒ hg (P := fun k => P (N₀ + k))
    (fun k => hP _) (x := fun k => x (N₀ + k)) (h := fun k => h (N₀ + k))
    (ϑ := fun k => ϑ (N₀ + k)) (fun k => htr (N₀ + k)) (fun k => hG (N₀ + k)) hD'
    (fun k => hinf _) (fun k => hh0 _) hh2 hdiv' hsq' hε N
  exact ⟨N₀ + k, by omega, hlt⟩

/-- **Convergence to Riemannian stationarity of augmented schemes** (Kusch–Schotthöfer–Walter,
arXiv 2502.03006, Thm 5.9, deterministic; Schotthöfer et al., arXiv 2410.18720, Thm 2): if the
augmented projectors `Π_k` (e.g. `Z ↦ Û_k Û_kᵀ Z`) fix the tangent gradient `T_k ∇ℒ(x_k)`
(`T_k = P(x_k)` the tangent projector of the low-rank manifold), Robbins–Monro learning rates
drive the Riemannian gradient to zero: `liminf_k ‖P(x_k) ∇ℒ(x_k)‖² = 0`. -/
theorem frequently_tangentGrad_sq_lt_of_absorbs (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P T : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    (hT : ∀ k, IsOrthProj (T k)) {x : ℕ → E} (habs : ∀ k, P k (T k (g (x k))) = T k (g (x k)))
    {h ϑ : ℕ → ℝ} {G D ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g (h k) (x k)‖ ≤ ϑ k)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g (h k) (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hD : ∀ n, ∑ k ∈ range n, ϑ k ≤ D) (hinf : ∀ k, ℒinf ≤ ℒ (x k))
    (hh0 : ∀ k, 0 ≤ h k) (hdiv : ¬ Summable h) (hsq : Summable fun k => h k ^ 2) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖T k (g (x k))‖ ^ 2 < ε := by
  obtain ⟨k, hk, hlt⟩ := frequently_projGrad_sq_lt_of_summable_sq hℒ hg hP htr hG hD hinf hh0
    hdiv hsq hε N
  exact ⟨k, hk, lt_of_le_of_lt
    (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_absorbs (hT k) (hP k) (habs k)) 2) hlt⟩

/-- Rate for the Riemannian gradient of augmented schemes with constant learning rate: if
`Π_k (T_k ∇ℒ(x_k)) = T_k ∇ℒ(x_k)`, then `min_{k<n} ‖T_k ∇ℒ(x_k)‖²` obeys the bound of
`exists_projGrad_sq_le`. -/
theorem exists_tangentGrad_sq_le_of_absorbs (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P T : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k))
    (hT : ∀ k, IsOrthProj (T k)) {x : ℕ → E} (habs : ∀ k, P k (T k (g (x k))) = T k (g (x k)))
    {h ϑ G ℒinf : ℝ}
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g h (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g h (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh : 0 < h * (1 - β * h / 2)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖T k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒinf) / (n * (h * (1 - β * h / 2))) + G * ϑ / (h * (1 - β * h / 2)) := by
  obtain ⟨k, hk, hle⟩ := exists_projGrad_sq_le hℒ hg hP htr hG hinf hh hn
  exact ⟨k, hk, (pow_le_pow_left₀ (norm_nonneg _)
    (norm_apply_le_of_absorbs (hT k) (hP k) (habs k)) 2).trans hle⟩

end Convergence

/-! ### GeoLoRA: the parallel augmented step is a tangent gradient step -/

section GeoLoRA

variable {ℒ : E → ℝ} {g : E → E} {β : ℝ}

/-- **Basis augmentation captures the new directions** (eq. (7) of arXiv 2410.18720): if the
augmented space `range (P₀ + P̃)`, `P̃ P₀ = 0`, contains `w ∈ range P₀` and the `K`-step update
`w - λ Q₀ v` (`K^new V₀ᵀ = W₀ - λ ∇ℒ V₀ V₀ᵀ`) with `λ ≠ 0`, then `P̃` fixes the new directions
`(1 - P₀) Q₀ v`. -/
lemma capture_of_mem_span {P₀ Pt Q : E →L[ℝ] E} (hPt : ∀ x, Pt (P₀ x) = 0) {w v : E}
    (hw : P₀ w = w) {lr : ℝ} (hlr : lr ≠ 0)
    (hK : P₀ (w - lr • Q v) + Pt (w - lr • Q v) = w - lr • Q v) :
    Pt (Q v - P₀ (Q v)) = Q v - P₀ (Q v) := by
  have h0 : Pt w = 0 := by rw [← hw]; exact hPt w
  have h1 : Pt (P₀ (Q v)) = 0 := hPt _
  simp only [map_sub, map_smul, hw, h0] at hK
  rw [zero_sub, ← sub_eq_add_neg, sub_sub, sub_right_inj, ← smul_add] at hK
  have h3 := smul_right_injective E hlr hK
  rw [map_sub, h1, sub_zero, eq_sub_iff_add_eq, add_comm, h3]

/-- **The GeoLoRA direction is the tangent gradient** (arXiv 2410.18720, proof of Thm 1:
`Ŵ = W₀ - λ P(W₀) ∇ℒ(W₀)`, with `P(W) Z = UUᵀZ + ZVVᵀ - UUᵀZVVᵀ`, eq. (18)): if `P₀, Q₀` commute,
`P₀` commutes with `Q̃`, `P̃ P₀ = 0`, `Q̃ Q₀ = 0`, and the new directions are captured,
`P̃ (1 - P₀) Q₀ v = (1 - P₀) Q₀ v` and `Q̃ (1 - Q₀) P₀ v = (1 - Q₀) P₀ v`, then
`P₀ Q₀ v + P̃ Q₀ v + P₀ Q̃ v = (P₀ + Q₀ - P₀ Q₀) v`. -/
lemma geoLoRADir_eq_tangent {P₀ Q₀ Pt Qt : E →L[ℝ] E} (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x))
    (hc' : ∀ x, P₀ (Qt x) = Qt (P₀ x)) (hPt : ∀ x, Pt (P₀ x) = 0) (hQt : ∀ x, Qt (Q₀ x) = 0)
    {v : E} (hPv : Pt (Q₀ v - P₀ (Q₀ v)) = Q₀ v - P₀ (Q₀ v))
    (hQv : Qt (P₀ v - Q₀ (P₀ v)) = P₀ v - Q₀ (P₀ v)) :
    geoLoRADir P₀ Q₀ Pt Qt v = tangent P₀ Q₀ v := by
  have h1 : Pt (Q₀ v) = Q₀ v - P₀ (Q₀ v) := by
    rw [← hPv, map_sub, hPt, sub_zero]
  have h2 : P₀ (Qt v) = P₀ v - Q₀ (P₀ v) := by
    rw [hc', ← hQv, map_sub, hQt, sub_zero]
  rw [geoLoRADir, tangent_apply, h1, h2, ← hc]
  abel

/-- **GeoLoRA bases from the augmentation `ortho([U₀, K^new])`, `ortho([V₀, L^new])`**
(arXiv 2410.18720, eq. (7)): if `W₀ = U₀S₀V₀ᵀ` lies in the ranges of `P₀` and `Q₀`, the augmented
left space contains `K^new V₀ᵀ = W₀ - λ Q₀ ∇ℒ` and the augmented right space contains
`U₀ L^new,ᵀ = W₀ - λ P₀ ∇ℒ` with `λ ≠ 0`, the capture conditions hold. -/
theorem IsGeoLoRABases.of_augmentation {P₀ Q₀ Pt Qt : E →L[ℝ] E} (hP₀ : IsOrthProj P₀)
    (hQ₀ : IsOrthProj Q₀) (hc : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)) (hc' : ∀ x, P₀ (Qt x) = Qt (P₀ x))
    (hPt : ∀ x, Pt (P₀ x) = 0) (hQt : ∀ x, Qt (Q₀ x) = 0) {w v : E} (hwP : P₀ w = w)
    (hwQ : Q₀ w = w) {lr : ℝ} (hlr : lr ≠ 0)
    (hK : P₀ (w - lr • Q₀ v) + Pt (w - lr • Q₀ v) = w - lr • Q₀ v)
    (hL : Q₀ (w - lr • P₀ v) + Qt (w - lr • P₀ v) = w - lr • P₀ v) :
    IsGeoLoRABases P₀ Q₀ Pt Qt v :=
  ⟨hP₀, hQ₀, hc, hc', hPt, hQt, capture_of_mem_span hPt hwP hlr hK,
    capture_of_mem_span hQt hwQ hlr hL⟩

lemma IsGeoLoRABases.dir_eq {P₀ Q₀ Pt Qt : E →L[ℝ] E} {v : E}
    (hb : IsGeoLoRABases P₀ Q₀ Pt Qt v) : geoLoRADir P₀ Q₀ Pt Qt v = tangent P₀ Q₀ v :=
  geoLoRADir_eq_tangent hb.comm hb.comm_aug hb.left_orth hb.right_orth hb.left_capture
    hb.right_capture

lemma IsGeoLoRABases.isOrthProj_tangent {P₀ Q₀ Pt Qt : E →L[ℝ] E} {v : E}
    (hb : IsGeoLoRABases P₀ Q₀ Pt Qt v) : IsOrthProj (tangent P₀ Q₀) :=
  hb.orthProj_left.tangent hb.orthProj_right hb.comm

/-- The GeoLoRA step is the explicit Euler step of the Riemannian gradient flow:
`Ŵ = W₀ - λ P(W₀) ∇ℒ(W₀)` (arXiv 2410.18720, proof of Thm 1). -/
theorem geoLoRAStep_eq {P₀ Q₀ Pt Qt : E →L[ℝ] E} {w : E} (hb : IsGeoLoRABases P₀ Q₀ Pt Qt (g w))
    (lr : ℝ) : geoLoRAStep P₀ Q₀ Pt Qt g lr w = projGradStep (tangent P₀ Q₀) g lr w := by
  rw [geoLoRAStep, hb.dir_eq, projGradStep]

/-- **Descent estimate of GeoLoRA** (arXiv 2410.18720, Thm 1, deterministic gradients): after the
truncation `‖W₁ - Ŵ‖ ≤ ϑ`, with `‖∇ℒ‖ ≤ G` on `[Ŵ, W₁]`,
`ℒ(W₁) ≤ ℒ(W₀) - λ (1 - β λ / 2) ‖P(W₀) ∇ℒ(W₀)‖² + G ϑ`.  (The paper's `λ(1 - Lλ²/2)` is a typo
for `λ(1 - Lλ/2)`, cf. its eq. (25); its last term `L ‖W₁ - Ŵ‖` uses `L` as gradient bound.) -/
theorem loss_truncated_geoLoRAStep_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P₀ Q₀ Pt Qt : E →L[ℝ] E} {w : E}
    (hb : IsGeoLoRABases P₀ Q₀ Pt Qt (g w)) (lr : ℝ) {w₁ : E} {ϑ G : ℝ}
    (htr : ‖w₁ - geoLoRAStep P₀ Q₀ Pt Qt g lr w‖ ≤ ϑ)
    (hG : ∀ z ∈ segment ℝ (geoLoRAStep P₀ Q₀ Pt Qt g lr w) w₁, ‖g z‖ ≤ G) :
    ℒ w₁ ≤ ℒ w - lr * (1 - β * lr / 2) * ‖tangent P₀ Q₀ (g w)‖ ^ 2 + G * ϑ := by
  rw [geoLoRAStep_eq hb] at htr hG
  exact loss_truncated_projGradStep_le hℒ hg hb.isOrthProj_tangent lr w htr hG

/-- **Convergence of GeoLoRA** (arXiv 2410.18720, Thm 2, deterministic gradients): with
Robbins–Monro learning rates (`∑ λ_k = ∞`, `∑ λ_k² < ∞`; the paper's restriction `λ_k ≤ 2/L` is
not needed), bounded accumulated truncation errors and a loss bounded below,
`liminf_k ‖P(W_k) ∇ℒ(W_k)‖² = 0`. -/
theorem frequently_geoLoRA_tangentGrad_sq_lt (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {P₀ Q₀ Pt Qt : ℕ → E →L[ℝ] E} {w : ℕ → E}
    (hb : ∀ k, IsGeoLoRABases (P₀ k) (Q₀ k) (Pt k) (Qt k) (g (w k))) {lr ϑ : ℕ → ℝ}
    {G D ℒinf : ℝ}
    (htr : ∀ k, ‖w (k + 1) - geoLoRAStep (P₀ k) (Q₀ k) (Pt k) (Qt k) g (lr k) (w k)‖ ≤ ϑ k)
    (hG : ∀ k, ∀ z ∈ segment ℝ (geoLoRAStep (P₀ k) (Q₀ k) (Pt k) (Qt k) g (lr k) (w k))
      (w (k + 1)), ‖g z‖ ≤ G)
    (hD : ∀ n, ∑ k ∈ range n, ϑ k ≤ D) (hinf : ∀ k, ℒinf ≤ ℒ (w k))
    (hlr0 : ∀ k, 0 ≤ lr k) (hdiv : ¬ Summable lr) (hsq : Summable fun k => lr k ^ 2) {ε : ℝ}
    (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖tangent (P₀ k) (Q₀ k) (g (w k))‖ ^ 2 < ε := by
  simp only [geoLoRAStep_eq (hb _)] at htr hG
  exact frequently_projGrad_sq_lt_of_summable_sq hℒ hg (fun k => (hb k).isOrthProj_tangent) htr
    hG hD hinf hlr0 hdiv hsq hε N

end GeoLoRA

/-! ### Stabilized DLRT: buffer augmentation -/

section Stabilized

variable {P Q : E →L[ℝ] E}

/-- **Augmentation by a compensation buffer can only reduce the projection residual**
(Stabilized DLRT, arXiv 2609.32615, proof of Thm 3.3, Step 1, with `γ = 1`): if the augmented
projector `Q` (`Û Ûᵀ`, bases enlarged by the buffer) absorbs the projector `P` (`Ũ Ũᵀ`), then
`‖(1 - Q) x‖ ≤ ‖(1 - P) x‖`. -/
lemma norm_sub_apply_le_of_absorbs (hQ : IsOrthProj Q) (h : ∀ x, Q (P x) = P x) (x : E) :
    ‖x - Q x‖ ≤ ‖x - P x‖ :=
  hQ.norm_sub_le_of_mem_range x (P x) (h x)

/-- Equality case of `norm_sub_apply_le_of_absorbs`: unless the augmented projector is the
identity, some vector has the same nonzero residual for both projectors. -/
theorem exists_norm_sub_apply_eq_of_absorbs (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (h : ∀ x, Q (P x) = P x) (hQ1 : ∃ y, Q y ≠ y) :
    ∃ x, ‖x - Q x‖ = ‖x - P x‖ ∧ 0 < ‖x - P x‖ := by
  obtain ⟨y, hy⟩ := hQ1
  set x := y - Q y
  have hQx : Q x = 0 := by simp [x, hQ.idem]
  have hPx : P x = 0 := by
    simp only [x, map_sub, hP.comp_eq_of_comp_eq hQ h, sub_self]
  refine ⟨x, by rw [hQx, hPx], ?_⟩
  rw [hPx, sub_zero, norm_pos_iff, sub_ne_zero]
  exact fun h' => hy h'.symm

/-- **No spectral contraction factor from subspace inclusion** (negative result on Step 1 of the
proof of Thm 3.3 in arXiv 2609.32615, which asserts some `γ ∈ (0, 1)` with
`‖(I - ÛÛᵀ) A₁‖ ≤ γ ‖(I - ŨŨᵀ) A₁‖`): for buffer-augmented projectors `Q ⊇ P` with `Q ≠ 1` there is
a vector `x` for which no `γ < 1` satisfies `‖(1 - Q) x‖ ≤ γ ‖(1 - P) x‖`.  Only `γ = 1`
(`norm_sub_apply_le_of_absorbs`) follows from the inclusion. -/
theorem not_exists_contraction_of_absorbs (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (h : ∀ x, Q (P x) = P x) (hQ1 : ∃ y, Q y ≠ y) :
    ∃ x, ¬ ∃ γ < 1, ‖x - Q x‖ ≤ γ * ‖x - P x‖ := by
  obtain ⟨x, hx, hpos⟩ := exists_norm_sub_apply_eq_of_absorbs hP hQ h hQ1
  refine ⟨x, fun ⟨γ, hγ, hle⟩ => ?_⟩
  rw [hx] at hle
  nlinarith

/-- Absorption is transitive: if the buffer-augmented projector `Q` absorbs `P` and `P` fixes the
tangent gradient `T v`, so does `Q`. -/
lemma apply_eq_of_absorbs_trans {T : E →L[ℝ] E} (h : ∀ x, Q (P x) = P x) {v : E}
    (hv : P (T v) = T v) : Q (T v) = T v := by
  rw [← hv, h]

/-- **Loss descent of buffer-augmented (stabilized) DLRT steps** (arXiv 2609.32615, SDLRT; in
the setting of arXiv 2502.03006, Thm 5.8): if the augmented projector `Q` fixes the tangent
gradient `T ∇ℒ(x)`, the truncated step satisfies the descent guarantee of the tangent step,
`ℒ(x₁) ≤ ℒ(x) - h (1 - β h / 2) ‖T ∇ℒ(x)‖² + G ϑ` for `h (1 - β h / 2) ≥ 0`. -/
theorem loss_truncated_projGradStep_le_of_absorbs {ℒ : E → ℝ} {g : E → E} {β : ℝ}
    {T : E →L[ℝ] E} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hT : IsOrthProj T) (hQ : IsOrthProj Q) {x : E}
    (hx : Q (T (g x)) = T (g x)) {h : ℝ} (hh : 0 ≤ h * (1 - β * h / 2)) {x₁ : E} {ϑ G : ℝ}
    (htr : ‖x₁ - projGradStep Q g h x‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ (projGradStep Q g h x) x₁, ‖g w‖ ≤ G) :
    ℒ x₁ ≤ ℒ x - h * (1 - β * h / 2) * ‖T (g x)‖ ^ 2 + G * ϑ := by
  have h1 := loss_truncated_projGradStep_le hℒ hg hQ h x htr hG
  have h2 : ‖T (g x)‖ ^ 2 ≤ ‖Q (g x)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_of_absorbs hT hQ hx) 2
  nlinarith

end Stabilized

/-! ### Federated dynamical low-rank training (FeDLRT) -/

section Federated

variable {ι : Type*} {ℒ : E → ℝ} {g : E → E} {gc : ι → E → E} {β lr : ℝ}
  {P : E →L[ℝ] E}

lemma fedClientIter_succ (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι)
    (s : ℕ) : fedClientIter P gc g lr x c (s + 1) = fedClientIter P gc g lr x c s -
      lr • P (gc c (fedClientIter P gc g lr x c s) - gc c x + g x) := rfl

/-- Closed form of the client iterates: the variance correction turns every local step into a
global gradient step plus a local gradient difference,
`z^s = x - s λ Π ∇ℒ(x) - λ ∑_{j<s} Π (∇ℒ_c(z^j) - ∇ℒ_c(x))`. -/
lemma fedClientIter_eq (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ) (x : E) (c : ι)
    (s : ℕ) :
    fedClientIter P gc g lr x c s = x - ((s : ℝ) * lr) • P (g x) -
      lr • ∑ j ∈ range s, P (gc c (fedClientIter P gc g lr x c j) - gc c x) := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    rw [fedClientIter_succ, sum_range_succ]
    nth_rw 1 [ih]
    rw [map_add]
    push_cast
    module

/-- Drift of the client iterates: `‖z^s - x‖ ≤ s λ (1 + λ β)^s ‖Π ∇ℒ(x)‖`. -/
lemma norm_fedClientIter_sub_le (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) (x : E)
    (c : ι) (s : ℕ) :
    ‖fedClientIter P gc g lr x c s - x‖ ≤ s * lr * (1 + lr * β) ^ s * ‖P (g x)‖ := by
  induction s with
  | zero => simp [fedClientIter]
  | succ s ih =>
    set z := fedClientIter P gc g lr x c s
    have h1 : fedClientIter P gc g lr x c (s + 1) - x =
        (z - x) - lr • P (gc c z - gc c x) - lr • P (g x) := by
      rw [fedClientIter_succ, map_add]
      module
    have h2 : ‖P (gc c z - gc c x)‖ ≤ β * ‖z - x‖ := (hP.norm_le _).trans (hgc c z x)
    have hq : 1 ≤ (1 + lr * β) ^ (s + 1) := one_le_pow₀ (by nlinarith)
    have hb : 0 ≤ 1 + lr * β := by nlinarith
    rw [h1]
    calc ‖(z - x) - lr • P (gc c z - gc c x) - lr • P (g x)‖
        ≤ ‖z - x‖ + lr * (β * ‖z - x‖) + lr * ‖P (g x)‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl ?_)) ?_)
          · rw [norm_smul, Real.norm_of_nonneg hlr]; exact mul_le_mul_of_nonneg_left h2 hlr
          · rw [norm_smul, Real.norm_of_nonneg hlr]
      _ = (1 + lr * β) * ‖z - x‖ + lr * ‖P (g x)‖ := by ring
      _ ≤ (1 + lr * β) * (s * lr * (1 + lr * β) ^ s * ‖P (g x)‖) + lr * ‖P (g x)‖ := by
          gcongr
      _ ≤ ((s + 1 : ℕ) : ℝ) * lr * (1 + lr * β) ^ (s + 1) * ‖P (g x)‖ := by
          have ha : 0 ≤ lr * ‖P (g x)‖ := mul_nonneg hlr (norm_nonneg _)
          have := mul_le_mul_of_nonneg_left hq ha
          rw [pow_succ] at this ⊢
          push_cast
          nlinarith

/-- **Client drift bound of FeDLRT** (Schotthöfer–Laiu, arXiv 2406.17887, Thm 1): if
`λ β s⋆ ≤ 1`, the variance-corrected client iterates satisfy, for every `s ≤ s⋆`,
`‖z^s - x‖ ≤ e s λ ‖Π ∇ℒ(x)‖ ≤ e s⋆ λ ‖∇_S̃ ℒ‖` (the paper states the bound `e s⋆ λ ‖∇_S̃ ℒ‖` for
`s < s⋆` under `λ ≤ 1/(L s⋆)`). -/
lemma norm_fedClientIter_sub_le_exp (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * β * sstar ≤ 1) (x : E) (c : ι) {s : ℕ} (hss : s ≤ sstar) :
    ‖fedClientIter P gc g lr x c s - x‖ ≤ Real.exp 1 * (s * lr) * ‖P (g x)‖ := by
  have h := norm_fedClientIter_sub_le (g := g) hP hgc hβ hlr x c s
  have hq : (1 + lr * β) ^ s ≤ Real.exp 1 := by
    calc (1 + lr * β) ^ s ≤ Real.exp (lr * β) ^ s :=
          pow_le_pow_left₀ (by nlinarith) (by linarith [Real.add_one_le_exp (lr * β)]) s
      _ = Real.exp (s * (lr * β)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := by
          refine Real.exp_le_exp.2 ?_
          have : (s : ℝ) ≤ sstar := by exact_mod_cast hss
          nlinarith [mul_nonneg hlr hβ]
  have ha : 0 ≤ s * lr * ‖P (g x)‖ := by positivity
  calc _ ≤ s * lr * (1 + lr * β) ^ s * ‖P (g x)‖ := h
    _ = (1 + lr * β) ^ s * (s * lr * ‖P (g x)‖) := by ring
    _ ≤ Real.exp 1 * (s * lr * ‖P (g x)‖) := mul_le_mul_of_nonneg_right hq ha
    _ = _ := by ring

/-- The aggregated FeDLRT update is a projected gradient step of length `s⋆ λ` perturbed by the
averaged drift: `x⋆ = x - s⋆ λ Π ∇ℒ(x) - λ Π w`. -/
lemma fedRound_eq [Fintype ι] [Nonempty ι] (P : E →L[ℝ] E) (gc : ι → E → E) (g : E → E) (lr : ℝ)
    (sstar : ℕ) (x : E) :
    fedRound P gc g lr sstar x =
      x - ((sstar : ℝ) * lr) • P (g x) - lr • P (fedDrift P gc g lr sstar x) := by
  have hC : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e : ∑ c, fedClientIter P gc g lr x c sstar = ∑ c, (x - ((sstar : ℝ) * lr) • P (g x) -
      lr • ∑ j ∈ range sstar, P (gc c (fedClientIter P gc g lr x c j) - gc c x)) :=
    sum_congr rfl fun c _ => fedClientIter_eq P gc g lr x c sstar
  rw [fedRound, e, fedDrift, sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, card_univ,
    ← smul_sum, map_smul, map_sum]
  simp_rw [map_sum]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
  match_scalars <;> field_simp

/-- Bound on the averaged drift: `‖w‖ ≤ s⋆ β e s⋆ λ ‖Π ∇ℒ(x)‖`. -/
lemma norm_fedDrift_le [Fintype ι] [Nonempty ι] (hP : IsOrthProj P)
    (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hs : lr * β * sstar ≤ 1) (x : E) :
    ‖fedDrift P gc g lr sstar x‖ ≤ sstar * (β * (Real.exp 1 * (sstar * lr) * ‖P (g x)‖)) := by
  set δ := β * (Real.exp 1 * (sstar * lr) * ‖P (g x)‖)
  have hterm : ∀ c, ∀ j ∈ range sstar,
      ‖gc c (fedClientIter P gc g lr x c j) - gc c x‖ ≤ δ := by
    intro c j hj
    refine (hgc c _ _).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    refine (norm_fedClientIter_sub_le_exp hP hgc hβ hlr hs x c (mem_range.1 hj).le).trans ?_
    have : (j : ℝ) ≤ sstar := by exact_mod_cast (mem_range.1 hj).le
    gcongr
  have hC : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [fedDrift, norm_smul, norm_inv, Real.norm_natCast]
  calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ c, ∑ j ∈ range sstar,
        (gc c (fedClientIter P gc g lr x c j) - gc c x)‖
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _c : ι, ∑ _j ∈ range sstar, δ := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun c _ =>
          (norm_sum_le _ _).trans (sum_le_sum (hterm c)))
    _ = sstar * δ := by
        rw [sum_const, sum_const, card_range, card_univ, nsmul_eq_mul, nsmul_eq_mul]
        field_simp

/-- **Loss descent of the aggregated FeDLRT round** (Schotthöfer–Laiu, arXiv 2406.17887, Thm 8,
before truncation; the augmentation itself does not change the loss, Lemma 7): if all client
losses and the global loss have `β`-Lipschitz gradients and `λ β s⋆ ≤ 1`, then
`ℒ(x⋆) ≤ ℒ(x) - s⋆ λ (1 - 12 s⋆ λ β) ‖Π ∇ℒ(x)‖²`.
(The paper assumes `λ ≤ 1/(12 L s⋆)`; we only need `λ β s⋆ ≤ 1`, and the global loss need not be
the client average.) -/
theorem loss_fedRound_le [Fintype ι] [Nonempty ι] (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) :
    ℒ (fedRound P gc g lr sstar x) ≤
      ℒ x - sstar * lr * (1 - 12 * (sstar * lr) * β) * ‖P (g x)‖ ^ 2 := by
  set A : ℝ := sstar * lr with hA
  set w := fedDrift P gc g lr sstar x
  set a := ‖P (g x)‖
  have hA0 : 0 ≤ A := by positivity
  have ha0 : 0 ≤ a := norm_nonneg _
  have hβA : β * A ≤ 1 := by rw [hA]; linarith
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hw : lr * ‖w‖ ≤ Real.exp 1 * β * A ^ 2 * a := by
    have := mul_le_mul_of_nonneg_left (norm_fedDrift_le (g := g) hP hgc hβ hlr hs x) hlr
    refine this.trans (le_of_eq ?_)
    rw [hA]; ring
  have hd := descent_lemma hℒ hg x (fedRound P gc g lr sstar x)
  have hdx : fedRound P gc g lr sstar x - x = -(A • P (g x) + lr • P w) := by
    rw [fedRound_eq]; abel
  rw [hdx, inner_neg_right, inner_add_right, inner_smul_right, inner_smul_right, norm_neg] at hd
  have h1 : ⟪g x, P (g x)⟫ = a ^ 2 := by rw [real_inner_comm, hP.inner_self_apply]
  have h2 : -(lr * ⟪g x, P w⟫) ≤ lr * (a * ‖w‖) := by
    rw [← hP.symm]
    have := abs_real_inner_le_norm (P (g x)) w
    have := neg_abs_le ⟪P (g x), w⟫
    nlinarith
  have h3 : ‖A • P (g x) + lr • P w‖ ≤ A * a + lr * ‖w‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg hA0]
    · rw [norm_smul, Real.norm_of_nonneg hlr]
      exact mul_le_mul_of_nonneg_left (hP.norm_le w) hlr
  have hω0 : 0 ≤ lr * ‖w‖ := mul_nonneg hlr (norm_nonneg _)
  have h4 : A * a + lr * ‖w‖ ≤ (1 + Real.exp 1) * (A * a) := by
    have : Real.exp 1 * β * A ^ 2 * a ≤ Real.exp 1 * (A * a) := by
      have := mul_le_mul_of_nonneg_left hβA (mul_nonneg he0 (mul_nonneg hA0 ha0))
      nlinarith
    nlinarith
  have h5 : ‖A • P (g x) + lr • P w‖ ^ 2 ≤ (1 + Real.exp 1) ^ 2 * (A * a) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h3.trans h4) 2
  have h6 : a * (lr * ‖w‖) ≤ Real.exp 1 * β * A ^ 2 * a ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw ha0
    nlinarith
  have hβA2 : 0 ≤ β * (A * a) ^ 2 := mul_nonneg hβ (sq_nonneg _)
  have h7 : β / 2 * ‖A • P (g x) + lr • P w‖ ^ 2 ≤
      β / 2 * ((1 + Real.exp 1) ^ 2 * (A * a) ^ 2) := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h8 : (Real.exp 1 + (1 + Real.exp 1) ^ 2 / 2) * (β * (A * a) ^ 2) ≤
      12 * (β * (A * a) ^ 2) := by
    refine mul_le_mul_of_nonneg_right ?_ hβA2
    nlinarith
  rw [h1] at hd
  linarith

/-- **Global loss descent of FeDLRT with variance correction** (Schotthöfer–Laiu,
arXiv 2406.17887, Thm 2, deterministic): one round with `s⋆` local steps, aggregation and a
truncation `‖x₁ - x⋆‖ ≤ ϑ` (with `‖∇ℒ‖ ≤ G` on `[x⋆, x₁]`) satisfies
`ℒ(x₁) - ℒ(x) ≤ -s⋆ λ (1 - 12 s⋆ λ β) ‖Π ∇ℒ(x)‖² + G ϑ`, which is eq. (12) with `L ϑ = G ϑ`. -/
theorem loss_truncated_fedRound_le [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    (hP : IsOrthProj P) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ} (hs : lr * β * sstar ≤ 1)
    (x : E) {x₁ : E} {ϑ G : ℝ} (htr : ‖x₁ - fedRound P gc g lr sstar x‖ ≤ ϑ)
    (hG : ∀ w ∈ segment ℝ (fedRound P gc g lr sstar x) x₁, ‖g w‖ ≤ G) :
    ℒ x₁ ≤ ℒ x - sstar * lr * (1 - 12 * (sstar * lr) * β) * ‖P (g x)‖ ^ 2 + G * ϑ := by
  have h1 := loss_fedRound_le hℒ hg hgc hP hβ hlr hs x
  have h2 := abs_energy_sub_le hℒ hG
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG _ (left_mem_segment ℝ _ _))
  have h3 : G * ‖x₁ - fedRound P gc g lr sstar x‖ ≤ G * ϑ := mul_le_mul_of_nonneg_left htr hG0
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Global convergence of FeDLRT** (Schotthöfer–Laiu, arXiv 2406.17887, Thm 3, general learning
rate): after `n > 0` rounds with round-dependent augmented Galerkin projectors `Π_k`,
`min_{k<n} ‖Π_k ∇ℒ(x_k)‖² ≤ (ℒ(x₀) - ℒ(x_n)) / (n c) + G ϑ / c` with
`c = s⋆ λ (1 - 12 s⋆ λ β) > 0`. -/
theorem exists_fedGrad_sq_le [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k)) (hβ : 0 ≤ β) (hlr : 0 ≤ lr) {sstar : ℕ}
    {x : ℕ → E} {ϑ G : ℝ} (htr : ∀ k, ‖x (k + 1) - fedRound (P k) gc g lr sstar (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (fedRound (P k) gc g lr sstar (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hpos : 0 < sstar * lr * (1 - 12 * (sstar * lr) * β)) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤
      (ℒ (x 0) - ℒ (x n)) / (n * (sstar * lr * (1 - 12 * (sstar * lr) * β))) +
        G * ϑ / (sstar * lr * (1 - 12 * (sstar * lr) * β)) := by
  have hA0 : 0 ≤ (sstar : ℝ) * lr := by positivity
  have hs : lr * β * sstar ≤ 1 := by
    have h12 : 0 < 1 - 12 * (sstar * lr) * β := by
      by_contra hcon
      have := not_lt.1 hcon
      nlinarith
    nlinarith
  refine exists_le_of_mul_sum_le hpos hn ?_
  have hsum := sum_le_of_le_sub_add (u := fun k => ℒ (x k))
    (a := fun k => sstar * lr * (1 - 12 * (sstar * lr) * β) * ‖P k (g (x k))‖ ^ 2)
    (e := fun _ => G * ϑ) (fun k => by
      have := loss_truncated_fedRound_le hℒ hg hgc (hP k) hβ hlr hs (x k) (htr k) (hG k)
      linarith) n
  rw [← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  linarith

/-- **Global convergence of FeDLRT, eq. (13) of arXiv 2406.17887** (Thm 3): with the learning rate
`s⋆ λ = 1 / (24 β)` used in the proof there,
`min_{k<n} ‖∇_S̃ ℒ(x_k)‖² ≤ 48 β / n (ℒ(x₀) - ℒ(x_n)) + 48 β G ϑ`
(the paper's `48 L² ϑ` with one factor `L` the gradient bound `G`). -/
theorem exists_fedGrad_sq_le_of_lr [Fintype ι] [Nonempty ι]
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hgc : ∀ c x y, ‖gc c x - gc c y‖ ≤ β * ‖x - y‖)
    {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k)) (hβ : 0 < β) (hlr : 0 ≤ lr) {sstar : ℕ}
    (hlr24 : sstar * lr * β = 1 / 24)
    {x : ℕ → E} {ϑ G : ℝ} (htr : ∀ k, ‖x (k + 1) - fedRound (P k) gc g lr sstar (x k)‖ ≤ ϑ)
    (hG : ∀ k, ∀ w ∈ segment ℝ (fedRound (P k) gc g lr sstar (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖P k (g (x k))‖ ^ 2 ≤ 48 * β / n * (ℒ (x 0) - ℒ (x n)) + 48 * β * G * ϑ := by
  have hA : (sstar : ℝ) * lr = 1 / (24 * β) := by
    rw [eq_div_iff (by positivity)]; linarith
  have hc : (sstar : ℝ) * lr * (1 - 12 * (sstar * lr) * β) = 1 / (48 * β) := by
    rw [hA]; field_simp; ring
  obtain ⟨k, hk, hle⟩ := exists_fedGrad_sq_le hℒ hg hgc hP hβ.le hlr htr hG
    (by rw [hc]; positivity) hn
  refine ⟨k, hk, hle.trans (le_of_eq ?_)⟩
  rw [hc]
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  field_simp

end Federated

/-! ### Continuous version: projected gradient flows -/

section Flow

variable {ℒ : E → ℝ} {g : E → E}

/-- **Loss decay along projected gradient flows** with a time-dependent family of orthogonal
projectors along the trajectory, `ẏ = -Π(t) ∇ℒ(y)`: if `α² ≤ ‖Π(t) ∇ℒ(y t)‖²`, then
`ℒ(y t) ≤ ℒ(y a) - α² (t - a)`.  Taking `Π(t) = P(y t)`, the tangent projector at `y t`, this is
the low-rank gradient flow `Ẇ = -P(W) ∇ℒ(W)` of dynamical low-rank training
(arXiv 2306.01485, eq. (4) ff.; arXiv 2410.18720, eq. (4)). -/
theorem loss_le_of_projGradFlow (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : ℝ → E →L[ℝ] E} (hP : ∀ t, IsOrthProj (P t)) {y : ℝ → E} {a b : ℝ}
    (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (-P t (g (y t))) (Ici t) t) {α : ℝ}
    (hα : ∀ t ∈ Ico a b, α ^ 2 ≤ ‖P t (g (y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℒ (y t) ≤ ℒ (y a) - α ^ 2 * (t - a) := by
  have hc : ContinuousOn (ℒ ∘ y) (Icc a b) :=
    (continuous_of_hasFDerivAt_innerSL hℒ).comp_continuousOn hyc
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (ℒ ∘ y) (-‖P t (g (y t))‖ ^ 2) (Ici t) t :=
    fun t ht => (hasDerivWithinAt_energy_comp hℒ (hy t ht)).congr_deriv (by
      rw [inner_neg_right, real_inner_comm, (hP t).inner_self_apply])
  have hB : ∀ t, HasDerivWithinAt (fun s => ℒ (y a) - α ^ 2 * (s - a)) (-(α ^ 2)) (Ici t) t :=
    fun t => by
      simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul (α ^ 2)).const_sub
        (ℒ (y a))
  have h := image_le_of_deriv_right_le_deriv_boundary hc hd
    (B := fun s => ℒ (y a) - α ^ 2 * (s - a)) (by simp)
    (Continuous.continuousOn (by fun_prop)) (fun t _ => hB t)
    fun t ht => by simpa using hα t ht
  exact fun t ht => h ht

/-- **Loss decay along the state-dependent projected gradient flow** `ẏ = -P(y) ∇ℒ(y)`, where
`P(x)` is an orthogonal projector for every `x` (the DLRA gradient flow on the low-rank manifold
with `P(x)` the tangent projector): `ℒ(y t) ≤ ℒ(y a)`. -/
theorem loss_le_of_stateProjGradFlow (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : E → E →L[ℝ] E} (hP : ∀ x, IsOrthProj (P x)) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ x => -P x (g x)) y a b) : ∀ t ∈ Icc a b, ℒ (y t) ≤ ℒ (y a) := by
  intro t ht
  have h := loss_le_of_projGradFlow hℒ (P := fun t => P (y t)) (fun t => hP (y t)) hy.cont
    hy.deriv (α := 0) (fun t _ => by simp) t ht
  simpa using h

/-- **Loss decay along the Galerkin gradient flow** `ẏ = -Π ∇ℒ(y)` on a fixed (augmented) space:
the continuous limit of the projected gradient step.  This is the energy decay of projected
gradient flows from `Foundations/Galerkin.lean` (arXiv 2104.05247, Thm 5) read as a statement
about training. -/
theorem loss_le_of_galerkinGradFlow (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ x => -P (g x)) y a b) : ∀ t ∈ Icc a b, ℒ (y t) ≤ ℒ (y a) :=
  hy.energy_le_gradFlow hP hℒ

/-- **Energy decay of the low-rank heavy-ball flow** (Schotthöfer–Klein–Kusch, arXiv 2506.17475,
Thm 1, energy part): if `Ẇ = P(t) V` and `V̇ = -γ V - P(t) ∇ℒ(W)` with symmetric `P(t)` (e.g. the
tangent projector `P(W(t))`) and friction `γ ≥ 0`, then the energy `ℒ(W) + ‖V‖²/2` is
nonincreasing; its derivative is `-γ ‖V‖²`. -/
theorem heavyBall_energy_le (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : ℝ → E →L[ℝ] E} (hP : ∀ t u v, ⟪P t u, v⟫ = ⟪u, P t v⟫) {γ : ℝ} (hγ : 0 ≤ γ)
    {W V : ℝ → E} {a b : ℝ} (hWc : ContinuousOn W (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hW : ∀ t ∈ Ico a b, HasDerivWithinAt W (P t (V t)) (Ici t) t)
    (hV : ∀ t ∈ Ico a b, HasDerivWithinAt V (-(γ • V t) - P t (g (W t))) (Ici t) t) :
    ∀ t ∈ Icc a b, ℒ (W t) + ‖V t‖ ^ 2 / 2 ≤ ℒ (W a) + ‖V a‖ ^ 2 / 2 := by
  have hc : ContinuousOn (fun s => ℒ (W s) + ‖V s‖ ^ 2 / 2) (Icc a b) :=
    ((continuous_of_hasFDerivAt_innerSL hℒ).comp_continuousOn hWc).add
      ((hVc.norm.pow 2).div_const 2)
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => ℒ (W s) + ‖V s‖ ^ 2 / 2)
      (-(γ * ‖V t‖ ^ 2)) (Ici t) t := by
    intro t ht
    have h1 := hasDerivWithinAt_energy_comp hℒ (hW t ht)
    have h2 := ((hV t ht).norm_sq).div_const 2
    refine (h1.add h2).congr_deriv ?_
    rw [inner_sub_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
      ← hP t, real_inner_comm (V t) (P t (g (W t)))]
    ring
  have h := image_le_of_deriv_right_le_deriv_boundary hc hd
    (B := fun _ => ℒ (W a) + ‖V a‖ ^ 2 / 2) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun t _ => hasDerivWithinAt_const _ _ _) fun t _ => by nlinarith [sq_nonneg ‖V t‖]
  exact fun t ht => h ht

/-- **Naive factor-wise momentum can stall away from Riemannian stationarity**
(Schotthöfer–Klein–Kusch, arXiv 2506.17475, Thm 4, algebraic core of the counterexample): with
vanishing momentum the naive update direction is `P̂ ∇ℒ = U Uᵀ ∇ℒ V Vᵀ = L (R ∇ℒ)`; if
`L ∇ℒ = 0` (`Uᵀ ∇ℒ = 0`), then `P̂ ∇ℒ = 0` while the tangent gradient is
`P(W) ∇ℒ = R ∇ℒ = ∇ℒ V Vᵀ`, nonzero whenever `∇ℒ V ≠ 0`. -/
theorem naiveMomentum_apply_eq_zero_of_left {L R : E →L[ℝ] E} (hc : ∀ x, L (R x) = R (L x))
    {v : E} (hv : L v = 0) : L (R v) = 0 ∧ tangent L R v = R v := by
  have h : L (R v) = 0 := by rw [hc, hv, map_zero]
  refine ⟨h, ?_⟩
  rw [tangent_apply, hv, h, zero_add, sub_zero]

end Flow

/-! ### Conditioning of the coefficient matrix -/

section Conditioning

/-- **Best multiple of a fixed element** (orthogonality relation (28) of arXiv 2505.08022): with
`c₀ = ⟪A, e⟫ / ‖e‖²`, the residual `A - c₀ e` is orthogonal to `e`.  For `A = SᵀS`, `e = I_r`
(Frobenius inner product) `c₀ = ‖S‖² / r = α_S²`. -/
lemma inner_sub_bestMultiple_eq_zero (A e : E) (he : e ≠ 0) :
    ⟪A - (⟪A, e⟫ / ‖e‖ ^ 2) • e, e⟫ = 0 := by
  have : ‖e‖ ^ 2 ≠ 0 := by positivity
  rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  field_simp
  ring

/-- Pythagoras for multiples of `e`:
`‖A - c e‖² = ‖A - c₀ e‖² + (c - c₀)² ‖e‖²` with `c₀ = ⟪A, e⟫ / ‖e‖²`. -/
lemma norm_sub_smul_sq_eq_add (A e : E) (he : e ≠ 0) (c : ℝ) :
    ‖A - c • e‖ ^ 2 =
      ‖A - (⟪A, e⟫ / ‖e‖ ^ 2) • e‖ ^ 2 + (c - ⟪A, e⟫ / ‖e‖ ^ 2) ^ 2 * ‖e‖ ^ 2 := by
  set c₀ := ⟪A, e⟫ / ‖e‖ ^ 2
  have h0 := inner_sub_bestMultiple_eq_zero A e he
  have hd : A - c • e = (A - c₀ • e) - (c - c₀) • e := by module
  rw [hd, norm_sub_sq_real, inner_smul_right, h0, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **The scale of the conditioning constraint is the best constant approximation**
(Schotthöfer et al., arXiv 2306.01485, §4: `s² = argmin_α ‖SᵀS - α² I‖_F`, the second moment of
the singular values; Definition 1 of arXiv 2505.08022): `‖A - c₀ e‖ ≤ ‖A - c e‖` for all `c`. -/
theorem norm_sub_bestMultiple_le (A e : E) (c : ℝ) :
    ‖A - (⟪A, e⟫ / ‖e‖ ^ 2) • e‖ ≤ ‖A - c • e‖ := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have h := norm_sub_smul_sq_eq_add A e he c
  have : 0 ≤ (c - ⟪A, e⟫ / ‖e‖ ^ 2) ^ 2 * ‖e‖ ^ 2 := by positivity
  exact abs_le_of_sq_le_sq' (by nlinarith) (norm_nonneg _) |>.2

/-- The minimal residual: `‖A - c₀ e‖² = ‖A‖² - ⟪A, e⟫² / ‖e‖²`; for `A = SᵀS`, `e = I_r` this is
`R(S)² = ‖SᵀS‖² - ‖S‖⁴ / r`, the identity used in eqs. (26) and (38) of arXiv 2505.08022. -/
lemma norm_sub_bestMultiple_sq (A e : E) (he : e ≠ 0) :
    ‖A - (⟪A, e⟫ / ‖e‖ ^ 2) • e‖ ^ 2 = ‖A‖ ^ 2 - ⟪A, e⟫ ^ 2 / ‖e‖ ^ 2 := by
  have h := norm_sub_smul_sq_eq_add A e he 0
  rw [zero_smul, sub_zero] at h
  have : ‖e‖ ^ 2 ≠ 0 := by positivity
  rw [h]; field_simp; ring

/-- **Conditioning tolerance of the constrained low-rank training** (arXiv 2306.01485, §4 and
Algorithm 1, line 8): if all singular values lie in `[s - ε, s + ε]` with `ε = τ s / (2 + τ)`,
`s > 0`, `τ ≥ 0`, the ratio of any two of them (in particular `cond₂(W) = σ_max / σ_min`) is at
most `(s + ε) / (s - ε) = 1 + τ`. -/
theorem div_le_one_add_of_mem_Icc {s τ σ₁ σ₂ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ)
    (h₁ : σ₁ ∈ Icc (s - τ * s / (2 + τ)) (s + τ * s / (2 + τ)))
    (h₂ : σ₂ ∈ Icc (s - τ * s / (2 + τ)) (s + τ * s / (2 + τ))) :
    σ₁ / σ₂ ≤ 1 + τ := by
  have h2τ : 0 < 2 + τ := by linarith
  have hlow : s - τ * s / (2 + τ) = 2 * s / (2 + τ) := by field_simp; ring
  have hup : s + τ * s / (2 + τ) = 2 * s * (1 + τ) / (2 + τ) := by field_simp; ring
  rw [hlow, hup] at h₁ h₂
  have hpos : 0 < 2 * s / (2 + τ) := by positivity
  have hσ₂ : 0 < σ₂ := hpos.trans_le h₂.1
  rw [div_le_iff₀ hσ₂]
  have := h₁.2
  have h3 : 2 * s * (1 + τ) / (2 + τ) = (1 + τ) * (2 * s / (2 + τ)) := by ring
  rw [h3] at this
  nlinarith [h₂.1]

end Conditioning

/-! ### Long-time stability of the robustness regulariser -/

section RobustDLRT

/-- **Long-time stability of the regularised least-squares flow**, sharp form of
Schotthöfer–Kusch et al., arXiv 2505.08022, Prop. 3: let `R : E → ℝ` be continuous and let the
field `r` (the gradient `∇R(S) = 2 S (SᵀS - α_S² I) / R(S)` of the regulariser) satisfy
`⟪r(S), S⟫ = 2 R(S)` (eq. (39)) and `‖r(S)‖ ≤ 2 ‖S‖` (eq. (40)).  Then every solution of
`Ṡ + β r(S) + S = M` on `[0, T]` with `β ≥ 0` satisfies, for `t ∈ [0, T]`,
`½‖S(t) - M‖² + 2β ∫₀ᵗ e^{τ-t} R(S(τ)) dτ ≤ ½ e^{-t} ‖S(0) - M‖² + 2(1 - e^{-t}) β (1 + β) ‖M‖²`.
Only the two identities of `r` are used, so `r` may be any selection of `∇R` where `R` is not
differentiable. -/
theorem robustDLRT_stability_sharp {R : E → ℝ} {r : E → E} {M : E} {β T : ℝ} (hβ : 0 ≤ β)
    (hRc : Continuous R) (hrS : ∀ S, ⟪r S, S⟫ = 2 * R S) (hr : ∀ S, ‖r S‖ ≤ 2 * ‖S‖)
    {S : ℝ → E} (hS : ODESolution (fun _ S => M - S - β • r S) S 0 T) :
    ∀ t ∈ Icc 0 T, ‖S t - M‖ ^ 2 / 2 + 2 * β * ∫ τ in (0 : ℝ)..t, Real.exp (τ - t) * R (S τ) ≤
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) + 2 * (1 - Real.exp (-t)) * β * (1 + β) * ‖M‖ ^ 2 := by
  set f : ℝ → ℝ := fun τ => Real.exp τ * R (S τ) with hf
  set C : ℝ := 2 * β * (1 + β) * ‖M‖ ^ 2 with hC
  have hfc : ContinuousOn f (Icc 0 T) :=
    Real.continuous_exp.continuousOn.mul (hRc.comp_continuousOn hS.cont)
  have hint : ContinuousOn (fun t => ∫ τ in (0 : ℝ)..t, f τ) (Icc 0 T) := by
    rcases le_total 0 T with h0T | hT0
    · have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
        (f := f) (a := 0) (b := T) (by rw [uIcc_of_le h0T]; exact hfc.integrableOn_Icc)
      rwa [uIcc_of_le h0T] at this
    · rcases hT0.eq_or_lt with rfl | hlt
      · simp [continuousOn_singleton]
      · simp [Icc_eq_empty_of_lt hlt]
  set φ : ℝ → ℝ := fun t => Real.exp t * (‖S t - M‖ ^ 2 / 2) + 2 * β * ∫ τ in (0 : ℝ)..t, f τ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    (Real.continuous_exp.continuousOn.mul (((hS.cont.sub continuousOn_const).norm.pow 2).div_const
      2)).add (hint.const_smul (2 * β))
  have hφd : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ
      (Real.exp t * (‖S t - M‖ ^ 2 / 2) +
        Real.exp t * (2 * ⟪S t - M, M - S t - β • r (S t)⟫ / 2) + 2 * β * f t) (Ici t) t := by
    intro t ht
    have hmem : Icc 0 T ∈ nhdsWithin t (Ioi t) :=
      Filter.mem_of_superset (Icc_mem_nhdsGT ht.2) (Icc_subset_Icc_left ht.1)
    have hI : HasDerivWithinAt (fun u => ∫ τ in (0 : ℝ)..u, f τ) (f t) (Ici t) t :=
      intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t)
        ((hfc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1)
        ((hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t).filter_mono
          (nhdsWithin_le_of_mem hmem))
        ((hfc t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin hmem)
    have hu := (((hS.deriv t ht).sub_const M).norm_sq).div_const 2
    have he := (Real.hasDerivAt_exp t).hasDerivWithinAt (s := Ici t)
    exact ((he.mul hu).add (hI.const_mul (2 * β))).congr_deriv (by ring)
  have key := image_le_of_deriv_right_le_deriv_boundary hφc hφd
    (B := fun t => ‖S 0 - M‖ ^ 2 / 2 + C * (Real.exp t - 1)) (B' := fun t => C * Real.exp t)
    (by simp [φ]) (Continuous.continuousOn (by fun_prop))
    (fun t _ => by
      simpa using (((Real.hasDerivAt_exp t).hasDerivWithinAt.sub_const 1).const_mul C).const_add
        (‖S 0 - M‖ ^ 2 / 2))
    (fun t _ => by
      set x := S t
      set D := ‖x - M‖ with hD
      have e1 : ⟪x - M, M - x - β • r x⟫ = -D ^ 2 - 2 * β * R x + β * ⟪r x, M⟫ := by
        have : M - x - β • r x = -(x - M) - β • r x := by abel
        rw [this, inner_sub_right, inner_neg_right, real_inner_self_eq_norm_sq, inner_smul_right,
          inner_sub_left, real_inner_comm (r x) x, hrS, real_inner_comm (r x) M, hD]
        ring
      have h1 : ⟪r x, M⟫ ≤ ‖r x‖ * ‖M‖ := real_inner_le_norm _ _
      have h2 : ‖x‖ ≤ D + ‖M‖ := by
        calc ‖x‖ = ‖(x - M) + M‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖r x‖ * ‖M‖ ≤ 2 * (D + ‖M‖) * ‖M‖ :=
        mul_le_mul_of_nonneg_right ((hr x).trans (by linarith)) (norm_nonneg _)
      have h4 : β * ⟪r x, M⟫ ≤ β * (2 * (D + ‖M‖) * ‖M‖) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) hβ
      have h5 : 2 * β * D * ‖M‖ ≤ D ^ 2 / 2 + 2 * β ^ 2 * ‖M‖ ^ 2 := by
        nlinarith [sq_nonneg (D - 2 * β * ‖M‖)]
      have h6 : -(D ^ 2 / 2) + β * ⟪r x, M⟫ ≤ C := by rw [hC]; nlinarith
      have e2 : Real.exp t * (D ^ 2 / 2) + Real.exp t * (2 * ⟪x - M, M - x - β • r x⟫ / 2) +
          2 * β * f t = Real.exp t * (-(D ^ 2 / 2) + β * ⟪r x, M⟫) := by
        rw [e1, hf]; ring
      rw [e2, mul_comm C]
      exact mul_le_mul_of_nonneg_left h6 (Real.exp_pos t).le)
  intro t ht
  have h1 := key ht
  simp only [φ] at h1
  have hfun : (fun τ => Real.exp (τ - t) * R (S τ)) = fun τ => Real.exp (-t) * f τ := by
    funext τ; rw [hf, sub_eq_add_neg, Real.exp_add]; ring
  rw [hfun, intervalIntegral.integral_const_mul]
  set I := ∫ τ in (0 : ℝ)..t, f τ
  have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-t)).le
  have hee : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have e2 : Real.exp (-t) * (Real.exp t * (‖S t - M‖ ^ 2 / 2) + 2 * β * I) =
      ‖S t - M‖ ^ 2 / 2 + 2 * β * (Real.exp (-t) * I) := by
    linear_combination (‖S t - M‖ ^ 2 / 2) * hee
  have e3 : Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2 + C * (Real.exp t - 1)) =
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) + 2 * (1 - Real.exp (-t)) * β * (1 + β) * ‖M‖ ^ 2 := by
    rw [hC]; linear_combination (2 * β * (1 + β) * ‖M‖ ^ 2) * hee
  rw [e2, e3] at hmul
  exact hmul

/-- **Long-time stability of the regularised flow** (arXiv 2505.08022, Prop. 3, eq. (5), with the
paper's constant `2 (1 - e^{-t}) β (1 + 2β) ‖M‖²`); see `robustDLRT_stability_sharp`. -/
theorem robustDLRT_stability {R : E → ℝ} {r : E → E} {M : E} {β T : ℝ} (hβ : 0 ≤ β)
    (hRc : Continuous R) (hrS : ∀ S, ⟪r S, S⟫ = 2 * R S) (hr : ∀ S, ‖r S‖ ≤ 2 * ‖S‖)
    {S : ℝ → E} (hS : ODESolution (fun _ S => M - S - β • r S) S 0 T) :
    ∀ t ∈ Icc 0 T, ‖S t - M‖ ^ 2 / 2 + 2 * β * ∫ τ in (0 : ℝ)..t, Real.exp (τ - t) * R (S τ) ≤
      Real.exp (-t) * (‖S 0 - M‖ ^ 2 / 2) +
        2 * (1 - Real.exp (-t)) * β * (1 + 2 * β) * ‖M‖ ^ 2 := by
  intro t ht
  refine (robustDLRT_stability_sharp hβ hRc hrS hr hS t ht).trans ?_
  have h1 : 0 ≤ 1 - Real.exp (-t) := by
    rw [sub_nonneg]; exact Real.exp_le_one_iff.2 (by linarith [ht.1])
  have h2 : 0 ≤ 2 * (1 - Real.exp (-t)) * β * ‖M‖ ^ 2 := by positivity
  nlinarith

end RobustDLRT

/-! ### Examples: the hypotheses are jointly satisfiable -/

section Examples

omit [InnerProductSpace ℝ E] in
/-- The quadratic loss `ℒ = ‖·‖² / 2` has the `1`-Lipschitz gradient `id`. -/
lemma lipschitz_id_grad (x y : E) : ‖id x - id y‖ ≤ 1 * ‖x - y‖ := by simp

/-- The descent lemma for the quadratic loss (where it is an equality). -/
example (x y : E) :
    ‖y‖ ^ 2 / 2 ≤ ‖x‖ ^ 2 / 2 + ⟪id x, y - x⟫ + 1 / 2 * ‖y - x‖ ^ 2 :=
  descent_lemma (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq lipschitz_id_grad x y

/-- Exact gradient descent `x_k = (1/2)^k x₀` on `ℒ = ‖·‖²/2` with `Π = 1`, `h = 1/2`, `β = 1`
satisfies all hypotheses of `exists_projGrad_sq_le_of_exact`. -/
example (x₀ : E) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖(1 : E →L[ℝ] E) (id ((1 / 2 : ℝ) ^ k • x₀))‖ ^ 2 ≤
      (‖(1 / 2 : ℝ) ^ 0 • x₀‖ ^ 2 / 2 - 0) / (n * (1 / 2 * (1 - 1 * (1 / 2) / 2))) := by
  refine exists_projGrad_sq_le_of_exact (ℒ := fun x : E => ‖x‖ ^ 2 / 2)
    (x := fun k => (1 / 2 : ℝ) ^ k • x₀) hasFDerivAt_half_norm_sq lipschitz_id_grad
    (fun _ => IsOrthProj.one) (fun k => ?_) (fun k => by positivity) (by norm_num) hn
  simp only [projGradStep, one_apply_eq_self, pow_succ]
  module

/-- One FeDLRT round with two identical clients on the quadratic loss satisfies the hypotheses of
`loss_fedRound_le`. -/
example (x : E) :
    ‖fedRound (1 : E →L[ℝ] E) (fun _ : Fin 2 => id) id (1 / 24) 1 x‖ ^ 2 / 2 ≤
      ‖x‖ ^ 2 / 2 - (1 : ℕ) * (1 / 24) * (1 - 12 * ((1 : ℕ) * (1 / 24)) * 1) *
        ‖(1 : E →L[ℝ] E) (id x)‖ ^ 2 :=
  loss_fedRound_le (ℒ := fun x : E => ‖x‖ ^ 2 / 2) hasFDerivAt_half_norm_sq lipschitz_id_grad
    (fun _ => lipschitz_id_grad) IsOrthProj.one zero_le_one (by norm_num) (by norm_num) x

/-- A FeDLRT round with one client, one local step, `Π = 1` and `∇ℒ = id` is `x ↦ (1 - λ) x`. -/
lemma fedRound_one_id_unit (lr : ℝ) (x : E) :
    fedRound (1 : E →L[ℝ] E) (fun _ : Unit => id) (fun x : E => x) lr 1 x = (1 - lr) • x := by
  simp [fedRound, fedClientIter, sub_smul]

/-- A FeDLRT run on `ℒ = ‖·‖²/2` that truncates to rank zero after the first round
(`x₀ = v`, `x_k = 0` for `k ≥ 1`) satisfies all hypotheses of `exists_fedGrad_sq_le_of_lr`, with
truncation tolerance `ϑ = ‖v‖` and gradient bound `G = ‖v‖`. -/
example (v : E) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, ‖(1 : E →L[ℝ] E) (id (if k = 0 then v else 0))‖ ^ 2 ≤
      48 * 1 / n * (‖if 0 = 0 then v else 0‖ ^ 2 / 2 - ‖if n = 0 then v else (0 : E)‖ ^ 2 / 2) +
        48 * 1 * ‖v‖ * ‖v‖ := by
  refine exists_fedGrad_sq_le_of_lr (ℒ := fun x : E => ‖x‖ ^ 2 / 2) (ι := Unit) (sstar := 1)
    (lr := 1 / 24) (x := fun k => if k = 0 then v else 0) hasFDerivAt_half_norm_sq
    lipschitz_id_grad (fun _ => lipschitz_id_grad) (fun _ => IsOrthProj.one) one_pos
    (by norm_num) (by norm_num) (fun k => ?_) (fun k w hw => ?_) hn
  · rw [fedRound_one_id_unit]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.zero_add, one_ne_zero, ite_false, ite_true, zero_sub, norm_neg, norm_smul]
      norm_num
      nlinarith [norm_nonneg v]
    · simp [hk.ne', norm_nonneg]
  · rw [fedRound_one_id_unit] at hw
    have hball : segment ℝ ((1 - 1 / 24 : ℝ) • (if k = 0 then v else 0))
        (if k + 1 = 0 then v else 0) ⊆ Metric.closedBall (0 : E) ‖v‖ := by
      refine (convex_closedBall (0 : E) ‖v‖).segment_subset ?_ ?_
      · rw [mem_closedBall_zero_iff, norm_smul]
        split_ifs <;> norm_num
        nlinarith [norm_nonneg v]
      · simp
    simpa using hball hw

/-- With `P₀ = T`, `Q₀ = 1 - T`, `P̃ = 1 - T`, `Q̃ = T` for an orthogonal projector `T`, all
relations of a GeoLoRA step hold, for every gradient `v`. -/
lemma isGeoLoRABases_compl {T : E →L[ℝ] E} (hT : IsOrthProj T) (v : E) :
    IsGeoLoRABases T (1 - T) (1 - T) T v where
  orthProj_left := hT
  orthProj_right := hT.compl
  comm x := by simp [hT.idem]
  comm_aug _ := rfl
  left_orth x := by simp [hT.idem]
  right_orth x := by simp [hT.idem]
  left_capture := by simp [hT.idem]
  right_capture := by simp [hT.idem]

/-- In the configuration of `isGeoLoRABases_compl` the tangent projector is the identity and the
GeoLoRA step is the full gradient step. -/
example {T : E →L[ℝ] E} (hT : IsOrthProj T) (g : E → E) (lr : ℝ) (w : E) :
    geoLoRAStep T (1 - T) (1 - T) T g lr w = w - lr • g w := by
  rw [geoLoRAStep_eq (isGeoLoRABases_compl hT (g w)), projGradStep]
  simp [hT.idem]

/-- The negative result on spectral contraction applies to the trivial projector `P = 0` and any
orthogonal projector `Q ≠ 1`. -/
example {T : E →L[ℝ] E} (hT : IsOrthProj T) {y : E} (hy : T y ≠ y) :
    ∃ x, ¬ ∃ γ < 1, ‖x - T x‖ ≤ γ * ‖x - (0 : E →L[ℝ] E) x‖ :=
  not_exists_contraction_of_absorbs IsOrthProj.zero hT (fun x => by simp) ⟨y, hy⟩

/-- The hypotheses of `robustDLRT_stability` hold for the Tikhonov-type regulariser
`R(S) = ‖S‖²` with `r(S) = 2 S`, `β = 1`, `M = 0` and the solution `S(t) = e^{-3t} S₀`. -/
example (S₀ : E) (T : ℝ) :
    ∀ t ∈ Icc 0 T, ‖Real.exp (-(3 * t)) • S₀ - 0‖ ^ 2 / 2 +
        2 * 1 * ∫ τ in (0 : ℝ)..t, Real.exp (τ - t) * ‖Real.exp (-(3 * τ)) • S₀‖ ^ 2 ≤
      Real.exp (-t) * (‖Real.exp (-(3 * 0)) • S₀ - 0‖ ^ 2 / 2) +
        2 * (1 - Real.exp (-t)) * 1 * (1 + 2 * 1) * ‖(0 : E)‖ ^ 2 := by
  have hS : ODESolution (fun _ S => (0 : E) - S - (1 : ℝ) • (2 : ℝ) • S)
      (fun t => Real.exp (-(3 * t)) • S₀) 0 T := by
    refine ⟨Continuous.continuousOn (by fun_prop), fun t _ => ?_⟩
    have h := ((((hasDerivAt_id t).const_mul 3).neg).exp.smul_const S₀).hasDerivWithinAt
      (s := Ici t)
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    module
  exact robustDLRT_stability (R := fun S : E => ‖S‖ ^ 2) (r := fun S => (2 : ℝ) • S)
    zero_le_one (by fun_prop)
    (fun S => by rw [inner_smul_left, real_inner_self_eq_norm_sq]; simp)
    (fun S => by rw [norm_smul]; simp) hS

/-- The configuration of `naiveMomentum_apply_eq_zero_of_left` occurs: for `L = T`, `R = 1 - T`
and `v = (1 - T) y` with `T y ≠ y`, the naive direction vanishes but the tangent gradient does
not. -/
example {T : E →L[ℝ] E} (hT : IsOrthProj T) {y : E} (hy : T y ≠ y) :
    T ((1 - T) (y - T y)) = 0 ∧ tangent T (1 - T) (y - T y) ≠ 0 := by
  have hc : ∀ x, T ((1 - T) x) = (1 - T) (T x) := fun x => by simp [hT.idem]
  have hv : T (y - T y) = 0 := by simp [hT.idem]
  obtain ⟨h1, h2⟩ := naiveMomentum_apply_eq_zero_of_left hc hv
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [sub_apply, one_apply_eq_self, hv, sub_zero]
  exact sub_ne_zero.2 (Ne.symm hy)

end Examples

end LeanDLRA
