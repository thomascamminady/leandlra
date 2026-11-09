import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Training.GradientFlowConvergence
import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2409.04206: Fast Forward low-rank (LoRA) training

Rahamim, Saphra, Kangaslahti and Belinkov, *Fast Forwarding Low-Rank Training*. The paper states
**no theorem**: it defines a procedure (Sec. 3: `Δ_W = W_t - W_{t-1}`, Eq. (2), then `W_t + τ Δ_W`
for `τ = 1, 2, …` until the loss on a tiny validation set stops improving, alternated with
`T_interval = 6` Adam steps) and reports measurements. This module formalizes the procedure
(`ffDir`, `ffPoint`, the stopping rule `IsFFStop`, the training loop `IsFFRun`, and for Eq. (1),
`W = W₀ + B A`, the stage on the factors `loraFF`) and proves the mathematical content of its
claims. For a `β`-smooth loss and `s = ⟪∇L(W), d⟫ < 0`: the line-search core `loss_ffPoint_lt` (a
corollary of `LeanDLRA.descent_lemma`), the per-step threshold `loss_ffStep_lt`, and the two-sided
bound `|s| / (β ‖d‖²) - 1/2 ≤ k ≤ |s| / (μ ‖d‖²) + 1/2` on the stage length (`ffStop_ge`,
`ffStop_le`); the gain `loss_ffStop_le_sub`; Appendix B's identification of the vertex under
convexity (`IsFFStop.le_nat_of_convexOn`, `IsFFStop.exists_vertex`, `loss_ffStop_le_add`,
`exists_isFFStop_of_isMinOn`); near-orthogonality of the next gradient, Sec. 6.1 and Fig. 6
(`abs_inner_grad_ffStop_le`, `abs_cosSim_ffStop_le`, `abs_cosSim_grad_ffStop_le`, against
`cosSim_regularStep_ge`); descent and stage length derived, not assumed, after a preconditioned or
gradient step (`inner_grad_le_of_align`, `ffStop_ge_of_precondStep`, `ffStop_ge_of_projGradStep`,
`loss_ffStage_le`); the exact vertex on quadratics, governed by curvature and not by the gradient
norm, Fig. 12a (`abs_quad_ffStop_sub_vertex_le`, `quad_vertex_gradStep`, `rayleigh_smul`,
`quad_ffStop_zero_iff`); for the loop, "FF does not harm" (`IsFFRun.exists_grad_sq_le`) and a rate
independent of the learning rate (`IsFFRun.exists_grad_sq_le_of_stage`); for LoRA, preservation of
the rank (`rank_loraFF_sub_le`, against `exists_weightFF_rank_two`) and stage lengths growing like
`1 / h` (`lora_ffStop_ge`, `lora_ffStop_ge_of_factorStep`, `exists_lr_lora_ffStop_ge`), which need
their own proof since the loss of the factors is not globally smooth.

**A false claim.**  The survey entry of this paper and OP-TR-27 (i) say that repeating the step
keeps decreasing `L` while `τ < 2 |s| / (β ‖d‖²)`, resp. that at least `⌊2 |s| / (β ‖d‖²)⌋` steps
decrease the loss. This is true against the *starting* loss (`loss_ffPoint_lt`) and false per step
(`exists_ffStep_increase_below_threshold`), so the rule of the paper may stop at half that number;
the sharp per-step threshold is `τ + 1/2 < |s| / (β ‖d‖²)`.

**Differences from the paper, and from OP-TR-27.**  The stopping rule is worded in two ways in the
paper (loss "stops improving", loss "increases"); `IsFFStop` covers both. The paper does not say
which iterate is kept: we keep the last good one, and `loss_ffStop_overshoot_le` bounds the cost of
the other choice. Convexity along the direction is an observation in the paper (Appendix B, Fig. 10)
and a hypothesis here; it does not give termination (`not_isFFStop_exp`). The constants `β ‖d‖² / 8`
and `β ‖d‖² / 2` improve the `β ‖d‖² / 2` and `β ‖d‖²` of OP-TR-27 (ii), (iii) and are sharp
(`ffStop_bounds_sharp`). Everything is deterministic; the validation loss `V` is any function, and
`|V - L| ≤ δ` enters as a hypothesis.

**Not formalized.**  The measured savings (41–87% of FLOPs, 40–81% of time) and the benchmark
accuracies are data, not statements. Adam's momentum is not covered: its update need not be a
descent direction, so the theorems on a general direction `d` assume `s < 0`, and the derived ones
use project–precondition–project steps or exact gradient steps. DoRA (no equation in the paper), the
flatness of the point reached (Fig. 5), the permanent switch to Adam of Sec. 5.1 and the failure at
full rank (Fig. 8; Sec. 6 rejects two hypotheses and concludes that the difference is due to the
projection matrices added by LoRA; `quad_ffStop_zero_iff` only gives a condition on quadratics) are
not treated.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2409_04206

open LeanDLRA

/-! ### The stopping rule -/

/-- `k` is a **stopping index** of a Fast Forward stage whose validation losses are
`v 0, v 1, v 2, …` (`v j` is the loss after `j` simulated steps): the stage reached `k` without
the loss going up, and step `k + 1` does not improve the loss.  arXiv 2409.04206 words the rule
in two ways ("until the loss stops improving", abstract and Fig. 1; "causes this validation loss
to increase", Sec. 3).  `IsFFStop` is the common weakening, so that every theorem about it covers
both; see `isFFStop_find_improve` and `isFFStop_find_increase`. -/
def IsFFStop (v : ℕ → ℝ) (k : ℕ) : Prop :=
  (∀ j < k, v (j + 1) ≤ v j) ∧ v k ≤ v (k + 1)

/-- The rule of Fig. 1 of arXiv 2409.04206 ("did loss improve? No: exit"): the first index at which
the next step does not strictly improve the loss is a stopping index.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem isFFStop_find_improve {v : ℕ → ℝ} [DecidablePred fun k => v k ≤ v (k + 1)]
    (h : ∃ k, v k ≤ v (k + 1)) : IsFFStop v (Nat.find h) :=
  ⟨fun _ hj => (not_le.1 (Nat.find_min h hj)).le, Nat.find_spec h⟩

/-- The rule of Sec. 3 of arXiv 2409.04206 ("causes this validation loss to increase"): the first
index at which the next step strictly increases the loss is a stopping index.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem isFFStop_find_increase {v : ℕ → ℝ} [DecidablePred fun k => v k < v (k + 1)]
    (h : ∃ k, v k < v (k + 1)) : IsFFStop v (Nat.find h) :=
  ⟨fun _ hj => not_lt.1 (Nat.find_min h hj), (Nat.find_spec h).le⟩

/-- A stage can only lower the loss: the iterate kept at a stopping index is at least as good as
all earlier iterates.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.le_of_le {v : ℕ → ℝ} {k : ℕ} (hk : IsFFStop v k) {j : ℕ} (hj : j ≤ k) :
    v k ≤ v j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h := hk.1
  clear hk hj
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (h (j + i) (by omega)).trans (ih fun m hm => h m (by omega))

/-- If the stage ever fails to beat its starting loss, then it has stopped before.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_isFFStop_of_le {v : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (h : v 0 ≤ v n) :
    ∃ k < n, IsFFStop v k := by
  classical
  have hex : ∃ k, v k ≤ v (k + 1) := by
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    have hanti : ∀ m, v (m + 1) < v 0 := by
      intro m
      induction m with
      | zero => exact hcon 0
      | succ m ih => exact (hcon (m + 1)).trans ih
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact absurd h (not_le.2 (hanti m))
  refine ⟨Nat.find hex, ?_, isFFStop_find_improve hex⟩
  by_contra hcon
  have hnk : n ≤ Nat.find hex := not_lt.1 hcon
  have hlt : ∀ m, m < Nat.find hex → v (m + 1) < v m := fun m hm =>
    not_le.1 (Nat.find_min hex hm)
  have hanti : ∀ m, m + 1 ≤ Nat.find hex → v (m + 1) < v 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hlt 0 (by omega)
    | succ m ih => exact fun hm => (hlt (m + 1) (by omega)).trans (ih (by omega))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact absurd h (not_le.2 (hanti m hnk))

/-- A Fast Forward stage need not terminate, even for a smooth convex loss that is bounded below:
along `φ(τ) = exp(-τ)` every step improves.  So the vertex that Appendix B of arXiv 2409.04206
searches for has to exist; compare `exists_isFFStop_of_isMinOn`. -/
theorem not_isFFStop_exp (k : ℕ) : ¬ IsFFStop (fun j : ℕ => Real.exp (-(j : ℝ))) k := by
  intro h
  have h2 := h.2
  simp only [Nat.cast_add, Nat.cast_one, Real.exp_le_exp] at h2
  linarith

/-! ### Second-order calculus on a line -/

section Line

variable {s : Set ℝ} {φ φ' : ℝ → ℝ} {κ μ : ℝ}

private lemma le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (h : ∀ t ∈ Icc a b, 0 ≤ f' t) : f a ≤ f b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t (Ioo_subset_Icc_self ht))
  have h1 := h c (Ioo_subset_Icc_self hc)
  rw [hc', le_div_iff₀ (sub_pos.2 hab)] at h1
  linarith

/-- Second-order upper bound on an interval `s` on which `φ'` is `κ`-Lipschitz.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem line_le (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    φ y ≤ φ x + φ' x * (y - x) + κ / 2 * (y - x) ^ 2 := by
  have hψ : ∀ t ∈ s, HasDerivAt (fun t => φ x + φ' x * (t - x) + κ / 2 * (t - x) ^ 2 - φ t)
      (φ' x + κ * (t - x) - φ' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t - x) 1 t := (hasDerivAt_id' t).sub_const x
    have h2 := (((h1.const_mul (φ' x)).const_add (φ x)).add
      ((h1.pow 2).const_mul (κ / 2))).sub (hφ t ht)
    refine h2.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  rcases le_total x y with hxy | hyx
  · have h := le_of_hasDerivAt_nonneg hxy
      (fun t ht => hψ t (hs.out hx hy ht)) (fun t ht => by
        have h1 := hκ t (hs.out hx hy ht) x hx
        rw [abs_of_nonneg (sub_nonneg.2 ht.1)] at h1
        have h2 := (abs_le.1 h1).2
        linarith)
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    linarith
  · have h := le_of_hasDerivAt_nonneg hyx (f := fun t => -(φ x + φ' x * (t - x) +
      κ / 2 * (t - x) ^ 2 - φ t)) (f' := fun t => -(φ' x + κ * (t - x) - φ' t))
      (fun t ht => (hψ t (hs.out hy hx ht)).neg) (fun t ht => by
        have h1 := hκ x hx t (hs.out hy hx ht)
        rw [abs_of_nonneg (sub_nonneg.2 ht.2)] at h1
        have h2 := (abs_le.1 h1).2
        linarith)
    simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    linarith

/-- Second-order lower bound on an interval `s` on which `φ'` is `κ`-Lipschitz.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem le_line (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    φ x + φ' x * (y - x) - κ / 2 * (y - x) ^ 2 ≤ φ y := by
  have h := line_le (φ := fun t => -φ t) (φ' := fun t => -φ' t) hs (fun t ht => (hφ t ht).neg)
    (fun a ha b hb => by
      have e : -φ' a - -φ' b = -(φ' a - φ' b) := by ring
      rw [e, abs_neg]
      exact hκ a ha b hb) hx hy
  linarith

/-- Strong convexity on `s`: if `φ'` grows at rate at least `μ`, then
`φ y ≥ φ x + φ'(x) (y - x) + μ/2 (y - x)²` for `x ≤ y`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem le_line_of_strong (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hμ : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → μ * (b - a) ≤ φ' b - φ' a) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≤ y) : φ x + φ' x * (y - x) + μ / 2 * (y - x) ^ 2 ≤ φ y := by
  have hψ : ∀ t ∈ s, HasDerivAt (fun t => φ t - (φ' x * (t - x) + μ / 2 * (t - x) ^ 2))
      (φ' t - (φ' x + μ * (t - x))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t - x) 1 t := (hasDerivAt_id' t).sub_const x
    have h2 := (hφ t ht).sub ((h1.const_mul (φ' x)).add ((h1.pow 2).const_mul (μ / 2)))
    refine h2.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h := le_of_hasDerivAt_nonneg hxy (fun t ht => hψ t (hs.out hx hy ht)) (fun t ht => by
    have := hμ x hx t (hs.out hx hy ht) ht.1
    linarith)
  simp only [sub_self, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero] at h
  linarith

/-- One simulated step changes the loss by at most `φ'(0) + κ (τ + 1/2)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem line_step_le (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (h0 : (0 : ℝ) ∈ s) {τ : ℝ}
    (hτ : 0 ≤ τ) (h1 : τ + 1 ∈ s) : φ (τ + 1) ≤ φ τ + φ' 0 + κ * (τ + 1 / 2) := by
  have hτs : τ ∈ s := hs.out h0 h1 ⟨hτ, by linarith⟩
  have h2 := line_le hs hφ hκ hτs h1
  have h3 := hκ τ hτs 0 h0
  rw [sub_zero, abs_of_nonneg hτ] at h3
  have h4 := (abs_le.1 h3).2
  have e : τ + 1 - τ = 1 := by ring
  rw [e] at h2
  linarith

/-- One simulated step changes the loss by at least `φ'(0) + μ (τ + 1/2)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem line_step_ge (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hμ : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → μ * (b - a) ≤ φ' b - φ' a) (h0 : (0 : ℝ) ∈ s) {τ : ℝ}
    (hτ : 0 ≤ τ) (h1 : τ + 1 ∈ s) : φ τ + φ' 0 + μ * (τ + 1 / 2) ≤ φ (τ + 1) := by
  have hτs : τ ∈ s := hs.out h0 h1 ⟨hτ, by linarith⟩
  have h2 := le_line_of_strong hs hφ hμ hτs h1 (by linarith)
  have h3 := hμ 0 h0 τ hτs hτ
  have e : τ + 1 - τ = 1 := by ring
  rw [e] at h2
  linarith

/-! ### The stopping index on a line -/

/-- The cast form of the stopping condition. -/
private lemma IsFFStop.step {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k) : φ k ≤ φ (k + 1) := by
  simpa using hk.2

private lemma IsFFStop.prev {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) (k + 1)) :
    φ (k + 1) ≤ φ k := by
  simpa using hk.1 k k.lt_succ_self

/-- **Lower bound on the stopping index**: `-φ'(0) ≤ κ (k + 1/2)`.  With `κ = β ‖d‖²` this says
`k ≥ |s| / (β ‖d‖²) - 1/2`, for the `s = φ'(0) < 0` of the descent direction.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.neg_deriv_le {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 1 ∈ s) : -φ' 0 ≤ κ * (k + 1 / 2) := by
  have h2 := line_step_le hs hφ hκ h0 (Nat.cast_nonneg k) h1
  have h3 := hk.step
  linarith

/-- **Upper bound on the stopping index**: if `φ'` grows at rate at least `μ ≥ 0` on `s` and
`φ'(0) ≤ 0`, then `μ (k - 1/2) ≤ -φ'(0)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.mul_le_neg_deriv {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hμ : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → μ * (b - a) ≤ φ' b - φ' a) (hμ0 : 0 ≤ μ) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) ∈ s) (hslope : φ' 0 ≤ 0) : μ * (k - 1 / 2) ≤ -φ' 0 := by
  rcases k with _ | n
  · simp only [Nat.cast_zero]
    nlinarith
  · have hn : (n : ℝ) + 1 ∈ s := by simpa using h1
    have h2 := line_step_ge hs hφ hμ h0 (Nat.cast_nonneg n) hn
    have h3 := hk.prev
    push_cast
    nlinarith

/-- **Stationarity along the direction at the stop**: `|φ'(k)| ≤ κ / 2`.  No convexity is needed.
The only use of `φ'(0) ≤ 0` is for `k = 0`, where no earlier iterate is available.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.abs_deriv_le {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 1 ∈ s) (hslope : φ' 0 ≤ 0) : |φ' k| ≤ κ / 2 := by
  have hks : (k : ℝ) ∈ s := hs.out h0 h1 ⟨Nat.cast_nonneg k, by linarith⟩
  have h2 := line_le hs hφ hκ hks h1
  have e : (k : ℝ) + 1 - k = 1 := by ring
  rw [e] at h2
  have h3 := hk.step
  rw [abs_le]
  constructor
  · linarith
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have h6 : φ' k ≤ 0 := by simpa [hk0] using hslope
      linarith
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
      have hns : (n : ℝ) ∈ s := hs.out h0 hks ⟨Nat.cast_nonneg n, by push_cast; linarith⟩
      have h4 := line_le hs hφ hκ hks hns
      have h5 := hk.prev
      have e2 : (n : ℝ) - ((n + 1 : ℕ) : ℝ) = -1 := by push_cast; ring
      rw [e2] at h4
      push_cast at h4 ⊢
      linarith

/-- If the stage keeps the failing iterate `k + 1` instead of `k`, the overshoot costs at most
`κ`.  (Sec. 3 of arXiv 2409.04206 does not say which of the two iterates is kept.)
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.overshoot_le {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 1 ∈ s) (hslope : φ' 0 ≤ 0) : φ (k + 1) ≤ φ k + κ := by
  have hks : (k : ℝ) ∈ s := hs.out h0 h1 ⟨Nat.cast_nonneg k, by linarith⟩
  have h2 := line_le hs hφ hκ hks h1
  have e : (k : ℝ) + 1 - k = 1 := by ring
  rw [e] at h2
  have h3 := (abs_le.1 (hk.abs_deriv_le hs hφ hκ h0 h1 hslope)).2
  linarith

/-- An integer within `1/2` of a real number `c ≥ 0`, below `c + 1/2`, chosen as the ceiling of
`c - 1/2`. -/
private lemma ceil_sub_half_props {c : ℝ} (hc : 0 ≤ c) :
    c - 1 / 2 ≤ (⌈c - 1 / 2⌉₊ : ℝ) ∧ ((⌈c - 1 / 2⌉₊ : ℝ) - c) ^ 2 ≤ 1 / 4 := by
  have h1 : c - 1 / 2 ≤ (⌈c - 1 / 2⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨h1, ?_⟩
  rcases le_or_gt (c - 1 / 2) 0 with h | h
  · have h0 : ⌈c - 1 / 2⌉₊ = 0 := Nat.ceil_eq_zero.2 h
    rw [h0]
    push_cast
    nlinarith
  · have h2 := Nat.ceil_lt_add_one h.le
    nlinarith

/-- **Guaranteed gain of a stage**: for `φ'(0) ≤ 0`, the stage gains as much as the exact line
search on the quadratic model `φ(0) + φ'(0) τ + κ τ²/2`, up to the rounding error `κ/8`:
`φ(k) ≤ φ(0) - φ'(0)²/(2κ) + κ/8`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.le_sub_gain {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (hκ0 : 0 < κ) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 1 ∈ s) (hslope : φ' 0 ≤ 0) :
    φ k ≤ φ 0 - φ' 0 ^ 2 / (2 * κ) + κ / 8 := by
  set c : ℝ := -φ' 0 / κ with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hκ0.le
  have hsl : φ' 0 = -(c * κ) := by rw [hc]; field_simp
  obtain ⟨hj1, hj2⟩ := ceil_sub_half_props hc0
  set j : ℕ := ⌈c - 1 / 2⌉₊ with hj
  have hle := hk.neg_deriv_le hs hφ hκ h0 h1
  have hjk : j ≤ k := by
    refine Nat.ceil_le.2 ?_
    rw [hsl, neg_neg] at hle
    have : c ≤ (k : ℝ) + 1 / 2 := le_of_mul_le_mul_right (by linarith) hκ0
    linarith
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hjs : (j : ℝ) ∈ s := hs.out h0 h1 ⟨Nat.cast_nonneg j, by linarith⟩
  have h2 := line_le hs hφ hκ h0 hjs
  have h3 : φ k ≤ φ j := hk.le_of_le hjk
  have e : φ' 0 ^ 2 / (2 * κ) = κ * c ^ 2 / 2 := by rw [hsl]; field_simp
  rw [e]
  rw [sub_zero, hsl] at h2
  nlinarith [mul_le_mul_of_nonneg_left hj2 hκ0.le]

/-- Version of `IsFFStop.le_sub_gain` for a stage that starts at `τ = 1` on the line through the
previous iterate (`τ = 0`): if `κ < 2 |φ'(0)|` then `φ(k + 1) ≤ φ(0) - φ'(0)²/(2κ) + κ/8`.  This
is the form that applies to the actual procedure: the direction comes from the step `0 → 1`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.le_sub_gain_shift {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ (j + 1 : ℕ)) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (hκ0 : 0 < κ) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 2 ∈ s) (hslope : κ < 2 * -φ' 0) :
    φ (k + 1) ≤ φ 0 - φ' 0 ^ 2 / (2 * κ) + κ / 8 := by
  set c : ℝ := -φ' 0 / κ with hc
  have hc1 : 1 / 2 < c := by
    rw [hc, lt_div_iff₀ hκ0]
    linarith
  have hsl : φ' 0 = -(c * κ) := by rw [hc]; field_simp
  obtain ⟨hj1, hj2⟩ := ceil_sub_half_props (show 0 ≤ c by linarith)
  set j : ℕ := ⌈c - 1 / 2⌉₊ with hj
  have hj0 : 0 < j := Nat.ceil_pos.2 (by linarith)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
  have hk1s : (k : ℝ) + 1 ∈ s := hs.out h0 h1 ⟨by positivity, by linarith⟩
  have h2 := line_step_le hs hφ hκ h0 (τ := (k : ℝ) + 1) (by positivity)
    (by convert h1 using 1; ring)
  have hstop : φ ((k + 1 : ℕ) : ℝ) ≤ φ ((k + 1 + 1 : ℕ) : ℝ) := hk.2
  have e1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have e2 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
  rw [e1, e2] at hstop
  have hjk : j ≤ k + 1 := by
    refine Nat.ceil_le.2 ?_
    have : c * κ ≤ ((k : ℝ) + 3 / 2) * κ := by nlinarith
    have := le_of_mul_le_mul_right this hκ0
    push_cast
    linarith
  have hik : i ≤ k := by omega
  have hjk' : (j : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hjk
  have hjs : (j : ℝ) ∈ s := hs.out h0 hk1s ⟨Nat.cast_nonneg j, hjk'⟩
  have h3 := line_le hs hφ hκ h0 hjs
  have h4 : φ ((k + 1 : ℕ) : ℝ) ≤ φ ((i + 1 : ℕ) : ℝ) := hk.le_of_le hik
  rw [← Nat.succ_eq_add_one i, ← hi, e1] at h4
  have e : φ' 0 ^ 2 / (2 * κ) = κ * c ^ 2 / 2 := by rw [hsl]; field_simp
  rw [e]
  rw [sub_zero, hsl] at h3
  nlinarith [mul_le_mul_of_nonneg_left hj2 hκ0.le]

/-- Version of `IsFFStop.neg_deriv_le` for a stage that starts at `τ = 1` on the line through the
previous iterate (`τ = 0`): `-φ'(0) ≤ κ (k + 3/2)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.neg_deriv_le_shift {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ (j + 1 : ℕ)) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 2 ∈ s) : -φ' 0 ≤ κ * (k + 3 / 2) := by
  have h2 := line_step_le hs hφ hκ h0 (τ := (k : ℝ) + 1) (by positivity)
    (by convert h1 using 1; ring)
  have hstop : φ ((k + 1 : ℕ) : ℝ) ≤ φ ((k + 1 + 1 : ℕ) : ℝ) := hk.2
  have e1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have e2 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
  rw [e1, e2] at hstop
  have e3 : κ * ((k : ℝ) + 1 + 1 / 2) = κ * (k + 3 / 2) := by ring
  rw [e3] at h2
  linarith

/-! ### Convexity along the direction (Appendix B of the paper) -/

/-- Appendix B of arXiv 2409.04206 observes that the loss is convex along the Fast Forward
direction, "meaning that we can identify a vertex by searching linearly until loss begins to
rise".  Formally: for `φ` convex on `[0, ∞)`, a stopping index minimises `φ` over the whole grid
`ℕ`.  No smoothness is needed. -/
theorem IsFFStop.le_nat_of_convexOn {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hconv : ConvexOn ℝ (Ici 0) φ) (j : ℕ) : φ k ≤ φ j := by
  have hstep := hk.step
  rcases le_or_gt j k with h | h
  · exact hk.le_of_le h
  · have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    exact hstep.trans (hconv.le_right_of_left_le'' (mem_Ici.2 (Nat.cast_nonneg k))
      (mem_Ici.2 (Nat.cast_nonneg j)) (by linarith) hk1 hstep)

private lemma gap_aux (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (hκ0 : 0 ≤ κ) {a b m : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hm : m ∈ s) (hd : φ' m = 0) (hab : φ a ≤ φ b)
    (h : |a - m| + |b - m| ≤ 1) : φ a ≤ φ m + κ / 8 := by
  have h1 := line_le hs hφ hκ hm ha
  have h2 := line_le hs hφ hκ hm hb
  rw [hd, zero_mul, add_zero] at h1 h2
  have sq_le : ∀ t : ℝ, |t| ≤ 1 / 2 → t ^ 2 ≤ 1 / 4 := fun t ht => by
    rw [← sq_abs t]
    nlinarith [abs_nonneg t]
  rcases le_total |a - m| (1 / 2) with h3 | h3
  · have := mul_le_mul_of_nonneg_left (sq_le _ h3) hκ0
    linarith
  · have := mul_le_mul_of_nonneg_left (sq_le (b - m) (by linarith)) hκ0
    linarith

/-- **The stop finds the vertex** (Appendix B of arXiv 2409.04206, for a loss that is convex along
the direction).  There is a vertex `m ≥ 0`, a global minimiser of `φ` on `[0, ∞)`, within one step
of the stopping index, and the iterate kept is optimal up to `κ / 8`.  The existence of the vertex
is a conclusion, not a hypothesis.  OP-TR-27 (ii) asks for `κ / 2`; `κ / 8` is sharp, see
`ffStop_bounds_sharp`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFStop.exists_vertex {k : ℕ} (hk : IsFFStop (fun j : ℕ => φ j) k)
    (hs : s.OrdConnected) (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t)
    (hκ : ∀ a ∈ s, ∀ b ∈ s, |φ' a - φ' b| ≤ κ * |a - b|) (hκ0 : 0 ≤ κ) (h0 : (0 : ℝ) ∈ s)
    (h1 : (k : ℝ) + 1 ∈ s) (hconv : ConvexOn ℝ (Ici 0) φ) :
    ∃ m : ℝ, 0 ≤ m ∧ |m - k| ≤ 1 ∧ (∀ x, 0 ≤ x → φ m ≤ φ x) ∧ φ k ≤ φ m + κ / 8 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set lo : ℝ := max ((k : ℝ) - 1) 0 with hlodef
  have hlo0 : 0 ≤ lo := le_max_right _ _
  have hlo : (k : ℝ) - 1 ≤ lo := le_max_left _ _
  have hlok : lo ≤ k := max_le (by linarith) hk0
  have hsub : Icc lo ((k : ℝ) + 1) ⊆ s := fun t ht => hs.out h0 h1 ⟨hlo0.trans ht.1, ht.2⟩
  have hcont : ContinuousOn φ (Icc lo ((k : ℝ) + 1)) := fun t ht =>
    (hφ t (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hcont
  have hmin' : ∀ t ∈ Icc lo ((k : ℝ) + 1), φ m ≤ φ t := fun t ht => hmin ht
  have hstep := hk.step
  have hks : (k : ℝ) ∈ s := hsub ⟨hlok, by linarith⟩
  -- the iterate before the stop
  have hprev : lo < k → lo = (k : ℝ) - 1 ∧ φ k ≤ φ lo := by
    intro hlt
    have hpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · have : lo = 0 := by simp [hlodef, h]
        simp [this, h] at hlt
      · exact h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have e : lo = (n : ℝ) := by
      rw [hlodef]
      push_cast
      simp
    refine ⟨by rw [e]; push_cast; ring, ?_⟩
    rw [e]
    simpa using hk.prev
  refine ⟨m, hlo0.trans hm.1, ?_, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hm.1, hm.2]
  · intro x hx
    rcases lt_or_ge x lo with hxlo | hxlo
    · have hlt : lo < k := by
        by_contra hcon
        have hlk : lo = k := le_antisymm hlok (not_lt.1 hcon)
        have : (k : ℝ) - 1 < k := by linarith
        have hkpos : lo = 0 := by
          rw [hlodef]
          exact max_eq_right (by
            by_contra hcon2
            have hpos : (k : ℝ) - 1 = lo := (max_eq_left (not_le.1 hcon2).le).symm
            linarith)
        linarith
      obtain ⟨e, hle⟩ := hprev hlt
      have h3 := hconv.le_left_of_right_le'' (mem_Ici.2 hx) (mem_Ici.2 hk0) hxlo.le hlt hle
      exact (hmin' lo ⟨le_rfl, by linarith⟩).trans h3
    · rcases le_or_gt x ((k : ℝ) + 1) with hxhi | hxhi
      · exact hmin' x ⟨hxlo, hxhi⟩
      · have h3 := hconv.le_right_of_left_le'' (mem_Ici.2 hk0) (mem_Ici.2 hx)
          (lt_add_one (k : ℝ)) hxhi.le hstep
        exact (hmin' _ ⟨by linarith, le_rfl⟩).trans h3
  · rcases lt_trichotomy m k with hlt | heq | hgt
    · have hlt' : lo < k := lt_of_le_of_lt hm.1 hlt
      obtain ⟨e, hle⟩ := hprev hlt'
      rcases hm.1.eq_or_lt with heq' | hlt''
      · rw [← heq']
        linarith
      · have hloc : IsLocalMin φ m := hmin.isLocalMin (Icc_mem_nhds hlt'' (by linarith))
        have hd : φ' m = 0 := hloc.hasDerivAt_eq_zero (hφ m (hsub hm))
        refine gap_aux (b := lo) hs hφ hκ hκ0 hks (hsub ⟨le_rfl, by linarith⟩) (hsub hm) hd hle ?_
        rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
        linarith
    · rw [heq]
      linarith
    · rcases hm.2.eq_or_lt with heq' | hlt''
      · rw [heq']
        linarith
      · have hloc : IsLocalMin φ m := hmin.isLocalMin (Icc_mem_nhds (by linarith) hlt'')
        have hd : φ' m = 0 := hloc.hasDerivAt_eq_zero (hφ m (hsub hm))
        refine gap_aux hs hφ hκ hκ0 hks h1 (hsub hm) hd hstep ?_
        rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]
        linarith

/-- **Termination when a vertex exists** (Appendix B of arXiv 2409.04206): if the convex function
`φ` has a minimiser `m ≥ 0` on `[0, ∞)`, then the stage ends, by the "stops improving" rule, after
at most `⌈m⌉` steps.  Without a vertex it need not end: `not_isFFStop_exp`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_isFFStop_of_isMinOn (hconv : ConvexOn ℝ (Ici 0) φ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ x, 0 ≤ x → φ m ≤ φ x) : ∃ k : ℕ, k ≤ ⌈m⌉₊ ∧ IsFFStop (fun j : ℕ => φ j) k := by
  classical
  have hN : m ≤ (⌈m⌉₊ : ℝ) := Nat.le_ceil m
  have hstep : φ (⌈m⌉₊ : ℝ) ≤ φ ((⌈m⌉₊ : ℝ) + 1) := by
    rcases hN.eq_or_lt with h | h
    · rw [← h]
      exact hm _ (by linarith)
    · exact hconv.le_right_of_left_le'' (mem_Ici.2 hm0) (mem_Ici.2 (by linarith)) h
        (by linarith) (hm _ (by linarith))
  have hex : ∃ k, (fun j : ℕ => φ j) k ≤ (fun j : ℕ => φ j) (k + 1) :=
    ⟨⌈m⌉₊, by simpa using hstep⟩
  exact ⟨Nat.find hex, Nat.find_min' hex (by simpa using hstep), isFFStop_find_improve hex⟩

/-- **Termination under strong convexity along the direction**, with `Nat.find` for the "stops
improving" rule.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_isFFStop_of_strong (hφ : ∀ t, HasDerivAt φ (φ' t) t)
    (hμ : ∀ a b, a ≤ b → μ * (b - a) ≤ φ' b - φ' a) (hμ0 : 0 < μ) :
    ∃ k, IsFFStop (fun j : ℕ => φ j) k := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (-φ' 0 / μ)
  rw [div_le_iff₀ hμ0] at hN
  have h := line_step_ge (s := univ) ordConnected_univ (fun t _ => hφ t) (fun a _ b _ => hμ a b)
    (mem_univ _) (τ := (N : ℝ)) (Nat.cast_nonneg N) (mem_univ _)
  have hstep : φ N ≤ φ ((N : ℝ) + 1) := by nlinarith
  have hex : ∃ k, (fun j : ℕ => φ j) k ≤ (fun j : ℕ => φ j) (k + 1) :=
    ⟨N, by simpa using hstep⟩
  exact ⟨_, isFFStop_find_improve hex⟩

end Line

/-! ### The Fast Forward stage on an inner product space -/

section Stage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Eq. (2) of arXiv 2409.04206: the Fast Forward direction `Δ_W = W_t - W_{t-1}`. -/
def ffDir (Wprev W : E) : E := W - Wprev

/-- The weights `W_t + τ Δ_W` in the `τ`-th Fast Forward step, Sec. 3 of arXiv 2409.04206. -/
def ffPoint (W d : E) (τ : ℝ) : E := W + τ • d

/-- The validation losses `L(W_t + j Δ_W)` that a stage looks at. -/
def ffVal (V : E → ℝ) (W d : E) (j : ℕ) : ℝ := V (ffPoint W d j)

@[simp] lemma ffPoint_zero (W d : E) : ffPoint W d 0 = W := by simp [ffPoint]

/-- The updates of Sec. 3 of arXiv 2409.04206 are recursive: a simulated step repeats the last
update. -/
lemma ffPoint_succ (W d : E) (j : ℕ) : ffPoint W d (j + 1 : ℕ) = ffPoint W d j + d := by
  simp [ffPoint, add_smul, add_assoc]

/-- Starting one step further along the direction is a shift of the parameter. -/
lemma ffPoint_add_self (W d : E) (τ : ℝ) : ffPoint (W + d) d τ = ffPoint W d (τ + 1) := by
  simp only [ffPoint, add_smul, one_smul]
  abel

/-- The stage runs along the line through the previous iterate `W_{t-1}`. -/
lemma ffPoint_eq_shift (Wprev W : E) (τ : ℝ) :
    ffPoint W (ffDir Wprev W) τ = ffPoint Wprev (ffDir Wprev W) (τ + 1) := by
  simp only [ffPoint, ffDir, add_smul, one_smul]
  abel

variable {L : E → ℝ} {g : E → E} {β μ : ℝ}

/-- The derivative of the loss along the line of a stage (`hasDerivAt_loss_line`). -/
lemma hasDeriv_ff (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x) (W d : E) :
    ∀ t ∈ (univ : Set ℝ), HasDerivAt (fun τ => L (ffPoint W d τ)) ⟪g (ffPoint W d t), d⟫ t :=
  fun t _ => hasDerivAt_loss_line hL W d t

private lemma lip_ff (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (W d : E) :
    ∀ a ∈ (univ : Set ℝ), ∀ b ∈ (univ : Set ℝ),
      |⟪g (ffPoint W d a), d⟫ - ⟪g (ffPoint W d b), d⟫| ≤ β * ‖d‖ ^ 2 * |a - b| := by
  intro a _ b _
  rw [← inner_sub_left]
  have h1 : ‖g (ffPoint W d a) - g (ffPoint W d b)‖ ≤ β * (|a - b| * ‖d‖) := by
    have h2 := hg (ffPoint W d a) (ffPoint W d b)
    have e : ffPoint W d a - ffPoint W d b = (a - b) • d := by
      simp only [ffPoint, sub_smul]
      abel
    rwa [e, norm_smul, Real.norm_eq_abs] at h2
  calc |⟪g (ffPoint W d a) - g (ffPoint W d b), d⟫|
      ≤ ‖g (ffPoint W d a) - g (ffPoint W d b)‖ * ‖d‖ := abs_real_inner_le_norm _ _
    _ ≤ β * (|a - b| * ‖d‖) * ‖d‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg d)
    _ = β * ‖d‖ ^ 2 * |a - b| := by ring

/-- A `μ`-strongly monotone gradient makes the slope along the line grow at rate `μ ‖d‖²`. -/
lemma strong_ff (hμ : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) (W d : E) :
    ∀ a ∈ (univ : Set ℝ), ∀ b ∈ (univ : Set ℝ), a ≤ b →
      μ * ‖d‖ ^ 2 * (b - a) ≤ ⟪g (ffPoint W d b), d⟫ - ⟪g (ffPoint W d a), d⟫ := by
  intro a _ b _ hab
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have h := hμ (ffPoint W d b) (ffPoint W d a)
  have e : ffPoint W d b - ffPoint W d a = (b - a) • d := by
    simp only [ffPoint, sub_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right, inner_sub_left] at h
  have hba : 0 < b - a := sub_pos.2 hab
  refine le_of_mul_le_mul_left ?_ hba
  nlinarith

private lemma stop_line {k : ℕ} {W d : E} (hk : IsFFStop (ffVal L W d) k) :
    IsFFStop (fun j : ℕ => (fun τ : ℝ => L (ffPoint W d τ)) j) k := hk

/-- **The line-search core** (arXiv 2409.04206, Fast Forward procedure, Sec. 3; the paper itself
has no theorems, this is the formal core of its line search).  For a `β`-smooth loss and a descent
direction `d`, every point `W + τ d` with `0 < τ < 2 |⟪∇L(W), d⟫| / (β ‖d‖²)` has a smaller loss
than `W`.
The comparison is with the *start* of the stage.  Read as "each repeated step decreases the loss
while `τ < 2 |⟪∇L, d⟫| / (β ‖d‖²)`" the claim is false: `exists_ffStep_increase_below_threshold`.
The true per-step threshold is half of this one: `loss_ffStep_lt`. -/
theorem loss_ffPoint_lt (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {W d : E} (hs : ⟪g W, d⟫ < 0) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ : τ < 2 * |⟪g W, d⟫| / (β * ‖d‖ ^ 2)) : L (ffPoint W d τ) < L W := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hs
  have hκ : 0 < β * ‖d‖ ^ 2 := by positivity
  rw [lt_div_iff₀ hκ, abs_of_neg hs] at hτ
  have h := descent_lemma hL hg W (ffPoint W d τ)
  have e : ffPoint W d τ - W = τ • d := by simp [ffPoint]
  rw [e, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have h1 : 0 < τ * (-⟪g W, d⟫ - τ * (β * ‖d‖ ^ 2) / 2) := mul_pos hτ0 (by linarith)
  nlinarith

/-- **Per-step form of the line-search core** (arXiv 2409.04206, Sec. 3): the step from `τ ≥ 0` to
`τ + 1` strictly decreases the loss as long as `τ + 1/2 < |⟪∇L(W), d⟫| / (β ‖d‖²)`.  The threshold
is sharp: see `ffStop_bounds_sharp`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStep_lt (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {W d : E} (hs : ⟪g W, d⟫ < 0) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ + 1 / 2 < |⟪g W, d⟫| / (β * ‖d‖ ^ 2)) :
    L (ffPoint W d (τ + 1)) < L (ffPoint W d τ) := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hs
  have hκ : 0 < β * ‖d‖ ^ 2 := by positivity
  rw [lt_div_iff₀ hκ, abs_of_neg hs] at hτ
  have h := line_step_le (φ := fun τ => L (ffPoint W d τ)) ordConnected_univ (hasDeriv_ff hL W d)
    (lip_ff hg W d) (mem_univ _) hτ0 (mem_univ _)
  rw [ffPoint_zero] at h
  nlinarith

/-- **The stage takes at least `|s| / (β ‖d‖²) - 1/2` steps** (arXiv 2409.04206, Sec. 3, rule of
Fig. 1 or of the text), where `s = ⟪∇L(W), d⟫ < 0`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_ge (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {W d : E} (hs : ⟪g W, d⟫ < 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) : |⟪g W, d⟫| / (β * ‖d‖ ^ 2) - 1 / 2 ≤ k := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hs
  have hκ : 0 < β * ‖d‖ ^ 2 := by positivity
  have h := (stop_line hk).neg_deriv_le ordConnected_univ (hasDeriv_ff hL W d)
    (lip_ff hg W d) (mem_univ _) (mem_univ _)
  rw [ffPoint_zero] at h
  rw [sub_le_iff_le_add, div_le_iff₀ hκ, abs_of_neg hs]
  linarith

/-- **The stage takes at most `|s| / (μ ‖d‖²) + 1/2` steps** if the loss is `μ`-strongly convex,
`μ > 0`, so with `ffStop_ge` the length of a stage is pinned down by the curvature along `d`
(the "number of Fast Forward steps" of Fig. 11 of arXiv 2409.04206). -/
theorem ffStop_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hμ : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) (hμ0 : 0 < μ) {W d : E}
    (hs : ⟪g W, d⟫ < 0) {k : ℕ} (hk : IsFFStop (ffVal L W d) k) :
    (k : ℝ) ≤ |⟪g W, d⟫| / (μ * ‖d‖ ^ 2) + 1 / 2 := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hs
  have hκ : 0 < μ * ‖d‖ ^ 2 := by positivity
  have h := (stop_line hk).mul_le_neg_deriv ordConnected_univ (hasDeriv_ff hL W d)
    (strong_ff hμ W d) hκ.le (mem_univ _) (mem_univ _) (by simpa using hs.le)
  rw [ffPoint_zero] at h
  rw [← sub_le_iff_le_add, le_div_iff₀ hκ, abs_of_neg hs]
  linarith

/-- The kept iterate is at least as good as the start of the stage.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_le_start {V : E → ℝ} {W d : E} {k : ℕ} (hk : IsFFStop (ffVal V W d) k) :
    V (ffPoint W d k) ≤ V W := by
  simpa [ffVal] using hk.le_of_le (Nat.zero_le k)

/-- **Why later updates leave the direction** (Sec. 6.1 and Fig. 6 of arXiv 2409.04206: "future
optimization steps no longer need to search in that direction"): at the stop the gradient has
almost no component along `d`, `|⟪∇L(W + k d), d⟫| ≤ β ‖d‖² / 2`.  No convexity is needed.
OP-TR-27 (iii) asks for `β ‖d‖²`; the constant `1/2` is sharp, see `ffStop_bounds_sharp`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem abs_inner_grad_ffStop_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {W d : E} (hs : ⟪g W, d⟫ ≤ 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) : |⟪g (ffPoint W d k), d⟫| ≤ β * ‖d‖ ^ 2 / 2 :=
  (stop_line hk).abs_deriv_le ordConnected_univ (hasDeriv_ff hL W d) (lip_ff hg W d) (mem_univ _)
    (mem_univ _) (by simpa using hs)

/-- If the stage keeps the iterate that failed instead of the last good one (Sec. 3 of arXiv
2409.04206 does not say which), this costs at most `β ‖d‖²`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStop_overshoot_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {W d : E} (hs : ⟪g W, d⟫ ≤ 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) :
    L (ffPoint W d (k + 1 : ℕ)) ≤ L (ffPoint W d k) + β * ‖d‖ ^ 2 := by
  have h := (stop_line hk).overshoot_le ordConnected_univ (hasDeriv_ff hL W d) (lip_ff hg W d)
    (mem_univ _) (mem_univ _) (by simpa using hs)
  simpa using h

/-- **Guaranteed gain of a stage** (the "ad-hoc optimal step size" of Sec. 1 of arXiv 2409.04206):
for `s = ⟪∇L(W), d⟫ ≤ 0`, the stage gains at least what the exact line search on the quadratic
upper model gains, up to a rounding error,
`L(W + k d) ≤ L(W) - s² / (2 β ‖d‖²) + β ‖d‖² / 8`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStop_le_sub (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {W d : E} (hd : d ≠ 0)
    (hs : ⟪g W, d⟫ ≤ 0) {k : ℕ} (hk : IsFFStop (ffVal L W d) k) :
    L (ffPoint W d k) ≤ L W - ⟪g W, d⟫ ^ 2 / (2 * (β * ‖d‖ ^ 2)) + β * ‖d‖ ^ 2 / 8 := by
  have hκ : 0 < β * ‖d‖ ^ 2 := by positivity
  have h := (stop_line hk).le_sub_gain ordConnected_univ (hasDeriv_ff hL W d) (lip_ff hg W d) hκ
    (mem_univ _) (mem_univ _) (by simpa using hs)
  simpa using h

/-- **The stop is nearly the vertex** (Appendix B of arXiv 2409.04206, under the observed convexity
of the loss along the direction, which is a hypothesis here):
`L(W + k d) ≤ L(W + τ d) + β ‖d‖² / 8` for all `τ ≥ 0`.  OP-TR-27 (ii) asks for the constant `1/2`
instead of the sharp `1/8`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStop_le_add (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W d : E} {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) (hconv : ConvexOn ℝ (Ici 0) fun τ => L (ffPoint W d τ))
    {τ : ℝ} (hτ : 0 ≤ τ) : L (ffPoint W d k) ≤ L (ffPoint W d τ) + β * ‖d‖ ^ 2 / 8 := by
  obtain ⟨m, -, -, hm, hgap⟩ := (stop_line hk).exists_vertex ordConnected_univ (hasDeriv_ff hL W d)
    (lip_ff hg W d) (by positivity) (mem_univ _) (mem_univ _) hconv
  have h := hm τ hτ
  linarith

/-- `loss_ffStop_le_add` over all of `ℝ`, for a loss convex along the whole line and a direction
with `⟪∇L(W), d⟫ ≤ 0`: the minimum of `L` on the line is attained up to `β ‖d‖² / 8`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStop_le_add_of_convexOn_univ (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W d : E} (hs : ⟪g W, d⟫ ≤ 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) (hconv : ConvexOn ℝ univ fun τ => L (ffPoint W d τ)) (τ : ℝ) :
    L (ffPoint W d k) ≤ L (ffPoint W d τ) + β * ‖d‖ ^ 2 / 8 := by
  have hconv' : ConvexOn ℝ (Ici 0) fun τ => L (ffPoint W d τ) :=
    hconv.subset (subset_univ _) (convex_Ici 0)
  rcases le_or_gt 0 τ with hτ | hτ
  · exact loss_ffStop_le_add hL hg hβ hk hconv' hτ
  · have h1 := loss_ffStop_le_add hL hg hβ hk hconv' le_rfl
    have h2 := hconv.slope_le_of_hasDerivAt (mem_univ τ) (mem_univ 0) hτ
      (hasDerivAt_loss_line hL W d 0)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h2
    simp only [ffPoint_zero] at h1 h2
    have h3 : ⟪g W, d⟫ * (0 - τ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs (by linarith)
    simp only [zero_smul, add_zero] at h2
    linarith

/-- **The "repeat while below the threshold" reading is false.**  The survey entry of arXiv
2409.04206 (Fast Forward procedure, Sec. 3) says that repeating the step keeps decreasing `L` while
`τ < 2 |⟪∇L, d⟫| / (β ‖d‖²)`, and OP-TR-27 (i) says that at least `⌊2 |s| / (β ‖d‖²)⌋` Fast Forward
steps decrease the loss.  This holds only against the starting loss (`loss_ffPoint_lt`).  On
`L = x²/2`, `W = -4`, `d = 1`, `β = 1` the threshold is `8`, but the step from `4` to `5` increases
the loss and the stage stops at `k = 4`. -/
theorem exists_ffStep_increase_below_threshold :
    ∃ (L g : ℝ → ℝ) (W d : ℝ) (k : ℕ),
      (∀ x, HasFDerivAt L (innerSL ℝ (g x)) x) ∧ (∀ x y, ‖g x - g y‖ ≤ 1 * ‖x - y‖) ∧
      ⟪g W, d⟫ < 0 ∧ (k : ℝ) + 1 < 2 * |⟪g W, d⟫| / (1 * ‖d‖ ^ 2) ∧
      L (ffPoint W d k) < L (ffPoint W d (k + 1 : ℕ)) ∧ IsFFStop (ffVal L W d) k := by
  refine ⟨fun x => ‖x‖ ^ 2 / 2, id, -4, 1, 4, hasFDerivAt_half_norm_sq, lipschitz_id_grad,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
    norm_num
  · simp [ffPoint]
    norm_num
  · intro j hj
    interval_cases j <;> norm_num [ffVal, ffPoint]
  · norm_num [ffVal, ffPoint]

/-- **All the constants of a stage are sharp** (arXiv 2409.04206, Sec. 3 and Appendix B; the rule
of Fig. 1).  On `L = x²/2`, `W = -1/2`, `d = 1`, `β = 1` (convex along the line) the stage stops at
`k = 0` because `L(W) = L(W + d)`, and then `ffStop_ge`, `abs_inner_grad_ffStop_le` and
`loss_ffStop_le_add` hold with equality.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_bounds_sharp :
    ∃ (L g : ℝ → ℝ) (W d : ℝ),
      (∀ x, HasFDerivAt L (innerSL ℝ (g x)) x) ∧ (∀ x y, ‖g x - g y‖ ≤ 1 * ‖x - y‖) ∧
      (ConvexOn ℝ univ fun τ => L (ffPoint W d τ)) ∧ ⟪g W, d⟫ < 0 ∧
      IsFFStop (ffVal L W d) 0 ∧
      |⟪g W, d⟫| / (1 * ‖d‖ ^ 2) - 1 / 2 = ((0 : ℕ) : ℝ) ∧
      |⟪g (ffPoint W d (0 : ℕ)), d⟫| = 1 * ‖d‖ ^ 2 / 2 ∧
      L (ffPoint W d (0 : ℕ)) = L (ffPoint W d (1 / 2)) + 1 * ‖d‖ ^ 2 / 8 := by
  refine ⟨fun x => ‖x‖ ^ 2 / 2, id, -(1 / 2), 1, hasFDerivAt_half_norm_sq, lipschitz_id_grad,
    ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · obtain rfl : b = 1 - a := by linarith
    simp only [ffPoint, smul_eq_mul, mul_one, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg ha hb, sq_nonneg (x - y)]
  · simp
  · refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    norm_num [ffVal, ffPoint]
  · simp
  · simp
  · norm_num [ffPoint]

/-! ### After an optimizer step: the descent condition is derived -/

/-- If the last update `d = W_t - W_{t-1}` was aligned with the gradient at `W_{t-1}`,
`⟪∇L(W_{t-1}), d⟫ ≤ -α ‖d‖²`, it is still a descent direction at `W_t` when `α > β`:
`⟪∇L(W_t), d⟫ ≤ -(α - β) ‖d‖²`.  This is what makes the Fast Forward direction of Eq. (2) of arXiv
2409.04206, which is computed at the *previous* point, usable at the current one. -/
theorem inner_grad_le_of_align (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {Wprev W : E} {α : ℝ}
    (hα : ⟪g Wprev, ffDir Wprev W⟫ ≤ -α * ‖ffDir Wprev W‖ ^ 2) :
    ⟪g W, ffDir Wprev W⟫ ≤ -(α - β) * ‖ffDir Wprev W‖ ^ 2 := by
  set d := ffDir Wprev W with hd
  have h1 : ‖g W - g Wprev‖ ≤ β * ‖d‖ := hg W Wprev
  have h2 : ⟪g W - g Wprev, d⟫ ≤ ‖g W - g Wprev‖ * ‖d‖ := real_inner_le_norm _ _
  rw [inner_sub_left] at h2
  nlinarith [mul_le_mul_of_nonneg_right h1 (norm_nonneg d)]

/-- **Length of a stage after an aligned update**: `k ≥ α / β - 3/2`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_ge_of_align (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {Wprev W : E} (hW : W ≠ Wprev) {α : ℝ}
    (hα : ⟪g Wprev, ffDir Wprev W⟫ ≤ -α * ‖ffDir Wprev W‖ ^ 2) {k : ℕ}
    (hk : IsFFStop (ffVal L W (ffDir Wprev W)) k) : α / β - 3 / 2 ≤ k := by
  have h1 := inner_grad_le_of_align hg hα
  set d := ffDir Wprev W with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hW
  have hdpos : 0 < ‖d‖ ^ 2 := by positivity
  have h2 := (stop_line hk).neg_deriv_le ordConnected_univ (hasDeriv_ff hL W d) (lip_ff hg W d)
    (mem_univ _) (mem_univ _)
  rw [ffPoint_zero] at h2
  have h3 : α ≤ β * (k + 3 / 2) := by
    have : α * ‖d‖ ^ 2 ≤ β * (k + 3 / 2) * ‖d‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hdpos
  rw [sub_le_iff_le_add, div_le_iff₀ hβ]
  linarith

/-- The project–precondition–project step `W = W' - h Π M Π ∇L(W')` (the Adam-type step of
`GradientFlowConvergence.loss_projPrecondStep_le`, without momentum) is aligned with
`α = dmin / (h dmax²)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem align_of_precondStep {P M : E →L[ℝ] E} (hP : IsOrthProj P) {dmin dmax h : ℝ}
    (hdmin : 0 ≤ dmin) (hdmax : 0 < dmax) (hmin : ∀ v, dmin * ‖v‖ ^ 2 ≤ ⟪M v, v⟫)
    (hmax : ∀ v, ‖M v‖ ≤ dmax * ‖v‖) (hh : 0 < h) {Wprev W : E}
    (hW : W = Wprev - h • P (M (P (g Wprev)))) :
    ⟪g Wprev, ffDir Wprev W⟫ ≤ -(dmin / (h * dmax ^ 2)) * ‖ffDir Wprev W‖ ^ 2 := by
  have h1 := GradientFlowConvergence.inner_projPrecond_ge hP hmin (g Wprev)
  have h2 := GradientFlowConvergence.norm_projPrecond_le hP hmax (g Wprev)
  set q := P (M (P (g Wprev))) with hq
  set v := P (g Wprev) with hv
  have hd : ffDir Wprev W = -(h • q) := by
    simp only [ffDir, hW]
    abel
  rw [hd, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_of_nonneg hh.le,
    mul_pow]
  have h3 : ‖q‖ ^ 2 ≤ dmax ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have e : dmin / (h * dmax ^ 2) * (h ^ 2 * ‖q‖ ^ 2) = h * (dmin * ‖q‖ ^ 2 / dmax ^ 2) := by
    field_simp
  have h4 : dmin * ‖q‖ ^ 2 / dmax ^ 2 ≤ dmin * ‖v‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hdmin]
  have h5 : h * (dmin * ‖q‖ ^ 2 / dmax ^ 2) ≤ h * ⟪g Wprev, q⟫ :=
    mul_le_mul_of_nonneg_left (h4.trans h1) hh.le
  have e2 : -(dmin / (h * dmax ^ 2)) * (h ^ 2 * ‖q‖ ^ 2) = -(h * (dmin * ‖q‖ ^ 2 / dmax ^ 2)) := by
    rw [neg_mul, e]
  rw [e2]
  linarith

/-- **Length of a stage after an Adam-type step** (arXiv 2409.04206, Sec. 3, with `Δ_W` from a
preconditioned step without momentum): `k ≥ dmin / (β h dmax²) - 3/2`.  The descent condition is
not assumed; it follows from the form of the step.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_ge_of_precondStep (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {P M : E →L[ℝ] E} (hP : IsOrthProj P)
    {dmin dmax h : ℝ} (hdmin : 0 ≤ dmin) (hdmax : 0 < dmax)
    (hmin : ∀ v, dmin * ‖v‖ ^ 2 ≤ ⟪M v, v⟫) (hmax : ∀ v, ‖M v‖ ≤ dmax * ‖v‖) (hh : 0 < h)
    {Wprev W : E} (hW : W = Wprev - h • P (M (P (g Wprev)))) (hne : W ≠ Wprev) {k : ℕ}
    (hk : IsFFStop (ffVal L W (ffDir Wprev W)) k) :
    dmin / (β * h * dmax ^ 2) - 3 / 2 ≤ k := by
  have h1 := ffStop_ge_of_align hL hg hβ hne (align_of_precondStep hP hdmin hdmax hmin hmax hh hW)
    hk
  have e : dmin / (β * h * dmax ^ 2) = dmin / (h * dmax ^ 2) / β := by
    field_simp
  rwa [e]

/-- **Length of a stage after a projected gradient step** (arXiv 2409.04206, Sec. 3, for the
simplest optimizer): `k ≥ 1 / (β h) - 3/2`, so that the stage multiplies the learning rate up to
the natural step size `1 / β`, whatever the learning rate was.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem ffStop_ge_of_projGradStep (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {h : ℝ} (hh : 0 < h) {Wprev W : E} (hW : W = Wprev - h • P (g Wprev))
    (hv : P (g Wprev) ≠ 0) {k : ℕ} (hk : IsFFStop (ffVal L W (ffDir Wprev W)) k) :
    1 / (β * h) - 3 / 2 ≤ k := by
  have hne : W ≠ Wprev := by
    intro heq
    rw [heq] at hW
    exact (smul_ne_zero hh.ne' hv) (sub_eq_self.1 hW.symm)
  have h1 := ffStop_ge_of_precondStep hL hg hβ hP (M := 1) (dmin := 1) (dmax := 1) zero_le_one
    one_pos (fun v => by simp) (fun v => by simp) hh
    (by simpa [hP.idem] using hW) hne hk
  simpa using h1

/-- **Loss after a gradient step and a full stage** (arXiv 2409.04206, Sec. 3 and Fig. 1, for a
projected gradient step `W = W' - h Π ∇L(W')`, `β h < 2`, on the loss that also drives the stage):
`L(W + k d) ≤ L(W') - (1/(2β) - β h²/8) ‖Π ∇L(W')‖²`.  One regular step alone only gains
`h (1 - β h / 2) ‖Π ∇L(W')‖²`, which vanishes with `h`; the gain with the stage does not.  This is
the mechanism behind the savings of Sec. 5.  The constant is attained on `L = x²/2`, `h = 2/3`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loss_ffStage_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {P : E →L[ℝ] E} (hP : IsOrthProj P)
    {h : ℝ} (hh : 0 < h) (hβh : β * h < 2) {Wprev W : E} (hW : W = Wprev - h • P (g Wprev)) {k : ℕ}
    (hk : IsFFStop (ffVal L W (ffDir Wprev W)) k) :
    L (ffPoint W (ffDir Wprev W) k) ≤
      L Wprev - (1 / (2 * β) - β * h ^ 2 / 8) * ‖P (g Wprev)‖ ^ 2 := by
  have hd : ffDir Wprev W = -(h • P (g Wprev)) := by
    simp only [ffDir, hW]
    abel
  by_cases hv : P (g Wprev) = 0
  · have e1 : ffDir Wprev W = 0 := by simp [hd, hv]
    have e2 : W = Wprev := by simpa [hv] using hW
    have e3 : ffPoint W (ffDir Wprev W) k = Wprev := by
      rw [e1]
      simp [ffPoint, e2]
    rw [e3, hv]
    simp
  set d := ffDir Wprev W with hddef
  have hvpos : 0 < ‖P (g Wprev)‖ ^ 2 := by positivity
  have hnd : ‖d‖ ^ 2 = h ^ 2 * ‖P (g Wprev)‖ ^ 2 := by
    rw [hd, norm_neg, norm_smul, Real.norm_of_nonneg hh.le, mul_pow]
  have hs : ⟪g Wprev, d⟫ = -(h * ‖P (g Wprev)‖ ^ 2) := by
    rw [hd, inner_neg_right, inner_smul_right, real_inner_comm, hP.inner_self_apply]
  have hκ : 0 < β * ‖d‖ ^ 2 := by
    rw [hnd]
    positivity
  have hstop : IsFFStop (fun j : ℕ => (fun τ : ℝ => L (ffPoint Wprev d τ)) (j + 1 : ℕ)) k := by
    have e : ffVal L W d = fun j : ℕ => (fun τ : ℝ => L (ffPoint Wprev d τ)) (j + 1 : ℕ) := by
      funext j
      simp only [ffVal, hddef]
      rw [ffPoint_eq_shift]
      push_cast
      rfl
    rw [← e]
    exact hk
  have h1 := hstop.le_sub_gain_shift ordConnected_univ (hasDeriv_ff hL Wprev d) (lip_ff hg Wprev d)
    hκ (mem_univ _) (mem_univ _) (by
      rw [ffPoint_zero, hs, hnd]
      have : β * h * (h * ‖P (g Wprev)‖ ^ 2) < 2 * (h * ‖P (g Wprev)‖ ^ 2) :=
        mul_lt_mul_of_pos_right hβh (by positivity)
      nlinarith)
  rw [ffPoint_zero, hs, hnd] at h1
  have e3 : ffPoint Wprev d ((k : ℝ) + 1) = ffPoint W d k := (ffPoint_eq_shift Wprev W k).symm
  simp only [e3] at h1
  have e4 : (-(h * ‖P (g Wprev)‖ ^ 2)) ^ 2 / (2 * (β * (h ^ 2 * ‖P (g Wprev)‖ ^ 2))) =
      1 / (2 * β) * ‖P (g Wprev)‖ ^ 2 := by
    field_simp
  rw [e4] at h1
  nlinarith

/-! ### Similarity of consecutive updates (Sec. 6.1 and Fig. 6 of the paper) -/

/-- The cosine similarity of Fig. 6 of arXiv 2409.04206. -/
noncomputable def cosSim (x y : E) : ℝ := ⟪x, y⟫ / (‖x‖ * ‖y‖)

/-- **After a stage the gradient is nearly orthogonal to the direction** (Sec. 6.1 and Fig. 6 of
arXiv 2409.04206):
`|cos ∠(∇L(W + k d), d)| ≤ β ‖d‖ / (2 ‖∇L(W + k d)‖)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem abs_cosSim_ffStop_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {W d : E} (hs : ⟪g W, d⟫ ≤ 0) (hd : d ≠ 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W d) k) (hu : g (ffPoint W d k) ≠ 0) :
    |cosSim (g (ffPoint W d k)) d| ≤ β * ‖d‖ / (2 * ‖g (ffPoint W d k)‖) := by
  have h := abs_inner_grad_ffStop_le hL hg hs hk
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hu' : 0 < ‖g (ffPoint W d k)‖ := norm_pos_iff.2 hu
  rw [cosSim, abs_div, abs_of_pos (mul_pos hu' hd'), div_le_div_iff₀ (mul_pos hu' hd')
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h (mul_nonneg hu'.le (by norm_num : (0 : ℝ) ≤ 2))]

/-- **The same bound against the previous gradient**: after a gradient step of size `h` with
`β h ≤ 1` and a full stage, `|cos ∠(∇L(W + k d), ∇L(W'))| ≤ β h ‖∇L(W')‖ / (2 ‖∇L(W + k d)‖)`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem abs_cosSim_grad_ffStop_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) {h : ℝ} (hh : 0 < h) (hβh : β * h ≤ 1) {Wprev W : E}
    (hW : W = Wprev - h • g Wprev) (hv : g Wprev ≠ 0) {k : ℕ}
    (hk : IsFFStop (ffVal L W (ffDir Wprev W)) k)
    (hu : g (ffPoint W (ffDir Wprev W) k) ≠ 0) :
    |cosSim (g (ffPoint W (ffDir Wprev W) k)) (g Wprev)| ≤
      β * h * ‖g Wprev‖ / (2 * ‖g (ffPoint W (ffDir Wprev W) k)‖) := by
  have hal : ⟪g Wprev, ffDir Wprev W⟫ ≤ -(1 / h) * ‖ffDir Wprev W‖ ^ 2 := by
    have h1 := align_of_precondStep (g := g) IsOrthProj.one (M := 1) (dmin := 1) (dmax := 1)
      zero_le_one one_pos (fun v => by simp) (fun v => by simp) hh
      (Wprev := Wprev) (W := W) (by simpa using hW)
    simpa using h1
  have hs : ⟪g W, ffDir Wprev W⟫ ≤ 0 := by
    have h1 := inner_grad_le_of_align hg hal
    have h2 : 0 ≤ 1 / h - β := by
      rw [sub_nonneg, le_div_iff₀ hh]
      exact hβh
    nlinarith [mul_nonneg h2 (sq_nonneg ‖ffDir Wprev W‖)]
  have hd : ffDir Wprev W = -(h • g Wprev) := by
    simp only [ffDir, hW]
    abel
  have h1 := abs_inner_grad_ffStop_le hL hg hs hk
  set u := g (ffPoint W (ffDir Wprev W) k) with huu
  rw [hd, inner_neg_right, inner_smul_right, abs_neg, abs_mul, abs_of_pos hh, norm_neg, norm_smul,
    Real.norm_of_nonneg hh.le, mul_pow] at h1
  have hv' : 0 < ‖g Wprev‖ := norm_pos_iff.2 hv
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have h2 : |⟪u, g Wprev⟫| ≤ β * h * ‖g Wprev‖ ^ 2 / 2 := by
    refine le_of_mul_le_mul_left ?_ hh
    calc h * |⟪u, g Wprev⟫| ≤ β * (h ^ 2 * ‖g Wprev‖ ^ 2) / 2 := h1
      _ = h * (β * h * ‖g Wprev‖ ^ 2 / 2) := by ring
  rw [cosSim, abs_div, abs_of_pos (mul_pos hu' hv'), div_le_div_iff₀ (mul_pos hu' hv')
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg hu'.le (by norm_num : (0 : ℝ) ≤ 2))]

/-- **Without a stage, consecutive gradients stay nearly collinear**: a plain gradient step with
`β h ≤ 1` has `cos ∠(∇L(W), ∇L(W')) ≥ (1 - β h) / (1 + β h)`.  Compared with
`abs_cosSim_grad_ffStop_le` this is the contrast of Fig. 6 of arXiv 2409.04206: regular training
keeps a high similarity with the previous gradient, a stage removes it.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem cosSim_regularStep_ge (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {h : ℝ}
    (hh : 0 < h) (hβh : β * h ≤ 1) {Wprev W : E} (hW : W = Wprev - h • g Wprev)
    (hv : g Wprev ≠ 0) (hu : g W ≠ 0) :
    (1 - β * h) / (1 + β * h) ≤ cosSim (g W) (g Wprev) := by
  have hv' : 0 < ‖g Wprev‖ := norm_pos_iff.2 hv
  have hu' : 0 < ‖g W‖ := norm_pos_iff.2 hu
  have hβh0 : 0 ≤ β * h := mul_nonneg hβ hh.le
  have h1 : ‖g W - g Wprev‖ ≤ β * h * ‖g Wprev‖ := by
    have h2 := hg W Wprev
    have e : W - Wprev = -(h • g Wprev) := by
      rw [hW]
      abel
    rwa [e, norm_neg, norm_smul, Real.norm_of_nonneg hh.le, ← mul_assoc] at h2
  have h2 : -(‖g W - g Wprev‖ * ‖g Wprev‖) ≤ ⟪g W - g Wprev, g Wprev⟫ :=
    (abs_le.1 (abs_real_inner_le_norm _ _)).1
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h2
  have h3 : ‖g W‖ ≤ (1 + β * h) * ‖g Wprev‖ := by
    have := norm_add_le (g W - g Wprev) (g Wprev)
    rw [sub_add_cancel] at this
    linarith
  have h4 : (1 - β * h) * ‖g Wprev‖ ^ 2 ≤ ⟪g W, g Wprev⟫ := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hv'.le]
  rw [cosSim, div_le_div_iff₀ (by linarith) (mul_pos hu' hv')]
  have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (sub_nonneg.2 hβh) hv'.le)
  have h6 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 1 + β * h by linarith)
  nlinarith

end Stage

/-! ### Exact quadratics: what determines the optimal length (Appendix B and C of the paper) -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {A : E →L[ℝ] E} {b : E}

/-- The quadratic loss `⟪A x, x⟫ / 2 - ⟪b, x⟫`, whose gradient is `A x - b` for symmetric `A`. -/
noncomputable def quadLoss (A : E →L[ℝ] E) (b x : E) : ℝ := ⟪A x, x⟫ / 2 - ⟪b, x⟫

/-- The Rayleigh quotient `⟪A v, v⟫ / ‖v‖²`, the curvature in the direction `v`. -/
noncomputable def rayleigh (A : E →L[ℝ] E) (v : E) : ℝ := ⟪A v, v⟫ / ‖v‖ ^ 2

/-- The loss is a parabola along a Fast Forward line.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem quadLoss_ffPoint (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) (W d : E) (τ : ℝ) :
    quadLoss A b (ffPoint W d τ) =
      quadLoss A b W + ⟪A W - b, d⟫ * τ + ⟪A d, d⟫ / 2 * τ ^ 2 := by
  have e : ⟪A d, W⟫ = ⟪A W, d⟫ := by rw [hA, real_inner_comm]
  simp only [quadLoss, ffPoint, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sub_left, e, RCLike.conj_to_real]
  ring

/-- Exact line search on a quadratic: the vertex `τ* = -⟪A W - b, d⟫ / ⟪A d, d⟫` is the minimiser,
and the gradient there is orthogonal to `d`, as in Sec. 6.1 of arXiv 2409.04206.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem quad_vertex (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) {W d : E} (ha : 0 < ⟪A d, d⟫) :
    (∀ τ, quadLoss A b (ffPoint W d (-⟪A W - b, d⟫ / ⟪A d, d⟫)) ≤ quadLoss A b (ffPoint W d τ)) ∧
      ⟪A (ffPoint W d (-⟪A W - b, d⟫ / ⟪A d, d⟫)) - b, d⟫ = 0 := by
  constructor
  · intro τ
    rw [quadLoss_ffPoint hA, quadLoss_ffPoint hA]
    set s := ⟪A W - b, d⟫
    set a := ⟪A d, d⟫
    have e : quadLoss A b W + s * (-s / a) + a / 2 * (-s / a) ^ 2 =
        quadLoss A b W - s ^ 2 / (2 * a) := by
      field_simp
      ring
    have h : 0 ≤ a / 2 * (τ + s / a) ^ 2 := by positivity
    have e2 : a / 2 * (τ + s / a) ^ 2 = s * τ + a / 2 * τ ^ 2 + s ^ 2 / (2 * a) := by
      field_simp
      ring
    rw [e]
    linarith
  · have e : A (ffPoint W d (-⟪A W - b, d⟫ / ⟪A d, d⟫)) - b =
        (A W - b) + (-⟪A W - b, d⟫ / ⟪A d, d⟫) • A d := by
      simp only [ffPoint, map_add, map_smul]
      abel
    rw [e, inner_add_left, inner_smul_left, RCLike.conj_to_real]
    field_simp
    ring

/-- **On a quadratic the stage rounds the vertex**: `|k - τ*| ≤ 1/2` for the
`τ* = -⟪A W - b, d⟫ / ⟪A d, d⟫ ≥ 0`.  The length of a stage is thus governed by the curvature
along the direction (the question of Appendix B of arXiv 2409.04206).
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem abs_quad_ffStop_sub_vertex_le (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) {W d : E}
    (ha : 0 < ⟪A d, d⟫) (hs : ⟪A W - b, d⟫ ≤ 0) {k : ℕ}
    (hk : IsFFStop (ffVal (quadLoss A b) W d) k) :
    |(k : ℝ) - -⟪A W - b, d⟫ / ⟪A d, d⟫| ≤ 1 / 2 := by
  set s := ⟪A W - b, d⟫ with hsdef
  set a := ⟪A d, d⟫ with hadef
  have hval : ∀ j : ℕ, ffVal (quadLoss A b) W d j = quadLoss A b W + s * j + a / 2 * (j : ℝ) ^ 2 :=
    fun j => quadLoss_ffPoint hA W d j
  have hup : -s / a - 1 / 2 ≤ k := by
    have h1 := hk.2
    rw [hval, hval] at h1
    push_cast at h1
    rw [sub_le_iff_le_add, div_le_iff₀ ha]
    nlinarith
  have hlo : (k : ℝ) - 1 / 2 ≤ -s / a := by
    rw [le_div_iff₀ ha]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp only [h0, Nat.cast_zero]
      nlinarith
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'
      have h1 := hk.1 n n.lt_succ_self
      rw [hval, hval] at h1
      push_cast at h1 ⊢
      nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **The vertex after a gradient step** (Appendix B and Fig. 12a of arXiv 2409.04206): for
`W = W' - h v` with `v = ∇L(W') = A W' - b`, the optimal number of Fast Forward steps is
`τ* = 1 / (h R(v)) - 1`, with `R(v) = ⟪A v, v⟫ / ‖v‖²` the curvature in the gradient direction. -/
theorem quad_vertex_gradStep {h : ℝ} (hh : 0 < h) {Wprev W : E}
    (hW : W = Wprev - h • (A Wprev - b)) (hv : 0 < ⟪A (A Wprev - b), A Wprev - b⟫) :
    -⟪A W - b, ffDir Wprev W⟫ / ⟪A (ffDir Wprev W), ffDir Wprev W⟫ =
      1 / (h * rayleigh A (A Wprev - b)) - 1 := by
  set v := A Wprev - b with hvdef
  have hv0 : v ≠ 0 := by
    rintro hzero
    simp [hzero] at hv
  have hnv : 0 < ‖v‖ ^ 2 := by positivity
  have hd : ffDir Wprev W = -(h • v) := by
    simp only [ffDir, hW]
    abel
  have hAW : A W - b = v - h • A v := by
    rw [hW, map_sub, map_smul, hvdef]
    abel
  rw [hd, hAW, map_neg, map_smul]
  simp only [inner_neg_right, inner_neg_left, inner_smul_left, inner_smul_right, inner_sub_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq, rayleigh]
  set a := ⟪A v, v⟫
  have ha : a ≠ 0 := hv.ne'
  field_simp

/-- **The optimal length does not depend on the size of the gradient** (formal counterpart of
Fig. 12a of arXiv 2409.04206, where the gradient norm has no predictive power): the curvature `R`
in `quad_vertex_gradStep` is invariant under rescaling of the gradient.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem rayleigh_smul (c : ℝ) (hc : c ≠ 0) (v : E) : rayleigh A (c • v) = rayleigh A v := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  simp only [rayleigh, map_smul, inner_smul_left, inner_smul_right, norm_smul,
    RCLike.conj_to_real, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- **When the first simulated step already fails** (compare Fig. 8 of arXiv 2409.04206): on a
quadratic, right after a gradient step, the stage ends at once if and only if
`h R(v) ≥ 2/3`.  This is a statement about learning rate and curvature.  The paper (Sec. 6)
concludes that the failure at full rank is due to the absence of the projection matrices added by
LoRA; no explanation of Fig. 8 is claimed here.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem quad_ffStop_zero_iff (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫) {h : ℝ} (hh : 0 < h) {Wprev W : E}
    (hW : W = Wprev - h • (A Wprev - b)) (hv : 0 < ⟪A (A Wprev - b), A Wprev - b⟫) :
    IsFFStop (ffVal (quadLoss A b) W (ffDir Wprev W)) 0 ↔
      2 / 3 ≤ h * rayleigh A (A Wprev - b) := by
  set v := A Wprev - b with hvdef
  have hv0 : v ≠ 0 := by
    rintro hzero
    simp [hzero] at hv
  have hnv : 0 < ‖v‖ ^ 2 := by positivity
  have hd : ffDir Wprev W = -(h • v) := by
    simp only [ffDir, hW]
    abel
  have hAW : A W - b = v - h • A v := by
    rw [hW, map_sub, map_smul, hvdef]
    abel
  have hstep : ffVal (quadLoss A b) W (ffDir Wprev W) 1 - ffVal (quadLoss A b) W (ffDir Wprev W) 0 =
      -(h * ‖v‖ ^ 2) + 3 / 2 * h ^ 2 * ⟪A v, v⟫ := by
    simp only [ffVal, quadLoss_ffPoint hA]
    rw [hd, hAW, map_neg, map_smul]
    simp only [inner_neg_right, inner_neg_left, inner_smul_left, inner_smul_right, inner_sub_left,
      RCLike.conj_to_real, real_inner_self_eq_norm_sq]
    push_cast
    ring
  have hiff : IsFFStop (ffVal (quadLoss A b) W (ffDir Wprev W)) 0 ↔
      ffVal (quadLoss A b) W (ffDir Wprev W) 0 ≤ ffVal (quadLoss A b) W (ffDir Wprev W) 1 :=
    ⟨fun hk => hk.2, fun hk => ⟨fun j hj => absurd hj (Nat.not_lt_zero j), hk⟩⟩
  rw [hiff, ← sub_nonneg, hstep, rayleigh, ← mul_div_assoc, le_div_iff₀ hnv]
  constructor
  · intro h1
    have : 0 ≤ h * (-(‖v‖ ^ 2) + 3 / 2 * h * ⟪A v, v⟫) := by nlinarith
    have h2 := nonneg_of_mul_nonneg_right this hh
    nlinarith
  · intro h1
    have : h * (2 / 3 * ‖v‖ ^ 2) ≤ h * (h * ⟪A v, v⟫) := mul_le_mul_of_nonneg_left h1 hh.le
    nlinarith

end Quadratic

/-! ### The training loop: alternating optimizer steps and stages -/

section Run

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L V : E → ℝ} {g : E → E} {β : ℝ}

/-- **A run of Fast Forward training** (Sec. 3 and Fig. 1 of arXiv 2409.04206), with validation loss
`V` and `T = T_interval` optimizer steps per round (`T = 6` in the paper).  Round `n` starts at
`x n`; `y n i` are the iterates of the optimizer phase, about which nothing is assumed here; then
a stage with direction `Δ = y n T - y n (T - 1)` from `y n T` stops at `k n`, and the next round
starts at `y n T + k n Δ`, the last iterate that did not worsen `V`. -/
structure IsFFRun (V : E → ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → ℕ → E) (k : ℕ → ℕ) : Prop where
  start : ∀ n, y n 0 = x n
  stop : ∀ n, IsFFStop (ffVal V (y n T) (ffDir (y n (T - 1)) (y n T))) (k n)
  next : ∀ n, x (n + 1) = ffPoint (y n T) (ffDir (y n (T - 1)) (y n T)) (k n)

/-- A stage does not increase the validation loss.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFRun.val_next_le {T : ℕ} {x : ℕ → E} {y : ℕ → ℕ → E} {k : ℕ → ℕ}
    (hrun : IsFFRun V T x y k) (n : ℕ) : V (x (n + 1)) ≤ V (y n T) := by
  rw [hrun.next]
  exact ffStop_le_start (hrun.stop n)

/-- A stage guided by a validation loss within `δ` of the training loss increases the training loss
by at most `2 δ`.  This is the price of the "tiny validation set" of arXiv 2409.04206.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFRun.loss_next_le {T : ℕ} {x : ℕ → E} {y : ℕ → ℕ → E} {k : ℕ → ℕ}
    (hrun : IsFFRun V T x y k) {δ : ℝ} (hV : ∀ x, |V x - L x| ≤ δ) (n : ℕ) :
    L (x (n + 1)) ≤ L (y n T) + 2 * δ := by
  have h1 := (abs_le.1 (hV (x (n + 1)))).1
  have h2 := (abs_le.1 (hV (y n T))).2
  have h3 := hrun.val_next_le n
  linarith

/-- The descent of `m ≤ T` project–precondition–project steps. -/
private lemma sum_regular_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {P M : ℕ → E →L[ℝ] E}
    (hP : ∀ i, IsOrthProj (P i)) {dmin dmax : ℝ} (hmin : ∀ i v, dmin * ‖v‖ ^ 2 ≤ ⟪M i v, v⟫)
    (hmax : ∀ i v, ‖M i v‖ ≤ dmax * ‖v‖) {h : ℝ} (hh : 0 ≤ h) {T : ℕ} {y : ℕ → E}
    (hy : ∀ i, i < T → y (i + 1) = y i - h • P i (M i (P i (g (y i))))) {m : ℕ} (hm : m ≤ T) :
    h * (dmin - β * h * dmax ^ 2 / 2) * ∑ i ∈ range m, ‖P i (g (y i))‖ ^ 2 ≤ L (y 0) - L (y m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := GradientFlowConvergence.loss_projPrecondStep_le hL hg hβ (hP m) (hmin m) (hmax m) hh
      (y m)
    rw [← hy m (by omega)] at h2
    rw [sum_range_succ, mul_add]
    linarith

/-- The total descent of the optimizer phases of `K` rounds; see `IsFFRun.exists_grad_sq_le`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem IsFFRun.sum_grad_sq_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {T : ℕ} {x : ℕ → E} {y : ℕ → ℕ → E}
    {k : ℕ → ℕ} (hrun : IsFFRun V T x y k) {P M : ℕ → ℕ → E →L[ℝ] E}
    (hP : ∀ n i, IsOrthProj (P n i)) {dmin dmax : ℝ}
    (hmin : ∀ n i v, dmin * ‖v‖ ^ 2 ≤ ⟪M n i v, v⟫) (hmax : ∀ n i v, ‖M n i v‖ ≤ dmax * ‖v‖)
    {h : ℝ} (hh : 0 ≤ h)
    (hy : ∀ n i, i < T → y n (i + 1) = y n i - h • P n i (M n i (P n i (g (y n i))))) {δ : ℝ}
    (hV : ∀ x, |V x - L x| ≤ δ) (K : ℕ) :
    h * (dmin - β * h * dmax ^ 2 / 2) *
        ∑ n ∈ range K, ∑ i ∈ range T, ‖P n i (g (y n i))‖ ^ 2 ≤
      L (x 0) - L (x K) + K * (2 * δ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 := sum_regular_le hL hg hβ (hP K) (hmin K) (hmax K) hh (hy K) le_rfl
    rw [hrun.start K] at h1
    have h2 := hrun.loss_next_le hV K
    rw [sum_range_succ, mul_add]
    push_cast
    linarith

/-- **Fast Forward does not harm convergence** (Secs. 5.1–5.2 of arXiv 2409.04206, empirical there;
the deterministic counterpart).  In a run with `K` rounds of `T` project–precondition–project
optimizer steps (Adam-type steps without momentum, `Π = Π_{n,i}` and `M = M_{n,i}` may vary), with
stages driven by a validation loss within `δ` of the loss `L`,
`min ‖Π ∇L‖² ≤ (L(x₀) - L_inf) / (K T c) + 2 δ / (T c)`, where `c = h (dmin - β h dmax²/2)`, the min
over all optimizer steps.  For `δ = 0` this is the bound `exists_projGrad_sq_le_of_projPrecond` of
plain training with `K T` steps: all the stages together, of any lengths, cost nothing.
The experimental percentages of the paper (41–87% of FLOPs) are measurements and are not formalized;
momentum in Adam is not covered, and neither is the switch to plain Adam of Sec. 5.1. -/
theorem IsFFRun.exists_grad_sq_le (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {T : ℕ} {x : ℕ → E} {y : ℕ → ℕ → E}
    {k : ℕ → ℕ} (hrun : IsFFRun V T x y k) {P M : ℕ → ℕ → E →L[ℝ] E}
    (hP : ∀ n i, IsOrthProj (P n i)) {dmin dmax : ℝ}
    (hmin : ∀ n i v, dmin * ‖v‖ ^ 2 ≤ ⟪M n i v, v⟫) (hmax : ∀ n i v, ‖M n i v‖ ≤ dmax * ‖v‖)
    {h : ℝ} (hh : 0 ≤ h) (hc : 0 < h * (dmin - β * h * dmax ^ 2 / 2))
    (hy : ∀ n i, i < T → y n (i + 1) = y n i - h • P n i (M n i (P n i (g (y n i))))) {δ : ℝ}
    (hV : ∀ x, |V x - L x| ≤ δ) {Linf : ℝ} (hinf : ∀ n, Linf ≤ L (x n)) {K : ℕ} (hK : 0 < K)
    (hT : 0 < T) :
    ∃ n < K, ∃ i < T, ‖P n i (g (y n i))‖ ^ 2 ≤
      (L (x 0) - Linf) / (K * T * (h * (dmin - β * h * dmax ^ 2 / 2))) +
        2 * δ / (T * (h * (dmin - β * h * dmax ^ 2 / 2))) := by
  set c := h * (dmin - β * h * dmax ^ 2 / 2) with hcdef
  have hsum : c * ∑ n ∈ range K, ∑ i ∈ range T, ‖P n i (g (y n i))‖ ^ 2 ≤
      L (x 0) - Linf + K * (2 * δ) := by
    have h1 : c * ∑ n ∈ range K, ∑ i ∈ range T, ‖P n i (g (y n i))‖ ^ 2 ≤
        L (x 0) - L (x K) + K * (2 * δ) := hrun.sum_grad_sq_le hL hg hβ hP hmin hmax hh hy hV K
    have h2 := hinf K
    linarith
  obtain ⟨n, hn, hle⟩ := exists_le_of_mul_sum_le hc hK hsum
  obtain ⟨i, hi, hle2⟩ := exists_le_of_mul_sum_le (c := 1) (e := 0)
    (A := (L (x 0) - Linf) / (K * c) + 2 * δ / c) one_pos hT (by simpa using hle)
  refine ⟨n, hn, i, hi, ?_⟩
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have e : ((L (x 0) - Linf) / (K * c) + 2 * δ / c) / (T * 1) + 0 / 1 =
      (L (x 0) - Linf) / (K * T * c) + 2 * δ / (T * c) := by
    field_simp
    ring
  rwa [e] at hle2

/-- **Fast Forward removes the dependence on the learning rate** (the acceleration of Sec. 5 of
arXiv 2409.04206; deterministic counterpart for projected gradient steps, with `V = L`).  If every
round consists of `T ≥ 1` projected gradient steps with `β h < 2` and a stage, then, among the last
optimizer steps of `K` rounds,
`min ‖Π ∇L‖² ≤ 2 β (L(x₀) - L_inf) / (K (1 - (β h / 2)²))`.
Plain training has a bound of order `(L(x₀) - L_inf) / (K T h)`, which blows up as `h → 0`.
The stages are counted as free here, while each costs `k + 1` validation evaluations, whose number
`ffStop_ge_of_projGradStep` bounds from below. -/
theorem IsFFRun.exists_grad_sq_le_of_stage (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x)
    (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖) (hβ : 0 < β) {T : ℕ} {x : ℕ → E} {y : ℕ → ℕ → E}
    {k : ℕ → ℕ} (hrun : IsFFRun L T x y k) {P : ℕ → ℕ → E →L[ℝ] E}
    (hP : ∀ n i, IsOrthProj (P n i)) {h : ℝ} (hh : 0 < h) (hβh : β * h < 2)
    (hy : ∀ n i, i < T → y n (i + 1) = y n i - h • P n i (g (y n i))) {Linf : ℝ}
    (hinf : ∀ n, Linf ≤ L (x n)) {K : ℕ} (hK : 0 < K) (hT : 0 < T) :
    ∃ n < K, ‖P n (T - 1) (g (y n (T - 1)))‖ ^ 2 ≤
      2 * β * (L (x 0) - Linf) / (K * (1 - (β * h / 2) ^ 2)) := by
  set c : ℝ := 1 / (2 * β) - β * h ^ 2 / 8 with hcdef
  have hβh0 : 0 < β * h := mul_pos hβ hh
  have hq : 0 < 1 - (β * h / 2) ^ 2 := by nlinarith
  have hc2 : c = (1 - (β * h / 2) ^ 2) / (2 * β) := by
    rw [hcdef]
    field_simp
    ring
  have hc : 0 < c := by
    rw [hc2]
    positivity
  have hmono : ∀ n m, m ≤ T - 1 → L (y n m) ≤ L (y n 0) := by
    intro n m
    induction m with
    | zero => exact fun _ => le_rfl
    | succ m ih =>
      intro hm
      have h1 := loss_projGradStep_le_self hL hg (hP n m) (h := h)
        (mul_nonneg hh.le (by nlinarith)) (y n m)
      have h2 : y n (m + 1) = projGradStep (P n m) g h (y n m) := hy n m (by omega)
      rw [← h2] at h1
      exact h1.trans (ih (by omega))
  have hstage : ∀ n, c * ‖P n (T - 1) (g (y n (T - 1)))‖ ^ 2 ≤ L (x n) - L (x (n + 1)) := by
    intro n
    have hTs : T - 1 + 1 = T := by omega
    have hW : y n T = y n (T - 1) - h • P n (T - 1) (g (y n (T - 1))) := by
      have := hy n (T - 1) (by omega)
      rwa [hTs] at this
    have h1 := loss_ffStage_le hL hg hβ (hP n (T - 1)) hh hβh hW (hrun.stop n)
    rw [← hrun.next n, ← hcdef] at h1
    have h2 := hmono n (T - 1) le_rfl
    rw [hrun.start n] at h2
    linarith
  have hsum : c * ∑ n ∈ range K, ‖P n (T - 1) (g (y n (T - 1)))‖ ^ 2 ≤
      L (x 0) - Linf + K * 0 := by
    have h1 := LeanDLRA.sum_le_of_le_sub_add (u := fun n => L (x n))
      (a := fun n => c * ‖P n (T - 1) (g (y n (T - 1)))‖ ^ 2) (e := fun _ => 0)
      (fun n => by linarith [hstage n]) K
    rw [← mul_sum, sum_const_zero] at h1
    have h2 := hinf K
    linarith
  obtain ⟨n, hn, hle⟩ := exists_le_of_mul_sum_le hc hK hsum
  refine ⟨n, hn, ?_⟩
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have e : (L (x 0) - Linf) / (K * c) + 0 / c =
      2 * β * (L (x 0) - Linf) / (K * (1 - (β * h / 2) ^ 2)) := by
    rw [hc2]
    field_simp
    ring
  rwa [e] at hle

/-- **Runs exist as soon as stages terminate**, for any optimizer `opt`, whose dependence on the
round and the step can carry internal state such as Adam's.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_isFFRun (hstop : ∀ W d, ∃ k, IsFFStop (ffVal V W d) k)
    (opt : ℕ → ℕ → E → E) (T : ℕ) (x₀ : E) :
    ∃ (x : ℕ → E) (y : ℕ → ℕ → E) (k : ℕ → ℕ), x 0 = x₀ ∧ IsFFRun V T x y k ∧
      ∀ n i, y n (i + 1) = opt n i (y n i) := by
  classical
  choose K hK using hstop
  let z : ℕ → E → ℕ → E := fun n w i => Nat.rec w (fun i zi => opt n i zi) i
  let W : ℕ → E → E := fun n w => z n w T
  let D : ℕ → E → E := fun n w => ffDir (z n w (T - 1)) (z n w T)
  let stage : ℕ → E → E := fun n w => ffPoint (W n w) (D n w) (K (W n w) (D n w))
  let x : ℕ → E := fun n => Nat.rec x₀ (fun n xn => stage n xn) n
  exact ⟨x, fun n i => z n (x n) i, fun n => K (W n (x n)) (D n (x n)), rfl,
    ⟨fun _ => rfl, fun _ => hK _ _, fun _ => rfl⟩, fun _ _ => rfl⟩

/-- On a strongly convex loss all stages terminate, so runs exist.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_isFFRun_of_strong (hL : ∀ x, HasFDerivAt L (innerSL ℝ (g x)) x) {μ : ℝ}
    (hμ : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫) (hμ0 : 0 < μ)
    (opt : ℕ → ℕ → E → E) (T : ℕ) (x₀ : E) :
    ∃ (x : ℕ → E) (y : ℕ → ℕ → E) (k : ℕ → ℕ), x 0 = x₀ ∧ IsFFRun L T x y k ∧
      ∀ n i, y n (i + 1) = opt n i (y n i) := by
  refine exists_isFFRun (fun W d => ?_) opt T x₀
  by_cases hd : d = 0
  · refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    simp [ffVal, ffPoint, hd]
  · have hκ : 0 < μ * ‖d‖ ^ 2 := by positivity
    exact exists_isFFStop_of_strong (φ := fun τ => L (ffPoint W d τ))
      (fun t => hasDeriv_ff hL W d t (mem_univ _))
      (fun a b => strong_ff hμ W d a (mem_univ _) b (mem_univ _)) hκ

/-- Non-vacuity of `IsFFRun.exists_grad_sq_le` and `IsFFRun.exists_grad_sq_le_of_stage`: gradient
descent with stages on `L = ‖x‖²/2`. -/
example (h : ℝ) (T : ℕ) (x₀ : E) :
    ∃ (x : ℕ → E) (y : ℕ → ℕ → E) (k : ℕ → ℕ), x 0 = x₀ ∧
      IsFFRun (fun x : E => ‖x‖ ^ 2 / 2) T x y k ∧
      ∀ n i, y n (i + 1) = y n i - h • (1 : E →L[ℝ] E) (id (y n i)) :=
  exists_isFFRun_of_strong (g := id) hasFDerivAt_half_norm_sq (μ := 1)
    (fun x y => by simp) one_pos
    (fun _ _ w => w - h • (1 : E →L[ℝ] E) (id w)) T x₀

end Run

/-! ### Curves of the form `W + τ V + τ² C`

A stage on the factors of `W = W₀ + B A` moves `W` along a parabola, not along a line. -/

section Curve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ℓ : E → ℝ} {G : E → E} {β : ℝ}

/-- The curve `W + τ V + τ² C`. -/
def curvePoint (W V C : E) (τ : ℝ) : E := W + τ • V + τ ^ 2 • C

/-- The velocity `V + 2 τ C` of `curvePoint`. -/
def curveVel (V C : E) (τ : ℝ) : E := V + (2 * τ) • C

/-- The curvature bound of a loss along `curvePoint` on `[0, T]`, in terms of `β`, of the size `g₀`
of the gradient at `τ = 0` and of the sizes `v`, `c` of `V`, `C`. -/
def curveCurv (β g₀ v c T : ℝ) : ℝ :=
  β * (v + 2 * T * c) ^ 2 + 2 * c * (g₀ + β * T * (v + T * c))

/-- The derivative of the curve. -/
lemma hasDerivAt_curvePoint (W V C : E) (t : ℝ) :
    HasDerivAt (curvePoint W V C) (curveVel V C t) t := by
  have h1 : HasDerivAt (fun τ : ℝ => τ • V) V t := by
    simpa using (hasDerivAt_id t).smul_const V
  have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2 • C) ((2 * t) • C) t := by
    simpa using (hasDerivAt_pow 2 t).smul_const C
  exact (h1.const_add W).add h2

/-- The derivative of the loss along the curve. -/
lemma hasDerivAt_loss_curve (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x) (W V C : E) (t : ℝ) :
    HasDerivAt (fun τ => ℓ (curvePoint W V C τ)) ⟪G (curvePoint W V C t), curveVel V C t⟫ t := by
  have h := (hℓ (curvePoint W V C t)).comp_hasDerivAt t (hasDerivAt_curvePoint W V C t)
  simpa [innerSL_apply_apply, Function.comp_def] using h

/-- The slope of a `β`-smooth loss along `curvePoint` is Lipschitz on `[0, T]` with constant
`curveCurv`.  Unlike on a line, the constant depends on `T` and on the gradient: the loss
`(B, A) ↦ ℓ(W₀ + B A)` of the factors is not globally smooth, even if `ℓ` is.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem abs_curve_slope_sub_le (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) (W V C : E)
    {T a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    |⟪G (curvePoint W V C a), curveVel V C a⟫ - ⟪G (curvePoint W V C b), curveVel V C b⟫| ≤
      curveCurv β ‖G W‖ ‖V‖ ‖C‖ T * |a - b| := by
  have hT : 0 ≤ T := ha.1.trans ha.2
  have hv := norm_nonneg V
  have hc := norm_nonneg C
  set Vb : ℝ := ‖V‖ + 2 * T * ‖C‖ with hVb
  have hVb0 : 0 ≤ Vb := by positivity
  have hdist : 0 ≤ |a - b| := abs_nonneg _
  -- the velocity
  have hva : ‖curveVel V C a‖ ≤ Vb := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ha.1])]
    nlinarith [ha.2, ha.1]
  -- distance of the points
  have hp : ‖curvePoint W V C a - curvePoint W V C b‖ ≤ |a - b| * Vb := by
    have e : curvePoint W V C a - curvePoint W V C b = (a - b) • (V + (a + b) • C) := by
      have e2 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
      calc curvePoint W V C a - curvePoint W V C b = (a - b) • V + (a ^ 2 - b ^ 2) • C := by
            simp only [curvePoint, sub_smul]
            abel
        _ = (a - b) • (V + (a + b) • C) := by rw [e2, smul_add, smul_smul]
    rw [e, norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hdist
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ha.1, hb.1])]
    nlinarith [ha.2, hb.2]
  -- size of the gradient
  have hGb : ‖G (curvePoint W V C b)‖ ≤ ‖G W‖ + β * T * (‖V‖ + T * ‖C‖) := by
    have h1 := hG (curvePoint W V C b) W
    have h2 : ‖curvePoint W V C b - W‖ ≤ T * (‖V‖ + T * ‖C‖) := by
      have e : curvePoint W V C b - W = b • V + b ^ 2 • C := by
        simp only [curvePoint]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hb.1, Real.norm_of_nonneg (sq_nonneg b)]
      have hb2 : b ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hb.1 hb.2 2
      nlinarith [mul_le_mul_of_nonneg_right hb.2 hv, mul_le_mul_of_nonneg_right hb2 hc]
    have h3 := norm_sub_norm_le (G (curvePoint W V C b)) (G W)
    have h4 := mul_le_mul_of_nonneg_left h2 hβ
    nlinarith
  -- velocities differ by a multiple of `C`
  have hdv : ‖curveVel V C a - curveVel V C b‖ = 2 * |a - b| * ‖C‖ := by
    have e : curveVel V C a - curveVel V C b = (2 * (a - b)) • C := by
      simp only [curveVel, mul_sub, sub_smul]
      abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_mul]
    norm_num
  have hsplit : ⟪G (curvePoint W V C a), curveVel V C a⟫ - ⟪G (curvePoint W V C b), curveVel V C b⟫
      = ⟪G (curvePoint W V C a) - G (curvePoint W V C b), curveVel V C a⟫ +
        ⟪G (curvePoint W V C b), curveVel V C a - curveVel V C b⟫ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hsplit]
  have h1 : |⟪G (curvePoint W V C a) - G (curvePoint W V C b), curveVel V C a⟫| ≤
      β * (|a - b| * Vb) * Vb := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (((hG _ _).trans (mul_le_mul_of_nonneg_left hp hβ))) hva (norm_nonneg _)
      (by positivity)
  have h2 : |⟪G (curvePoint W V C b), curveVel V C a - curveVel V C b⟫| ≤
      (‖G W‖ + β * T * (‖V‖ + T * ‖C‖)) * (2 * |a - b| * ‖C‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hdv]
    exact mul_le_mul_of_nonneg_right hGb (by positivity)
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  simp only [curveCurv, hVb]
  ring

/-- **Stages along a curve take at least `T` steps** if `(T - 1/2) κ_T < |slope at 0|`, where
`κ_T = curveCurv … T` is the curvature bound on `[0, T]`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem curve_ffStop_ge (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W V C : E} {T k : ℕ}
    (hT : ((T : ℝ) - 1 / 2) * curveCurv β ‖G W‖ ‖V‖ ‖C‖ T < -⟪G W, V⟫)
    (hk : IsFFStop (fun j : ℕ => ℓ (curvePoint W V C j)) k) : T ≤ k := by
  by_contra hcon
  have hkT : (k : ℝ) + 1 ≤ T := by exact_mod_cast not_le.1 hcon
  have hκ0 : 0 ≤ curveCurv β ‖G W‖ ‖V‖ ‖C‖ T := by
    unfold curveCurv
    positivity
  have h := IsFFStop.neg_deriv_le (φ := fun τ => ℓ (curvePoint W V C τ)) (s := Icc 0 (T : ℝ)) hk
    ordConnected_Icc (fun t _ => hasDerivAt_loss_curve hℓ W V C t)
    (fun a ha b hb => abs_curve_slope_sub_le hG hβ W V C ha hb) ⟨le_rfl, Nat.cast_nonneg T⟩
    ⟨by positivity, hkT⟩
  have e0 : ⟪G (curvePoint W V C 0), curveVel V C 0⟫ = ⟪G W, V⟫ := by
    simp [curvePoint, curveVel]
  rw [e0] at h
  nlinarith

/-- `curve_ffStop_ge` for a stage that starts at `τ = 1`, the case of a stage after a step that
went from `τ = 0` to `τ = 1`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem curve_ffStop_ge_shift (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W V C : E} {T k : ℕ}
    (hT : ((T : ℝ) + 1 / 2) * curveCurv β ‖G W‖ ‖V‖ ‖C‖ (T + 1) < -⟪G W, V⟫)
    (hk : IsFFStop (fun j : ℕ => ℓ (curvePoint W V C (j + 1 : ℕ))) k) : T ≤ k := by
  by_contra hcon
  have hkT : (k : ℝ) + 1 ≤ T := by exact_mod_cast not_le.1 hcon
  have hκ0 : 0 ≤ curveCurv β ‖G W‖ ‖V‖ ‖C‖ (T + 1) := by
    unfold curveCurv
    positivity
  have h := IsFFStop.neg_deriv_le_shift (φ := fun τ => ℓ (curvePoint W V C τ))
    (s := Icc 0 ((T : ℝ) + 1)) hk ordConnected_Icc (fun t _ => hasDerivAt_loss_curve hℓ W V C t)
    (fun a ha b hb => abs_curve_slope_sub_le hG hβ W V C ha hb) ⟨le_rfl, by positivity⟩
    ⟨by positivity, by linarith⟩
  have e0 : ⟪G (curvePoint W V C 0), curveVel V C 0⟫ = ⟪G W, V⟫ := by
    simp [curvePoint, curveVel]
  rw [e0] at h
  nlinarith

/-- Stationarity at the stop along a curve: `|⟪∇ℓ(W(k)), W'(k)⟫| ≤ κ_T / 2` for `k + 1 ≤ T`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem curve_abs_slope_ffStop_le (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W V C : E} {T : ℝ} {k : ℕ}
    (hkT : (k : ℝ) + 1 ≤ T) (hs : ⟪G W, V⟫ ≤ 0)
    (hk : IsFFStop (fun j : ℕ => ℓ (curvePoint W V C j)) k) :
    |⟪G (curvePoint W V C k), curveVel V C k⟫| ≤ curveCurv β ‖G W‖ ‖V‖ ‖C‖ T / 2 := by
  have hT : 0 ≤ T := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact IsFFStop.abs_deriv_le (φ := fun τ => ℓ (curvePoint W V C τ))
    (φ' := fun t => ⟪G (curvePoint W V C t), curveVel V C t⟫) (s := Icc 0 T) hk
    ordConnected_Icc (fun t _ => hasDerivAt_loss_curve hℓ W V C t)
    (fun a ha b hb => abs_curve_slope_sub_le hG hβ W V C ha hb) ⟨le_rfl, hT⟩
    ⟨by positivity, hkT⟩ (by simpa [curvePoint, curveVel] using hs)

/-- Guaranteed gain along a curve: `ℓ(W(k)) ≤ ℓ(W) - s² / (2 κ_T) + κ_T / 8` for `k + 1 ≤ T`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem curve_ffStop_le_sub (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W V C : E} {T : ℝ} {k : ℕ}
    (hkT : (k : ℝ) + 1 ≤ T) (hs : ⟪G W, V⟫ ≤ 0) (hκ : 0 < curveCurv β ‖G W‖ ‖V‖ ‖C‖ T)
    (hk : IsFFStop (fun j : ℕ => ℓ (curvePoint W V C j)) k) :
    ℓ (curvePoint W V C k) ≤ ℓ W - ⟪G W, V⟫ ^ 2 / (2 * curveCurv β ‖G W‖ ‖V‖ ‖C‖ T) +
      curveCurv β ‖G W‖ ‖V‖ ‖C‖ T / 8 := by
  have hT : 0 ≤ T := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := IsFFStop.le_sub_gain (φ := fun τ => ℓ (curvePoint W V C τ))
    (φ' := fun t => ⟪G (curvePoint W V C t), curveVel V C t⟫) (s := Icc 0 T) hk
    ordConnected_Icc (fun t _ => hasDerivAt_loss_curve hℓ W V C t)
    (fun a ha b hb => abs_curve_slope_sub_le hG hβ W V C ha hb) hκ ⟨le_rfl, hT⟩
    ⟨by positivity, hkT⟩ (by simpa [curvePoint, curveVel] using hs)
  simpa [curvePoint, curveVel] using h

end Curve

/-! ### LoRA: a stage on the factors of `W = W₀ + B A` (Eq. (1) of the paper) -/

section LoRA

open scoped LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable {ℓ : Matrix m n ℝ → ℝ} {G : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}

/-- Eq. (1) of arXiv 2409.04206: LoRA adds a trainable low-rank product to the frozen weights
`W₀`. -/
def loraWeight (W₀ : Matrix m n ℝ) (B : Matrix m r ℝ) (A : Matrix r n ℝ) : Matrix m n ℝ :=
  W₀ + B * A

/-- The weights during a stage on the trainable parameters `B` and `A` (Sec. 3 of arXiv 2409.04206:
"for each trainable parameter"): `W₀ + (B + τ Δ_B) (A + τ Δ_A)`. -/
noncomputable def loraFF (W₀ : Matrix m n ℝ) (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ) (τ : ℝ) :
    Matrix m n ℝ :=
  loraWeight W₀ (ffPoint B ΔB τ) (ffPoint A ΔA τ)

/-- A stage on the factors moves the weights on a parabola,
`W(τ) = W + τ (Δ_B A + B Δ_A) + τ² Δ_B Δ_A`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loraFF_eq_curvePoint (W₀ : Matrix m n ℝ) (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ)
    (τ : ℝ) :
    loraFF W₀ B ΔB A ΔA τ =
      curvePoint (loraWeight W₀ B A) (ΔB * A + B * ΔA) (ΔB * ΔA) τ := by
  simp only [loraFF, loraWeight, ffPoint, curvePoint, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, pow_two]
  abel

/-- A stage after the update `(Δ_B, Δ_A)` runs on the same parabola as the update.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem loraFF_shift (W₀ : Matrix m n ℝ) (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ) (τ : ℝ) :
    loraFF W₀ (B + ΔB) ΔB (A + ΔA) ΔA τ = loraFF W₀ B ΔB A ΔA (τ + 1) := by
  simp only [loraFF, ffPoint_add_self]

/-- **The low rank is preserved** (LoRA, Eq. (1) of arXiv 2409.04206): during a stage on the factors
the update `W(τ) - W₀` has rank at most `r`, for every `τ`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem rank_loraFF_sub_le (W₀ : Matrix m n ℝ) (B ΔB : Matrix m r ℝ) (A ΔA : Matrix r n ℝ)
    (τ : ℝ) : (loraFF W₀ B ΔB A ΔA τ - W₀).rank ≤ Fintype.card r := by
  have e : loraFF W₀ B ΔB A ΔA τ - W₀ = ffPoint B ΔB τ * ffPoint A ΔA τ := by
    simp [loraFF, loraWeight]
  rw [e]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)

/-- **A stage on the weights themselves would leave the low-rank set**, which is why Eq. (2) of
arXiv 2409.04206 has to be read factor by factor: two rank-one LoRA updates whose weight-space
extrapolation `W_t + (W_t - W_{t-1})` has rank two.  Compare `rank_loraFF_sub_le`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_weightFF_rank_two :
    ∃ (B B' : Matrix (Fin 2) Unit ℝ) (A A' : Matrix Unit (Fin 2) ℝ),
      (loraWeight 0 B A - 0).rank ≤ 1 ∧ (loraWeight 0 B' A' - 0).rank ≤ 1 ∧
      (ffPoint (loraWeight 0 B A) (ffDir (loraWeight 0 B' A') (loraWeight 0 B A)) 1 -
        0).rank = 2 := by
  refine ⟨Matrix.of fun i _ => if i = 0 then 1 else 0, Matrix.of fun i _ => if i = 1 then 1 else 0,
    Matrix.of fun _ j => if j = 0 then 1 else 0, Matrix.of fun _ j => if j = 1 then 1 else 0,
    ?_, ?_, ?_⟩
  · simp only [loraWeight, zero_add, sub_zero]
    exact (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_le_card_height _).trans (by simp))
  · simp only [loraWeight, zero_add, sub_zero]
    exact (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_le_card_height _).trans (by simp))
  · have e : ffPoint (loraWeight (0 : Matrix (Fin 2) (Fin 2) ℝ)
        (Matrix.of fun i _ => if i = 0 then 1 else 0 : Matrix (Fin 2) Unit ℝ)
        (Matrix.of fun _ j => if j = 0 then 1 else 0 : Matrix Unit (Fin 2) ℝ))
        (ffDir (loraWeight 0
          (Matrix.of fun i _ => if i = 1 then 1 else 0 : Matrix (Fin 2) Unit ℝ)
          (Matrix.of fun _ j => if j = 1 then 1 else 0 : Matrix Unit (Fin 2) ℝ))
        (loraWeight 0
          (Matrix.of fun i _ => if i = 0 then 1 else 0 : Matrix (Fin 2) Unit ℝ)
          (Matrix.of fun _ j => if j = 0 then 1 else 0 : Matrix Unit (Fin 2) ℝ))) 1 - 0 =
        !![2, 0; 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [ffPoint, ffDir, loraWeight, Matrix.mul_apply]
    rw [e]
    have hu : IsUnit (!![2, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
      norm_num
    simpa using Matrix.rank_of_isUnit _ hu

/-- **Stage length for LoRA** (arXiv 2409.04206, Sec. 3 on the factors): if
`(T - 1/2) κ_T < |⟪∇ℓ(W), Δ_B A + B Δ_A⟫|`, every stopping index of a stage on the factors is at
least `T`.  Here `ℓ` is `β`-smooth in the *weights* and `κ_T` is the explicit `curveCurv`.  The
loss of the factors is not globally smooth, so the theorems for the line (`ffStop_ge`) do not
apply, which is why this bound depends on `T`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem lora_ffStop_ge (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W₀ : Matrix m n ℝ}
    {B ΔB : Matrix m r ℝ} {A ΔA : Matrix r n ℝ} {T k : ℕ}
    (hT : ((T : ℝ) - 1 / 2) *
        curveCurv β ‖G (loraWeight W₀ B A)‖ ‖ΔB * A + B * ΔA‖ ‖ΔB * ΔA‖ T <
      -⟪G (loraWeight W₀ B A), ΔB * A + B * ΔA⟫)
    (hk : IsFFStop (fun j : ℕ => ℓ (loraFF W₀ B ΔB A ΔA j)) k) : T ≤ k := by
  refine curve_ffStop_ge hℓ hG hβ hT ?_
  simpa only [loraFF_eq_curvePoint] using hk

/-- **Stationarity at the stop for LoRA** (Sec. 6.1 of arXiv 2409.04206): the velocity of the
weights is nearly orthogonal to the gradient, `|⟪∇ℓ(W(k)), W'(k)⟫| ≤ κ_T / 2` for `k + 1 ≤ T`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem lora_abs_slope_ffStop_le (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W₀ : Matrix m n ℝ}
    {B ΔB : Matrix m r ℝ} {A ΔA : Matrix r n ℝ} {T : ℝ} {k : ℕ} (hkT : (k : ℝ) + 1 ≤ T)
    (hs : ⟪G (loraWeight W₀ B A), ΔB * A + B * ΔA⟫ ≤ 0)
    (hk : IsFFStop (fun j : ℕ => ℓ (loraFF W₀ B ΔB A ΔA j)) k) :
    |⟪G (loraFF W₀ B ΔB A ΔA k), curveVel (ΔB * A + B * ΔA) (ΔB * ΔA) k⟫| ≤
      curveCurv β ‖G (loraWeight W₀ B A)‖ ‖ΔB * A + B * ΔA‖ ‖ΔB * ΔA‖ T / 2 := by
  rw [loraFF_eq_curvePoint]
  refine curve_abs_slope_ffStop_le hℓ hG hβ hkT hs ?_
  simpa only [loraFF_eq_curvePoint] using hk

/-- **Guaranteed gain of a LoRA stage**: `ℓ(W(k)) ≤ ℓ(W) - s² / (2 κ_T) + κ_T / 8` for `k + 1 ≤ T`,
with `s = ⟪∇ℓ(W), Δ_B A + B Δ_A⟫ ≤ 0`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem lora_ffStop_le_sub (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W₀ : Matrix m n ℝ}
    {B ΔB : Matrix m r ℝ} {A ΔA : Matrix r n ℝ} {T : ℝ} {k : ℕ} (hkT : (k : ℝ) + 1 ≤ T)
    (hs : ⟪G (loraWeight W₀ B A), ΔB * A + B * ΔA⟫ ≤ 0)
    (hκ : 0 < curveCurv β ‖G (loraWeight W₀ B A)‖ ‖ΔB * A + B * ΔA‖ ‖ΔB * ΔA‖ T)
    (hk : IsFFStop (fun j : ℕ => ℓ (loraFF W₀ B ΔB A ΔA j)) k) :
    ℓ (loraFF W₀ B ΔB A ΔA k) ≤ ℓ (loraWeight W₀ B A) -
      ⟪G (loraWeight W₀ B A), ΔB * A + B * ΔA⟫ ^ 2 /
        (2 * curveCurv β ‖G (loraWeight W₀ B A)‖ ‖ΔB * A + B * ΔA‖ ‖ΔB * ΔA‖ T) +
      curveCurv β ‖G (loraWeight W₀ B A)‖ ‖ΔB * A + B * ΔA‖ ‖ΔB * ΔA‖ T / 8 := by
  rw [loraFF_eq_curvePoint]
  refine curve_ffStop_le_sub hℓ hG hβ hkT hs hκ ?_
  simpa only [loraFF_eq_curvePoint] using hk

/-- The factor gradients: the directional derivative of `(B, A) ↦ ℓ(W₀ + B A)` in the direction
`(X, Y)` is `⟪∇ℓ Aᵀ, X⟫ + ⟪Bᵀ ∇ℓ, Y⟫`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem lora_hasDerivAt_direction (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (W₀ : Matrix m n ℝ) (B X : Matrix m r ℝ) (A Y : Matrix r n ℝ) :
    HasDerivAt (fun τ => ℓ (loraFF W₀ B X A Y τ))
      (⟪G (loraWeight W₀ B A) * Aᵀ, X⟫ + ⟪Bᵀ * G (loraWeight W₀ B A), Y⟫) 0 := by
  have h := hasDerivAt_loss_curve hℓ (loraWeight W₀ B A) (X * A + B * Y) (X * Y) 0
  simp only [← loraFF_eq_curvePoint] at h
  have e : ⟪G (loraFF W₀ B X A Y 0), curveVel (X * A + B * Y) (X * Y) 0⟫ =
      ⟪G (loraWeight W₀ B A) * Aᵀ, X⟫ + ⟪Bᵀ * G (loraWeight W₀ B A), Y⟫ := by
    have e1 : loraFF W₀ B X A Y 0 = loraWeight W₀ B A := by simp [loraFF]
    rw [e1, curveVel, mul_zero, zero_smul, add_zero, inner_add_right,
      LeanDLRA.Frobenius.inner_mul_right', LeanDLRA.Frobenius.inner_mul_left']
  rwa [e] at h

/-- **After a gradient step on the factors the direction is a descent direction.**  For
`P = ∇ℓ Aᵀ`, `Q = Bᵀ ∇ℓ` at the previous factors and the step `(Δ_B, Δ_A) = -h (P, Q)`, the slope
at the previous point is `-h (‖P‖² + ‖Q‖²)`.  This is derived, not assumed.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem inner_factorStep (W₀ : Matrix m n ℝ) (B : Matrix m r ℝ) (A : Matrix r n ℝ) (h : ℝ)
    {P : Matrix m r ℝ} {Q : Matrix r n ℝ} (hP : P = G (loraWeight W₀ B A) * Aᵀ)
    (hQ : Q = Bᵀ * G (loraWeight W₀ B A)) :
    ⟪G (loraWeight W₀ B A), (-(h • P)) * A + B * (-(h • Q))⟫ = -(h * (‖P‖ ^ 2 + ‖Q‖ ^ 2)) := by
  have e : (-(h • P)) * A + B * (-(h • Q)) = -(h • (P * A + B * Q)) := by
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_add]
    abel
  rw [e, inner_neg_right, inner_smul_right, inner_add_right,
    LeanDLRA.Frobenius.inner_mul_right', LeanDLRA.Frobenius.inner_mul_left', ← hP, ← hQ,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- **Stage length after a gradient step on the LoRA factors** (arXiv 2409.04206, Sec. 3, with an
exact gradient step in place of the paper's Adam).  For the factor gradients `P`, `Q` at `(B, A)`,
the step `(B, A) ↦ (B - h P, A - h Q)` with `0 < h ≤ 1` and a stage with
`(Δ_B, Δ_A) = -h (P, Q)`: if `(T + 1/2) h K_T < ‖P‖² + ‖Q‖²`, where
`K_T = curveCurv β ‖∇ℓ‖ ‖P A + B Q‖ ‖P Q‖ (T + 1)` does not depend on `h`, then every stopping index
is at least `T`.  So the stage length grows like `1 / h`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem lora_ffStop_ge_of_factorStep (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W₀ : Matrix m n ℝ}
    {B : Matrix m r ℝ} {A : Matrix r n ℝ} {P : Matrix m r ℝ} {Q : Matrix r n ℝ}
    (hP : P = G (loraWeight W₀ B A) * Aᵀ) (hQ : Q = Bᵀ * G (loraWeight W₀ B A)) {h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) {T k : ℕ}
    (hT : ((T : ℝ) + 1 / 2) * h *
        curveCurv β ‖G (loraWeight W₀ B A)‖ ‖P * A + B * Q‖ ‖P * Q‖ (T + 1) < ‖P‖ ^ 2 + ‖Q‖ ^ 2)
    (hk : IsFFStop (fun j : ℕ =>
      ℓ (loraFF W₀ (B + -(h • P)) (-(h • P)) (A + -(h • Q)) (-(h • Q)) j)) k) : T ≤ k := by
  set g₀ := ‖G (loraWeight W₀ B A)‖ with hg₀
  set V := (-(h • P)) * A + B * (-(h • Q)) with hV
  set C := (-(h • P)) * (-(h • Q)) with hC
  have hVn : ‖V‖ = h * ‖P * A + B * Q‖ := by
    have e : V = -(h • (P * A + B * Q)) := by
      simp only [hV, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hh0.le]
  have hCn : ‖C‖ = h ^ 2 * ‖P * Q‖ := by
    have e : C = h ^ 2 • (P * Q) := by
      simp only [hC, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_neg,
        neg_neg, smul_smul, pow_two]
    rw [e, norm_smul, Real.norm_of_nonneg (sq_nonneg h)]
  have hs := inner_factorStep (G := G) W₀ B A h hP hQ
  rw [← hV] at hs
  have hstop : IsFFStop (fun j : ℕ => ℓ (curvePoint (loraWeight W₀ B A) V C (j + 1 : ℕ))) k := by
    have e : (fun j : ℕ => ℓ (loraFF W₀ (B + -(h • P)) (-(h • P)) (A + -(h • Q)) (-(h • Q)) j)) =
        fun j : ℕ => ℓ (curvePoint (loraWeight W₀ B A) V C (j + 1 : ℕ)) := by
      funext j
      rw [loraFF_shift, loraFF_eq_curvePoint]
      push_cast
      rfl
    rw [← e]
    exact hk
  refine curve_ffStop_ge_shift hℓ hG hβ ?_ hstop
  rw [hs, neg_neg, hVn, hCn]
  set v := ‖P * A + B * Q‖ with hv
  set c := ‖P * Q‖ with hc
  set S := ‖P‖ ^ 2 + ‖Q‖ ^ 2 with hS
  have hv0 : 0 ≤ v := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hT0 : (0 : ℝ) ≤ (T : ℝ) + 1 := by positivity
  have hg0 : 0 ≤ g₀ := norm_nonneg _
  have hh2 : h ^ 2 ≤ h := by nlinarith
  -- the curvature scales like `h²`
  have hcurv : curveCurv β g₀ (h * v) (h ^ 2 * c) (T + 1) ≤
      h ^ 2 * curveCurv β g₀ v c (T + 1) := by
    simp only [curveCurv]
    have h1 : h * v + 2 * ((T : ℝ) + 1) * (h ^ 2 * c) ≤ h * (v + 2 * ((T : ℝ) + 1) * c) := by
      have : ((T : ℝ) + 1) * c * h ^ 2 ≤ ((T : ℝ) + 1) * c * h :=
        mul_le_mul_of_nonneg_left hh2 (by positivity)
      nlinarith
    have h2 : (h * v + 2 * ((T : ℝ) + 1) * (h ^ 2 * c)) ^ 2 ≤
        h ^ 2 * (v + 2 * ((T : ℝ) + 1) * c) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 2
    have h3 : g₀ + β * ((T : ℝ) + 1) * (h * v + ((T : ℝ) + 1) * (h ^ 2 * c)) ≤
        g₀ + β * ((T : ℝ) + 1) * (v + ((T : ℝ) + 1) * c) := by
      have h4 : h * v ≤ v := by nlinarith
      have h5 : h ^ 2 * c ≤ c := by nlinarith
      have h6 : h * v + ((T : ℝ) + 1) * (h ^ 2 * c) ≤ v + ((T : ℝ) + 1) * c := by
        nlinarith [mul_le_mul_of_nonneg_left h5 hT0]
      have := mul_le_mul_of_nonneg_left h6 (mul_nonneg hβ hT0)
      linarith
    have h7 := mul_le_mul_of_nonneg_left h2 hβ
    have h8 := mul_le_mul_of_nonneg_left h3
      (show 0 ≤ 2 * (h ^ 2 * c) by positivity)
    nlinarith
  have hTpos : (0 : ℝ) ≤ (T : ℝ) + 1 / 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hcurv hTpos
  have h2 := mul_lt_mul_of_pos_left hT hh0
  nlinarith

/-- **As the learning rate goes to `0`, stages on the LoRA factors get arbitrarily long**, as long
as the factor gradient does not vanish: for every `T` there is `h₀ > 0` such that for
`0 < h ≤ h₀` every stopping index of the stage after the step `(B - h P, A - h Q)` is at least `T`.
This also shows that the hypotheses of `lora_ffStop_ge_of_factorStep` can hold for every `T`.
(arXiv 2409.04206, Fast Forward procedure, Sec. 3.) -/
theorem exists_lr_lora_ffStop_ge (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖) (hβ : 0 ≤ β) {W₀ : Matrix m n ℝ}
    {B : Matrix m r ℝ} {A : Matrix r n ℝ} {P : Matrix m r ℝ} {Q : Matrix r n ℝ}
    (hP : P = G (loraWeight W₀ B A) * Aᵀ) (hQ : Q = Bᵀ * G (loraWeight W₀ B A))
    (hne : P ≠ 0 ∨ Q ≠ 0) (T : ℕ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℕ, IsFFStop (fun j : ℕ =>
      ℓ (loraFF W₀ (B + -(h • P)) (-(h • P)) (A + -(h • Q)) (-(h • Q)) j)) k → T ≤ k := by
  set K := curveCurv β ‖G (loraWeight W₀ B A)‖ ‖P * A + B * Q‖ ‖P * Q‖ (T + 1) with hK
  have hK0 : 0 ≤ K := by
    simp only [hK, curveCurv]
    positivity
  set S := ‖P‖ ^ 2 + ‖Q‖ ^ 2 with hS
  have hSpos : 0 < S := by
    rcases hne with h | h
    · have := norm_pos_iff.2 h
      positivity
    · have := norm_pos_iff.2 h
      positivity
  have hdenom : 0 < 2 * ((T : ℝ) + 1 / 2) * (K + 1) := by positivity
  refine ⟨min 1 (S / (2 * ((T : ℝ) + 1 / 2) * (K + 1))), lt_min one_pos (by positivity), ?_⟩
  intro h hh0 hh k hk
  refine lora_ffStop_ge_of_factorStep hℓ hG hβ hP hQ hh0 (hh.trans (min_le_left _ _)) ?_ hk
  have h1 : h * (2 * ((T : ℝ) + 1 / 2) * (K + 1)) ≤ S :=
    (le_div_iff₀ hdenom).1 (hh.trans (min_le_right _ _))
  have h2 : ((T : ℝ) + 1 / 2) * h * K ≤ S / 2 := by
    have : ((T : ℝ) + 1 / 2) * h * (K + 1) ≤ S / 2 := by nlinarith
    have h3 : 0 ≤ ((T : ℝ) + 1 / 2) * h := by positivity
    nlinarith
  rw [← hK, ← hS]
  linarith

end LoRA

end LeanDLRA.Literature.P2409_04206
