import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Dynamics.ContinuousDLRA

/-!
# Rank-adaptive BUG: a-posteriori bounds and tolerance schedules

Error bounds for the rank-adaptive BUG integrator (`IsRankAdaptiveBUGStep`) that extend the core
theorem `rankAdaptiveBUG_global_error`: a bound through a computable residual of the Galerkin
step, and bounds for a truncation tolerance that changes from step to step. Two statements on
Galerkin flows `Z' = R F(t, Z)` in the range of an orthogonal projector `R` come first: a larger
Galerkin space loses at most the stability factor, and for a linear field a Galerkin space that
contains Krylov vectors of the initial value gives an error of high order.

Throughout, `F` is `L`-Lipschitz (`IsLipschitzField`), `A` is an exact solution
(`ODESolution F A`) and the grid is `tₙ = t₀ + n h`.

## Main results

* `galerkin_quasiMonotone_of_le`: for orthogonal projectors with `R' (R x) = R x` (the range of
  `R` lies in the range of `R'`): if the Galerkin flow in `range R` from `R (A t₀)` stays within
  `d` of `A` on `[t₀, t₁]`, the Galerkin flow in `range R'` from `R' (A t₀)` stays within
  `e^{L (t - t₀)} d`.
* `galerkin_krylov_error`: for the linear field `y' = 𝒜 y` and `R` with `R (𝒜ʲ y₀) = 𝒜ʲ y₀` for
  `j ≤ k`, the Galerkin flow from `y₀` has error at most
  `2 e^{h ‖𝒜‖} (h ‖𝒜‖)^{k+1} ‖y₀‖ / (k+1)!` at time `h`.
* `IsRankAdaptiveBUGStep.aposteriori_local_error`: if
  `‖F(t, YS t) - P₁ Q₁ F(t, YS t)‖ ≤ η` along the Galerkin step `YS`, then
  `‖Y₁ - A t₁‖ ≤ ϑ + e^{L h} (‖Y₀ - A t₀‖ + h η)`. Neither the normal bound `ε` nor a bound of
  the field enters.
* `rankAdaptiveBUG_aposteriori_global_error`: along a run with tolerances `ϑ k` and residual
  bounds `η k`, `‖Yₙ - A tₙ‖ ≤ e^{L n h} (‖Y₀ - A t₀‖ + ∑_{k<n} (ϑ k + h η k))`.
* `rankAdaptiveBUG_global_error_sum`: with tolerance `ϑ k` at step `k` and a field bounded by
  `B`, `‖Yₙ - A tₙ‖ ≤ e^{L n h} (‖Y₀ - A t₀‖ + ∑_{k<n} (h (c₁ ε + c₂ h) + ϑ k))`, with
  `c₁ = bugC₁ L H` and `c₂ = bugC₂ L B H` for `h ≤ H`.
* `rankAdaptiveBUG_global_error_of_tol`: if `ϑ k ≤ τ h²` and `‖Y₀ - A t₀‖ ≤ δ`, then for
  `n h ≤ T`, `‖Yₙ - A tₙ‖ ≤ e^{L T} (δ + T (c₁ ε + (c₂ + τ) h))`.

## References

* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, arXiv 2104.05247 (Theorem 2: the bound for a fixed tolerance, in the core as
  `rankAdaptiveBUG_global_error`).
-/

open Set Finset Matrix

namespace LeanDLRA

section Truncation

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n]

end Truncation

section Tie

open EckartYoung

end Tie

section Distance

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε t₀ t₁ : ℝ} {A : ℝ → Matrix m n ℝ}

end Distance

section Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L t₀ t₁ : ℝ} {A : ℝ → E}

/-- **Augmented-space quasi-monotonicity** (source: research idea; OP-RA-26, OP-OT-19). If
`range R ⊆ range R'` (e.g. the augmented BUG space `[K(t₁), U₀] ⊗ [L(t₁), V₀]` versus the BUG
space), the Galerkin flow in the larger space has error at most `e^{L(t - t₀)}` times the
largest error of the flow in the smaller space. -/
theorem galerkin_quasiMonotone_of_le {R R' : E →L[ℝ] E} (hR : IsOrthProj R)
    (hR' : IsOrthProj R') (hle : ∀ x, R' (R x) = R x) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hA : ODESolution F A t₀ t₁) {Z Z' : ℝ → E}
    (hZ : ODESolution (fun t x => R (F t x)) Z t₀ t₁) (hZ₀ : Z t₀ = R (A t₀))
    (hZ' : ODESolution (fun t x => R' (F t x)) Z' t₀ t₁) (hZ'₀ : Z' t₀ = R' (A t₀)) {d : ℝ}
    (hd : ∀ t ∈ Icc t₀ t₁, ‖Z t - A t‖ ≤ d) :
    ∀ t ∈ Icc t₀ t₁, ‖Z' t - A t‖ ≤ Real.exp (L * (t - t₀)) * d := by
  have hZmem : ∀ t ∈ Icc t₀ t₁, R (Z t) = Z t :=
    hZ.galerkin_mem_range hR (by rw [hZ₀, hR.idem])
  have hbest : ∀ t ∈ Icc t₀ t₁, ‖A t - R' (A t)‖ ≤ d := fun t ht =>
    ((hR'.norm_sub_le_of_mem_range (A t) (Z t) (by rw [← hZmem t ht, hle])).trans_eq
      (norm_sub_rev _ _)).trans (hd t ht)
  have hXc : ContinuousOn (fun t => R' (A t)) (Icc t₀ t₁) :=
    R'.continuous.comp_continuousOn hA.cont
  have hX : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => R' (A t)) (R' (F t (A t))) (Ici t) t :=
    fun t ht => R'.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
  have h1 := ODESolution.dlra_norm_sub_le_of_comparison (P := fun _ => R') (κ₁ := 0) (κ₂ := 0)
    (η₁ := L * d) (η₂ := 0) (δ := 0) hF hZ' (fun _ _ => hR') hXc hX
    (fun t ht => by
      rw [zero_mul, zero_add, map_sub, hR'.idem, ← map_sub]
      refine (hR'.norm_le _).trans ?_
      refine (hF t _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [norm_sub_rev]
      exact hbest t ⟨ht.1, ht.2.le⟩)
    (fun t ht => by
      simp [hR'.idem])
    (by rw [hZ'₀, sub_self, norm_zero])
  intro t ht
  have h2 := h1 t ht
  have h3 : gronwallBound 0 (L + 0 + 0) (L * d + 0) (t - t₀) + d ≤ Real.exp (L * (t - t₀)) * d := by
    rw [add_zero, add_zero, add_zero]
    rcases hL.eq_or_lt with rfl | hLp
    · simp [gronwallBound_K0]
    · rw [gronwallBound_of_K_ne_0 hLp.ne']
      simp only
      field_simp
      ring_nf
      rfl
  calc ‖Z' t - A t‖ ≤ ‖Z' t - R' (A t)‖ + ‖R' (A t) - A t‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      rw [norm_sub_rev (R' (A t))]
      linarith [hbest t ht]


private theorem krylov_poly_deriv (M : E →L[ℝ] E) (z₀ : E) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ j ∈ range (k + 1), ((s ^ j / (j.factorial : ℝ)) • (M ^ j) z₀))
      (M (∑ j ∈ range k, ((t ^ j / (j.factorial : ℝ)) • (M ^ j) z₀))) t := by
  induction k with
  | zero => simpa using hasDerivAt_const t z₀
  | succ k ih =>
    have h1 : HasDerivAt (fun s : ℝ => (s ^ (k + 1) / ((k + 1).factorial : ℝ)) •
        (M ^ (k + 1)) z₀) ((t ^ k / (k.factorial : ℝ)) • (M ^ (k + 1)) z₀) t := by
      have := (((hasDerivAt_pow (k + 1) t).div_const ((k + 1).factorial : ℝ)).smul_const
        ((M ^ (k + 1)) z₀))
      convert this using 2
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have h2 := ih.add h1
    have e : (fun s : ℝ => ∑ j ∈ range (k + 1 + 1), ((s ^ j / (j.factorial : ℝ)) • (M ^ j) z₀))
        = fun s => (∑ j ∈ range (k + 1), ((s ^ j / (j.factorial : ℝ)) • (M ^ j) z₀))
          + (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • (M ^ (k + 1)) z₀ := by
      funext s; rw [sum_range_succ _ (k + 1)]
    rw [e]
    convert h2 using 1
    rw [sum_range_succ _ k, map_add, map_smul, pow_succ' M k, mul_apply_eq_comp]

private theorem krylov_tail {M : E →L[ℝ] E} {a h : ℝ} (ha : ‖M‖ ≤ a) {z : ℝ → E}
    (hz : ODESolution (fun _ v => M v) z 0 h) :
    ∀ k : ℕ, ∀ t ∈ Icc 0 h,
      ‖z t - ∑ j ∈ range k, ((t ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0))‖ ≤
        (t * a) ^ k / (k.factorial : ℝ) * Real.exp (t * a) * ‖z 0‖ := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  intro k
  induction k with
  | zero =>
    intro t ht
    have h0 := norm_le_gronwallBound_of_norm_deriv_right_le (f := z) (f' := fun t => M (z t))
      (K := a) (ε := 0) hz.cont hz.deriv (δ := ‖z 0‖) le_rfl (fun x _ => by
        rw [add_zero]; exact M.le_of_opNorm_le ha _) t ht
    rw [gronwallBound_ε0, sub_zero] at h0
    simpa [mul_comm] using h0
  | succ k ih =>
    intro t ht
    set c := ‖z 0‖ with hc
    let f : ℝ → E := fun s =>
      z s - ∑ j ∈ range (k + 1), ((s ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0))
    let B : ℝ → ℝ := fun s => (s * a) ^ (k + 1) / ((k + 1).factorial : ℝ) * Real.exp (s * a) * c
    have hfc : ContinuousOn f (Icc 0 h) := by
      refine hz.cont.sub ?_
      fun_prop
    have hf' : ∀ s ∈ Ico 0 h, HasDerivWithinAt f
        (M (z s - ∑ j ∈ range k, ((s ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0)))) (Ici s) s := by
      intro s hs
      have := (hz.deriv s hs).sub (krylov_poly_deriv M (z 0) k s).hasDerivWithinAt
      rwa [map_sub]
    have hB : ∀ x, HasDerivAt B ((((k + 1 : ℕ) : ℝ) * (x * a) ^ k * a / ((k + 1).factorial : ℝ)
        * Real.exp (x * a) + (x * a) ^ (k + 1) / ((k + 1).factorial : ℝ) * (Real.exp (x * a) * a))
        * c) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => s * a) a x := by
        simpa using (hasDerivAt_id x).mul_const a
      have h2 := (h1.pow (k + 1)).div_const ((k + 1).factorial : ℝ)
      have h3 := (h1.exp)
      have h4 := (h2.mul h3).mul_const c
      simpa using h4
    have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := f) hfc hf'
      (B := B) (a := 0) (b := h) (by
        have h0 : ∑ j ∈ range (k + 1), (((0 : ℝ) ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0))
            = z 0 := by
          rw [sum_range_succ']; simp
        simp only [f, B, h0, sub_self, norm_zero, zero_mul]
        simp) hB (fun s hs => by
      have hs0 : 0 ≤ s := hs.1
      have hr := ih s ⟨hs.1, hs.2.le⟩
      calc ‖M (z s - ∑ j ∈ range k, ((s ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0)))‖
          ≤ a * ‖z s - ∑ j ∈ range k, ((s ^ j / (j.factorial : ℝ)) • (M ^ j) (z 0))‖ :=
            M.le_of_opNorm_le ha _
        _ ≤ a * ((s * a) ^ k / (k.factorial : ℝ) * Real.exp (s * a) * c) :=
            mul_le_mul_of_nonneg_left hr ha0
        _ ≤ _ := by
          have hpos : 0 ≤ (s * a) ^ (k + 1) / ((k + 1).factorial : ℝ) *
              (Real.exp (s * a) * a) * c :=
            mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg (mul_nonneg hs0 ha0) _)
              (Nat.cast_nonneg _)) (mul_nonneg (Real.exp_pos _).le ha0)) (norm_nonneg _)
          have heq : (((k + 1 : ℕ) : ℝ) * (s * a) ^ k * a / ((k + 1).factorial : ℝ)
              * Real.exp (s * a)) * c =
              a * ((s * a) ^ k / (k.factorial : ℝ) * Real.exp (s * a) * c) := by
            rw [Nat.factorial_succ]; push_cast
            field_simp
          nlinarith) ht
    exact hmain

/-- **Krylov enrichment gives high order** (source: OP-RA-14; initial bond enrichment). For a
linear field `y' = 𝒜 y` and a projector `R` whose range contains `y₀, 𝒜 y₀, …, 𝒜ᵏ y₀`, the
Galerkin flow `y' = R 𝒜 y` from `y₀` has error
`≤ 2 e^{h ‖𝒜‖} (h ‖𝒜‖)^{k+1} ‖y₀‖ / (k+1)!` at time `h`, instead of `O(h ε)`. -/
theorem galerkin_krylov_error {𝒜 R : E →L[ℝ] E} (hR : IsOrthProj R) {k : ℕ} {y₀ : E}
    (hK : ∀ j ≤ k, R ((𝒜 ^ j) y₀) = (𝒜 ^ j) y₀) {h : ℝ} (hh : 0 ≤ h) {x y : ℝ → E}
    (hx : ODESolution (fun _ v => 𝒜 v) x 0 h) (hx₀ : x 0 = y₀)
    (hy : ODESolution (fun _ v => R (𝒜 v)) y 0 h) (hy₀ : y 0 = y₀) :
    ‖y h - x h‖ ≤
      2 * Real.exp (h * ‖𝒜‖) * (h * ‖𝒜‖) ^ (k + 1) / (k + 1).factorial * ‖y₀‖ := by
  have hRn : ‖R * 𝒜‖ ≤ ‖𝒜‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (fun v => (hR.norm_le _).trans (𝒜.le_opNorm v))
  have hmem : h ∈ Icc 0 h := ⟨hh, le_rfl⟩
  have hx' := krylov_tail (le_refl ‖𝒜‖) hx (k + 1) h hmem
  have hy' := krylov_tail (M := R * 𝒜) hRn hy (k + 1) h hmem
  rw [hx₀] at hx'
  rw [hy₀] at hy'
  have hpow : ∀ j ≤ k, ((R * 𝒜) ^ j) y₀ = (𝒜 ^ j) y₀ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [pow_succ', mul_apply_eq_comp, ih (by omega)]
      simpa only [mul_apply_eq_comp, pow_succ'] using hK (j + 1) hj
  have hsum : ∑ j ∈ range (k + 1), ((h ^ j / (j.factorial : ℝ)) • ((R * 𝒜) ^ j) y₀)
      = ∑ j ∈ range (k + 1), ((h ^ j / (j.factorial : ℝ)) • (𝒜 ^ j) y₀) :=
    sum_congr rfl fun j hj => by rw [hpow j (by have := mem_range.1 hj; omega)]
  rw [hsum] at hy'
  set S : E := ∑ j ∈ range (k + 1), ((h ^ j / (j.factorial : ℝ)) • (𝒜 ^ j) y₀) with hS
  have := norm_sub_le_norm_sub_add_norm_sub (y h) S (x h)
  have e : ‖S - x h‖ = ‖x h - S‖ := norm_sub_rev _ _
  calc ‖y h - x h‖ ≤ _ := this
    _ ≤ _ := by
      rw [e]
      have := add_le_add hy' hx'
      refine this.trans (le_of_eq ?_)
      ring


end Galerkin

section RankAdaptive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : ℝ → E → E} {L B ε : ℝ}

/-- **Reliable a posteriori local error estimate** (source: OP-RA-24). For one rank-adaptive BUG
step, the computable residual `η ≥ ‖(1 - P₁Q₁) F(t, YS t)‖` of the Galerkin S-step bounds the
error against **any** exact solution: `‖Y₁ - A(t₁)‖ ≤ ϑ + e^{L h} (‖Y₀ - A(t₀)‖ + h η)`, with no
normal-component assumption `ε` and no bound `B`. -/
theorem IsRankAdaptiveBUGStep.aposteriori_local_error {ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E}
    {t₀ t₁ h : ℝ} {Y₀ Y₁ : E} {YK YL YS A : ℝ → E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) {η : ℝ}
    (hη : ∀ t ∈ Icc t₀ t₁, ‖F t (YS t) - P₁ (Q₁ (F t (YS t)))‖ ≤ η) :
    ‖Y₁ - A t₁‖ ≤ ϑ + Real.exp (L * h) * (‖Y₀ - A t₀‖ + h * η) := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη t₀ ⟨le_rfl, by linarith⟩)
  have hdef : ∀ t ∈ Ico t₀ t₁, ‖(P₁ * Q₁) (F t (YS t)) - F t (YS t)‖ ≤ η := fun t ht => by
    rw [norm_sub_rev]
    exact hη t ⟨ht.1, ht.2.le⟩
  have h1 := hA.norm_sub_le_of_perturbed hs.sSol' hF.isOneSidedLipschitzField hdef t₁
    ⟨by linarith, le_rfl⟩
  rw [hs.start_eq, show t₁ - t₀ = h by linarith] at h1
  have h2 := (gronwallBound_le_exp_mul (δ := ‖Y₀ - A t₀‖) (x := h) hL hη0).trans' h1
  have h3 := hs.trunc
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Reliable a posteriori global error estimate** (source: OP-RA-24). Along a run of
rank-adaptive BUG steps with step-dependent tolerances `ϑ k` and Galerkin residuals `η k`,
`‖Yₙ - A(tₙ)‖ ≤ e^{L n h} (‖Y₀ - A(t₀)‖ + ∑_{k<n} (ϑ k + h η k))`: a fully computable bound,
with no exact flows `Φ` from the numerical values. -/
theorem rankAdaptiveBUG_aposteriori_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E} {ϑ η : ℕ → ℝ}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hη : ∀ n < N, ∀ t ∈ Icc (t₀ + n * h) (t₀ + (n + 1) * h),
      ‖F t (YS n t) - Pa n (Qa n (F t (YS n t)))‖ ≤ η n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, (ϑ k + h * η k)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - A (t₀ + ((n + 1 : ℕ) : ℝ) * h)‖ ≤
      Real.exp (L * h) * ‖Y n - A (t₀ + n * h)‖ + (ϑ n + Real.exp (L * h) * (h * η n)) := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have hNh : ((n : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hn' hh
    have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
    have hAn : ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) :=
      hA.mono (by linarith) (by linarith)
    have := (hstep n hn).aposteriori_local_error hF hL (h := h) (by ring) hh hAn (hη n hn)
    push_cast
    linarith
  have hϑ0 : ∀ n < N, 0 ≤ ϑ n := fun n hn => (hstep n hn).tol_nonneg
  have hη0 : ∀ n < N, 0 ≤ η n := fun n hn => (norm_nonneg _).trans
    (hη n hn (t₀ + n * h) ⟨le_rfl, by
      have : (0 : ℝ) ≤ h := hh
      linarith⟩)
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hloc n (by omega)
    have hLh : 0 ≤ L * (n * h) := mul_nonneg hL (mul_nonneg (Nat.cast_nonneg _) hh)
    have hexp : Real.exp (L * h) * Real.exp (L * (n * h))
        = Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hone : 1 ≤ Real.exp (L * (n * h)) := Real.one_le_exp hLh
    have hS : 0 ≤ ϑ n + h * η n := add_nonneg (hϑ0 n (by omega))
      (mul_nonneg hh (hη0 n (by omega)))
    have hc : 0 ≤ ϑ n := hϑ0 n (by omega)
    have hd : 0 ≤ h * η n := mul_nonneg hh (hη0 n (by omega))
    have hE : 0 < Real.exp (L * h) := Real.exp_pos _
    rw [sum_range_succ]
    calc ‖Y (n + 1) - A (t₀ + ((n + 1 : ℕ) : ℝ) * h)‖
        ≤ Real.exp (L * h) * ‖Y n - A (t₀ + n * h)‖ + (ϑ n + Real.exp (L * h) * (h * η n)) := h2
      _ ≤ Real.exp (L * h) * (Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n,
          (ϑ k + h * η k))) + (ϑ n + Real.exp (L * h) * (h * η n)) := by
        have := mul_le_mul_of_nonneg_left h1 hE.le
        linarith
      _ ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n,
          (ϑ k + h * η k)) + Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * (ϑ n + h * η n) := by
        rw [← mul_assoc, hexp]
        have hbig : Real.exp (L * h) ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) := by
          rw [← hexp]; exact le_mul_of_one_le_right hE.le hone
        have hbig1 : 1 ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) := by
          rw [← hexp]; exact one_le_mul_of_one_le_of_one_le (by
            exact Real.one_le_exp (mul_nonneg hL hh)) hone
        have e1 : ϑ n ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * ϑ n :=
          le_mul_of_one_le_left hc hbig1
        have e2 : Real.exp (L * h) * (h * η n) ≤
            Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * (h * η n) :=
          mul_le_mul_of_nonneg_right hbig hd
        nlinarith
      _ = _ := by ring

/-- **Rank-adaptive BUG with a tolerance schedule** (source: OP-RA-04; arXiv 2104.05247,
Theorem 2 with step-dependent `ϑ`). With tolerance `ϑ k` at step `k`,
`‖Yₙ - A(tₙ)‖ ≤ e^{L n h} (‖Y₀ - A(t₀)‖ + ∑_{k<n} (h (c₁ ε + c₂ h) + ϑ k))`. -/
theorem rankAdaptiveBUG_global_error_sum (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E} {ϑ : ℕ → ℝ}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + ∑ k ∈ range n, (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ n := fun n hn =>
    (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  exact lady_windermere_sum hF hL hh hA hΦ hΦ₀ hloc

/-- **Tolerance control preserves first order** (source: OP-RA-04 (i); the contrasting
lower bound for `ϑ = O(h)` is OP-RA-17). If the
truncation tolerance is scaled as `ϑ k ≤ τ h²`, the accumulated truncation error is `O(h)` and
`‖Yₙ - A(tₙ)‖ ≤ e^{L T} (δ + T (c₁ ε + (c₂ + τ) h))` for `n h ≤ T`, uniformly in `n` (in
contrast to `ϑ = O(h)`, where the `n ϑ` term is `O(1)`). -/
theorem rankAdaptiveBUG_global_error_of_tol (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E} {ϑ : ℕ → ℝ}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε (ϑ n) (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {τ : ℝ} (hτ : 0 ≤ τ)
    (hϑ : ∀ n < N, ϑ n ≤ τ * h ^ 2) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤
        Real.exp (L * T) * (δ + T * (bugC₁ L H * ε + (bugC₂ L B H + τ) * h)) := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have h1 := rankAdaptiveBUG_global_error_sum hF hL hB hh hhH hA hstep hΦ hΦ₀ n hn
  set g := bugC₁ L H * ε + (bugC₂ L B H + τ) * h with hg_def
  have hg : 0 ≤ g :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (add_nonneg (bugC₂_nonneg hL hB.nonneg hH) hτ) hh)
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hterm : ∀ k ∈ range n,
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k ≤ h * g := fun k hk => by
    have := hϑ k (lt_of_lt_of_le (mem_range.1 hk) hn)
    rw [hg_def]
    nlinarith [this]
  have hnn : ∀ k ∈ range n, 0 ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k := fun k hk =>
    add_nonneg (mul_nonneg hh (add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)))
      (hstep k (lt_of_lt_of_le (mem_range.1 hk) hn)).tol_nonneg
  have hsum : ∑ k ∈ range n, (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k) ≤ T * g := by
    calc _ ≤ ∑ k ∈ range n, h * g := sum_le_sum hterm
      _ = (n * h) * g := by simp [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ T * g := mul_le_mul_of_nonneg_right hT hg
  have hX : 0 ≤ ‖Y 0 - A t₀‖ + ∑ k ∈ range n, (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k) :=
    add_nonneg (norm_nonneg _) (sum_nonneg hnn)
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  calc ‖Y n - A (t₀ + n * h)‖ ≤ _ := h1
    _ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n,
        (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ k)) := mul_le_mul_of_nonneg_right hexp hX
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

end RankAdaptive

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end QuasiOptimal

end LeanDLRA
