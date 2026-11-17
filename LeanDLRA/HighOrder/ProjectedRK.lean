import LeanDLRA.HighOrder.RungeKuttaBUG

/-!
# Projected Runge–Kutta methods: stage analysis and local error

The projected Runge–Kutta methods of Kieri and Vandereycken approximate the solution of
`Y' = F(t, Y)` on a set `ℳ` (the matrices or tensor trains of rank at most `r`) by an explicit
Runge–Kutta scheme whose stage derivatives are projected onto tangent spaces and whose stages
and result are retracted to `ℳ` ([KieriVandereycken2019], eqs. (26), (27)):

  `Z_j = y + h ∑_{l<j} a_{jl} e_l`,  `η_j = ℛ(Z_j)`,  `e_j = P(η_j) F(t_j, η_j)`,
  `y₁ = ℛ(y + h ∑_j b_j e_j)`,

with a quasi-optimal retraction `ℛ` (`‖ℛ(x) - x‖ ≤ κ ‖z - x‖` for all `z ∈ ℳ`). This file
compares such a step with the classical Runge–Kutta step
`Z̃_j = y + h ∑_{l<j} a_{jl} F(t_j, Z̃_l)`, `z̃ = y + h ∑_j b_j F(t_j, Z̃_j)` and with the exact
solution, and proves the local error `h C (ε + g + K h^{q'})` ([KieriVandereycken2019], Lemma 7
and the proof of Theorem 6).

The setting is abstract: a normed space `E`, a set `ℳ ⊆ E`, and the values of the scheme as
data. `Fη j` stands for the field at the stage `η j` and `FZt j` for the field at the classical
stage `Z̃ j` (at the same stage time); the analysis uses

* the normal bound `‖e_j - Fη_j‖ ≤ ε` (their assumption (10): `e_j` is the tangent part of
  `Fη_j` and `η_j ∈ ℳ`),
* the Lipschitz bound `‖Fη_j - FZt_j‖ ≤ L ‖η_j - Z̃_j‖` at these pairs only (their (8)),
* the stage orders `‖Z̃_j - w_j‖ ≤ K h^{q_j + 1}` and the order `‖z̃ - w_f‖ ≤ K h^{p + 1}`, where
  `w_j`, `w_f` are the exact solution at the stage times and at the end of the step (their (30)
  and (19)),
* the closeness of these exact values to `ℳ`: `dist(w_j, ℳ) ≤ h g`, `dist(w_f, ℳ) ≤ h g` (their
  (15), with `g = ε max {1, e^{ℓ h}}`; for matrices it is `distLR_flow_le_exp_of_tube` with
  `g = ε e^{L h}`).

The stage orders and the order are hypotheses: the library has no order theory of Runge–Kutta
methods. The step size is at most `1` (the paper's `h ≤ h₀`).

## Main definitions

* `ProjectedRK.stageGrowth a b L κ = 1 + L κ + L (1 + κ) α`, `α = tabWeight a b`.
* `ProjectedRK.localErrorConst a b L κ = (1 + κ) (α γ^s + 2)`, `γ = stageGrowth a b L κ`.

## Main results

* `ProjectedRK.norm_stage_sub_le` ([KieriVandereycken2019], Lemma 7): the first stage agrees with
  the classical one and its projected derivative is `ε`-close to the classical derivative; for
  the later stages `‖Z_j - Z̃_j‖ ≤ α γ^s h (ε + g + K h^{q₂+1})` and
  `‖e_j - F(Z̃_j)‖ ≤ γ^s (ε + g + K h^{q̃_j + 1})`, `q̃_j = min(q_j, q₂ + 1)`.
* `ProjectedRK.norm_sub_le_of_stages` ([KieriVandereycken2019], proof of Theorem 6, eq. (38)):
  `‖y₁ - w_f‖ ≤ h · localErrorConst a b L κ · (ε + g + K h^{q'})` for every admissible `q'`.
* `ProjectedRK.admissible_min_q₂`, `ProjectedRK.admissible_of_b₂_eq_zero`: the exponent of
  Theorem 6 (`min(p, q₂ + 1)`, and `min(p, q₃ + 1, q₂ + 2)` when `b₂ = 0`) is admissible.
* `ProjectedRK.exists_explicit_stages`: the stages of an explicit scheme can be chosen one after
  the other.

## Implementation notes

Stages are indexed by `Fin s` from `0`; stage `j` with `j.val = 0` is the paper's stage `1`, and
`q₂` is the order of the stage with `j.val = 1`. Only `q₂ ≤ q_j` for the later stages is used,
not the full ordering `q₁ ≤ ⋯ ≤ q_s` of the paper. The constants are those of the proof and are
not optimised.

## References

* [KieriVandereycken2019] E. Kieri, B. Vandereycken, *Projection methods for dynamical low-rank
  approximation of high-dimensional problems*, Comput. Methods Appl. Math. 19 (2019), §5.2.
-/

open Finset

namespace LeanDLRA.ProjectedRK

open LeanDLRA.RungeKuttaBUG

/-! ### Constants -/

section Constants

variable {s : ℕ}

/-- The growth factor `γ = 1 + L κ + L (1 + κ) α` of the stage errors of a projected
Runge–Kutta step, `α = tabWeight a b` (a bound for the row sums `∑_l |a_{jl}|` and for
`∑_j |b_j|`), `κ` the quasi-optimality constant of the retraction. -/
noncomputable def stageGrowth (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L κ : ℝ) : ℝ :=
  1 + L * κ + L * (1 + κ) * tabWeight a b

/-- The constant `(1 + κ) (α γ^s + 2)` of the local error of a projected Runge–Kutta step
(`ProjectedRK.norm_sub_le_of_stages`), `α = tabWeight a b`, `γ = stageGrowth a b L κ`. -/
noncomputable def localErrorConst (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) (L κ : ℝ) : ℝ :=
  (1 + κ) * (tabWeight a b * stageGrowth a b L κ ^ s + 2)

/-- `γ ≥ 1`. -/
theorem one_le_stageGrowth (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) {L κ : ℝ} (hL : 0 ≤ L)
    (hκ : 0 ≤ κ) : 1 ≤ stageGrowth a b L κ := by
  have := tabWeight_nonneg a b
  unfold stageGrowth
  have : 0 ≤ L * κ := mul_nonneg hL hκ
  have : 0 ≤ L * (1 + κ) * tabWeight a b := by positivity
  linarith

/-- The local error constant is not negative. -/
theorem localErrorConst_nonneg (a : Fin s → Fin s → ℝ) (b : Fin s → ℝ) {L κ : ℝ} (hL : 0 ≤ L)
    (hκ : 0 ≤ κ) : 0 ≤ localErrorConst a b L κ := by
  have := tabWeight_nonneg a b
  have := one_le_stageGrowth a b hL hκ
  unfold localErrorConst
  positivity

end Constants

/-! ### Existence of the stages of an explicit scheme -/

/-- **The stages of an explicit scheme can be chosen one after the other.** Let `P j Z x` say
that `x` is an admissible value of stage `j` given the stages `Z`, and suppose that it depends
only on the stages `Z l` with `l < j` and that an admissible value exists for every `Z`. Then
there are stages `Z` such that every `Z j` is admissible given `Z`. -/
theorem exists_explicit_stages {s : ℕ} {X : Type*} [Nonempty X]
    (P : Fin s → (Fin s → X) → X → Prop)
    (hP : ∀ j (Z Z' : Fin s → X) (x : X), (∀ l, l < j → Z l = Z' l) → P j Z x → P j Z' x)
    (hex : ∀ j (Z : Fin s → X), ∃ x, P j Z x) : ∃ Z : Fin s → X, ∀ j, P j Z (Z j) := by
  classical
  have key : ∀ k : ℕ, k ≤ s → ∃ Z : Fin s → X, ∀ j : Fin s, j.val < k → P j Z (Z j) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => Classical.arbitrary X, fun j hj => absurd hj (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZ⟩ := ih (by omega)
      set j₀ : Fin s := ⟨k, by omega⟩ with hj₀
      obtain ⟨x, hx⟩ := hex j₀ Z
      refine ⟨Function.update Z j₀ x, fun j hj => ?_⟩
      have hagree : ∀ i : Fin s, i.val < k → Function.update Z j₀ x i = Z i := fun i hi =>
        Function.update_of_ne (fun h => by rw [h] at hi; simp [hj₀] at hi) _ _
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [hagree j hj]
        exact hP j Z _ _ (fun l hl => (hagree l (lt_trans hl hj)).symm) (hZ j hj)
      · have hjj : j = j₀ := Fin.ext hj
        subst hjj
        rw [Function.update_self]
        exact hP _ Z _ _ (fun l hl => (hagree l hl).symm) hx
  obtain ⟨Z, hZ⟩ := key s le_rfl
  exact ⟨Z, fun j => hZ j j.isLt⟩

/-! ### The stages -/

section Stages

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ}
  {a : Fin s → Fin s → ℝ} {b : Fin s → ℝ} {ℳ : Set E} {κ L ε g K h : ℝ} {y : E}
  {Z η e Fη Zt FZt w : Fin s → E}

/-- **Stage bounds of a projected Runge–Kutta step** ([KieriVandereycken2019], Lemma 7, with
explicit constants). Let the tableau be explicit, `y ∈ ℳ`, `0 ≤ h ≤ 1`, and let

* `Z j = y + h ∑_l a_{jl} e_l` and `η j` a `κ`-quasi-optimal point of `ℳ` for `Z j`,
* `‖e j - Fη j‖ ≤ ε` and `‖Fη j - FZt j‖ ≤ L ‖η j - Zt j‖`,
* `Zt j = y + h ∑_l a_{jl} FZt_l` (the classical stages),
* for the stages `j` with `j.val > 0`: `‖Zt j - w j‖ ≤ K h^{q_j + 1}`, `q₂ ≤ q_j`, and a point of
  `ℳ` within `h g` of `w j`.

Then, with `α = tabWeight a b` and `γ = stageGrowth a b L κ`, the first stage satisfies
`Z j = Zt j` and `‖e j - FZt j‖ ≤ ε`, and the later stages satisfy

  `‖Z j - Zt j‖ ≤ α γ^s h (ε + g + K h^{q₂+1})`,
  `‖e j - FZt j‖ ≤ γ^s (ε + g + K h^{min(q_j, q₂+1) + 1})`

(their (33) and (34)). -/
theorem norm_stage_sub_le (ha : ∀ i j, i ≤ j → a i j = 0) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hg : 0 ≤ g) (hK : 0 ≤ K) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hy : y ∈ ℳ)
    (hZ : ∀ j, Z j = y + h • ∑ l, a j l • e l)
    (hη : ∀ j, ∀ z ∈ ℳ, ‖η j - Z j‖ ≤ κ * ‖z - Z j‖)
    (he : ∀ j, ‖e j - Fη j‖ ≤ ε) (hLip : ∀ j, ‖Fη j - FZt j‖ ≤ L * ‖η j - Zt j‖)
    (hZt : ∀ j, Zt j = y + h • ∑ l, a j l • FZt l) {q : Fin s → ℕ} {q₂ : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j)
    (hw : ∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1))
    (hM : ∀ j : Fin s, 0 < j.val → ∃ z ∈ ℳ, ‖z - w j‖ ≤ h * g) (j : Fin s) :
    (j.val = 0 → Z j = Zt j ∧ ‖e j - FZt j‖ ≤ ε) ∧
    (0 < j.val →
      ‖Z j - Zt j‖ ≤ tabWeight a b * stageGrowth a b L κ ^ s * h * (ε + g + K * h ^ (q₂ + 1)) ∧
      ‖e j - FZt j‖ ≤ stageGrowth a b L κ ^ s * (ε + g + K * h ^ (min (q j) (q₂ + 1) + 1))) := by
  set γ := stageGrowth a b L κ with hγdef
  set α := tabWeight a b with hαdef
  have hγ : 1 ≤ γ := one_le_stageGrowth a b hL hκ
  have hα : 0 ≤ α := tabWeight_nonneg a b
  -- the first stage is `y` in both schemes
  have hfirst : ∀ j : Fin s, j.val = 0 → Z j = y ∧ Zt j = y := by
    intro j hj
    have h0 : ∀ l, a j l = 0 := fun l =>
      ha j l (by rw [Fin.le_iff_val_le_val, hj]; exact Nat.zero_le _)
    exact ⟨by rw [hZ j]; simp [h0], by rw [hZt j]; simp [h0]⟩
  have hE0 : ∀ j : Fin s, j.val = 0 → ‖e j - FZt j‖ ≤ ε := by
    intro j hj
    obtain ⟨hZy, hZty⟩ := hfirst j hj
    have hηy : η j = y := by
      have h₁ := hη j y hy
      rw [hZy, sub_self, norm_zero, mul_zero] at h₁
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h₁)
    have h₁ := hLip j
    rw [hηy, hZty, sub_self, norm_zero, mul_zero] at h₁
    calc ‖e j - FZt j‖ ≤ ‖e j - Fη j‖ + ‖Fη j - FZt j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + 0 := add_le_add (he j) h₁
      _ = ε := add_zero ε
  have hdiff : ∀ j, ‖Z j - Zt j‖ ≤ h * ∑ l, |a j l| * ‖e l - FZt l‖ := by
    intro j
    have h₁ : Z j - Zt j = h • ∑ l, a j l • (e l - FZt l) := by
      rw [hZ j, hZt j]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h₁, norm_smul, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)) hh
    rw [norm_smul, Real.norm_eq_abs]
  -- one stage: the projected derivative against the classical one
  have hE : ∀ j : Fin s, 0 < j.val → ‖e j - FZt j‖ ≤
      ε + L * (κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖) := by
    intro j hj
    obtain ⟨z, hz, hzw⟩ := hM j hj
    have hzZ : ‖z - Z j‖ ≤ h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖ := by
      have h₂ : ‖w j - Zt j‖ ≤ K * h ^ (q j + 1) := by rw [norm_sub_rev]; exact hw j hj
      calc ‖z - Z j‖ ≤ ‖z - Zt j‖ + ‖Zt j - Z j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (‖z - w j‖ + ‖w j - Zt j‖) + ‖Zt j - Z j‖ :=
            add_le_add (norm_sub_le_norm_sub_add_norm_sub _ _ _) le_rfl
        _ ≤ h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖ := by
            rw [norm_sub_rev (Zt j)]; linarith
    have h₂ : ‖η j - Zt j‖ ≤ κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖ := by
      calc ‖η j - Zt j‖ ≤ ‖η j - Z j‖ + ‖Z j - Zt j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ κ * ‖z - Z j‖ + ‖Z j - Zt j‖ := add_le_add (hη j z hz) le_rfl
        _ ≤ κ * (h * g + K * h ^ (q j + 1) + ‖Z j - Zt j‖) + ‖Z j - Zt j‖ := by gcongr
        _ = _ := by ring
    calc ‖e j - FZt j‖ ≤ ‖e j - Fη j‖ + ‖Fη j - FZt j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + L * ‖η j - Zt j‖ := add_le_add (he j) (hLip j)
      _ ≤ _ := by gcongr
  set X := ε + g + K * h ^ (q₂ + 1) with hXdef
  have hX0 : 0 ≤ X := add_nonneg (add_nonneg hε hg) (mul_nonneg hK (pow_nonneg hh _))
  -- one stage, given the bounds of the earlier stages
  have hstep : ∀ j : Fin s, 0 < j.val →
      (∀ l : Fin s, l < j → ‖e l - FZt l‖ ≤ γ ^ l.val * X) →
      ‖Z j - Zt j‖ ≤ α * γ ^ (j.val - 1) * h * X ∧
      ‖e j - FZt j‖ ≤ γ ^ j.val * (ε + g + K * h ^ (min (q j) (q₂ + 1) + 1)) := by
    intro j hj IH
    have hd : ‖Z j - Zt j‖ ≤ α * γ ^ (j.val - 1) * h * X := by
      refine (hdiff j).trans ?_
      have hs := sum_abs_mul_le (w := a j) (D := fun l => ‖e l - FZt l‖)
        (X := γ ^ (j.val - 1) * X) (mul_nonneg (pow_nonneg (by linarith) _) hX0)
        (fun l hl => by
          have hlj : l < j := lt_of_not_ge fun hjl => hl (ha j l hjl)
          refine (IH l hlj).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hγ ?_) hX0)
          have : l.val < j.val := hlj
          omega) (row_le_tabWeight a b j)
      calc h * ∑ l, |a j l| * ‖e l - FZt l‖ ≤ h * (α * (γ ^ (j.val - 1) * X)) :=
            mul_le_mul_of_nonneg_left hs hh
        _ = α * γ ^ (j.val - 1) * h * X := by ring
    refine ⟨hd, ?_⟩
    set qt := min (q j) (q₂ + 1) with hqt
    set Xj := ε + g + K * h ^ (qt + 1) with hXj
    have hpow1 : h ^ (q j + 1) ≤ h ^ (qt + 1) :=
      pow_le_pow_of_le_one hh hh1 (by omega)
    have hpow2 : h * h ^ (q₂ + 1) ≤ h ^ (qt + 1) := by
      rw [← pow_succ']
      exact pow_le_pow_of_le_one hh hh1 (by omega)
    have hhX : h * X ≤ Xj := by
      have h₁ : h * ε ≤ ε := mul_le_of_le_one_left hε hh1
      have h₂ : h * g ≤ g := mul_le_of_le_one_left hg hh1
      have h₃ : h * (K * h ^ (q₂ + 1)) ≤ K * h ^ (qt + 1) := by
        rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hpow2 hK
      rw [hXdef, hXj]
      nlinarith
    have hXj0 : 0 ≤ Xj := add_nonneg (add_nonneg hε hg) (mul_nonneg hK (pow_nonneg hh _))
    have hγj : γ ^ (j.val - 1) * γ = γ ^ j.val := by
      rw [← pow_succ]; congr 1; omega
    have hγj1 : 1 ≤ γ ^ (j.val - 1) := one_le_pow₀ hγ
    have hd' : (1 + κ) * ‖Z j - Zt j‖ ≤ (1 + κ) * (α * γ ^ (j.val - 1) * Xj) := by
      refine mul_le_mul_of_nonneg_left (hd.trans ?_) (by linarith)
      have : 0 ≤ α * γ ^ (j.val - 1) := mul_nonneg hα (by positivity)
      calc α * γ ^ (j.val - 1) * h * X = α * γ ^ (j.val - 1) * (h * X) := by ring
        _ ≤ α * γ ^ (j.val - 1) * Xj := mul_le_mul_of_nonneg_left hhX this
    have hκg : κ * (h * g + K * h ^ (q j + 1)) ≤ κ * Xj := by
      refine mul_le_mul_of_nonneg_left ?_ hκ
      have h₂ : h * g ≤ g := mul_le_of_le_one_left hg hh1
      have h₃ : K * h ^ (q j + 1) ≤ K * h ^ (qt + 1) := mul_le_mul_of_nonneg_left hpow1 hK
      rw [hXj]; linarith
    calc ‖e j - FZt j‖
        ≤ ε + L * (κ * (h * g + K * h ^ (q j + 1)) + (1 + κ) * ‖Z j - Zt j‖) := hE j hj
      _ ≤ Xj + L * (κ * Xj + (1 + κ) * (α * γ ^ (j.val - 1) * Xj)) := by
          have : ε ≤ Xj := by
            rw [hXj]; have := mul_nonneg hK (pow_nonneg hh (qt + 1)); linarith
          gcongr
      _ = (1 + L * κ + L * (1 + κ) * α * γ ^ (j.val - 1)) * Xj := by ring
      _ ≤ (γ ^ (j.val - 1) * (1 + L * κ + L * (1 + κ) * α)) * Xj := by
          refine mul_le_mul_of_nonneg_right ?_ hXj0
          have hLκ : 0 ≤ L * κ := mul_nonneg hL hκ
          nlinarith
      _ = γ ^ j.val * Xj := by rw [← hγj, hγdef, stageGrowth, ← hαdef]
  -- all stages
  have hall : ∀ k : ℕ, ∀ i : Fin s, i.val < k → ‖e i - FZt i‖ ≤ γ ^ i.val * X := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · rw [h0, pow_zero, one_mul]
        have := mul_nonneg hK (pow_nonneg hh (q₂ + 1))
        linarith [hE0 i h0, hg]
      · have hs := (hstep i hpos fun l hl => ih l (by have : l.val < i.val := hl; omega)).2
        refine hs.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _))
        have : h ^ (min (q i) (q₂ + 1) + 1) ≤ h ^ (q₂ + 1) :=
          pow_le_pow_of_le_one hh hh1 (by have := hq i hpos; omega)
        have := mul_le_mul_of_nonneg_left this hK
        linarith
  refine ⟨fun hj => ⟨(hfirst j hj).1.trans (hfirst j hj).2.symm, hE0 j hj⟩, fun hj => ?_⟩
  obtain ⟨hd, hEj⟩ := hstep j hj fun l _ => hall s l l.isLt
  have hjs : j.val ≤ s := j.isLt.le
  constructor
  · refine hd.trans ?_
    have : γ ^ (j.val - 1) ≤ γ ^ s := pow_le_pow_right₀ hγ (by omega)
    have := mul_le_mul_of_nonneg_left this hα
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hh hX0)
    nlinarith
  · refine hEj.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hγ hjs) ?_)
    exact add_nonneg (add_nonneg hε hg) (mul_nonneg hK (pow_nonneg hh _))

/-- **Local error of a projected Runge–Kutta step** ([KieriVandereycken2019], proof of
Theorem 6, eq. (38), with explicit constants). In the setting of `ProjectedRK.norm_stage_sub_le`,
let in addition `y₁` be a `κ`-quasi-optimal point of `ℳ` for `y + h ∑_j b_j e_j`, let
`zt = y + h ∑_j b_j FZt_j` be the classical result with `‖zt - wf‖ ≤ K h^{p+1}` (order `p`), and
let `ℳ` contain a point within `h g` of `wf`. If `q' ≤ p` and `q' ≤ min(q_j, q₂ + 1) + 1` for
every later stage `j` with `b_j ≠ 0`, then

  `‖y₁ - wf‖ ≤ h · localErrorConst a b L κ · (ε + g + K h^{q'})`.

With `wf` the exact solution at the end of the step this is the local error `O(h (ε + h^{q'}))`
behind Theorem 6; `ProjectedRK.admissible_min_q₂` and `ProjectedRK.admissible_of_b₂_eq_zero`
show that the exponent `q` of Theorem 6 is admissible. -/
theorem norm_sub_le_of_stages (ha : ∀ i j, i ≤ j → a i j = 0) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hg : 0 ≤ g) (hK : 0 ≤ K) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hy : y ∈ ℳ)
    (hZ : ∀ j, Z j = y + h • ∑ l, a j l • e l)
    (hη : ∀ j, ∀ z ∈ ℳ, ‖η j - Z j‖ ≤ κ * ‖z - Z j‖)
    (he : ∀ j, ‖e j - Fη j‖ ≤ ε) (hLip : ∀ j, ‖Fη j - FZt j‖ ≤ L * ‖η j - Zt j‖)
    (hZt : ∀ j, Zt j = y + h • ∑ l, a j l • FZt l) {q : Fin s → ℕ} {q₂ p q' : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j)
    (hw : ∀ j : Fin s, 0 < j.val → ‖Zt j - w j‖ ≤ K * h ^ (q j + 1))
    (hM : ∀ j : Fin s, 0 < j.val → ∃ z ∈ ℳ, ‖z - w j‖ ≤ h * g) {y₁ zt wf : E}
    (hy₁ : ∀ z ∈ ℳ, ‖y₁ - (y + h • ∑ j, b j • e j)‖ ≤ κ * ‖z - (y + h • ∑ j, b j • e j)‖)
    (hzt : zt = y + h • ∑ j, b j • FZt j) (hp : ‖zt - wf‖ ≤ K * h ^ (p + 1))
    (hMf : ∃ z ∈ ℳ, ‖z - wf‖ ≤ h * g) (hqp : q' ≤ p)
    (hqb : ∀ j : Fin s, 0 < j.val → b j ≠ 0 → q' ≤ min (q j) (q₂ + 1) + 1) :
    ‖y₁ - wf‖ ≤ h * (localErrorConst a b L κ * (ε + g + K * h ^ q')) := by
  set γ := stageGrowth a b L κ with hγdef
  set α := tabWeight a b with hαdef
  have hγ : 1 ≤ γ := one_le_stageGrowth a b hL hκ
  have hα : 0 ≤ α := tabWeight_nonneg a b
  set Y' := ε + g + K * h ^ q' with hY'
  have hY'0 : 0 ≤ Y' := add_nonneg (add_nonneg hε hg) (mul_nonneg hK (pow_nonneg hh _))
  have hst := norm_stage_sub_le (b := b) ha hκ hL hε hg hK hh hh1 hy hZ hη he hLip hZt hq hw hM
  -- every weighted stage derivative is `γ^s Y'`-accurate
  have hEb : ∀ j, b j ≠ 0 → ‖e j - FZt j‖ ≤ γ ^ s * Y' := by
    intro j hbj
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · refine ((hst j).1 h0).2.trans ?_
      have : Y' ≤ γ ^ s * Y' := le_mul_of_one_le_left hY'0 (one_le_pow₀ hγ)
      have := mul_nonneg hK (pow_nonneg hh q')
      linarith
    · refine ((hst j).2 hpos).2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : h ^ (min (q j) (q₂ + 1) + 1) ≤ h ^ q' := pow_le_pow_of_le_one hh hh1 (hqb j hpos hbj)
      have := mul_le_mul_of_nonneg_left this hK
      linarith
  set x := y + h • ∑ j, b j • e j with hx
  have hxzt : ‖x - zt‖ ≤ h * (α * (γ ^ s * Y')) := by
    have h₁ : x - zt = h • ∑ j, b j • (e j - FZt j) := by
      rw [hx, hzt]; simp only [smul_sub, Finset.sum_sub_distrib]; abel
    rw [h₁, norm_smul, Real.norm_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    calc ‖∑ j, b j • (e j - FZt j)‖ ≤ ∑ j, ‖b j • (e j - FZt j)‖ := norm_sum_le _ _
      _ = ∑ j, |b j| * ‖e j - FZt j‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ α * (γ ^ s * Y') := sum_abs_mul_le (by positivity) hEb (b_le_tabWeight a b)
  have hxw : ‖x - wf‖ ≤ h * ((α * γ ^ s + 1) * Y') := by
    have hp' : K * h ^ (p + 1) ≤ h * (K * h ^ q') := by
      rw [pow_succ, mul_comm (h ^ p) h, ← mul_assoc, mul_comm K h, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh hh1 hqp) hK) hh
    have : K * h ^ q' ≤ Y' := by rw [hY']; linarith
    calc ‖x - wf‖ ≤ ‖x - zt‖ + ‖zt - wf‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ h * (α * (γ ^ s * Y')) + h * (K * h ^ q') := add_le_add hxzt (hp.trans hp')
      _ ≤ h * (α * (γ ^ s * Y')) + h * Y' := by gcongr
      _ = h * ((α * γ ^ s + 1) * Y') := by ring
  obtain ⟨z, hz, hzw⟩ := hMf
  have hgY : g ≤ Y' := by rw [hY']; have := mul_nonneg hK (pow_nonneg hh q'); linarith
  calc ‖y₁ - wf‖ ≤ ‖y₁ - x‖ + ‖x - wf‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ κ * ‖z - x‖ + ‖x - wf‖ := add_le_add (hy₁ z hz) le_rfl
    _ ≤ κ * (h * g + ‖x - wf‖) + ‖x - wf‖ := by
        gcongr
        calc ‖z - x‖ ≤ ‖z - wf‖ + ‖wf - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖z - wf‖ + ‖x - wf‖ := by rw [norm_sub_rev wf]
          _ ≤ h * g + ‖x - wf‖ := by linarith
    _ = κ * (h * g) + (1 + κ) * ‖x - wf‖ := by ring
    _ ≤ κ * (h * Y') + (1 + κ) * (h * ((α * γ ^ s + 1) * Y')) := by gcongr
    _ ≤ h * ((1 + κ) * (α * γ ^ s + 2) * Y') := by
        have : κ * (h * Y') ≤ (1 + κ) * (h * Y') :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hh hY'0)
        nlinarith
    _ = h * (localErrorConst a b L κ * Y') := by rw [localErrorConst, ← hαdef, ← hγdef]

end Stages

/-! ### Admissible orders -/

section Orders

variable {s : ℕ}

/-- **The order of [KieriVandereycken2019], Theorem 6, for `b₂ ≠ 0`**: the exponent
`q' = min(p, q₂ + 1)` is admissible for `ProjectedRK.norm_sub_le_of_stages` whatever the weights
`b`, if `q₂ ≤ q_j` for the later stages. -/
theorem admissible_min_q₂ {b : Fin s → ℝ} {q : Fin s → ℕ} {q₂ p : ℕ}
    (hq : ∀ j : Fin s, 0 < j.val → q₂ ≤ q j) :
    ∀ j : Fin s, 0 < j.val → b j ≠ 0 → min p (q₂ + 1) ≤ min (q j) (q₂ + 1) + 1 := by
  intro j hj _
  have := hq j hj
  omega

/-- **The order of [KieriVandereycken2019], Theorem 6, for `b₂ = 0`**: if the stage with
`j.val = 1` (the paper's second stage) has weight `0` and the stages after it have stage order at
least `q₃`, the exponent `q' = min(p, q₃ + 1, q₂ + 2)` is admissible for
`ProjectedRK.norm_sub_le_of_stages`. -/
theorem admissible_of_b₂_eq_zero {b : Fin s → ℝ} {q : Fin s → ℕ} {q₂ q₃ p : ℕ}
    (hb : ∀ j : Fin s, j.val = 1 → b j = 0) (hq₃ : ∀ j : Fin s, 2 ≤ j.val → q₃ ≤ q j) :
    ∀ j : Fin s, 0 < j.val → b j ≠ 0 →
      min p (min (q₃ + 1) (q₂ + 2)) ≤ min (q j) (q₂ + 1) + 1 := by
  intro j hj hbj
  have h2 : 2 ≤ j.val := by
    by_contra h
    exact hbj (hb j (by omega))
  have := hq₃ j h2
  omega

end Orders

/-! ### Non-vacuity -/

section Examples

/-- **Non-vacuity of `ProjectedRK.exists_explicit_stages`**: stages that exceed all earlier
stages can be chosen one after the other. -/
example : ∃ Z : Fin 3 → ℕ, ∀ j l, l < j → Z l < Z j := by
  obtain ⟨Z, hZ⟩ := exists_explicit_stages (fun j Z x => ∀ l, l < j → Z l < x)
    (fun j Z Z' x h hx l hl => h l hl ▸ hx l hl)
    (fun j Z => ⟨∑ l, Z l + 1, fun l _ => Nat.lt_succ_of_le
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))⟩)
  exact ⟨Z, fun j l hl => hZ j l hl⟩

/-- **Non-vacuity of `ProjectedRK.norm_stage_sub_le` with a nonzero normal part.** Heun's
tableau (`a₂₁ = 1`, `b = (1/2, 1/2)`) on `ℝ` with `ℳ = ℝ`, the field `1` and projected stage
derivatives `2` (normal part `ε = 1`): the second stages differ by `1 ≤ α γ² h ε = 2`. -/
example : ‖(![0, 2] : Fin 2 → ℝ) 1 - (![0, 1] : Fin 2 → ℝ) 1‖ ≤
    tabWeight (s := 2) ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] *
      stageGrowth (s := 2) ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 0 0 ^ 2 * 1 *
        (1 + 0 + 0 * 1 ^ (1 + 1)) := by
  refine ((norm_stage_sub_le (E := ℝ) (s := 2) (a := ![![0, 0], ![1, 0]])
    (b := ![1 / 2, 1 / 2]) (ℳ := Set.univ) (κ := 0) (L := 0) (ε := 1) (g := 0) (K := 0)
    (h := 1) (y := 0) (Z := ![0, 2]) (η := ![0, 2]) (e := ![2, 2]) (Fη := ![1, 1])
    (Zt := ![0, 1]) (FZt := ![1, 1]) (w := ![0, 1]) (q := fun _ => 1) (q₂ := 1) ?_ le_rfl
    le_rfl zero_le_one le_rfl le_rfl zero_le_one le_rfl (Set.mem_univ _) ?_ ?_ ?_ ?_ ?_
    (fun _ _ => le_rfl) ?_ ?_ 1).2 (by simp)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
  · intro j z _; fin_cases j <;> simp
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> simp
  · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
  · intro j _; fin_cases j <;> simp
  · intro j _; exact ⟨![(0 : ℝ), 1] j, Set.mem_univ _, by simp⟩

/-- **Non-vacuity of `ProjectedRK.norm_sub_le_of_stages` with a nonzero normal part.** The data
of the previous example, the result `y₁ = 2` of the projected step, the classical result `1`
and the exact value `1` of `y' = 1`, `y(0) = 0` at `h = 1`: `‖y₁ - w_f‖ = 1` is at most
`h · localErrorConst · ε = 4`, with the exponent `q' = 2` of Heun's method. -/
example : ‖(2 : ℝ) - 1‖ ≤ 1 * (localErrorConst (s := 2) ![![0, 0], ![1, 0]] ![1 / 2, 1 / 2] 0 0 *
    (1 + 0 + 0 * 1 ^ 2)) := by
  refine norm_sub_le_of_stages (E := ℝ) (s := 2) (a := ![![0, 0], ![1, 0]])
    (b := ![1 / 2, 1 / 2]) (ℳ := Set.univ) (κ := 0) (L := 0) (ε := 1) (g := 0) (K := 0)
    (h := 1) (y := 0) (Z := ![0, 2]) (η := ![0, 2]) (e := ![2, 2]) (Fη := ![1, 1])
    (Zt := ![0, 1]) (FZt := ![1, 1]) (w := ![0, 1]) (q := fun _ => 1) (q₂ := 1) (p := 2)
    (zt := 1) ?_ le_rfl le_rfl zero_le_one le_rfl le_rfl zero_le_one le_rfl (Set.mem_univ _)
    ?_ ?_ ?_ ?_ ?_ (fun _ _ => le_rfl) ?_ ?_ ?_ ?_ (by simp) ⟨1, Set.mem_univ _, by simp⟩
    le_rfl ?_
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
  · intro j z _; fin_cases j <;> simp
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j <;> simp
  · intro j; fin_cases j <;> simp [Fin.sum_univ_two]
  · intro j _; fin_cases j <;> simp
  · intro j _; exact ⟨![(0 : ℝ), 1] j, Set.mem_univ _, by simp⟩
  · intro z _; simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · intro j hj _; fin_cases j <;> simp_all

end Examples

end LeanDLRA.ProjectedRK
