import LeanDLRA.Foundations.ODE

/-!
# Discrete Grönwall inequalities and Lady Windermere's fan

Every global error bound for a dynamical low-rank integrator is obtained from a *local* error bound
(the error committed in one step, measured against the exact flow started at the numerical value)
by the standard argument of **Lady Windermere's fan** (Hairer–Nørsett–Wanner, *Solving Ordinary
Differential Equations I*, Section II.3).  In the DLRA literature this step is invoked, e.g., in

* Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank approximation*,
  [CerutiLubich2022], proof of Theorem 7 (global error of the BUG integrator);
* Ceruti–Lubich, *Time integration of symmetric and anti-symmetric low-rank matrices and Tucker
  tensors*, [CerutiLubich2020], proof of Theorem 4;
* Kieri–Lubich–Walach (2016), global error of the projector-splitting integrator.

The argument has two ingredients, both formalised here:

1. **Stability of the exact flow** (`ODESolution.norm_sub_le_exp`): two solutions of
   `y' = F(t, y)` with `F` `L`-Lipschitz satisfy `‖y t - z t‖ ≤ exp (L (t - a)) ‖y a - z a‖`
   (the continuous Grönwall inequality with zero defect).
2. **Discrete Grönwall inequalities** (`discrete_gronwall_le`, `discrete_gronwall_const_le`,
   `discrete_gronwall_exp_sum_le`, `discrete_gronwall_exp_le`): a sequence with
   `e (n+1) ≤ a e n + b n` satisfies `e n ≤ aⁿ e 0 + ∑ₖ a^(n-1-k) b k`; for `a = exp (L h)`,
   `L, h ≥ 0`, `b k ≥ 0` this gives `e n ≤ exp (L n h) (e 0 + ∑_{k<n} b k)`.

Combining them yields Lady Windermere's fan (`lady_windermere`, `lady_windermere_sum`,
`lady_windermere_of_le`): with grid points `tₙ = t₀ + n h`, exact solution `A`, numerical values
`Y n`, and exact flows `Φ n` started at `(tₙ, Y n)`, local errors
`‖Y (n+1) - Φ n tₙ₊₁‖ ≤ ℓ` imply the global bound

    ‖Y n - A tₙ‖ ≤ exp (L n h) (‖Y 0 - A t₀‖ + n ℓ),

and for local errors `ℓ = h g` (consistency of order `g`) and `n h ≤ T`,
`‖Y n - A tₙ‖ ≤ exp (L T) (‖Y 0 - A t₀‖ + T g)`.

All statements hold in an arbitrary real normed space and with explicit constants; the finite
horizon versions (`∀ n ≤ N`) only assume the recursion for `n < N`.
-/

open Set Finset

namespace LeanDLRA

/-! ### Discrete Grönwall inequalities -/

section Discrete

/-- **Discrete Grönwall inequality** (finite horizon, variable inhomogeneity).
If `e (n+1) ≤ a * e n + b n` for `n < N` with `a ≥ 0`, then for `n ≤ N`
`e n ≤ aⁿ e 0 + ∑_{k<n} a^(n-1-k) b k`.  No sign condition on `e` or `b` is needed. -/
theorem discrete_gronwall_le {e b : ℕ → ℝ} {a : ℝ} {N : ℕ} (ha : 0 ≤ a)
    (he : ∀ n < N, e (n + 1) ≤ a * e n + b n) :
    ∀ n ≤ N, e n ≤ a ^ n * e 0 + ∑ k ∈ range n, a ^ (n - 1 - k) * b k := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := he n (by omega)
    have hsum : ∑ k ∈ range (n + 1), a ^ (n + 1 - 1 - k) * b k
        = a * ∑ k ∈ range n, a ^ (n - 1 - k) * b k + b n := by
      rw [sum_range_succ, mul_sum]
      congr 1
      · refine sum_congr rfl fun k hk => ?_
        have hk : k < n := mem_range.1 hk
        rw [show n + 1 - 1 - k = (n - 1 - k) + 1 by omega, pow_succ']
        ring
      · simp
    rw [hsum, pow_succ']
    calc e (n + 1) ≤ a * e n + b n := h2
      _ ≤ a * (a ^ n * e 0 + ∑ k ∈ range n, a ^ (n - 1 - k) * b k) + b n :=
        add_le_add_left (mul_le_mul_of_nonneg_left h1 ha) _
      _ = _ := by ring

/-- **Discrete Grönwall inequality** (variable inhomogeneity, all `n`). -/
theorem discrete_gronwall {e b : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (he : ∀ n, e (n + 1) ≤ a * e n + b n) (n : ℕ) :
    e n ≤ a ^ n * e 0 + ∑ k ∈ range n, a ^ (n - 1 - k) * b k :=
  discrete_gronwall_le (N := n) ha (fun k _ => he k) n le_rfl

/-- **Discrete Grönwall inequality** (finite horizon, constant inhomogeneity).
If `e (n+1) ≤ a * e n + b` for `n < N` with `a ≥ 0`, then for `n ≤ N`
`e n ≤ aⁿ e 0 + b ∑_{k<n} a^k`.  No sign condition on `e` or `b` is needed. -/
theorem discrete_gronwall_const_le {e : ℕ → ℝ} {a b : ℝ} {N : ℕ} (ha : 0 ≤ a)
    (he : ∀ n < N, e (n + 1) ≤ a * e n + b) :
    ∀ n ≤ N, e n ≤ a ^ n * e 0 + b * ∑ k ∈ range n, a ^ k := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := he n (by omega)
    rw [geom_sum_succ, pow_succ']
    calc e (n + 1) ≤ a * e n + b := h2
      _ ≤ a * (a ^ n * e 0 + b * ∑ k ∈ range n, a ^ k) + b :=
        add_le_add_left (mul_le_mul_of_nonneg_left h1 ha) _
      _ = _ := by ring

/-- **Discrete Grönwall inequality** (constant inhomogeneity, all `n`). -/
theorem discrete_gronwall_const {e : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (he : ∀ n, e (n + 1) ≤ a * e n + b) (n : ℕ) :
    e n ≤ a ^ n * e 0 + b * ∑ k ∈ range n, a ^ k :=
  discrete_gronwall_const_le (N := n) ha (fun k _ => he k) n le_rfl

/-- **Discrete Grönwall inequality, exponential form** (finite horizon, per-step inhomogeneity).
If `e (n+1) ≤ exp (L h) e n + b n` for `n < N`, with `L, h ≥ 0` and `b n ≥ 0`, then for `n ≤ N`
`e n ≤ exp (L n h) (e 0 + ∑_{k<n} b k)`.  No sign condition on `e` is needed. -/
theorem discrete_gronwall_exp_sum_le {e b : ℕ → ℝ} {L h : ℝ} {N : ℕ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hb : ∀ n < N, 0 ≤ b n) (he : ∀ n < N, e (n + 1) ≤ Real.exp (L * h) * e n + b n) :
    ∀ n ≤ N, e n ≤ Real.exp (L * (n * h)) * (e 0 + ∑ k ∈ range n, b k) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := he n (by omega)
    have hexp : Real.exp (L * h) * Real.exp (L * (n * h))
        = Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hone : 1 ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) :=
      Real.one_le_exp (mul_nonneg hL (mul_nonneg (Nat.cast_nonneg _) hh))
    rw [sum_range_succ]
    calc e (n + 1) ≤ Real.exp (L * h) * e n + b n := h2
      _ ≤ Real.exp (L * h) * (Real.exp (L * (n * h)) * (e 0 + ∑ k ∈ range n, b k)) + b n :=
        add_le_add_left (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) _
      _ ≤ Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * (e 0 + ∑ k ∈ range n, b k)
          + Real.exp (L * (((n + 1 : ℕ) : ℝ) * h)) * b n := by
        rw [← mul_assoc, hexp]
        exact add_le_add_right (le_mul_of_one_le_left (hb n (by omega)) hone) _
      _ = _ := by ring

/-- **Discrete Grönwall inequality, exponential form** (per-step inhomogeneity, all `n`). -/
theorem discrete_gronwall_exp_sum {e b : ℕ → ℝ} {L h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hb : ∀ n, 0 ≤ b n) (he : ∀ n, e (n + 1) ≤ Real.exp (L * h) * e n + b n) (n : ℕ) :
    e n ≤ Real.exp (L * (n * h)) * (e 0 + ∑ k ∈ range n, b k) :=
  discrete_gronwall_exp_sum_le (N := n) hL hh (fun k _ => hb k) (fun k _ => he k) n le_rfl

/-- **Discrete Grönwall inequality, exponential form** (finite horizon, constant inhomogeneity).
If `e (n+1) ≤ exp (L h) e n + b` for `n < N`, with `L, h, b ≥ 0`, then for `n ≤ N`
`e n ≤ exp (L n h) (e 0 + n b)`.  No sign condition on `e` is needed. -/
theorem discrete_gronwall_exp_le {e : ℕ → ℝ} {L h b : ℝ} {N : ℕ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hb : 0 ≤ b) (he : ∀ n < N, e (n + 1) ≤ Real.exp (L * h) * e n + b) :
    ∀ n ≤ N, e n ≤ Real.exp (L * (n * h)) * (e 0 + n * b) := by
  intro n hn
  have := discrete_gronwall_exp_sum_le (b := fun _ => b) hL hh (fun _ _ => hb) he n hn
  simpa [sum_const, card_range, nsmul_eq_mul] using this

/-- **Discrete Grönwall inequality, exponential form** (constant inhomogeneity, all `n`). -/
theorem discrete_gronwall_exp {e : ℕ → ℝ} {L h b : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (he : ∀ n, e (n + 1) ≤ Real.exp (L * h) * e n + b) (n : ℕ) :
    e n ≤ Real.exp (L * (n * h)) * (e 0 + n * b) :=
  discrete_gronwall_exp_le (N := n) hL hh hb (fun k _ => he k) n le_rfl

end Discrete

/-! ### Stability of the exact flow and Lady Windermere's fan -/

section Fan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Stability of the exact flow.**  Two solutions `y`, `z` of `y' = F(t, y)` on `[a, b]` with
`F` `L`-Lipschitz (`L ≥ 0`) satisfy `‖y t - z t‖ ≤ exp (L (t - a)) ‖y a - z a‖` on `[a, b]`.
(Continuous Grönwall inequality with zero defect.) -/
theorem ODESolution.norm_sub_le_exp {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {y z : ℝ → E} {a b : ℝ} (hy : ODESolution F y a b)
    (hz : ODESolution F z a b) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (L * (t - a)) * ‖y a - z a‖ := by
  intro t ht
  have := norm_sub_le_gronwallBound hF hL (u := fun t => F t (y t)) (w := fun t => F t (z t))
    (ηy := 0) (ηz := 0) hy.cont hy.deriv (fun _ _ => by simp) hz.cont hz.deriv
    (fun _ _ => by simp) le_rfl t ht
  rw [add_zero, gronwallBound_ε0] at this
  rw [mul_comm]
  exact this

/-- One step of Lady Windermere's fan: the error at `tₙ₊₁` is bounded by the local error plus
the error at `tₙ` propagated by the exact flow over one step. -/
theorem lady_windermere_step {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {n : ℕ} (hn : n < N) :
    ‖Y (n + 1) - A (t₀ + ((n + 1 : ℕ) : ℝ) * h)‖ ≤
      Real.exp (L * h) * ‖Y n - A (t₀ + n * h)‖ + ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ := by
  have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have hNh : ((n : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hn' hh
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hAn : ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) :=
    hA.mono (by linarith) (by linarith)
  have hstab := (hΦ n hn).norm_sub_le_exp hF hL hAn (t₀ + (n + 1) * h)
    ⟨by linarith, le_rfl⟩
  rw [hΦ₀ n hn, show t₀ + (n + 1) * h - (t₀ + n * h) = h by ring] at hstab
  have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  rw [hcast]
  calc ‖Y (n + 1) - A (t₀ + (n + 1) * h)‖
      ≤ ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖
        + ‖Φ n (t₀ + (n + 1) * h) - A (t₀ + (n + 1) * h)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ + Real.exp (L * h) * ‖Y n - A (t₀ + n * h)‖ :=
        add_le_add_right hstab _
    _ = _ := by ring

/-- **Lady Windermere's fan** with per-step local errors.  Let `F` be `L`-Lipschitz, `L ≥ 0`,
`tₙ = t₀ + n h` with `h ≥ 0`, let `A` solve `A' = F(t, A)` on `[t₀, t₀ + N h]`, and for `n < N`
let `Φ n` solve the same ODE on `[tₙ, tₙ₊₁]` with `Φ n tₙ = Y n`.  If the local errors satisfy
`‖Y (n+1) - Φ n tₙ₊₁‖ ≤ ℓ n`, then for `n ≤ N`
`‖Y n - A tₙ‖ ≤ exp (L n h) (‖Y 0 - A t₀‖ + ∑_{k<n} ℓ k)`.
(Hairer–Nørsett–Wanner, Section II.3; used in [CerutiLubich2022], proof of Theorem 7.) -/
theorem lady_windermere_sum {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {ℓ : ℕ → ℝ} (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ ℓ n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, ℓ k) := by
  have key := discrete_gronwall_exp_sum_le (e := fun n => ‖Y n - A (t₀ + n * h)‖) (b := ℓ)
    hL hh (fun n hn => (norm_nonneg _).trans (hloc n hn)) (fun n hn =>
      (lady_windermere_step hF hL hh hA hΦ hΦ₀ hn).trans
        (add_le_add_right (hloc n hn) _))
  intro n hn
  simpa using key n hn

/-- **Lady Windermere's fan** (local → global error).  Let `F` be `L`-Lipschitz, `L ≥ 0`,
`tₙ = t₀ + n h` with `h ≥ 0`, let `A` solve `A' = F(t, A)` on `[t₀, t₀ + N h]`, and for `n < N`
let `Φ n` solve the same ODE on `[tₙ, tₙ₊₁]` with `Φ n tₙ = Y n`.  If the local errors satisfy
`‖Y (n+1) - Φ n tₙ₊₁‖ ≤ ℓ`, then for `n ≤ N`
`‖Y n - A tₙ‖ ≤ exp (L n h) (‖Y 0 - A t₀‖ + n ℓ)`.
(Hairer–Nørsett–Wanner, Section II.3; used in [CerutiLubich2022], proof of Theorem 7, and
[CerutiLubich2020], proof of Theorem 4.) -/
theorem lady_windermere {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {ℓ : ℝ} (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ ℓ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * ℓ) := by
  intro n hn
  have := lady_windermere_sum hF hL hh hA hΦ hΦ₀ (ℓ := fun _ => ℓ) hloc n hn
  simpa [sum_const, card_range, nsmul_eq_mul] using this

/-- **Lady Windermere's fan, consistency form.**  Under the hypotheses of `lady_windermere`, if the
local errors are `O(h g)`, i.e. `‖Y (n+1) - Φ n tₙ₊₁‖ ≤ h g` with `g ≥ 0`, then for `n ≤ N` with
`n h ≤ T`: `‖Y n - A tₙ‖ ≤ exp (L T) (‖Y 0 - A t₀‖ + T g)`.  (For a method of order `p`,
`g = C h^p`.) -/
theorem lady_windermere_of_le {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n)
    {g : ℝ} (hg : 0 ≤ g) (hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * g)
    {T : ℝ} :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * g) := by
  intro n hn hT
  have h1 := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
  have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hsum : ‖Y 0 - A t₀‖ + n * (h * g) ≤ ‖Y 0 - A t₀‖ + T * g := by
    rw [← mul_assoc]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hT hg) _
  have hsum0 : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * g) := by
    rw [← mul_assoc]; exact add_nonneg (norm_nonneg _) (mul_nonneg hnh hg)
  exact h1.trans (mul_le_mul hexp hsum hsum0 (Real.exp_pos _).le)

/-- The hypotheses of `lady_windermere` are jointly satisfiable with nonzero local errors:
for the zero vector field on `ℝ`, the exact solution `A = 0`, numerical values `Y n = n` and
constant local flows `Φ n = n`, every local error equals `1`, and the resulting bound
`‖Y n‖ ≤ n` is sharp. -/
example : ∀ n ≤ 5, ‖((n : ℕ) : ℝ) - 0‖ ≤
    Real.exp (0 * (n * 1)) * (‖((0 : ℕ) : ℝ) - 0‖ + n * 1) :=
  lady_windermere (E := ℝ) (F := fun _ _ => 0) (L := 0) (fun _ _ _ => by simp) le_rfl
    (t₀ := 0) (h := 1) zero_le_one (N := 5) (A := fun _ => 0)
    ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩
    (Y := fun n => (n : ℝ)) (Φ := fun n _ => (n : ℝ))
    (fun _ _ => ⟨continuousOn_const, fun _ _ => hasDerivWithinAt_const _ _ _⟩)
    (fun _ _ => rfl) (ℓ := 1) (fun n _ => by simp)

end Fan

end LeanDLRA
