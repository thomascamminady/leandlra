import LeanDLRA.Foundations.OneSided

/-!
# Results of arXiv 2203.08455: Low-rank Parareal

Formalization of the analysis of low-rank Parareal (Carrel, Gander, Vandereycken).
Part 1 is the double-recursion analysis `E_{n+1}^{k+1} ≤ α E_n^k + β E_n^{k+1} + κ`
(Thm 3.3 linear bound, Thm 3.5 superlinear bound, Thm 3.6 second linear bound), proved
directly by comparison with explicit supersolutions rather than through the closed form of
Lemma 3.4.  Part 2 is Lemma 3.2 (the one-step error recursion for affine `F`) on an abstract real
inner product space `E`: the DLRA flows are abstracted by vector fields that are `ε`-close to `F`,
the truncations by Lipschitz maps.  Thm 3.8 (SVD perturbation) and Lemma 4.1 (Zolotarev decay)
are not covered.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2203_08455

section Recursion

variable {e : ℕ → ℕ → ℝ} {α β κ γ : ℝ}

/-- Fixed point `c = κ/(1-α-β)` of the comparison recursion. -/
private lemma fixed_pt (h : α + β < 1) :
    κ / (1 - α - β) = (α + β) * (κ / (1 - α - β)) + κ := by
  have : (1 - α - β) ≠ 0 := by intro h0; linarith
  field_simp; ring

/-- **Thm 3.3 (linear convergence), pointwise form** (arXiv 2203.08455, Thm 3.3).
Errors `e k n = E_n^k` with `E_0^k = 0` satisfying `e^{k+1}_{n+1} ≤ α e^k_n + β e^{k+1}_n + κ`,
`α,β,κ ≥ 0`, `α+β<1`, and `e^0_n ≤ M`.  Then `e^k_n ≤ (α/(1-β))^k M + κ/(1-α-β)`.
Taking `M = max_n E_n^0` gives the statement of the paper (`thm_3_3` below). No sign condition on
`e` is needed. -/
theorem thm_3_3_le (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hαβ : α + β < 1)
    (h0 : ∀ k, e k 0 = 0)
    (hrec : ∀ k n, e (k + 1) (n + 1) ≤ α * e k n + β * e (k + 1) n + κ)
    {M : ℝ} (hM : ∀ n, e 0 n ≤ M) (k n : ℕ) :
    e k n ≤ (α / (1 - β)) ^ k * M + κ / (1 - α - β) := by
  have hβ1 : 0 < 1 - β := by linarith
  have hc : 0 ≤ κ / (1 - α - β) := div_nonneg hκ (by linarith)
  have hcfix := fixed_pt (κ := κ) hαβ
  generalize hcdef : κ / (1 - α - β) = c at hc hcfix ⊢
  generalize hr : α / (1 - β) = r
  have hr0 : 0 ≤ r := hr ▸ div_nonneg hα hβ1.le
  have hr1 : r < 1 := by rw [← hr, div_lt_one hβ1]; linarith
  have hM0 : 0 ≤ M := (h0 0 ▸ hM 0)
  -- D k = r^k (M - c) + c satisfies (1-β) D(k+1) = α D k + κ
  let D : ℕ → ℝ := fun k => r ^ k * (M - c) + c
  have hDpos : ∀ k, 0 ≤ D k := by
    intro k
    have : r ^ k ≤ 1 := pow_le_one₀ hr0 hr1.le
    have h2 : 0 ≤ r ^ k := pow_nonneg hr0 k
    simp only [D]; nlinarith
  have hDrec : ∀ k, α * D k + κ ≤ (1 - β) * D (k + 1) := by
    intro k
    have h1 : α = r * (1 - β) := by rw [← hr]; field_simp
    have h2 : c * (1 - β) = α * c + κ := by nlinarith
    simp only [D]; rw [pow_succ]
    exact le_of_eq (by linear_combination (r ^ k * (M - c)) * h1 - h2)
  have key : ∀ k n, e k n ≤ D k := by
    intro k
    induction k with
    | zero => intro n; simpa [D] using hM n
    | succ k ih =>
      intro n
      induction n with
      | zero => rw [h0]; exact hDpos _
      | succ n ihn =>
        have := hrec k n
        have h3 := ih n
        nlinarith [hDrec k]
  have := key k n
  have h2 : r ^ k * (M - c) + c ≤ r ^ k * M + c := by
    have : 0 ≤ r ^ k * c := mul_nonneg (pow_nonneg hr0 k) hc
    nlinarith
  exact this.trans h2

/-- **Thm 3.3 (linear convergence)** (arXiv 2203.08455, Thm 3.3), in the paper's form with maxima:
if `α+β<1`, `E_0^k = 0` and `E^{k+1}_{n+1} ≤ α E^k_n + β E^{k+1}_n + κ` (eq. (15), the conclusion
of Lemma 3.2 with the constants (16)), then
`max_n E_n^k ≤ (α/(1-β))^k max_n E_n^0 + κ/(1-α-β)`.
Difference: the abstract sequence `e k n` replaces the norms `‖E_n^k‖`; the maxima are `iSup`s over
all `n : ℕ`, and boundedness of `n ↦ E_n^0` is assumed (it is a maximum in the paper).
The hypothesis `E_0^k = 0` is not in the printed theorem; the paper uses it implicitly: it is the
condition `e_0^k = 0` of (18) in Lemma 3.4, and the proof of (17) takes the maximum of (15) over
`n`, which bounds only `E_{n+1}^{k+1}`. -/
theorem thm_3_3 (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hαβ : α + β < 1)
    (h0 : ∀ k, e k 0 = 0)
    (hrec : ∀ k n, e (k + 1) (n + 1) ≤ α * e k n + β * e (k + 1) n + κ)
    (hbdd : BddAbove (Set.range (e 0))) (k : ℕ) :
    BddAbove (Set.range (e k)) ∧
    ⨆ n, e k n ≤ (α / (1 - β)) ^ k * (⨆ n, e 0 n) + κ / (1 - α - β) := by
  have hb : ∀ n, e k n ≤ (α / (1 - β)) ^ k * (⨆ n, e 0 n) + κ / (1 - α - β) :=
    fun n => thm_3_3_le hα hβ hκ hαβ h0 hrec (fun n => le_ciSup hbdd n) k n
  exact ⟨⟨_, by rintro _ ⟨n, rfl⟩; exact hb n⟩, ciSup_le hb⟩

/-- **Thm 3.6 (second linear bound)** (arXiv 2203.08455, Thm 3.6): with `e^0_n ≤ γ`,
`e^k_n ≤ α^k (1+β)^{n-1} γ + κ/(1-α-β)` for all `k` and `n ≥ 1`.  The paper takes `γ = max E_n^0`
and states all `n ∈ ℕ`; `n = 0` (where `(1+β)^{-1}` appears) is excluded here and is trivial since
`E_0^k = 0`. As in `thm_3_3`, `E_0^k = 0` is the paper's implicit condition from (18).
-/
theorem thm_3_6 (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hαβ : α + β < 1)
    (h0 : ∀ k, e k 0 = 0)
    (hrec : ∀ k n, e (k + 1) (n + 1) ≤ α * e k n + β * e (k + 1) n + κ)
    (hγ : ∀ n, e 0 n ≤ γ) (k n : ℕ) (hn : 1 ≤ n) :
    e k n ≤ α ^ k * (1 + β) ^ (n - 1) * γ + κ / (1 - α - β) := by
  have hc : 0 ≤ κ / (1 - α - β) := div_nonneg hκ (by linarith)
  have hcfix := fixed_pt (κ := κ) hαβ
  set c := κ / (1 - α - β)
  have hγ0 : 0 ≤ γ := (h0 0 ▸ hγ 0)
  have key : ∀ n k, e k (n + 1) ≤ α ^ k * (1 + β) ^ n * γ + c := by
    intro n
    induction n with
    | zero =>
      intro k
      cases k with
      | zero => simpa using (hγ 1).trans (by linarith)
      | succ k =>
        have := hrec k 0
        rw [h0, h0] at this
        have : 0 ≤ α ^ (k + 1) * γ := mul_nonneg (pow_nonneg hα _) hγ0
        nlinarith
    | succ n ih =>
      intro k
      cases k with
      | zero =>
        have : γ ≤ (1 + β) ^ (n + 1) * γ := by
          have : 1 ≤ (1 + β) ^ (n + 1) := one_le_pow₀ (by linarith)
          nlinarith
        simpa using (hγ (n + 2)).trans (by linarith)
      | succ k =>
        have h1 := hrec k (n + 1)
        have h2 := ih k
        have h3 := ih (k + 1)
        have hp : 0 ≤ α ^ k * (1 + β) ^ n * γ :=
          mul_nonneg (mul_nonneg (pow_nonneg hα _) (pow_nonneg (by linarith) _)) hγ0
        calc e (k + 1) (n + 1 + 1) ≤ _ := h1
          _ ≤ α * (α ^ k * (1 + β) ^ n * γ + c)
              + β * (α ^ (k + 1) * (1 + β) ^ n * γ + c) + κ := by
            gcongr
          _ = α ^ (k + 1) * (1 + β) ^ (n + 1) * γ + c := by
            rw [pow_succ α k, pow_succ (1 + β) n]; nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using key m k

/-- The truncated product `∏_{j=2}^k (n-j)` of Thm 3.5 (natural subtraction). -/
private noncomputable def prodTr (k n : ℕ) : ℝ := ∏ j ∈ Icc 2 k, ((n - j : ℕ) : ℝ)

private lemma prodTr_succ (k n : ℕ) (hk : 1 ≤ k) :
    prodTr (k + 1) n = prodTr k n * ((n - (k + 1) : ℕ) : ℝ) := by
  unfold prodTr
  rw [Finset.prod_Icc_succ_top (by omega)]

private lemma prodTr_succ_succ (k n : ℕ) (hk : 1 ≤ k) :
    prodTr (k + 1) (n + 1) = ((n - 1 : ℕ) : ℝ) * prodTr k n := by
  induction k, hk using Nat.le_induction with
  | base => simp [prodTr]
  | succ k hk ih =>
    rw [prodTr_succ (k + 1) (n + 1) (by omega), ih, prodTr_succ k n hk]
    have : n + 1 - (k + 1 + 1) = n - (k + 1) := by omega
    rw [this]; ring

private lemma prodTr_nonneg (k n : ℕ) : 0 ≤ prodTr k n :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- **Thm 3.5 (superlinear convergence)** (arXiv 2203.08455, Thm 3.5): for `k ≥ 1` and all `n`,
`e^k_n ≤ α^k / (k-1)! · ∏_{j=2}^k (n-j) / (1-β) · γ + κ/(1-α-β)` where `e^0_n ≤ γ`
(the paper takes `γ = max E_n^0`).
Difference from the paper: the factors `n - j` are truncated subtractions in `ℕ` (so the product is
`0` for `n ≤ k`).  The printed (21) says "for all `n, k ∈ ℕ`" with signed factors, but its proof
treats only `n ≥ k + 1` (for `n ≤ k` the `γ`-term of (19) vanishes).  For `n ≤ 1 < k` with `k` even
the signed product is negative, and the signed reading does not follow from (15) alone: the
`example` after this theorem gives a sequence satisfying (15) for which it fails at `n = 1, k = 2`.
The case `k = 0` is excluded (`(k-1)!` is undefined). `E_0^k = 0` is as in `thm_3_3`. -/
theorem thm_3_5 (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hαβ : α + β < 1)
    (h0 : ∀ k, e k 0 = 0)
    (hrec : ∀ k n, e (k + 1) (n + 1) ≤ α * e k n + β * e (k + 1) n + κ)
    (hγ : ∀ n, e 0 n ≤ γ) (k n : ℕ) (hk : 1 ≤ k) :
    e k n ≤ α ^ k * (∏ j ∈ Icc 2 k, ((n - j : ℕ) : ℝ)) / ((k - 1).factorial : ℝ)
      * (γ / (1 - β)) + κ / (1 - α - β) := by
  have hβ1 : 0 < 1 - β := by linarith
  have hc : 0 ≤ κ / (1 - α - β) := div_nonneg hκ (by linarith)
  have hcfix := fixed_pt (κ := κ) hαβ
  generalize κ / (1 - α - β) = c at hc hcfix ⊢
  have hγ0 : 0 ≤ γ := (h0 0 ▸ hγ 0)
  have hg0 : 0 ≤ γ / (1 - β) := div_nonneg hγ0 hβ1.le
  -- U k n
  let U : ℕ → ℕ → ℝ := fun k n => α ^ k * prodTr k n / ((k - 1).factorial : ℝ) * (γ / (1 - β))
  have hU0 : ∀ k n, 0 ≤ U k n := fun k n =>
    mul_nonneg
      (div_nonneg (mul_nonneg (pow_nonneg hα _) (prodTr_nonneg _ _)) (Nat.cast_nonneg _)) hg0
  -- A: for n ≤ k the error is below c
  have hA : ∀ n k, n ≤ k → e k n ≤ c := by
    intro n
    induction n with
    | zero => intro k _; rw [h0]; exact hc
    | succ n ih =>
      intro k hnk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h1 := hrec k n
      have h2 := ih k (by omega)
      have h3 := ih (k + 1) (by omega)
      nlinarith
  -- base k = 1
  have hbase' : ∀ n, e 1 n ≤ α * (γ / (1 - β)) + c := by
    intro n
    induction n with
    | zero => rw [h0]; have := mul_nonneg hα hg0; linarith
    | succ n ih =>
      have h1 := hrec 0 n
      have h2 := hγ n
      have h3 : α * e 0 n ≤ α * γ := mul_le_mul_of_nonneg_left h2 hα
      have h4 : α * γ + β * (α * (γ / (1 - β))) = α * (γ / (1 - β)) := by
        field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left ih hβ]
  have hbase : ∀ n, e 1 n ≤ U 1 n + c := fun n => by
    have hU1 : U 1 n = α * (γ / (1 - β)) := by simp [U, prodTr]
    rw [hU1]; exact hbase' n
  have hmain : ∀ k, 1 ≤ k → ∀ n, e k n ≤ U k n + c := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      intro n
      induction n with
      | zero => rw [h0]; linarith [hU0 (k + 1) 0]
      | succ n ihn =>
        by_cases hnk : n + 1 ≤ k + 1
        · linarith [hA (n + 1) (k + 1) hnk, hU0 (k + 1) (n + 1)]
        · have hn : k + 1 ≤ n := by omega
          have h1 := hrec k n
          have h2 := ih n
          have hsup : α * U k n + β * U (k + 1) n ≤ U (k + 1) (n + 1) := by
            obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
            have e1 := prodTr_succ (m + 1) n hk
            have e2 := prodTr_succ_succ (m + 1) n hk
            have hnm : ((n - (m + 1 + 1) : ℕ) : ℝ) = (n : ℝ) - (m + 2) := by
              rw [Nat.cast_sub (by omega)]; push_cast; ring
            have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega)]; simp
            rw [hnm] at e1; rw [hn1] at e2
            simp only [U, Nat.add_sub_cancel]
            rw [e1, e2]
            have hfac : (((m + 1).factorial : ℕ) : ℝ) = (m + 1) * (m.factorial : ℝ) := by
              rw [Nat.factorial_succ]; push_cast; ring
            rw [hfac]
            have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
            have hP := prodTr_nonneg (m + 1) n
            have hnm0 : (0 : ℝ) ≤ (n : ℝ) - (m + 2) := by
              have : ((m + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : m + 2 ≤ n)
              push_cast at this; linarith
            have hQ : 0 ≤ α ^ (m + 1 + 1) * prodTr (m + 1) n * (γ / (1 - β))
                / (((m : ℝ) + 1) * m.factorial) :=
              div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hα _) hP) hg0)
                (mul_nonneg (by positivity) hf.le)
            have key : α * (α ^ (m + 1) * prodTr (m + 1) n / m.factorial * (γ / (1 - β)))
                + β * (α ^ (m + 1 + 1) * (prodTr (m + 1) n * ((n : ℝ) - (m + 2)))
                    / (((m : ℝ) + 1) * m.factorial) * (γ / (1 - β)))
                = (((m : ℝ) + 1) + β * ((n : ℝ) - (m + 2))) *
                  (α ^ (m + 1 + 1) * prodTr (m + 1) n * (γ / (1 - β))
                    / (((m : ℝ) + 1) * m.factorial)) := by
              field_simp; ring
            have key3 : α ^ (m + 1 + 1) * (((n : ℝ) - 1) * prodTr (m + 1) n)
                / (((m : ℝ) + 1) * m.factorial) * (γ / (1 - β))
                = ((n : ℝ) - 1) * (α ^ (m + 1 + 1) * prodTr (m + 1) n * (γ / (1 - β))
                    / (((m : ℝ) + 1) * m.factorial)) := by ring
            rw [key, key3]
            refine mul_le_mul_of_nonneg_right ?_ hQ
            nlinarith
          nlinarith [hsup]
  have := hmain k hk n
  simpa [U, prodTr] using this

/-- The signed reading of (21) does not follow from (15) alone. With `α = 1/2`, `β = 0`, `κ = 1`,
`γ = 100`, the sequence `e k 0 = 0`, `e 0 n = 100`, `e k n = 1` (`k, n ≥ 1`) satisfies (15) and
`E_n^0 ≤ γ`, but at `n = 1`, `k = 2` the signed right side of (21) is
`(1/2)^2 · (1 - 2) / 1! · 100 + 2 = -23 < 1 = e 2 1`. -/
example : ∃ e : ℕ → ℕ → ℝ, (∀ k, e k 0 = 0) ∧
    (∀ k n, e (k + 1) (n + 1) ≤ (1 / 2) * e k n + 0 * e (k + 1) n + 1) ∧ (∀ n, e 0 n ≤ 100) ∧
    (1 / 2 : ℝ) ^ 2 * (∏ j ∈ Icc (2 : ℕ) 2, ((1 : ℝ) - j)) / ((2 - 1).factorial : ℝ)
      * (100 / (1 - 0)) + 1 / (1 - 1 / 2 - 0) < e 2 1 := by
  refine ⟨fun k n => if n = 0 then 0 else if k = 0 then 100 else 1, fun k => by simp,
    fun k n => ?_, fun n => ?_, ?_⟩
  · by_cases hn : n = 0 <;> by_cases hk : k = 0 <;> simp [hn, hk]
  · by_cases hn : n = 0 <;> simp [hn]
  · norm_num

end Recursion

section ErrorIteration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `gronwallBound δ ℓ η h = e^{ℓh} δ + η ∫_0^h e^{ℓ(h-s)} ds`. -/
lemma gronwallBound_eq_integral (δ ℓ η h : ℝ) :
    gronwallBound δ ℓ η h =
      Real.exp (ℓ * h) * δ + η * ∫ s in (0 : ℝ)..h, Real.exp (ℓ * (h - s)) := by
  have hint : ∫ s in (0 : ℝ)..h, Real.exp (ℓ * (h - s)) = ∫ s in (0 : ℝ)..h, Real.exp (ℓ * s) := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := h)
      (fun x => Real.exp (ℓ * x)) h
    simpa using this
  rw [hint]
  by_cases hℓ : ℓ = 0
  · subst hℓ; simp [gronwallBound]
  · have h2 : ∫ s in (0 : ℝ)..h, Real.exp (ℓ * s) = ℓ⁻¹ * (Real.exp (ℓ * h) - 1) := by
      rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hℓ, integral_exp]
      simp
    rw [h2, gronwallBound_of_K_ne_0 hℓ]
    field_simp

/-- **Lemma 3.2 (error iteration for affine `F`)** (arXiv 2203.08455, Lemma 3.2, eq. (11)).
Abstract core on a real inner product space `E` (in the paper `E = ℝ^{m×m}` with the Frobenius
norm).
Let `F x = A x + B` be affine with one-sided Lipschitz constant `ℓ` (`⟪A x, x⟫ ≤ ℓ‖x‖²`, which is
the
paper's `⟪X-Y, F X - F Y⟫ ≤ ℓ‖X-Y‖²` for affine `F`).  `X` is the exact flow of `F` from `Xn`
(so `X h = X_{n+1}`); `Z`, `W`, `V` are the DLRA flows of ranks `r`, `q`, `q`, abstracted as
solutions
of autonomous fields `Gr`, `Gq`, `Gq` that are `ε_r`- resp. `ε_q`-close to `F` everywhere (the
paper's "maps almost to the tangent bundle": `G_r Y = P_Y F(Y)`, `‖F Y - G_r Y‖ ≤ ε_r`), started at
`Z 0 = Tr Y_n^k`, `W 0 = Tq Y_n^{k+1}`, `V 0 = Tq Y_n^k`. The truncations `Tr`, `Tq` are abstracted
to maps with `Tr - Tq` `C_{r,q}`-Lipschitz and `Tq` `C_q`-Lipschitz. Then for
`Y_{n+1}^{k+1} = Z h + W h - V h` (eq. (9)),
`‖X_{n+1} - Y_{n+1}^{k+1}‖ ≤ e^{ℓh}(C_{r,q}‖E_n^k‖ + C_q‖E_n^{k+1}‖ + ‖X_n - T_r X_n‖)
  + (2ε_q + ε_r) ∫_0^h e^{ℓ(h-s)} ds`, with `E_n^k = X_n - Y_n^k`.
Differences from the paper: the term `max_{n≥0}‖X_n - T_r X_n‖` is replaced by the sharper
`‖X_n - T_r X_n‖` (the paper's follows by monotonicity); no Lipschitz bound on `F` is needed. -/
theorem lemma_3_2 (A : E →L[ℝ] E) (B : E) {ℓ : ℝ} (hA : ∀ x, ⟪A x, x⟫ ≤ ℓ * ‖x‖ ^ 2)
    (Gr Gq : E → E) {εr εq : ℝ}
    (hGr : ∀ y, ‖(A y + B) - Gr y‖ ≤ εr) (hGq : ∀ y, ‖(A y + B) - Gq y‖ ≤ εq)
    (Tr Tq : E → E) {Crq Cq : NNReal}
    (hTrq : LipschitzWith Crq (fun x => Tr x - Tq x)) (hTq : LipschitzWith Cq Tq)
    {h : ℝ} (hh : 0 ≤ h) {X Z W V : ℝ → E}
    (hX : ODESolution (fun _ x => A x + B) X 0 h) (hZ : ODESolution (fun _ => Gr) Z 0 h)
    (hW : ODESolution (fun _ => Gq) W 0 h) (hV : ODESolution (fun _ => Gq) V 0 h)
    {Xn Yk Yk1 : E} (hX0 : X 0 = Xn) (hZ0 : Z 0 = Tr Yk) (hW0 : W 0 = Tq Yk1)
    (hV0 : V 0 = Tq Yk) :
    ‖X h - (Z h + W h - V h)‖ ≤
      Real.exp (ℓ * h) * (Crq * ‖Xn - Yk‖ + Cq * ‖Xn - Yk1‖ + ‖Xn - Tr Xn‖)
        + (2 * εq + εr) * ∫ s in (0 : ℝ)..h, Real.exp (ℓ * (h - s)) := by
  set Ec : ℝ → E := fun t => X t - Z t - W t + V t with hEc
  set d : ℝ → E := fun t => (A (X t) + B) - Gr (Z t) - Gq (W t) + Gq (V t) with hd
  have hEcd : ∀ t ∈ Ico (0 : ℝ) h, HasDerivWithinAt Ec (d t) (Ici t) t := fun t ht =>
    (((hX.deriv t ht).sub (hZ.deriv t ht)).sub (hW.deriv t ht)).add (hV.deriv t ht)
  have hdef : ∀ t ∈ Ico (0 : ℝ) h, ‖d t - (fun _ x => A x) t (Ec t)‖ ≤ εr + 2 * εq := by
    intro t _
    have heq : d t - A (Ec t) = ((A (Z t) + B) - Gr (Z t)) + ((A (W t) + B) - Gq (W t))
        - ((A (V t) + B) - Gq (V t)) := by
      simp only [hd, hEc, map_add, map_sub]; abel
    change ‖d t - A (Ec t)‖ ≤ _
    rw [heq]
    calc _ ≤ ‖((A (Z t) + B) - Gr (Z t)) + ((A (W t) + B) - Gq (W t))‖
            + ‖(A (V t) + B) - Gq (V t)‖ := norm_sub_le _ _
      _ ≤ (‖(A (Z t) + B) - Gr (Z t)‖ + ‖(A (W t) + B) - Gq (W t)‖)
            + ‖(A (V t) + B) - Gq (V t)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (εr + εq) + εq := by
          gcongr
          · exact hGr _
          · exact hGq _
          · exact hGq _
      _ = _ := by ring
  have hcont : ContinuousOn Ec (Icc 0 h) :=
    ((hX.cont.sub hZ.cont).sub hW.cont).add hV.cont
  have hmain := norm_sub_le_gronwallBound_of_inner_le (F := fun _ x => A x) (ℓ := ℓ)
    (y := Ec) (z := fun _ => (0 : E)) (u := d) (w := fun _ => (0 : E)) (a := 0) (b := h)
    (ηy := εr + 2 * εq) (ηz := 0) (δ := ‖Ec 0‖)
    (fun t _ => by simpa using hA (Ec t)) hcont hEcd hdef continuousOn_const
    (fun t _ => hasDerivWithinAt_const t _ (0 : E)) (fun t _ => by simp) (by simp) h
    ⟨hh, le_rfl⟩
  have hEh : Ec h - 0 = X h - (Z h + W h - V h) := by simp only [hEc]; abel
  rw [hEh, gronwallBound_eq_integral] at hmain
  have hE0 : ‖Ec 0‖ ≤ Crq * ‖Xn - Yk‖ + Cq * ‖Xn - Yk1‖ + ‖Xn - Tr Xn‖ := by
    have hsplit : Ec 0 = (Xn - Tr Xn) + (((Tr Xn - Tq Xn) - (Tr Yk - Tq Yk)))
        + (Tq Xn - Tq Yk1) := by
      simp only [hEc, hX0, hZ0, hW0, hV0]; abel
    rw [hsplit]
    have h1 := hTrq.dist_le_mul Xn Yk
    have h2 := hTq.dist_le_mul Xn Yk1
    simp only [dist_eq_norm] at h1 h2
    calc _ ≤ ‖(Xn - Tr Xn) + ((Tr Xn - Tq Xn) - (Tr Yk - Tq Yk))‖ + ‖Tq Xn - Tq Yk1‖ :=
          norm_add_le _ _
      _ ≤ (‖Xn - Tr Xn‖ + ‖(Tr Xn - Tq Xn) - (Tr Yk - Tq Yk)‖) + ‖Tq Xn - Tq Yk1‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith
  have hexp := Real.exp_pos (ℓ * h)
  have := mul_le_mul_of_nonneg_left hE0 hexp.le
  simp only [sub_zero, add_zero] at hmain
  nlinarith

/-- Non-vacuity of the hypotheses of `lemma_3_2`: `E = ℝ`, `F = 0`, all flows constant,
`Tr = Tq = id` (so `Tr - Tq = 0` is `0`-Lipschitz and `Tq` is `1`-Lipschitz). -/
example : ‖(0 : ℝ) - (0 + 0 - 0)‖ ≤
    Real.exp ((0 : ℝ) * 1) * (((0 : NNReal) : ℝ) * ‖(0 : ℝ) - 0‖
      + ((1 : NNReal) : ℝ) * ‖(0 : ℝ) - 0‖ + ‖(0 : ℝ) - id 0‖)
      + (2 * 0 + 0) * ∫ s in (0 : ℝ)..1, Real.exp (0 * (1 - s)) := by
  have hc : ODESolution (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 1 :=
    ⟨continuousOn_const, fun t _ => hasDerivWithinAt_const t _ _⟩
  have hA : ODESolution (fun (_ : ℝ) (x : ℝ) => (0 : ℝ →L[ℝ] ℝ) x + 0) (fun _ => (0 : ℝ)) 0 1 := by
    simpa using hc
  exact lemma_3_2 (E := ℝ) 0 0 (ℓ := 0) (by simp) (fun _ => 0) (fun _ => 0) (εr := 0) (εq := 0)
    (by simp) (by simp) id id (Crq := 0) (Cq := 1)
    (by simp)
    LipschitzWith.id (h := 1) zero_le_one hA hc hc hc (X := fun _ => 0) (Z := fun _ => 0)
    (W := fun _ => 0) (V := fun _ => 0) (Xn := 0) (Yk := 0) (Yk1 := 0) rfl rfl rfl rfl

/-- Non-vacuity of the recursion hypotheses of Thms 3.3, 3.5, 3.6 (`α = β = 1/4`, `κ = 1`). -/
example : ∃ e : ℕ → ℕ → ℝ, (∀ k, e k 0 = 0) ∧
    (∀ k n, e (k + 1) (n + 1) ≤ (1 / 4) * e k n + (1 / 4) * e (k + 1) n + 1) :=
  ⟨fun _ _ => 0, fun _ => rfl, fun _ _ => by norm_num⟩

end ErrorIteration

end LeanDLRA.Literature.P2203_08455
