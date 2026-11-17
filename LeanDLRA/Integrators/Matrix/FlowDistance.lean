import LeanDLRA.Integrators.Matrix.ParallelBUGStep

/-!
# Distance of an exact solution to the low-rank matrices, near a reference solution

Let `Φ` be an exact solution of `Y' = F(t, Y)` that starts at a matrix of rank at most `r`. The
distance of `Φ t₁` to the matrices of rank at most `r` measures how much a retraction to rank
`r` after a step of size `h = t₁ - t₀` costs. `distLR_flow_le_of_tube` bounds it by
`h (10 L B h + ε)` when the field is controlled only on a tube around a reference solution. That
bound has a term `h²`, which is harmless for methods of order one but spoils every method of
higher order: the local error of the retraction must be `O(h (ε + h^p))`.

This file proves the bound without the `h²` term on a tube:

  `dist(Φ t₁, M_{≤ r}) ≤ h ε e^{L h}`

(`distLR_flow_le_exp_of_tube`). It is the bound (15) of [KieriVandereycken2019] (proof of their
Theorem 2) with `ℓ = L`, there obtained from the solution of the projected equation
`Y' = P(Y) F(t, Y)` on the rank-`r` manifold; here no such solution and no singular value of
`Φ t₀` enters.

## Main results

* `distLR_flow_step_of_tube`: over a substep `[s, s + τ]`,
  `dist(Φ(s + τ), M_{≤ r}) ≤ e^{L τ} dist(Φ s, M_{≤ r}) + τ (10 L B τ + ε)`.
* `distLR_flow_le_exp_of_tube`: the bound `h ε e^{L h}`.

## Implementation notes

The library has bounds of the same form for fields that are Lipschitz and bounded everywhere and
whose normal part is small at every factored rank-`r` matrix (`distLR_flow_le_exp` and
`distLR_flow_le_exp_mul_add`, with the constant `1`). They cannot be applied to the
tube extension `tubeExt F A a b ρ` of the field: the extension evaluates `F` at the point
retracted to the ball around `A t`, which is not of the form `U S Vᵀ` for the factors of the
original point, so the normal bound of the extension is not controlled outside the tube. The
proof therefore localizes the argument, not the statement: the step is split into `N` substeps;
on each, the exact solution `Ψ` started at a best approximation of rank at most `r` of the
current value stays in the tube, so `distLR_flow_le_of_tube` applies to it, and Grönwall's
inequality for the extended field compares `Φ` with `Ψ`. Summing the substeps gives
`h ε e^{L h} + 10 L B h² e^{L h} / N`, and `N → ∞` removes the second term.

The margin `‖Φ t₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ` keeps the start values of all substep solutions
in the tube: they are within `B (t - t₀)` of `Φ t`, which is within `2 B (t - t₀)` of its
distance to `A` at `t₀`, and the substep solutions move by at most `2 B τ` relative to `A`.

## References

* [KieriVandereycken2019] E. Kieri, B. Vandereycken, *Projection methods for dynamical low-rank
  approximation of high-dimensional problems*, Comput. Methods Appl. Math. 19 (2019), eq. (15).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

section FlowDistance

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A Φ : ℝ → Matrix m n ℝ} {a b ρ L B ε t₀ t₁ : ℝ}

/-- **One substep of the distance recursion, near a reference solution.** Let `F` be
`L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
continuous there, with normal part at most `ε` at the factored rank-`r` points of the tube. Let
`Φ` be an exact solution on `[t₀, t₁] ⊆ [a, b]` whose start value has rank at most `r` and
satisfies `‖Φ t₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`. Then for every substep `[s, s + τ] ⊆ [t₀, t₁]`

  `dist(Φ(s + τ), M_{≤ r}) ≤ e^{L τ} dist(Φ s, M_{≤ r}) + τ (10 L B τ + ε)`. -/
theorem distLR_flow_step_of_tube (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hε₀ : 0 ≤ ε) (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hΦ : ODESolution F Φ t₀ t₁) (hrank : (Φ t₀).rank ≤ r)
    (hsmall : ‖Φ t₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) {s τ : ℝ} (hs : t₀ ≤ s) (hτ : 0 ≤ τ)
    (hsτ : s + τ ≤ t₁) :
    distLR r (Φ (s + τ)) ≤ Real.exp (L * τ) * distLR r (Φ s) + τ * (10 * L * B * τ + ε) := by
  have h0 : 0 ≤ t₁ - t₀ := sub_nonneg.2 h01
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB h0
  have hρ : 0 ≤ ρ := by linarith [norm_nonneg (Φ t₀ - A t₀)]
  have hst : s ≤ t₁ := by linarith
  have has : a ≤ s := ha.trans hs
  have hbs : s + τ ≤ b := hsτ.trans hb
  -- `Φ` stays in the tube and moves at speed at most `B`; so does `A`
  have hnearΦ := ODESolution.near_of_comp_proj (Ψ := id) (G := F) hΦ (fun _ => le_rfl) hFB hB
    ha hb hA (by linarith)
  have hAs : ‖A s - A t₀‖ ≤ B * (s - t₀) := hA.norm_sub_le (hFB.along hρ ha hb) s ⟨hs, hst⟩
  have hΦs : ‖Φ s - Φ t₀‖ ≤ B * (s - t₀) := (hnearΦ s ⟨hs, hst⟩).2
  have hΦA : ‖Φ s - A s‖ ≤ ‖Φ t₀ - A t₀‖ + 2 * B * (s - t₀) := by
    have e : Φ s - A s = (Φ s - Φ t₀) + (Φ t₀ - A t₀) - (A s - A t₀) := by abel
    rw [e]
    linarith [norm_sub_le ((Φ s - Φ t₀) + (Φ t₀ - A t₀)) (A s - A t₀),
      norm_add_le (Φ s - Φ t₀) (Φ t₀ - A t₀)]
  -- a best approximation `Z` of `Φ s` of rank at most `r`
  obtain ⟨Z, hZ, hZd⟩ := exists_best_approx r (Φ s)
  have hds : distLR r (Φ s) ≤ B * (s - t₀) := (distLR_le_norm_sub hrank).trans hΦs
  have hZA : ‖Z - A s‖ + 2 * B * τ < ρ := by
    have h₁ : ‖Z - A s‖ ≤ ‖Z - Φ s‖ + ‖Φ s - A s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev Z (Φ s), hZd] at h₁
    nlinarith [mul_nonneg hB (sub_nonneg.2 hsτ), mul_nonneg hB hτ]
  -- the extended field and the solution `Ψ` started at `Z`
  set G := tubeExt F A a b ρ with hGdef
  have hGL : IsLipschitzField G L := isLipschitzField_tubeExt hFL hL hρ
  have hGB : IsBoundedField G B := isBoundedField_tubeExt hFB hB hρ
  have hGc : ∀ x, ContinuousOn (fun t => G t x) (Icc s (s + τ)) := fun x =>
    (continuousOn_tubeExt hc hAc hρ x).mono (Icc_subset_Icc has hbs)
  obtain ⟨Ψ, hΨ, hΨ₀⟩ := exists_ODESolution_of_continuousOn hGL hGB hGc (by linarith) Z
  have hAs' : ODESolution F A s (s + τ) := hA.mono hs hsτ
  have hAG : ODESolution G A s (s + τ) :=
    (odeSolution_tubeExt_iff has hbs fun t _ => by simpa using hρ).2 hAs'
  -- `Ψ` stays in the tube, so it solves the original equation
  have hinΨ := ODESolution.near_of_comp_proj (Ψ := id) (G := G) hΨ (fun _ => le_rfl)
    (hGB.isBoundedOnTube A a b ρ) hB has hbs hAG (by rw [hΨ₀, add_sub_cancel_left]; exact hZA)
  have hΨF : ODESolution F Ψ s (s + τ) :=
    (odeSolution_tubeExt_iff has hbs fun t ht => (hinΨ t (Ico_subset_Icc_self ht)).1.le).1 hΨ
  have h₁ := distLR_flow_le_of_tube hε hε₀ hFL hL hFB hB hc hAc has hbs (by linarith) hAs' hΨF
    (by rw [hΨ₀]; exact hZ) (by rw [hΨ₀, add_sub_cancel_left]; exact hZA)
  rw [add_sub_cancel_left] at h₁
  -- Grönwall for the extended field
  have hΦG : ODESolution G Φ s (s + τ) :=
    (odeSolution_tubeExt_iff has hbs fun t ht =>
      (hnearΦ t ⟨hs.trans ht.1, ht.2.le.trans hsτ⟩).1.le).2 (hΦ.mono hs hsτ)
  have h₂ := norm_sub_le_exp_of_odeSolution hGL hL (by linarith) hΦG hΨ
  rw [hΨ₀, hZd, add_sub_cancel_left] at h₂
  have h₃ := distLR_le_add (r := r) (Φ (s + τ)) (Ψ (s + τ))
  linarith

/-- **The `h²`-free distance bound near a reference solution** ([KieriVandereycken2019],
eq. (15), with `ℓ = L` and without the projected solution). Let `F` be `L`-Lipschitz and bounded
by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, continuous there, with
normal part at most `ε` at the factored rank-`r` points of the tube (`FactoredNormalBoundOn`).
Let `Φ` be an exact solution on `[t₀, t₁] ⊆ [a, b]` whose start value has rank at most `r` and
satisfies `‖Φ t₀ - A t₀‖ + 3 B (t₁ - t₀) < ρ`. Then

  `dist(Φ t₁, M_{≤ r}) ≤ (t₁ - t₀) ε e^{L (t₁ - t₀)}`.

No singular value of `Φ t₀` enters. This is the tube form of the global bound
`distLR_flow_le_exp`, with the same constant `1`; the global statements need the normal bound
at every factored matrix and cannot be applied to the tube extension of `F`, so the proof repeats
the substep argument inside the tube (`distLR_flow_step_of_tube`) and lets the number of
substeps tend to infinity. -/
theorem distLR_flow_le_exp_of_tube (hε : FactoredNormalBoundOn F r (tubeSet A a b ρ) ε)
    (hε₀ : 0 ≤ ε) (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L)
    (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (hc : ContinuousOn (Function.uncurry F) (tubeSet A a b ρ)) (hAc : ContinuousOn A (Icc a b))
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hΦ : ODESolution F Φ t₀ t₁) (hrank : (Φ t₀).rank ≤ r)
    (hsmall : ‖Φ t₀ - A t₀‖ + 3 * B * (t₁ - t₀) < ρ) :
    distLR r (Φ t₁) ≤ (t₁ - t₀) * ε * Real.exp (L * (t₁ - t₀)) := by
  set h := t₁ - t₀ with hhdef
  have hh : 0 ≤ h := sub_nonneg.2 h01
  have hN : ∀ N : ℕ, 0 < N → distLR r (Φ t₁) ≤
      h * ε * Real.exp (L * h) + 10 * L * B * h ^ 2 * Real.exp (L * h) / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set τ := h / N with hτdef
    have hτ : 0 ≤ τ := div_nonneg hh hNr.le
    have hNτ : (N : ℝ) * τ = h := by rw [hτdef]; field_simp
    set c := τ * (10 * L * B * τ + ε) with hcdef
    have hc0 : 0 ≤ c := by positivity
    -- the recursion over the substeps (discrete Grönwall)
    have grid : ∀ k : ℕ, k ≤ N →
        distLR r (Φ (t₀ + k * τ)) ≤ k * c * Real.exp (L * (k * τ)) := by
      intro k
      induction k with
      | zero => intro _; simp [distLR_eq_zero_of_rank_le hrank]
      | succ k ih =>
        intro hk
        have hk' : k ≤ N := by omega
        have hkτ : ((k + 1 : ℕ) : ℝ) * τ ≤ h := by
          rw [← hNτ]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hτ
        have hkτ0 : 0 ≤ (k : ℝ) * τ := mul_nonneg (Nat.cast_nonneg k) hτ
        have hstep := distLR_flow_step_of_tube hε hε₀ hFL hL hFB hB hc hAc ha hb h01 hA hΦ
          hrank hsmall (s := t₀ + k * τ) (τ := τ) (by linarith) hτ
          (by push_cast at hkτ; linarith)
        have e0 : t₀ + ((k + 1 : ℕ) : ℝ) * τ = t₀ + k * τ + τ := by push_cast; ring
        rw [e0]
        have e1 : Real.exp (L * τ) * Real.exp (L * (k * τ)) =
            Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) := by
          rw [← Real.exp_add]; push_cast; ring_nf
        have e2 : 1 ≤ Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) := Real.one_le_exp (by positivity)
        have hexp0 : 0 ≤ Real.exp (L * τ) := (Real.exp_pos _).le
        have h5 := mul_le_mul_of_nonneg_left (ih hk') hexp0
        have h6 : Real.exp (L * τ) * (k * c * Real.exp (L * (k * τ))) =
            k * c * Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) := by
          rw [← e1]; ring
        have h7 : c ≤ c * Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) :=
          le_mul_of_one_le_right hc0 e2
        calc distLR r (Φ (t₀ + k * τ + τ))
            ≤ Real.exp (L * τ) * distLR r (Φ (t₀ + k * τ)) + c := hstep
          _ ≤ k * c * Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ))
              + c * Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) := by linarith
          _ = ((k + 1 : ℕ) : ℝ) * c * Real.exp (L * (((k + 1 : ℕ) : ℝ) * τ)) := by
              push_cast; ring
    have hg := grid N le_rfl
    rw [hNτ, show t₀ + h = t₁ by rw [hhdef]; ring] at hg
    have e : (N : ℝ) * c = h * ε + 10 * L * B * h ^ 2 / N := by
      rw [hcdef, hτdef]
      field_simp
      ring
    rw [e] at hg
    calc distLR r (Φ t₁) ≤ (h * ε + 10 * L * B * h ^ 2 / N) * Real.exp (L * h) := hg
      _ = _ := by ring
  -- let the number of substeps tend to infinity
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨N, hN'⟩ := exists_nat_gt (10 * L * B * h ^ 2 * Real.exp (L * h) / η)
  have hq : 0 ≤ 10 * L * B * h ^ 2 * Real.exp (L * h) / η := by positivity
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt hq hN'
  have hlt : 10 * L * B * h ^ 2 * Real.exp (L * h) / N ≤ η := by
    rw [div_le_iff₀ hNr]
    rw [div_lt_iff₀ hη] at hN'
    linarith [mul_comm η (N : ℝ)]
  linarith [hN N (by exact_mod_cast hNr)]

/-- **Non-vacuity of `distLR_flow_le_exp_of_tube`**, for the linear field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`). On the tube of
radius `ρ` around `A(t) = C` the field is `(‖M‖ + ‖N‖)`-Lipschitz, bounded by `(‖M‖ + ‖N‖) ρ`, and
its normal part is at most `‖G‖` (`dlraProblem_linear`, `factoredNormalBoundOn_linear`). Every
solution that starts at a matrix of rank at most `r` close enough to `C` stays within
`(t₁ - t₀) ‖G‖ e^{(‖M‖ + ‖N‖)(t₁ - t₀)}` of the matrices of rank at most `r`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) {ρ t₀ t₁ : ℝ} (hρ : 0 ≤ ρ) (h01 : t₀ ≤ t₁)
    {Φ : ℝ → Matrix m n ℝ} (hΦ : ODESolution (fun _ Y => M * Y + Y * Nᵀ + G) Φ t₀ t₁)
    (hrank : (Φ t₀).rank ≤ r)
    (hsmall : ‖Φ t₀ - C‖ + 3 * ((‖M‖ + ‖N‖) * ρ) * (t₁ - t₀) < ρ) :
    distLR r (Φ t₁) ≤ (t₁ - t₀) * ‖G‖ * Real.exp ((‖M‖ + ‖N‖) * (t₁ - t₀)) := by
  have hP := dlraProblem_linear M N G C hC t₀ t₁ hρ
  exact distLR_flow_le_exp_of_tube (factoredNormalBoundOn_linear M N G _) (norm_nonneg G)
    hP.lipschitz hP.L_nonneg hP.bounded hP.B_nonneg
    (continuous_uncurry_linear M N G).continuousOn continuousOn_const le_rfl le_rfl h01 hP.sol
    hΦ hrank hsmall

end FlowDistance

end LeanDLRA
