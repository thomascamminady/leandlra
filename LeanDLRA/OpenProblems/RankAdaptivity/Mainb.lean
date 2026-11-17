import LeanDLRA.OpenProblems.RankAdaptivity.MainDefs
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.BestApproximation
import LeanDLRA.Stability.Conservation
import LeanDLRA.Training.Descent
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall

/-!
# Open problems OP-RA-14, OP-RA-15, OP-RA-23, OP-RA-24, OP-RA-25
-/

open Set Finset Matrix
open scoped RealInnerProductSpace

namespace LeanDLRA.OpenProblems.RankAdaptivity

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Variable-defect comparison (variation of constants for `D⁺ ‖y - z‖ ≤ ℓ ‖y - z‖ + η`). -/
private theorem norm_sub_le_exp_add_integral {y z u w : ℝ → E} {ℓ a b : ℝ} {η : ℝ → ℝ}
    (hηc : ContinuousOn η (Icc a b))
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hin : ∀ t ∈ Ico a b, ⟪y t - z t, u t - w t⟫ ≤ ℓ * ‖y t - z t‖ ^ 2 + ‖y t - z t‖ * η t)
    (hzero : ∀ t ∈ Ico a b, y t = z t → ‖u t - w t‖ ≤ η t) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤
      Real.exp (ℓ * (t - a)) * ‖y a - z a‖ + ∫ s in a..t, Real.exp (ℓ * (t - s)) * η s := by
  intro t₁ ht₁
  have hab : a ≤ b := ht₁.1.trans ht₁.2
  set ηt : ℝ → ℝ := fun s => η (max a (min s b)) with hηt
  have hηtc : Continuous ηt :=
    hηc.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun s => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hηeq : ∀ s ∈ Icc a b, ηt s = η s := by
    intro s hs
    simp only [hηt, min_eq_left hs.2, max_eq_right hs.1]
  set δ : ℝ := ‖y a - z a‖ with hδ
  set g : ℝ → ℝ := fun s => Real.exp (-ℓ * (s - a)) * ηt s with hg
  have hgc : Continuous g := by
    refine Continuous.mul ?_ hηtc
    fun_prop
  set Φ : ℝ → ℝ := fun t => Real.exp (ℓ * (t - a)) * (δ + ∫ s in a..t, g s) with hΦ
  have hΦd : ∀ t, HasDerivAt Φ (ℓ * Φ t + ηt t) t := by
    intro t
    have h1 : HasDerivAt (fun t => Real.exp (ℓ * (t - a))) (Real.exp (ℓ * (t - a)) * ℓ) t := by
      have := ((hasDerivAt_id t).sub_const a).const_mul ℓ
      simpa using this.exp
    have h2 : HasDerivAt (fun t => δ + ∫ s in a..t, g s) (g t) t :=
      ((hgc.integral_hasStrictDerivAt a t).hasDerivAt).const_add δ
    have h3 := h1.mul h2
    convert h3 using 1
    simp only [hΦ, hg]
    have : Real.exp (ℓ * (t - a)) * Real.exp (-ℓ * (t - a)) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc ℓ * (Real.exp (ℓ * (t - a)) * (δ + ∫ s in a..t, g s)) + ηt t
        = Real.exp (ℓ * (t - a)) * ℓ * (δ + ∫ s in a..t, g s) + ηt t * 1 := by ring
      _ = _ := by rw [← this]; ring
  have H : ∀ ε > 0, ∀ x ∈ Icc a b, ‖y x - z x‖ ≤ Φ x + ε * Real.exp ((ℓ + 1) * (x - a)) := by
    intro ε hε x hx
    refine image_le_of_liminf_slope_right_lt_deriv_boundary
      (f := fun t => ‖y t - z t‖) (f' := fun t => ℓ * ‖y t - z t‖ + η t)
      (B := fun t => Φ t + ε * Real.exp ((ℓ + 1) * (t - a)))
      (B' := fun t => ℓ * Φ t + ηt t + ε * (Real.exp ((ℓ + 1) * (t - a)) * (ℓ + 1)))
      (hyc.sub hzc).norm ?_ ?_ ?_ ?_ hx
    · intro x hx r hr
      have he : HasDerivWithinAt (fun t => y t - z t) (u x - w x) (Ici x) x :=
        (hy x hx).sub (hz x hx)
      by_cases hx0 : y x - z x = 0
      · have hnorm : ‖u x - w x‖ < r := by
          refine lt_of_le_of_lt (hzero x hx (sub_eq_zero.1 hx0)) ?_
          simpa [hx0] using hr
        exact he.liminf_right_slope_norm_le hnorm
      · have hd := hasDerivWithinAt_norm_of_ne he hx0
        have hpos : 0 < ‖y x - z x‖ := norm_pos_iff.2 hx0
        have hle : ⟪y x - z x, u x - w x⟫ / ‖y x - z x‖ ≤ ℓ * ‖y x - z x‖ + η x := by
          rw [div_le_iff₀ hpos]
          have := hin x hx
          nlinarith
        have := hd.liminf_right_slope_le (lt_of_le_of_lt hle hr)
        simpa [slope_def_module, smul_eq_mul] using this
    · simp only [hΦ, sub_self, mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero,
        one_mul, mul_one]
      linarith
    · intro x
      have h1 : HasDerivAt (fun t => Real.exp ((ℓ + 1) * (t - a)))
          (Real.exp ((ℓ + 1) * (x - a)) * (ℓ + 1)) x := by
        have := ((hasDerivAt_id x).sub_const a).const_mul (ℓ + 1)
        simpa using this.exp
      exact (hΦd x).add (h1.const_mul ε)
    · intro x hx' hfx
      have hηx : ηt x = η x := hηeq x (Ico_subset_Icc_self hx')
      change ‖y x - z x‖ = _ at hfx
      change ℓ * ‖y x - z x‖ + η x < _
      rw [hηx]
      have hpos : 0 < ε * Real.exp ((ℓ + 1) * (x - a)) := by positivity
      rw [hfx]
      nlinarith [mul_pos hε (Real.exp_pos ((ℓ + 1) * (x - a)))]
  have hfinal : ‖y t₁ - z t₁‖ ≤ Φ t₁ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc : 0 < Real.exp ((ℓ + 1) * (t₁ - a)) := Real.exp_pos _
    have := H (ε / Real.exp ((ℓ + 1) * (t₁ - a))) (div_pos hε hc) t₁ ht₁
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  refine hfinal.trans (le_of_eq ?_)
  simp only [hΦ]
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  refine congrArg (fun y : ℝ => _ + y) ?_
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht₁.1] at hs
  have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht₁.2⟩
  simp only [hg]
  rw [hηeq s hsb, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The Taylor polynomial `∑_{j ≤ k} sʲ vⱼ / j!` has derivative `∑_{j < k} sʲ vⱼ₊₁ / j!`. -/
private theorem hasDerivAt_taylor_sum (v : ℕ → E) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ j ∈ range (k + 1), (s ^ j / (j.factorial : ℝ)) • v j)
      (∑ j ∈ range k, (t ^ j / (j.factorial : ℝ)) • v (j + 1)) t := by
  induction k with
  | zero => simpa using hasDerivAt_const t (v 0)
  | succ k ih =>
    have h1 : HasDerivAt (fun s : ℝ => (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • v (k + 1))
        ((t ^ k / (k.factorial : ℝ)) • v (k + 1)) t := by
      have := ((hasDerivAt_pow (k + 1) t).div_const ((k + 1).factorial : ℝ)).smul_const (v (k + 1))
      convert this using 2
      rw [Nat.factorial_succ]
      push_cast
      have : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have h2 := ih.add h1
    convert h2 using 1
    · funext s
      exact sum_range_succ _ _
    · exact sum_range_succ _ _

/-- A Galerkin trajectory `y' = R 𝒜 y` started in the range of the projector stays there. -/
private theorem galerkin_range_eq {𝒜 R : E →L[ℝ] E} (hR : IsOrthProj R) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ v => R (𝒜 v)) y a b) (h0 : R (y a) = y a) :
    ∀ t ∈ Icc a b, R (y t) = y t := by
  intro t ht
  have hgc : ContinuousOn (fun s => y s - R (y s)) (Icc a b) :=
    hy.cont.sub (R.continuous.comp_continuousOn hy.cont)
  have hgd : ∀ s ∈ Ico a b, HasDerivWithinAt (fun s => y s - R (y s)) 0 (Ici s) s := by
    intro s hs
    have h1 := hy.deriv s hs
    have h2 := R.hasFDerivAt.comp_hasDerivWithinAt s h1
    convert h1.sub h2 using 1
    all_goals first | rfl | rw [hR.idem, sub_self]
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd (C := 0)
    (fun _ _ => by simp) t ht
  rw [h0, sub_self, sub_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- **OP-RA-14: Krylov enrichment for skew-adjoint (Schrödinger-type) generators.**  If
`⟪𝒜 v, v⟫ = 0` and `range R ⊇ span {y₀, 𝒜 y₀, …, 𝒜ᵏ y₀}`, the Galerkin flow `y' = R 𝒜 y` from
`y₀` has error `≤ 2 (h ‖𝒜‖)^{k+1} ‖y₀‖ / (k+1)!` at time `h`, without the factor `e^{h ‖𝒜‖}` of
the general case (`galerkin_krylov_error`). -/
theorem galerkin_krylov_error_skew {𝒜 R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hskew : ∀ v, ⟪𝒜 v, v⟫ = 0) {k : ℕ} {y₀ : E}
    (hK : ∀ j ≤ k, R ((𝒜 ^ j) y₀) = (𝒜 ^ j) y₀) {h : ℝ} (hh : 0 ≤ h) {x y : ℝ → E}
    (hx : ODESolution (fun _ v => 𝒜 v) x 0 h) (hx₀ : x 0 = y₀)
    (hy : ODESolution (fun _ v => R (𝒜 v)) y 0 h) (hy₀ : y 0 = y₀) :
    ‖y h - x h‖ ≤ 2 * (h * ‖𝒜‖) ^ (k + 1) / (k + 1).factorial * ‖y₀‖ := by
  have hyR : ∀ t ∈ Icc 0 h, R (y t) = y t :=
    galerkin_range_eq hR hy (by rw [hy₀]; simpa using hK 0 (Nat.zero_le _))
  set v : ℕ → E := fun j => (𝒜 ^ j) y₀ with hv
  set C : ℝ := ‖𝒜‖ ^ (k + 1) * ‖y₀‖ with hC
  set p : ℝ → E := fun s => ∑ j ∈ range (k + 1), (s ^ j / (j.factorial : ℝ)) • v j with hp
  set q : ℝ → E := fun s => ∑ j ∈ range k, (s ^ j / (j.factorial : ℝ)) • v (j + 1) with hq
  have hpd : ∀ s, HasDerivAt p (q s) s := fun s => hasDerivAt_taylor_sum v k s
  have hpc : ContinuousOn p (Icc 0 h) := fun s _ => (hpd s).continuousAt.continuousWithinAt
  have hvs : ∀ j, 𝒜 (v j) = v (j + 1) := fun j => by simp [hv, pow_succ']
  have hAp : ∀ s, 𝒜 (p s) = q s + (s ^ k / (k.factorial : ℝ)) • v (k + 1) := by
    intro s
    simp only [hp, hq, map_sum, map_smul, hvs]
    exact sum_range_succ _ _
  have hRp : ∀ s, R (p s) = p s := by
    intro s
    simp only [hp, map_sum, map_smul]
    refine sum_congr rfl fun j hj => ?_
    rw [show R (v j) = v j from hK j (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  have hRq : ∀ s, R (q s) = q s := by
    intro s
    simp only [hq, map_sum, map_smul]
    refine sum_congr rfl fun j hj => ?_
    rw [show R (v (j + 1)) = v (j + 1) from hK (j + 1) (mem_range.1 hj)]
  have hv1 : ‖v (k + 1)‖ ≤ C := by
    calc ‖v (k + 1)‖ = ‖(𝒜 ^ (k + 1)) y₀‖ := rfl
      _ ≤ ‖𝒜 ^ (k + 1)‖ * ‖y₀‖ := (𝒜 ^ (k + 1)).le_opNorm y₀
      _ ≤ ‖𝒜‖ ^ (k + 1) * ‖y₀‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le' 𝒜 (Nat.succ_pos k)) (norm_nonneg _)
  set η : ℝ → ℝ := fun s => s ^ k / (k.factorial : ℝ) * C with hη
  have hηc : ContinuousOn η (Icc 0 h) := by
    refine Continuous.continuousOn ?_
    simp only [hη]
    fun_prop
  have hdef : ∀ s ∈ Ico 0 h, ‖(s ^ k / (k.factorial : ℝ)) • v (k + 1)‖ ≤ η s := by
    intro s hs
    rw [norm_smul, Real.norm_of_nonneg (by have := hs.1; positivity)]
    exact mul_le_mul_of_nonneg_left hv1 (by have := hs.1; positivity)
  have hint : ∀ s ∈ Icc (0 : ℝ) h, ∫ r in (0 : ℝ)..s, Real.exp (0 * (s - r)) * η r =
      s ^ (k + 1) / ((k + 1).factorial : ℝ) * C := by
    intro s _
    simp only [hη, zero_mul, Real.exp_zero, one_mul]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_pow]
    simp only [Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hp0 : p 0 = y₀ := by simp [hp, hv, sum_range_succ']
  have hAp' : ∀ s, 𝒜 (p s) - q s = (s ^ k / (k.factorial : ℝ)) • v (k + 1) := fun s => by
    rw [hAp s]; abel
  have hRAp : ∀ s, R (𝒜 (p s)) - q s = (s ^ k / (k.factorial : ℝ)) • R (v (k + 1)) := fun s => by
    rw [hAp s, map_add, map_smul, hRq s]; abel
  have hxin : ∀ t ∈ Ico 0 h, ⟪x t - p t, 𝒜 (x t) - q t⟫ ≤
      0 * ‖x t - p t‖ ^ 2 + ‖x t - p t‖ * η t := by
    intro t ht
    have hs : 𝒜 (x t) - q t = 𝒜 (x t - p t) + (t ^ k / (k.factorial : ℝ)) • v (k + 1) := by
      rw [map_sub, ← hAp' t]; abel
    rw [hs, inner_add_right, real_inner_comm, hskew, zero_add, zero_mul, zero_add]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hdef t ht) (norm_nonneg _))
  have hxz : ∀ t ∈ Ico 0 h, x t = p t → ‖𝒜 (x t) - q t‖ ≤ η t := by
    intro t ht hxp
    rw [hxp, hAp' t]
    exact hdef t ht
  have hyin : ∀ t ∈ Ico 0 h, ⟪y t - p t, R (𝒜 (y t)) - q t⟫ ≤
      0 * ‖y t - p t‖ ^ 2 + ‖y t - p t‖ * η t := by
    intro t ht
    have hRe : R (y t - p t) = y t - p t := by
      rw [map_sub, hyR t (Ico_subset_Icc_self ht), hRp t]
    have hs : R (𝒜 (y t)) - q t =
        R (𝒜 (y t - p t)) + (t ^ k / (k.factorial : ℝ)) • R (v (k + 1)) := by
      rw [← hRAp t, map_sub, map_sub]; abel
    have hnorm : ‖(t ^ k / (k.factorial : ℝ)) • R (v (k + 1))‖ ≤ η t := by
      refine le_trans ?_ (hdef t ht)
      rw [norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hR.norm_le _) (norm_nonneg _)
    have h0 : ⟪y t - p t, R (𝒜 (y t - p t))⟫ = 0 := by
      rw [← hR.symm, hRe, real_inner_comm, hskew]
    rw [hs, inner_add_right, h0, zero_add, zero_mul, zero_add]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hyz : ∀ t ∈ Ico 0 h, y t = p t → ‖R (𝒜 (y t)) - q t‖ ≤ η t := by
    intro t ht hyp
    rw [hyp, hRAp t]
    refine le_trans ?_ (hdef t ht)
    rw [norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hR.norm_le _) (norm_nonneg _)
  have hx1 := norm_sub_le_exp_add_integral (y := x) (z := p) (u := fun s => 𝒜 (x s)) (w := q)
    (ℓ := 0) hηc hx.cont hx.deriv hpc (fun s _ => (hpd s).hasDerivWithinAt) hxin hxz h
    ⟨hh, le_rfl⟩
  have hy1 := norm_sub_le_exp_add_integral (y := y) (z := p) (u := fun s => R (𝒜 (y s)))
    (w := q) (ℓ := 0) hηc hy.cont hy.deriv hpc (fun s _ => (hpd s).hasDerivWithinAt) hyin hyz h
    ⟨hh, le_rfl⟩
  rw [hint h ⟨hh, le_rfl⟩, hx₀, hp0, sub_self, norm_zero, mul_zero, zero_add] at hx1
  rw [hint h ⟨hh, le_rfl⟩, hy₀, hp0, sub_self, norm_zero, mul_zero, zero_add] at hy1
  have htri := norm_sub_le_norm_sub_add_norm_sub (y h) (p h) (x h)
  rw [norm_sub_rev (p h) (x h)] at htri
  calc ‖y h - x h‖ ≤ 2 * (h ^ (k + 1) / ((k + 1).factorial : ℝ) * C) := by linarith
    _ = _ := by rw [hC, mul_pow]; ring

attribute [-instance] ContinuousLinearMap.instNPowId in
/-- The statement of `galerkin_krylov_error_skew` as recorded on v4.36.0-rc2, where `𝒜 ^ j`
elaborated with `Monoid.toNPow`; Mathlib v4.36.0 elaborates `ContinuousLinearMap.instNPowId`.
Both forms are the same proposition: this one follows from the theorem by `exact`. -/
example {𝒜 R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hskew : ∀ v, ⟪𝒜 v, v⟫ = 0) {k : ℕ} {y₀ : E}
    (hK : ∀ j ≤ k, R ((𝒜 ^ j) y₀) = (𝒜 ^ j) y₀) {h : ℝ} (hh : 0 ≤ h) {x y : ℝ → E}
    (hx : ODESolution (fun _ v => 𝒜 v) x 0 h) (hx₀ : x 0 = y₀)
    (hy : ODESolution (fun _ v => R (𝒜 v)) y 0 h) (hy₀ : y 0 = y₀) :
    ‖y h - x h‖ ≤ 2 * (h * ‖𝒜‖) ^ (k + 1) / (k + 1).factorial * ‖y₀‖ := by
  exact galerkin_krylov_error_skew hR hskew hK hh hx hx₀ hy hy₀

set_option linter.unusedSectionVars false in
/-- **OP-RA-15 (i): a fixed tolerance gives a plateau, not convergence.**  For an iteration that
contracts with factor `q < 1` towards the fixed point `x⋆` and is perturbed by truncations of
size `≤ ϑ`, `‖xₙ - x⋆‖ ≤ qⁿ ‖x₀ - x⋆‖ + ϑ / (1 - q)`. -/
theorem perturbed_contraction_le {G : E → E} {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1)
    (hG : ∀ x y, ‖G x - G y‖ ≤ q * ‖x - y‖) {xs : E} (hfix : G xs = xs) {x : ℕ → E} {ϑ : ℝ}
    (hx : ∀ n, ‖x (n + 1) - G (x n)‖ ≤ ϑ) :
    ∀ n, ‖x n - xs‖ ≤ q ^ n * ‖x 0 - xs‖ + ϑ / (1 - q) := by
  have hq' : 0 < 1 - q := sub_pos.2 hq
  intro n
  induction n with
  | zero =>
    have := (norm_nonneg _).trans (hx 0)
    simp only [pow_zero, one_mul]
    linarith [div_nonneg this hq'.le]
  | succ n ih =>
    have h1 := norm_sub_le_norm_sub_add_norm_sub (x (n + 1)) (G (x n)) xs
    have h2 := hG (x n) xs
    rw [hfix] at h2
    have h3 := hx n
    have h4 : q * (q ^ n * ‖x 0 - xs‖ + ϑ / (1 - q)) + ϑ =
        q ^ (n + 1) * ‖x 0 - xs‖ + ϑ / (1 - q) := by
      field_simp
      ring
    have h5 := mul_le_mul_of_nonneg_left ih hq0
    linarith

set_option linter.unusedSectionVars false in
/-- **OP-RA-15 (iii): an a posteriori tolerance keeps linear convergence.**  If the truncation
at step `n` is bounded by `c ‖xₙ₊₁ - xₙ‖` with `c < 1`, the perturbed contraction converges
linearly with rate `(q + c) / (1 - c)` (a contraction when `q + 2 c < 1`). -/
theorem perturbed_contraction_aposteriori {G : E → E} {q : ℝ} (hq0 : 0 ≤ q)
    (hG : ∀ x y, ‖G x - G y‖ ≤ q * ‖x - y‖) {xs : E} (hfix : G xs = xs) {x : ℕ → E} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : ∀ n, ‖x (n + 1) - G (x n)‖ ≤ c * ‖x (n + 1) - x n‖) :
    ∀ n, ‖x n - xs‖ ≤ ((q + c) / (1 - c)) ^ n * ‖x 0 - xs‖ := by
  have hc' : 0 < 1 - c := sub_pos.2 hc1
  have hr : 0 ≤ (q + c) / (1 - c) := div_nonneg (by linarith) hc'.le
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := norm_sub_le_norm_sub_add_norm_sub (x (n + 1)) (G (x n)) xs
    have h2 := hG (x n) xs
    rw [hfix] at h2
    have h3 := hx n
    have h4 : ‖x (n + 1) - x n‖ ≤ ‖x (n + 1) - xs‖ + ‖x n - xs‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (x (n + 1)) xs (x n)
      rwa [norm_sub_rev xs (x n)] at this
    have h5 := mul_le_mul_of_nonneg_left h4 hc0
    have h6 : (1 - c) * ‖x (n + 1) - xs‖ ≤ (q + c) * ‖x n - xs‖ := by nlinarith
    have h7 : ‖x (n + 1) - xs‖ ≤ (q + c) / (1 - c) * ‖x n - xs‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc']
      linarith
    calc ‖x (n + 1) - xs‖ ≤ (q + c) / (1 - c) * ‖x n - xs‖ := h7
      _ ≤ (q + c) / (1 - c) * (((q + c) / (1 - c)) ^ n * ‖x 0 - xs‖) :=
          mul_le_mul_of_nonneg_left ih hr
      _ = _ := by ring

/-- **OP-RA-23: rank-adaptive splitting for stiff problems (abstract core).**  If every step is
an untruncated splitting step `Z n` with local error `η n` against the exact flow from `Y n`
(the fixed-rank analysis of the papers, including the `τ |log τ|` term from parabolic smoothing,
is a hypothesis) followed by a truncation of size `≤ ϑ`, and `F` is one-sided Lipschitz with
constant `ℓ`, then `‖Yₙ - A(tₙ)‖ ≤ e^{max(ℓ,0) n h} (‖Y₀ - A(t₀)‖ + ∑_{k<n} (η k + ϑ))`. -/
theorem truncatedSplitting_global_error {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {Y Z : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {η : ℕ → ℝ} {ϑ : ℝ}
    (hsplit : ∀ n < N, ‖Z n - Φ n (t₀ + (n + 1) * h)‖ ≤ η n)
    (htr : ∀ n < N, ‖Y (n + 1) - Z n‖ ≤ ϑ) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (max ℓ 0 * (n * h)) * (‖Y 0 - A t₀‖ + ∑ k ∈ range n, (η k + ϑ)) := by
  have key := discrete_gronwall_exp_sum_le (e := fun n => ‖Y n - A (t₀ + n * h)‖)
    (b := fun k => η k + ϑ) (L := max ℓ 0) (le_max_right _ _) hh (N := N) ?_ ?_
  · intro n hn
    simpa using key n hn
  · intro n hn
    have h1 := (norm_nonneg _).trans (hsplit n hn)
    have h2 := (norm_nonneg _).trans (htr n hn)
    linarith
  · intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have hNh : ((n : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hn' hh
    have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) hh
    have hAn : ODESolution F A (t₀ + n * h) (t₀ + (n + 1) * h) :=
      hA.mono (by linarith) (by linarith)
    have hstab := (hΦ n hn).norm_sub_le_exp_of_oneSided hAn hF (t₀ + (n + 1) * h)
      ⟨by linarith, le_rfl⟩
    rw [hΦ₀ n hn, show t₀ + (n + 1) * h - (t₀ + n * h) = h by ring] at hstab
    have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
    simp only [hcast]
    have hexp : Real.exp (ℓ * h) ≤ Real.exp (max ℓ 0 * h) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hh)
    have h1 : ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ η n + ϑ := by
      have := norm_sub_le_norm_sub_add_norm_sub (Y (n + 1)) (Z n) (Φ n (t₀ + (n + 1) * h))
      linarith [htr n hn, hsplit n hn]
    have h2 := mul_le_mul_of_nonneg_right hexp (norm_nonneg (Y n - A (t₀ + n * h)))
    have h3 := norm_sub_le_norm_sub_add_norm_sub (Y (n + 1)) (Φ n (t₀ + (n + 1) * h))
      (A (t₀ + (n + 1) * h))
    linarith

/-- **OP-RA-24: reliable a posteriori bound with a time-dependent computed defect.**  If the
computed trajectory `Y` solves `Y' = G(t, Y)` (e.g. `G = P(Y) F`, continuous DLRA) and its defect
`‖G(t, Y t) - F(t, Y t)‖ ≤ η t` is computed along `Y`, then for one-sided Lipschitz `F`,
`‖Y t - A t‖ ≤ e^{ℓ (t - a)} ‖Y a - A a‖ + ∫_a^t e^{ℓ (t - s)} η(s) ds`, a fully computable
bound (the constant-defect case is `ODESolution.norm_sub_le_of_perturbed`). -/
theorem aposteriori_integral {F G : ℝ → E → E} {ℓ a b : ℝ} (hF : IsOneSidedLipschitzField F ℓ)
    {A Y : ℝ → E} (hA : ODESolution F A a b) (hY : ODESolution G Y a b) {η : ℝ → ℝ}
    (hηc : ContinuousOn η (Icc a b)) (hdef : ∀ t ∈ Icc a b, ‖G t (Y t) - F t (Y t)‖ ≤ η t) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤
      Real.exp (ℓ * (t - a)) * ‖Y a - A a‖ + ∫ s in a..t, Real.exp (ℓ * (t - s)) * η s := by
  refine norm_sub_le_exp_add_integral hηc hY.cont hY.deriv hA.cont hA.deriv ?_ ?_
  · intro t ht
    have hsplit : G t (Y t) - F t (A t) =
        (G t (Y t) - F t (Y t)) + (F t (Y t) - F t (A t)) := by abel
    rw [hsplit, inner_add_right]
    have h1 := hF t (Y t) (A t)
    have h2 := real_inner_le_norm (Y t - A t) (G t (Y t) - F t (Y t))
    have h3 := mul_le_mul_of_nonneg_left (hdef t (Ico_subset_Icc_self ht)) (norm_nonneg (Y t - A t))
    rw [real_inner_comm] at h1
    linarith
  · intro t ht hYA
    have : G t (Y t) - F t (A t) = G t (Y t) - F t (Y t) := by rw [hYA]
    rw [this]
    exact hdef t (Ico_subset_Icc_self ht)

/-- **OP-RA-25 (i): a gradient-relative truncation tolerance needs no summability assumption.**
For projected gradient steps followed by truncations of size `≤ c hₖ ‖Πₖ ∇ℒ(xₖ)‖²` with
`G c ≤ 1/4` (`G` a gradient bound on the truncation segments), `β hₖ ≤ 1` and `∑ hₖ = ∞`,
`liminf ‖Πₖ ∇ℒ(xₖ)‖ = 0` unconditionally (compare `frequently_projGrad_sq_lt`, which assumes
bounded accumulated truncation errors).  Stochastic minibatch gradients (Tucker DLRT) are out of
scope; this is the deterministic core. -/
theorem frequently_projGrad_sq_lt_of_relative_tol {ℒ : E → ℝ} {g : E → E} {β : ℝ}
    (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖)
    {P : ℕ → E →L[ℝ] E} (hP : ∀ k, IsOrthProj (P k)) {x : ℕ → E} {h : ℕ → ℝ}
    {G c ℒinf : ℝ} (hc : 0 ≤ c)
    (htr : ∀ k, ‖x (k + 1) - projGradStep (P k) g (h k) (x k)‖ ≤
      c * h k * ‖P k (g (x k))‖ ^ 2)
    (hG : ∀ k, ∀ w ∈ segment ℝ (projGradStep (P k) g (h k) (x k)) (x (k + 1)), ‖g w‖ ≤ G)
    (hGc : G * c ≤ 1 / 4) (hinf : ∀ k, ℒinf ≤ ℒ (x k)) (hh0 : ∀ k, 0 ≤ h k)
    (hh1 : ∀ k, β * h k ≤ 1) (hdiv : ¬ Summable h) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k, N ≤ k ∧ ‖P k (g (x k))‖ ^ 2 < ε := by
  have _ := hc
  refine exists_lt_of_sum_mul_le hh0 (fun k => sq_nonneg _) hdiv
    (C := 4 * (ℒ (x 0) - ℒinf)) (fun n => ?_) hε N
  have hs := sum_descent_le (ϑ := fun k => c * h k * ‖P k (g (x k))‖ ^ 2) hℒ hg hP htr hG n
  have h1 := hinf n
  have h2 : G * ∑ k ∈ range n, c * h k * ‖P k (g (x k))‖ ^ 2 =
      ∑ k ∈ range n, (G * c) * (h k * ‖P k (g (x k))‖ ^ 2) := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have h3 : ∑ k ∈ range n, (1 / 4 + G * c) * (h k * ‖P k (g (x k))‖ ^ 2) ≤
      ∑ k ∈ range n, h k * (1 - β * h k / 2) * ‖P k (g (x k))‖ ^ 2 := by
    refine sum_le_sum fun k _ => ?_
    have hk : 1 / 4 + G * c ≤ 1 - β * h k / 2 := by linarith [hh1 k]
    have hnn : 0 ≤ h k * ‖P k (g (x k))‖ ^ 2 := mul_nonneg (hh0 k) (sq_nonneg _)
    calc (1 / 4 + G * c) * (h k * ‖P k (g (x k))‖ ^ 2)
        ≤ (1 - β * h k / 2) * (h k * ‖P k (g (x k))‖ ^ 2) := mul_le_mul_of_nonneg_right hk hnn
      _ = _ := by ring
  have h4 : ∑ k ∈ range n, (1 / 4 + G * c) * (h k * ‖P k (g (x k))‖ ^ 2) =
      1 / 4 * ∑ k ∈ range n, h k * ‖P k (g (x k))‖ ^ 2 +
        ∑ k ∈ range n, (G * c) * (h k * ‖P k (g (x k))‖ ^ 2) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  linarith

end Abstract

section Counting

end Counting

section Matrices

open scoped LeanDLRA.Frobenius
open EckartYoung WeylSingular Curvature MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n]

end Matrices

end LeanDLRA.OpenProblems.RankAdaptivity
