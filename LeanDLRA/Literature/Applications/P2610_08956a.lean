import Mathlib

/-!
# Results of arXiv 2610.08956: Numerical Bogoliubov approximation of boson dynamics

Two results of the paper are formalized as their abstract cores on a complex inner product
space `H`. The paper works in `L²(Ω)` and `L²_s(Ω²)`, and Mathlib has no symmetric tensor
product on `L²(Ω^N)`, so the statements do not mention `φ`, `χ₂` or the tensorization (9)-(10).

* `orthogonality_restoration` (Sec. 4.6.1, "Preserving the orthogonality"). Let `W` be a
  subspace with an orthogonal projection (in the paper `W = φ(t)^⊥ ⊗ₛ φ(t)^⊥`, the set of `χ`
  with `∫ φ(t,y) χ(y,·) dy = 0`), `x` (the paper's `χ₂(0)`), and `κ = W.starProjection x`
  (the paper's `Proj ×ₛ Proj χ₂(0)`). If `κ ≠ 0`, then `κ / ‖κ‖` is a unit vector of `W` closest
  to `x`, and it is the only such minimizer. The paper's reduction of problem (56) to `κ` is
  proved here by Pythagoras. Not formalized: that `W` and `κ` are the symmetric-tensor
  objects of the paper.
* `phase_gauge_rate` (Lemma 1, "phase gauge"). For a differentiable curve `χ̃` and an angle
  `θ` with `χ = e^{-iθ} χ̃ / ‖χ̃‖` and `⟨χ, χ̇⟩ = 0`, one has
  `θ̇ = Im⟨χ̃, χ̃̇⟩ / ‖χ̃‖²`. This is the first equality in (26). Not formalized: the paper
  applies it to the tensorized functions `χ̃_{2j}` of (9), and the second expression in (26),
  which needs the symmetric tensor power.

Not formalized: the Dirac–Frenkel equations of Theorem 1 (they need `L²_s(Ω^N)`), the unitarity
and N-uniform bounds of Theorem 3 (they need the tensorized Hamiltonian), and the complex-symmetric
BUG integrator of Appendix C.

Core definitions: `LeanDLRA.IsOrthProj` is stated for real inner product spaces only, while the
paper's functions are complex. The complex orthogonal projection is therefore Mathlib's
`Submodule.starProjection`. No other core definition is used.
-/

namespace LeanDLRA.Literature.P2610_08956

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expansion of the square of a difference, with the real part of the complex inner product. -/
lemma norm_sub_sq_complex (a b : H) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * Complex.re (inner ℂ a b) + ‖b‖ ^ 2 :=
  norm_sub_sq (𝕜 := ℂ) a b

/-- **Orthogonality restoration (arXiv 2610.08956, Sec. 4.6.1).** Let `W` be a subspace of `H`
with an orthogonal projection, `x ∈ H`, and `κ = W.starProjection x ≠ 0`. Then `u = κ / ‖κ‖`
lies in `W`, has norm one, and minimizes `‖y - x‖` over the unit vectors `y ∈ W`; it is the
only minimizer. This is the paper's problem (56) with `W` abstract. -/
theorem orthogonality_restoration (W : Submodule ℂ H) [W.HasOrthogonalProjection] (x u : H)
    (hκ : W.starProjection x ≠ 0)
    (hu : u = ((‖W.starProjection x‖⁻¹ : ℝ) : ℂ) • W.starProjection x) :
    u ∈ W ∧ ‖u‖ = 1 ∧
      (∀ y ∈ W, ‖y‖ = 1 → ‖u - x‖ ≤ ‖y - x‖) ∧
      (∀ y ∈ W, ‖y‖ = 1 → ‖y - x‖ = ‖u - x‖ → y = u) := by
  set κ := W.starProjection x with hκdef
  have hκW : κ ∈ W := W.starProjection_apply_mem x
  have hn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  -- Pythagoras: for `w ∈ W`, `‖w - x‖² = ‖w - κ‖² + ‖κ - x‖²`.
  have hpy : ∀ w ∈ W, ‖w - x‖ ^ 2 = ‖w - κ‖ ^ 2 + ‖κ - x‖ ^ 2 := by
    intro w hw
    have hperp : inner ℂ (w - κ) (κ - x) = 0 := by
      have h1 : x - κ ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
      have h2 := Submodule.inner_right_of_mem_orthogonal (W.sub_mem hw hκW) h1
      rw [← neg_sub x κ, inner_neg_right, h2, neg_zero]
    have h3 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (w - κ) (κ - x) hperp
    have hw' : w - x = (w - κ) + (κ - x) := by abel
    rw [hw']
    simp only [sq]
    linarith [h3]
  have hUW : u ∈ W := by rw [hu]; exact W.smul_mem _ hκW
  have hκu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hn.le),
      inv_mul_cancel₀ hn.ne']
  have hc0 : (‖κ‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have huk : inner ℂ u κ = (‖κ‖ : ℂ) := by
    rw [hu, inner_smul_left, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal]
    push_cast
    field_simp
    rfl
  have hu_re : Complex.re (inner ℂ u κ) = ‖κ‖ := by rw [huk]; simp
  have hyk : ∀ y : H, ‖y‖ = 1 →
      ‖y - κ‖ ^ 2 = 1 - 2 * Complex.re (inner ℂ y κ) + ‖κ‖ ^ 2 := by
    intro y hy1
    rw [norm_sub_sq_complex, hy1]
    ring
  have huk2 : ‖u - κ‖ ^ 2 = 1 - 2 * ‖κ‖ + ‖κ‖ ^ 2 := by
    rw [norm_sub_sq_complex, hκu, hu_re]
    ring
  have hre : ∀ y : H, ‖y‖ = 1 → Complex.re (inner ℂ y κ) ≤ ‖κ‖ := by
    intro y hy1
    have h : Complex.re (inner ℂ y κ) ≤ ‖y‖ * ‖κ‖ :=
      re_inner_le_norm (𝕜 := ℂ) y κ
    rwa [hy1, one_mul] at h
  refine ⟨hUW, hκu, ?_, ?_⟩
  · intro y hy hy1
    have hsq : ‖u - x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
      rw [hpy u hUW, hpy y hy]
      have := hre y hy1
      linarith [hyk y hy1, huk2]
    nlinarith [norm_nonneg (u - x), norm_nonneg (y - x)]
  · intro y hy hy1 heq
    have hsq2 : ‖y - x‖ ^ 2 = ‖u - x‖ ^ 2 := by rw [heq]
    rw [hpy y hy, hpy u hUW] at hsq2
    have hry : Complex.re (inner ℂ y κ) = ‖κ‖ := by
      have hd : ‖y - κ‖ ^ 2 = ‖u - κ‖ ^ 2 := by linarith
      rw [hyk y hy1, huk2] at hd
      linarith
    have hyu : Complex.re (inner ℂ y u) = 1 := by
      rw [hu, inner_smul_right, Complex.re_ofReal_mul, hry, inv_mul_cancel₀ hn.ne']
    have h0 : ‖y - u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_complex, hy1, hκu, hyu]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

/-- Non-vacuity: for `W = ⊤` and `x = 3` the hypothesis `κ ≠ 0` holds, and the normalized vector
has norm one. -/
example (u : ℂ)
    (hu : u = ((‖(⊤ : Submodule ℂ ℂ).starProjection (3 : ℂ)‖⁻¹ : ℝ) : ℂ) •
      (⊤ : Submodule ℂ ℂ).starProjection (3 : ℂ)) :
    ‖u‖ = 1 :=
  (orthogonality_restoration ⊤ 3 u
    (by rw [Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top]; norm_num) hu).2.1

/-- The normalized excitation `χ = e^{-iθ} χ̃ / ‖χ̃‖` of the paper's (10), for a curve `χ̃`. -/
noncomputable def gaugeCurve (ct : ℝ → H) (θ : ℝ → ℝ) (s : ℝ) : H :=
  Complex.exp (-(θ s : ℂ) * Complex.I) • (((‖ct s‖⁻¹ : ℝ) : ℂ) • ct s)

/-- **Phase gauge (arXiv 2610.08956, Lemma 1, first equality of (26)).** If
`χ = e^{-iθ} χ̃ / ‖χ̃‖` at time `t` with `χ̃(t) ≠ 0`, and the orthogonality `⟨χ, χ̇⟩ = 0`
holds at `t`, then `θ̇(t) = Im⟨χ̃, χ̃̇⟩ / ‖χ̃‖²`. The paper's `χ̃` is the tensorized function
of (9); this is the abstract version for any differentiable curve `χ̃`. -/
theorem phase_gauge_rate (ct : ℝ → H) (θ : ℝ → ℝ) (t : ℝ)
    (hct : DifferentiableAt ℝ ct t) (hθ : DifferentiableAt ℝ θ t) (hne : ct t ≠ 0)
    (horth : inner ℂ (gaugeCurve ct θ t) (deriv (gaugeCurve ct θ) t) = 0) :
    deriv θ t = (inner ℂ (ct t) (deriv ct t)).im / ‖ct t‖ ^ 2 := by
  have hc : HasDerivAt ct (deriv ct t) t := hct.hasDerivAt
  have hθ' : HasDerivAt θ (deriv θ t) t := hθ.hasDerivAt
  have hn0 : ‖ct t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  -- derivative of the real normalization `‖ct s‖⁻¹`; needed for the real-valued norm
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hsqrt := (hc.norm_sq).sqrt (pow_ne_zero 2 hn0)
  have hfun : (fun s => Real.sqrt (‖ct s‖ ^ 2)) = fun s => ‖ct s‖ :=
    funext fun s => Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hsqrt
  obtain ⟨ρ', hρ⟩ : ∃ ρ' : ℝ, HasDerivAt (fun s => ‖ct s‖⁻¹) ρ' t := ⟨_, hsqrt.inv hn0⟩
  have h1 : HasDerivAt (fun s => -((θ s : ℝ) : ℂ) * Complex.I)
      (-((deriv θ t : ℝ) : ℂ) * Complex.I) t :=
    (hθ'.ofReal_comp.neg).mul_const Complex.I
  have hE := h1.cexp
  have hR : HasDerivAt (fun s => ((‖ct s‖⁻¹ : ℝ) : ℂ)) (ρ' : ℂ) t := hρ.ofReal_comp
  have hS := hR.smul hc
  have hG : HasDerivAt (gaugeCurve ct θ)
      (Complex.exp (-(θ t : ℂ) * Complex.I) •
          (((‖ct t‖⁻¹ : ℝ) : ℂ) • deriv ct t + (ρ' : ℂ) • ct t) +
        (Complex.exp (-(θ t : ℂ) * Complex.I) *
          (-((deriv θ t : ℝ) : ℂ) * Complex.I)) • (((‖ct t‖⁻¹ : ℝ) : ℂ) • ct t)) t :=
    hE.smul hS
  rw [hG.deriv] at horth
  simp only [gaugeCurve] at horth
  set E := Complex.exp (-(θ t : ℂ) * Complex.I) with hEdef
  have hz : starRingEnd ℂ (-(θ t : ℂ) * Complex.I) + (-(θ t : ℂ) * Complex.I) = 0 := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hEE : starRingEnd ℂ E * E = 1 := by
    rw [hEdef, ← Complex.exp_conj, ← Complex.exp_add, hz, Complex.exp_zero]
  simp only [inner_add_right, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, Complex.conj_ofReal] at horth
  have hr : (‖ct t‖⁻¹) ^ 2 * ‖ct t‖ ^ 2 = 1 := by
    field_simp
  have hn2 : ((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * ((‖ct t‖ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast hr
  have hQ : (-((deriv θ t : ℝ) : ℂ) * Complex.I) *
      (((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * ((‖ct t‖ : ℝ) : ℂ) ^ 2) +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) * (ρ' : ℂ) * ((‖ct t‖ : ℝ) : ℂ) ^ 2 +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * inner ℂ (ct t) (deriv ct t) = 0 := by
    linear_combination horth - ((-((deriv θ t : ℝ) : ℂ) * Complex.I) *
      (((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * ((‖ct t‖ : ℝ) : ℂ) ^ 2) +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) * (ρ' : ℂ) * ((‖ct t‖ : ℝ) : ℂ) ^ 2 +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * inner ℂ (ct t) (deriv ct t)) * hEE
  have hQ2 : -((deriv θ t : ℝ) : ℂ) * Complex.I +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) * (ρ' : ℂ) * ((‖ct t‖ : ℝ) : ℂ) ^ 2 +
      ((‖ct t‖⁻¹ : ℝ) : ℂ) ^ 2 * inner ℂ (ct t) (deriv ct t) = 0 := by
    linear_combination hQ + ((deriv θ t : ℝ) : ℂ) * Complex.I * hn2
  have hQ3 : -((deriv θ t : ℝ) : ℂ) * Complex.I +
      ((‖ct t‖⁻¹ * ρ' * ‖ct t‖ ^ 2 : ℝ) : ℂ) +
      (((‖ct t‖⁻¹) ^ 2 : ℝ) : ℂ) * inner ℂ (ct t) (deriv ct t) = 0 := by
    push_cast at hQ2 ⊢
    linear_combination hQ2
  have him := congrArg Complex.im hQ3
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_im, Complex.neg_re, Complex.I_re, Complex.I_im, Complex.zero_im] at him
  rw [eq_div_iff (pow_ne_zero 2 hn0)]
  linear_combination (-(‖ct t‖ ^ 2)) * him + (inner ℂ (ct t) (deriv ct t)).im * hr

/-- Non-vacuity: the constant curve `χ̃ = 1` with `θ = 0` satisfies the hypotheses at `t = 0`. -/
example : deriv (fun _ : ℝ => (0 : ℝ)) 0 =
    (inner ℂ ((fun _ : ℝ => (1 : ℂ)) 0) (deriv (fun _ : ℝ => (1 : ℂ)) 0)).im /
      ‖(1 : ℂ)‖ ^ 2 := by
  apply phase_gauge_rate (H := ℂ) (fun _ => (1 : ℂ)) (fun _ => (0 : ℝ)) 0
    (differentiableAt_const _) (differentiableAt_const _) one_ne_zero
  have h : gaugeCurve (fun _ : ℝ => (1 : ℂ)) (fun _ : ℝ => (0 : ℝ)) = fun _ => 1 := by
    funext s
    simp [gaugeCurve]
  rw [h]
  simp

end LeanDLRA.Literature.P2610_08956
