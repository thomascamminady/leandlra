import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Results of arXiv 2609.11811: Fermionic mode optimization via block-entropy gradients

This module formalizes the abstract core of the gradient step of the block entropy area
(BEA) mode optimization (`gradBEA`), of arXiv 2609.11811 (Werner, Friesecke, Menczer, Kapás,
Legeza), in the following two parts.

* `renyiEntropy`, `hasDerivAt_renyiEntropy` and `hasDerivAt_blockEntropy` (Eqs. (4), (10)): the
  Rényi entropy `S_μ = (1-μ)⁻¹ log Σ_α p_α^μ` of the Schmidt weights `p_α = λ_α²`, and its
  derivative along a differentiable family of Schmidt weights, `∂S_μ/∂θ = (1-μ)⁻¹ Σ_α μ p_α^{μ-1}
  ∂p_α/∂θ / Σ_α p_α^μ`; the block entropy `B_μ = Σ_i S_μ^{(i)}` is the sum over bonds, so its
  derivative is the sum over bonds (the gradient entering `H_dis` in Eq. (11)).  Stated for any
  real `μ` (the paper uses `0 < μ < ∞`, `μ = 1/2` in the numerics), and any finite index sets; at
  `μ = 1` both sides vanish trivially in Lean.  Positivity of the Schmidt weights is assumed,
  since `p^{μ-1}` is singular at `p = 0` for `μ < 1`.
* `exists_pos_step_decreases` (Eqs. (11)-(12) and the line search): for a differentiable cost
  `B` on the parameter vector `θ` of the rotation, the step `θ ↦ -τ g` with `g` the partial
  derivatives of `B` at `0` decreases `B` for some `τ > 0` whenever the gradient is nonzero. Here
  `B θ` stands for `B_μ` evaluated at `exp(Σ_{(kl)} θ_{kl} X^{(kl)})`; the composition with the
  rotation is not formalized, only the statement about `B` on parameters. The paper's `τ*` is a
  minimizer over `τ`, so it satisfies `B(τ*) ≤ B(τ)` for all `τ`, and in particular `B(τ*) < B(0)`
  whenever the gradient is nonzero. The disentangler `H_dis = -i Σ ∂B/∂θ T̂` (Eq. (11)) is a
  definition and is not formalized.

Not formalized: Eq. (9), the first-order variation of the Schmidt weights
`∂p_α/∂θ = 2 λ_α Re Ξ_{αα}`. It is a perturbation theorem for a simple eigenvalue of
`ρ_A = M M^T` (the Hellmann–Feynman-type step), and it needs non-degeneracy of the Schmidt
spectrum. Mathlib does not provide that eigenvalue-derivative theory, and it was left out for
time.
-/

open Set Filter Topology Finset

namespace LeanDLRA.Literature.P2609_11811

/-- Rényi entropy of the Schmidt weights `p_α = λ_α²`, as in Eq. (4) of arXiv 2609.11811:
`S_μ = (1-μ)⁻¹ log Σ_α λ_α^{2μ} = (1-μ)⁻¹ log Σ_α p_α^μ`. -/
noncomputable def renyiEntropy {α : Type*} [Fintype α] (μ : ℝ) (p : α → ℝ) : ℝ :=
  (1 - μ)⁻¹ * Real.log (∑ a, p a ^ μ)

/-- Eq. (10) of arXiv 2609.11811: the derivative of the Rényi entropy of the Schmidt weights
along a differentiable family `s ↦ p s` with positive weights at `t` is
`∂S_μ/∂θ = (1-μ)⁻¹ (Σ_α μ p_α^{μ-1} ∂p_α/∂θ) / (Σ_α p_α^μ)`. -/
theorem hasDerivAt_renyiEntropy {α : Type*} [Fintype α] [Nonempty α] (μ : ℝ)
    {p : ℝ → α → ℝ} {p' : α → ℝ} {t : ℝ}
    (hp : ∀ a, HasDerivAt (fun s => p s a) (p' a) t) (hpos : ∀ a, 0 < p t a) :
    HasDerivAt (fun s => renyiEntropy μ (p s))
      ((1 - μ)⁻¹ * ((∑ a, μ * p t a ^ (μ - 1) * p' a) / ∑ a, p t a ^ μ)) t := by
  have hsum : HasDerivAt (fun s => ∑ a, p s a ^ μ) (∑ a, μ * p t a ^ (μ - 1) * p' a) t := by
    apply HasDerivAt.fun_sum
    intro a _
    convert (hp a).rpow_const (p := μ) (Or.inl (hpos a).ne') using 1
    ring
  have hne : ∑ a, p t a ^ μ ≠ 0 :=
    (Finset.sum_pos (fun a _ => Real.rpow_pos_of_pos (hpos a) μ) Finset.univ_nonempty).ne'
  have hlog := (hsum.log hne).const_mul (1 - μ)⁻¹
  unfold renyiEntropy
  convert hlog using 1

/-- Eqs. (4), (10) and (11) of arXiv 2609.11811: the block entropy `B_μ = Σ_i S_μ^{(i)}`, summed
over bonds `i`, has derivative equal to the sum over bonds of the derivatives in Eq. (10), which
is the gradient that defines the disentangler. -/
theorem hasDerivAt_blockEntropy {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α] (μ : ℝ)
    {p : ℝ → ι → α → ℝ} {p' : ι → α → ℝ} {t : ℝ}
    (hp : ∀ i a, HasDerivAt (fun s => p s i a) (p' i a) t) (hpos : ∀ i a, 0 < p t i a) :
    HasDerivAt (fun s => ∑ i, renyiEntropy μ (p s i))
      (∑ i, (1 - μ)⁻¹ * ((∑ a, μ * p t i a ^ (μ - 1) * p' i a) / ∑ a, p t i a ^ μ)) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact hasDerivAt_renyiEntropy μ (fun a => hp i a) (fun a => hpos i a)

/-- Eqs. (11)-(12) and the line search of arXiv 2609.11811, in its abstract core: let `B` be a
differentiable cost on parameter vectors `θ` (in the paper, `B_μ` at the rotation
`exp(Σ θ_{kl} X^{(kl)})`), and let `g i` be its partial derivatives at `θ = 0`. If the gradient is
nonzero, then some step `θ ↦ -τ g` with `τ > 0` strictly decreases `B`. -/
theorem exists_pos_step_decreases {ι : Type*} [Finite ι] [DecidableEq ι] (B : (ι → ℝ) → ℝ)
    (hB : DifferentiableAt ℝ B 0) (hne : ∃ i, fderiv ℝ B 0 (Pi.single i 1) ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧
      B (fun i => -τ * fderiv ℝ B 0 (Pi.single i 1)) < B 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  set g : ι → ℝ := fun i => fderiv ℝ B 0 (Pi.single i 1) with hg_def
  set w : ι → ℝ := fun i => -g i with hw_def
  -- The derivative of the directional restriction `τ ↦ B (τ • w)` at `0` is `L w`.
  set L := fderiv ℝ B 0 with hL_def
  have hline : HasDerivAt (fun τ : ℝ => B (τ • w)) (L w) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have h2 := hB.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h2
  -- `L w = -Σ_i g_i²`, which is negative since the gradient is nonzero.
  have hLw : L w = -∑ i, g i ^ 2 := by
    have hsplit : w = ∑ i, (Pi.single i (w i) : ι → ℝ) := (Finset.univ_sum_single w).symm
    have hscal : ∀ i, Pi.single i (w i) = w i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      intro i
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    conv_lhs => rw [hsplit]
    rw [map_sum]
    simp only [hscal, map_smul, smul_eq_mul]
    simp [hw_def, hg_def, hL_def, Finset.sum_neg_distrib, sq]
  have hneg : L w < 0 := by
    rw [hLw]
    obtain ⟨i, hi⟩ := hne
    have hpos : 0 < ∑ j, g j ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨i, Finset.mem_univ _, by
          have : g i ≠ 0 := hi
          positivity⟩
    linarith
  -- A negative derivative gives a strictly smaller value for small positive `τ`.
  have hslope := hline.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (B ((0 + t) • w) - B ((0 : ℝ) • w)) < 0 :=
    hslope.eventually (gt_mem_nhds hneg)
  obtain ⟨t, htev, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht : (0 : ℝ) < t := htpos
  refine ⟨t, ht, ?_⟩
  have hlt : B ((0 + t) • w) - B ((0 : ℝ) • w) < 0 := by
    simp only [smul_eq_mul] at htev
    exact neg_of_mul_neg_right htev (inv_nonneg.mpr ht.le)
  have hfun : (fun i => -t * g i) = (0 + t) • w := by
    funext i
    simp [hw_def]
  rw [hfun]
  simp only [zero_smul] at hlt
  linarith

end LeanDLRA.Literature.P2609_11811
