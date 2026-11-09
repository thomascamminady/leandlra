import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.OpenProblems.RankAdaptivity.Maine
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Results of arXiv 2609.11811: Fermionic mode optimization via block-entropy gradients

This module formalizes the finite-dimensional linear-algebra and calculus content of the
gradient-based block entropy area (BEA) mode optimization (`gradBEA`) of arXiv 2609.11811
(Werner, Friesecke, Menczer, Kapás, Legeza).  The paper is a physics letter: it states no
numbered theorems, so each result below is a displayed equation or a sentence of the text.
A bipartite state `|Ψ⟩ = Σ_{ij} M_{ij} |i⟩_A |j⟩_B` is represented by its real coefficient
matrix `M` (the paper keeps everything real, `U ∈ SO(N)`, for time-reversal symmetric models).
The Fock space, the Jordan–Wigner signs, the MPS and the fermionic operators `T̂_{(kl)}` are not
formalized: a mode rotation enters only through the derivative `Ξ` of the coefficient matrix
(`|Ξ⟩ = T̂_{(kl)} |Ψ₀⟩` in the paper).

## Main results

* Schmidt decomposition and truncation (Eq. (3), text after it), via the core Eckart–Young
  module `LeanDLRA.EckartYoung`: `leftSchmidtVector` (`a_α = σ_α⁻¹ M e_α`, `e_α` the core
  `rightSingularVectors`), `toEuclideanLin_eq_sum_schmidt` (`M = Σ_α σ_α a_α e_αᵀ`),
  `orthonormal_leftSchmidtVector`, `sum_sq_singularValues_eq_one` (`Σ λ_α² = 1`),
  `truncationError`, `truncation_optimal` (keeping the `D` largest Schmidt values is optimal with
  squared error `ε_Tr = Σ_{α > D} λ_α²`) and `truncationError_eq_one_sub`.
* Chain, not in the paper: `truncationError_le_renyiEntropy`, `ε_Tr ≤ μ/(1-μ) e^{(1-μ)S_μ/μ}
  D^{1-1/μ}` for `0 < μ < 1` (from OP-RA-39 (b), `renyi_tail_le`), which is why minimizing the
  Rényi entropies (instead of the ill-posed truncation errors) controls the truncation error.
* Reduced density matrix (Eqs. (7), (8)): `reducedDensity M = M Mᵀ` (`reducedDensity_apply`:
  the partial trace over `B`), `reducedDensity_leftSchmidtVector` (`ρ_A a_α = λ_α² a_α`) and
  `hasDerivAt_reducedDensity` (`ρ_A' = Ξ Mᵀ + M Ξᵀ`, Eq. (8)) with its Schmidt-basis entries
  `inner_reducedDensity_deriv` (`λ_α Ξ_{βα} + Ξ_{αβ} λ_β`).
* Eq. (9), first-order non-degenerate perturbation theory:
  `hasDerivAt_eigenvalue_of_simple` (Hellmann–Feynman for a simple eigenvalue of a
  differentiable family of symmetric operators on a finite-dimensional real inner product space;
  differentiability of the eigenvalue is *derived*, only continuity is assumed), and its Schmidt
  form `hasDerivAt_schmidtWeight` (`∂p_α/∂θ = 2 λ_α Ξ_{αα}`), also at a core singular triple
  (`hasDerivAt_schmidtWeight_singular`).  `hasDerivAt_schmidtWeight_of_skew_left/right`:
  rotations inside `A` or inside `B` do not change the Schmidt weights to first order (the
  paper's remark that only rotations between the two subsystems give nonzero derivatives).
* Eqs. (4), (10): `renyiEntropy`, `hasDerivAt_renyiEntropy`, `hasDerivAt_blockEntropy`, and the
  chained formula `hasDerivAt_renyiEntropy_schmidt` (Eq. (9) inserted into Eq. (10)).
* Eqs. (5), (12): `rotGen` (`X^{(kl)}`), `rotGenSum` (`Σ_{k<l} θ_{kl} X^{(kl)}`),
  `transpose_rotGenSum`, `rotGenSum_apply(_of_lt)`, `rotGenSum_of_skew` (the generators span the
  antisymmetric matrices), `transpose_mul_one_add_of_skew` (Eq. (5) is orthogonal to first
  order), `exp_mem_specialOrthogonalGroup`, `exp_neg_smul_rotGenSum_mem` (the update `U_n` of
  Eq. (12) lies in `SO(N)`).
* Steepest descent (Eqs. (11)-(12), Fig. 1a): `exists_pos_step_decreases` (abstract),
  `exists_rotation_decreases` (the step `U = exp(-τ Σ ∂B/∂θ_{kl} X^{(kl)}) ∈ SO(N)` strictly
  decreases a cost whose pull-back to the angles has nonzero gradient) and
  `lineSearch_lt` (the line-search minimizer `τ*` does too).

## Deviations from the paper

* Real setting throughout (the paper's own choice for its models), so `Re Ξ_{αα} = Ξ_{αα}`.
* Eq. (9): the eigenvalue branch is given as data, a unit eigenvector `a(θ)` of `ρ_A(θ)` with
  eigenvalue `p(θ)` for `θ` near `t`, with `p` continuous at `t` (this identifies the branch);
  the existence of such a branch is not formalized.  Simplicity of `p(t)` is the paper's
  non-degeneracy assumption (footnote [52]); the degenerate case is
  `LeanDLRA.OpenProblems.TensorNetworks.hasDerivAt_trace_cfc` (OP-TN-32).
* Eq. (10) assumes positive Schmidt weights (`p^{μ-1}` is singular at `0` for `μ < 1`).
* The Schmidt states `|α⟩_B` are the core right singular vectors (eigenvectors of `MᵀM`) and
  `|α⟩_A = λ_α⁻¹ M |α⟩_B`; the paper's Schmidt values are the singular values of `M`.
* `exists_rotation_decreases` uses the exponential parametrization `θ ↦ exp(Σ θ_{kl} X^{(kl)})`
  of Eq. (12) for the gradient; the paper differentiates along the linear parametrization of
  Eq. (5), which has the same first-order term (the equality of the two gradients is not
  formalized).

## Not formalized

The Fock-space objects (Eqs. (1), (2), (6), the disentangler `Ĥ_dis` of Eq. (11) and its MPO
bond dimension `O(N)`), the PS-TDVP time evolution and the Polak–Ribière–Polyak correction need
fermionic Fock space and tensor-train (MPS/MPO) infrastructure that the library does not have;
the numerical results are not mathematical statements.

Core definitions used: `Matrix.toEuclideanLin`, the Frobenius normed space
(`LeanDLRA.Frobenius`), `LeanDLRA.EckartYoung.rightSingularVectors` and `truncation`,
`Matrix.specialOrthogonalGroup`.  Local definitions: `renyiEntropy`, `truncationError`,
`leftSchmidtVector`, `reducedDensity`, `rotGen`, `rotGenSum`, `ModePair`, `rotCost`.  The core
has no Rényi entropy, Schmidt vector, reduced density matrix or rotation generator;
`leftSchmidtVector` and `truncationError` are built from the core singular value data, and
`toEuclideanLin_reducedDensity` identifies `reducedDensity M` with the operator `T T†`.
-/

open Set Filter Topology Finset Asymptotics
open scoped RealInnerProductSpace

namespace LeanDLRA.Literature.P2609_11811

/-- Rényi entropy of the Schmidt weights `p_α = λ_α²`, as in Eq. (4) of arXiv 2609.11811:
`S_μ = (1-μ)⁻¹ log Σ_α λ_α^{2μ} = (1-μ)⁻¹ log Σ_α p_α^μ`. -/
noncomputable def renyiEntropy {α : Type*} [Fintype α] (μ : ℝ) (p : α → ℝ) : ℝ :=
  (1 - μ)⁻¹ * Real.log (∑ a, p a ^ μ)

/-- Eq. (10) of arXiv 2609.11811: the derivative of the Rényi entropy of the Schmidt weights
along a differentiable family `s ↦ p s` with positive weights at `t` is
`∂S_μ/∂θ = (1-μ)⁻¹ (Σ_α μ p_α^{μ-1} ∂p_α/∂θ) / (Σ_α p_α^μ)`.  Stated for every real `μ` (the
paper has `0 < μ < ∞`, `μ ≠ 1`; at `μ = 1` both sides are `0` in Lean); positivity of the
weights is an added hypothesis, needed since `p^{μ-1}` is singular at `0` for `μ < 1`. -/
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
is the gradient that defines the disentangler.  The Schmidt index set `α i` may depend on the
bond `i` (the Schmidt rank varies along an MPS); positivity of the weights as in
`hasDerivAt_renyiEntropy`. -/
theorem hasDerivAt_blockEntropy {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)]
    [∀ i, Nonempty (α i)] (μ : ℝ) {p : ℝ → (i : ι) → α i → ℝ} {p' : (i : ι) → α i → ℝ} {t : ℝ}
    (hp : ∀ i a, HasDerivAt (fun s => p s i a) (p' i a) t) (hpos : ∀ i a, 0 < p t i a) :
    HasDerivAt (fun s => ∑ i, renyiEntropy μ (p s i))
      (∑ i, (1 - μ)⁻¹ * ((∑ a, μ * p t i a ^ (μ - 1) * p' i a) / ∑ a, p t i a ^ μ)) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact hasDerivAt_renyiEntropy μ (fun a => hp i a) (fun a => hpos i a)

/-- Eqs. (11)-(12) and the line search of arXiv 2609.11811, in its abstract core: let `B` be a
differentiable cost on parameter vectors `θ` (in the paper, `B_μ` at the rotation
`exp(Σ θ_{kl} X^{(kl)})`, see `exists_rotation_decreases`), and let `g i` be its partial
derivatives at `θ = 0`. If the gradient is nonzero, then some step `θ ↦ -τ g` with `τ > 0`
strictly decreases `B`. -/
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

/-- The line search of arXiv 2609.11811 (Fig. 1a, Fig. 2a): `B_μ` is minimized along the
search line at some `τ* ≥ 0`.  Any such minimizer strictly decreases `B` when the gradient is
nonzero.  The minimizer is a hypothesis (the paper locates it numerically); its existence is not
claimed. -/
theorem lineSearch_lt {ι : Type*} [Finite ι] [DecidableEq ι] (B : (ι → ℝ) → ℝ)
    (hB : DifferentiableAt ℝ B 0) (hne : ∃ i, fderiv ℝ B 0 (Pi.single i 1) ≠ 0) {τs : ℝ}
    (hmin : ∀ τ, 0 ≤ τ → B (fun i => -τs * fderiv ℝ B 0 (Pi.single i 1)) ≤
      B (fun i => -τ * fderiv ℝ B 0 (Pi.single i 1))) :
    B (fun i => -τs * fderiv ℝ B 0 (Pi.single i 1)) < B 0 := by
  obtain ⟨τ, hτ, hlt⟩ := exists_pos_step_decreases B hB hne
  exact (hmin τ hτ.le).trans_lt hlt

/-! ### First-order perturbation of a simple eigenvalue (Eq. (9)) -/

section HellmannFeynman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Spectral gap of a simple eigenvalue: if the kernel of `A` is spanned by the unit vector `v`,
then `A` is bounded below on the orthogonal complement of `v`. -/
theorem exists_gap_of_ker {A : E →L[ℝ] E} {v : E} (hv : ‖v‖ = 1)
    (hker : ∀ u, A u = 0 → ∃ c : ℝ, u = c • v) :
    ∃ δ > 0, ∀ w, ⟪v, w⟫ = 0 → δ * ‖w‖ ≤ ‖A w‖ := by
  set K : Submodule ℝ E := (ℝ ∙ v)ᗮ
  set f : K →ₗ[ℝ] E := (A : E →ₗ[ℝ] E) ∘ₗ K.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨c, hc⟩ := hker w hw
    have h0 : ⟪v, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hv] at h0
    have hc0 : c = 0 := by simpa using h0
    ext
    simp [hc, hc0]
  obtain ⟨C, hCpos, hC⟩ := f.injective_iff_antilipschitz.mp hinj
  refine ⟨(C : ℝ)⁻¹, by positivity, fun w hw => ?_⟩
  have hwK : w ∈ K := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw
  have h := hC.le_mul_dist ⟨w, hwK⟩ 0
  simp only [dist_zero_right, map_zero] at h
  have h' : ‖w‖ ≤ C * ‖A w‖ := by simpa [hf] using h
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hCpos
  rw [inv_mul_le_iff₀ hC0]
  exact h'

/-- Eq. (9) of arXiv 2609.11811 in its abstract form (first-order non-degenerate perturbation
theory, Hellmann–Feynman): let `ρ θ` be symmetric operators on a finite-dimensional real inner
product space, differentiable at `t` with derivative `ρ'`, and let `p θ` be an eigenvalue of
`ρ θ` with unit eigenvector `v θ` for `θ` near `t`.  If `p` is continuous at `t` and `p t` is a
simple eigenvalue of `ρ t`, then `p` is differentiable at `t` with `p'(t) = ⟪v t, ρ' (v t)⟫`.
No differentiability or continuity of the eigenvectors is assumed. -/
theorem hasDerivAt_eigenvalue_of_simple {ρ : ℝ → E →L[ℝ] E} {ρ' : E →L[ℝ] E} {t : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hsymm : ∀ᶠ θ in 𝓝 t, (ρ θ : E →ₗ[ℝ] E).IsSymmetric)
    {p : ℝ → ℝ} {v : ℝ → E} (hv : ∀ᶠ θ in 𝓝 t, ‖v θ‖ = 1 ∧ ρ θ (v θ) = p θ • v θ)
    (hp : ContinuousAt p t) (hsimple : ∀ u, ρ t u = p t • u → ∃ c : ℝ, u = c • v t) :
    HasDerivAt p ⟪v t, ρ' (v t)⟫ t := by
  obtain ⟨hv1, hvt⟩ := hv.self_of_nhds
  set v₀ := v t with hv₀
  set A : E →L[ℝ] E := ρ t - p t • ContinuousLinearMap.id ℝ E with hA
  have hker : ∀ u, A u = 0 → ∃ c : ℝ, u = c • v₀ := by
    intro u hu
    apply hsimple
    have : ρ t u - p t • u = 0 := by simpa [hA] using hu
    exact sub_eq_zero.mp this
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_of_ker hv1 hker
  -- The Rayleigh quotient at the fixed vector `v₀` carries the derivative.
  set q : ℝ → ℝ := fun θ => ⟪v₀, ρ θ v₀⟫ with hq_def
  have hq : HasDerivAt q ⟪v₀, ρ' v₀⟫ t := by
    have h1 : HasDerivAt (fun θ => ρ θ v₀) (ρ' v₀) t := by
      simpa using hρ.clm_apply (hasDerivAt_const t v₀)
    simpa using (hasDerivAt_const t v₀).inner ℝ h1
  have hpq : p t = q t := by
    simp [hq_def, hvt, real_inner_smul_right, hv1]
  set Δ : ℝ → E →L[ℝ] E := fun θ => ρ θ - ρ t with hΔ
  set η : ℝ → ℝ := fun θ => ‖Δ θ‖ + |p θ - p t| with hη_def
  have hη : Tendsto η (𝓝 t) (𝓝 0) := by
    have h1 : Tendsto (fun θ => ‖ρ θ - ρ t‖) (𝓝 t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hρ.continuousAt.tendsto
    have h2 : Tendsto (fun θ => |p θ - p t|) (𝓝 t) (𝓝 0) := by
      simpa [Real.norm_eq_abs] using tendsto_iff_norm_sub_tendsto_zero.mp hp.tendsto
    simpa [hη_def, hΔ] using h1.add h2
  have hsmall : ∀ᶠ θ in 𝓝 t, η θ ≤ δ / 2 := hη.eventually (ge_mem_nhds (by linarith))
  -- Key estimate: `|p θ - q θ| ≤ (2/δ) ‖ρ θ - ρ t‖ η θ`, from the gap on `v₀ᗮ`.
  have hbound : ∀ᶠ θ in 𝓝 t, |p θ - q θ| ≤ (2 / δ) * (‖Δ θ‖ * η θ) := by
    filter_upwards [hv, hsymm, hsmall] with θ ⟨hvθ1, hvθ⟩ hsθ hηθ
    set c := ⟪v₀, v θ⟫ with hc
    set w := v θ - c • v₀ with hw
    have hw0 : ⟪v₀, w⟫ = 0 := by
      rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv1, ← hc]
      ring
    have hAv0 : A v₀ = 0 := by simp [hA, hvt]
    have hAw : A w = (p θ - p t) • v θ - Δ θ (v θ) := by
      have : A w = A (v θ) := by simp [hw, map_sub, map_smul, hAv0]
      rw [this]
      simp only [hA, hΔ, sub_apply, smul_apply, ContinuousLinearMap.id_apply, hvθ, sub_smul]
      abel
    have hAwle : ‖A w‖ ≤ η θ := by
      rw [hAw]
      calc ‖(p θ - p t) • v θ - Δ θ (v θ)‖ ≤ ‖(p θ - p t) • v θ‖ + ‖Δ θ (v θ)‖ :=
            norm_sub_le _ _
        _ ≤ |p θ - p t| * 1 + ‖Δ θ‖ * 1 := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs, hvθ1]
            · rw [← hvθ1]; exact (Δ θ).le_opNorm _
        _ = η θ := by simp [hη_def]; ring
    have hwle : ‖w‖ ≤ η θ / δ := by
      rw [le_div_iff₀ hδ, mul_comm]
      exact (hgap w hw0).trans hAwle
    have hwhalf : ‖w‖ ≤ 1 / 2 := by
      calc ‖w‖ ≤ η θ / δ := hwle
        _ ≤ (δ / 2) / δ := by gcongr
        _ = 1 / 2 := by field_simp
    have hpyth : ‖v θ‖ * ‖v θ‖ = ‖c • v₀‖ * ‖c • v₀‖ + ‖w‖ * ‖w‖ := by
      have hdec : v θ = c • v₀ + w := by simp [hw]
      have horth : ⟪c • v₀, w⟫ = 0 := by rw [real_inner_smul_left, hw0, mul_zero]
      rw [hdec]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    have hcv : ‖c • v₀‖ = |c| := by rw [norm_smul, hv1, Real.norm_eq_abs, mul_one]
    rw [hvθ1, hcv] at hpyth
    have hc2 : 1 / 2 ≤ |c| := by
      have hw2 : ‖w‖ * ‖w‖ ≤ 1 / 4 := by
        have := norm_nonneg w
        nlinarith
      have habs := abs_nonneg c
      nlinarith
    have hid : c * (p θ - q θ) = ⟪Δ θ v₀, w⟫ := by
      have e1 : ⟪ρ θ v₀, v θ⟫ = p θ * c := by
        have hs := hsθ v₀ (v θ)
        simp only [ContinuousLinearMap.coe_coe] at hs
        rw [hs, hvθ, real_inner_smul_right]
      have e2 : ⟪ρ t v₀, v θ⟫ = p t * c := by
        rw [hvt, real_inner_smul_left]
      have e3 : q θ = q t + ⟪Δ θ v₀, v₀⟫ := by
        simp only [hq_def, hΔ, sub_apply, inner_sub_left]
        rw [real_inner_comm v₀ (ρ θ v₀), real_inner_comm v₀ (ρ t v₀)]
        ring
      rw [e3, ← hpq]
      simp only [hw, inner_sub_right, real_inner_smul_right, hΔ, sub_apply, inner_sub_left, e1,
        e2]
      ring
    have hle : |c| * |p θ - q θ| ≤ ‖Δ θ‖ * (η θ / δ) := by
      rw [← abs_mul, hid]
      calc |⟪Δ θ v₀, w⟫| ≤ ‖Δ θ v₀‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖Δ θ‖ * ‖w‖ := by
            gcongr
            calc ‖Δ θ v₀‖ ≤ ‖Δ θ‖ * ‖v₀‖ := (Δ θ).le_opNorm _
              _ = ‖Δ θ‖ := by rw [hv1, mul_one]
        _ ≤ ‖Δ θ‖ * (η θ / δ) := by gcongr
    have hpq0 := abs_nonneg (p θ - q θ)
    calc |p θ - q θ| ≤ 2 * (|c| * |p θ - q θ|) := by nlinarith
      _ ≤ 2 * (‖Δ θ‖ * (η θ / δ)) := by gcongr
      _ = (2 / δ) * (‖Δ θ‖ * η θ) := by field_simp
  -- `‖ρ θ - ρ t‖ = O(θ - t)` and `η θ → 0` turn the estimate into `p - q = o(θ - t)`.
  have hΔO : (fun θ => ‖Δ θ‖) =O[𝓝 t] (fun θ => θ - t) := hρ.isBigO_sub.norm_left
  have hηo : η =o[𝓝 t] (fun _ => (1 : ℝ)) := isLittleO_one_iff ℝ |>.mpr hη
  have hprod : (fun θ => ‖Δ θ‖ * η θ) =o[𝓝 t] (fun θ => (θ - t) * 1) :=
    hΔO.mul_isLittleO hηo
  have hO : (fun θ => p θ - q θ) =O[𝓝 t] (fun θ => ‖Δ θ‖ * η θ) := by
    refine IsBigO.of_bound (2 / δ) ?_
    filter_upwards [hbound] with θ hθ
    have h0 : 0 ≤ ‖Δ θ‖ * η θ := by
      have : 0 ≤ η θ := by simp only [hη_def]; positivity
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
    exact hθ
  have hlo : (fun θ => p θ - q θ) =o[𝓝 t] (fun θ => θ - t) := by
    simpa using hO.trans_isLittleO hprod
  have hr : HasDerivAt (fun θ => p θ - q θ) 0 t := by
    rw [hasDerivAt_iff_isLittleO]
    simpa [hpq] using hlo
  have := hq.add hr
  simp only [add_zero] at this
  convert this using 1
  funext θ
  simp only [Pi.add_apply]
  ring

/-- Non-vacuity of `hasDerivAt_eigenvalue_of_simple`: the family `ρ θ = θ • id` on `ℝ`. -/
example : HasDerivAt (fun θ : ℝ => θ) 1 0 := by
  have h := hasDerivAt_eigenvalue_of_simple (E := ℝ) (ρ := fun θ => θ • ContinuousLinearMap.id ℝ ℝ)
    (ρ' := ContinuousLinearMap.id ℝ ℝ) (t := 0) (p := fun θ => θ) (v := fun _ => 1)
    (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ContinuousLinearMap.id ℝ ℝ))
    (Eventually.of_forall fun θ x y => by simp [mul_comm, mul_left_comm])
    (Eventually.of_forall fun θ => by simp) continuousAt_id
    (fun u _ => ⟨u, by simp⟩)
  simpa using h

end HellmannFeynman

/-! ### Schmidt decomposition and truncation (Eq. (3)) -/

section MatrixOperators

open Matrix

/-- `⟪Aᵀ x, y⟫ = ⟪x, A y⟫` for real matrices acting on Euclidean spaces. -/
theorem inner_toEuclideanLin_transpose {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]
    [DecidableEq l] (A : Matrix m l ℝ) (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ l) :
    ⟪toEuclideanLin Aᵀ x, y⟫ = ⟪x, toEuclideanLin A y⟫ := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left]

/-- `⟪A x, y⟫ = ⟪x, Aᵀ y⟫` for real matrices acting on Euclidean spaces. -/
theorem inner_toEuclideanLin_left {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]
    [DecidableEq l] (A : Matrix m l ℝ) (x : EuclideanSpace ℝ l) (y : EuclideanSpace ℝ m) :
    ⟪toEuclideanLin A x, y⟫ = ⟪x, toEuclideanLin Aᵀ y⟫ := by
  rw [real_inner_comm, ← inner_toEuclideanLin_transpose, real_inner_comm]

/-- `(A B) x = A (B x)` for real matrices acting on Euclidean spaces. -/
theorem toEuclideanLin_mul_apply {m k l : Type*} [Fintype k] [Fintype l] [DecidableEq l]
    [DecidableEq k] (A : Matrix m l ℝ) (B : Matrix l k ℝ) (x : EuclideanSpace ℝ k) :
    toEuclideanLin (A * B) x = toEuclideanLin A (toEuclideanLin B x) := by
  rw [toLpLin_mul_same, LinearMap.comp_apply]

/-- A skew-symmetric matrix has `⟪x, K x⟫ = 0`. -/
theorem inner_toEuclideanLin_self_of_skew {l : Type*} [Fintype l] [DecidableEq l]
    {K : Matrix l l ℝ} (hK : Kᵀ = -K) (x : EuclideanSpace ℝ l) :
    ⟪x, toEuclideanLin K x⟫ = 0 := by
  have h1 := inner_toEuclideanLin_transpose K x x
  rw [hK, map_neg, LinearMap.neg_apply, inner_neg_left, real_inner_comm] at h1
  linarith

end MatrixOperators

section Schmidt

open Matrix EckartYoung Module

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The left Schmidt vectors of Eq. (3) of arXiv 2609.11811: `a_α = σ_α⁻¹ M e_α` (and `0` when
`σ_α = 0`), where `e_α` are the core right singular vectors
`LeanDLRA.EckartYoung.rightSingularVectors` and `σ_α = λ_α` the singular (Schmidt) values. -/
noncomputable def leftSchmidtVector (M : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) : EuclideanSpace ℝ m :=
  ((toEuclideanLin M).singularValues i)⁻¹ • toEuclideanLin M (rightSingularVectors M i)

/-- Schmidt pair, first half: `M e_α = λ_α a_α`. -/
theorem toEuclideanLin_rightSingularVectors (M : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    toEuclideanLin M (rightSingularVectors M i) =
      (toEuclideanLin M).singularValues i • leftSchmidtVector M i := by
  by_cases hσ : (toEuclideanLin M).singularValues i = 0
  · have h := sq_norm_toEuclideanLin_rightSingularVectors M i
    rw [hσ] at h
    have h0 : toEuclideanLin M (rightSingularVectors M i) = 0 := by simpa using h
    rw [h0, hσ, zero_smul]
  · rw [leftSchmidtVector, smul_inv_smul₀ hσ]

/-- Schmidt pair, second half: `Mᵀ a_α = λ_α e_α`. -/
theorem transpose_leftSchmidtVector [DecidableEq m] (M : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    toEuclideanLin Mᵀ (leftSchmidtVector M i) =
      (toEuclideanLin M).singularValues i • rightSingularVectors M i := by
  have hadj : toEuclideanLin Mᵀ = LinearMap.adjoint (toEuclideanLin M) := by
    rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_eq_adjoint]
  rw [leftSchmidtVector, map_smul, hadj, adjoint_toEuclideanLin_rightSingularVectors, smul_smul]
  by_cases hσ : (toEuclideanLin M).singularValues i = 0
  · simp [hσ]
  · congr 1
    field_simp

/-- The left Schmidt vectors of nonzero Schmidt values are unit vectors. -/
theorem norm_leftSchmidtVector (M : Matrix m n ℝ) (i : Fin (finrank ℝ (EuclideanSpace ℝ n)))
    (hσ : (toEuclideanLin M).singularValues i ≠ 0) : ‖leftSchmidtVector M i‖ = 1 := by
  have h0 := (toEuclideanLin M).singularValues_nonneg i
  have hn : ‖toEuclideanLin M (rightSingularVectors M i)‖ =
      (toEuclideanLin M).singularValues i :=
    (pow_left_inj₀ (norm_nonneg _) h0 two_ne_zero).mp
      (sq_norm_toEuclideanLin_rightSingularVectors M i)
  rw [leftSchmidtVector, norm_smul, hn, norm_inv, Real.norm_of_nonneg h0, inv_mul_cancel₀ hσ]

/-- The left Schmidt vectors of nonzero Schmidt values are pairwise orthonormal. -/
theorem inner_leftSchmidtVector (M : Matrix m n ℝ) (i j : Fin (finrank ℝ (EuclideanSpace ℝ n)))
    (hi : (toEuclideanLin M).singularValues i ≠ 0) :
    ⟪leftSchmidtVector M i, leftSchmidtVector M j⟫ = if i = j then 1 else 0 := by
  classical
  have hi' : leftSchmidtVector M i = ((toEuclideanLin M).singularValues i)⁻¹ •
      toEuclideanLin M (rightSingularVectors M i) := rfl
  rw [hi', real_inner_smul_left, inner_toEuclideanLin_left, transpose_leftSchmidtVector,
    real_inner_smul_right, orthonormal_iff_ite.mp (rightSingularVectors M).orthonormal i j]
  split_ifs with h
  · subst h
    field_simp
  · simp

/-- The Schmidt states `|α⟩_A` of Eq. (3) (left Schmidt vectors of nonzero Schmidt values) form
an orthonormal family; the `|α⟩_B` are the core orthonormal basis `rightSingularVectors`. -/
theorem orthonormal_leftSchmidtVector (M : Matrix m n ℝ) :
    Orthonormal ℝ (fun i : {i : Fin (finrank ℝ (EuclideanSpace ℝ n)) //
      (toEuclideanLin M).singularValues i ≠ 0} => leftSchmidtVector M i) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_leftSchmidtVector M i j i.2]
  simp [Subtype.ext_iff]

/-- Eq. (3) of arXiv 2609.11811, the Schmidt decomposition `|Ψ⟩ = Σ_α λ_α |α⟩_A |α⟩_B`, in
operator form: `M x = Σ_α λ_α ⟪e_α, x⟫ a_α`, with the Schmidt values `λ_α = σ_α(M)` and the
Schmidt states built from the core singular value data. -/
theorem toEuclideanLin_eq_sum_schmidt (M : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    toEuclideanLin M x = ∑ i : Fin (finrank ℝ (EuclideanSpace ℝ n)),
      ((toEuclideanLin M).singularValues i *
      ⟪rightSingularVectors M i, x⟫) • leftSchmidtVector M i := by
  conv_lhs => rw [← (rightSingularVectors M).sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toEuclideanLin_rightSingularVectors, smul_smul, mul_comm]

/-- The truncation error `ε_Tr = Σ_{α > D} λ_α²` of arXiv 2609.11811 (text after Eq. (3)), with
the Schmidt values `λ_α = σ_α(M)` sorted decreasingly and indexed from `0`. -/
noncomputable def truncationError (M : Matrix m n ℝ) (D : ℕ) : ℝ :=
  ∑ i ∈ Ico D (Fintype.card n), (toEuclideanLin M).singularValues i ^ 2

section Frobenius

open scoped LeanDLRA.Frobenius

/-- Normalization in Eq. (3) of arXiv 2609.11811: a normalized state (`‖M‖_F = 1`) has
`Σ_α λ_α² = 1`.  Instance of the core identity `‖M‖_F² = Σ σ_i²`. -/
theorem sum_sq_singularValues_eq_one {M : Matrix m n ℝ} (hM : ‖M‖ = 1) :
    ∑ i ∈ range (Fintype.card n), (toEuclideanLin M).singularValues i ^ 2 = 1 := by
  rw [← sq_norm_eq_sum_sq_singularValues, hM, one_pow]

/-- Text after Eq. (3) of arXiv 2609.11811: keeping only the `D` largest Schmidt values (the
core SVD truncation `LeanDLRA.EckartYoung.truncation`) gives a state of Schmidt rank `≤ D`,
whose squared error is the truncation error `ε_Tr`, and which is an optimal approximation among
all states of Schmidt rank `≤ D` (Eckart–Young–Mirsky, Frobenius norm).  The error is the
Frobenius (state) norm of the unnormalized truncated state. -/
theorem truncation_optimal (M : Matrix m n ℝ) (D : ℕ) :
    (truncation M D).rank ≤ D ∧ ‖M - truncation M D‖ ^ 2 = truncationError M D ∧
      ∀ B : Matrix m n ℝ, B.rank ≤ D → ‖M - truncation M D‖ ≤ ‖M - B‖ :=
  ⟨rank_truncation_le M D, sq_norm_sub_truncation M D, fun _ hB => norm_sub_truncation_le M hB⟩

/-- For a normalized state the truncation error is the discarded weight,
`ε_Tr = 1 - Σ_{α ≤ D} λ_α²`. -/
theorem truncationError_eq_one_sub {M : Matrix m n ℝ} (hM : ‖M‖ = 1) {D : ℕ}
    (hD : D ≤ Fintype.card n) :
    truncationError M D = 1 - ∑ i ∈ range D, (toEuclideanLin M).singularValues i ^ 2 := by
  rw [← sum_sq_singularValues_eq_one hM, ← Finset.sum_range_add_sum_Ico _ hD, truncationError]
  ring

/-- Chain (not stated in the paper): the Rényi entropy `S_μ`, `0 < μ < 1`, of the Schmidt
weights controls the truncation error, `ε_Tr(D) ≤ μ/(1-μ) · exp((1-μ)/μ · S_μ) · D^{1-1/μ}`
for every `D ≥ 1`.  This is why the paper can replace the ill-posed sum of truncation errors by
the Rényi entropies (text before Eq. (4)): decreasing `S_μ` decreases this bound on the optimal
truncation error (`truncation_optimal`).  Chains `truncationError` with
`LeanDLRA.OpenProblems.RankAdaptivity.renyi_tail_le` (OP-RA-39 (b)). -/
theorem truncationError_le_renyiEntropy (M : Matrix m n ℝ) {D : ℕ} (hD : 0 < D) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    truncationError M D ≤ μ / (1 - μ) * Real.exp ((1 - μ) / μ *
      renyiEntropy μ (fun i : Fin (Fintype.card n) => (toEuclideanLin M).singularValues i ^ 2)) *
        (D : ℝ) ^ (1 - 1 / μ) := by
  have h := OpenProblems.RankAdaptivity.renyi_tail_le (N := Fintype.card n) hD
    (p := fun i => (toEuclideanLin M).singularValues i ^ 2)
    (fun i => sq_nonneg _) (fun i j hij => sq_singularValues_antitone _ hij) hμ0 hμ1
  unfold truncationError
  set S : ℝ := ∑ i ∈ range (Fintype.card n), ((toEuclideanLin M).singularValues i ^ 2) ^ μ
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (sq_nonneg _) _
  have hc : 0 < μ / (1 - μ) := div_pos hμ0 (by linarith)
  have hDpos : 0 < (D : ℝ) ^ (1 - 1 / μ) := Real.rpow_pos_of_pos (by exact_mod_cast hD) _
  rcases hS0.eq_or_lt with h0 | hpos
  · have hz : S ^ (1 / μ) = 0 := by
      rw [← h0]; exact Real.zero_rpow (one_div_pos.mpr hμ0).ne'
    rw [hz, mul_zero, zero_mul] at h
    exact h.trans (mul_nonneg (mul_nonneg hc.le (Real.exp_pos _).le) hDpos.le)
  · have hSfin : ∑ i : Fin (Fintype.card n), ((toEuclideanLin M).singularValues i ^ 2) ^ μ =
        S := by
      rw [hS, Fin.sum_univ_eq_sum_range (fun i => ((toEuclideanLin M).singularValues i ^ 2) ^ μ)]
    have hexp : Real.exp ((1 - μ) / μ * renyiEntropy μ
        (fun i : Fin (Fintype.card n) => (toEuclideanLin M).singularValues i ^ 2)) =
          S ^ (1 / μ) := by
      simp only [renyiEntropy]
      rw [hSfin, Real.rpow_def_of_pos hpos]
      congr 1
      field_simp [(by linarith : (1 - μ) ≠ 0)]
    rw [hexp]
    exact h

end Frobenius

/-- The reduced density matrix of subsystem `A`, `ρ̂_A = Tr_B |Ψ⟩⟨Ψ| = M Mᵀ` (Eq. (7) of
arXiv 2609.11811), for the state with coefficient matrix `M`. -/
def reducedDensity (M : Matrix m n ℝ) : Matrix m m ℝ := M * Mᵀ

omit [Fintype m] [DecidableEq n] in
/-- `ρ̂_A` is the partial trace over `B`: `(ρ̂_A)_{ii'} = Σ_j M_{ij} M_{i'j}`. -/
theorem reducedDensity_apply (M : Matrix m n ℝ) (i i' : m) :
    reducedDensity M i i' = ∑ j, M i j * M i' j := by
  simp [reducedDensity, Matrix.mul_apply]

omit [Fintype m] [DecidableEq n] in
/-- `ρ̂_A` is symmetric. -/
theorem reducedDensity_isHermitian (M : Matrix m n ℝ) : (reducedDensity M).IsHermitian := by
  simpa [reducedDensity, conjTranspose_eq_transpose_of_trivial] using
    isHermitian_mul_conjTranspose_self M

/-- `ρ̂_A x = M (Mᵀ x)`. -/
theorem toEuclideanLin_reducedDensity [DecidableEq m] (M : Matrix m n ℝ) (x : EuclideanSpace ℝ m) :
    toEuclideanLin (reducedDensity M) x = toEuclideanLin M (toEuclideanLin Mᵀ x) :=
  toEuclideanLin_mul_apply M Mᵀ x

/-- Eq. (7) of arXiv 2609.11811: `ρ̂_A = Σ_α p_α |α⟩_A ⟨α|_A`, i.e. the left Schmidt vectors are
eigenvectors of `ρ̂_A` with eigenvalues the Schmidt weights `p_α = λ_α²`. -/
theorem reducedDensity_leftSchmidtVector [DecidableEq m] (M : Matrix m n ℝ)
    (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) :
    toEuclideanLin (reducedDensity M) (leftSchmidtVector M i) =
      (toEuclideanLin M).singularValues i ^ 2 • leftSchmidtVector M i := by
  rw [toEuclideanLin_reducedDensity, transpose_leftSchmidtVector, map_smul,
    toEuclideanLin_rightSingularVectors, smul_smul, sq]

/-- Eq. (8) of arXiv 2609.11811 in the Schmidt basis: for Schmidt pairs `Mᵀ a_α = λ_α b_α`,
`Mᵀ a_β = λ_β b_β`, the `(α, β)` entry of `Ξ Mᵀ + M Ξᵀ` is `λ_α Ξ_{βα} + Ξ_{αβ} λ_β`, where
`Ξ_{αβ} = ⟪a_α, Ξ b_β⟫` are the coefficients of `|Ξ⟩` in the Schmidt basis (the paper's
`λ_α Ξ*_{βα} + Ξ_{αβ} λ_β`, real case). -/
theorem inner_reducedDensity_deriv [DecidableEq m] (M Ξ : Matrix m n ℝ)
    {aα aβ : EuclideanSpace ℝ m} {bα bβ : EuclideanSpace ℝ n} {σα σβ : ℝ}
    (hα : toEuclideanLin Mᵀ aα = σα • bα) (hβ : toEuclideanLin Mᵀ aβ = σβ • bβ) :
    ⟪aα, toEuclideanLin (Ξ * Mᵀ + M * Ξᵀ) aβ⟫ =
      σα * ⟪aβ, toEuclideanLin Ξ bα⟫ + ⟪aα, toEuclideanLin Ξ bβ⟫ * σβ := by
  rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    inner_add_right, hβ, map_smul, real_inner_smul_right,
    ← inner_toEuclideanLin_transpose M aα, hα, real_inner_smul_left,
    ← inner_toEuclideanLin_left Ξ bα aβ, real_inner_comm aβ]
  ring

end Schmidt

/-! ### Derivatives of the Schmidt weights (Eqs. (8)-(10)) -/

section SchmidtWeights

open Matrix EckartYoung Module
open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Eq. (8) of arXiv 2609.11811: if the coefficient matrix `M θ` of the state is differentiable
with derivative `Ξ` (the coefficient matrix of `|Ξ⟩ = T̂ |Ψ₀⟩`), then
`ρ̂_A' = Ξ Mᵀ + M Ξᵀ`, i.e. `Tr_B (|Ξ⟩⟨Ψ₀| + |Ψ₀⟩⟨Ξ|)` (Frobenius norm on matrices). -/
theorem hasDerivAt_reducedDensity {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ} {t : ℝ}
    (hM : HasDerivAt M Ξ t) :
    HasDerivAt (fun θ => reducedDensity (M θ)) (Ξ * (M t)ᵀ + M t * Ξᵀ) t :=
  Frobenius.hasDerivAt_mul hM (Frobenius.hasDerivAt_transpose hM)

/-- Square matrices as continuous linear operators on Euclidean space (continuous for the
Frobenius norm, as every linear map on a finite-dimensional space). -/
private noncomputable def toCLM :
    Matrix m m ℝ →L[ℝ] (EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      (toEuclideanLin : Matrix m m ℝ ≃ₗ[ℝ] _).toLinearMap)

private theorem toCLM_apply (A : Matrix m m ℝ) (x : EuclideanSpace ℝ m) :
    toCLM A x = toEuclideanLin A x := rfl

/-- Eq. (9) of arXiv 2609.11811: `∂p_α/∂θ = 2 λ_α Re Ξ_{αα}` (real setting, `Re` dropped).  Let
`M θ` be the coefficient matrix of the state, differentiable at `t` with derivative `Ξ`, and let
`p θ` be an eigenvalue of `ρ̂_A(θ) = M θ (M θ)ᵀ` with unit eigenvector `a θ` for `θ` near `t`,
continuous at `t`, and simple at `t` (the paper's non-degeneracy, footnote [52]).  If
`(M t)ᵀ a t = λ b` (a Schmidt pair `(|α⟩_A, |α⟩_B) = (a t, b)` with Schmidt value `λ`), then `p`
is differentiable at `t` with derivative `2 λ Ξ_{αα}`, where `Ξ_{αα} = ⟪a t, Ξ b⟫` is the
`(α, α)` coefficient of `|Ξ⟩` in the Schmidt basis.  Derived from
`hasDerivAt_eigenvalue_of_simple` and Eq. (8). -/
theorem hasDerivAt_schmidtWeight {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ} {t : ℝ}
    (hM : HasDerivAt M Ξ t) {p : ℝ → ℝ} {a : ℝ → EuclideanSpace ℝ m}
    (ha : ∀ᶠ θ in 𝓝 t, ‖a θ‖ = 1 ∧ toEuclideanLin (reducedDensity (M θ)) (a θ) = p θ • a θ)
    (hp : ContinuousAt p t)
    (hsimple : ∀ u, toEuclideanLin (reducedDensity (M t)) u = p t • u → ∃ c : ℝ, u = c • a t)
    {σ : ℝ} {b : EuclideanSpace ℝ n} (hb : toEuclideanLin (M t)ᵀ (a t) = σ • b) :
    HasDerivAt p (2 * σ * ⟪a t, toEuclideanLin Ξ b⟫) t := by
  have hρ : HasDerivAt (fun θ => toCLM (reducedDensity (M θ)))
      (toCLM (Ξ * (M t)ᵀ + M t * Ξᵀ)) t :=
    (toCLM (m := m)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_reducedDensity hM)
  have hsymm : ∀ θ, ((toCLM (reducedDensity (M θ)) :
      EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m)).IsSymmetric := fun θ =>
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (reducedDensity_isHermitian (M θ))
  have h := hasDerivAt_eigenvalue_of_simple hρ (Eventually.of_forall hsymm) ha hp hsimple
  convert h using 1
  rw [toCLM_apply, inner_reducedDensity_deriv (M t) Ξ hb hb]
  ring

/-- Non-vacuity of `hasDerivAt_schmidtWeight`: the one-mode state `M θ = 1 + θ`, with Schmidt
weight `p θ = (1 + θ)²`. -/
example : HasDerivAt (fun θ : ℝ => (1 + θ) ^ 2) 2 0 := by
  have hM : HasDerivAt (fun θ : ℝ => (1 + θ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)
  have hρ : ∀ (θ : ℝ) (u : EuclideanSpace ℝ (Fin 1)),
      toEuclideanLin (reducedDensity ((1 + θ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) u =
        (1 + θ) ^ 2 • u := by
    intro θ u
    have hred : reducedDensity ((1 + θ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        (1 + θ) ^ 2 • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      simp [reducedDensity, sq, smul_smul]
    rw [hred, map_smul, LinearMap.smul_apply, Matrix.toLpLin_one, LinearMap.id_apply]
  have hsing : ∀ u : EuclideanSpace ℝ (Fin 1), u = u 0 • EuclideanSpace.single 0 1 := by
    intro u
    ext i
    fin_cases i
    simp
  have h := hasDerivAt_schmidtWeight
    (M := fun θ : ℝ => (1 + θ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (p := fun θ => (1 + θ) ^ 2)
    (a := fun _ => EuclideanSpace.single 0 1) (σ := 1) (b := EuclideanSpace.single 0 1) hM
    (Eventually.of_forall fun θ => ⟨by simp, hρ θ _⟩) (by fun_prop)
    (fun u _ => ⟨u 0, hsing u⟩) (by simp)
  simpa using h

/-- Eq. (9) of arXiv 2609.11811 at a Schmidt pair built from the core singular value data:
`∂p_α/∂θ = 2 σ_α ⟪a_α, Ξ e_α⟫`, with `a_α = leftSchmidtVector` and `e_α` the core
`rightSingularVectors`. -/
theorem hasDerivAt_schmidtWeight_singular {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ} {t : ℝ}
    (hM : HasDerivAt M Ξ t) (i : Fin (finrank ℝ (EuclideanSpace ℝ n))) {p : ℝ → ℝ}
    {a : ℝ → EuclideanSpace ℝ m}
    (ha : ∀ᶠ θ in 𝓝 t, ‖a θ‖ = 1 ∧ toEuclideanLin (reducedDensity (M θ)) (a θ) = p θ • a θ)
    (hat : a t = leftSchmidtVector (M t) i) (hp : ContinuousAt p t)
    (hsimple : ∀ u, toEuclideanLin (reducedDensity (M t)) u = p t • u → ∃ c : ℝ, u = c • a t) :
    HasDerivAt p (2 * (toEuclideanLin (M t)).singularValues i *
      ⟪leftSchmidtVector (M t) i, toEuclideanLin Ξ (rightSingularVectors (M t) i)⟫) t := by
  have h := hasDerivAt_schmidtWeight hM ha hp hsimple
    (by rw [hat]; exact transpose_leftSchmidtVector (M t) i)
  rwa [hat] at h

omit [DecidableEq n] in
/-- Text after Eq. (9) of arXiv 2609.11811 ("nonzero derivatives are only measured for those
(kl) pairs that correspond to mode rotations between the two subsystems"), first half: a
rotation inside subsystem `A` (`Ξ = K M` with `K` skew-symmetric) leaves every simple Schmidt
weight stationary. -/
theorem hasDerivAt_schmidtWeight_of_skew_left {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ}
    {t : ℝ} (hM : HasDerivAt M Ξ t) {p : ℝ → ℝ} {a : ℝ → EuclideanSpace ℝ m}
    (ha : ∀ᶠ θ in 𝓝 t, ‖a θ‖ = 1 ∧ toEuclideanLin (reducedDensity (M θ)) (a θ) = p θ • a θ)
    (hp : ContinuousAt p t)
    (hsimple : ∀ u, toEuclideanLin (reducedDensity (M t)) u = p t • u → ∃ c : ℝ, u = c • a t)
    {σ : ℝ} {b : EuclideanSpace ℝ n} (hb : toEuclideanLin (M t)ᵀ (a t) = σ • b)
    {K : Matrix m m ℝ} (hK : Kᵀ = -K) (hΞ : Ξ = K * M t) : HasDerivAt p 0 t := by
  classical
  have h := hasDerivAt_schmidtWeight hM ha hp hsimple hb
  convert h using 1
  obtain ⟨_, hat⟩ := ha.self_of_nhds
  by_cases hσ : σ = 0
  · simp [hσ]
  · have hMb : toEuclideanLin (M t) b = (σ⁻¹ * p t) • a t := by
      have h2 : toEuclideanLin (M t) (toEuclideanLin (M t)ᵀ (a t)) = p t • a t := by
        rw [← toEuclideanLin_reducedDensity]; exact hat
      rw [hb, map_smul] at h2
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hσ, one_smul]
    rw [hΞ, toEuclideanLin_mul_apply, hMb, map_smul, real_inner_smul_right,
      inner_toEuclideanLin_self_of_skew hK]
    ring

omit [DecidableEq n] in
/-- Text after Eq. (9) of arXiv 2609.11811, second half: a rotation inside subsystem `B`
(`Ξ = M K` with `K` skew-symmetric) leaves every simple Schmidt weight stationary. -/
theorem hasDerivAt_schmidtWeight_of_skew_right {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ}
    {t : ℝ} (hM : HasDerivAt M Ξ t) {p : ℝ → ℝ} {a : ℝ → EuclideanSpace ℝ m}
    (ha : ∀ᶠ θ in 𝓝 t, ‖a θ‖ = 1 ∧ toEuclideanLin (reducedDensity (M θ)) (a θ) = p θ • a θ)
    (hp : ContinuousAt p t)
    (hsimple : ∀ u, toEuclideanLin (reducedDensity (M t)) u = p t • u → ∃ c : ℝ, u = c • a t)
    {σ : ℝ} {b : EuclideanSpace ℝ n} (hb : toEuclideanLin (M t)ᵀ (a t) = σ • b)
    {K : Matrix n n ℝ} (hK : Kᵀ = -K) (hΞ : Ξ = M t * K) : HasDerivAt p 0 t := by
  classical
  have h := hasDerivAt_schmidtWeight hM ha hp hsimple hb
  convert h using 1
  rw [hΞ, toEuclideanLin_mul_apply, ← inner_toEuclideanLin_transpose (M t) (a t), hb,
    real_inner_smul_left,
    inner_toEuclideanLin_self_of_skew hK]
  ring

/-- Eq. (9) inserted into Eq. (10) of arXiv 2609.11811: the derivative of the Rényi entropy of a
family of simple, positive Schmidt weights `p_α(θ)` (eigenvalue branches of `ρ̂_A(θ)`) is
`(1-μ)⁻¹ Σ_α μ p_α^{μ-1} · 2 λ_α Ξ_{αα} / Σ_α p_α^μ`.  This is the entropy of `ρ̂_A(θ)` when the
branches exhaust its spectrum (which requires `ρ̂_A(t)` to be positive definite with simple
spectrum); that identification is not formalized. -/
theorem hasDerivAt_renyiEntropy_schmidt {ι : Type*} [Fintype ι] [Nonempty ι] (μ : ℝ)
    {M : ℝ → Matrix m n ℝ} {Ξ : Matrix m n ℝ} {t : ℝ} (hM : HasDerivAt M Ξ t)
    {p : ℝ → ι → ℝ} {a : ι → ℝ → EuclideanSpace ℝ m}
    (ha : ∀ α, ∀ᶠ θ in 𝓝 t,
      ‖a α θ‖ = 1 ∧ toEuclideanLin (reducedDensity (M θ)) (a α θ) = p θ α • a α θ)
    (hp : ∀ α, ContinuousAt (fun θ => p θ α) t)
    (hsimple : ∀ α u, toEuclideanLin (reducedDensity (M t)) u = p t α • u →
      ∃ c : ℝ, u = c • a α t)
    {σ : ι → ℝ} {b : ι → EuclideanSpace ℝ n}
    (hb : ∀ α, toEuclideanLin (M t)ᵀ (a α t) = σ α • b α) (hpos : ∀ α, 0 < p t α) :
    HasDerivAt (fun θ => renyiEntropy μ (p θ))
      ((1 - μ)⁻¹ * ((∑ α, μ * p t α ^ (μ - 1) * (2 * σ α * ⟪a α t, toEuclideanLin Ξ (b α)⟫)) /
        ∑ α, p t α ^ μ)) t :=
  hasDerivAt_renyiEntropy μ
    (fun α => hasDerivAt_schmidtWeight hM (ha α) (hp α) (hsimple α) (hb α)) hpos

end SchmidtWeights

/-! ### Mode rotations (Eqs. (5), (12)) -/

section Rotations

open Matrix

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Eq. (5) of arXiv 2609.11811: the antisymmetric generator of the rotation between modes `k`
and `l`, `X^{(kl)}_{ij} = δ_{ki} δ_{lj} - δ_{kj} δ_{li}`. -/
def rotGen (k l : N) : Matrix N N ℝ := single k l 1 - single l k 1

omit [Fintype N] in
theorem rotGen_apply (k l i j : N) :
    rotGen k l i j = (if k = i ∧ l = j then 1 else 0) - (if l = i ∧ k = j then 1 else 0) := by
  simp [rotGen, single]

omit [Fintype N] in
/-- `X^{(kl)}` is antisymmetric. -/
theorem transpose_rotGen (k l : N) : (rotGen k l)ᵀ = -rotGen k l := by
  rw [rotGen, transpose_sub, transpose_single, transpose_single, neg_sub]

/-- Eq. (5) of arXiv 2609.11811 is orthogonal to first order: for antisymmetric `A`,
`(I + A)ᵀ (I + A) = I + Aᵀ A`, so `U = I + Σ Δθ_{(kl)} X^{(kl)}` satisfies `Uᵀ U = I + O(Δθ²)`. -/
theorem transpose_mul_one_add_of_skew {A : Matrix N N ℝ} (hA : Aᵀ = -A) :
    (1 + A)ᵀ * (1 + A) = 1 + Aᵀ * A := by
  rw [transpose_add, transpose_one, hA]
  noncomm_ring

/-- The exponential of an antisymmetric real matrix lies in `SO(N)`: it is orthogonal, and its
determinant is `1` (not just `±1`).  The paper's update `U_n` of Eq. (12) is of this form. -/
theorem exp_mem_specialOrthogonalGroup {A : Matrix N N ℝ} (hA : Aᵀ = -A) :
    NormedSpace.exp A ∈ specialOrthogonalGroup N ℝ := by
  have horth : ∀ B : Matrix N N ℝ, Bᵀ = -B →
      (NormedSpace.exp B)ᵀ * NormedSpace.exp B = 1 := by
    intro B hB
    rw [← Matrix.exp_transpose, hB, Matrix.exp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp B))
  refine mem_specialOrthogonalGroup_iff.mpr ⟨(mem_orthogonalGroup_iff' N ℝ).mpr (horth A hA), ?_⟩
  set B : Matrix N N ℝ := (1 / 2 : ℝ) • A with hB
  have hBs : Bᵀ = -B := by rw [hB, transpose_smul, hA, smul_neg]
  have hdet : (NormedSpace.exp B).det ^ 2 = 1 := by
    have h := congrArg det (horth B hBs)
    rw [det_mul, det_transpose, det_one] at h
    rw [sq, h]
  have h2 : (2 : ℕ) • B = A := by
    rw [two_nsmul, hB, ← add_smul]
    norm_num
  rw [← h2, Matrix.exp_nsmul, det_pow, hdet]

end Rotations

section ModePairs

open Matrix

variable {N : Type*} [Fintype N] [LinearOrder N]

/-- The mode pairs `(k, l)` with `k < l` that index the angles `θ_{(kl)}` of Eq. (5) of
arXiv 2609.11811. -/
abbrev ModePair (N : Type*) [LinearOrder N] := {q : N × N // q.1 < q.2}

/-- `Σ_{(kl), k < l} θ_{(kl)} X^{(kl)}`, the generator in Eqs. (5) and (12) of
arXiv 2609.11811. -/
noncomputable def rotGenSum (θ : ModePair N → ℝ) : Matrix N N ℝ :=
  ∑ q, θ q • rotGen q.1.1 q.1.2

/-- Entries of `Σ θ_{(kl)} X^{(kl)}`: `θ_{(ij)}` above the diagonal, `-θ_{(ji)}` below. -/
theorem rotGenSum_apply (θ : ModePair N → ℝ) (i j : N) :
    rotGenSum θ i j =
      (if h : i < j then θ ⟨(i, j), h⟩ else 0) - (if h : j < i then θ ⟨(j, i), h⟩ else 0) := by
  simp only [rotGenSum, Matrix.sum_apply, Matrix.smul_apply, rotGen_apply, smul_eq_mul, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  congr 1
  · split_ifs with h
    · rw [Fintype.sum_eq_single ⟨(i, j), h⟩]
      · simp
      · intro q hq
        rw [ite_eq_right_iff]
        rintro ⟨h1, h2⟩
        exact absurd (Subtype.ext (Prod.ext h1 h2)) hq
    · refine Finset.sum_eq_zero fun q _ => ?_
      rw [ite_eq_right_iff]
      rintro ⟨h1, h2⟩
      have hq := q.2
      rw [h1, h2] at hq
      exact absurd hq h
  · split_ifs with h
    · rw [Fintype.sum_eq_single ⟨(j, i), h⟩]
      · simp
      · intro q hq
        rw [ite_eq_right_iff]
        rintro ⟨h1, h2⟩
        exact absurd (Subtype.ext (Prod.ext h2 h1)) hq
    · refine Finset.sum_eq_zero fun q _ => ?_
      rw [ite_eq_right_iff]
      rintro ⟨h1, h2⟩
      have hq := q.2
      rw [h1, h2] at hq
      exact absurd hq h

/-- The angles are the entries above the diagonal, so `θ ↦ Σ θ_{(kl)} X^{(kl)}` is injective. -/
theorem rotGenSum_apply_of_lt (θ : ModePair N → ℝ) {i j : N} (h : i < j) :
    rotGenSum θ i j = θ ⟨(i, j), h⟩ := by
  simp [rotGenSum_apply, h, lt_asymm h]

/-- `Σ θ_{(kl)} X^{(kl)}` is antisymmetric. -/
theorem transpose_rotGenSum (θ : ModePair N → ℝ) : (rotGenSum θ)ᵀ = -rotGenSum θ := by
  ext i j
  simp only [transpose_apply, Matrix.neg_apply, rotGenSum_apply]
  ring

/-- The generators `X^{(kl)}`, `k < l`, of Eq. (5) of arXiv 2609.11811 span all antisymmetric
matrices (the Lie algebra of `SO(N)`): every antisymmetric `A` is `Σ_{k<l} A_{kl} X^{(kl)}`, so
the gradient over `θ` involves all generators of the rotation group. -/
theorem rotGenSum_of_skew {A : Matrix N N ℝ} (hA : Aᵀ = -A) :
    rotGenSum (fun q => A q.1.1 q.1.2) = A := by
  ext i j
  have hji : A j i = -A i j := by simpa using congrFun (congrFun hA i) j
  rw [rotGenSum_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h]
  · have h0 : A i i = 0 := by linarith
    simp [h0]
  · simp [h, lt_asymm h, hji]

/-- Eq. (12) of arXiv 2609.11811: `U_n = exp(-τ Σ_{(kl)} g_{(kl)} X^{(kl)}) ∈ SO(N)` for every
step length `τ` and every gradient (or corrected search direction) `g`. -/
theorem exp_neg_smul_rotGenSum_mem (τ : ℝ) (g : ModePair N → ℝ) :
    NormedSpace.exp (-τ • rotGenSum g) ∈ specialOrthogonalGroup N ℝ :=
  exp_mem_specialOrthogonalGroup (by rw [transpose_smul, transpose_rotGenSum, smul_neg])

/-- A cost on `N × N` matrices pulled back to the rotation angles,
`θ ↦ C(exp(Σ_{k<l} θ_{(kl)} X^{(kl)}))` (in the paper `C(U) = B_μ` after rotating the modes by
`U`). -/
noncomputable def rotCost (C : Matrix N N ℝ → ℝ) (θ : ModePair N → ℝ) : ℝ :=
  C (NormedSpace.exp (rotGenSum θ))

/-- Eqs. (11)-(12) of arXiv 2609.11811 (steepest descent over `SO(N)`): if the cost pulled back
to the angles is differentiable at `0` with nonzero gradient `g_{(kl)} = ∂B/∂θ_{(kl)}`, then for
some `τ > 0` the rotation `U = exp(-τ Σ g_{(kl)} X^{(kl)})` lies in `SO(N)` and strictly
decreases the cost: `C(U) < C(I)`.  Chains `exists_pos_step_decreases` with
`exp_neg_smul_rotGenSum_mem`. -/
theorem exists_rotation_decreases (C : Matrix N N ℝ → ℝ)
    (hC : DifferentiableAt ℝ (rotCost C) 0)
    (hne : ∃ q, fderiv ℝ (rotCost C) 0 (Pi.single q 1) ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧
      NormedSpace.exp (-τ • rotGenSum fun q => fderiv ℝ (rotCost C) 0 (Pi.single q 1)) ∈
        specialOrthogonalGroup N ℝ ∧
      C (NormedSpace.exp (-τ • rotGenSum fun q => fderiv ℝ (rotCost C) 0 (Pi.single q 1))) <
        C 1 := by
  obtain ⟨τ, hτ, hlt⟩ := exists_pos_step_decreases (rotCost C) hC hne
  refine ⟨τ, hτ, exp_neg_smul_rotGenSum_mem τ _, ?_⟩
  have hlin : rotGenSum (fun q => -τ * fderiv ℝ (rotCost C) 0 (Pi.single q 1)) =
      -τ • rotGenSum (fun q => fderiv ℝ (rotCost C) 0 (Pi.single q 1)) := by
    simp only [rotGenSum, Finset.smul_sum, smul_smul]
  have h0 : rotCost C 0 = C 1 := by simp [rotCost, rotGenSum]
  rw [h0, rotCost, hlin] at hlt
  exact hlt

end ModePairs

end LeanDLRA.Literature.P2609_11811
