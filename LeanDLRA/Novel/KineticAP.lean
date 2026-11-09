import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.OpenProblems.Curated.StiffAndStochasticDefs
import LeanDLRA.LinearAlgebra.Factorization.Defs

/-!
# Asymptotic preservation of low-rank IMEX schemes, characterized

Statements at fixed time step and fixed mesh, with explicit constants.
All statements concern actual matrices `g ∈ ℝ^{m × n}` (space × moments) and the actual implicit
substeps; nothing about the limit is assumed.

## Lemma H and its source form

For a self-adjoint `C ≤ 0`, an orthogonal projector `P` and `K = range P ⊓ ker C`:

* `lemmaH`: `‖v - P_K w‖ ≤ ‖P w - P_K w‖ / (1 + s γ)` for the implicit step `v = P (w + s C v)`;
  the gap `γ = relaxGap P C` is defined, and positive when `range P ⊖ K ≠ 0` (`relaxGap_pos`);
* `lemmaH_sharp`: the rate is attained for every `s`;
* `relax_le`, `existsUnique_chapmanEnskog`, `starProjection_step`, `norm_step_ge`: the same with a
  stiff source `s F`, and the solvability alternative `P_K F = 0`;
* `tendsto_equilibrium_iff`, `starProjection_eq_iff`, `forall_starProjection_eq_iff`: the step tends
  to the true equilibrium projection if and only if that projection lies in the Galerkin space.

## BGK relaxation: the equilibrium statement

For `C g = -σ (g - g M Mᵀ)` with equilibrium direction `M`: `bgk_tendsto_iff` (the limit is correct
iff `M ∈ range V` and `w M ∈ range U`), `bgk_le_of_mem` (rate with gap `σ₀`), `bgk_le_of_not_mem`
(otherwise the mass is lost, with the degenerating gap `σ₀ dist(M, range V)²`).

## The micro-macro BUG scheme of Einkemmer–Hu–Kusch, arXiv 2212.12012

`IsMicroMacroBUGStep` is (4.4), (4.6), (4.8) of the paper, `IsMicroMacroRun` adds the macro update.
Both are non-vacuous (`exists_step`, `exists_run`).

* `kStep_le`, `lStep_le`, `sStep_le`: the three substep limits, with a rate;
* `not_isUnit_of_lLimit_eq`: the invertibility hypothesis of the published proof cannot hold for
  `r ≥ 2`, and `ap_fails_with_V_perp_a`: at `r = 1` it does not suffice;
* `capture_kStep`, `capture_lStep`, `ap_step_le`, `tendsto_diffFlux`: what replaces it;
* `ap_step_le_of_capture`: augmentation makes AP unconditional;
* `capture_defect_le_norm`, `tendsto_diffFlux_iff`, `sLimit_eq_diffFlux_iff`, `sLimit_eq_zero_iff`:
  the characterisation, in terms of the new bases;
* `norm_macro_sub_le`, `norm_macro_sub_effective_le`: the diffusion step and the effective equation;
* `ap_run`, `inner_next_gradient_pos`: AP of every step of a run, from nondegeneracy at `n = 0`
  and a parabolic CFL condition;
* `sStep_ge`, `exists_rate_not_eps_sq`: the rate is `ε`, not `ε² / dt`.

## Remarks

1. `σ` is invertible on the micro variable, so `ker C = 0` there: `a` and `σ⁻¹ ∂ₓρ` are not
   equilibrium directions but Chapman–Enskog directions, and Lemma H without a source says nothing
   about the scheme.  The equilibrium statement is the BGK one above; the micro-macro statement
   needs the source form.
2. The per-step rate `C ε² / (dt σ_min)` is false: the explicit `1/ε` transport gives order `ε`.
3. The "only if" of Theorem I is false, in both of its conditions (`ap_holds_with_V_perp_a`,
   `ap_holds_with_X_perp_d`), and `V ⊥ a` does not give `g = 0` (`ap_fails_with_V_perp_a`,
   `ap_lost_with_both_perp`): the true condition is on the new bases.  These counterexamples use
   constant `σ` and `𝒯 (X S Vᵀ) V = 0`; for generic `V ⊥ a`, AP does fail.
4. The limit of the `L`-step is `-a ⟨X Xᵀ σ⟩⁻¹ ⟨∂ₓρ, X⟩`, not `-a ⟨∂ₓρ, X⟩`.
5. The limit of the micro variable has rank at most one, not two (`rank_diffFlux_le`).
6. `ker C ≤ range P` fails for the `L`- and `S`-steps of a low-rank scheme whenever `U` is not onto,
   so the "iff" must be used pointwise (`starProjection_eq_iff`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Novel.KineticAP

open LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `C` is a relaxation operator: self-adjoint and nonpositive. -/
structure IsRelaxation (C : E →L[ℝ] E) : Prop where
  symm : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫
  nonpos : ∀ x, ⟪C x, x⟫ ≤ 0

/-- The energy identity behind every estimate of this file. -/
private theorem core_le {P C : E →L[ℝ] E} (hP : IsOrthProj P) {e z : E} {s γ : ℝ} (hs : 0 ≤ s)
    (hγ : 0 ≤ γ) (hPe : P e = e) (he : e = z + s • P (C e)) (hcoer : γ * ‖e‖ ^ 2 ≤ -⟪C e, e⟫) :
    ‖e‖ ≤ ‖z‖ / (1 + s * γ) := by
  have key : ‖e‖ ^ 2 = ⟪z, e⟫ + s * ⟪C e, e⟫ := by
    have h : ⟪e, e⟫ = ⟪z + s • P (C e), e⟫ := by rw [← he]
    rwa [real_inner_self_eq_norm_sq, inner_add_left, real_inner_smul_left, hP.symm, hPe] at h
  have hz := real_inner_le_norm z e
  have hne : 0 ≤ ‖e‖ := norm_nonneg e
  have hsc := mul_le_mul_of_nonneg_left hcoer hs
  have h1 : (1 + s * γ) * ‖e‖ ^ 2 ≤ ‖z‖ * ‖e‖ := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  by_cases h0 : ‖e‖ = 0
  · rw [h0]; simp
  · have hpos : 0 < ‖e‖ := lt_of_le_of_ne hne (Ne.symm h0)
    have h2 : ((1 + s * γ) * ‖e‖ - ‖z‖) * ‖e‖ ≤ 0 := by nlinarith
    have h3 : (1 + s * γ) * ‖e‖ - ‖z‖ ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hc hpos]
    linarith

/-- A semidefinite operator annihilates its isotropic vectors. -/
theorem IsRelaxation.apply_eq_zero {C : E →L[ℝ] E} (hC : IsRelaxation C) {x : E}
    (hx : ⟪C x, x⟫ = 0) : C x = 0 := by
  by_contra hne
  have hN : 0 < ‖C x‖ ^ 2 := by have := norm_pos_iff.2 hne; positivity
  have hc0 : ⟪C (C x), C x⟫ ≤ 0 := hC.nonpos _
  have hexp : ∀ t : ℝ, ⟪C (x + t • C x), x + t • C x⟫ =
      2 * t * ‖C x‖ ^ 2 + t ^ 2 * ⟪C (C x), C x⟫ := by
    intro t
    have h2 : ⟪C (C x), x⟫ = ‖C x‖ ^ 2 := by rw [hC.symm, real_inner_self_eq_norm_sq]
    have h3 : ⟪C x, C x⟫ = ‖C x‖ ^ 2 := real_inner_self_eq_norm_sq _
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      hx, h2, h3]
    ring
  set c := ⟪C (C x), C x⟫ with hc
  set N := ‖C x‖ ^ 2 with hNdef
  have h1c : 0 < 1 - c := by linarith
  have hle := hC.nonpos (x + (N / (1 - c)) • C x)
  rw [hexp] at hle
  have ht : 0 < N / (1 - c) := div_pos hN h1c
  set t := N / (1 - c) with htdef
  have htc : t * (1 - c) = N := by rw [htdef]; field_simp
  have hval : 2 * t * N + t ^ 2 * c = t ^ 2 * (2 - c) := by rw [← htc]; ring
  rw [hval] at hle
  have : 0 < t ^ 2 * (2 - c) := by have : 0 < 2 - c := by linarith
                                   positivity
  linarith

/-- The Galerkin relaxation estimate with a stiff source, for `C` coercive on all of `range P`.
Writing the step as `v = P (w + s (C v + F))` and `y` for the solution of the limit (Galerkin
Chapman–Enskog) problem `P (C y + F) = 0`, the error contracts by `1 / (1 + s γ)`.  `C` need not
be self-adjoint. -/
theorem coercive_relax_le {P C : E →L[ℝ] E} (hP : IsOrthProj P) {γ : ℝ} (hγ : 0 ≤ γ)
    (hcoer : ∀ x, P x = x → γ * ‖x‖ ^ 2 ≤ -⟪C x, x⟫) {s : ℝ} (hs : 0 ≤ s) {w F v y : E}
    (hv : v = P (w + s • (C v + F))) (hy : P y = y) (hF : P (C y + F) = 0) :
    ‖v - y‖ ≤ ‖P w - y‖ / (1 + s * γ) := by
  have hPv : P v = v := by rw [hv, hP.idem]
  have hPe : P (v - y) = v - y := by rw [map_sub, hPv, hy]
  have hsplit : P (C v + F) = P (C (v - y)) := by
    have : C v + F = C (v - y) + (C y + F) := by rw [map_sub]; abel
    rw [this, map_add, hF, add_zero]
  have heq : v - y = (P w - y) + s • P (C (v - y)) := by
    have h1 : v = P w + s • P (C v + F) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul]
    rw [hsplit] at h1
    calc v - y = (P w + s • P (C (v - y))) - y := congrArg (· - y) h1
      _ = (P w - y) + s • P (C (v - y)) := by abel
  exact core_le hP hs hγ hPe heq (hcoer _ hPe)

/-- The matching lower bound: if `‖P C x‖ ≤ Λ ‖x‖` on `range P`, the error of the implicit step
is at least `‖P w - y‖ / (1 + s Λ)`.  So the contraction factor is exact up to the conditioning of
`C` on the Galerkin space, and any part of `P w` that grows as `ε → 0` survives in the error. -/
theorem coercive_relax_ge {P C : E →L[ℝ] E} (hP : IsOrthProj P) {Λ : ℝ}
    (hΛ : ∀ x, P x = x → ‖P (C x)‖ ≤ Λ * ‖x‖) {s : ℝ} (hs : 0 ≤ s) {w F v y : E}
    (hv : v = P (w + s • (C v + F))) (hy : P y = y) (hF : P (C y + F) = 0) :
    ‖P w - y‖ ≤ (1 + s * Λ) * ‖v - y‖ := by
  have hPv : P v = v := by rw [hv, hP.idem]
  have hPe : P (v - y) = v - y := by rw [map_sub, hPv, hy]
  have hsplit : P (C v + F) = P (C (v - y)) := by
    have : C v + F = C (v - y) + (C y + F) := by rw [map_sub]; abel
    rw [this, map_add, hF, add_zero]
  have heq : P w - y = (v - y) - s • P (C (v - y)) := by
    have h1 : v = P w + s • P (C v + F) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul]
    rw [hsplit] at h1
    calc P w - y = (P w + s • P (C (v - y))) - y - s • P (C (v - y)) := by abel
      _ = (v - y) - s • P (C (v - y)) := by rw [← h1]
  rw [heq]
  calc ‖(v - y) - s • P (C (v - y))‖ ≤ ‖v - y‖ + ‖s • P (C (v - y))‖ := norm_sub_le _ _
    _ = ‖v - y‖ + s * ‖P (C (v - y))‖ := by rw [norm_smul, Real.norm_of_nonneg hs]
    _ ≤ ‖v - y‖ + s * (Λ * ‖v - y‖) := by
        gcongr
        exact hΛ _ hPe
    _ = (1 + s * Λ) * ‖v - y‖ := by ring

/-- Membership in the Galerkin equilibria `K = range P ⊓ ker C`. -/
theorem mem_apEquilibria_iff {P C : E →L[ℝ] E} (hP : IsOrthProj P) {k : E} :
    k ∈ apEquilibria P C ↔ P k = k ∧ C k = 0 := by
  constructor
  · rintro ⟨⟨z, hz⟩, h⟩
    refine ⟨?_, h⟩
    have hz' : P z = k := hz
    rw [← hz', hP.idem]
  · rintro ⟨h1, h2⟩
    exact ⟨⟨k, h1⟩, h2⟩

/-- The space `range P ⊖ K` on which the spectral gap of the relaxation is measured. -/
noncomputable def gapSpace (P C : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.range (P : E →ₗ[ℝ] E) ⊓ (apEquilibria P C)ᗮ

theorem mem_gapSpace_iff {P C : E →L[ℝ] E} (hP : IsOrthProj P) {x : E} :
    x ∈ gapSpace P C ↔ P x = x ∧ x ∈ (apEquilibria P C)ᗮ := by
  constructor
  · rintro ⟨⟨z, hz⟩, h⟩
    refine ⟨?_, h⟩
    have hz' : P z = x := hz
    rw [← hz', hP.idem]
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩

private theorem continuous_rayleigh (C : E →L[ℝ] E) : Continuous fun x => -⟪C x, x⟫ := by
  fun_prop

variable [FiniteDimensional ℝ E]

/-- The orthogonal projector onto a subspace is an `IsOrthProj`. -/
theorem isOrthProj_starProjection (K : Submodule ℝ E) : IsOrthProj K.starProjection where
  idem x := Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem K x)
  symm x y := Submodule.inner_starProjection_left_eq_right K x y

/-- The spectral gap `γ` of `-C` compressed to `range P ⊖ K`: the minimum of the Rayleigh quotient
on the unit sphere of that space (and `0` if the space is trivial). -/
noncomputable def relaxGap (P C : E →L[ℝ] E) : ℝ :=
  sInf ((fun x => -⟪C x, x⟫) '' {x | x ∈ gapSpace P C ∧ ‖x‖ = 1})

private theorem isCompact_gapSphere (P C : E →L[ℝ] E) :
    IsCompact {x | x ∈ gapSpace P C ∧ ‖x‖ = 1} := by
  have h : {x | x ∈ gapSpace P C ∧ ‖x‖ = 1} =
      Metric.sphere (0 : E) 1 ∩ (gapSpace P C : Set E) := by
    ext x; simp [and_comm]
  rw [h]
  exact (isCompact_sphere 0 1).inter_right (Submodule.closed_of_finiteDimensional _)

/-- The gap is a coercivity constant on `range P ⊖ K`. -/
theorem relaxGap_mul_le (P C : E →L[ℝ] E) {x : E} (hx : x ∈ gapSpace P C) :
    relaxGap P C * ‖x‖ ^ 2 ≤ -⟪C x, x⟫ := by
  by_cases h0 : x = 0
  · simp [h0]
  have hn : 0 < ‖x‖ := norm_pos_iff.2 h0
  have hmem : ‖x‖⁻¹ • x ∈ {x | x ∈ gapSpace P C ∧ ‖x‖ = 1} := by
    refine ⟨Submodule.smul_mem _ _ hx, ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hbdd := ((isCompact_gapSphere P C).image (continuous_rayleigh C)).bddBelow
  have hle := csInf_le hbdd (Set.mem_image_of_mem _ hmem)
  have hval : -⟪C (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ = (‖x‖⁻¹) ^ 2 * -⟪C x, x⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  change relaxGap P C ≤ -⟪C (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫ at hle
  rw [hval] at hle
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  calc relaxGap P C * ‖x‖ ^ 2 ≤ (‖x‖⁻¹) ^ 2 * -⟪C x, x⟫ * ‖x‖ ^ 2 := by gcongr
    _ = -⟪C x, x⟫ := by field_simp

private theorem exists_rayleigh_min {P C : E →L[ℝ] E} (hW : gapSpace P C ≠ ⊥) :
    ∃ e, e ∈ gapSpace P C ∧ ‖e‖ = 1 ∧ -⟪C e, e⟫ = relaxGap P C := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hne : {x | x ∈ gapSpace P C ∧ ‖x‖ = 1}.Nonempty := by
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine ⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  obtain ⟨e, he, hmin⟩ := (isCompact_gapSphere P C).exists_isMinOn hne
    (continuous_rayleigh C).continuousOn
  refine ⟨e, he.1, he.2, ?_⟩
  have hbdd := ((isCompact_gapSphere P C).image (continuous_rayleigh C)).bddBelow
  apply le_antisymm
  · refine le_csInf (hne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  · exact csInf_le hbdd (Set.mem_image_of_mem _ he)

/-- The spectral gap is automatically positive when `range P ⊖ K` is nontrivial: no assumption on
`C` beyond self-adjointness and `C ≤ 0` is needed, and no gap on `(ker C)ᗮ` is assumed. -/
theorem relaxGap_pos {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C)
    (hW : gapSpace P C ≠ ⊥) : 0 < relaxGap P C := by
  obtain ⟨e, he, hn, hval⟩ := exists_rayleigh_min hW
  rw [← hval]
  have h1 : ⟪C e, e⟫ ≤ 0 := hC.nonpos e
  rcases h1.lt_or_eq with h | h
  · linarith
  · exfalso
    have hCe := hC.apply_eq_zero h
    have hPe := ((mem_gapSpace_iff hP).1 he).1
    have hk : e ∈ apEquilibria P C := (mem_apEquilibria_iff hP).2 ⟨hPe, hCe⟩
    have h0 : ⟪e, e⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hk he.2
    rw [real_inner_self_eq_norm_sq, hn] at h0
    norm_num at h0

theorem relaxGap_nonneg {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) :
    0 ≤ relaxGap P C := by
  by_cases hW : gapSpace P C = ⊥
  · have : {x | x ∈ gapSpace P C ∧ ‖x‖ = 1} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, hW,
        Submodule.mem_bot]
      rintro rfl
      simp
    rw [relaxGap, this, Set.image_empty, Real.sInf_empty]
  · exact (relaxGap_pos hP hC hW).le

/-- The implicit Galerkin step `v = P (w + s (C v + F))` is uniquely solvable for all `s ≥ 0`. -/
theorem existsUnique_step {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {s : ℝ}
    (hs : 0 ≤ s) (w F : E) : ∃! v, v = P (w + s • (C v + F)) := by
  have hinj : ∀ x : E, x = s • P (C x) → P x = x → x = 0 := by
    intro x hx hPx
    have h := core_le (z := 0) hP hs le_rfl hPx (by rw [zero_add]; exact hx)
      (by simpa using hC.nonpos x)
    simpa using h
  let T : E →ₗ[ℝ] E := LinearMap.id - s • ((P : E →ₗ[ℝ] E) ∘ₗ (C : E →ₗ[ℝ] E) ∘ₗ (P : E →ₗ[ℝ] E))
  have hT : ∀ x, T x = x - s • P (C (P x)) := fun x => rfl
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hT, sub_eq_zero] at hx
    have hPx : P x = x := by
      have h := congrArg P hx
      rw [map_smul, hP.idem, ← hx] at h
      exact h
    rw [hPx] at hx
    exact hinj x hx hPx
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hTinj (P (w + s • F))
  rw [hT] at hv
  have hv' : v = P (w + s • F) + s • P (C (P v)) := by rw [← hv]; abel
  have hPv : P v = v := by
    have h := congrArg P hv'
    rw [map_add, map_smul, hP.idem, hP.idem, ← hv'] at h
    exact h
  rw [hPv] at hv'
  refine ⟨v, ?_, ?_⟩
  · change v = _
    conv_lhs => rw [hv']
    simp only [map_add, map_smul, smul_add]
    abel
  · intro v' hv''
    change v' = _ at hv''
    have hPv' : P v' = v' := by rw [hv'', hP.idem]
    have hdiff : v' - v = s • P (C (v' - v)) := by
      conv_lhs => rw [hv'', hv']
      simp only [map_add, map_smul, map_sub, smul_sub, smul_add]
      abel
    have := hinj (v' - v) hdiff (by rw [map_sub, hPv', hPv])
    exact sub_eq_zero.1 this

/-- **Lemma H with a source term.**  Let `C` be a relaxation operator, `P` an orthogonal projector,
`K = range P ⊓ ker C` and `γ` a coercivity constant of `-C` on `range P ⊖ K` (`relaxGap` is one, see
`relaxGap_mul_le`).  If `u ∈ range P ⊖ K` solves the Galerkin Chapman–Enskog problem
`P (C u + F) = 0`, then the implicit step `v = P (w + s (C v + F))` satisfies
`‖v - (P_K w + u)‖ ≤ ‖P w - P_K w - u‖ / (1 + s γ)`.

The source is what the application needs: in the micro-macro scheme the stiff drive `s F` does not
vanish, while `Lemma H` has no source and cannot see it. -/
theorem relax_le {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {γ : ℝ} (hγ : 0 ≤ γ)
    (hgap : ∀ x ∈ gapSpace P C, γ * ‖x‖ ^ 2 ≤ -⟪C x, x⟫) {s : ℝ} (hs : 0 ≤ s) {w F v u : E}
    (hv : v = P (w + s • (C v + F))) (hu : u ∈ gapSpace P C) (hF : P (C u + F) = 0) :
    ‖v - ((apEquilibria P C).starProjection w + u)‖ ≤
      ‖P w - (apEquilibria P C).starProjection w - u‖ / (1 + s * γ) := by
  set K := apEquilibria P C with hK
  set p := K.starProjection w with hp
  have hpK : p ∈ K := Submodule.starProjection_apply_mem K w
  obtain ⟨hPp, hCp⟩ := (mem_apEquilibria_iff hP).1 hpK
  obtain ⟨hPu, huK⟩ := (mem_gapSpace_iff hP).1 hu
  have hPv : P v = v := by rw [hv, hP.idem]
  set e := v - (p + u) with he
  have hPe : P e = e := by rw [he, map_sub, map_add, hPv, hPp, hPu]
  have hCv : C v = C e + C u := by
    have : v = e + p + u := by rw [he]; abel
    conv_lhs => rw [this]
    rw [map_add, map_add, hCp, add_zero]
  have hstep : v = P w + s • P (C e) := by
    have h1 : P (C v + F) = P (C e) := by
      rw [hCv, add_assoc, map_add, hF, add_zero]
    conv_lhs => rw [hv]
    rw [map_add, map_smul, h1]
  have heq : e = (P w - p - u) + s • P (C e) := by
    calc e = v - (p + u) := rfl
      _ = (P w + s • P (C e)) - (p + u) := congrArg (· - (p + u)) hstep
      _ = _ := by abel
  have heK : e ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    obtain ⟨hPk, hCk⟩ := (mem_apEquilibria_iff hP).1 hk
    have h1 : ⟪k, v⟫ = ⟪k, w⟫ := by
      have hkC : ∀ z, ⟪k, C z⟫ = 0 := fun z => by rw [← hC.symm, hCk, inner_zero_left]
      have hkF : ⟪k, F⟫ = 0 := by
        have h2 : ⟪k, C u + F⟫ = 0 := by rw [← hPk, hP.symm, hF, inner_zero_right]
        rwa [inner_add_right, hkC, zero_add] at h2
      conv_lhs => rw [hv, ← hP.symm, hPk]
      rw [inner_add_right, inner_smul_right, inner_add_right, hkC, hkF]
      simp
    have h2 : ⟪k, u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hk huK
    have h3 : ⟪k, w - p⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hk (Submodule.sub_starProjection_mem_orthogonal w)
    rw [he, inner_sub_right, inner_add_right, h1, h2]
    rw [inner_sub_right] at h3
    linarith
  have heW : e ∈ gapSpace P C := (mem_gapSpace_iff hP).2 ⟨hPe, heK⟩
  exact core_le hP hs hγ hPe heq (hgap e heW)

/-- `P_K (P w) = P_K w`, since `K ≤ range P`. -/
theorem starProjection_apply_of_le {P C : E →L[ℝ] E} (hP : IsOrthProj P) {w : E} :
    (apEquilibria P C).starProjection (P w) = (apEquilibria P C).starProjection w := by
  set K := apEquilibria P C with hK
  apply Submodule.eq_starProjection_of_mem_orthogonal (Submodule.starProjection_apply_mem K w)
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hPk := ((mem_apEquilibria_iff hP).1 hk).1
  have h3 : ⟪k, w - K.starProjection w⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hk (Submodule.sub_starProjection_mem_orthogonal w)
  have h4 : ⟪k, P w⟫ = ⟪k, w⟫ := by rw [← hP.symm, hPk]
  rw [inner_sub_right] at h3 ⊢
  rw [h4]
  exact h3

/-- **Lemma H**, in the sharper form with `‖P w - P_K w‖` in place of `‖P w‖`.  The
implicit Galerkin relaxation step `v = P (w + s C v)` with `C = Cᵀ ≤ 0` and `P` an orthogonal
projector satisfies `‖v - P_K w‖ ≤ ‖P w - P_K w‖ / (1 + s γ) ≤ ‖P w‖ / (1 + s γ)`, where
`K = range P ⊓ ker C` and `γ = relaxGap P C` is the (automatically positive) spectral gap.

This finite-dimensional statement is the core lemma proposed for OP-ST-07. -/
theorem lemmaH {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {s : ℝ} (hs : 0 ≤ s)
    {w v : E} (hv : v = P (w + s • C v)) :
    ‖v - (apEquilibria P C).starProjection w‖ ≤
        ‖P w - (apEquilibria P C).starProjection w‖ / (1 + s * relaxGap P C) ∧
      ‖P w - (apEquilibria P C).starProjection w‖ ≤ ‖P w‖ := by
  set K := apEquilibria P C with hK
  constructor
  · have h := relax_le hP hC (relaxGap_nonneg hP hC) (fun x hx => relaxGap_mul_le P C hx) hs
      (F := 0) (u := 0) (v := v) (w := w) (by simpa using hv) (Submodule.zero_mem _) (by simp)
    simpa using h
  · rw [← starProjection_apply_of_le hP]
    exact (isOrthProj_starProjection K).norm_sub_le (P w)

/-- `relax_le` for the spectral gap of `relaxGap`. -/
theorem relax_le_relaxGap {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {s : ℝ}
    (hs : 0 ≤ s) {w F v u : E} (hv : v = P (w + s • (C v + F))) (hu : u ∈ gapSpace P C)
    (hF : P (C u + F) = 0) :
    ‖v - ((apEquilibria P C).starProjection w + u)‖ ≤
      ‖P w - (apEquilibria P C).starProjection w - u‖ / (1 + s * relaxGap P C) :=
  relax_le hP hC (relaxGap_nonneg hP hC) (fun _ hx => relaxGap_mul_le P C hx) hs hv hu hF

/-- The rate of Lemma H is attained: when `range P ⊖ K` is nontrivial there is a unit vector
`e ∈ range P ⊖ K` with `P C e = -γ e`, for which the implicit step from `w = e` is exactly
`v = e / (1 + s γ)`, so the bound is an equality for every `s ≥ 0`. -/
theorem lemmaH_sharp {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C)
    (hW : gapSpace P C ≠ ⊥) :
    ∃ e ∈ gapSpace P C, ‖e‖ = 1 ∧ P (C e) = -(relaxGap P C • e) ∧
      (apEquilibria P C).starProjection e = 0 ∧
      ∀ s : ℝ, 0 ≤ s → ((1 + s * relaxGap P C)⁻¹ • e = P (e + s • C ((1 + s * relaxGap P C)⁻¹ • e))
        ∧ ‖(1 + s * relaxGap P C)⁻¹ • e - (apEquilibria P C).starProjection e‖ =
          ‖P e - (apEquilibria P C).starProjection e‖ / (1 + s * relaxGap P C)) := by
  set γ := relaxGap P C with hγdef
  have hγ : 0 < γ := relaxGap_pos hP hC hW
  obtain ⟨e, he, hn, hval⟩ := exists_rayleigh_min hW
  rw [← hγdef] at hval
  obtain ⟨hPe, heK⟩ := (mem_gapSpace_iff hP).1 he
  -- the quadratic form `q z = -⟪C z, z⟫ - γ ‖z‖²` is nonnegative on `W` and vanishes at `e`
  have hstat : ∀ y ∈ gapSpace P C, ⟪C e + γ • e, y⟫ = 0 := by
    intro y hy
    set b := ⟪C e + γ • e, y⟫ with hb
    set c := -⟪C y, y⟫ - γ * ‖y‖ ^ 2 with hc
    have hc0 : 0 ≤ c := by have := relaxGap_mul_le P C hy; linarith
    have hq : ∀ t : ℝ, 0 ≤ -2 * t * b + t ^ 2 * c := by
      intro t
      have hmem : e + t • y ∈ gapSpace P C := Submodule.add_mem _ he (Submodule.smul_mem _ _ hy)
      have h := relaxGap_mul_le P C hmem
      rw [← hγdef] at h
      have h1 : ⟪C (e + t • y), e + t • y⟫ =
          ⟪C e, e⟫ + 2 * t * ⟪C e, y⟫ + t ^ 2 * ⟪C y, y⟫ := by
        have h2 : ⟪C y, e⟫ = ⟪C e, y⟫ := by rw [hC.symm, real_inner_comm]
        rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
          real_inner_smul_right, h2]
        ring
      have h3 : ‖e + t • y‖ ^ 2 = ‖e‖ ^ 2 + 2 * t * ⟪e, y⟫ + t ^ 2 * ‖y‖ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
        ring
      rw [h1, h3, hn] at h
      have hbexp : b = ⟪C e, y⟫ + γ * ⟪e, y⟫ := by
        rw [hb, inner_add_left, real_inner_smul_left]
      rw [hbexp, hc]
      nlinarith
    have h1c : 0 < 1 + c := by linarith
    have := hq (b / (1 + c))
    have hval2 : -2 * (b / (1 + c)) * b + (b / (1 + c)) ^ 2 * c =
        -(b / (1 + c)) ^ 2 * (2 + c) := by
      field_simp
      ring
    rw [hval2] at this
    have h2c : 0 < 2 + c := by linarith
    have h0 : (b / (1 + c)) ^ 2 = 0 := by
      have : 0 ≤ (b / (1 + c)) ^ 2 := by positivity
      nlinarith
    have h00 : b / (1 + c) = 0 := by simpa using h0
    have := (div_eq_zero_iff.1 h00)
    rcases this with h | h
    · exact h
    · linarith
  set r := P (C e) + γ • e with hr
  have hPr : P r = r := by rw [hr, map_add, hP.idem, map_smul, hPe]
  have hrK : r ∈ (apEquilibria P C)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    obtain ⟨hPk, hCk⟩ := (mem_apEquilibria_iff hP).1 hk
    have h0 : ⟪k, e⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hk heK
    rw [hr, inner_add_right, real_inner_smul_right, h0, ← hP.symm, hPk, ← hC.symm, hCk]
    simp
  have hr0 : r = 0 := by
    have h := hstat r ((mem_gapSpace_iff hP).2 ⟨hPr, hrK⟩)
    have h2 : ⟪C e + γ • e, r⟫ = ⟪r, r⟫ := by
      conv_lhs => rw [← hPr, ← hP.symm, map_add, map_smul, hPe]
    rw [h2] at h
    exact inner_self_eq_zero.1 h
  have heig : P (C e) = -(γ • e) := eq_neg_of_add_eq_zero_left hr0
  have hpe : (apEquilibria P C).starProjection e = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 heK
  refine ⟨e, he, hn, heig, hpe, fun s hs => ?_⟩
  have h1 : 0 < 1 + s * γ := by positivity
  constructor
  · have hc : (1 + s * γ)⁻¹ = 1 - s * ((1 + s * γ)⁻¹ * γ) := by
      field_simp
      ring
    rw [map_add, hPe, map_smul, map_smul, map_smul, heig, smul_neg, smul_neg, smul_smul, smul_smul,
      ← sub_eq_add_neg]
    conv_lhs => rw [hc]
    rw [sub_smul, one_smul, mul_assoc]
  · rw [hpe, sub_zero, sub_zero, hPe, norm_smul, hn, mul_one, norm_inv, Real.norm_of_nonneg h1.le,
      one_div]

/-- **Solvability alternative.**  The `K`-component of the implicit step is
`P_K v = P_K w + s P_K F`: the stiff relaxation cannot touch it.  This is the discrete Fredholm
alternative in the Galerkin space. -/
theorem starProjection_step {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {s : ℝ}
    {w F v : E} (hv : v = P (w + s • (C v + F))) :
    (apEquilibria P C).starProjection v =
      (apEquilibria P C).starProjection w + s • (apEquilibria P C).starProjection F := by
  set K := apEquilibria P C with hK
  refine ext_inner_right ℝ fun z => ?_
  have hmem : K.starProjection z ∈ K := Submodule.starProjection_apply_mem K z
  obtain ⟨hPk, hCk⟩ := (mem_apEquilibria_iff hP).1 hmem
  have hkC : ⟪C v, K.starProjection z⟫ = 0 := by rw [hC.symm, hCk, inner_zero_right]
  rw [inner_add_left, real_inner_smul_left, Submodule.inner_starProjection_left_eq_right,
    Submodule.inner_starProjection_left_eq_right, Submodule.inner_starProjection_left_eq_right]
  conv_lhs => rw [hv, hP.symm, hPk]
  rw [inner_add_left, real_inner_smul_left, inner_add_left, hkC, zero_add]

/-- Failure of the solvability condition makes the implicit step blow up: if `P_K F ≠ 0`, no bound
uniform in `s` holds, since `s ‖P_K F‖ - ‖P_K w‖ ≤ ‖v‖`. -/
theorem norm_step_ge {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {s : ℝ}
    (hs : 0 ≤ s) {w F v : E} (hv : v = P (w + s • (C v + F))) :
    s * ‖(apEquilibria P C).starProjection F‖ - ‖(apEquilibria P C).starProjection w‖ ≤ ‖v‖ := by
  set K := apEquilibria P C with hK
  have h := starProjection_step hP hC hv
  rw [← hK] at h
  have h1 : ‖K.starProjection v‖ ≤ ‖v‖ := K.norm_starProjection_apply_le v
  have h2 : s • K.starProjection F = K.starProjection v - K.starProjection w := by
    rw [h]; abel
  have h3 : s * ‖K.starProjection F‖ = ‖K.starProjection v - K.starProjection w‖ := by
    rw [← h2, norm_smul, Real.norm_of_nonneg hs]
  have h4 := norm_sub_le (K.starProjection v) (K.starProjection w)
  linarith

/-- The Galerkin Chapman–Enskog problem `P (C u + F) = 0` has a unique solution `u` in
`range P ⊖ K` under the solvability condition `P_K F = 0` (which is also necessary, see
`starProjection_step`). -/
theorem existsUnique_chapmanEnskog {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C)
    {F : E} (hF : (apEquilibria P C).starProjection F = 0) :
    ∃! u, u ∈ gapSpace P C ∧ P (C u + F) = 0 := by
  set K := apEquilibria P C with hK
  have hzero : ∀ z, P (C z) = 0 → P z = z → C z = 0 := by
    intro z h1 h2
    refine hC.apply_eq_zero ?_
    have h3 : ⟪C z, z⟫ = ⟪P (C z), z⟫ := by rw [hP.symm, h2]
    rw [h3, h1, inner_zero_left]
  let T : E →ₗ[ℝ] E := (P : E →ₗ[ℝ] E) ∘ₗ (C : E →ₗ[ℝ] E) ∘ₗ (P : E →ₗ[ℝ] E)
  have hT : ∀ x, T x = P (C (P x)) := fun x => rfl
  have hTsym : T.IsSymmetric := by
    intro x y
    change ⟪T x, y⟫ = ⟪x, T y⟫
    rw [hT, hT, hP.symm, hC.symm, hP.symm]
  have hmem : P F ∈ LinearMap.range T := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range T), hTsym.orthogonal_range,
      Submodule.mem_orthogonal]
    intro z hz
    have h1 : P (C (P z)) = 0 := hz
    have hk : P z ∈ K := (mem_apEquilibria_iff hP).2 ⟨hP.idem z, hzero _ h1 (hP.idem z)⟩
    rw [← hP.symm, ← Submodule.starProjection_eq_self_iff.2 hk,
      Submodule.inner_starProjection_left_eq_right, hF, inner_zero_right]
  obtain ⟨y, hy⟩ := hmem
  rw [hT] at hy
  set p := K.starProjection (P y) with hp
  have hpK : p ∈ K := Submodule.starProjection_apply_mem K _
  obtain ⟨hPp, hCp⟩ := (mem_apEquilibria_iff hP).1 hpK
  refine ⟨-(P y - p), ⟨(mem_gapSpace_iff hP).2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [map_neg, map_sub, hP.idem, hPp]
  · exact Submodule.neg_mem _ (Submodule.sub_starProjection_mem_orthogonal _)
  · rw [map_neg, map_sub, hCp, sub_zero, map_add, map_neg, hy, neg_add_cancel]
  · rintro u' ⟨hu', hFu'⟩
    set u := -(P y - p) with hu
    have huW : u ∈ gapSpace P C := (mem_gapSpace_iff hP).2 ⟨by
      rw [hu, map_neg, map_sub, hP.idem, hPp], Submodule.neg_mem _
        (Submodule.sub_starProjection_mem_orthogonal _)⟩
    have hFu : P (C u + F) = 0 := by
      rw [hu, map_neg, map_sub, hCp, sub_zero, map_add, map_neg, hy, neg_add_cancel]
    have hdW : u' - u ∈ gapSpace P C := Submodule.sub_mem _ hu' huW
    obtain ⟨hPd, hdK⟩ := (mem_gapSpace_iff hP).1 hdW
    have hPCd : P (C (u' - u)) = 0 := by
      have : C (u' - u) = (C u' + F) - (C u + F) := by rw [map_sub]; abel
      rw [this, map_sub, hFu', hFu, sub_zero]
    have hk : u' - u ∈ K := (mem_apEquilibria_iff hP).2 ⟨hPd, hzero _ hPCd hPd⟩
    have h0 : ⟪u' - u, u' - u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hk hdK
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem tendsto_div_one_add_mul {c γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun s : ℝ => c / (1 + s * γ)) atTop (𝓝 0) := by
  refine Tendsto.const_div_atTop ?_ c
  exact tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hγ)

/-- The limit of the implicit Galerkin step with source, as `s → ∞`. -/
theorem relax_tendsto {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C) {w F u : E}
    (hu : u ∈ gapSpace P C) (hF : P (C u + F) = 0) {v : ℝ → E}
    (hv : ∀ s, 0 ≤ s → v s = P (w + s • (C (v s) + F))) :
    Tendsto v atTop (𝓝 ((apEquilibria P C).starProjection w + u)) := by
  set K := apEquilibria P C with hK
  set z := P w - K.starProjection w - u with hz
  have hzW : z ∈ gapSpace P C := by
    obtain ⟨hPu, huK⟩ := (mem_gapSpace_iff hP).1 hu
    have hmem : K.starProjection w ∈ K := Submodule.starProjection_apply_mem K w
    obtain ⟨hPk, -⟩ := (mem_apEquilibria_iff hP).1 hmem
    refine (mem_gapSpace_iff hP).2 ⟨by rw [hz, map_sub, map_sub, hP.idem, hPk, hPu], ?_⟩
    refine Submodule.sub_mem _ ?_ huK
    rw [← starProjection_apply_of_le (w := w) hP]
    exact Submodule.sub_starProjection_mem_orthogonal _
  have hbound : ∀ s, 0 ≤ s → ‖v s - (K.starProjection w + u)‖ ≤ ‖z‖ / (1 + s * relaxGap P C) :=
    fun s hs => relax_le_relaxGap hP hC hs (hv s hs) hu hF
  have hlim : Tendsto (fun s : ℝ => ‖z‖ / (1 + s * relaxGap P C)) atTop (𝓝 0) := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hW : gapSpace P C ≠ ⊥ := fun h => hz0 (by simpa [h] using hzW)
      exact tendsto_div_one_add_mul (relaxGap_pos hP hC hW)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' ?_ ?_ hlim)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 0] with s hs using hbound s hs

/-- Pointwise form of the "iff" of Lemma H: the Galerkin equilibrium projection of `w` is the true
equilibrium projection of `w` exactly when the latter lies in the Galerkin space.  This is the
version needed for the factors of a low-rank scheme, where `ker C ≤ range P` is far too strong
(see `IsBGK`). -/
theorem starProjection_eq_iff {P C : E →L[ℝ] E} (hP : IsOrthProj P) {w : E} :
    (apEquilibria P C).starProjection w = (LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w ↔
      P ((LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w) =
        (LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w := by
  set N := LinearMap.ker (C : E →ₗ[ℝ] E) with hN
  set K := apEquilibria P C with hK
  have hKN : K ≤ N := inf_le_right
  constructor
  · intro h
    rw [← h]
    exact ((mem_apEquilibria_iff hP).1 (Submodule.starProjection_apply_mem K w)).1
  · intro h
    have hq : N.starProjection w ∈ N := Submodule.starProjection_apply_mem N w
    have hmem : N.starProjection w ∈ K := (mem_apEquilibria_iff hP).2 ⟨h, hq⟩
    exact Submodule.eq_starProjection_of_mem_orthogonal hmem
      (Submodule.orthogonal_le hKN (Submodule.sub_starProjection_mem_orthogonal w))

/-- The "iff" of Lemma H: the implicit Galerkin relaxation reproduces the true equilibrium
projection for all data exactly when all equilibrium directions lie in the Galerkin space. -/
theorem forall_starProjection_eq_iff {P C : E →L[ℝ] E} (hP : IsOrthProj P) :
    (∀ w, (apEquilibria P C).starProjection w =
        (LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w) ↔
      LinearMap.ker (C : E →ₗ[ℝ] E) ≤ LinearMap.range (P : E →ₗ[ℝ] E) := by
  set N := LinearMap.ker (C : E →ₗ[ℝ] E) with hN
  constructor
  · intro h x hx
    have h1 := h x
    rw [Submodule.starProjection_eq_self_iff.2 hx] at h1
    rw [← h1]
    exact (Submodule.starProjection_apply_mem (apEquilibria P C) x).1
  · intro h w
    obtain ⟨z, hz⟩ := h (Submodule.starProjection_apply_mem N w)
    have hz' : P z = N.starProjection w := hz
    exact (starProjection_eq_iff hP).2 (by rw [← hz', hP.idem])

/-- **AP of the implicit Galerkin relaxation, as an equivalence.**  For a family `v s` of implicit
steps from `w`, `v s → P_{ker C} w` as `s → ∞` if and only if the true equilibrium `P_{ker C} w`
lies in the Galerkin space; the limit is always `P_K w`, and the rate is `1 / (1 + s γ)`
(`lemmaH`).  This is the abstract form of the asymptotic-preservation statement. -/
theorem tendsto_equilibrium_iff {P C : E →L[ℝ] E} (hP : IsOrthProj P) (hC : IsRelaxation C)
    {w : E} {v : ℝ → E} (hv : ∀ s, 0 ≤ s → v s = P (w + s • C (v s))) :
    Tendsto v atTop (𝓝 ((LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w)) ↔
      P ((LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w) =
        (LinearMap.ker (C : E →ₗ[ℝ] E)).starProjection w := by
  have hlim : Tendsto v atTop (𝓝 ((apEquilibria P C).starProjection w)) := by
    have h := relax_tendsto hP hC (F := 0) (u := 0) (w := w) (v := v) (Submodule.zero_mem _)
      (by simp) (by simpa using hv)
    simpa using h
  rw [← starProjection_eq_iff hP]
  constructor
  · intro h
    exact tendsto_nhds_unique hlim h
  · intro h
    rwa [← h]

end Abstract

section MicroMacro

open scoped LeanDLRA.Frobenius
open LeanDLRA.Frobenius

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]
  [DecidableEq m]

/-- The bounds `0 < σ₀ ≤ σ ≤ σ₁` on the scattering cross-section. -/
structure IsCrossSection (σ : m → ℝ) (σ₀ σ₁ : ℝ) : Prop where
  pos : 0 < σ₀
  le : σ₀ ≤ σ₁
  lower : ∀ i, σ₀ ≤ σ i
  upper : ∀ i, σ i ≤ σ₁

/-- The scattering term `g ↦ -σ g` on the micro variable `g`, an operator on `ℝ^{m × n}`. -/
noncomputable def scatter (σ : m → ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  -Frobenius.leftMulCLM (Matrix.diagonal σ)

@[simp] theorem scatter_apply (σ : m → ℝ) (Z : Matrix m n ℝ) :
    scatter σ Z = -(Matrix.diagonal σ * Z) := rfl

theorem inner_diagonal_mul (σ : m → ℝ) (Y Z : Matrix m r ℝ) :
    ⟪Matrix.diagonal σ * Y, Z⟫ = ∑ i, ∑ j, σ i * (Y i j * Z i j) := by
  rw [inner_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul]
  ring

theorem inner_diagonal_comm (σ : m → ℝ) (Y Z : Matrix m r ℝ) :
    ⟪Matrix.diagonal σ * Y, Z⟫ = ⟪Y, Matrix.diagonal σ * Z⟫ := by
  rw [inner_diagonal_mul, real_inner_comm, inner_diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem IsCrossSection.lower_inner {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    (Z : Matrix m r ℝ) : σ₀ * ‖Z‖ ^ 2 ≤ ⟪Matrix.diagonal σ * Z, Z⟫ := by
  rw [inner_diagonal_mul, norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := hσ.lower i
  nlinarith [sq_nonneg (Z i j)]

theorem IsCrossSection.upper_inner {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    (Z : Matrix m r ℝ) : ⟪Matrix.diagonal σ * Z, Z⟫ ≤ σ₁ * ‖Z‖ ^ 2 := by
  rw [inner_diagonal_mul, norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have := hσ.upper i
  nlinarith [sq_nonneg (Z i j)]

theorem IsCrossSection.norm_diagonal_mul_le {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) (Z : Matrix m r ℝ) :
    ‖Matrix.diagonal σ * Z‖ ≤ σ₁ * ‖Z‖ := by
  have hσ₁ : 0 ≤ σ₁ := hσ.pos.le.trans hσ.le
  have hsq : ‖Matrix.diagonal σ * Z‖ ^ 2 ≤ (σ₁ * ‖Z‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.diagonal_mul, mul_pow]
    have h1 : σ i ^ 2 ≤ σ₁ ^ 2 := by
      have h2 := hσ.pos.le.trans (hσ.lower i)
      have h3 := hσ.upper i
      nlinarith
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

/-! The Galerkin projector `Z ↦ Y Yᵀ Z W Wᵀ` onto `range Y ⊗ range W` is the core
`LeanDLRA.galerkinProj` (`galerkinProj_apply`, `isOrthProj_galerkinProj`); the local copy of an
earlier version of this file was the same definition (unification batch C2). -/

/-- The Galerkin limit `-φ aᵀ W Wᵀ` lies in the Galerkin space and solves the limit problem. -/
private theorem galerkin_limit_props [DecidableEq q] {σ : m → ℝ} {Y : Matrix m p ℝ}
    {W : Matrix n q ℝ} (hW : Wᵀ * W = 1) {d φ : Matrix m Unit ℝ} {a : Matrix n Unit ℝ}
    (hφY : Y * Yᵀ * φ = φ) (hφ : Yᵀ * (Matrix.diagonal σ * φ) = Yᵀ * d) :
    galerkinProj Y W (-(φ * (aᵀ * W * Wᵀ))) = -(φ * (aᵀ * W * Wᵀ)) ∧
      galerkinProj Y W (scatter σ (-(φ * (aᵀ * W * Wᵀ))) + -(d * aᵀ)) = 0 := by
  have hAA : aᵀ * W * Wᵀ * (W * Wᵀ) = aᵀ * W * Wᵀ := by
    rw [Matrix.mul_assoc _ Wᵀ, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul]
  have hA' : aᵀ * (W * Wᵀ) = aᵀ * W * Wᵀ := by rw [Matrix.mul_assoc]
  set A := aᵀ * W * Wᵀ with hA
  constructor
  · rw [galerkinProj_apply, Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    calc Y * Yᵀ * (φ * A) * (W * Wᵀ) = (Y * Yᵀ * φ) * (A * (W * Wᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = φ * A := by rw [hφY, hAA]
  · have h1 : galerkinProj Y W (scatter σ (-(φ * A)) + -(d * aᵀ)) =
        Y * (Yᵀ * (Matrix.diagonal σ * φ)) * (A * (W * Wᵀ)) -
          Y * (Yᵀ * d) * (aᵀ * (W * Wᵀ)) := by
      rw [galerkinProj_apply, scatter_apply]
      simp only [Matrix.mul_neg, neg_neg, Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul,
        Matrix.mul_assoc, sub_eq_add_neg]
    rw [h1, hφ, hAA, hA', sub_self]

/-- One Galerkin relaxation step on `range Y ⊗ range W` with drive `d aᵀ`.  All three substeps of
the BUG integrator are of this form. If `φ ∈ range Y` satisfies `Yᵀ σ φ = Yᵀ d`, the limit of the
step is `-φ aᵀ W Wᵀ` and the contraction factor is `1 / (1 + s σ₀)`. -/
theorem galerkin_step_le [DecidableEq p] [DecidableEq q] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ}
    {W : Matrix n q ℝ} (hY : Yᵀ * Y = 1) (hW : Wᵀ * W = 1)
    {d φ : Matrix m Unit ℝ} {a : Matrix n Unit ℝ} (hφY : Y * Yᵀ * φ = φ)
    (hφ : Yᵀ * (Matrix.diagonal σ * φ) = Yᵀ * d) {s : ℝ} (hs : 0 ≤ s) {w v : Matrix m n ℝ}
    (hv : v = galerkinProj Y W (w + s • (scatter σ v + -(d * aᵀ)))) :
    ‖v - -(φ * (aᵀ * W * Wᵀ))‖ ≤
      ‖galerkinProj Y W w - -(φ * (aᵀ * W * Wᵀ))‖ / (1 + s * σ₀) := by
  obtain ⟨h1, h2⟩ := galerkin_limit_props (σ := σ) (a := a) hW hφY hφ
  refine coercive_relax_le (isOrthProj_galerkinProj hY hW) hσ.pos.le ?_ hs hv h1 h2
  intro x _
  rw [scatter_apply, inner_neg_left, neg_neg]
  exact hσ.lower_inner x

/-- `Xᵀ σ X`, the matrix `⟨X Xᵀ σ⟩` of the paper. -/
noncomputable def stiffness (σ : m → ℝ) (Y : Matrix m p ℝ) : Matrix p p ℝ :=
  Yᵀ * Matrix.diagonal σ * Y

theorem IsCrossSection.lower_stiffness [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (Z : Matrix p r ℝ) :
    σ₀ * ‖Z‖ ^ 2 ≤ ⟪stiffness σ Y * Z, Z⟫ := by
  have h : ⟪stiffness σ Y * Z, Z⟫ = ⟪Matrix.diagonal σ * (Y * Z), Y * Z⟫ := by
    rw [stiffness, Matrix.mul_assoc, Matrix.mul_assoc, inner_mul_left, Matrix.transpose_transpose,
      inner_mul_right']
  rw [h, ← norm_mul_of_orthonormal hY Z]
  exact hσ.lower_inner _

omit [DecidableEq m] in
private theorem isUnit_of_coercive [DecidableEq p] {A : Matrix p p ℝ} {c : ℝ} (hc : 0 < c)
    (hA : ∀ Z : Matrix p Unit ℝ, c * ‖Z‖ ^ 2 ≤ ⟪A * Z, Z⟫) : IsUnit A := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  set Z : Matrix p Unit ℝ := Matrix.of (fun i (_ : Unit) => x i - y i) with hZ
  have hz : A * Z = 0 := by
    ext i j
    have h := congrFun hxy i
    rw [Matrix.zero_apply, Matrix.mul_apply]
    simp only [hZ, Matrix.of_apply, Matrix.mulVec, dotProduct] at h ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]
  have h := hA Z
  rw [hz, inner_zero_left] at h
  have h2 : ‖Z‖ ^ 2 = 0 := by
    have h3 : 0 ≤ ‖Z‖ ^ 2 := sq_nonneg _
    by_contra hne
    have h4 : 0 < ‖Z‖ ^ 2 := lt_of_le_of_ne h3 (Ne.symm hne)
    nlinarith
  have hz0 : Z = 0 := by simpa using h2
  ext i
  have := congrFun (congrFun hz0 i) ()
  simpa [hZ, sub_eq_zero] using this

/-- The stiffness matrix `⟨X Xᵀ σ⟩` is invertible. This, not any invertibility of `S_L`, is the
only inverse that the limit of the scheme needs. -/
theorem IsCrossSection.isUnit_stiffness [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) :
    IsUnit (stiffness σ Y) :=
  isUnit_of_coercive hσ.pos (hσ.lower_stiffness hY)

/-- The matrix `1 + s ⟨X Xᵀ σ⟩` of the implicit substeps is invertible. -/
theorem IsCrossSection.isUnit_one_add_stiffness [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) {s : ℝ} (hs : 0 ≤ s) :
    IsUnit (1 + s • stiffness σ Y) := by
  refine isUnit_of_coercive one_pos fun Z => ?_
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, one_mul]
  have h := hσ.lower_stiffness hY Z
  have h1 : 0 ≤ σ₀ * ‖Z‖ ^ 2 := by have := hσ.pos; positivity
  have h2 := mul_nonneg hs (h1.trans h)
  linarith

theorem stiffness_mul_inv [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) : stiffness σ Y * (stiffness σ Y)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hσ.isUnit_stiffness hY))

omit [Fintype p] in
theorem stiffness_transpose (σ : m → ℝ) (Y : Matrix m p ℝ) :
    (stiffness σ Y)ᵀ = stiffness σ Y := by
  simp [stiffness, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The transported Chapman–Enskog direction `σ⁻¹ d`, with `d = ∂ₓρ`. -/
noncomputable def ceDir (σ : m → ℝ) (d : Matrix m Unit ℝ) : Matrix m Unit ℝ :=
  Matrix.diagonal (fun i => (σ i)⁻¹) * d

theorem diagonal_mul_ceDir {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    (d : Matrix m Unit ℝ) : Matrix.diagonal σ * ceDir σ d = d := by
  have hne : ∀ i, σ i ≠ 0 := fun i => (hσ.pos.trans_le (hσ.lower i)).ne'
  rw [ceDir, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  have : (fun i => σ i * (σ i)⁻¹) = fun _ => (1 : ℝ) := by
    ext i
    exact mul_inv_cancel₀ (hne i)
  rw [this, Matrix.diagonal_one, Matrix.one_mul]

/-- The `σ`-weighted Galerkin projection `X ⟨X Xᵀ σ⟩⁻¹ ⟨X, d⟩` of `σ⁻¹ d` onto `range X`. -/
noncomputable def galerkinFlux [DecidableEq p] (σ : m → ℝ) (Y : Matrix m p ℝ)
    (d : Matrix m Unit ℝ) : Matrix m Unit ℝ :=
  Y * ((stiffness σ Y)⁻¹ * (Yᵀ * d))

theorem galerkinFlux_range [DecidableEq p] {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (σ : m → ℝ)
    (d : Matrix m Unit ℝ) : Y * Yᵀ * galerkinFlux σ Y d = galerkinFlux σ Y d := by
  rw [galerkinFlux, ← Matrix.mul_assoc, Matrix.mul_assoc Y, hY, Matrix.mul_one]

theorem galerkinFlux_orth [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (d : Matrix m Unit ℝ) :
    Yᵀ * (Matrix.diagonal σ * galerkinFlux σ Y d) = Yᵀ * d := by
  have h : Yᵀ * (Matrix.diagonal σ * galerkinFlux σ Y d) =
      stiffness σ Y * ((stiffness σ Y)⁻¹ * (Yᵀ * d)) := by
    simp only [galerkinFlux, stiffness, Matrix.mul_assoc]
  rw [h, ← Matrix.mul_assoc, stiffness_mul_inv hσ hY, Matrix.one_mul]

/-- `κ = √(σ₁ / σ₀)`, the factor by which the `σ`-weighted projection can exceed the orthogonal
one; `κ = 1` for constant cross-section. -/
noncomputable def kappa (σ₀ σ₁ : ℝ) : ℝ := √(σ₁ / σ₀)

omit [Fintype m] [DecidableEq m] in
theorem IsCrossSection.one_le_kappa {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁) :
    1 ≤ kappa σ₀ σ₁ := by
  rw [kappa, Real.one_le_sqrt, one_le_div hσ.pos]
  exact hσ.le

private theorem le_kappa_mul {σ₀ σ₁ x z : ℝ} (h0 : 0 < σ₀) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (h : σ₀ * x ^ 2 ≤ σ₁ * z ^ 2) : x ≤ kappa σ₀ σ₁ * z := by
  have h1 : x ^ 2 ≤ (σ₁ / σ₀) * z ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h0]
    linarith
  calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ √((σ₁ / σ₀) * z ^ 2) := Real.sqrt_le_sqrt h1
    _ = kappa σ₀ σ₁ * z := by rw [Real.sqrt_mul' _ (sq_nonneg z), Real.sqrt_sq hz, kappa]

/-- Pythagoras for the `σ`-weighted inner product. -/
private theorem weighted_pythagoras {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    {e y : Matrix m r ℝ} (h : ⟪Matrix.diagonal σ * e, y⟫ = 0) :
    σ₀ * ‖e‖ ^ 2 ≤ σ₁ * ‖e + y‖ ^ 2 ∧ σ₀ * ‖y‖ ^ 2 ≤ σ₁ * ‖e + y‖ ^ 2 := by
  have h1 := hσ.upper_inner (e + y)
  have h2 : ⟪Matrix.diagonal σ * (e + y), e + y⟫ =
      ⟪Matrix.diagonal σ * e, e⟫ + ⟪Matrix.diagonal σ * y, y⟫ := by
    have h3 : ⟪Matrix.diagonal σ * y, e⟫ = 0 := by
      rw [inner_diagonal_comm, real_inner_comm, h]
    rw [Matrix.mul_add, inner_add_left, inner_add_right, inner_add_right, h, h3]
    ring
  have h4 := hσ.lower_inner e
  have h5 := hσ.lower_inner y
  have h6 : 0 ≤ σ₀ * ‖e‖ ^ 2 := by have := hσ.pos; positivity
  have h7 : 0 ≤ σ₀ * ‖y‖ ^ 2 := by have := hσ.pos; positivity
  constructor <;> linarith

private theorem galerkin_orth [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (d : Matrix m Unit ℝ)
    (c : Matrix p Unit ℝ) :
    ⟪Matrix.diagonal σ * (ceDir σ d - galerkinFlux σ Y d), Y * c⟫ = 0 := by
  have h : Yᵀ * (Matrix.diagonal σ * (ceDir σ d - galerkinFlux σ Y d)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, diagonal_mul_ceDir hσ, galerkinFlux_orth hσ hY, sub_self]
  rw [inner_mul_left', h, inner_zero_left]

/-- **Céa's lemma for the `σ`-weighted projection**: the Galerkin flux is quasi-optimal in the
Euclidean norm, with constant `κ = √(σ₁ / σ₀)`. -/
theorem norm_sub_galerkinFlux_le [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (d : Matrix m Unit ℝ) :
    ‖ceDir σ d - galerkinFlux σ Y d‖ ≤ kappa σ₀ σ₁ * ‖ceDir σ d - Y * Yᵀ * ceDir σ d‖ := by
  set u := ceDir σ d with hu
  set φ := galerkinFlux σ Y d with hφ
  have hrange : φ - Y * Yᵀ * u = Y * ((stiffness σ Y)⁻¹ * (Yᵀ * d) - Yᵀ * u) := by
    rw [Matrix.mul_sub, hφ, galerkinFlux, Matrix.mul_assoc]
  have h := galerkin_orth hσ hY d ((stiffness σ Y)⁻¹ * (Yᵀ * d) - Yᵀ * u)
  rw [← hrange, ← hu, ← hφ] at h
  have hsum : (u - φ) + (φ - Y * Yᵀ * u) = u - Y * Yᵀ * u := by abel
  have h2 := (weighted_pythagoras hσ h).1
  rw [hsum] at h2
  exact le_kappa_mul hσ.pos (norm_nonneg _) (norm_nonneg _) h2

theorem norm_galerkinFlux_le [DecidableEq p] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} (hY : Yᵀ * Y = 1) (d : Matrix m Unit ℝ) :
    ‖galerkinFlux σ Y d‖ ≤ kappa σ₀ σ₁ * ‖ceDir σ d‖ := by
  have h := galerkin_orth hσ hY d ((stiffness σ Y)⁻¹ * (Yᵀ * d))
  have h1 : Y * ((stiffness σ Y)⁻¹ * (Yᵀ * d)) = galerkinFlux σ Y d := rfl
  rw [h1] at h
  have h2 := (weighted_pythagoras hσ h).2
  rw [sub_add_cancel] at h2
  exact le_kappa_mul hσ.pos (norm_nonneg _) (norm_nonneg _) h2

omit [DecidableEq m] in
private theorem norm_limit_le [DecidableEq q] {W : Matrix n q ℝ} (hW : Wᵀ * W = 1)
    (φ : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) : ‖φ * (aᵀ * W * Wᵀ)‖ ≤ ‖φ‖ * ‖a‖ := by
  refine (Frobenius.norm_mul_le _ _).trans ?_
  gcongr
  rw [norm_mul_transpose_of_orthonormal hW, ← norm_transpose a]
  exact norm_mul_le_of_orthonormal hW _

/-- The size bound `Φ` of one substep: `Φ = (B + (dt/ε) τ B + F) / (1 + (dt/ε²) σ₀)`, where `B`
bounds the old iterate, `τ` the transport operator and `F` the limit. -/
noncomputable def apPhi (dt ε σ₀ τ B F : ℝ) : ℝ :=
  (B + dt / ε * τ * B + F) / (1 + dt / ε ^ 2 * σ₀)

/-- `Φ` is `O(ε)` and not better in general: the `ε²/dt` is only the first term,
the second comes from the explicit `1/ε` transport.  With no transport (`τ = 0`), `Φ = O(ε²/dt)`. -/
theorem apPhi_le {dt ε σ₀ τ B F : ℝ} (hdt : 0 < dt) (hε : 0 < ε) (hσ₀ : 0 < σ₀) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hF : 0 ≤ F) :
    apPhi dt ε σ₀ τ B F ≤ ε ^ 2 / (dt * σ₀) * (B + F) + ε / σ₀ * (τ * B) := by
  have hden : 0 < 1 + dt / ε ^ 2 * σ₀ := by positivity
  rw [apPhi, div_le_iff₀ hden]
  have h1 : ε ^ 2 / (dt * σ₀) * (dt / ε ^ 2 * σ₀) = 1 := by field_simp
  have h2 : ε / σ₀ * (dt / ε ^ 2 * σ₀) = dt / ε := by field_simp
  have h3 : 0 ≤ ε ^ 2 / (dt * σ₀) * (B + F) := by positivity
  have h4 : 0 ≤ ε / σ₀ * (τ * B) := by positivity
  calc B + dt / ε * τ * B + F
      = (ε ^ 2 / (dt * σ₀) * (dt / ε ^ 2 * σ₀)) * (B + F) +
        (ε / σ₀ * (dt / ε ^ 2 * σ₀)) * (τ * B) := by rw [h1, h2]; ring
    _ ≤ (ε ^ 2 / (dt * σ₀) * (B + F) + ε / σ₀ * (τ * B)) * (1 + dt / ε ^ 2 * σ₀) := by nlinarith

/-- One implicit substep is within `Φ` of its limit. -/
private theorem substep_le [DecidableEq p] [DecidableEq q] {σ : m → ℝ} {σ₀ σ₁ : ℝ}
    (hσ : IsCrossSection σ σ₀ σ₁) {Y : Matrix m p ℝ} {W : Matrix n q ℝ} (hY : Yᵀ * Y = 1)
    (hW : Wᵀ * W = 1) {d φ : Matrix m Unit ℝ} {a : Matrix n Unit ℝ} (hφY : Y * Yᵀ * φ = φ)
    (hφ : Yᵀ * (Matrix.diagonal σ * φ) = Yᵀ * d) {𝒯 : Matrix m n ℝ → Matrix m n ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) {dt ε : ℝ} (hdt : 0 < dt) (hε : 0 < ε)
    {w₀ v : Matrix m n ℝ} {B F : ℝ} (hB : ‖w₀‖ ≤ B) (hF : ‖φ‖ * ‖a‖ ≤ F)
    (hv : v = galerkinProj Y W ((w₀ - (dt / ε) • 𝒯 w₀) +
      (dt / ε ^ 2) • (scatter σ v + -(d * aᵀ)))) :
    ‖v - -(φ * (aᵀ * W * Wᵀ))‖ ≤ apPhi dt ε σ₀ τ B F := by
  have ht : 0 ≤ dt / ε := by positivity
  have hs : 0 ≤ dt / ε ^ 2 := by positivity
  have h := galerkin_step_le hσ hY hW hφY hφ hs hv
  refine h.trans ?_
  rw [apPhi]
  gcongr
  · have := hσ.pos
    positivity
  rw [sub_neg_eq_add]
  refine (norm_add_le _ _).trans ?_
  have hP := isOrthProj_galerkinProj (n := n) hY hW
  have h1 : ‖galerkinProj Y W (w₀ - (dt / ε) • 𝒯 w₀)‖ ≤ B + dt / ε * τ * B := by
    refine (hP.norm_le _).trans ((norm_sub_le _ _).trans ?_)
    rw [norm_smul, Real.norm_of_nonneg ht]
    have h2 : ‖𝒯 w₀‖ ≤ τ * B := (hτ w₀).trans (by gcongr)
    have h3 := mul_le_mul_of_nonneg_left h2 ht
    nlinarith
  have h4 := (norm_limit_le hW φ a).trans hF
  linarith

/-- **One step of the micro-macro BUG scheme** of Einkemmer–Hu–Kusch, arXiv 2212.12012, equations
(4.4), (4.6), (4.8), for `∂ₜ g = -ε⁻¹ 𝒯 g - ε⁻² d aᵀ - ε⁻² σ g`, on matrices `g ∈ ℝ^{m × n}` (space
× moments) with `d = ∂ₓρⁿ`, `σ` a diagonal matrix, and `𝒯 g = ∂ₓ g A` any transport operator.
`K₁` and `L₁` are the implicit `K`- and `L`-step values; `X₁`, `V₁` are any orthonormal bases
capturing them (a QR factorisation, possibly augmented: the number of columns is free); `S₁` is the
implicit `S`-step value started from `S̃ = X₁ᵀ Xⁿ Sⁿ Vⁿᵀ V₁`.

The `L`-step follows the fully discrete §5.2 of the paper, with `⟨X Xᵀ σ⟩` once: (4.5)–(4.6) print
a second factor `σ` in front of the bracket. -/
structure IsMicroMacroBUGStep [DecidableEq r] [DecidableEq p] [DecidableEq q] (σ : m → ℝ)
    (𝒯 : Matrix m n ℝ → Matrix m n ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) (dt ε : ℝ)
    (X : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ)
    (K₁ : Matrix m r ℝ) (L₁ : Matrix n r ℝ)
    (X₁ : Matrix m p ℝ) (V₁ : Matrix n q ℝ) (S₁ : Matrix p q ℝ) : Prop where
  hX : Xᵀ * X = 1
  hV : Vᵀ * V = 1
  hX₁ : X₁ᵀ * X₁ = 1
  hV₁ : V₁ᵀ * V₁ = 1
  kStep : K₁ = X * S - (dt / ε) • (𝒯 (X * S * Vᵀ) * V)
    - (dt / ε ^ 2) • (d * (aᵀ * V) + Matrix.diagonal σ * K₁)
  lStep : L₁ = V * Sᵀ - (dt / ε) • ((𝒯 (X * S * Vᵀ))ᵀ * X)
    - (dt / ε ^ 2) • (a * (dᵀ * X) + L₁ * stiffness σ X)
  kCap : X₁ * X₁ᵀ * K₁ = K₁
  lCap : V₁ * V₁ᵀ * L₁ = L₁
  sStep : S₁ = X₁ᵀ * (X * S * Vᵀ) * V₁
    - (dt / ε) • (X₁ᵀ * 𝒯 (X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ)) * V₁)
    - (dt / ε ^ 2) • (X₁ᵀ * d * (aᵀ * V₁) + stiffness σ X₁ * S₁)

namespace IsMicroMacroBUGStep

variable [DecidableEq r] [DecidableEq p] [DecidableEq q] {σ : m → ℝ}
  {𝒯 : Matrix m n ℝ → Matrix m n ℝ} {d : Matrix m Unit ℝ} {a : Matrix n Unit ℝ} {dt ε : ℝ}
  {X : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} {K₁ : Matrix m r ℝ} {L₁ : Matrix n r ℝ}
  {X₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ} {S₁ : Matrix p q ℝ}

/-- The `K`-step is the Galerkin relaxation on `ℝ^m ⊗ range V`. -/
theorem kLift (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    K₁ * Vᵀ = galerkinProj (1 : Matrix m m ℝ) V ((X * S * Vᵀ - (dt / ε) • 𝒯 (X * S * Vᵀ)) +
      (dt / ε ^ 2) • (scatter σ (K₁ * Vᵀ) + -(d * aᵀ))) := by
  have hVV : Vᵀ * (V * Vᵀ) = Vᵀ := by rw [← Matrix.mul_assoc, h.hV, Matrix.one_mul]
  rw [galerkinProj_apply, scatter_apply]
  conv_lhs => rw [h.kStep]
  simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul, Matrix.sub_mul, Matrix.add_mul,
    Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_assoc, hVV]
  simp only [sub_eq_add_neg, smul_add, smul_neg]
  abel

/-- The `L`-step is the Galerkin relaxation on `range X ⊗ ℝⁿ`. -/
theorem lLift [DecidableEq n]
    (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    X * L₁ᵀ = galerkinProj X (1 : Matrix n n ℝ) ((X * S * Vᵀ - (dt / ε) • 𝒯 (X * S * Vᵀ)) +
      (dt / ε ^ 2) • (scatter σ (X * L₁ᵀ) + -(d * aᵀ))) := by
  have hL : L₁ᵀ = S * Vᵀ - (dt / ε) • (Xᵀ * 𝒯 (X * S * Vᵀ)) -
      (dt / ε ^ 2) • (Xᵀ * d * aᵀ + stiffness σ X * L₁ᵀ) := by
    have h1 := congrArg Matrix.transpose h.lStep
    simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_mul, Matrix.transpose_transpose, stiffness_transpose] using h1
  have hXX : Xᵀ * (X * (S * Vᵀ)) = S * Vᵀ := by rw [← Matrix.mul_assoc, h.hX, Matrix.one_mul]
  rw [galerkinProj_apply, scatter_apply]
  conv_lhs => rw [hL]
  simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.mul_assoc, stiffness, hXX]
  simp only [sub_eq_add_neg, smul_add, smul_neg]
  abel

/-- The `S`-step is the Galerkin relaxation on `range X₁ ⊗ range V₁`. -/
theorem sLift (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    X₁ * S₁ * V₁ᵀ = galerkinProj X₁ V₁
      ((X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ) -
          (dt / ε) • 𝒯 (X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ))) +
        (dt / ε ^ 2) • (scatter σ (X₁ * S₁ * V₁ᵀ) + -(d * aᵀ))) := by
  have hS := h.sStep
  have hXZ : ∀ Z : Matrix p n ℝ, X₁ᵀ * (X₁ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h.hX₁, Matrix.one_mul]
  have hVV : V₁ᵀ * (V₁ * V₁ᵀ) = V₁ᵀ := by rw [← Matrix.mul_assoc, h.hV₁, Matrix.one_mul]
  generalize X * S * Vᵀ = g at hS ⊢
  generalize 𝒯 (X₁ * X₁ᵀ * g * (V₁ * V₁ᵀ)) = T at hS ⊢
  rw [galerkinProj_apply, scatter_apply]
  conv_lhs => rw [hS]
  simp only [stiffness, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hXZ, hVV]
  simp only [sub_eq_add_neg, smul_add, smul_neg]
  abel

/-- The norm of the old iterate is `‖S‖`. -/
theorem norm_iterate (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖X * S * Vᵀ‖ = ‖S‖ := by
  rw [norm_mul_transpose_of_orthonormal h.hV, norm_mul_of_orthonormal h.hX]

end IsMicroMacroBUGStep

/-- The limit `K₀ = -σ⁻¹ ∂ₓρ aᵀ V` of the `K`-step, of rank at most one. -/
noncomputable def kLimit (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (V : Matrix n r ℝ) : Matrix m r ℝ :=
  -(ceDir σ d * (aᵀ * V))

/-- The coefficient `c = ⟨X Xᵀ σ⟩⁻¹ ⟨∂ₓρ, X⟩` of the limit of the `L`-step. -/
noncomputable def lCoeff [DecidableEq r] (σ : m → ℝ) (d : Matrix m Unit ℝ) (X : Matrix m r ℝ) :
    Matrix r Unit ℝ :=
  (stiffness σ X)⁻¹ * (Xᵀ * d)

/-- The limit `L₀ = -a cᵀ` of the `L`-step, of rank at most one. -/
noncomputable def lLimit [DecidableEq r] (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (X : Matrix m r ℝ) : Matrix n r ℝ :=
  -(a * (lCoeff σ d X)ᵀ)

/-- The limit `S₀ = -⟨X₁ X₁ᵀ σ⟩⁻¹ ⟨∂ₓρ, X₁⟩ (aᵀ V₁)` of the `S`-step: this is the limiting equation
(4.10) of the paper, and it needs no hypothesis to be solvable. -/
noncomputable def sLimit [DecidableEq p] (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (X₁ : Matrix m p ℝ) (V₁ : Matrix n q ℝ) : Matrix p q ℝ :=
  -(lCoeff σ d X₁ * (aᵀ * V₁))

/-- The diffusive flux `G = -σ⁻¹ ∂ₓρ aᵀ` of the limit equation. -/
noncomputable def diffFlux (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) :
    Matrix m n ℝ :=
  -(ceDir σ d * aᵀ)

/-- The Galerkin limit `X₁ S₀ V₁ᵀ` in closed form: the `σ`-weighted projection of `σ⁻¹ d` onto
`range X₁`, tensored with the orthogonal projection of `a` onto `range V₁`. -/
theorem mul_sLimit_mul [DecidableEq p] (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (X₁ : Matrix m p ℝ) (V₁ : Matrix n q ℝ) :
    X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ = -(galerkinFlux σ X₁ d * (aᵀ * V₁ * V₁ᵀ)) := by
  simp only [sLimit, lCoeff, galerkinFlux, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- `bᵀ b = ‖b‖²` for a column vector. -/
theorem transpose_mul_self_col (b : Matrix r Unit ℝ) :
    bᵀ * b = (‖b‖ ^ 2) • (1 : Matrix Unit Unit ℝ) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.mul_apply, norm_sq_eq_sum]
  simp [sq]

omit [DecidableEq m] in
/-- The Frobenius norm of a rank-one matrix `x aᵀ`. -/
theorem norm_mul_transpose_col (x : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) :
    ‖x * aᵀ‖ = ‖x‖ * ‖a‖ := by
  have h : ‖x * aᵀ‖ ^ 2 = (‖x‖ * ‖a‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, norm_sq_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply, mul_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

omit [DecidableEq m] in
/-- **The inverse-free capture estimate.**  If `Q` captures `K`, and `K` is close to the rank-one
matrix `-x bᵀ`, then `x` is close to `range Q`, with a constant that blows up only as `b → 0`.  No
inverse of any coefficient matrix is taken. -/
theorem capture_le [DecidableEq p] {Q : Matrix m p ℝ} (hQ : Qᵀ * Q = 1) {K : Matrix m r ℝ}
    {x : Matrix m Unit ℝ} {b : Matrix r Unit ℝ} (hcap : Q * Qᵀ * K = K) :
    ‖b‖ * ‖x - Q * Qᵀ * x‖ ≤ ‖K - -(x * bᵀ)‖ := by
  set Z := K - -(x * bᵀ) with hZ
  have hZb : Z * b = K * b + (‖b‖ ^ 2) • x := by
    rw [hZ, sub_neg_eq_add, Matrix.add_mul, Matrix.mul_assoc x, transpose_mul_self_col,
      Matrix.mul_smul, Matrix.mul_one]
  have h1 : Z * b - Q * Qᵀ * (Z * b) = (‖b‖ ^ 2) • (x - Q * Qᵀ * x) := by
    have hK : Q * Qᵀ * (K * b) = K * b := by rw [← Matrix.mul_assoc, hcap]
    rw [hZb, Matrix.mul_add, hK, Matrix.mul_smul, smul_sub]
    abel
  have h2 : ‖Z * b - Q * Qᵀ * (Z * b)‖ ≤ ‖Z * b‖ := by
    simpa using (isOrthProj_leftProj (n := Unit) hQ).norm_sub_le (Z * b)
  have h3 : ‖Z * b‖ ≤ ‖Z‖ * ‖b‖ := Frobenius.norm_mul_le _ _
  rw [h1, norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  by_cases hb : ‖b‖ = 0
  · rw [hb, zero_mul]
    exact norm_nonneg _
  · have hb' : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
    have h4 : ‖b‖ * (‖b‖ * ‖x - Q * Qᵀ * x‖) ≤ ‖b‖ * ‖Z‖ := by nlinarith
    exact le_of_mul_le_mul_left h4 hb'

omit [DecidableEq m] in
/-- A matrix in `range Y ⊗ range W` is far from `x bᵀ` unless `x ∈ range Y` and `b ∈ range W`. -/
theorem rank_one_defect_le {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {Y : Matrix m k ℝ} {W : Matrix n k' ℝ} (hY : Yᵀ * Y = 1) (hW : Wᵀ * W = 1)
    (B : Matrix k k' ℝ) (x : Matrix m Unit ℝ) (b : Matrix n Unit ℝ) :
    ‖x - Y * Yᵀ * x‖ * ‖b‖ ≤ ‖Y * B * Wᵀ - x * bᵀ‖ ∧
      ‖x‖ * ‖b - W * Wᵀ * b‖ ≤ ‖Y * B * Wᵀ - x * bᵀ‖ := by
  set Z := Y * B * Wᵀ - x * bᵀ with hZ
  constructor
  · have h := (isOrthProj_leftProj (n := n) hY).norm_sub_le Z
    have h1 : Z - leftProj Y Z = -((x - Y * Yᵀ * x) * bᵀ) := by
      have h2 : Y * Yᵀ * (Y * B * Wᵀ) = Y * B * Wᵀ := by
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc Y, hY, Matrix.mul_one]
      rw [leftProj_apply, hZ, Matrix.mul_sub, h2, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
      abel
    rw [h1, norm_neg, norm_mul_transpose_col] at h
    exact h
  · have h := (isOrthProj_rightProj (m := m) hW).norm_sub_le Z
    have h1 : Z - rightProj W Z = -(x * (b - W * Wᵀ * b)ᵀ) := by
      have h2 : Y * B * Wᵀ * W * Wᵀ = Y * B * Wᵀ := by
        rw [Matrix.mul_assoc (Y * B), hW, Matrix.mul_one]
      rw [rightProj_apply, hZ, Matrix.sub_mul, Matrix.sub_mul, h2, Matrix.transpose_sub,
        Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel
    rw [h1, norm_neg, norm_mul_transpose_col] at h
    exact h

section Limits

variable [DecidableEq r] [DecidableEq p] [DecidableEq q] {σ : m → ℝ}
  {σ₀ σ₁ : ℝ} {𝒯 : Matrix m n ℝ → Matrix m n ℝ} {τ : ℝ} {d : Matrix m Unit ℝ}
  {a : Matrix n Unit ℝ} {dt ε : ℝ} {X : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
  {K₁ : Matrix m r ℝ} {L₁ : Matrix n r ℝ} {X₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ}
  {S₁ : Matrix p q ℝ}

/-- **The `K`-step limit, with a rate.**  `‖K₁ - K₀‖ ≤ Φ`, where `K₀ = -σ⁻¹ ∂ₓρ aᵀ V`.  The limit
of the paper's proof of Theorem 4.1, made quantitative. -/
theorem kStep_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖K₁ - kLimit σ d a V‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have hone : (1 : Matrix m m ℝ)ᵀ * 1 = 1 := by simp
  have h1 := substep_le (φ := ceDir σ d) (F := kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) hσ hone h.hV
    (by simp) (by simp [diagonal_mul_ceDir hσ]) hτ0 hτ hdt hε h.norm_iterate.le ?_ h.kLift
  · have h2 : K₁ * Vᵀ - -(ceDir σ d * (aᵀ * V * Vᵀ)) = (K₁ - kLimit σ d a V) * Vᵀ := by
      simp only [kLimit, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc]
    rwa [h2, norm_mul_transpose_of_orthonormal h.hV] at h1
  · have := hσ.one_le_kappa
    have h3 : 0 ≤ ‖ceDir σ d‖ * ‖a‖ := by positivity
    nlinarith

/-- **The `L`-step limit, with a rate.**  `‖L₁ - L₀‖ ≤ Φ`, where `L₀ = -a cᵀ` and
`c = ⟨X Xᵀ σ⟩⁻¹ ⟨∂ₓρ, X⟩`. -/
theorem lStep_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖L₁ - lLimit σ d a X‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  classical
  have hone : (1 : Matrix n n ℝ)ᵀ * 1 = 1 := by simp
  have h1 := substep_le (φ := galerkinFlux σ X d) (F := kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) hσ h.hX
    hone (galerkinFlux_range h.hX σ d) (galerkinFlux_orth hσ h.hX d) hτ0 hτ hdt hε
    h.norm_iterate.le ?_ h.lLift
  · have h2 : X * L₁ᵀ - -(galerkinFlux σ X d * (aᵀ * (1 : Matrix n n ℝ) * (1 : Matrix n n ℝ)ᵀ)) =
        X * (L₁ - lLimit σ d a X)ᵀ := by
      simp only [lLimit, lCoeff, galerkinFlux, Matrix.transpose_sub, Matrix.transpose_neg,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub, Matrix.mul_neg,
        Matrix.mul_one, Matrix.transpose_one, Matrix.mul_assoc]
    rwa [h2, norm_mul_of_orthonormal h.hX, norm_transpose] at h1
  · have := norm_galerkinFlux_le hσ h.hX d
    gcongr

/-- **The `S`-step limit, with a rate.**  `‖S₁ - S₀‖ ≤ Φ` for any orthonormal bases `X₁`, `V₁`. -/
theorem sStep_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖S₁ - sLimit σ d a X₁ V₁‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have hB : ‖X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ)‖ ≤ ‖S‖ := by
    have hP := isOrthProj_galerkinProj (n := n) h.hX₁ h.hV₁
    have h2 := hP.norm_le (X * S * Vᵀ)
    rwa [galerkinProj_apply, h.norm_iterate] at h2
  have h1 := substep_le (φ := galerkinFlux σ X₁ d) (F := kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) hσ h.hX₁
    h.hV₁ (galerkinFlux_range h.hX₁ σ d) (galerkinFlux_orth hσ h.hX₁ d) hτ0 hτ hdt hε hB ?_ h.sLift
  · have h2 : X₁ * S₁ * V₁ᵀ - -(galerkinFlux σ X₁ d * (aᵀ * V₁ * V₁ᵀ)) =
        X₁ * (S₁ - sLimit σ d a X₁ V₁) * V₁ᵀ := by
      rw [← mul_sLimit_mul, Matrix.mul_sub, Matrix.sub_mul]
    rwa [h2, norm_mul_transpose_of_orthonormal h.hV₁, norm_mul_of_orthonormal h.hX₁] at h1
  · have := norm_galerkinFlux_le hσ h.hX₁ d
    gcongr

omit [DecidableEq r] in
/-- The limit of the `K`-step has rank at most one. -/
theorem rank_kLimit_le (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (V : Matrix n r ℝ) : (kLimit σ d a V).rank ≤ 1 := by
  rw [kLimit, ← Matrix.neg_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (-ceDir σ d))

omit [Fintype n] in
/-- The limit of the `L`-step has rank at most one. -/
theorem rank_lLimit_le (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ)
    (X : Matrix m r ℝ) : (lLimit σ d a X).rank ≤ 1 := by
  rw [lLimit, ← Matrix.neg_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (-a))

/-- **The hypothesis in the published proof can never hold for `r ≥ 2`.**  The proof of Theorem 4.1
of Einkemmer–Hu–Kusch, arXiv 2212.12012 assumes `L^{n+1} = V^{n+1} S_L` with
`S_L ⟨Xⁿ Xⁿᵀ σ⟩` invertible, where `L^{n+1}` is the limit of the `L`-step.  That limit has rank at
most one, so `S_L` has too, whatever the bases.  See `ap_step_le` for what replaces it. -/
theorem not_isUnit_of_lLimit_eq (hr : 2 ≤ Fintype.card r) {V₁ : Matrix n r ℝ}
    (hV₁ : V₁ᵀ * V₁ = 1) {SL : Matrix r r ℝ} (hL : lLimit σ d a X = V₁ * SL) (M : Matrix r r ℝ) :
    ¬ IsUnit (SL * M) := by
  intro hu
  have hSL : SL = V₁ᵀ * lLimit σ d a X := by rw [hL, ← Matrix.mul_assoc, hV₁, Matrix.one_mul]
  have h1 : (SL * M).rank ≤ 1 := by
    refine (Matrix.rank_mul_le_left _ _).trans ?_
    rw [hSL]
    exact (Matrix.rank_mul_le_right _ _).trans (rank_lLimit_le σ d a X)
  have h2 : (SL * M).rank = Fintype.card r := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact Matrix.rank_of_isUnit _ u.isUnit
  omega

omit [DecidableEq q] in
/-- The distance from `G` to the Galerkin limit `X₁ S₀ V₁ᵀ`, in terms of the capture defects. -/
theorem norm_sLimit_sub_le (hσ : IsCrossSection σ σ₀ σ₁) (hX₁ : X₁ᵀ * X₁ = 1) :
    ‖X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ - diffFlux σ d a‖ ≤
      kappa σ₀ σ₁ * (‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ * ‖a‖ +
        ‖ceDir σ d‖ * ‖a - V₁ * V₁ᵀ * a‖) := by
  have hdec : X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ - diffFlux σ d a =
      (ceDir σ d - galerkinFlux σ X₁ d) * aᵀ +
        galerkinFlux σ X₁ d * (a - V₁ * V₁ᵀ * a)ᵀ := by
    rw [mul_sLimit_mul, diffFlux, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, sub_eq_add_neg, neg_neg]
    abel
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul_transpose_col, norm_mul_transpose_col]
  have h1 := norm_sub_galerkinFlux_le hσ hX₁ d
  have h2 := norm_galerkinFlux_le hσ hX₁ d
  have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg a)
  have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (a - V₁ * V₁ᵀ * a))
  linarith

omit [DecidableEq r] in
/-- **Necessity, at every `ε`.**  The new iterate lies in `range X₁ ⊗ range V₁`, so its distance
to the diffusive flux `G` bounds both capture defects from above. No hypothesis on the step.  This
is the necessary half of the corrected Theorem I. -/
theorem capture_defect_le_norm (hX₁ : X₁ᵀ * X₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) (B : Matrix p q ℝ) :
    ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ * ‖a‖ ≤ ‖X₁ * B * V₁ᵀ - diffFlux σ d a‖ ∧
      ‖ceDir σ d‖ * ‖a - V₁ * V₁ᵀ * a‖ ≤ ‖X₁ * B * V₁ᵀ - diffFlux σ d a‖ := by
  have h := rank_one_defect_le (m := m) (n := n) hX₁ hV₁ B (-(ceDir σ d)) a
  have h2 : -(ceDir σ d) * aᵀ = diffFlux σ d a := by rw [diffFlux, Matrix.neg_mul]
  have h3 : -(ceDir σ d) - X₁ * X₁ᵀ * (-(ceDir σ d)) =
      -(ceDir σ d - X₁ * X₁ᵀ * ceDir σ d) := by
    rw [Matrix.mul_neg]
    abel
  rwa [h2, h3, norm_neg, norm_neg] at h

/-- **The replacement for the published hypothesis, `K`-step.**  If `aᵀ V ≠ 0`, any orthonormal
`X₁` capturing `K₁` (for instance a QR factor of `K₁`, of any rank) nearly contains `σ⁻¹ ∂ₓρ`:
`‖Vᵀ a‖ dist(σ⁻¹ ∂ₓρ, range X₁) ≤ Φ`. No invertibility is used, in place of the hypothesis of
arXiv 2212.12012, Thm 4.1.  Compare the assumption `(M1)ᵀ Vⁿ ≠ 0` of arXiv 2607.27736. -/
theorem capture_kStep (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖Vᵀ * a‖ * ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have h1 := capture_le (x := ceDir σ d) (b := Vᵀ * a) h.hX₁ h.kCap
  have h2 : -(ceDir σ d * (Vᵀ * a)ᵀ) = kLimit σ d a V := by
    rw [kLimit, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [h2] at h1
  exact h1.trans (kStep_le hσ hτ0 hτ hdt hε h)

theorem stiffness_mul_lCoeff (hσ : IsCrossSection σ σ₀ σ₁) (hX : Xᵀ * X = 1) :
    stiffness σ X * lCoeff σ d X = Xᵀ * d := by
  rw [lCoeff, ← Matrix.mul_assoc, stiffness_mul_inv hσ hX, Matrix.one_mul]

/-- `‖⟨∂ₓρ, X⟩‖ ≤ σ₁ ‖c‖`, so `c ≠ 0` as soon as `⟨∂ₓρ, X⟩ ≠ 0`. -/
theorem norm_transpose_mul_le_lCoeff (hσ : IsCrossSection σ σ₀ σ₁) (hX : Xᵀ * X = 1) :
    ‖Xᵀ * d‖ ≤ σ₁ * ‖lCoeff σ d X‖ := by
  rw [← stiffness_mul_lCoeff hσ hX, stiffness, Matrix.mul_assoc, Matrix.mul_assoc]
  refine (norm_transpose_mul_le hX _).trans ((hσ.norm_diagonal_mul_le _).trans ?_)
  rw [norm_mul_of_orthonormal hX]

/-- **The replacement for the published hypothesis, `L`-step.**  If `⟨∂ₓρ, X⟩ ≠ 0`, any
orthonormal `V₁` capturing `L₁` nearly contains `a`:
`‖⟨∂ₓρ, X⟩‖ dist(a, range V₁) ≤ σ₁ Φ`, in place of the hypothesis of arXiv 2212.12012, Thm 4.1. -/
theorem capture_lStep (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖Xᵀ * d‖ * ‖a - V₁ * V₁ᵀ * a‖ ≤
      σ₁ * apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have h1 := capture_le (x := a) (b := lCoeff σ d X) h.hV₁ h.lCap
  have h3 := (h1.trans_eq (by rfl : _ = ‖L₁ - lLimit σ d a X‖)).trans (lStep_le hσ hτ0 hτ hdt hε h)
  have h4 := norm_transpose_mul_le_lCoeff (d := d) hσ h.hX
  have hσ₁ : 0 ≤ σ₁ := hσ.pos.le.trans hσ.le
  calc ‖Xᵀ * d‖ * ‖a - V₁ * V₁ᵀ * a‖
      ≤ (σ₁ * ‖lCoeff σ d X‖) * ‖a - V₁ * V₁ᵀ * a‖ := by gcongr
    _ = σ₁ * (‖lCoeff σ d X‖ * ‖a - V₁ * V₁ᵀ * a‖) := by ring
    _ ≤ _ := by gcongr

/-- The new iterate is within `Φ` of the Galerkin limit `X₁ S₀ V₁ᵀ`. -/
theorem norm_iterate_sub_sLimit_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖X₁ * S₁ * V₁ᵀ - X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have h1 := sStep_le hσ hτ0 hτ hdt hε h
  have h2 : X₁ * S₁ * V₁ᵀ - X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ =
      X₁ * (S₁ - sLimit σ d a X₁ V₁) * V₁ᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [h2, norm_mul_transpose_of_orthonormal h.hV₁, norm_mul_of_orthonormal h.hX₁]

/-- **The upper half of the AP characterisation.**  For every step,
`‖g₁ - G‖ ≤ Φ + κ (‖a‖ dist(σ⁻¹ ∂ₓρ, range X₁) + ‖σ⁻¹ ∂ₓρ‖ dist(a, range V₁))`.
Together with `capture_defect_le_norm` this says that `g₁ → G` exactly when both defects vanish
in the limit (`tendsto_diffFlux_iff`). -/
theorem ap_step_bound (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    ‖X₁ * S₁ * V₁ᵀ - diffFlux σ d a‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) +
        kappa σ₀ σ₁ * (‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ * ‖a‖ +
          ‖ceDir σ d‖ * ‖a - V₁ * V₁ᵀ * a‖) := by
  have h1 := norm_iterate_sub_sLimit_le hσ hτ0 hτ hdt hε h
  have h2 := norm_sLimit_sub_le (d := d) (a := a) (V₁ := V₁) hσ h.hX₁
  calc ‖X₁ * S₁ * V₁ᵀ - diffFlux σ d a‖
      = ‖(X₁ * S₁ * V₁ᵀ - X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ) +
          (X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ - diffFlux σ d a)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)

/-- **Theorem I, corrected: AP of one BUG step, with a rate and without the unsatisfiable
hypothesis.**  If `aᵀ V ≠ 0` and `⟨∂ₓρ, X⟩ ≠ 0`, then for all `ε > 0`, all ranks, and every choice
of orthonormal `X₁`, `V₁` capturing `K₁`, `L₁`,
`‖g₁ + σ⁻¹ ∂ₓρ aᵀ‖ ≤ (1 + κ (‖a‖ / ‖Vᵀ a‖ + σ₁ ‖σ⁻¹ ∂ₓρ‖ / ‖Xᵀ ∂ₓρ‖)) Φ`.

This replaces the assumption "`S_L ⟨X Xᵀ σ⟩` is invertible" of Einkemmer–Hu–Kusch, arXiv 2212.12012,
Thm 4.1 (see `not_isUnit_of_lLimit_eq`) and the `O(1)` assumptions listed under OP-ST-07.  The rate
is `O(ε)`, see `apPhi_le`, and that order is sharp, see `exists_rate_not_eps_sq`.  It matters
because both conditions can be read off the bases. -/
theorem ap_step_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε) (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (hb : Vᵀ * a ≠ 0) (hc : Xᵀ * d ≠ 0) :
    ‖X₁ * S₁ * V₁ᵀ - diffFlux σ d a‖ ≤
      (1 + kappa σ₀ σ₁ * (‖a‖ / ‖Vᵀ * a‖ + σ₁ * ‖ceDir σ d‖ / ‖Xᵀ * d‖)) *
        apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  set Φ := apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) with hΦ
  have hbn : 0 < ‖Vᵀ * a‖ := norm_pos_iff.2 hb
  have hcn : 0 < ‖Xᵀ * d‖ := norm_pos_iff.2 hc
  have h1 := ap_step_bound hσ hτ0 hτ hdt hε h
  have h2 := capture_kStep hσ hτ0 hτ hdt hε h
  have h3 := capture_lStep hσ hτ0 hτ hdt hε h
  rw [← hΦ] at h1 h2 h3
  have hk : 0 ≤ kappa σ₀ σ₁ := by linarith [hσ.one_le_kappa]
  have h4 : ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ ≤ Φ / ‖Vᵀ * a‖ := by
    rw [le_div_iff₀ hbn, mul_comm]
    exact h2
  have h5 : ‖a - V₁ * V₁ᵀ * a‖ ≤ σ₁ * Φ / ‖Xᵀ * d‖ := by
    rw [le_div_iff₀ hcn, mul_comm]
    exact h3
  have h6 : ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ * ‖a‖ + ‖ceDir σ d‖ * ‖a - V₁ * V₁ᵀ * a‖ ≤
      (‖a‖ / ‖Vᵀ * a‖ + σ₁ * ‖ceDir σ d‖ / ‖Xᵀ * d‖) * Φ := by
    calc _ ≤ Φ / ‖Vᵀ * a‖ * ‖a‖ + ‖ceDir σ d‖ * (σ₁ * Φ / ‖Xᵀ * d‖) := by gcongr
      _ = _ := by field_simp
  have h7 := mul_le_mul_of_nonneg_left h6 hk
  calc _ ≤ Φ + _ := h1
    _ ≤ Φ + kappa σ₀ σ₁ * ((‖a‖ / ‖Vᵀ * a‖ + σ₁ * ‖ceDir σ d‖ / ‖Xᵀ * d‖) * Φ) := by gcongr
    _ = _ := by ring

/-- **Augmentation makes AP unconditional.**  If the new bases contain `σ⁻¹ ∂ₓρ` and `a` (for
instance because `X₁`, `V₁` were augmented with them), then `‖g₁ - G‖ ≤ Φ`, with no condition on
the old bases at all. -/
theorem ap_step_le_of_capture (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (hu : X₁ * X₁ᵀ * ceDir σ d = ceDir σ d) (ha : V₁ * V₁ᵀ * a = a) :
    ‖X₁ * S₁ * V₁ᵀ - diffFlux σ d a‖ ≤
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) := by
  have h1 := ap_step_bound hσ hτ0 hτ hdt hε h
  rw [hu, ha, sub_self, sub_self] at h1
  simpa only [norm_zero, zero_mul, mul_zero, add_zero] using h1

/-- **The exact limit criterion, for frozen bases.**  With `X₁`, `V₁` fixed, the iterate tends
to `X₁ S₀ V₁ᵀ` (`norm_iterate_sub_sLimit_le`), and this is the diffusive flux `-σ⁻¹ ∂ₓρ aᵀ` if and
only if `σ⁻¹ ∂ₓρ ∈ range X₁` and `a ∈ range V₁`.

This is the "if and only if" that is true for the micro-macro scheme. Note it concerns the *new*
bases. The condition `aᵀVⁿ ≠ 0` on the *old* basis is not necessary, see
`ap_holds_with_V_perp_a`. -/
theorem sLimit_eq_diffFlux_iff (hσ : IsCrossSection σ σ₀ σ₁) (hX₁ : X₁ᵀ * X₁ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) (hd : d ≠ 0) (ha : a ≠ 0) :
    X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ = diffFlux σ d a ↔
      X₁ * X₁ᵀ * ceDir σ d = ceDir σ d ∧ V₁ * V₁ᵀ * a = a := by
  have hu : ceDir σ d ≠ 0 := by
    intro h0
    apply hd
    rw [← diagonal_mul_ceDir hσ d, h0, Matrix.mul_zero]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := capture_defect_le_norm (σ := σ) (d := d) (a := a) hX₁ hV₁
      (sLimit σ d a X₁ V₁)
    rw [h, sub_self, norm_zero] at h1 h2
    have han : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hun : 0 < ‖ceDir σ d‖ := norm_pos_iff.2 hu
    constructor
    · have h3 : ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ = 0 := by
        have := norm_nonneg (ceDir σ d - X₁ * X₁ᵀ * ceDir σ d)
        nlinarith
      exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
    · have h3 : ‖a - V₁ * V₁ᵀ * a‖ = 0 := by
        have := norm_nonneg (a - V₁ * V₁ᵀ * a)
        nlinarith
      exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
  · rintro ⟨h1, h2⟩
    have h3 := norm_sLimit_sub_le (d := d) (a := a) (V₁ := V₁) hσ hX₁
    rw [h1, h2, sub_self, sub_self] at h3
    simp only [norm_zero, zero_mul, mul_zero, add_zero] at h3
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h3)

/-- The Galerkin limit vanishes exactly when `∂ₓρ ⊥ range X₁` or `a ⊥ range V₁`.  Orthogonality
`V ⊥ a` to the old basis does not give `g = 0`: it is the *new* bases that matter. -/
theorem sLimit_eq_zero_iff (hσ : IsCrossSection σ σ₀ σ₁) (hX₁ : X₁ᵀ * X₁ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) :
    X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ = 0 ↔ X₁ᵀ * d = 0 ∨ V₁ᵀ * a = 0 := by
  have h1 : ‖X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ‖ = ‖lCoeff σ d X₁‖ * ‖V₁ᵀ * a‖ := by
    rw [norm_mul_transpose_of_orthonormal hV₁, norm_mul_of_orthonormal hX₁, sLimit, norm_neg]
    have : aᵀ * V₁ = (V₁ᵀ * a)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [this, norm_mul_transpose_col]
  rw [← norm_eq_zero, h1, mul_eq_zero, norm_eq_zero, norm_eq_zero]
  refine or_congr ?_ Iff.rfl
  constructor
  · intro h
    rw [← stiffness_mul_lCoeff hσ hX₁, h, Matrix.mul_zero]
  · intro h
    rw [lCoeff, h, Matrix.mul_zero]

theorem tendsto_apPhi {dt σ₀ τ B F : ℝ} (hdt : 0 < dt) (hσ₀ : 0 < σ₀) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hF : 0 ≤ F) : Tendsto (fun ε => apPhi dt ε σ₀ τ B F) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ε ^ 2 / (dt * σ₀) * (B + F) + ε / σ₀ * (τ * B)) (𝓝[>] 0)
      (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => ε ^ 2 / (dt * σ₀) * (B + F) + ε / σ₀ * (τ * B) := by
      fun_prop
    have h0 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
      add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [apPhi]
    positivity
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact apPhi_le hdt hε hσ₀ hτ hB hF

/-- **AP of a BUG step, characterised.**  Fix the old iterate and let `ε → 0`, with arbitrary
(possibly `ε`-dependent) capturing bases `X₁ ε`, `V₁ ε`.  Then `g₁ ε → -σ⁻¹ ∂ₓρ aᵀ` if and only if
`dist(σ⁻¹ ∂ₓρ, range (X₁ ε)) → 0` and `dist(a, range (V₁ ε)) → 0`.

In the micro-macro scheme `ker(σ) = 0`, so these two directions are not equilibria: they are the
Chapman–Enskog directions. See `tendsto_equilibrium_iff` and `IsBGK` for the true equilibrium
statement. -/
theorem tendsto_diffFlux_iff (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) (hd : d ≠ 0) (ha : a ≠ 0)
    {K₁' : ℝ → Matrix m r ℝ} {L₁' : ℝ → Matrix n r ℝ} {X₁' : ℝ → Matrix m p ℝ}
    {V₁' : ℝ → Matrix n q ℝ} {S₁' : ℝ → Matrix p q ℝ}
    (h : ∀ ε > 0, IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε) (S₁' ε)) :
    Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ - diffFlux σ d a‖) (𝓝[>] 0) (𝓝 0) ↔
      Tendsto (fun ε => ‖ceDir σ d - X₁' ε * (X₁' ε)ᵀ * ceDir σ d‖) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun ε => ‖a - V₁' ε * (V₁' ε)ᵀ * a‖) (𝓝[>] 0) (𝓝 0) := by
  have hu : ceDir σ d ≠ 0 := by
    intro h0
    apply hd
    rw [← diagonal_mul_ceDir hσ d, h0, Matrix.mul_zero]
  have han : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hun : 0 < ‖ceDir σ d‖ := norm_pos_iff.2 hu
  constructor
  · intro hlim
    have hlim1 := hlim.div_const ‖a‖
    have hlim2 := hlim.div_const ‖ceDir σ d‖
    rw [zero_div] at hlim1 hlim2
    constructor
    · refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim1
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [le_div_iff₀ han]
      exact (capture_defect_le_norm (h ε hε).hX₁ (h ε hε).hV₁ _).1
    · refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim2
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [le_div_iff₀ hun, mul_comm]
      exact (capture_defect_le_norm (h ε hε).hX₁ (h ε hε).hV₁ _).2
  · rintro ⟨h1, h2⟩
    have hk : 0 ≤ kappa σ₀ σ₁ := by linarith [hσ.one_le_kappa]
    have hΦ := tendsto_apPhi (B := ‖S‖) (F := kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) hdt hσ.pos hτ0
      (norm_nonneg _) (by positivity)
    have hsum := hΦ.add ((((h1.mul_const ‖a‖).add (h2.const_mul ‖ceDir σ d‖))).const_mul
      (kappa σ₀ σ₁))
    simp only [zero_mul, mul_zero, add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ap_step_bound hσ hτ0 hτ hdt hε (h ε hε)

variable {M : Type*} [Fintype M]

/-- One explicit Euler step of the limit equation (4.9) of the paper,
`ρ⁺ = ρ + dt ‖a‖² ∂ₓ(σ⁻¹ ∂ₓ ρ)`, with `∂ₓ = 𝒢` on `ρ` and `-𝒢ᵀ` on interface fluxes (the
summation-by-parts pair `D⁺`, `D⁻` of the paper).  In the paper `‖a‖² = a₀² = 1/3`. -/
noncomputable def diffusionStep (𝒢 : Matrix m M ℝ) (σ : m → ℝ) (a : Matrix n Unit ℝ) (dt : ℝ)
    (ρ : Matrix M Unit ℝ) : Matrix M Unit ℝ :=
  ρ - (dt * ‖a‖ ^ 2) • (𝒢ᵀ * ceDir σ (𝒢 * ρ))

omit [DecidableEq r] [DecidableEq p] [DecidableEq q] in
theorem diffFlux_mul (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) :
    diffFlux σ d a * a = -((‖a‖ ^ 2) • ceDir σ d) := by
  rw [diffFlux, Matrix.neg_mul, Matrix.mul_assoc, transpose_mul_self_col, Matrix.mul_smul,
    Matrix.mul_one]

omit [DecidableEq r] [DecidableEq p] [DecidableEq q] in
/-- **The macro update recovers the diffusion step.**  With `ρ₁ = ρ + dt 𝒢ᵀ (g₁ a)`, the distance
to the explicit Euler step of the limit equation is at most `dt ‖𝒢‖ ‖a‖ ‖g₁ - G‖`. -/
theorem norm_macro_sub_le {𝒢 : Matrix m M ℝ} {ρ ρ₁ : Matrix M Unit ℝ} {g₁ : Matrix m n ℝ}
    (hdt : 0 ≤ dt) (hρ : ρ₁ = ρ + dt • (𝒢ᵀ * (g₁ * a))) :
    ‖ρ₁ - diffusionStep 𝒢 σ a dt ρ‖ ≤ dt * ‖𝒢‖ * ‖a‖ * ‖g₁ - diffFlux σ (𝒢 * ρ) a‖ := by
  have h1 : ρ₁ - diffusionStep 𝒢 σ a dt ρ = dt • (𝒢ᵀ * ((g₁ - diffFlux σ (𝒢 * ρ) a) * a)) := by
    rw [hρ, diffusionStep, Matrix.sub_mul, diffFlux_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_smul, sub_neg_eq_add, smul_add, smul_smul]
    abel
  rw [h1, norm_smul, Real.norm_of_nonneg hdt]
  have h2 : ‖𝒢ᵀ * ((g₁ - diffFlux σ (𝒢 * ρ) a) * a)‖ ≤
      ‖𝒢‖ * (‖g₁ - diffFlux σ (𝒢 * ρ) a‖ * ‖a‖) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [norm_transpose]
    gcongr
    exact Frobenius.norm_mul_le _ _
  calc dt * _ ≤ dt * (‖𝒢‖ * (‖g₁ - diffFlux σ (𝒢 * ρ) a‖ * ‖a‖)) := by gcongr
    _ = _ := by ring

/-- **The effective limit equation of the scheme, for frozen bases.**  As `ε → 0`, the macro update
tends to `ρ - dt ‖V₁ᵀ a‖² 𝒢ᵀ φ`, where `φ` is the `σ`-weighted Galerkin projection of `σ⁻¹ ∂ₓρ` onto
`range X₁`.  So when `a ∉ range V₁` the diffusion coefficient `‖a‖² = 1/3` is replaced by
`‖V₁ᵀ a‖²`, which is the loss of the diffusion coefficient. -/
theorem norm_macro_sub_effective_le (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) (hε : 0 < ε) {𝒢 : Matrix m M ℝ}
    {ρ ρ₁ : Matrix M Unit ℝ}
    (h : IsMicroMacroBUGStep σ 𝒯 (𝒢 * ρ) a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (hρ : ρ₁ = ρ + dt • (𝒢ᵀ * (X₁ * S₁ * V₁ᵀ * a))) :
    ‖ρ₁ - (ρ - (dt * ‖V₁ᵀ * a‖ ^ 2) • (𝒢ᵀ * galerkinFlux σ X₁ (𝒢 * ρ)))‖ ≤
      dt * ‖𝒢‖ * ‖a‖ *
        apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ (𝒢 * ρ)‖ * ‖a‖) := by
  set y := X₁ * sLimit σ (𝒢 * ρ) a X₁ V₁ * V₁ᵀ with hy
  have hya : y * a = -((‖V₁ᵀ * a‖ ^ 2) • galerkinFlux σ X₁ (𝒢 * ρ)) := by
    have h1 : aᵀ * V₁ * V₁ᵀ * a = (‖V₁ᵀ * a‖ ^ 2) • (1 : Matrix Unit Unit ℝ) := by
      rw [← transpose_mul_self_col, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [hy, mul_sLimit_mul, Matrix.neg_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one]
  have h1 : ρ₁ - (ρ - (dt * ‖V₁ᵀ * a‖ ^ 2) • (𝒢ᵀ * galerkinFlux σ X₁ (𝒢 * ρ))) =
      dt • (𝒢ᵀ * ((X₁ * S₁ * V₁ᵀ - y) * a)) := by
    rw [hρ, Matrix.sub_mul, hya, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, sub_neg_eq_add,
      smul_add, smul_smul]
    abel
  rw [h1, norm_smul, Real.norm_of_nonneg hdt.le]
  have h2 : ‖𝒢ᵀ * ((X₁ * S₁ * V₁ᵀ - y) * a)‖ ≤ ‖𝒢‖ * (‖X₁ * S₁ * V₁ᵀ - y‖ * ‖a‖) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [norm_transpose]
    gcongr
    exact Frobenius.norm_mul_le _ _
  have h3 := norm_iterate_sub_sLimit_le hσ hτ0 hτ hdt hε h
  calc dt * _ ≤ dt * (‖𝒢‖ * (‖X₁ * S₁ * V₁ᵀ - y‖ * ‖a‖)) := by gcongr
    _ ≤ dt * (‖𝒢‖ * (apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ (𝒢 * ρ)‖ * ‖a‖) * ‖a‖)) := by
        gcongr
    _ = _ := by ring

/-- **The rate `O(ε)` is exact.**  The `S`-step cannot be closer to its limit than
`((dt/ε) ‖Π 𝒯 g̃‖ - ‖g̃ - y‖) / (1 + (dt/ε²) σ₁)`, where `Π` is the Galerkin projector, `g̃ = Π gⁿ`
and `y = X₁ S₀ V₁ᵀ`.  So as soon as the projected transport `Π 𝒯 g̃` does not vanish, the error
is bounded below by a multiple of `ε`. The rate `ε²/dt` holds only when
`Π 𝒯 g̃ = 0`. -/
theorem sStep_ge (hσ : IsCrossSection σ σ₀ σ₁) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) :
    dt / ε * ‖galerkinProj X₁ V₁ (𝒯 (X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ)))‖ -
        ‖X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ) - X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ‖ ≤
      (1 + dt / ε ^ 2 * σ₁) * ‖X₁ * S₁ * V₁ᵀ - X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ‖ := by
  have hP := isOrthProj_galerkinProj (n := n) h.hX₁ h.hV₁
  set gt := X₁ * X₁ᵀ * (X * S * Vᵀ) * (V₁ * V₁ᵀ) with hg
  have hPg : galerkinProj X₁ V₁ gt = gt := by
    rw [hg, ← galerkinProj_apply, hP.idem]
  obtain ⟨hy1, hy2⟩ := galerkin_limit_props (σ := σ) (d := d) (a := a) h.hV₁
    (galerkinFlux_range h.hX₁ σ d) (galerkinFlux_orth hσ h.hX₁ d)
  rw [← mul_sLimit_mul] at hy1 hy2
  set y := X₁ * sLimit σ d a X₁ V₁ * V₁ᵀ with hy
  have hs : 0 ≤ dt / ε ^ 2 := by positivity
  have ht : 0 ≤ dt / ε := by positivity
  have hΛ : ∀ x, galerkinProj X₁ V₁ x = x →
      ‖galerkinProj X₁ V₁ (scatter σ x)‖ ≤ σ₁ * ‖x‖ := by
    intro x _
    refine (hP.norm_le _).trans ?_
    rw [scatter_apply, norm_neg]
    exact hσ.norm_diagonal_mul_le x
  have h1 := coercive_relax_ge hP hΛ hs h.sLift hy1 hy2
  have h2 : galerkinProj X₁ V₁ (gt - (dt / ε) • 𝒯 gt) - y =
      (gt - y) - (dt / ε) • galerkinProj X₁ V₁ (𝒯 gt) := by
    rw [map_sub, map_smul, hPg]
    abel
  rw [h2] at h1
  have h3 : dt / ε * ‖galerkinProj X₁ V₁ (𝒯 gt)‖ ≤
      ‖(gt - y) - (dt / ε) • galerkinProj X₁ V₁ (𝒯 gt)‖ + ‖gt - y‖ := by
    have h5 : (dt / ε) • galerkinProj X₁ V₁ (𝒯 gt) =
        (gt - y) - ((gt - y) - (dt / ε) • galerkinProj X₁ V₁ (𝒯 gt)) := by abel
    have h4 := norm_sub_le (gt - y) ((gt - y) - (dt / ε) • galerkinProj X₁ V₁ (𝒯 gt))
    rw [← h5, norm_smul, Real.norm_of_nonneg ht] at h4
    linarith
  linarith

/-- **Well-posedness of the step**: for all data the implicit substeps are uniquely solvable and
bases of fixed rank `k` exist, so `IsMicroMacroBUGStep` is never vacuous. -/
theorem exists_step {k : ℕ} (hm : k ≤ Fintype.card m) (hn : k ≤ Fintype.card n)
    (hσ : IsCrossSection σ σ₀ σ₁) (hdt : 0 < dt) (hε : 0 < ε) (𝒯 : Matrix m n ℝ → Matrix m n ℝ)
    (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) {X : Matrix m (Fin k) ℝ}
    (S : Matrix (Fin k) (Fin k) ℝ)
    {V : Matrix n (Fin k) ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) :
    ∃ (K₁ : Matrix m (Fin k) ℝ) (L₁ : Matrix n (Fin k) ℝ) (X₁ : Matrix m (Fin k) ℝ)
      (V₁ : Matrix n (Fin k) ℝ) (S₁ : Matrix (Fin k) (Fin k) ℝ),
      IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁ := by
  have hs : 0 ≤ dt / ε ^ 2 := by positivity
  set s := dt / ε ^ 2 with hsdef
  set t := dt / ε with htdef
  set g := X * S * Vᵀ with hg
  have hone : (1 : Matrix m m ℝ)ᵀ * 1 = 1 := by simp
  -- the `K`-step
  have hAK := hσ.isUnit_one_add_stiffness hone hs
  have hAK' : stiffness σ (1 : Matrix m m ℝ) = Matrix.diagonal σ := by simp [stiffness]
  rw [hAK'] at hAK
  set RK := X * S - t • (𝒯 g * V) - s • (d * (aᵀ * V)) with hRK
  set K₁ := (1 + s • Matrix.diagonal σ)⁻¹ * RK with hK₁
  have hKeq : (1 + s • Matrix.diagonal σ) * K₁ = RK := by
    rw [hK₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hAK),
      Matrix.one_mul]
  -- the `L`-step
  have hAL := hσ.isUnit_one_add_stiffness hX hs
  set RL := V * Sᵀ - t • ((𝒯 g)ᵀ * X) - s • (a * (dᵀ * X)) with hRL
  set L₁ := RL * (1 + s • stiffness σ X)⁻¹ with hL₁
  have hLeq : L₁ * (1 + s • stiffness σ X) = RL := by
    rw [hL₁, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hAL),
      Matrix.mul_one]
  -- the bases
  obtain ⟨X₁, hX₁, hXcap⟩ := exists_orthonormal_capture_of_le_card K₁ hm
  obtain ⟨V₁, hV₁, hVcap⟩ := exists_orthonormal_capture_of_le_card L₁ hn
  -- the `S`-step
  have hAS := hσ.isUnit_one_add_stiffness hX₁ hs
  set RS := X₁ᵀ * g * V₁ - t • (X₁ᵀ * 𝒯 (X₁ * X₁ᵀ * g * (V₁ * V₁ᵀ)) * V₁) -
    s • (X₁ᵀ * d * (aᵀ * V₁)) with hRS
  set S₁ := (1 + s • stiffness σ X₁)⁻¹ * RS with hS₁
  have hSeq : (1 + s • stiffness σ X₁) * S₁ = RS := by
    rw [hS₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hAS),
      Matrix.one_mul]
  refine ⟨K₁, L₁, X₁, V₁, S₁, hX, hV, hX₁, hV₁, ?_, ?_, hXcap, hVcap, ?_⟩
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at hKeq
    rw [smul_add, ← sub_sub, ← hRK, ← hKeq]
    abel
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hLeq
    rw [smul_add, ← sub_sub, ← hRL, ← hLeq]
    abel
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at hSeq
    rw [smul_add, ← sub_sub, ← hRS, ← hSeq]
    abel

/-- The diffusive flux has rank at most one in the micro variable `g`. The bound `≤ 2` is the rank
of `f = ρ e₀ + ε g`, not of `g`. -/
theorem rank_diffFlux_le (σ : m → ℝ) (d : Matrix m Unit ℝ) (a : Matrix n Unit ℝ) :
    (diffFlux σ d a).rank ≤ 1 := by
  rw [diffFlux, ← Matrix.neg_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width (-ceDir σ d))

/-- `ap_step_le` as a limit: under `aᵀ V ≠ 0` and `⟨∂ₓρ, X⟩ ≠ 0`, for every family of steps with
arbitrary capturing bases, `g₁ ε → -σ⁻¹ ∂ₓρ aᵀ` as `ε → 0`. -/
theorem tendsto_diffFlux (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) (hb : Vᵀ * a ≠ 0) (hc : Xᵀ * d ≠ 0)
    {K₁' : ℝ → Matrix m r ℝ} {L₁' : ℝ → Matrix n r ℝ} {X₁' : ℝ → Matrix m p ℝ}
    {V₁' : ℝ → Matrix n q ℝ} {S₁' : ℝ → Matrix p q ℝ}
    (h : ∀ ε > 0, IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε) (S₁' ε)) :
    Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ - diffFlux σ d a‖) (𝓝[>] 0) (𝓝 0) := by
  have hk : 0 ≤ kappa σ₀ σ₁ := by linarith [hσ.one_le_kappa]
  have hΦ := (tendsto_apPhi (B := ‖S‖) (F := kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) hdt hσ.pos hτ0
    (norm_nonneg _) (by positivity)).const_mul
      (1 + kappa σ₀ σ₁ * (‖a‖ / ‖Vᵀ * a‖ + σ₁ * ‖ceDir σ d‖ / ‖Xᵀ * d‖))
  rw [mul_zero] at hΦ
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hΦ
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ap_step_le hσ hτ0 hτ hdt hε (h ε hε) hb hc

end Limits

section BGK

variable {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']

/-- The BGK-type relaxation `C g = -σ (g - g M Mᵀ)` of a kinetic solution `g ∈ ℝ^{m × n}` towards
the equilibrium direction `M ∈ ℝⁿ` (the discrete Maxwellian), with `Mᵀ M = 1`. -/
noncomputable def bgk (σ : m → ℝ) (M : Matrix n Unit ℝ) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ :=
  scatter σ * (1 - rightProj M)

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
theorem bgk_apply (σ : m → ℝ) (M : Matrix n Unit ℝ) (g : Matrix m n ℝ) :
    bgk σ M g = -(Matrix.diagonal σ * (g - g * M * Mᵀ)) := by
  simp [bgk]

variable {σ : m → ℝ} {σ₀ σ₁ : ℝ} {M : Matrix n Unit ℝ}

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
private theorem inner_bgk (hM : Mᵀ * M = 1) (x y : Matrix m n ℝ) :
    ⟪bgk σ M x, y⟫ = -⟪Matrix.diagonal σ * (x - x * M * Mᵀ), y - y * M * Mᵀ⟫ := by
  have hQ := isOrthProj_rightProj (m := m) hM
  rw [bgk_apply, inner_neg_left, inner_sub_right (𝕜 := ℝ) _ y]
  have h1 : ⟪Matrix.diagonal σ * (x - x * M * Mᵀ), y * M * Mᵀ⟫ = 0 := by
    have h2 : ⟪Matrix.diagonal σ * (x - x * M * Mᵀ), rightProj M y⟫ =
        ⟪rightProj M (Matrix.diagonal σ * (x - x * M * Mᵀ)), y⟫ := (hQ.symm _ _).symm
    rw [rightProj_apply] at h2
    rw [h2, rightProj_apply]
    have h3 : Matrix.diagonal σ * (x - x * M * Mᵀ) * M * Mᵀ = 0 := by
      have h4 : (x - x * M * Mᵀ) * M = 0 := by
        rw [Matrix.sub_mul, Matrix.mul_assoc (x * M), hM, Matrix.mul_one, sub_self]
      rw [Matrix.mul_assoc _ (x - x * M * Mᵀ), h4, Matrix.mul_zero, Matrix.zero_mul]
    rw [h3, inner_zero_left]
  rw [h1, sub_zero]

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
/-- The BGK operator is a relaxation operator. -/
theorem bgk_isRelaxation (hσ : IsCrossSection σ σ₀ σ₁) (hM : Mᵀ * M = 1) :
    IsRelaxation (bgk σ M : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) where
  symm x y := by
    rw [inner_bgk hM, real_inner_comm (bgk σ M y) x, inner_bgk hM, inner_diagonal_comm,
      real_inner_comm]
  nonpos x := by
    rw [inner_bgk hM]
    have h1 := hσ.lower_inner (x - x * M * Mᵀ)
    have h2 : 0 ≤ σ₀ * ‖x - x * M * Mᵀ‖ ^ 2 := by have := hσ.pos; positivity
    linarith

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
private theorem bgk_eq_zero_iff (hσ : IsCrossSection σ σ₀ σ₁) (hM : Mᵀ * M = 1)
    (x : Matrix m n ℝ) : bgk σ M x = 0 ↔ x * M * Mᵀ = x := by
  constructor
  · intro h
    have h1 := inner_bgk (σ := σ) hM x x
    rw [h, inner_zero_left] at h1
    have h2 := hσ.lower_inner (x - x * M * Mᵀ)
    have h3 : ‖x - x * M * Mᵀ‖ ^ 2 = 0 := by
      have h4 : 0 ≤ ‖x - x * M * Mᵀ‖ ^ 2 := sq_nonneg _
      by_contra hne
      have h5 : 0 < ‖x - x * M * Mᵀ‖ ^ 2 := lt_of_le_of_ne h4 (Ne.symm hne)
      have := mul_pos hσ.pos h5
      linarith
    have h4 : x - x * M * Mᵀ = 0 := by simpa using h3
    exact (sub_eq_zero.1 h4).symm
  · intro h
    rw [bgk_apply, h, sub_self, Matrix.mul_zero, neg_zero]

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
/-- The true equilibrium projection of `w` is `w M Mᵀ`: the density `w M` times the Maxwellian. -/
theorem bgk_starProjection (hσ : IsCrossSection σ σ₀ σ₁) (hM : Mᵀ * M = 1) (w : Matrix m n ℝ) :
    (LinearMap.ker ((bgk σ M : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :
      Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)).starProjection w = w * M * Mᵀ := by
  have hQ := isOrthProj_rightProj (m := m) hM
  have hmem : w * M * Mᵀ ∈ LinearMap.ker
      ((bgk σ M : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ) := by
    change bgk σ M (w * M * Mᵀ) = 0
    rw [bgk_eq_zero_iff hσ hM]
    have h1 : w * M * Mᵀ * M * Mᵀ = w * M * (Mᵀ * M) * Mᵀ := by simp only [Matrix.mul_assoc]
    rw [h1, hM, Matrix.mul_one]
  refine Submodule.eq_starProjection_of_mem_orthogonal hmem ?_
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz' : bgk σ M z = 0 := hz
  have hzQ := (bgk_eq_zero_iff hσ hM z).1 hz'
  have h1 : ⟪rightProj M z, w - rightProj M w⟫ = 0 := by
    rw [hQ.symm, map_sub, hQ.idem, sub_self, inner_zero_right]
  rwa [rightProj_apply, hzQ, rightProj_apply] at h1

omit [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] in
private theorem norm_eq_one_of_orthonormal (hM : Mᵀ * M = 1) : ‖M‖ = 1 := by
  have h := transpose_mul_self_col M
  rw [hM] at h
  have h1 := congrFun (congrFun h ()) ()
  simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h1
  have h2 : ‖M‖ ^ 2 = 1 ^ 2 := by rw [← h1, one_pow]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2

omit [DecidableEq k] [DecidableEq k'] in
/-- **AP of implicit low-rank BGK relaxation: "equilibrium in the Galerkin space" as an
equivalence.**  Let `v s` be the implicit relaxation step `v = U Uᵀ (w + s C v) V Vᵀ` towards the
equilibrium direction `M`, and suppose the density `w M` does not vanish.  Then `v s` converges as
`s → ∞` to the true equilibrium `w M Mᵀ` if and only if `M ∈ range V` and `w M ∈ range U`.

This is the literal content of asymptotic preservation and the application of Lemma H.  The
pointwise `w M ∈ range U` is the right condition on `U`: `ker C ≤ range P` would force `U` to be
onto. Compare the formal limits of arXiv 1907.04247 and arXiv 2505.19929, which are listed under
OP-ST-07. -/
theorem bgk_tendsto_iff [DecidableEq k] [DecidableEq k'] (hσ : IsCrossSection σ σ₀ σ₁)
    (hM : Mᵀ * M = 1) {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {w : Matrix m n ℝ} (hw : w * M ≠ 0) {v : ℝ → Matrix m n ℝ}
    (hv : ∀ s, 0 ≤ s → v s = galerkinProj U V (w + s • bgk σ M (v s))) :
    Tendsto v atTop (𝓝 (w * M * Mᵀ)) ↔ V * Vᵀ * M = M ∧ U * Uᵀ * (w * M) = w * M := by
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  have h := tendsto_equilibrium_iff hP (bgk_isRelaxation hσ hM) hv
  rw [bgk_starProjection hσ hM] at h
  rw [h, galerkinProj_apply]
  have hMn := norm_eq_one_of_orthonormal hM
  have hwn : 0 < ‖w * M‖ := norm_pos_iff.2 hw
  constructor
  · intro h1
    obtain ⟨h2, h3⟩ := rank_one_defect_le hU hV (Uᵀ * (w * M * Mᵀ) * V) (w * M) M
    have h4 : U * (Uᵀ * (w * M * Mᵀ) * V) * Vᵀ - w * M * Mᵀ = 0 := by
      rw [sub_eq_zero]
      conv_rhs => rw [← h1]
      simp only [Matrix.mul_assoc]
    rw [h4, norm_zero, hMn, mul_one] at h2
    rw [h4, norm_zero] at h3
    have h5 : ‖M - V * Vᵀ * M‖ = 0 := by
      have := norm_nonneg (M - V * Vᵀ * M)
      nlinarith
    exact ⟨(sub_eq_zero.1 (norm_eq_zero.1 h5)).symm,
      (sub_eq_zero.1 (norm_le_zero_iff.1 h2)).symm⟩
  · rintro ⟨h1, h2⟩
    have h3 : Mᵀ * (V * Vᵀ) = Mᵀ := by
      have := congrArg Matrix.transpose h1
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
    calc U * Uᵀ * (w * M * Mᵀ) * (V * Vᵀ) = (U * Uᵀ * (w * M)) * (Mᵀ * (V * Vᵀ)) := by
          simp only [Matrix.mul_assoc]
      _ = w * M * Mᵀ := by rw [h2, h3]

omit [DecidableEq k] [DecidableEq k'] in
/-- **The equilibrium direction is in the basis: rate `1 / (1 + s σ₀)`.**  If `M ∈ range V`, the
implicit step converges to `U Uᵀ (w M) Mᵀ`, with the spectral gap `σ₀` of the cross-section,
independently of the bases: no loss of gap in the low-rank space. -/
theorem bgk_le_of_mem [DecidableEq k] [DecidableEq k'] (hσ : IsCrossSection σ σ₀ σ₁)
    (hM : Mᵀ * M = 1) {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hMV : V * Vᵀ * M = M) {s : ℝ} (hs : 0 ≤ s)
    {w v : Matrix m n ℝ} (hv : v = galerkinProj U V (w + s • bgk σ M v)) :
    ‖v - U * Uᵀ * (w * M) * Mᵀ‖ ≤ ‖galerkinProj U V w‖ / (1 + s * σ₀) := by
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  have hQ := isOrthProj_rightProj (m := m) hM
  set y := U * Uᵀ * (w * M) * Mᵀ with hy
  have hPv : galerkinProj U V v = v := by rw [hv, hP.idem]
  have hMVt : Mᵀ * (V * Vᵀ) = Mᵀ := by
    have := congrArg Matrix.transpose hMV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  have hUU : U * Uᵀ * (U * Uᵀ) = U * Uᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  have hPy : galerkinProj U V y = y := by
    rw [galerkinProj_apply, hy]
    calc U * Uᵀ * (U * Uᵀ * (w * M) * Mᵀ) * (V * Vᵀ)
        = (U * Uᵀ * (U * Uᵀ)) * (w * M) * (Mᵀ * (V * Vᵀ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, hMVt]
  have hyM : y * M = U * Uᵀ * (w * M) := by
    rw [hy, Matrix.mul_assoc, hM, Matrix.mul_one]
  have hCy : bgk σ M y = 0 := by
    rw [bgk_eq_zero_iff hσ hM, hyM]
  have hstep : v = galerkinProj U V w + s • galerkinProj U V (bgk σ M v) := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul]
  have hRM : ∀ x : Matrix m n ℝ, (x - x * M * Mᵀ) * M = 0 := fun x => by
    rw [Matrix.sub_mul, Matrix.mul_assoc (x * M), hM, Matrix.mul_one, sub_self]
  have hvM : v * M = U * Uᵀ * (w * M) := by
    have h1 : galerkinProj U V (w + s • bgk σ M v) * M =
        U * Uᵀ * ((w + s • bgk σ M v) * M) := by
      rw [galerkinProj_apply, Matrix.mul_assoc _ (V * Vᵀ), hMV, Matrix.mul_assoc (U * Uᵀ)]
    have h2 : bgk σ M v * M = 0 := by
      rw [bgk_apply, Matrix.neg_mul, Matrix.mul_assoc, hRM, Matrix.mul_zero, neg_zero]
    rw [← hv] at h1
    rw [h1, Matrix.add_mul, Matrix.smul_mul, h2, smul_zero, add_zero]
  set e := v - y with he
  have heM : e * M = 0 := by rw [he, Matrix.sub_mul, hvM, hyM, sub_self]
  have hee : e * M * Mᵀ = 0 := by rw [heM, Matrix.zero_mul]
  have hCe : bgk σ M e = -(Matrix.diagonal σ * e) := by rw [bgk_apply, hee, sub_zero]
  have hPe : galerkinProj U V e = e := by rw [he, map_sub, hPv, hPy]
  have hCv : bgk σ M v = bgk σ M e := by
    have : v = e + y := by rw [he]; abel
    conv_lhs => rw [this]
    rw [map_add, hCy, add_zero]
  have heq : e = (galerkinProj U V w - y) + s • galerkinProj U V (bgk σ M e) := by
    rw [hCv] at hstep
    calc e = (galerkinProj U V w + s • galerkinProj U V (bgk σ M e)) - y :=
          congrArg (· - y) hstep
      _ = _ := by abel
  have hcoer : σ₀ * ‖e‖ ^ 2 ≤ -⟪bgk σ M e, e⟫ := by
    rw [hCe, inner_neg_left, neg_neg]
    exact hσ.lower_inner e
  have h1 := core_le hP hs hσ.pos.le hPe heq hcoer
  refine h1.trans ?_
  have hden : 0 < 1 + s * σ₀ := by have := hσ.pos; positivity
  gcongr
  have hyQ : y = rightProj M (galerkinProj U V w) := by
    rw [rightProj_apply, galerkinProj_apply, hy, Matrix.mul_assoc (U * Uᵀ * w), hMV,
      Matrix.mul_assoc (U * Uᵀ) w]
  rw [hyQ]
  exact hQ.norm_sub_le _

omit [DecidableEq k] [DecidableEq k'] in
/-- **The equilibrium direction is not in the basis: the mass is lost.**  For any bases,
`‖v‖ ≤ ‖P w‖ / (1 + s σ₀ γ)` with `γ = dist(M, range V)²`.  So if `M ∉ range V` the implicit
relaxation drives the solution to zero as `s → ∞`, and with it the density `v M`, however large
the density of `w`.  The gap `σ₀ γ` degenerates as `M` approaches `range V`, so the limit `s → ∞`
of the low-rank scheme depends discontinuously on the basis. -/
theorem bgk_le_of_not_mem [DecidableEq k] [DecidableEq k'] (hσ : IsCrossSection σ σ₀ σ₁)
    (hM : Mᵀ * M = 1) {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {s : ℝ} (hs : 0 ≤ s)
    {w v : Matrix m n ℝ} (hv : v = galerkinProj U V (w + s • bgk σ M v)) :
    ‖v‖ ≤ ‖galerkinProj U V w‖ / (1 + s * (σ₀ * ‖M - V * Vᵀ * M‖ ^ 2)) := by
  have hP := isOrthProj_galerkinProj (n := n) hU hV
  have hQ := isOrthProj_rightProj (m := m) hM
  have hPv : galerkinProj U V v = v := by rw [hv, hP.idem]
  set γ := ‖M - V * Vᵀ * M‖ ^ 2 with hγ
  have hstep : v = galerkinProj U V w + s • galerkinProj U V (bgk σ M v) := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul]
  have hγ0 : 0 ≤ σ₀ * γ := by have := hσ.pos; positivity
  have hcoer : (σ₀ * γ) * ‖v‖ ^ 2 ≤ -⟪bgk σ M v, v⟫ := by
    rw [inner_bgk hM, neg_neg]
    refine le_trans ?_ (hσ.lower_inner _)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hσ.pos.le
    -- `‖v M‖ ≤ ‖v‖ ‖V Vᵀ M‖`, by Pythagoras in both factors
    have hvV : v * (V * Vᵀ) = v := by
      have hVV : V * Vᵀ * (V * Vᵀ) = V * Vᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
      conv_lhs => rw [← hPv, galerkinProj_apply, Matrix.mul_assoc, hVV]
      rw [← galerkinProj_apply, hPv]
    have h1 := hQ.norm_sq_add v
    have h2 : ‖v * M * Mᵀ‖ = ‖v * M‖ := norm_mul_transpose_of_orthonormal hM _
    have h3 : v * M = v * (V * Vᵀ * M) := by
      conv_lhs => rw [← hvV]
      rw [Matrix.mul_assoc]
    have h4 : ‖v * M‖ ≤ ‖v‖ * ‖V * Vᵀ * M‖ := by
      conv_lhs => rw [h3]
      exact Frobenius.norm_mul_le _ _
    have h5 := (isOrthProj_leftProj (n := Unit) hV).norm_sq_add M
    rw [leftProj_apply, norm_eq_one_of_orthonormal hM, one_pow] at h5
    have h6 : ‖v * M‖ ^ 2 ≤ ‖v‖ ^ 2 * ‖V * Vᵀ * M‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h4 2
    rw [rightProj_apply, h2] at h1
    have h7 : ‖V * Vᵀ * M‖ ^ 2 = 1 - γ := by rw [hγ]; linarith
    rw [h7] at h6
    nlinarith
  have h1 := core_le hP hs hγ0 hPv hstep hcoer
  exact h1

end BGK

section Perp

variable [DecidableEq r] {c τ dt ε : ℝ} {𝒯 : Matrix m n ℝ → Matrix m n ℝ}
  {d : Matrix m Unit ℝ} {a : Matrix n Unit ℝ} {X : Matrix m r ℝ} {S : Matrix r r ℝ}
  {V : Matrix n r ℝ} {K₁ : Matrix m r ℝ} {L₁ : Matrix n r ℝ} {X₁ : Matrix m r ℝ}
  {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ}

omit [DecidableEq r] [Fintype m] [DecidableEq m] in
theorem isCrossSection_const (hc : 0 < c) : IsCrossSection (fun _ : m => c) c c :=
  ⟨hc, le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩

theorem kappa_self (hc : 0 < c) : kappa c c = 1 := by
  simp [kappa, div_self hc.ne']

omit [DecidableEq r] [Fintype r] in
private theorem diagonal_const_mul (Z : Matrix m r ℝ) :
    Matrix.diagonal (fun _ : m => c) * Z = c • Z := by
  ext i j
  simp [Matrix.diagonal_mul]

omit [DecidableEq r] in
theorem ceDir_const (d : Matrix m Unit ℝ) : ceDir (fun _ : m => c) d = c⁻¹ • d := by
  ext i j
  simp [ceDir, Matrix.diagonal_mul]

omit [Fintype r] in
private theorem stiffness_const (hX : Xᵀ * X = 1) : stiffness (fun _ : m => c) X = c • 1 := by
  rw [stiffness, Matrix.mul_assoc, diagonal_const_mul, Matrix.mul_smul, hX]

omit [DecidableEq m] in
/-- Cancel an invertible factor on the right. -/
private theorem cancel_right {k : Type*} {Y : Matrix k r ℝ} {Z : Matrix k r ℝ} {T : Matrix r r ℝ}
    (hT : IsUnit T) (h : Y * T = Z * T) : Y = Z := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hT
  calc Y = Y * (T * T⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = Z * (T * T⁻¹) := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
    _ = Z := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

/-- With constant cross-section, `a ⊥ range V` and no transport in the `K`-step, the `K`-step only
rescales `X S`, so `X₁` captures `X` and, at fixed rank, spans exactly the same space. -/
theorem range_eq_of_perp (hc : 0 < c) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (haV : aᵀ * V = 0) (hT : 𝒯 (X * S * Vᵀ) * V = 0) (hS : IsUnit S) :
    X * Xᵀ = X₁ * X₁ᵀ := by
  have hs : 0 < 1 + dt / ε ^ 2 * c := by positivity
  have hk := h.kStep
  rw [haV, hT, Matrix.mul_zero, smul_zero, sub_zero, zero_add, diagonal_const_mul] at hk
  have h1 : (1 + dt / ε ^ 2 * c) • K₁ = X * S := by
    rw [add_smul, one_smul, mul_smul]
    calc K₁ + (dt / ε ^ 2) • c • K₁ = (X * S - (dt / ε ^ 2) • c • K₁) + (dt / ε ^ 2) • c • K₁ := by
          rw [← hk]
      _ = X * S := sub_add_cancel _ _
  have hcap : X₁ * X₁ᵀ * X * S = X * S := by
    rw [Matrix.mul_assoc, ← h1, Matrix.mul_smul, h.kCap]
  exact mul_transpose_eq_of_capture rfl h.hX (cancel_right hS hcap)

/-- **What the scheme does when `V ⊥ a`.**  Let the cross-section be constant, `aᵀ V = 0`, let the
`K`-step see no transport, `𝒯 (X S Vᵀ) V = 0`, and let `S` be invertible and the rank fixed.  If
`⟨∂ₓρ, X⟩ ≠ 0`, the iterate tends to `-(X Xᵀ σ⁻¹ ∂ₓρ) aᵀ`: not to zero, and the diffusive flux
exactly when `σ⁻¹ ∂ₓρ` already lay in `range X`.

So the claim of OP-CO-12 that `V ⊥ a` forces `g = 0` and loses AP is false: the
`L`-step restores `a` on its own, and only the direction `σ⁻¹ ∂ₓρ` can be missed. -/
theorem norm_iterate_sub_perp_le (hc : 0 < c) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (haV : aᵀ * V = 0) (hT : 𝒯 (X * S * Vᵀ) * V = 0) (hS : IsUnit S) (hXd : Xᵀ * d ≠ 0) :
    ‖X₁ * S₁ * V₁ᵀ - -(X * Xᵀ * ceDir (fun _ : m => c) d * aᵀ)‖ ≤
      (1 + c * ‖ceDir (fun _ : m => c) d‖ / ‖Xᵀ * d‖) *
        apPhi dt ε c τ ‖S‖ (kappa c c * ‖ceDir (fun _ : m => c) d‖ * ‖a‖) := by
  have hσ := isCrossSection_const (m := m) hc
  set u := ceDir (fun _ : m => c) d with hu
  set Φ := apPhi dt ε c τ ‖S‖ (kappa c c * ‖u‖ * ‖a‖) with hΦ
  have hP := range_eq_of_perp hc hdt hε h haV hT hS
  have hcn : 0 < ‖Xᵀ * d‖ := norm_pos_iff.2 hXd
  set φ := galerkinFlux (fun _ : m => c) X₁ d with hφ
  have hφu : φ = X₁ * X₁ᵀ * u := by
    have h1 := galerkinFlux_orth hσ h.hX₁ d
    rw [← hφ] at h1
    have h2 := galerkinFlux_range h.hX₁ (fun _ : m => c) d
    rw [← hφ] at h2
    have hdφ : Matrix.diagonal (fun _ : m => c) * φ = c • φ := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [hdφ, Matrix.mul_smul] at h1
    have h3 : X₁ᵀ * φ = X₁ᵀ * u := by
      rw [hu, ceDir_const, Matrix.mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [← h2, Matrix.mul_assoc, h3, Matrix.mul_assoc]
  have hφn : ‖φ‖ ≤ ‖u‖ := by
    rw [hφu]
    simpa using (isOrthProj_leftProj (n := Unit) h.hX₁).norm_le u
  have h1 := norm_iterate_sub_sLimit_le hσ hτ0 hτ hdt hε h
  rw [← hu, ← hΦ] at h1
  have h2 := capture_lStep hσ hτ0 hτ hdt hε h
  rw [← hu, ← hΦ] at h2
  have hδ : ‖a - V₁ * V₁ᵀ * a‖ ≤ c * Φ / ‖Xᵀ * d‖ := by
    rw [le_div_iff₀ hcn, mul_comm]
    exact h2
  have hy : X₁ * sLimit (fun _ : m => c) d a X₁ V₁ * V₁ᵀ - -(X * Xᵀ * u * aᵀ) =
      φ * (a - V₁ * V₁ᵀ * a)ᵀ := by
    rw [mul_sLimit_mul, ← hφ, hP, ← hφu, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub]
    simp only [Matrix.mul_assoc, sub_eq_add_neg, neg_neg]
    abel
  have h3 : ‖X₁ * sLimit (fun _ : m => c) d a X₁ V₁ * V₁ᵀ - -(X * Xᵀ * u * aᵀ)‖ ≤
      ‖u‖ * (c * Φ / ‖Xᵀ * d‖) := by
    rw [hy, norm_mul_transpose_col]
    gcongr
  calc ‖X₁ * S₁ * V₁ᵀ - -(X * Xᵀ * u * aᵀ)‖
      = ‖(X₁ * S₁ * V₁ᵀ - X₁ * sLimit (fun _ : m => c) d a X₁ V₁ * V₁ᵀ) +
          (X₁ * sLimit (fun _ : m => c) d a X₁ V₁ * V₁ᵀ - -(X * Xᵀ * u * aᵀ))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ Φ + ‖u‖ * (c * Φ / ‖Xᵀ * d‖) := (norm_add_le _ _).trans (add_le_add h1 h3)
    _ = _ := by ring

/-- **AP really can fail when `V ⊥ a`, by a fixed amount, for every `ε`.**  In the setting of
`norm_iterate_sub_perp_le`, the error is bounded below by `‖a‖ dist(σ⁻¹ ∂ₓρ, range X)`
for all `ε > 0`. -/
theorem norm_iterate_sub_ge_of_perp (hc : 0 < c) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (haV : aᵀ * V = 0) (hT : 𝒯 (X * S * Vᵀ) * V = 0) (hS : IsUnit S) :
    ‖ceDir (fun _ : m => c) d - X * Xᵀ * ceDir (fun _ : m => c) d‖ * ‖a‖ ≤
      ‖X₁ * S₁ * V₁ᵀ - diffFlux (fun _ : m => c) d a‖ := by
  rw [range_eq_of_perp hc hdt hε h haV hT hS]
  exact (capture_defect_le_norm h.hX₁ h.hV₁ S₁).1

/-- With constant cross-section, `∂ₓρ ⊥ range X` and no transport in the `L`-step, the `L`-step only
rescales `V Sᵀ`, so `V₁` spans exactly `range V` at fixed rank. -/
theorem vRange_eq_of_perp (hc : 0 < c) (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (hXd : Xᵀ * d = 0) (hTL : (𝒯 (X * S * Vᵀ))ᵀ * X = 0) (hS : IsUnit S) :
    V * Vᵀ = V₁ * V₁ᵀ := by
  have hs : 0 < 1 + dt / ε ^ 2 * c := by positivity
  have hk := h.lStep
  have hdX : dᵀ * X = 0 := by
    have := congrArg Matrix.transpose hXd
    simpa [Matrix.transpose_mul] using this
  rw [hTL, hdX, stiffness_const h.hX, Matrix.mul_zero, smul_zero, sub_zero, zero_add,
    Matrix.mul_smul, Matrix.mul_one] at hk
  have h1 : (1 + dt / ε ^ 2 * c) • L₁ = V * Sᵀ := by
    rw [add_smul, one_smul, mul_smul]
    calc L₁ + (dt / ε ^ 2) • c • L₁ =
        (V * Sᵀ - (dt / ε ^ 2) • c • L₁) + (dt / ε ^ 2) • c • L₁ := by rw [← hk]
      _ = V * Sᵀ := sub_add_cancel _ _
  have hcap : V₁ * V₁ᵀ * V * Sᵀ = V * Sᵀ := by
    rw [Matrix.mul_assoc, ← h1, Matrix.mul_smul, h.lCap]
  have hSt : IsUnit Sᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hS
  exact mul_transpose_eq_of_capture rfl h.hV (cancel_right hSt hcap)

/-- **`⟨∂ₓρ, X⟩ ≠ 0` is not necessary either.**  If `∂ₓρ ⊥ range X` but `a ∈ range V` already, and
the `L`-step sees no transport, the `K`-step alone restores `σ⁻¹ ∂ₓρ` and the scheme is AP. -/
theorem norm_iterate_sub_le_of_X_perp (hc : 0 < c) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (hXd : Xᵀ * d = 0) (hTL : (𝒯 (X * S * Vᵀ))ᵀ * X = 0) (hS : IsUnit S)
    (hVa : V * Vᵀ * a = a) (hb : Vᵀ * a ≠ 0) :
    ‖X₁ * S₁ * V₁ᵀ - diffFlux (fun _ : m => c) d a‖ ≤
      (1 + kappa c c * ‖a‖ / ‖Vᵀ * a‖) *
        apPhi dt ε c τ ‖S‖ (kappa c c * ‖ceDir (fun _ : m => c) d‖ * ‖a‖) := by
  have hσ := isCrossSection_const (m := m) hc
  set Φ := apPhi dt ε c τ ‖S‖ (kappa c c * ‖ceDir (fun _ : m => c) d‖ * ‖a‖) with hΦ
  have hbn : 0 < ‖Vᵀ * a‖ := norm_pos_iff.2 hb
  have hQ := vRange_eq_of_perp hc hdt hε h hXd hTL hS
  have h1 := ap_step_bound hσ hτ0 hτ hdt hε h
  have h2 := capture_kStep hσ hτ0 hτ hdt hε h
  rw [← hΦ] at h1 h2
  rw [← hQ, hVa, sub_self] at h1
  simp only [norm_zero, mul_zero, add_zero] at h1
  have h3 : ‖ceDir (fun _ : m => c) d - X₁ * X₁ᵀ * ceDir (fun _ : m => c) d‖ ≤ Φ / ‖Vᵀ * a‖ := by
    rw [le_div_iff₀ hbn, mul_comm]
    exact h2
  have hk : 0 ≤ kappa c c := by rw [kappa_self hc]; exact zero_le_one
  calc _ ≤ Φ + kappa c c *
        (‖ceDir (fun _ : m => c) d - X₁ * X₁ᵀ * ceDir (fun _ : m => c) d‖ * ‖a‖) := h1
    _ ≤ Φ + kappa c c * (Φ / ‖Vᵀ * a‖ * ‖a‖) := by gcongr
    _ = _ := by ring

/-- **The genuinely degenerate case.**  If `a ⊥ range V` and also `∂ₓρ ⊥ range X`, and neither the
`K`- nor the `L`-step sees transport, the iterate is within `Φ` of zero and the macro flux is lost.
This is what is left of "`V ⊥ a` gives `g = 0`": both conditions are needed. -/
theorem norm_iterate_le_of_perp_perp (hc : 0 < c) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hε : 0 < ε)
    (h : IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁)
    (haV : aᵀ * V = 0) (hXd : Xᵀ * d = 0) (hTL : (𝒯 (X * S * Vᵀ))ᵀ * X = 0) (hS : IsUnit S) :
    ‖X₁ * S₁ * V₁ᵀ‖ ≤
      apPhi dt ε c τ ‖S‖ (kappa c c * ‖ceDir (fun _ : m => c) d‖ * ‖a‖) := by
  have hσ := isCrossSection_const (m := m) hc
  have hQ := vRange_eq_of_perp hc hdt hε h hXd hTL hS
  have hVa : Vᵀ * a = 0 := by
    have := congrArg Matrix.transpose haV
    simpa [Matrix.transpose_mul] using this
  have hV₁a : V₁ᵀ * a = 0 := by
    have h2 : V₁ * V₁ᵀ * a = 0 := by rw [← hQ, Matrix.mul_assoc, hVa, Matrix.mul_zero]
    have h3 : V₁ᵀ * (V₁ * V₁ᵀ * a) = V₁ᵀ * a := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V₁ᵀ, h.hV₁, Matrix.one_mul]
    rw [← h3, h2, Matrix.mul_zero]
  have h4 := norm_iterate_sub_sLimit_le hσ hτ0 hτ hdt hε h
  rwa [(sLimit_eq_zero_iff hσ h.hX₁ h.hV₁).2 (Or.inr hV₁a), sub_zero] at h4

end Perp


section Run

variable {M : Type*} [Fintype M] [DecidableEq r]

/-- A full run of the micro-macro BUG scheme: steps of fixed rank, with the macro update
`ρ_{k+1} = ρ_k + dt 𝒢ᵀ (g_{k+1} a)` of (3.2) and the drive `d_k = 𝒢 ρ_k`. -/
structure IsMicroMacroRun (σ : m → ℝ) (𝒯 : Matrix m n ℝ → Matrix m n ℝ) (𝒢 : Matrix m M ℝ)
    (a : Matrix n Unit ℝ) (dt ε : ℝ) (ρ : ℕ → Matrix M Unit ℝ) (X : ℕ → Matrix m r ℝ)
    (S : ℕ → Matrix r r ℝ) (V : ℕ → Matrix n r ℝ) : Prop where
  step : ∀ k, ∃ K₁ L₁, IsMicroMacroBUGStep σ 𝒯 (𝒢 * ρ k) a dt ε (X k) (S k) (V k) K₁ L₁
    (X (k + 1)) (V (k + 1)) (S (k + 1))
  update : ∀ k, ρ (k + 1) = ρ k + dt • (𝒢ᵀ * (X (k + 1) * S (k + 1) * (V (k + 1))ᵀ * a))

/-- The iterates of the explicit Euler scheme for the limit diffusion equation. -/
noncomputable def diffIter (𝒢 : Matrix m M ℝ) (σ : m → ℝ) (a : Matrix n Unit ℝ) (dt : ℝ)
    (ρ₀ : Matrix M Unit ℝ) : ℕ → Matrix M Unit ℝ
  | 0 => ρ₀
  | k + 1 => diffusionStep 𝒢 σ a dt (diffIter 𝒢 σ a dt ρ₀ k)

omit [DecidableEq r] in
theorem ceDir_sub (σ : m → ℝ) (x y : Matrix m Unit ℝ) :
    ceDir σ x - ceDir σ y = ceDir σ (x - y) := by
  simp only [ceDir, Matrix.mul_sub]

omit [DecidableEq r] in
theorem norm_ceDir_le {σ : m → ℝ} {σ₀ σ₁ : ℝ} (hσ : IsCrossSection σ σ₀ σ₁)
    (x : Matrix m Unit ℝ) : ‖ceDir σ x‖ ≤ σ₀⁻¹ * ‖x‖ := by
  have h1 := hσ.lower_inner (ceDir σ x)
  rw [diagonal_mul_ceDir hσ] at h1
  have h2 := real_inner_le_norm x (ceDir σ x)
  have hσ₀ := hσ.pos
  rw [inv_mul_eq_div, le_div_iff₀ hσ₀]
  by_cases h0 : ‖ceDir σ x‖ = 0
  · rw [h0, zero_mul]
    exact norm_nonneg _
  · have hpos : 0 < ‖ceDir σ x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h3 : ‖ceDir σ x‖ * (‖ceDir σ x‖ * σ₀) ≤ ‖ceDir σ x‖ * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_left h3 hpos

omit [DecidableEq r] in
/-- The macro update, compared with the diffusion step from a perturbed density. -/
theorem norm_macro_sub_le' {σ : m → ℝ} {a : Matrix n Unit ℝ} {dt : ℝ} {𝒢 : Matrix m M ℝ}
    {ρ ρb ρ₁ : Matrix M Unit ℝ} {g₁ : Matrix m n ℝ} (hdt : 0 ≤ dt)
    (hρ : ρ₁ = ρ + dt • (𝒢ᵀ * (g₁ * a))) :
    ‖ρ₁ - diffusionStep 𝒢 σ a dt ρb‖ ≤
      ‖ρ - ρb‖ + dt * ‖𝒢‖ * ‖a‖ * ‖g₁ - diffFlux σ (𝒢 * ρb) a‖ := by
  have h1 : ρ₁ - diffusionStep 𝒢 σ a dt ρb =
      (ρ - ρb) + dt • (𝒢ᵀ * ((g₁ - diffFlux σ (𝒢 * ρb) a) * a)) := by
    rw [hρ, diffusionStep, Matrix.sub_mul, diffFlux_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_smul, sub_neg_eq_add, smul_add, smul_smul]
    abel
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hdt]
  have h2 : ‖𝒢ᵀ * ((g₁ - diffFlux σ (𝒢 * ρb) a) * a)‖ ≤
      ‖𝒢‖ * (‖g₁ - diffFlux σ (𝒢 * ρb) a‖ * ‖a‖) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [norm_transpose]
    gcongr
    exact Frobenius.norm_mul_le _ _
  have h3 := mul_le_mul_of_nonneg_left h2 hdt
  nlinarith

private theorem phi_le_mul {dt ε σ₀ τ B B' F F' : ℝ} (hdt : 0 < dt) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hσ₀ : 0 < σ₀) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hBB : B ≤ B') (hF : 0 ≤ F) (hFF : F ≤ F') :
    apPhi dt ε σ₀ τ B F ≤ ((B' + F') / (dt * σ₀) + τ * B' / σ₀) * ε := by
  refine (apPhi_le hdt hε hσ₀ hτ hB hF).trans ?_
  have h1 : ε ^ 2 ≤ ε := by nlinarith
  have hB' : 0 ≤ B' := hB.trans hBB
  have hF' : 0 ≤ F' := hF.trans hFF
  have h2 : ε ^ 2 / (dt * σ₀) * (B + F) ≤ ε / (dt * σ₀) * (B' + F') := by gcongr
  have h3 : ε / σ₀ * (τ * B) ≤ ε / σ₀ * (τ * B') := by gcongr
  calc _ ≤ ε / (dt * σ₀) * (B' + F') + ε / σ₀ * (τ * B') := add_le_add h2 h3
    _ = _ := by field_simp

variable {σ : m → ℝ} {σ₀ σ₁ τ Γ dt : ℝ} {𝒯 : Matrix m n ℝ → Matrix m n ℝ} {𝒢 : Matrix m M ℝ}
  {a : Matrix n Unit ℝ}

omit [DecidableEq r] in
/-- What one step inherits from the density being `C ε`-close to the limit density. -/
private theorem step_estimates (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hdt : 0 < dt)
    {ρ ρb : Matrix M Unit ℝ} {S : Matrix r r ℝ} {C B ε η U P : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : ‖ρ - ρb‖ ≤ C * ε) (hS : ‖S‖ ≤ B)
    (hη : η = σ₀⁻¹ * ‖𝒢‖ * C) (hU : U = ‖ceDir σ (𝒢 * ρb)‖ + η)
    (hP : P = (B + kappa σ₀ σ₁ * U * ‖a‖) / (dt * σ₀) + τ * B / σ₀) :
    ‖ceDir σ (𝒢 * ρ) - ceDir σ (𝒢 * ρb)‖ ≤ η * ε ∧ ‖ceDir σ (𝒢 * ρ)‖ ≤ U ∧
      apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ (𝒢 * ρ)‖ * ‖a‖) ≤ P * ε := by
  have hσ₀ := hσ.pos
  have hk : 0 ≤ kappa σ₀ σ₁ := by linarith [hσ.one_le_kappa]
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have h1 : ‖ceDir σ (𝒢 * ρ) - ceDir σ (𝒢 * ρb)‖ ≤ η * ε := by
    rw [ceDir_sub, ← Matrix.mul_sub]
    refine (norm_ceDir_le hσ _).trans ?_
    have h2 : ‖𝒢 * (ρ - ρb)‖ ≤ ‖𝒢‖ * (C * ε) :=
      (Frobenius.norm_mul_le _ _).trans (by gcongr)
    rw [hη]
    calc σ₀⁻¹ * ‖𝒢 * (ρ - ρb)‖ ≤ σ₀⁻¹ * (‖𝒢‖ * (C * ε)) := by gcongr
      _ = _ := by ring
  have h2 : ‖ceDir σ (𝒢 * ρ)‖ ≤ U := by
    have h3 : ‖ceDir σ (𝒢 * ρ)‖ ≤ ‖ceDir σ (𝒢 * ρb)‖ + ‖ceDir σ (𝒢 * ρ) - ceDir σ (𝒢 * ρb)‖ := by
      have := norm_add_le (ceDir σ (𝒢 * ρb)) (ceDir σ (𝒢 * ρ) - ceDir σ (𝒢 * ρb))
      rwa [add_sub_cancel] at this
    have h4 : η * ε ≤ η := by nlinarith
    rw [hU]
    linarith
  refine ⟨h1, h2, ?_⟩
  rw [hP]
  exact phi_le_mul hdt hε hε1 hσ₀ hτ0 (norm_nonneg _) hS (by positivity) (by gcongr)

/-- The two capture defects of a nondegenerate step. -/
private theorem defects_le [DecidableEq p] [DecidableEq q] (hσ : IsCrossSection σ σ₀ σ₁)
    (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt) {ε : ℝ} (hε : 0 < ε)
    {d : Matrix m Unit ℝ} {X : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ}
    {K₁ : Matrix m r ℝ} {L₁ : Matrix n r ℝ} {X₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ}
    {S₁ : Matrix p q ℝ} (h : IsMicroMacroBUGStep σ 𝒯 d a dt ε X S V K₁ L₁ X₁ V₁ S₁) {β Φ : ℝ}
    (hβ : 0 < β) (hV : β ≤ ‖Vᵀ * a‖) (hX : β ≤ ‖Xᵀ * d‖)
    (hΦ : apPhi dt ε σ₀ τ ‖S‖ (kappa σ₀ σ₁ * ‖ceDir σ d‖ * ‖a‖) ≤ Φ) :
    ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ ≤ Φ / β ∧ ‖a - V₁ * V₁ᵀ * a‖ ≤ σ₁ * Φ / β := by
  have hσ₁ : 0 ≤ σ₁ := hσ.pos.le.trans hσ.le
  have h1 := capture_kStep hσ hτ0 hτ hdt hε h
  have h2 := capture_lStep hσ hτ0 hτ hdt hε h
  constructor
  · rw [le_div_iff₀ hβ, mul_comm]
    calc β * ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖
        ≤ ‖Vᵀ * a‖ * ‖ceDir σ d - X₁ * X₁ᵀ * ceDir σ d‖ := by gcongr
      _ ≤ Φ := h1.trans hΦ
  · rw [le_div_iff₀ hβ, mul_comm]
    calc β * ‖a - V₁ * V₁ᵀ * a‖ ≤ ‖Xᵀ * d‖ * ‖a - V₁ * V₁ᵀ * a‖ := by gcongr
      _ ≤ _ := h2
      _ ≤ σ₁ * Φ := by gcongr

/-- The induction hypothesis of `ap_run`. -/
private structure RunInv (𝒢 : Matrix m M ℝ) (σ : m → ℝ) (a : Matrix n Unit ℝ) (dt : ℝ)
    (ρ₀ : Matrix M Unit ℝ) (ρ' : ℝ → ℕ → Matrix M Unit ℝ) (X' : ℝ → ℕ → Matrix m r ℝ)
    (S' : ℝ → ℕ → Matrix r r ℝ) (V' : ℝ → ℕ → Matrix n r ℝ) (k : ℕ) : Prop where
  rho : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖ρ' ε k - diffIter 𝒢 σ a dt ρ₀ k‖ ≤ C * ε
  core : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖S' ε k‖ ≤ B
  nondeg : 𝒢 * diffIter 𝒢 σ a dt ρ₀ k ≠ 0 → ∃ β : ℝ, 0 < β ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    β ≤ ‖(V' ε k)ᵀ * a‖ ∧ β ≤ ‖(X' ε k)ᵀ * (𝒢 * ρ' ε k)‖

private theorem eventually_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const one_pos
  filter_upwards [h1, h2] with ε h3 h4 using ⟨h3, h4.le⟩

private theorem eventually_mul_le {W c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W * ε ≤ c := by
  have h : Tendsto (fun ε : ℝ => W * ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Continuous fun ε : ℝ => W * ε := by fun_prop
    have h2 := h1.tendsto 0
    simp only [mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  filter_upwards [h.eventually_lt_const hc] with ε h3 using h3.le

/-- The **discrete parabolic CFL condition makes the gradient persist**: `⟨∂ₓρ_{k+1}, σ⁻¹ ∂ₓρ_k⟩`
is positive along the limit scheme.  This is what lets `X_{k+1}` carry over to the next `L`-step. -/
theorem inner_next_gradient_pos (hσ : IsCrossSection σ σ₀ σ₁)
    (hΓ : ∀ x : Matrix m Unit ℝ, ‖𝒢ᵀ * x‖ ≤ Γ * ‖x‖) (hcfl : dt * ‖a‖ ^ 2 * Γ ^ 2 < σ₀)
    (hdt : 0 ≤ dt) {ρ : Matrix M Unit ℝ} (hd : 𝒢 * ρ ≠ 0) :
    0 < ⟪𝒢 * diffusionStep 𝒢 σ a dt ρ, ceDir σ (𝒢 * ρ)⟫ := by
  set u := ceDir σ (𝒢 * ρ) with hu
  have hDu : Matrix.diagonal σ * u = 𝒢 * ρ := diagonal_mul_ceDir hσ _
  have hu0 : u ≠ 0 := by
    intro h0
    apply hd
    rw [← hDu, h0, Matrix.mul_zero]
  have hun : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu0; positivity
  have h1 : ⟪𝒢 * diffusionStep 𝒢 σ a dt ρ, u⟫ =
      ⟪Matrix.diagonal σ * u, u⟫ - (dt * ‖a‖ ^ 2) * ‖𝒢ᵀ * u‖ ^ 2 := by
    rw [diffusionStep, Matrix.mul_sub, Matrix.mul_smul, inner_sub_left, real_inner_smul_left,
      inner_mul_left 𝒢 (𝒢ᵀ * u) u, real_inner_self_eq_norm_sq, ← hDu]
  have h2 := hσ.lower_inner u
  have h3 : ‖𝒢ᵀ * u‖ ^ 2 ≤ Γ ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hΓ u) 2
  have h4 : 0 ≤ dt * ‖a‖ ^ 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left h3 h4
  have h6 : 0 < (σ₀ - dt * ‖a‖ ^ 2 * Γ ^ 2) * ‖u‖ ^ 2 := mul_pos (by linarith) hun
  rw [h1]
  nlinarith


/-- The induction step of `ap_run`: closeness at step `k` gives the flux at step `k + 1` and
propagates closeness, boundedness and nondegeneracy. -/
private theorem run_step (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ)
    (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt)
    (hΓ : ∀ x : Matrix m Unit ℝ, ‖𝒢ᵀ * x‖ ≤ Γ * ‖x‖) (hcfl : dt * ‖a‖ ^ 2 * Γ ^ 2 < σ₀)
    (ha : a ≠ 0) {ρ₀ : Matrix M Unit ℝ} {ρ' : ℝ → ℕ → Matrix M Unit ℝ}
    {X' : ℝ → ℕ → Matrix m r ℝ} {S' : ℝ → ℕ → Matrix r r ℝ} {V' : ℝ → ℕ → Matrix n r ℝ}
    (hrun : ∀ ε > 0, IsMicroMacroRun σ 𝒯 𝒢 a dt ε (ρ' ε) (X' ε) (S' ε) (V' ε)) {k : ℕ}
    (hinv : RunInv 𝒢 σ a dt ρ₀ ρ' X' S' V' k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ -
        diffFlux σ (𝒢 * diffIter 𝒢 σ a dt ρ₀ k) a‖ ≤ C * ε) ∧
      RunInv 𝒢 σ a dt ρ₀ ρ' X' S' V' (k + 1) := by
  obtain ⟨Cρ, hCρ0, hρ⟩ := hinv.rho
  obtain ⟨B, hB0, hB⟩ := hinv.core
  set ρb := diffIter 𝒢 σ a dt ρ₀ k with hρb
  have hnext : diffIter 𝒢 σ a dt ρ₀ (k + 1) = diffusionStep 𝒢 σ a dt ρb := rfl
  set ub := ceDir σ (𝒢 * ρb) with hub
  set Gb := diffFlux σ (𝒢 * ρb) a with hGb
  set κ := kappa σ₀ σ₁ with hκdef
  have hκ1 : 1 ≤ κ := hσ.one_le_kappa
  have hκ0 : 0 ≤ κ := by linarith
  have hσ₀ := hσ.pos
  have hσ₁ : 0 ≤ σ₁ := hσ₀.le.trans hσ.le
  set η := σ₀⁻¹ * ‖𝒢‖ * Cρ with hη
  set U := ‖ub‖ + η with hU
  set P := (B + κ * U * ‖a‖) / (dt * σ₀) + τ * B / σ₀ with hP
  have hη0 : 0 ≤ η := by positivity
  have hU0 : 0 ≤ U := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hbase : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 ∧ ‖ρ' ε k - ρb‖ ≤ Cρ * ε ∧ ‖S' ε k‖ ≤ B := by
    filter_upwards [eventually_small, hρ, hB] with ε h1 h2 h3 using ⟨h1.1, h1.2, h2, h3⟩
  -- the flux converges, in both cases
  have hflux : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ - Gb‖ ≤ C * ε := by
    by_cases hd : 𝒢 * ρb = 0
    · refine ⟨P + κ * η * ‖a‖, by positivity, ?_⟩
      filter_upwards [hbase] with ε h0
      obtain ⟨hε, hε1, h1, h2⟩ := h0
      obtain ⟨K₁, L₁, hs⟩ := (hrun ε hε).step k
      obtain ⟨h3, -, h5⟩ := step_estimates (a := a) (𝒢 := 𝒢) hσ hτ0 hdt hCρ0 hε hε1 h1 h2
        hη hU hP
      have hub0 : ub = 0 := by rw [hub, hd]; simp [ceDir]
      have hGb0 : Gb = 0 := by rw [hGb, diffFlux, ← hub, hub0]; simp
      rw [← hub, hub0, sub_zero] at h3
      have h6 := norm_iterate_sub_sLimit_le hσ hτ0 hτ hdt hε hs
      have h7 : ‖X' ε (k + 1) * sLimit σ (𝒢 * ρ' ε k) a (X' ε (k + 1)) (V' ε (k + 1)) *
          (V' ε (k + 1))ᵀ‖ ≤ κ * ‖ceDir σ (𝒢 * ρ' ε k)‖ * ‖a‖ := by
        rw [mul_sLimit_mul, norm_neg]
        refine (norm_limit_le hs.hV₁ _ a).trans ?_
        gcongr
        exact norm_galerkinFlux_le hσ hs.hX₁ _
      have h8 : κ * ‖ceDir σ (𝒢 * ρ' ε k)‖ * ‖a‖ ≤ κ * (η * ε) * ‖a‖ := by gcongr
      rw [hGb0, sub_zero]
      calc ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ‖
          ≤ ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ -
              X' ε (k + 1) * sLimit σ (𝒢 * ρ' ε k) a (X' ε (k + 1)) (V' ε (k + 1)) *
                (V' ε (k + 1))ᵀ‖ +
            ‖X' ε (k + 1) * sLimit σ (𝒢 * ρ' ε k) a (X' ε (k + 1)) (V' ε (k + 1)) *
                (V' ε (k + 1))ᵀ‖ := norm_le_norm_sub_add _ _
        _ ≤ P * ε + κ * (η * ε) * ‖a‖ := add_le_add (h6.trans h5) (h7.trans h8)
        _ = _ := by ring
    · obtain ⟨β, hβ, hnd⟩ := hinv.nondeg hd
      refine ⟨P * (1 + κ * (‖a‖ + U * σ₁) / β) + η * ‖a‖, by positivity, ?_⟩
      filter_upwards [hbase, hnd] with ε h0 hn0
      obtain ⟨hε, hε1, h1, h2⟩ := h0
      obtain ⟨hV, hX⟩ := hn0
      obtain ⟨K₁, L₁, hs⟩ := (hrun ε hε).step k
      obtain ⟨h3, h4, h5⟩ := step_estimates (a := a) (𝒢 := 𝒢) hσ hτ0 hdt hCρ0 hε hε1 h1 h2
        hη hU hP
      obtain ⟨h6, h7⟩ := defects_le hσ hτ0 hτ hdt hε hs hβ hV hX h5
      have h8 := ap_step_bound hσ hτ0 hτ hdt hε hs
      have h9 : ‖diffFlux σ (𝒢 * ρ' ε k) a - Gb‖ ≤ η * ε * ‖a‖ := by
        have h10 : diffFlux σ (𝒢 * ρ' ε k) a - Gb = -((ceDir σ (𝒢 * ρ' ε k) - ub) * aᵀ) := by
          rw [hGb, diffFlux, diffFlux, ← hub, Matrix.sub_mul]
          abel
        rw [h10, norm_neg, norm_mul_transpose_col]
        gcongr
      have h11 : ‖ceDir σ (𝒢 * ρ' ε k) - X' ε (k + 1) * (X' ε (k + 1))ᵀ * ceDir σ (𝒢 * ρ' ε k)‖ *
            ‖a‖ + ‖ceDir σ (𝒢 * ρ' ε k)‖ * ‖a - V' ε (k + 1) * (V' ε (k + 1))ᵀ * a‖ ≤
          (P * ε / β) * ‖a‖ + U * (σ₁ * (P * ε) / β) := by gcongr
      calc ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ - Gb‖
          ≤ ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ - diffFlux σ (𝒢 * ρ' ε k) a‖ +
              ‖diffFlux σ (𝒢 * ρ' ε k) a - Gb‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (P * ε + κ * ((P * ε / β) * ‖a‖ + U * (σ₁ * (P * ε) / β))) + η * ε * ‖a‖ := by
            refine add_le_add (h8.trans (add_le_add h5 ?_)) h9
            exact mul_le_mul_of_nonneg_left h11 hκ0
        _ = _ := by field_simp
  obtain ⟨C₁, hC₁0, hC₁⟩ := hflux
  refine ⟨⟨C₁, hC₁0, hC₁⟩, ?_⟩
  -- the density stays close
  have hrho : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖ρ' ε (k + 1) - diffIter 𝒢 σ a dt ρ₀ (k + 1)‖ ≤ C * ε := by
    refine ⟨Cρ + dt * ‖𝒢‖ * ‖a‖ * C₁, by positivity, ?_⟩
    filter_upwards [hbase, hC₁] with ε h0 h2
    obtain ⟨hε, -, h1, -⟩ := h0
    rw [hnext]
    have h3 := norm_macro_sub_le' (σ := σ) (ρb := ρb) hdt.le ((hrun ε hε).update k)
    have hc : 0 ≤ dt * ‖𝒢‖ * ‖a‖ := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    calc _ ≤ _ := h3
      _ ≤ Cρ * ε + dt * ‖𝒢‖ * ‖a‖ * (C₁ * ε) := add_le_add h1 h4
      _ = _ := by ring
  obtain ⟨Cρ₁, hCρ₁0, hρ₁⟩ := id hrho
  refine ⟨hrho, ?_, ?_⟩
  · -- the core stays bounded
    refine ⟨‖Gb‖ + C₁, by positivity, ?_⟩
    filter_upwards [hbase, hC₁] with ε h0 h2
    obtain ⟨hε, hε1, -, -⟩ := h0
    obtain ⟨K₁, L₁, hs⟩ := (hrun ε hε).step k
    have h3 : ‖S' ε (k + 1)‖ =
        ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ‖ := by
      rw [norm_mul_transpose_of_orthonormal hs.hV₁, norm_mul_of_orthonormal hs.hX₁]
    have h4 := norm_le_norm_sub_add (X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ) Gb
    have h5 : C₁ * ε ≤ C₁ := by nlinarith
    linarith
  · -- nondegeneracy persists: this is where the CFL condition is used
    intro hd₁
    have hd : 𝒢 * ρb ≠ 0 := by
      intro h0
      apply hd₁
      have hub0 : ub = 0 := by rw [hub, h0]; simp [ceDir]
      rw [hnext, diffusionStep, ← hub, hub0, Matrix.mul_zero, smul_zero, sub_zero, h0]
    obtain ⟨β, hβ, hnd⟩ := hinv.nondeg hd
    have hθ := inner_next_gradient_pos (a := a) (𝒢 := 𝒢) hσ hΓ hcfl hdt.le hd
    rw [← hnext, ← hub] at hθ
    set db₁ := 𝒢 * diffIter 𝒢 σ a dt ρ₀ (k + 1) with hdb₁
    set θ := ⟪db₁, ub⟫ with hθdef
    have hub0 : ub ≠ 0 := by
      intro h0
      rw [hθdef, h0, inner_zero_right] at hθ
      exact lt_irrefl _ hθ
    have hubn : 0 < ‖ub‖ := norm_pos_iff.2 hub0
    have han : 0 < ‖a‖ := norm_pos_iff.2 ha
    set D₁ := ‖db₁‖ + ‖𝒢‖ * Cρ₁ with hD₁
    set W := ‖𝒢‖ * Cρ₁ * ‖ub‖ + D₁ * (P / β + η) with hW
    refine ⟨min (‖a‖ / 2) (θ / (2 * ‖ub‖)), lt_min (by positivity) (by positivity), ?_⟩
    filter_upwards [hbase, hρ₁, hnd, eventually_mul_le (W := W) (half_pos hθ),
      eventually_mul_le (W := σ₁ * P / β) (half_pos han)] with ε h0 h3 hn0 h4 h5
    obtain ⟨hε, hε1, h1, h2⟩ := h0
    obtain ⟨hV, hX⟩ := hn0
    obtain ⟨K₁, L₁, hs⟩ := (hrun ε hε).step k
    obtain ⟨h6, -, h8⟩ := step_estimates (a := a) (𝒢 := 𝒢) hσ hτ0 hdt hCρ0 hε hε1 h1 h2
      hη hU hP
    obtain ⟨h9, h10⟩ := defects_le hσ hτ0 hτ hdt hε hs hβ hV hX h8
    constructor
    · -- the direction `a` stays in the velocity basis
      refine (min_le_left _ _).trans ?_
      have h11 : ‖(V' ε (k + 1))ᵀ * a‖ = ‖V' ε (k + 1) * (V' ε (k + 1))ᵀ * a‖ := by
        rw [Matrix.mul_assoc, norm_mul_of_orthonormal hs.hV₁]
      have h12 : ‖a‖ ≤ ‖a - V' ε (k + 1) * (V' ε (k + 1))ᵀ * a‖ +
          ‖V' ε (k + 1) * (V' ε (k + 1))ᵀ * a‖ := norm_le_norm_sub_add _ _
      have h13 : σ₁ * (P * ε) / β = σ₁ * P / β * ε := by ring
      rw [h13] at h10
      rw [h11]
      linarith
    · -- `∂ₓρ_{k+1}` is not orthogonal to the new spatial basis, by the CFL condition
      refine (min_le_right _ _).trans ?_
      set Y := X' ε (k + 1) with hY
      set d₁ := 𝒢 * ρ' ε (k + 1) with hd₁def
      set u := ceDir σ (𝒢 * ρ' ε k) with hu
      have hd₁near : ‖d₁ - db₁‖ ≤ ‖𝒢‖ * (Cρ₁ * ε) := by
        rw [hd₁def, hdb₁, ← Matrix.mul_sub]
        exact (Frobenius.norm_mul_le _ _).trans (by gcongr)
      have hd₁le : ‖d₁‖ ≤ D₁ := by
        have h11 := norm_le_norm_sub_add d₁ db₁
        have h12 : ‖𝒢‖ * (Cρ₁ * ε) ≤ ‖𝒢‖ * Cρ₁ := by
          have : Cρ₁ * ε ≤ Cρ₁ := by nlinarith
          gcongr
        rw [hD₁]
        linarith
      have hub' : ‖ub - Y * Yᵀ * ub‖ ≤ (P / β + η) * ε := by
        have h11 : ub - Y * Yᵀ * ub = (u - Y * Yᵀ * u) + ((ub - u) - Y * Yᵀ * (ub - u)) := by
          rw [Matrix.mul_sub]
          abel
        have h12 : ‖(ub - u) - Y * Yᵀ * (ub - u)‖ ≤ ‖ub - u‖ := by
          simpa using (isOrthProj_leftProj (n := Unit) hs.hX₁).norm_sub_le (ub - u)
        have h13 : ‖ub - u‖ ≤ η * ε := by rw [norm_sub_rev]; exact h6
        have h14 : P * ε / β = P / β * ε := by ring
        rw [h14] at h9
        rw [h11]
        refine (norm_add_le _ _).trans ?_
        calc _ ≤ P / β * ε + η * ε := add_le_add h9 (h12.trans h13)
          _ = _ := by ring
      have hkey : ⟪d₁, Y * Yᵀ * ub⟫ ≤ ‖Yᵀ * d₁‖ * ‖ub‖ := by
        have h11 : ⟪d₁, Y * Yᵀ * ub⟫ = ⟪Yᵀ * d₁, Yᵀ * ub⟫ := by
          rw [Matrix.mul_assoc, inner_mul_left']
        rw [h11]
        refine (real_inner_le_norm _ _).trans ?_
        gcongr
        exact norm_transpose_mul_le hs.hX₁ ub
      have hlow : θ / 2 ≤ ⟪d₁, Y * Yᵀ * ub⟫ := by
        have h11 : ⟪d₁, Y * Yᵀ * ub⟫ =
            θ + ⟪d₁ - db₁, ub⟫ - ⟪d₁, ub - Y * Yᵀ * ub⟫ := by
          rw [inner_sub_left, inner_sub_right]
          ring
        have h12 : -(‖d₁ - db₁‖ * ‖ub‖) ≤ ⟪d₁ - db₁, ub⟫ := by
          have := abs_real_inner_le_norm (d₁ - db₁) ub
          exact (abs_le.1 this).1
        have h13 : ⟪d₁, ub - Y * Yᵀ * ub⟫ ≤ ‖d₁‖ * ‖ub - Y * Yᵀ * ub‖ := real_inner_le_norm _ _
        have h14 : ‖d₁ - db₁‖ * ‖ub‖ ≤ ‖𝒢‖ * (Cρ₁ * ε) * ‖ub‖ := by gcongr
        have h15 : ‖d₁‖ * ‖ub - Y * Yᵀ * ub‖ ≤ D₁ * ((P / β + η) * ε) := by gcongr
        have h16 : W * ε = ‖𝒢‖ * (Cρ₁ * ε) * ‖ub‖ + D₁ * ((P / β + η) * ε) := by
          rw [hW]
          ring
        rw [h11]
        linarith
      rw [div_le_iff₀ (by positivity)]
      calc θ = 2 * (θ / 2) := by ring
        _ ≤ 2 * (‖Yᵀ * d₁‖ * ‖ub‖) :=
            mul_le_mul_of_nonneg_left (hlow.trans hkey) (by norm_num)
        _ = ‖Yᵀ * d₁‖ * (2 * ‖ub‖) := by ring

/-- **AP of the full run, with the nondegeneracy needed only at the first step.**  Consider the
micro-macro BUG scheme of arXiv 2212.12012 at fixed `dt`, fixed mesh and fixed rank `r`, for any
choice of capturing bases, with data independent of `ε`.  If `V₀ᵀ a ≠ 0`, `X₀ᵀ ∂ₓρ₀ ≠ 0` and the
parabolic CFL condition `dt ‖a‖² Γ² < σ₀` holds, then for every step `k`, as `ε → 0`,
`‖ρ_k - ρ̄_k‖ = O(ε)` and `‖g_{k+1} + σ⁻¹ ∂ₓρ̄_k aᵀ‖ = O(ε)`, where `ρ̄_k` are the explicit Euler
iterates of the limit diffusion equation (4.9).

The nondegeneracy is not assumed along the run: `a` stays in the velocity basis, and the CFL
condition keeps `∂ₓρ_{k+1}` from becoming orthogonal to the new spatial basis
(`inner_next_gradient_pos`).  Compare the assumptions listed under OP-ST-07 and OP-ST-21.  The
constants depend on `k` and on the mesh, so this is the limit at a fixed number of steps and fixed
discretisation, not a uniform-in-time or uniform-in-mesh estimate.  The CFL condition is sufficient
for this propagation; it is not shown to be necessary. -/
theorem ap_run (hσ : IsCrossSection σ σ₀ σ₁) (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖)
    (hdt : 0 < dt) (hΓ : ∀ x : Matrix m Unit ℝ, ‖𝒢ᵀ * x‖ ≤ Γ * ‖x‖)
    (hcfl : dt * ‖a‖ ^ 2 * Γ ^ 2 < σ₀) {ρ₀ : Matrix M Unit ℝ} {X₀ : Matrix m r ℝ}
    {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {ρ' : ℝ → ℕ → Matrix M Unit ℝ}
    {X' : ℝ → ℕ → Matrix m r ℝ} {S' : ℝ → ℕ → Matrix r r ℝ} {V' : ℝ → ℕ → Matrix n r ℝ}
    (hrun : ∀ ε > 0, IsMicroMacroRun σ 𝒯 𝒢 a dt ε (ρ' ε) (X' ε) (S' ε) (V' ε))
    (h0 : ∀ ε > 0, ρ' ε 0 = ρ₀ ∧ X' ε 0 = X₀ ∧ S' ε 0 = S₀ ∧ V' ε 0 = V₀)
    (hb : V₀ᵀ * a ≠ 0) (hc : X₀ᵀ * (𝒢 * ρ₀) ≠ 0) (k : ℕ) :
    (∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖ρ' ε k - diffIter 𝒢 σ a dt ρ₀ k‖ ≤ C * ε) ∧
      (∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ‖X' ε (k + 1) * S' ε (k + 1) * (V' ε (k + 1))ᵀ -
          diffFlux σ (𝒢 * diffIter 𝒢 σ a dt ρ₀ k) a‖ ≤ C * ε) := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hb (Matrix.mul_zero _)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hinv : ∀ j, RunInv 𝒢 σ a dt ρ₀ ρ' X' S' V' j := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨0, le_rfl, ?_⟩, ⟨‖S₀‖, norm_nonneg _, ?_⟩, fun _ => ?_⟩
      · filter_upwards [hpos] with ε hε
        rw [(h0 ε hε).1]
        simp [diffIter]
      · filter_upwards [hpos] with ε hε
        rw [(h0 ε hε).2.2.1]
      · refine ⟨min ‖V₀ᵀ * a‖ ‖X₀ᵀ * (𝒢 * ρ₀)‖,
          lt_min (norm_pos_iff.2 hb) (norm_pos_iff.2 hc), ?_⟩
        filter_upwards [hpos] with ε hε
        obtain ⟨h1, h2, -, h4⟩ := h0 ε hε
        rw [h1, h2, h4]
        exact ⟨min_le_left _ _, min_le_right _ _⟩
    | succ j ih => exact (run_step hσ hτ0 hτ hdt hΓ hcfl ha hrun ih).2
  obtain ⟨C₁, -, h1⟩ := (hinv k).rho
  obtain ⟨C₂, -, h2⟩ := (run_step hσ hτ0 hτ hdt hΓ hcfl ha hrun (hinv k)).1
  exact ⟨⟨C₁, h1⟩, ⟨C₂, h2⟩⟩

/-- Runs exist: `IsMicroMacroRun` is never vacuous, for any orthonormal initial bases. -/
theorem exists_run {k₀ : ℕ} (hm : k₀ ≤ Fintype.card m) (hn : k₀ ≤ Fintype.card n)
    (hσ : IsCrossSection σ σ₀ σ₁) (hdt : 0 < dt) {ε : ℝ} (hε : 0 < ε)
    (𝒯 : Matrix m n ℝ → Matrix m n ℝ) (𝒢 : Matrix m M ℝ) (a : Matrix n Unit ℝ)
    (ρ₀ : Matrix M Unit ℝ) {X₀ : Matrix m (Fin k₀) ℝ} (S₀ : Matrix (Fin k₀) (Fin k₀) ℝ)
    {V₀ : Matrix n (Fin k₀) ℝ} (hX₀ : X₀ᵀ * X₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (ρ : ℕ → Matrix M Unit ℝ) (X : ℕ → Matrix m (Fin k₀) ℝ)
      (S : ℕ → Matrix (Fin k₀) (Fin k₀) ℝ) (V : ℕ → Matrix n (Fin k₀) ℝ),
      IsMicroMacroRun σ 𝒯 𝒢 a dt ε ρ X S V ∧ ρ 0 = ρ₀ ∧ X 0 = X₀ ∧ S 0 = S₀ ∧ V 0 = V₀ := by
  let St := {t : Matrix M Unit ℝ × Matrix m (Fin k₀) ℝ × Matrix (Fin k₀) (Fin k₀) ℝ ×
    Matrix n (Fin k₀) ℝ // t.2.1ᵀ * t.2.1 = 1 ∧ t.2.2.2ᵀ * t.2.2.2 = 1}
  have hnext : ∀ t : St, ∃ t' : St, (∃ K₁ L₁, IsMicroMacroBUGStep σ 𝒯 (𝒢 * t.1.1) a dt ε t.1.2.1
      t.1.2.2.1 t.1.2.2.2 K₁ L₁ t'.1.2.1 t'.1.2.2.2 t'.1.2.2.1) ∧
      t'.1.1 = t.1.1 + dt • (𝒢ᵀ * (t'.1.2.1 * t'.1.2.2.1 * t'.1.2.2.2ᵀ * a)) := by
    intro t
    obtain ⟨K₁, L₁, X₁, V₁, S₁, hs⟩ := exists_step hm hn hσ hdt hε 𝒯 (𝒢 * t.1.1) a t.1.2.2.1
      t.2.1 t.2.2
    exact ⟨⟨(t.1.1 + dt • (𝒢ᵀ * (X₁ * S₁ * V₁ᵀ * a)), X₁, S₁, V₁), hs.hX₁, hs.hV₁⟩,
      ⟨K₁, L₁, hs⟩, rfl⟩
  choose f hf using hnext
  let seq : ℕ → St := fun k => Nat.rec ⟨(ρ₀, X₀, S₀, V₀), hX₀, hV₀⟩ (fun _ t => f t) k
  refine ⟨fun k => (seq k).1.1, fun k => (seq k).1.2.1, fun k => (seq k).1.2.2.1,
    fun k => (seq k).1.2.2.2, ⟨fun k => (hf (seq k)).1, fun k => (hf (seq k)).2⟩,
    rfl, rfl, rfl, rfl⟩

end Run


section Instances

/-- The flux matrix of the `P₂` system, (2.7) of the paper, with off-diagonal entry `α`. -/
def fluxP2 (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, α; α, 0]

/-- A skew-symmetric difference matrix on two periodic cells. -/
def skewD : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The transport `g ↦ D g A` of the `P₂` system, a true transport operator: the examples below do
not rely on switching transport off. -/
def transportP2 (α : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  skewD * g * fluxP2 α

/-- The unit columns, as rank-one bases. -/
def eCol (i : Fin 2) : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun j _ => if j = i then 1 else 0

/-- The unit columns, as vectors. -/
def eVec (i : Fin 2) : Matrix (Fin 2) Unit ℝ := Matrix.of fun j _ => if j = i then 1 else 0

theorem norm_transportP2_le (α : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖transportP2 α x‖ ≤ (‖skewD‖ * ‖fluxP2 α‖) * ‖x‖ := by
  rw [transportP2]
  refine (Frobenius.norm_mul_le _ _).trans ?_
  have h := Frobenius.norm_mul_le skewD x
  calc ‖skewD * x‖ * ‖fluxP2 α‖ ≤ (‖skewD‖ * ‖x‖) * ‖fluxP2 α‖ := by gcongr
    _ = _ := by ring

theorem eCol_orth (i : Fin 2) : (eCol i)ᵀ * eCol i = 1 := by
  ext a b
  obtain rfl : a = 0 := Subsingleton.elim _ _
  obtain rfl : b = 0 := Subsingleton.elim _ _
  fin_cases i <;> simp [Matrix.mul_apply, eCol]

theorem eVec_orth (i : Fin 2) : (eVec i)ᵀ * eVec i = 1 := by
  ext a b
  fin_cases i <;> simp [Matrix.mul_apply, eVec]

theorem eVec_perp : (eVec 0)ᵀ * eCol 1 = 0 := by
  ext a b
  simp [Matrix.mul_apply, eVec, eCol]

private theorem flux_quad (α : ℝ) : (eCol 1)ᵀ * (fluxP2 α * eCol 1) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  simp [fluxP2, eCol]

private theorem skew_quad (i : Fin 2) : (eCol i)ᵀ * (skewDᵀ * eCol i) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> simp [skewD, eCol]

theorem transportP2_kStep (α : ℝ) :
    transportP2 α (eCol 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol 1)ᵀ) * eCol 1 = 0 := by
  calc transportP2 α (eCol 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol 1)ᵀ) * eCol 1
      = skewD * eCol 0 * ((eCol 1)ᵀ * (fluxP2 α * eCol 1)) := by
        simp only [transportP2, Matrix.mul_one, Matrix.mul_assoc]
    _ = 0 := by rw [flux_quad, Matrix.mul_zero]

private theorem transportP2_lStep_aux (α : ℝ) (i j : Fin 2) :
    (transportP2 α (eCol i * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol j)ᵀ))ᵀ * eCol i = 0 := by
  calc (transportP2 α (eCol i * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol j)ᵀ))ᵀ * eCol i
      = (fluxP2 α)ᵀ * (eCol j * ((eCol i)ᵀ * (skewDᵀ * eCol i))) := by
        simp only [transportP2, Matrix.mul_one, Matrix.mul_assoc, Matrix.transpose_mul,
          Matrix.transpose_transpose]
    _ = 0 := by rw [skew_quad, Matrix.mul_zero, Matrix.mul_zero]

theorem transportP2_lStep (α : ℝ) :
    (transportP2 α (eCol 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol 1)ᵀ))ᵀ * eCol 0 = 0 :=
  transportP2_lStep_aux α 0 1

/-- The limit of `norm_iterate_sub_perp_le`, as a statement about a family of steps. -/
theorem tendsto_iterate_perp {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m]
    [DecidableEq r] {c τ dt : ℝ} {𝒯 : Matrix m n ℝ → Matrix m n ℝ}
    {d : Matrix m Unit ℝ} {a : Matrix n Unit ℝ} {X : Matrix m r ℝ} {S : Matrix r r ℝ}
    {V : Matrix n r ℝ} {K₁' : ℝ → Matrix m r ℝ} {L₁' : ℝ → Matrix n r ℝ}
    {X₁' : ℝ → Matrix m r ℝ} {V₁' : ℝ → Matrix n r ℝ} {S₁' : ℝ → Matrix r r ℝ} (hc : 0 < c)
    (hτ0 : 0 ≤ τ) (hτ : ∀ x, ‖𝒯 x‖ ≤ τ * ‖x‖) (hdt : 0 < dt)
    (h : ∀ ε > 0, IsMicroMacroBUGStep (fun _ : m => c) 𝒯 d a dt ε X S V (K₁' ε) (L₁' ε) (X₁' ε)
      (V₁' ε) (S₁' ε))
    (haV : aᵀ * V = 0) (hT : 𝒯 (X * S * Vᵀ) * V = 0) (hS : IsUnit S) (hXd : Xᵀ * d ≠ 0) :
    Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ - -(X * Xᵀ * ceDir (fun _ : m => c) d * aᵀ)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hk : 0 ≤ kappa c c := by rw [kappa_self hc]; exact zero_le_one
  have hΦ := (tendsto_apPhi (B := ‖S‖) (F := kappa c c * ‖ceDir (fun _ : m => c) d‖ * ‖a‖) hdt hc
    hτ0 (norm_nonneg _) (by positivity)).const_mul
      (1 + c * ‖ceDir (fun _ : m => c) d‖ / ‖Xᵀ * d‖)
  rw [mul_zero] at hΦ
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hΦ
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_iterate_sub_perp_le hc hτ0 hτ hdt hε (h ε hε) haV hT hS hXd

variable {α dt : ℝ} {K₁' : ℝ → Matrix (Fin 2) (Fin 1) ℝ} {L₁' : ℝ → Matrix (Fin 2) (Fin 1) ℝ}
  {X₁' : ℝ → Matrix (Fin 2) (Fin 1) ℝ} {V₁' : ℝ → Matrix (Fin 2) (Fin 1) ℝ}
  {S₁' : ℝ → Matrix (Fin 1) (Fin 1) ℝ}

private theorem ceDir_one (d : Matrix (Fin 2) Unit ℝ) : ceDir (fun _ : Fin 2 => (1 : ℝ)) d = d := by
  rw [ceDir_const, inv_one, one_smul]

/-- **`V ⊥ a` does not prevent AP: the "only if" of Theorem I is false.**  For the `P₂`
transport at rank one with `a = e₀`, `V = e₁ ⊥ a` and `X = e₀ ∥ ∂ₓρ = e₀`, the scheme is AP: for
every family of steps, `g₁ → G ≠ 0`.  The steps exist by `exists_step`.  This is special: it needs
constant `σ` and `𝒯 (X S Vᵀ) V = 0`, and for a generic `V ⊥ a` the scheme is not AP. -/
theorem ap_holds_with_V_perp_a (hdt : 0 < dt)
    (h : ∀ ε > 0, IsMicroMacroBUGStep (fun _ : Fin 2 => (1 : ℝ)) (transportP2 α) (eVec 0) (eVec 0)
      dt ε (eCol 0) 1 (eCol 1) (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε) (S₁' ε)) :
    (eVec 0)ᵀ * eCol 1 = 0 ∧ diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0) ≠ 0 ∧
      Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ -
        diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0)‖) (𝓝[>] 0) (𝓝 0) := by
  have hXd : (eCol 0)ᵀ * eVec 0 ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 0) ()
    simp [Matrix.mul_apply, eCol, eVec] at this
  have hcap : eCol 0 * (eCol 0)ᵀ * eVec 0 = eVec 0 := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, eCol, eVec]
  refine ⟨eVec_perp, ?_, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp [diffFlux, ceDir_one, Matrix.mul_apply, eVec] at this
  · have h1 := tendsto_iterate_perp one_pos (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_transportP2_le α) hdt h eVec_perp (transportP2_kStep α) isUnit_one hXd
    rw [ceDir_one, hcap] at h1
    simpa [diffFlux, ceDir_one] using h1

/-- **`V ⊥ a` does not give `g = 0`, and the published hypothesis does not rescue rank one.**  With
`∂ₓρ = e₀ + e₁`, `V = e₁ ⊥ a = e₀` and `X = e₀`, the iterate tends to the nonzero wrong limit
`-e₀ e₀ᵀ`, and misses the diffusive flux by at least `1` for every `ε`.  Yet at this rank one the
hypothesis of the published proof holds (`L₀ = V₁ S_L` with `S_L ⟨X Xᵀ σ⟩` invertible): it says
nothing about `σ⁻¹ ∂ₓρ ∈ range X₁`, which is the condition `aᵀ V ≠ 0` it omits. -/
theorem ap_fails_with_V_perp_a (hdt : 0 < dt)
    (h : ∀ ε > 0, IsMicroMacroBUGStep (fun _ : Fin 2 => (1 : ℝ)) (transportP2 α)
      (eVec 0 + eVec 1) (eVec 0) dt ε (eCol 0) 1 (eCol 1) (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε)
      (S₁' ε)) :
    (eVec 0)ᵀ * eCol 1 = 0 ∧
      Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ - -(eVec 0 * (eVec 0)ᵀ)‖) (𝓝[>] 0) (𝓝 0) ∧
      -(eVec 0 * (eVec 0)ᵀ) ≠ (0 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      (∀ ε > 0, 1 ≤ ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ -
        diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0 + eVec 1) (eVec 0)‖) ∧
      (∃ (V₁ : Matrix (Fin 2) (Fin 1) ℝ) (SL : Matrix (Fin 1) (Fin 1) ℝ), V₁ᵀ * V₁ = 1 ∧
        lLimit (fun _ : Fin 2 => (1 : ℝ)) (eVec 0 + eVec 1) (eVec 0) (eCol 0) = V₁ * SL ∧
        IsUnit (SL * stiffness (fun _ : Fin 2 => (1 : ℝ)) (eCol 0))) := by
  have hXd : (eCol 0)ᵀ * (eVec 0 + eVec 1) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 0) ()
    simp [Matrix.mul_apply, eCol, eVec] at this
  have hcap : eCol 0 * (eCol 0)ᵀ * (eVec 0 + eVec 1) = eVec 0 := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, eCol, eVec]
  have hstiff : stiffness (fun _ : Fin 2 => (1 : ℝ)) (eCol 0) = 1 := by
    rw [stiffness_const (eCol_orth 0), one_smul]
  refine ⟨eVec_perp, ?_, ?_, ?_, ?_⟩
  · have h1 := tendsto_iterate_perp one_pos (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_transportP2_le α) hdt h eVec_perp (transportP2_kStep α) isUnit_one hXd
    rwa [ceDir_one, hcap] at h1
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp [Matrix.mul_apply, eVec] at this
  · intro ε hε
    have h1 := norm_iterate_sub_ge_of_perp one_pos hdt hε (h ε hε) eVec_perp
      (transportP2_kStep α) isUnit_one
    rw [ceDir_one, hcap, add_sub_cancel_left, norm_eq_one_of_orthonormal (eVec_orth 1),
      norm_eq_one_of_orthonormal (eVec_orth 0), one_mul] at h1
    exact h1
  · refine ⟨eCol 0, -1, eCol_orth 0, ?_, ?_⟩
    · have hc : lCoeff (fun _ : Fin 2 => (1 : ℝ)) (eVec 0 + eVec 1) (eCol 0) =
          (eCol 0)ᵀ * (eVec 0 + eVec 1) := by
        rw [lCoeff, hstiff, inv_one, Matrix.one_mul]
      rw [lLimit, hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, eCol, eVec]
    · rw [hstiff, mul_one]
      exact isUnit_one.neg

/-- **The true degenerate case.**  If also `∂ₓρ = e₁ ⊥ X = e₀`, the iterate tends to `0` while the
diffusive flux does not vanish: the diffusion is lost altogether. -/
theorem ap_lost_with_both_perp (hdt : 0 < dt)
    (h : ∀ ε > 0, IsMicroMacroBUGStep (fun _ : Fin 2 => (1 : ℝ)) (transportP2 α) (eVec 1) (eVec 0)
      dt ε (eCol 0) 1 (eCol 1) (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε) (S₁' ε)) :
    diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 1) (eVec 0) ≠ 0 ∧
      Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ‖) (𝓝[>] 0) (𝓝 0) := by
  have hXd : (eCol 0)ᵀ * eVec 1 = 0 := by
    ext i j
    simp [Matrix.mul_apply, eCol, eVec]
  refine ⟨?_, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 1) 0
    simp [diffFlux, ceDir_one, Matrix.mul_apply, eVec] at this
  · have hτ := norm_transportP2_le α
    have hτ0 : 0 ≤ ‖skewD‖ * ‖fluxP2 α‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hk : 0 ≤ kappa 1 1 := by rw [kappa_self one_pos]; exact zero_le_one
    have hΦ := tendsto_apPhi (B := ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖)
      (F := kappa 1 1 * ‖ceDir (fun _ : Fin 2 => (1 : ℝ)) (eVec 1)‖ * ‖eVec 0‖) hdt one_pos hτ0
      (norm_nonneg _) (by positivity)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hΦ
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_iterate_le_of_perp_perp one_pos hτ0 hτ hdt hε (h ε hε) eVec_perp hXd
      (transportP2_lStep α) isUnit_one

theorem transportP2_lStep' (α : ℝ) :
    (transportP2 α (eCol 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (eCol 0)ᵀ))ᵀ * eCol 1 = 0 :=
  transportP2_lStep_aux α 1 0

/-- **`⟨∂ₓρ, Xⁿ⟩ ≠ 0` is not necessary for AP either.**  For the `P₂` transport at rank one with
`∂ₓρ = a = e₀`, `V = e₀` and `X = e₁ ⊥ ∂ₓρ`, the scheme is AP. So neither half of the "only if" of
Theorem I holds. -/
theorem ap_holds_with_X_perp_d (hdt : 0 < dt)
    (h : ∀ ε > 0, IsMicroMacroBUGStep (fun _ : Fin 2 => (1 : ℝ)) (transportP2 α) (eVec 0) (eVec 0)
      dt ε (eCol 1) 1 (eCol 0) (K₁' ε) (L₁' ε) (X₁' ε) (V₁' ε) (S₁' ε)) :
    (eCol 1)ᵀ * eVec 0 = 0 ∧ diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0) ≠ 0 ∧
      Tendsto (fun ε => ‖X₁' ε * S₁' ε * (V₁' ε)ᵀ -
        diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0)‖) (𝓝[>] 0) (𝓝 0) := by
  have hXd : (eCol 1)ᵀ * eVec 0 = 0 := by
    ext i j
    simp [Matrix.mul_apply, eCol, eVec]
  have hVa : eCol 0 * (eCol 0)ᵀ * eVec 0 = eVec 0 := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, eCol, eVec]
  have hb : (eCol 0)ᵀ * eVec 0 ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 0) ()
    simp [Matrix.mul_apply, eCol, eVec] at this
  refine ⟨hXd, ?_, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp [diffFlux, ceDir_one, Matrix.mul_apply, eVec] at this
  · have hτ0 : 0 ≤ ‖skewD‖ * ‖fluxP2 α‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hk : 0 ≤ kappa 1 1 := by rw [kappa_self one_pos]; exact zero_le_one
    have hΦ := (tendsto_apPhi (B := ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖)
      (F := kappa 1 1 * ‖ceDir (fun _ : Fin 2 => (1 : ℝ)) (eVec 0)‖ * ‖eVec 0‖) hdt one_pos hτ0
      (norm_nonneg _) (by positivity)).const_mul (1 + kappa 1 1 * ‖eVec 0‖ / ‖(eCol 0)ᵀ * eVec 0‖)
    rw [mul_zero] at hΦ
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hΦ
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_iterate_sub_le_of_X_perp one_pos hτ0 (norm_transportP2_le α) hdt hε (h ε hε) hXd
      (transportP2_lStep' α) isUnit_one hVa hb

/-- **`ε²/dt` is not the rate.**  Already for the full-rank `P₂` scheme from well-prepared data
`gⁿ = G`, for every `C` there is an `ε ∈ (0, 1)` and a step with `‖g₁ - G‖ > C ε²`, because the
explicit `1/ε` transport contributes `(dt/ε) / (1 + dt/ε²) ‖𝒯 G‖ ≈ ε ‖𝒯 G‖ / σ`, the first
Chapman–Enskog correction.  This is the bound of `sStep_ge`, and it refutes the per-step rate
`C ε² / (dt σ_min)`; the correct order is `ε` (`apPhi_le`). -/
theorem exists_rate_not_eps_sq (hdt : 0 < dt) (C : ℝ) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ (K₁ L₁ X₁ V₁ : Matrix (Fin 2) (Fin 2) ℝ)
      (S₁ : Matrix (Fin 2) (Fin 2) ℝ),
      IsMicroMacroBUGStep (fun _ : Fin 2 => (1 : ℝ)) (transportP2 1) (eVec 0) (eVec 0) dt ε
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0))
        (1 : Matrix (Fin 2) (Fin 2) ℝ) K₁ L₁ X₁ V₁ S₁ ∧
      C * ε ^ 2 < ‖X₁ * S₁ * V₁ᵀ - diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0)‖ := by
  set G := diffFlux (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0) with hG
  have hσ := isCrossSection_const (m := Fin 2) (one_pos (α := ℝ))
  have hGval : G = !![-1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hG, diffFlux, ceDir_one, Matrix.mul_apply, eVec]
  have hT : 0 < ‖transportP2 1 G‖ := by
    have h1 : transportP2 1 G = !![0, 0; 0, 1] := by
      rw [hGval, transportP2, skewD, fluxP2, Matrix.mul_fin_two, Matrix.mul_fin_two]
      norm_num
    rw [norm_pos_iff, h1]
    intro h0
    have := congrFun (congrFun h0 1) 1
    simp at this
  set T := ‖transportP2 1 G‖ with hTdef
  set W := |C| * (1 + dt) + 1 with hW
  have hW0 : 0 < W := by positivity
  set ε := min (1 / 2) (T * dt / (2 * W)) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp
  obtain ⟨K₁, L₁, X₁, V₁, S₁, hs⟩ := exists_step (k := 2) (by simp) (by simp) hσ hdt hε0
    (transportP2 1) (eVec 0) (eVec 0) G hone hone
  refine ⟨ε, ⟨hε0, hε1⟩, K₁, L₁, X₁, V₁, S₁, hs, ?_⟩
  have hX₁ : X₁ * X₁ᵀ = 1 := mul_transpose_eq_one_of_transpose_mul_eq_one hs.hX₁
  have hV₁ : V₁ * V₁ᵀ = 1 := mul_transpose_eq_one_of_transpose_mul_eq_one hs.hV₁
  have hy : X₁ * sLimit (fun _ : Fin 2 => (1 : ℝ)) (eVec 0) (eVec 0) X₁ V₁ * V₁ᵀ = G := by
    have h1 := norm_sLimit_sub_le (d := eVec 0) (a := eVec 0) (V₁ := V₁) hσ hs.hX₁
    rw [hX₁, hV₁, Matrix.one_mul, Matrix.one_mul, sub_self, sub_self] at h1
    simp only [norm_zero, zero_mul, mul_zero, add_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  have h1 := sStep_ge hσ hdt hε0 hs
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) * G * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = G := by simp
  have h3 : galerkinProj X₁ V₁ (transportP2 1 G) = transportP2 1 G := by
    rw [galerkinProj_apply, hX₁, hV₁, Matrix.one_mul, Matrix.mul_one]
  rw [h2, hX₁, hV₁, Matrix.one_mul, Matrix.mul_one, h3, hy, sub_self, norm_zero, sub_zero,
    ← hTdef, mul_one] at h1
  by_contra hcon
  push Not at hcon
  have hε2 : 0 < ε ^ 2 := by positivity
  have h4 : (1 + dt / ε ^ 2) * ‖X₁ * S₁ * V₁ᵀ - G‖ ≤ |C| * (1 + dt) := by
    have h5 : (1 + dt / ε ^ 2) * ‖X₁ * S₁ * V₁ᵀ - G‖ ≤ (1 + dt / ε ^ 2) * (C * ε ^ 2) :=
      mul_le_mul_of_nonneg_left hcon (by positivity)
    have h6 : (1 + dt / ε ^ 2) * (C * ε ^ 2) = C * (ε ^ 2 + dt) := by field_simp
    have h7 : ε ^ 2 ≤ 1 := by nlinarith
    rw [h6] at h5
    have h8 : C * (ε ^ 2 + dt) ≤ |C| * (ε ^ 2 + dt) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h9 : |C| * (ε ^ 2 + dt) ≤ |C| * (1 + dt) := by gcongr
    linarith
  have h10 : 2 * W ≤ dt / ε * T := by
    have h11 : ε ≤ T * dt / (2 * W) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h11
    rw [div_mul_eq_mul_div, le_div_iff₀ hε0]
    nlinarith
  linarith

end Instances

end MicroMacro

/-- The local Galerkin projector of this file, replaced by the core `LeanDLRA.galerkinProj` (same
definition `leftProj Y * rightProj W`). -/
@[deprecated (since := "2026-11-09")] alias galerkinProj := LeanDLRA.galerkinProj

/-- Replaced by the core `LeanDLRA.galerkinProj_apply`. -/
@[deprecated (since := "2026-11-09")] alias galerkinProj_apply := LeanDLRA.galerkinProj_apply

/-- Replaced by the core `LeanDLRA.isOrthProj_galerkinProj`. -/
@[deprecated (since := "2026-11-09")] alias isOrthProj_galerkinProj :=
  LeanDLRA.isOrthProj_galerkinProj

end LeanDLRA.Novel.KineticAP
