import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stochastic.MeanSquare

/-!
# Results of arXiv 1803.00499: error propagation of stochastic DLRA

This module formalizes **Theorem 3 (error propagation bound)** of Cao and Lu, arXiv 1803.00499
(Section 4.2), as an abstract statement in a real normed space `V`.  The paper's measure-valued
objects are replaced by `V`-valued trajectories, for a fixed test function `f(x) = xx†`:
`F t = 𝔼_{μ_t} f`, `FL t = 𝔼_{μ_LR,t} f`, `Gm t = 𝔼_{μ_t}[𝒜_t* f]`, `GLR t = 𝔼_{μ_LR,t}[𝒜_LR,t* f]`
and `Gl t = 𝔼_{μ_LR,t}[𝒜_t* f]`.  The error is `E(t) = ‖F t − FL t‖`, which is the Hilbert–Schmidt
error `‖𝔼_μ[xx†] − 𝔼_μLR[xx†]‖_HS` when `V` is the space of matrices.

What is proved (`error_bound_of_consistency`):
* the integral inequality `E(t) ≤ E(0) + ε² t + ∫₀ᵗ γ E`, derived from the two assumptions of
  Theorem 3 by the fundamental theorem of calculus and the triangle inequality, and
* the Grönwall step `E(t) ≤ (E(0) + ε² t) exp(∫₀ᵗ γ)`, which is `MeanSquare.integral_gronwall_le`
  applied after extending the trajectories constantly outside `[0, T]`.

Differences from the paper:
* The weak form of the Fokker–Planck/Lindblad equation, `d/dt 𝔼_{μ_t} f = 𝔼_{μ_t}[𝒜_t* f]`
  (and likewise for `μ_LR,t`), is taken as the hypothesis `hFd`, `hFLd`.  This is the definition of
  the adjoint generator used in the paper's proof, not a step of the argument.  Integrability
  (`hGm`, `hGLR`) and continuity on `[0, T]` are regularity hypotheses implicit in "differentiable
  trajectory".
* Theorem 3 assumes `γ` is a function.  Here it is required to be continuous and nonnegative on
  `[0, T]` (`hγ`, `hγ0`).  Nonnegativity is used by the Grönwall step and holds in the paper's
  application because assumption 2 bounds a norm by `γ(t) E(t)`.
* `ε²` enters as `ε ^ 2` in assumption 1 (`d_F ≤ ε²`), with `ε` any real number.  The horizon
  satisfies `0 ≤ T`.  The test function is fixed to `f(x) = xx†` (the paper's singleton `F`), so
  the supremum in `d_F` reduces to a norm.

Not formalized: Lemma 1 (adjoint generator of the SDE), Theorem 1 (optimal SDLR dynamics, first
order stationarity and the block decomposition), Lemma 2 and Theorem 2 (consistency at the
SDE level), Lemma 3 and Theorem 5 (unravelling commutes with DLRA), Theorem 4 (DLRA of the Lindblad
equation), and Example 1 (explicit `γ` for linear coefficients).  Those need a measure-theoretic
expectation layer or matrix calculus beyond this slice.

The module uses `Integrators/BUG`, `Matrix/Projectors` and `Stochastic/MeanSquare` from the core.
The Grönwall lemma `integral_gronwall_le` is the core definition reused here; the rest is local.
-/

open Set Filter Topology Finset MeasureTheory

namespace LeanDLRA.Literature.P1803_00499

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Error propagation for the low-rank second moments** (1803.00499 Theorem 3).

Let `F`, `FL` be the test-function expectations of the true and the low-rank measure, with
derivatives `Gm` (true generator) and `GLR` (low-rank generator).  Assume
1. `‖GLR s − Gl s‖ ≤ ε²` on `[0, T]`, where `Gl s` is the true generator applied to `μ_LR`
   (this is `d_F(𝒜_LR μ_LR, 𝒜 μ_LR) ≤ ε²`);
2. `‖Gm s − Gl s‖ ≤ γ(s) ‖F s − FL s‖` on `[0, T]` with `γ ≥ 0` continuous.

Then the error `E(t) = ‖F t − FL t‖` satisfies `E(t) ≤ (E(0) + ε² t) exp(∫₀ᵗ γ)` on `[0, T]`.
The integral inequality `E(t) ≤ E(0) + ε² t + ∫₀ᵗ γ E` is proved on the way. -/
theorem error_bound_of_consistency {F FL Gm GLR Gl : ℝ → V} {γ : ℝ → ℝ} {T ε : ℝ}
    (hT : 0 ≤ T)
    (hF : ContinuousOn F (Icc 0 T)) (hFL : ContinuousOn FL (Icc 0 T))
    (hFd : ∀ s ∈ Ioo 0 T, HasDerivAt F (Gm s) s)
    (hFLd : ∀ s ∈ Ioo 0 T, HasDerivAt FL (GLR s) s)
    (hGm : ∀ t ∈ Icc 0 T, IntervalIntegrable Gm MeasureTheory.volume 0 t)
    (hGLR : ∀ t ∈ Icc 0 T, IntervalIntegrable GLR MeasureTheory.volume 0 t)
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ0 : ∀ s ∈ Icc 0 T, 0 ≤ γ s)
    (h1 : ∀ s ∈ Icc 0 T, ‖GLR s - Gl s‖ ≤ ε ^ 2)
    (h2 : ∀ s ∈ Icc 0 T, ‖Gm s - Gl s‖ ≤ γ s * ‖F s - FL s‖) :
    ∀ t ∈ Icc 0 T, ‖F t - FL t‖ ≤
      (‖F 0 - FL 0‖ + ε ^ 2 * t) * Real.exp (∫ s in (0 : ℝ)..t, γ s) := by
  have hE : ContinuousOn (fun s => ‖F s - FL s‖) (Icc 0 T) := (hF.sub hFL).norm
  -- Step A: the integral inequality `E(t) ≤ E(0) + ε² t + ∫₀ᵗ γ E`.
  have hint : ∀ t ∈ Icc 0 T, ‖F t - FL t‖ ≤
      ‖F 0 - FL 0‖ + ε ^ 2 * t + ∫ s in (0 : ℝ)..t, γ s * ‖F s - FL s‖ := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have htT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hFint : ∫ s in (0 : ℝ)..t, Gm s = F t - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0 (hF.mono htT)
        (fun s hs => hFd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩) (hGm t ht)
    have hFLint : ∫ s in (0 : ℝ)..t, GLR s = FL t - FL 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0 (hFL.mono htT)
        (fun s hs => hFLd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩) (hGLR t ht)
    have hdiff : F t - FL t = (F 0 - FL 0) + ∫ s in (0 : ℝ)..t, (Gm s - GLR s) := by
      rw [intervalIntegral.integral_sub (hGm t ht) (hGLR t ht), hFint, hFLint]
      abel
    have hγE : IntervalIntegrable (fun s => γ s * ‖F s - FL s‖) MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht0]
      exact (hγ.mono htT).mul (hE.mono htT)
    have hcont : IntervalIntegrable (fun s => γ s * ‖F s - FL s‖ + ε ^ 2)
        MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht0]
      exact ((hγ.mono htT).mul (hE.mono htT)).add continuousOn_const
    have hnorm : ‖∫ s in (0 : ℝ)..t, (Gm s - GLR s)‖ ≤
        ∫ s in (0 : ℝ)..t, (γ s * ‖F s - FL s‖ + ε ^ 2) := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht0).trans ?_
      apply intervalIntegral.integral_mono_on ht0 ((hGm t ht).sub (hGLR t ht)).norm hcont
      intro s hs
      have hsI : s ∈ Icc 0 T := htT hs
      calc ‖Gm s - GLR s‖ = ‖(Gm s - Gl s) - (GLR s - Gl s)‖ := by congr 1; abel
        _ ≤ ‖Gm s - Gl s‖ + ‖GLR s - Gl s‖ := norm_sub_le _ _
        _ ≤ γ s * ‖F s - FL s‖ + ε ^ 2 := add_le_add (h2 s hsI) (h1 s hsI)
    have hsplit : ∫ s in (0 : ℝ)..t, (γ s * ‖F s - FL s‖ + ε ^ 2) =
        (∫ s in (0 : ℝ)..t, γ s * ‖F s - FL s‖) + ε ^ 2 * t := by
      rw [intervalIntegral.integral_add hγE intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hdiff]
    refine (norm_add_le _ _).trans ?_
    rw [hsplit] at hnorm
    linarith
  -- Step B: Grönwall, after extending the trajectories constantly outside `[0, T]`.
  set cl : ℝ → ℝ := fun s => max 0 (min s T) with hcl
  have hcl_mem : ∀ s, cl s ∈ Icc 0 T := fun s =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Icc 0 T, cl s = s := fun s hs => by
    simp only [hcl]
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hcont_cl : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hFc : Continuous (F ∘ cl) := hF.comp_continuous hcont_cl hcl_mem
  have hFLc : Continuous (FL ∘ cl) := hFL.comp_continuous hcont_cl hcl_mem
  have hgc : Continuous (fun s => γ (cl s)) := hγ.comp_continuous hcont_cl hcl_mem
  set e : ℝ → ℝ := fun s => ‖F (cl s) - FL (cl s)‖ with he
  set g : ℝ → ℝ := fun s => γ (cl s) with hg
  have he_cont : Continuous e := (hFc.sub hFLc).norm
  have he_t : ∀ t ∈ Icc 0 T, e t = ‖F t - FL t‖ := fun t ht => by
    simp only [he, hcl_id t ht]
  have he_0 : e 0 = ‖F 0 - FL 0‖ := by
    simp only [he, hcl_id 0 ⟨le_rfl, hT⟩]
  have hcongr : ∀ t ∈ Icc 0 T, ∫ s in (0 : ℝ)..t, g s * e s =
      ∫ s in (0 : ℝ)..t, γ s * ‖F s - FL s‖ := fun t ht => by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsI : s ∈ Icc 0 T := Icc_subset_Icc le_rfl ht.2 hs
    simp only [hg, he, hcl_id s hsI]
  have hcongrΓ : ∀ t ∈ Icc 0 T, ∫ s in (0 : ℝ)..t, g s = ∫ s in (0 : ℝ)..t, γ s := fun t ht => by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsI : s ∈ Icc 0 T := Icc_subset_Icc le_rfl ht.2 hs
    simp only [hg, hcl_id s hsI]
  have hint' : ∀ t ∈ Icc 0 T, e t ≤ e 0 + ε ^ 2 * t + ∫ s in (0 : ℝ)..t, g s * e s := by
    intro t ht
    rw [hcongr t ht, he_t t ht, he_0]
    exact hint t ht
  have key := LeanDLRA.MeanSquare.integral_gronwall_le he_cont hgc
    (fun s => hγ0 _ (hcl_mem s)) (sq_nonneg ε) hint'
  intro t ht
  have h := key t ht
  rw [hcongrΓ t ht, he_t t ht, he_0] at h
  exact h

/-- Non-vacuity of `error_bound_of_consistency`: on `[0, 1]` the trajectories `F t = t` and
`FL = 0` have true generator `Gm = Gl = 1`, low-rank generator `GLR = 0`, and `ε = 1`, `γ = 0`.
All hypotheses hold, and the conclusion is `E(t) = t ≤ t`. -/
theorem error_bound_nonvacuous :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖(fun s : ℝ => s) t - (fun _ : ℝ => (0 : ℝ)) t‖ ≤
      (‖(fun s : ℝ => s) 0 - (fun _ : ℝ => (0 : ℝ)) 0‖ + (1 : ℝ) ^ 2 * t) *
        Real.exp (∫ _ in (0 : ℝ)..t, (0 : ℝ)) :=
  error_bound_of_consistency (V := ℝ) (F := fun s => s) (FL := fun _ => 0)
    (Gm := fun _ => 1) (GLR := fun _ => 0) (Gl := fun _ => 1) (γ := fun _ => 0)
    (T := 1) (ε := 1) zero_le_one continuousOn_id continuousOn_const
    (fun s _ => hasDerivAt_id' s) (fun s _ => hasDerivAt_const s 0)
    (fun t _ => intervalIntegrable_const) (fun t _ => intervalIntegrable_const)
    continuousOn_const (fun _ _ => le_rfl)
    (fun s _ => by norm_num) (fun s _ => by norm_num)

end LeanDLRA.Literature.P1803_00499
