import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Stability.Energy

/-!
# arXiv 2111.07160: a collision source method for rank-adaptive DLRA in radiation therapy

Kusch–Stammer, *A robust collision source method for rank adaptive dynamical low-rank
approximation in radiation therapy*.  This module proves the exactness of the projector-splitting
integrator for right-multiplicative fields claimed in Sec. 3.2 (`ksl_rightMul_exact`, matrix form
`ksl_rightMul_exact_matrix`: the S-step undoes the K-step and one step returns `Y₀ e^{hG}` for
`Ẏ = Y G`), the exactness of the collided/uncollided multilevel splitting of Secs. 4.1–4.2
(`collidedSplit_odeSolution`, `collidedSplit_eq`), and Theorems 1–4 for the discretization of
Sec. 2.4 (finite-volume `P_N` with Roe matrices `|A| = V |Λ| Vᵀ` and density `ρ`, explicit Euler
streaming (34c), implicit scattering (36c), collided-flux steps (37c), (37d)) in the case of
**spatially constant density**: `theorem1` (fixed-rank BUG streaming step), `theorem3`
(rank-adaptive streaming step with truncated SVD), `theorem2` and `theorem4` (one step of the
full multilevel scheme, fixed rank and rank adaptive).  For spatially varying density, as the
paper states them, Theorems 1 and 2 are false: `theorem1_false_of_variable_density` and
`theorem2_false_of_variable_density`.

Differences from the paper.
* Sign of the flux.  Sec. 2.4 prints `u̇ = F(u) + G` with `L^{(1)}` having diagonal
  `+1/(ρ Δx)` and off-diagonal `-1/(2ρΔx)`; with this sign the scheme is anti-diffusive.  The
  proof of Theorem 1 uses `D^{(1)} = (e^{iθ} - 2 + e^{-iθ})/(2Δx) = (cos θ - 1)/Δx`, the symbol
  of `-T^{(1)}`.  We use `u̇ = -F(u)` (`PNScheme.euler`), the upwind (Roe) discretization of
  `∂_t u = -A·∇(u/ρ)`; the sign of the `T^{(2)}` term only fixes the transport direction and does
  not affect any estimate.
* Grid and CFL.  Neighbours are given by arbitrary permutations of the cells (the Fourier proof
  needs a periodic grid); the CFL condition is imposed per direction with `Δx`, `Δy`, reading
  `λ_max` as `max_k |λ_k|`.
* Proof.  No Fourier analysis: under the CFL condition `1/2` the one-direction step with doubled
  time step is, in the eigenbasis of `A`, a convex combination of shifted grid functions
  (`dir_step_norm_le`), and the full step is the mean of the two directions.
* Bases and truncation.  The bounds hold for any new bases with orthonormal columns (capture of
  `K(t₁)` and augmentation are what make the formulas the BUG steps, but are not needed for the
  estimates), and for the truncated SVD `EckartYoung.truncation` of any rank.
* Uncollided flux.  The paper computes `ψ` with an `S_N` solver and uses
  `‖ψ(t₁)‖ = ‖ψ(t₀)‖/(1 + Δt Σ_t)`; we take `ψ` in moment form (`ψ T_M`) and assume
  `(1 + Δt Σ_t) ‖ψ(t₁)‖ ≤ ‖ψ(t₀)‖`, which `uncollided_norm_le` proves for explicit `P_N`
  streaming with implicit absorption.
* Scattering.  `Σ = diag(Σ_kk)` with `|Σ_kk| ≤ Σ_t`; the scattering CFL condition (41) is derived
  (`scattering_cfl`, Remark 2).  Instead of the paper's factor
  `max_k Σ_kk/(1 + Δt Σ_t - Δt Σ_kk)` for `‖Σ‖ ‖(I + Σ_t Δt I - Δt Σ)⁻¹‖` we use the separate
  bounds `Σ_t` and `1` (equal to it when `Σ_11 = Σ_t`), which give the same recursion
  (`level_telescope`).
* Sec. 3.2 is stated for exactly solved substeps with `G` constant over the step (for
  time-dependent `G` the K- and S-flows need not cancel; this remark is not proved here).
* False claim.  Theorem 1 with variable density: on the periodic `2 × 1` grid with `ρ = (2, 4)`,
  `A_x = A_y = [[0, 1], [1, 0]]` and `Δt = Δx = Δy = 1` (CFL number exactly `1/2`) the full-rank
  BUG step maps `u⁰ = [[1, 0], [1, 0]]` to a matrix of norm `√(17/8) > √2`.  (On this grid both
  `x`-neighbours of a cell are the other cell and the `y`-neighbour is the cell itself; the
  stencils are applied in operator form, contributions added, as in `T1`, `T2`, so the
  `y`-stencils vanish.  The scheme is the one with the sign of the paper's proof, see above.)
  The proof bounds `‖½ I + Δt M ρ̃⁻¹‖` by `|½ + Δt λ_max(M) λ_max(ρ̃⁻¹)|` with the non-diagonal
  `ρ̃⁻¹ = Eᴴ ρ⁻¹ E`, which is not valid unless `ρ̃⁻¹` is a multiple of the identity, i.e. the
  density is constant.  The same data refute Theorem 2.  Theorems 3 and 4 rest on the same
  estimate; only their constant-density versions are proved here.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2111_07160

/-- The matrix exponential `e^G` (Mathlib's `NormedSpace.exp`, entrywise topology; defined before
the Frobenius norm is opened). -/
noncomputable def mexp {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ) :
    Matrix n n ℝ :=
  NormedSpace.exp G

/-! ### Sec. 3.2: the projector-splitting integrator for right-multiplicative fields -/

section RightMultiplicative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A continuous linear map is a Lipschitz (autonomous) vector field with constant `‖M‖`. -/
lemma isLipschitzField_clm (M : E →L[ℝ] E) : IsLipschitzField (fun _ x => M x) ‖M‖ :=
  fun _ x y => by rw [← map_sub]; exact M.le_opNorm _

/-- `t ↦ exp((t - c) M) y₀` solves the linear ODE `y' = M y`. -/
lemma odeSolution_exp (M : E →L[ℝ] E) (c a b : ℝ) (y₀ : E) :
    ODESolution (fun _ x => M x) (fun t => NormedSpace.exp ((t - c) • M) y₀) a b := by
  have hd : ∀ t, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - c) • M) y₀)
      (M (NormedSpace.exp ((t - c) • M) y₀)) t := by
    intro t
    have h := ((hasDerivAt_exp_smul_const' M (t - c)).comp_sub_const t c).clm_apply
      (hasDerivAt_const t y₀)
    convert h using 1
    simp
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- **Sec. 3.2 of arXiv 2111.07160 (citing its ref. [30]): for a right-multiplicative field the
K- and S-steps of the projector-splitting integrator cancel and the integrator is exact.**
Abstract form: `F(t, Y) = 𝓡 Y` with a fixed continuous linear map `𝓡` (for matrices
`𝓡 Y = Y G`, `G` constant over the step) that commutes with the new left projector `P₁`
(left and right multiplications commute), and `P₁` commutes with the old right projector `Q₀`.
For one exact KSL step `IsKSLStep` (K-step, backward S-step, L-step, each solved exactly, and
`P₁` capturing `K(t₁)`) started at `Y₀`:

* the S-step undoes the K-step: `YS t₁ = Y₀`;
* the result is the exact solution: `YL t₁ = A t₁` for the solution `A' = 𝓡 A`, `A t₀ = Y₀`.

No rank or normal-component assumption is used (the bound `ε` of `IsKSLStep` plays no role).
Proof: the K- and S-flows are `e^{±(t-t₀) Q₀𝓡}` (the S-step stays in `range P₁`, where
`P₁ Q₀ 𝓡 = Q₀ 𝓡`), so `YS t₁ = Y₀`; hence `P₁ Y₀ = Y₀`, the exact solution stays in `range P₁`
and solves the L-step equation `Y' = P₁ 𝓡 Y`. -/
theorem ksl_rightMul_exact {F : ℝ → E → E} {𝓡 P₁ Q₀ : E →L[ℝ] E} {ε t₀ t₁ : ℝ} {Y₀ : E}
    {YK YS YL A : ℝ → E} (hF : ∀ t x, F t x = 𝓡 x)
    (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁)
    (hR : ∀ x, P₁ (𝓡 x) = 𝓡 (P₁ x)) (hPQ : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x))
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    YS t₁ = Y₀ ∧ YL t₁ = A t₁ := by
  obtain rfl : F = fun _ x => 𝓡 x := funext fun t => funext fun x => hF t x
  set M : E →L[ℝ] E := Q₀.comp 𝓡 with hM
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨h01, le_rfl⟩
  have hK : ∀ t ∈ Icc t₀ t₁, YK t = NormedSpace.exp ((t - t₀) • M) Y₀ := by
    have h1 : ODESolution (fun _ x => M x) YK t₀ t₁ := hs.kSol
    exact fun t ht => h1.eqOn (odeSolution_exp M t₀ t₀ t₁ Y₀) (isLipschitzField_clm M)
      (norm_nonneg _) (by simp [hs.kStart]) ht
  have hSP := ksl_S_mem_range hs.projP₁ hs.sSol hs.sStart hs.kCap
  have hS : ODESolution (fun _ x => (-M) x) YS t₀ t₁ := by
    refine ⟨hs.sSol.cont, fun t ht => ?_⟩
    have h := hs.sSol.deriv t ht
    have hP : P₁ (YS t) = YS t := hSP t (Ico_subset_Icc_self ht)
    have e : -P₁ (Q₀ (𝓡 (YS t))) = (-M) (YS t) := by
      rw [hPQ, hR, hP]; simp [hM]
    simpa only [e] using h
  have hsm : (t₀ - t₁) • (-M) = (t₁ - t₀) • M := by rw [smul_neg, ← neg_smul, neg_sub]
  have hSZ : ∀ t ∈ Icc t₀ t₁, YS t = NormedSpace.exp ((t - t₁) • (-M)) Y₀ := fun t ht =>
    hS.eqOn (odeSolution_exp (-M) t₁ t₀ t₁ Y₀) (isLipschitzField_clm (-M)) (norm_nonneg _)
      (by rw [hs.sStart, hK t₁ ht₁, hsm]) ht
  have hS₁ : YS t₁ = Y₀ := by rw [hSZ t₁ ht₁]; simp
  have hY₀P : P₁ Y₀ = Y₀ := by rw [← hS₁]; exact hSP t₁ ht₁
  have hAP : ∀ t ∈ Icc t₀ t₁, P₁ (A t) = A t := by
    have hB : ODESolution (fun _ x => 𝓡 x) (fun t => P₁ (A t)) t₀ t₁ := by
      refine ⟨P₁.continuous.comp_continuousOn hA.cont, fun t ht => ?_⟩
      have h := P₁.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht)
      simpa [Function.comp_def, hR] using h
    exact fun t ht => hB.eqOn hA (isLipschitzField_clm 𝓡) (norm_nonneg _)
      (by rw [hA₀, hY₀P]) ht
  have hAL : ODESolution (fun _ x => P₁ (𝓡 x)) A t₀ t₁ := by
    refine ⟨hA.cont, fun t ht => ?_⟩
    have h : HasDerivWithinAt A (𝓡 (A t)) (Ici t) t := hA.deriv t ht
    have e : 𝓡 (A t) = P₁ (𝓡 (A t)) := by rw [hR, hAP t (Ico_subset_Icc_self ht)]
    rwa [e] at h
  have hLA : EqOn YL A (Icc t₀ t₁) :=
    hs.lSol.eqOn hAL (isLipschitzField_clm (P₁.comp 𝓡)) (norm_nonneg _)
      (by rw [hs.lStart, hS₁, hA₀])
  exact ⟨hS₁, hLA ht₁⟩

end RightMultiplicative

section RightMultiplicativeMatrix

open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Derivative of `s ↦ e^{sG}` (auxiliary for Sec. 3.2 of arXiv 2111.07160). -/
lemma hasDerivAt_mexp (G : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mexp (s • G)) (mexp (t • G) * G) t := by
  let _ := Matrix.frobeniusNormedRing (m := n) (α := ℝ)
  let _ := Matrix.frobeniusNormedAlgebra (m := n) (α := ℝ) (R := ℝ)
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) G t

/-- `e^0 = 1` (auxiliary for Sec. 3.2 of arXiv 2111.07160). -/
lemma mexp_zero : mexp (0 : Matrix n n ℝ) = 1 := by
  simp [mexp]

omit [DecidableEq m] in
/-- `t ↦ Y₀ e^{(t - t₀) G}` solves `Y' = Y G`. -/
lemma odeSolution_mul_mexp (G : Matrix n n ℝ) (Y₀ : Matrix m n ℝ) (t₀ a b : ℝ) :
    ODESolution (fun _ Y => Y * G) (fun t => Y₀ * mexp ((t - t₀) • G)) a b := by
  have hd : ∀ t, HasDerivAt (fun t : ℝ => Y₀ * mexp ((t - t₀) • G))
      (Y₀ * mexp ((t - t₀) • G) * G) t := by
    intro t
    have h := Frobenius.hasDerivAt_const_mul Y₀ ((hasDerivAt_mexp G (t - t₀)).comp_sub_const t t₀)
    simpa [Matrix.mul_assoc] using h
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

omit [DecidableEq m] in
/-- **Sec. 3.2 of arXiv 2111.07160, matrix form: the projector-splitting integrator is exact for
`Ẏ = Y G`.**  For the field `F(t, Y) = Y G` with `G` constant over the step, one exact KSL step
(`IsKSLStep`: the new left projector `U₁ U₁ᵀ` is orthogonal and captures `K(t₁)`) with old right
basis `V₀` has S-step value `Y₀` and returns the exact solution `Y₁ = Y₀ e^{h G}`,
`h = t₁ - t₀`.  This justifies
computing only the L-step `L̇_c = -Σ_t L_c + L_c Σ` for the collided flux (eq. (33)). -/
theorem ksl_rightMul_exact_matrix {k k' : Type*} [Fintype k] [Fintype k']
    {G : Matrix n n ℝ} {U₁ : Matrix m k ℝ} {V₀ : Matrix n k' ℝ}
    {ε t₀ t₁ : ℝ} {Y₀ : Matrix m n ℝ} {YK YS YL : ℝ → Matrix m n ℝ}
    (hs : IsKSLStep (fun _ Y => Y * G) ε (leftProj U₁) (rightProj V₀) t₀ t₁ Y₀ YK YS YL)
    (h01 : t₀ ≤ t₁) :
    YS t₁ = Y₀ ∧ YL t₁ = Y₀ * mexp ((t₁ - t₀) • G) := by
  have h := ksl_rightMul_exact (𝓡 := Frobenius.rightMulCLM G) (fun _ _ => rfl) hs h01
    (fun x => by simp [Matrix.mul_assoc]) (leftProj_rightProj_comm U₁ V₀)
    (odeSolution_mul_mexp G Y₀ t₀ t₀ t₁) (by simp [mexp_zero])
  exact h

end RightMultiplicativeMatrix

/-! ### Secs. 4.1–4.2: the collided/uncollided multilevel splitting -/

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Secs. 4.1–4.2 of arXiv 2111.07160, eqs. (24a)–(24c) / (31a)–(31c): the collided/uncollided
splitting is exact.**  Let `𝒯 t` be the streaming-and-absorption operator
(`-Ω·∇(·/ρ) - Σ_t`) and `𝒮 t` the in-scattering operator, both linear.  If the uncollided flux
`ψ 0` solves `ψ₀' = 𝒯 ψ₀`, each collided level `ψ (ℓ+1)`, `ℓ < L`, solves
`ψ_{ℓ+1}' = 𝒯 ψ_{ℓ+1} + 𝒮 ψ_ℓ` (the previous level enters as a source), and the collided flux
`ψc` solves `ψc' = 𝒯 ψc + 𝒮 (ψ_L + ψc)`, then `ψ = ψ₀ + ⋯ + ψ_L + ψc` solves the full equation
`ψ' = 𝒯 ψ + 𝒮 ψ`.  Abstract statement on a normed space; time-dependent operators are allowed. -/
theorem collidedSplit_odeSolution {𝒯 𝒮 : ℝ → E →L[ℝ] E} {L : ℕ} {ψ : ℕ → ℝ → E}
    {ψc : ℝ → E} {a b : ℝ}
    (h0 : ODESolution (fun t x => 𝒯 t x) (ψ 0) a b)
    (hℓ : ∀ ℓ < L, ODESolution (fun t x => 𝒯 t x + 𝒮 t (ψ ℓ t)) (ψ (ℓ + 1)) a b)
    (hc : ODESolution (fun t x => 𝒯 t x + 𝒮 t (ψ L t + x)) ψc a b) :
    ODESolution (fun t x => 𝒯 t x + 𝒮 t x)
      (fun t => ∑ ℓ ∈ range (L + 1), ψ ℓ t + ψc t) a b := by
  constructor
  · refine ContinuousOn.add ?_ hc.cont
    refine continuousOn_finsetSum _ fun ℓ hℓ' => ?_
    rcases ℓ with _ | ℓ
    · exact h0.cont
    · exact (hℓ ℓ (by simp at hℓ'; omega)).cont
  · intro t ht
    have hd : ∀ ℓ ∈ range (L + 1), HasDerivWithinAt (ψ ℓ)
        (𝒯 t (ψ ℓ t) + if ℓ = 0 then 0 else 𝒮 t (ψ (ℓ - 1) t)) (Ici t) t := by
      intro ℓ hℓ'
      rcases ℓ with _ | ℓ
      · simpa using h0.deriv t ht
      · simpa using (hℓ ℓ (by simp at hℓ'; omega)).deriv t ht
    have hsum := (HasDerivWithinAt.fun_sum hd).add (hc.deriv t ht)
    have e1 : ∑ ℓ ∈ range (L + 1), (if ℓ = 0 then (0 : E) else 𝒮 t (ψ (ℓ - 1) t)) =
        ∑ ℓ ∈ range L, 𝒮 t (ψ ℓ t) := by
      rw [Finset.sum_range_succ']; simp
    convert hsum using 1
    rw [Finset.sum_add_distrib, e1]
    simp only [map_add, map_sum, Finset.sum_range_succ]
    abel

/-- **Secs. 4.1–4.2 of arXiv 2111.07160: the levels add up to the full solution.**  With the
initial data of the method (`ψ₀(t₀) = ψ(t₀)`, all collided components zero at `t₀`) and uniformly
bounded operators, the sum of the components equals the solution of the full equation. -/
theorem collidedSplit_eq {𝒯 𝒮 : ℝ → E →L[ℝ] E} {L : ℕ} {ψ : ℕ → ℝ → E}
    {ψc Ψ : ℝ → E} {a b K₁ K₂ : ℝ} (hK₁ : ∀ t, ‖𝒯 t‖ ≤ K₁) (hK₂ : ∀ t, ‖𝒮 t‖ ≤ K₂)
    (h0 : ODESolution (fun t x => 𝒯 t x) (ψ 0) a b)
    (hℓ : ∀ ℓ < L, ODESolution (fun t x => 𝒯 t x + 𝒮 t (ψ ℓ t)) (ψ (ℓ + 1)) a b)
    (hc : ODESolution (fun t x => 𝒯 t x + 𝒮 t (ψ L t + x)) ψc a b)
    (hΨ : ODESolution (fun t x => 𝒯 t x + 𝒮 t x) Ψ a b)
    (hi0 : ψ 0 a = Ψ a) (hiℓ : ∀ ℓ < L, ψ (ℓ + 1) a = 0) (hic : ψc a = 0) :
    ∀ t ∈ Icc a b, ∑ ℓ ∈ range (L + 1), ψ ℓ t + ψc t = Ψ t := by
  have hsol := collidedSplit_odeSolution h0 hℓ hc
  have hK : 0 ≤ K₁ + K₂ := by
    have := hK₁ 0; have := hK₂ 0
    linarith [norm_nonneg (𝒯 0), norm_nonneg (𝒮 0)]
  have hlip : IsLipschitzField (fun t x => 𝒯 t x + 𝒮 t x) (K₁ + K₂) := by
    intro t x y
    have e : 𝒯 t x + 𝒮 t x - (𝒯 t y + 𝒮 t y) = 𝒯 t (x - y) + 𝒮 t (x - y) := by
      simp only [map_sub]; abel
    rw [e, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact ((𝒯 t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK₁ t) (norm_nonneg _))
    · exact ((𝒮 t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK₂ t) (norm_nonneg _))
  refine fun t ht => hsol.eqOn hΨ hlip hK ?_ ht
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun ℓ hℓ' => hiℓ ℓ (Finset.mem_range.1 hℓ'),
    hic, hi0]
  simp

end Splitting


/-! ### Sec. 2.4: the finite-volume `P_N` streaming discretization -/

section Streaming

open scoped LeanDLRA.Frobenius

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The shift (permutation) matrix `(Π_σ v)_i = v_{σ i}`.  On a periodic grid with
`σ (i, j) = (i + 1, j)` it picks the right neighbour. -/
def shiftMat (σ : Equiv.Perm ι) : Matrix ι ι ℝ := σ.toPEquiv.toMatrix

omit [Fintype κ] [DecidableEq κ] in
/-- Entries of `Π_σ M`: `(Π_σ M)_{ik} = M_{σ i, k}` (auxiliary, Sec. 2.4 of arXiv 2111.07160). -/
lemma shiftMat_mul_apply (σ : Equiv.Perm ι) (M : Matrix ι κ ℝ) (i : ι) (k : κ) :
    (shiftMat σ * M) i k = M (σ i) k := by
  simp only [shiftMat, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id]

/-- `T^{(2)}` of Sec. 2.4: entries `±1/(2Δ)` at the neighbours `σ^{±1} i` (central difference
`(v_{i+1} - v_{i-1}) / (2Δ)`). -/
noncomputable def T2 (σ : Equiv.Perm ι) (Δ : ℝ) : Matrix ι ι ℝ :=
  (1 / (2 * Δ)) • (shiftMat σ - shiftMat σ⁻¹)

/-- `T^{(1)}` of Sec. 2.4: diagonal `1/Δ` and `-1/(2Δ)` at the neighbours `σ^{±1} i`
(`(2 v_i - v_{i+1} - v_{i-1}) / (2Δ)`, the numerical diffusion of the Roe flux). -/
noncomputable def T1 (σ : Equiv.Perm ι) (Δ : ℝ) : Matrix ι ι ℝ :=
  (1 / (2 * Δ)) • ((2 : ℝ) • (1 : Matrix ι ι ℝ) - shiftMat σ - shiftMat σ⁻¹)

omit [Fintype κ] [DecidableEq κ] in
/-- Entries of `T^{(2)} M` (auxiliary, Sec. 2.4 of arXiv 2111.07160). -/
lemma T2_mul_apply (σ : Equiv.Perm ι) (Δ : ℝ) (M : Matrix ι κ ℝ) (i : ι) (k : κ) :
    (T2 σ Δ * M) i k = (M (σ i) k - M (σ⁻¹ i) k) / (2 * Δ) := by
  simp only [T2, Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply,
    shiftMat_mul_apply, smul_eq_mul]
  ring

omit [Fintype κ] [DecidableEq κ] in
/-- Entries of `T^{(1)} M` (auxiliary, Sec. 2.4 of arXiv 2111.07160). -/
lemma T1_mul_apply (σ : Equiv.Perm ι) (Δ : ℝ) (M : Matrix ι κ ℝ) (i : ι) (k : κ) :
    (T1 σ Δ * M) i k = (2 * M i k - M (σ i) k - M (σ⁻¹ i) k) / (2 * Δ) := by
  simp only [T1, Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply,
    shiftMat_mul_apply, smul_eq_mul, Matrix.one_mul]
  ring

/-- The data of the finite-volume `P_N` streaming discretization of Sec. 2.4: cells `ι`,
moments `κ`, the neighbour maps in `x` and `y` (on the periodic `N_x × N_y` grid of the von
Neumann analysis, `(i, j) ↦ (i + 1, j)` and `(i, j) ↦ (i, j + 1)`; any permutations are
allowed), mesh sizes, cell densities `ρ_ij`, and the orthonormal eigenvectors and eigenvalues
of the symmetric flux matrices, `A_x = V_x Λ_x V_xᵀ`, `A_y = V_y Λ_y V_yᵀ`. -/
structure PNScheme (ι κ : Type*) where
  σx : Equiv.Perm ι
  σy : Equiv.Perm ι
  Δx : ℝ
  Δy : ℝ
  ρ : ι → ℝ
  Vx : Matrix κ κ ℝ
  lx : κ → ℝ
  Vy : Matrix κ κ ℝ
  ly : κ → ℝ

namespace PNScheme

variable (S : PNScheme ι κ)

/-- `A_x = V_x Λ_x V_xᵀ`. -/
noncomputable def Ax : Matrix κ κ ℝ := S.Vx * Matrix.diagonal S.lx * S.Vxᵀ
/-- `A_y = V_y Λ_y V_yᵀ`. -/
noncomputable def Ay : Matrix κ κ ℝ := S.Vy * Matrix.diagonal S.ly * S.Vyᵀ
/-- The Roe matrix `|A_x| = V_x |Λ_x| V_xᵀ`. -/
noncomputable def absAx : Matrix κ κ ℝ := S.Vx * Matrix.diagonal (fun k => |S.lx k|) * S.Vxᵀ
/-- The Roe matrix `|A_y| = V_y |Λ_y| V_yᵀ`. -/
noncomputable def absAy : Matrix κ κ ℝ := S.Vy * Matrix.diagonal (fun k => |S.ly k|) * S.Vyᵀ

/-- `ρ⁻¹ = diag(ρ_ij)⁻¹`. -/
noncomputable def rhoInv : Matrix ι ι ℝ := Matrix.diagonal fun i => (S.ρ i)⁻¹

/-- `L^{(2)}_x = T^{(2)}_x ρ⁻¹`. -/
noncomputable def L2x : Matrix ι ι ℝ := T2 S.σx S.Δx * S.rhoInv
/-- `L^{(2)}_y = T^{(2)}_y ρ⁻¹`. -/
noncomputable def L2y : Matrix ι ι ℝ := T2 S.σy S.Δy * S.rhoInv
/-- `L^{(1)}_x = T^{(1)}_x ρ⁻¹`. -/
noncomputable def L1x : Matrix ι ι ℝ := T1 S.σx S.Δx * S.rhoInv
/-- `L^{(1)}_y = T^{(1)}_y ρ⁻¹`. -/
noncomputable def L1y : Matrix ι ι ℝ := T1 S.σy S.Δy * S.rhoInv

/-- The flux `F(u) = L^{(2)}_x u A_xᵀ + L^{(2)}_y u A_yᵀ + L^{(1)}_x u |A_x|ᵀ + L^{(1)}_y u |A_y|ᵀ`
of Sec. 2.4. -/
noncomputable def flux (u : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  S.L2x * u * S.Axᵀ + S.L2y * u * S.Ayᵀ + S.L1x * u * S.absAxᵀ + S.L1y * u * S.absAyᵀ

/-- The full explicit Euler streaming step `u ↦ u - Δt F(u)` (upwind/Roe scheme for
`∂_t u = -A·∇(u/ρ)`; see the module docstring for the sign). -/
noncomputable def euler (Δt : ℝ) (u : Matrix ι κ ℝ) : Matrix ι κ ℝ := u - Δt • S.flux u

/-- The hypotheses of Theorem 1 of arXiv 2111.07160 in the case of a **spatially constant
density** `ρ ≡ ρ₀`: positive mesh sizes, `Δt ≥ 0`, orthogonal eigenvector matrices, and the CFL
condition `|λ_k| Δt / (ρ₀ Δ) ≤ 1/2` in both directions. -/
structure CFL (ρ₀ Δt : ℝ) : Prop where
  rho_eq : ∀ i, S.ρ i = ρ₀
  rho_pos : 0 < ρ₀
  Δx_pos : 0 < S.Δx
  Δy_pos : 0 < S.Δy
  Δt_nonneg : 0 ≤ Δt
  Vx_orth : S.Vxᵀ * S.Vx = 1
  Vy_orth : S.Vyᵀ * S.Vy = 1
  cflx : ∀ k, |S.lx k| * Δt / (ρ₀ * S.Δx) ≤ 1 / 2
  cfly : ∀ k, |S.ly k| * Δt / (ρ₀ * S.Δy) ≤ 1 / 2

end PNScheme

omit [DecidableEq ι] in
/-- Right multiplication by a square orthogonal matrix is an isometry. -/
lemma norm_mul_orth {V : Matrix κ κ ℝ} (hV : Vᵀ * V = 1) (X : Matrix ι κ ℝ) :
    ‖X * V‖ = ‖X‖ := by
  have h : V * Vᵀ = 1 := mul_eq_one_comm.1 hV
  have h' : Vᵀᵀ * Vᵀ = 1 := by rw [Matrix.transpose_transpose]; exact h
  have := Frobenius.norm_mul_transpose_of_orthonormal h' X
  rwa [Matrix.transpose_transpose] at this

/-- Jensen for three weights: `(a x + b y + c z)² ≤ a x² + b y² + c z²` when `a, b, c ≥ 0` and
`a + b + c = 1`. -/
lemma sq_convex3_le {a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    (a * x + b * y + c * z) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  have hc' : c = 1 - a - b := by linarith
  subst hc'
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y)),
    mul_nonneg (mul_nonneg ha hc) (sq_nonneg (x - z)),
    mul_nonneg (mul_nonneg hb hc) (sq_nonneg (y - z))]

/-- **One-direction step with doubled time step is a contraction** (the core of the proof of
Theorem 1 of arXiv 2111.07160).  For constant density `ρ₀`, `A = V Λ Vᵀ` with `V` orthogonal and
`|λ_k| Δt/(ρ₀ Δ) ≤ 1/2`, the step `u ↦ u - 2Δt (T^{(2)} ρ⁻¹ u Aᵀ + T^{(1)} ρ⁻¹ u |A|ᵀ)` does not
increase the Frobenius norm.  (In the eigenbasis of `A` it is, column by column, the convex
combination `(1 - 2μ|λ|) w_i + μ(|λ| - λ) w_{i+1} + μ(|λ| + λ) w_{i-1}`, `μ = Δt/(ρ₀Δ)`.) -/
lemma dir_step_norm_le (σ : Equiv.Perm ι) {Δ Δt ρ₀ : ℝ} {ρ : ι → ℝ} (hρ : ∀ i, ρ i = ρ₀)
    (hρ₀ : 0 < ρ₀) (hΔ : 0 < Δ) (hΔt : 0 ≤ Δt) {V : Matrix κ κ ℝ} (hV : Vᵀ * V = 1)
    {l : κ → ℝ} (hcfl : ∀ k, |l k| * Δt / (ρ₀ * Δ) ≤ 1 / 2) (u : Matrix ι κ ℝ) :
    ‖u - (2 * Δt) • (T2 σ Δ * Matrix.diagonal (fun i => (ρ i)⁻¹) * u *
        (V * Matrix.diagonal l * Vᵀ)ᵀ +
      T1 σ Δ * Matrix.diagonal (fun i => (ρ i)⁻¹) * u *
        (V * Matrix.diagonal (fun k => |l k|) * Vᵀ)ᵀ)‖ ≤ ‖u‖ := by
  set D : Matrix ι ι ℝ := Matrix.diagonal (fun i => (ρ i)⁻¹) with hD
  set Z := u - (2 * Δt) • (T2 σ Δ * D * u * (V * Matrix.diagonal l * Vᵀ)ᵀ +
      T1 σ Δ * D * u * (V * Matrix.diagonal (fun k => |l k|) * Vᵀ)ᵀ) with hZ
  set W := u * V with hW
  have hVV : Vᵀ * V = 1 := hV
  -- `Aᵀ V = V Λ`
  have hAV : ∀ d : κ → ℝ, (V * Matrix.diagonal d * Vᵀ)ᵀ * V = V * Matrix.diagonal d := by
    intro d
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hZV : Z * V = W - (2 * Δt) • (T2 σ Δ * D * W * Matrix.diagonal l +
      T1 σ Δ * D * W * Matrix.diagonal (fun k => |l k|)) := by
    rw [hZ, Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_assoc _ _ V,
      Matrix.mul_assoc _ (V * Matrix.diagonal (fun k => |l k|) * Vᵀ)ᵀ V, hAV, hAV, hW]
    simp only [Matrix.mul_assoc]
  set μ : ℝ := Δt / (ρ₀ * Δ) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg hΔt (mul_pos hρ₀ hΔ).le
  set a0 : κ → ℝ := fun k => 1 - 2 * μ * |l k|
  set ap : κ → ℝ := fun k => μ * (|l k| - l k)
  set am : κ → ℝ := fun k => μ * (|l k| + l k)
  have ha0 : ∀ k, 0 ≤ a0 k := by
    intro k
    have h := hcfl k
    have : |l k| * Δt / (ρ₀ * Δ) = μ * |l k| := by rw [hμ]; ring
    simp only [a0]; linarith
  have hap : ∀ k, 0 ≤ ap k := fun k =>
    mul_nonneg hμ0 (by linarith [le_abs_self (l k)])
  have ham : ∀ k, 0 ≤ am k := fun k =>
    mul_nonneg hμ0 (by linarith [neg_abs_le (l k)])
  have hsum : ∀ k, a0 k + ap k + am k = 1 := fun k => by simp only [a0, ap, am]; ring
  have hentry : ∀ i k, (Z * V) i k = a0 k * W i k + ap k * W (σ i) k + am k * W (σ⁻¹ i) k := by
    intro i k
    rw [hZV]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.mul_assoc (T2 σ Δ), Matrix.mul_assoc (T1 σ Δ), T2_mul_apply, T1_mul_apply, hD,
      Matrix.diagonal_mul, hρ, smul_eq_mul, a0, ap, am, hμ]
    field_simp
    ring
  have hsq : ‖Z * V‖ ^ 2 ≤ ‖W‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    calc ∑ i, ∑ k, (Z * V) i k ^ 2
        ≤ ∑ i, ∑ k, (a0 k * W i k ^ 2 + ap k * W (σ i) k ^ 2 + am k * W (σ⁻¹ i) k ^ 2) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
          rw [hentry]
          exact sq_convex3_le (ha0 k) (hap k) (ham k) (hsum k)
      _ = ∑ i, ∑ k, a0 k * W i k ^ 2 + ∑ i, ∑ k, ap k * W i k ^ 2 +
            ∑ i, ∑ k, am k * W i k ^ 2 := by
          simp only [Finset.sum_add_distrib]
          rw [Equiv.sum_comp σ (fun i => ∑ k, ap k * W i k ^ 2),
            Equiv.sum_comp σ⁻¹ (fun i => ∑ k, am k * W i k ^ 2)]
      _ = ∑ i, ∑ k, W i k ^ 2 := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          have := hsum k
          linear_combination (W i k ^ 2) * this
  have h1 : ‖Z * V‖ ≤ ‖W‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  rw [norm_mul_orth hV] at h1
  rwa [hW, norm_mul_orth hV] at h1

/-- **`L²`-contractivity of the full explicit Euler streaming step** (the full-rank content of
Theorem 1 of arXiv 2111.07160) for spatially constant density under the CFL condition. -/
theorem PNScheme.euler_norm_le (S : PNScheme ι κ) {ρ₀ Δt : ℝ} (hS : S.CFL ρ₀ Δt)
    (u : Matrix ι κ ℝ) : ‖S.euler Δt u‖ ≤ ‖u‖ := by
  have hx := dir_step_norm_le S.σx (hS.rho_eq) hS.rho_pos hS.Δx_pos hS.Δt_nonneg hS.Vx_orth
    hS.cflx u
  have hy := dir_step_norm_le S.σy (hS.rho_eq) hS.rho_pos hS.Δy_pos hS.Δt_nonneg hS.Vy_orth
    hS.cfly u
  have e : S.euler Δt u =
      (1 / 2 : ℝ) • (u - (2 * Δt) • (T2 S.σx S.Δx * Matrix.diagonal (fun i => (S.ρ i)⁻¹) * u *
        (S.Vx * Matrix.diagonal S.lx * S.Vxᵀ)ᵀ +
        T1 S.σx S.Δx * Matrix.diagonal (fun i => (S.ρ i)⁻¹) * u *
        (S.Vx * Matrix.diagonal (fun k => |S.lx k|) * S.Vxᵀ)ᵀ)) +
      (1 / 2 : ℝ) • (u - (2 * Δt) • (T2 S.σy S.Δy * Matrix.diagonal (fun i => (S.ρ i)⁻¹) * u *
        (S.Vy * Matrix.diagonal S.ly * S.Vyᵀ)ᵀ +
        T1 S.σy S.Δy * Matrix.diagonal (fun i => (S.ρ i)⁻¹) * u *
        (S.Vy * Matrix.diagonal (fun k => |S.ly k|) * S.Vyᵀ)ᵀ)) := by
    simp only [PNScheme.euler, PNScheme.flux, PNScheme.L2x, PNScheme.L2y, PNScheme.L1x,
      PNScheme.L1y, PNScheme.rhoInv, PNScheme.Ax, PNScheme.Ay, PNScheme.absAx, PNScheme.absAy]
    module
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

end Streaming


/-! ### Theorems 1 and 3: `L²`-stability of the streaming step -/

section StreamingDLRA

open scoped LeanDLRA.Frobenius

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The start value `S̃⁰ = X^{1/2,T} X⁰ S⁰ W⁰ᵀ W^{1/2}` of the S-step. -/
noncomputable def galerkinStart {r₀ r : Type*} [Fintype r₀] [Fintype r]
    (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ) (W₀ : Matrix κ r₀ ℝ) (X : Matrix ι r ℝ)
    (W : Matrix κ r ℝ) : Matrix r r ℝ :=
  Xᵀ * (X₀ * S₀ * W₀ᵀ) * W

/-- The explicit Euler S-step of the fixed-rank BUG streaming step, eq. (34c):
`S^{1/2} = S̃⁰ - Δt X^{1/2,T} F(X^{1/2} S̃⁰ W^{1/2,T}) W^{1/2}` (with the sign of the module
docstring); `bugStreamS_eq_reduced` writes it with the reduced matrices of (34c). -/
noncomputable def bugStreamS (S : PNScheme ι κ) (Δt : ℝ) {r₀ r : Type*} [Fintype r₀]
    [Fintype r] (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ) (W₀ : Matrix κ r₀ ℝ)
    (X : Matrix ι r ℝ) (W : Matrix κ r ℝ) : Matrix r r ℝ :=
  galerkinStart X₀ S₀ W₀ X W -
    Δt • (Xᵀ * S.flux (X * galerkinStart X₀ S₀ W₀ X W * Wᵀ) * W)

/-- `bugStreamS` is (34c): `S̃⁰ - Δt (L̂^{(2)}_x S̃⁰ Â_x + L̂^{(2)}_y S̃⁰ Â_y + L̂^{(1)}_x S̃⁰ |Â_x|
+ L̂^{(1)}_y S̃⁰ |Â_y|)` with `L̂ = X^{1/2,T} L X^{1/2}`, `Â = W^{1/2,T} Aᵀ W^{1/2}`. -/
lemma bugStreamS_eq_reduced (S : PNScheme ι κ) (Δt : ℝ) {r₀ r : Type*} [Fintype r₀]
    [Fintype r] (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ) (W₀ : Matrix κ r₀ ℝ)
    (X : Matrix ι r ℝ) (W : Matrix κ r ℝ) :
    bugStreamS S Δt X₀ S₀ W₀ X W =
      galerkinStart X₀ S₀ W₀ X W - Δt • (
        (Xᵀ * S.L2x * X) * galerkinStart X₀ S₀ W₀ X W * (Wᵀ * S.Axᵀ * W) +
        (Xᵀ * S.L2y * X) * galerkinStart X₀ S₀ W₀ X W * (Wᵀ * S.Ayᵀ * W) +
        (Xᵀ * S.L1x * X) * galerkinStart X₀ S₀ W₀ X W * (Wᵀ * S.absAxᵀ * W) +
        (Xᵀ * S.L1y * X) * galerkinStart X₀ S₀ W₀ X W * (Wᵀ * S.absAyᵀ * W)) := by
  simp only [bugStreamS, PNScheme.flux, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- **Theorem 1 of arXiv 2111.07160 (spatially constant density): `L²`-stability of the
fixed-rank BUG streaming step.**  Under the CFL condition `|λ_k| Δt / (ρ₀ Δx) ≤ 1/2`,
`|λ_k| Δt / (ρ₀ Δy) ≤ 1/2` (eigenvalues of `A_x`, `A_y`), for any new bases `X^{1/2}`, `W^{1/2}`
with orthonormal columns (in the integrator they come from the K- and L-steps),
`‖X^{1/2} S^{1/2} W^{1/2,T}‖_F ≤ ‖X⁰ S⁰ W⁰ᵀ‖_F`.  Differences from the paper: the density is
`ρ ≡ ρ₀` (for variable density the claim is false, `theorem1_false_of_variable_density`), the
grid neighbours are arbitrary permutations (periodic grid in the paper's Fourier proof), and the
proof is a convex-combination argument instead of von Neumann analysis. -/
theorem theorem1 (S : PNScheme ι κ) {ρ₀ Δt : ℝ} (hS : S.CFL ρ₀ Δt) {r₀ r : Type*}
    [Fintype r₀] [Fintype r] [DecidableEq r] (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ)
    (W₀ : Matrix κ r₀ ℝ) {X : Matrix ι r ℝ} {W : Matrix κ r ℝ} (hX : Xᵀ * X = 1)
    (hW : Wᵀ * W = 1) :
    ‖X * bugStreamS S Δt X₀ S₀ W₀ X W * Wᵀ‖ ≤ ‖X₀ * S₀ * W₀ᵀ‖ := by
  set St := galerkinStart X₀ S₀ W₀ X W with hSt
  set Y := X * St * Wᵀ with hY
  have hXY : Xᵀ * Y * W = St := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, Matrix.one_mul, Matrix.mul_assoc,
      hW, Matrix.mul_one]
  have e : bugStreamS S Δt X₀ S₀ W₀ X W = Xᵀ * S.euler Δt Y * W := by
    rw [bugStreamS, ← hSt, ← hY, PNScheme.euler, Matrix.mul_sub, Matrix.sub_mul, hXY,
      Matrix.mul_smul, Matrix.smul_mul]
  have hE : ∀ x : Matrix ι κ ℝ, eulerStep (fun u => -S.flux u) Δt x = S.euler Δt x := by
    intro x; simp [eulerStep, PNScheme.euler, sub_eq_add_neg]
  -- the explicit Euler BUG step is `P₁ Q₁ (ū + Δt F(ū))`, `ū = P₁ Q₁ u⁰`
  have hstep : X * bugStreamS S Δt X₀ S₀ W₀ X W * Wᵀ = leftProj X (rightProj W
      (eulerStep (fun u => -S.flux u) Δt (leftProj X (rightProj W (X₀ * S₀ * W₀ᵀ))))) := by
    rw [leftProj_rightProj_apply, leftProj_rightProj_apply, ← galerkinStart, ← hSt, ← hY, hE, e]
  rw [hstep, ← one_mul ‖X₀ * S₀ * W₀ᵀ‖]
  exact bug_euler_norm_le (isOrthProj_leftProj hX) (isOrthProj_rightProj hW)
    (leftProj_rightProj_comm X W) zero_le_one
    (fun x _ => by rw [hE, one_mul]; exact S.euler_norm_le hS x) _

/-- `‖truncation A r‖ ≤ ‖A‖`: the truncated SVD (an orthogonal projection of `A`) does not
increase the Frobenius norm. -/
lemma norm_truncation_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (r : ℕ) : ‖EckartYoung.truncation A r‖ ≤ ‖A‖ := by
  have hP := isOrthProj_rightProj (m := m)
    (EckartYoung.transpose_mul_topRightSingularVectors A r)
  have e : rightProj (EckartYoung.topRightSingularVectors A r) A =
      EckartYoung.truncation A r := by
    rw [rightProj_apply, EckartYoung.truncation]
  rw [← e]
  exact hP.norm_le A

/-- The augmented S-step of the rank-adaptive streaming step (Sec. 6):
`Ŝ^{1/2} = X̂^{1/2,T} u⁰ Ŵ^{1/2} - Δt X̂^{1/2,T} F(u⁰) Ŵ^{1/2}`, `u⁰ = X⁰ S⁰ W⁰ᵀ`.  For augmented
bases `X̂ = [X⁰, ΔX]`, `Ŵ = [W⁰, ΔW]` the first term is `[I, 0]ᵀ S⁰ [I, 0]` and the second is the
paper's `Δt (L̂^{(2),1/2}_x S⁰ A^{1/2}_x + ⋯)` with `L̂^{1/2} = X̂ᵀ L X⁰`, `A^{1/2} = W⁰ᵀ Aᵀ Ŵ`. -/
noncomputable def augStreamS (S : PNScheme ι κ) (Δt : ℝ) {r₀ r : Type*} [Fintype r₀]
    [Fintype r] (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ) (W₀ : Matrix κ r₀ ℝ)
    (Xa : Matrix ι r ℝ) (Wa : Matrix κ r ℝ) : Matrix r r ℝ :=
  Xaᵀ * (X₀ * S₀ * W₀ᵀ) * Wa - Δt • (Xaᵀ * S.flux (X₀ * S₀ * W₀ᵀ) * Wa)

/-- **Theorem 3 of arXiv 2111.07160 (spatially constant density): `L²`-stability of the
rank-adaptive streaming step.**  Under the CFL condition of `theorem1`, the augmented S-step
followed by truncation of `Ŝ^{1/2}` to rank `rt` by the truncated SVD,
`X^{1/2} S^{1/2} W^{1/2,T} = X̂ (truncation Ŝ^{1/2} rt) Ŵᵀ`, satisfies
`‖X^{1/2} S^{1/2} W^{1/2,T}‖_F ≤ ‖X⁰ S⁰ W⁰ᵀ‖_F`, for every truncation rank `rt` (in the paper
chosen from a tolerance) and any orthonormal `X̂`, `Ŵ` (the augmentation `X⁰ ⊂ range X̂` is what
makes `augStreamS` the Galerkin step from `u⁰`, but is not needed for the bound). -/
theorem theorem3 (S : PNScheme ι κ) {ρ₀ Δt : ℝ} (hS : S.CFL ρ₀ Δt) {r₀ : Type*} [Fintype r₀]
    {ra : ℕ} (X₀ : Matrix ι r₀ ℝ) (S₀ : Matrix r₀ r₀ ℝ) (W₀ : Matrix κ r₀ ℝ)
    {Xa : Matrix ι (Fin ra) ℝ} {Wa : Matrix κ (Fin ra) ℝ} (hX : Xaᵀ * Xa = 1)
    (hW : Waᵀ * Wa = 1) (rt : ℕ) :
    ‖Xa * EckartYoung.truncation (augStreamS S Δt X₀ S₀ W₀ Xa Wa) rt * Waᵀ‖ ≤
      ‖X₀ * S₀ * W₀ᵀ‖ := by
  have hE : eulerStep (fun u => -S.flux u) Δt (X₀ * S₀ * W₀ᵀ) = S.euler Δt (X₀ * S₀ * W₀ᵀ) := by
    simp [eulerStep, PNScheme.euler, sub_eq_add_neg]
  have e : augStreamS S Δt X₀ S₀ W₀ Xa Wa = Xaᵀ * S.euler Δt (X₀ * S₀ * W₀ᵀ) * Wa := by
    rw [augStreamS, PNScheme.euler, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [← one_mul ‖X₀ * S₀ * W₀ᵀ‖]
  refine augmentedBug_euler_norm_le (isOrthProj_leftProj_mul_rightProj hX hW)
    (by rw [hE, one_mul]; exact S.euler_norm_le hS _) ?_
  rw [Frobenius.norm_mul_transpose_of_orthonormal hW, Frobenius.norm_mul_of_orthonormal hX,
    mul_apply_eq_comp, leftProj_rightProj_apply, hE, ← e,
    Frobenius.norm_mul_transpose_of_orthonormal hW, Frobenius.norm_mul_of_orthonormal hX]
  exact norm_truncation_le _ rt

end StreamingDLRA


/-! ### Theorems 2 and 4: stability of the multilevel scheme with implicit scattering -/

section Scattering

open scoped LeanDLRA.Frobenius

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Right multiplication by `diag(d)` with `|d_k| ≤ c` multiplies the norm by at most `c`. -/
lemma norm_mul_diagonal_le {m : Type*} [Fintype m] {d : κ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ k, |d k| ≤ c) (M : Matrix m κ ℝ) : ‖M * Matrix.diagonal d‖ ≤ c * ‖M‖ := by
  have hsq : ‖M * Matrix.diagonal d‖ ^ 2 ≤ (c * ‖M‖) ^ 2 := by
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Matrix.mul_diagonal, mul_pow]
    have h1 : d k ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hd k) 2
    nlinarith [sq_nonneg (M i k)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 hsq

/-- The resolvent `(I + Σ_t Δt I - Δt Σ)⁻¹` of the implicit L-step (37d), `Σ = diag(Σ_kk)`. -/
noncomputable def resolvent (Δt sigT : ℝ) (sigS : κ → ℝ) : Matrix κ κ ℝ :=
  (1 + (Δt * sigT) • (1 : Matrix κ κ ℝ) - Δt • Matrix.diagonal sigS)⁻¹

omit [Fintype κ] [DecidableEq κ] in
/-- **Remark 2 / condition (41) of arXiv 2111.07160.**  If `Σ_kk ≤ Σ_t` (in the paper
`|Σ_kk| ≤ Σ_11 = Σ_t`) and `Δt ≥ 0`, the scattering CFL condition
`1 / (1 + Δt Σ_t - Δt Σ_kk) ≤ 1` holds for every `k`. -/
lemma scattering_cfl {Δt sigT : ℝ} {sigS : κ → ℝ} (hΔt : 0 ≤ Δt) (hsig : ∀ k, sigS k ≤ sigT)
    (k : κ) : 1 / (1 + Δt * sigT - Δt * sigS k) ≤ 1 := by
  have h : 0 ≤ Δt * sigT - Δt * sigS k := by
    rw [← mul_sub]; exact mul_nonneg hΔt (sub_nonneg.2 (hsig k))
  rw [div_le_one (by linarith)]
  linarith

/-- The resolvent is the diagonal matrix of the `1 / (1 + Δt Σ_t - Δt Σ_kk)` (the explicit inverse
noted after (37d)). -/
lemma resolvent_eq {Δt sigT : ℝ} {sigS : κ → ℝ} (hΔt : 0 ≤ Δt) (hsig : ∀ k, sigS k ≤ sigT) :
    resolvent Δt sigT sigS = Matrix.diagonal fun k => (1 + Δt * sigT - Δt * sigS k)⁻¹ := by
  have hpos : ∀ k, 0 < 1 + Δt * sigT - Δt * sigS k := fun k => by
    have h : 0 ≤ Δt * sigT - Δt * sigS k := by
      rw [← mul_sub]; exact mul_nonneg hΔt (sub_nonneg.2 (hsig k))
    linarith
  apply Matrix.inv_eq_right_inv
  ext i j
  rw [Matrix.mul_diagonal]
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq, smul_eq_mul, mul_one]
    exact mul_inv_cancel₀ (hpos i).ne'
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

/-- Multiplication by the resolvent does not increase the norm. -/
lemma norm_mul_resolvent_le {m : Type*} [Fintype m] {Δt sigT : ℝ} {sigS : κ → ℝ}
    (hΔt : 0 ≤ Δt) (hsig : ∀ k, sigS k ≤ sigT) (M : Matrix m κ ℝ) :
    ‖M * resolvent Δt sigT sigS‖ ≤ ‖M‖ := by
  rw [resolvent_eq hΔt hsig]
  have h : ∀ k, |(1 + Δt * sigT - Δt * sigS k)⁻¹| ≤ 1 := fun k => by
    have h0 : 0 ≤ Δt * sigT - Δt * sigS k := by
      rw [← mul_sub]; exact mul_nonneg hΔt (sub_nonneg.2 (hsig k))
    rw [abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_le_one_of_one_le₀ (by linarith)
  simpa using norm_mul_diagonal_le zero_le_one h M

/-- The bracket of the scattering S-steps (37c) (and of the rank-adaptive versions in Sec. 6):
`X₁ᵀ u^{1/2} W₁ + Δt X₁ᵀ u_src Σ W₁`, where `u^{1/2}` is the streamed solution of the level and
`u_src` the solution of the previous level at `t₁` (`ψ(t₁) T_M` for the first level).  For
`u^{1/2} = X^{1/2} S^{1/2} W^{1/2,T}` the first term is the paper's `S̃^{1/2}`. -/
noncomputable def collidedS {r : Type*} [Fintype r] (Δt : ℝ) (sigS : κ → ℝ)
    (uh : Matrix ι κ ℝ) (X : Matrix ι r ℝ) (W : Matrix κ r ℝ) (src : Matrix ι κ ℝ) :
    Matrix r r ℝ :=
  Xᵀ * uh * W + Δt • (Xᵀ * src * Matrix.diagonal sigS * W)

/-- The implicit scattering S-step (36c) of the collided levels:
`S^1 = (1 + Δt Σ_t)⁻¹ (S̃^{1/2} + Δt X₁ᵀ u_src Σ W₁)`. -/
noncomputable def scatterS {r : Type*} [Fintype r] (Δt sigT : ℝ) (sigS : κ → ℝ)
    (uh : Matrix ι κ ℝ) (X : Matrix ι r ℝ) (W : Matrix κ r ℝ) (src : Matrix ι κ ℝ) :
    Matrix r r ℝ :=
  (1 + Δt * sigT)⁻¹ • collidedS Δt sigS uh X W src

omit [DecidableEq ι] in
/-- Norm bound for the bracket (37c) of arXiv 2111.07160:
`‖X₁ᵀ u^{1/2} W₁ + Δt X₁ᵀ u_src Σ W₁‖ ≤ ‖u^{1/2}‖ + Δt Σ_t ‖u_src‖`. -/
lemma collidedS_norm_le {r : Type*} [Fintype r] [DecidableEq r] {Δt sigT : ℝ}
    {sigS : κ → ℝ} (hΔt : 0 ≤ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT)
    (uh : Matrix ι κ ℝ) {X : Matrix ι r ℝ} {W : Matrix κ r ℝ} (hX : Xᵀ * X = 1)
    (hW : Wᵀ * W = 1) (src : Matrix ι κ ℝ) :
    ‖collidedS Δt sigS uh X W src‖ ≤ ‖uh‖ + Δt * sigT * ‖src‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_mul_le_of_orthonormal hW _).trans (norm_transpose_mul_le hX _)
  · rw [norm_smul, Real.norm_of_nonneg hΔt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hΔt
    calc ‖Xᵀ * src * Matrix.diagonal sigS * W‖ ≤ ‖Xᵀ * src * Matrix.diagonal sigS‖ :=
          norm_mul_le_of_orthonormal hW _
      _ = ‖Xᵀ * (src * Matrix.diagonal sigS)‖ := by rw [Matrix.mul_assoc]
      _ ≤ ‖src * Matrix.diagonal sigS‖ := norm_transpose_mul_le hX _
      _ ≤ sigT * ‖src‖ := norm_mul_diagonal_le hsigT hsig src

omit [DecidableEq ι] in
/-- Norm bound for the implicit scattering step (36c) of arXiv 2111.07160:
`(1 + Δt Σ_t) ‖S¹‖ ≤ ‖u^{1/2}‖ + Δt Σ_t ‖u_src‖`. -/
lemma scatterS_norm_le {r : Type*} [Fintype r] [DecidableEq r] {Δt sigT : ℝ}
    {sigS : κ → ℝ} (hΔt : 0 ≤ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT)
    (uh : Matrix ι κ ℝ) {X : Matrix ι r ℝ} {W : Matrix κ r ℝ} (hX : Xᵀ * X = 1)
    (hW : Wᵀ * W = 1) (src : Matrix ι κ ℝ) :
    (1 + Δt * sigT) * ‖scatterS Δt sigT sigS uh X W src‖ ≤ ‖uh‖ + Δt * sigT * ‖src‖ := by
  have hpos : 0 < 1 + Δt * sigT := by have := mul_nonneg hΔt hsigT; linarith
  rw [scatterS, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul]
  exact collidedS_norm_le hΔt hsigT hsig uh hX hW src

/-- **The level recursion behind Theorems 2 and 4.**  With `b = Δt Σ_t`, if the uncollided
flux satisfies `(1 + b) p₁ ≤ p₀`, each collided level `ℓ = 1, …, L` satisfies
`(1 + b) a₁ ℓ ≤ a₀ ℓ + b a₁ (ℓ-1)` (with `a₁ 0 = p₁`), and the collided flux satisfies
`c₁ ≤ c₀ + b a₁ L`, then `c₁ + ∑ a₁ + p₁ ≤ c₀ + ∑ a₀ + p₀`. -/
lemma level_telescope {L : ℕ} {a₀ a₁ : ℕ → ℝ} {p₀ c₀ c₁ b : ℝ}
    (hp : (1 + b) * a₁ 0 ≤ p₀)
    (hℓ : ∀ ℓ ∈ Finset.Icc 1 L, (1 + b) * a₁ ℓ ≤ a₀ ℓ + b * a₁ (ℓ - 1))
    (hc : c₁ ≤ c₀ + b * a₁ L) :
    c₁ + ∑ ℓ ∈ Finset.Icc 1 L, a₁ ℓ + a₁ 0 ≤ c₀ + ∑ ℓ ∈ Finset.Icc 1 L, a₀ ℓ + p₀ := by
  have key : ∀ n ≤ L, ∑ ℓ ∈ Finset.Icc 1 n, a₁ ℓ + a₁ 0 + b * a₁ n ≤
      ∑ ℓ ∈ Finset.Icc 1 n, a₀ ℓ + p₀ := by
    intro n
    induction n with
    | zero =>
      intro _
      have e : (1 + b) * a₁ 0 = a₁ 0 + b * a₁ 0 := by ring
      simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, zero_add]
      linarith
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hℓ (n + 1) (Finset.mem_Icc.2 ⟨by omega, hn⟩)
      simp only [Nat.add_sub_cancel] at h2
      have e : (1 + b) * a₁ (n + 1) = a₁ (n + 1) + b * a₁ (n + 1) := by ring
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      linarith
  have := key L le_rfl
  linarith

/-- One collided level of the **fixed-rank** scheme in one time step: the old factors
`X⁰, S⁰, W⁰`, the bases `X^{1/2}, W^{1/2}` of the streaming step and `X¹, W¹` of the scattering
step (for the collided flux `W¹` is the `W̃¹_c` of (37b)). -/
structure FixedLevel (ι κ : Type*) where
  r₀ : ℕ
  rh : ℕ
  r₁ : ℕ
  X₀ : Matrix ι (Fin r₀) ℝ
  S₀ : Matrix (Fin r₀) (Fin r₀) ℝ
  W₀ : Matrix κ (Fin r₀) ℝ
  Xh : Matrix ι (Fin rh) ℝ
  Wh : Matrix κ (Fin rh) ℝ
  X₁ : Matrix ι (Fin r₁) ℝ
  W₁ : Matrix κ (Fin r₁) ℝ

namespace FixedLevel

variable (lv : FixedLevel ι κ)

/-- The new bases have orthonormal columns. -/
structure Orth : Prop where
  hXh : lv.Xhᵀ * lv.Xh = 1
  hWh : lv.Whᵀ * lv.Wh = 1
  hX₁ : lv.X₁ᵀ * lv.X₁ = 1
  hW₁ : lv.W₁ᵀ * lv.W₁ = 1

/-- `u⁰ = X⁰ S⁰ W⁰ᵀ`. -/
noncomputable def u₀ : Matrix ι κ ℝ := lv.X₀ * lv.S₀ * lv.W₀ᵀ

/-- The streamed solution `u^{1/2} = X^{1/2} S^{1/2} W^{1/2,T}`, `S^{1/2}` from (34c). -/
noncomputable def uh (S : PNScheme ι κ) (Δt : ℝ) : Matrix ι κ ℝ :=
  lv.Xh * bugStreamS S Δt lv.X₀ lv.S₀ lv.W₀ lv.Xh lv.Wh * lv.Whᵀ

/-- A collided level after the scattering step (36c): `u¹ = X¹ S¹ W^{1,T}`. -/
noncomputable def scatter (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (src : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  lv.X₁ * scatterS Δt sigT sigS (lv.uh S Δt) lv.X₁ lv.W₁ src * lv.W₁ᵀ

/-- The collided flux after (37c) and the L-step (37d): `u¹_c = X¹_c S¹_c W^{1,T}_c = X¹_c L̃¹_c`,
`L̃¹_c = S̃¹_c W̃^{1,T}_c (I + Σ_t Δt I - Δt Σ)⁻¹`. -/
noncomputable def collide (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (src : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  lv.X₁ * (collidedS Δt sigS (lv.uh S Δt) lv.X₁ lv.W₁ src * lv.W₁ᵀ * resolvent Δt sigT sigS)

variable {lv}

/-- Theorem 1 of arXiv 2111.07160 for one level: `‖u^{1/2}‖ ≤ ‖u⁰‖`. -/
lemma uh_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt : ℝ} (hS : S.CFL ρ₀ Δt) :
    ‖lv.uh S Δt‖ ≤ ‖lv.u₀‖ :=
  theorem1 S hS lv.X₀ lv.S₀ lv.W₀ hlv.hXh hlv.hWh

/-- One collided level of arXiv 2111.07160 (proof of Theorem 2):
`(1 + Δt Σ_t) ‖u¹_ℓ‖ ≤ ‖u⁰_ℓ‖ + Δt Σ_t ‖u¹_{ℓ-1}‖`. -/
lemma scatter_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ}
    (hS : S.CFL ρ₀ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) (src : Matrix ι κ ℝ) :
    (1 + Δt * sigT) * ‖lv.scatter S Δt sigT sigS src‖ ≤ ‖lv.u₀‖ + Δt * sigT * ‖src‖ := by
  rw [scatter, Frobenius.norm_mul_transpose_of_orthonormal hlv.hW₁,
    Frobenius.norm_mul_of_orthonormal hlv.hX₁]
  refine (scatterS_norm_le hS.Δt_nonneg hsigT hsig _ hlv.hX₁ hlv.hW₁ src).trans ?_
  linarith [uh_norm_le hlv S hS]

/-- The collided flux of arXiv 2111.07160 (proof of Theorem 2):
`‖u¹_c‖ ≤ ‖u⁰_c‖ + Δt Σ_t ‖u¹_L‖`. -/
lemma collide_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ}
    (hS : S.CFL ρ₀ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) (src : Matrix ι κ ℝ) :
    ‖lv.collide S Δt sigT sigS src‖ ≤ ‖lv.u₀‖ + Δt * sigT * ‖src‖ := by
  rw [collide, Frobenius.norm_mul_of_orthonormal hlv.hX₁]
  refine (norm_mul_resolvent_le hS.Δt_nonneg (fun k => (le_abs_self _).trans (hsig k)) _).trans ?_
  rw [Frobenius.norm_mul_transpose_of_orthonormal hlv.hW₁]
  refine (collidedS_norm_le hS.Δt_nonneg hsigT hsig _ hlv.hX₁ hlv.hW₁ src).trans ?_
  linarith [uh_norm_le hlv S hS]

end FixedLevel

/-- The solutions `u¹_ℓ` of the fixed-rank scheme: `ℓ = 0` is the uncollided flux `ψ(t₁)` (in
moment form), and level `ℓ + 1` is scattered from level `ℓ` (the recursion of Sec. 4.2). -/
noncomputable def fixedSol (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (lv : ℕ → FixedLevel ι κ) (ψ₁ : Matrix ι κ ℝ) : ℕ → Matrix ι κ ℝ
  | 0 => ψ₁
  | ℓ + 1 => (lv (ℓ + 1)).scatter S Δt sigT sigS (fixedSol S Δt sigT sigS lv ψ₁ ℓ)

/-- **Theorem 2 of arXiv 2111.07160 (spatially constant density): stability of the fixed-rank
collided-source scheme with implicit scattering.**  Assume the streaming CFL condition of
`theorem1` and `|Σ_kk| ≤ Σ_t` (which gives the scattering CFL condition (41),
`scattering_cfl`).  Let `ψ₀ = ψ(t₀)`, `ψ₁ = ψ(t₁)` be the uncollided flux (in moment form, i.e.
`ψ T_M`), computed by any solver with `(1 + Δt Σ_t) ‖ψ₁‖ ≤ ‖ψ₀‖` (the paper's implicit
treatment; `uncollided_norm_le` gives one).  Then for the collided levels `ℓ = 1, …, L`
(streaming (34c), scattering (36c)) and the collided flux `c` (streaming, (37c), L-step (37d)),
with arbitrary orthonormal new bases,

`‖u¹_c‖ + ∑_{ℓ=1}^L ‖u¹_ℓ‖ + ‖ψ(t₁)‖ ≤ ‖u⁰_c‖ + ∑_{ℓ=1}^L ‖u⁰_ℓ‖ + ‖ψ(t₀)‖` (Frobenius norms). -/
theorem theorem2 (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ} (hS : S.CFL ρ₀ Δt)
    (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) {L : ℕ} {lv : ℕ → FixedLevel ι κ}
    (hlv : ∀ ℓ ∈ Finset.Icc 1 L, (lv ℓ).Orth) {c : FixedLevel ι κ} (hc : c.Orth)
    {ψ₀ ψ₁ : Matrix ι κ ℝ} (hψ : (1 + Δt * sigT) * ‖ψ₁‖ ≤ ‖ψ₀‖) :
    ‖c.collide S Δt sigT sigS (fixedSol S Δt sigT sigS lv ψ₁ L)‖ +
        ∑ ℓ ∈ Finset.Icc 1 L, ‖fixedSol S Δt sigT sigS lv ψ₁ ℓ‖ + ‖ψ₁‖ ≤
      ‖c.u₀‖ + ∑ ℓ ∈ Finset.Icc 1 L, ‖(lv ℓ).u₀‖ + ‖ψ₀‖ := by
  refine level_telescope (a₁ := fun ℓ => ‖fixedSol S Δt sigT sigS lv ψ₁ ℓ‖) hψ ?_
    (c.collide_norm_le hc S hS hsigT hsig _)
  intro ℓ hℓ
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by simp at hℓ; omega⟩
  exact (lv (k + 1)).scatter_norm_le (hlv _ hℓ) S hS hsigT hsig _

/-- The uncollided update `ψ(t₁) = (1 + Δt Σ_t)⁻¹ (ψ(t₀) - Δt F(ψ(t₀)))` (explicit streaming,
implicit absorption, in moment form) satisfies the hypothesis of `theorem2`. -/
theorem uncollided_norm_le (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} (hS : S.CFL ρ₀ Δt)
    (hsigT : 0 ≤ sigT) (ψ₀ : Matrix ι κ ℝ) :
    (1 + Δt * sigT) * ‖(1 + Δt * sigT)⁻¹ • S.euler Δt ψ₀‖ ≤ ‖ψ₀‖ := by
  have hpos : 0 < 1 + Δt * sigT := by have := mul_nonneg hS.Δt_nonneg hsigT; linarith
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), ← mul_assoc,
    mul_inv_cancel₀ hpos.ne', one_mul]
  exact S.euler_norm_le hS ψ₀

/-- One collided level of the **rank-adaptive** scheme (Sec. 6) in one time step: old factors,
augmented streaming bases `X̂^{1/2}, Ŵ^{1/2}` and truncation rank `ta`, augmented scattering bases
`X̂¹, Ŵ¹` and truncation rank `tb`. -/
structure AdaptiveLevel (ι κ : Type*) where
  r₀ : ℕ
  ra : ℕ
  rb : ℕ
  X₀ : Matrix ι (Fin r₀) ℝ
  S₀ : Matrix (Fin r₀) (Fin r₀) ℝ
  W₀ : Matrix κ (Fin r₀) ℝ
  Xa : Matrix ι (Fin ra) ℝ
  Wa : Matrix κ (Fin ra) ℝ
  ta : ℕ
  Xb : Matrix ι (Fin rb) ℝ
  Wb : Matrix κ (Fin rb) ℝ
  tb : ℕ

namespace AdaptiveLevel

variable (lv : AdaptiveLevel ι κ)

/-- The augmented bases have orthonormal columns. -/
structure Orth : Prop where
  hXa : lv.Xaᵀ * lv.Xa = 1
  hWa : lv.Waᵀ * lv.Wa = 1
  hXb : lv.Xbᵀ * lv.Xb = 1
  hWb : lv.Wbᵀ * lv.Wb = 1

/-- `u⁰ = X⁰ S⁰ W⁰ᵀ`. -/
noncomputable def u₀ : Matrix ι κ ℝ := lv.X₀ * lv.S₀ * lv.W₀ᵀ

/-- The streamed and truncated solution `u^{1/2} = X̂ (truncation Ŝ^{1/2} ta) Ŵᵀ`. -/
noncomputable def uh (S : PNScheme ι κ) (Δt : ℝ) : Matrix ι κ ℝ :=
  lv.Xa * EckartYoung.truncation (augStreamS S Δt lv.X₀ lv.S₀ lv.W₀ lv.Xa lv.Wa) lv.ta * lv.Waᵀ

/-- A collided level after the augmented implicit scattering step and truncation (Sec. 6). -/
noncomputable def scatter (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (src : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  lv.Xb * EckartYoung.truncation (scatterS Δt sigT sigS (lv.uh S Δt) lv.Xb lv.Wb src) lv.tb *
    lv.Wbᵀ

/-- The collided flux after the augmented step `Ŝ¹_c`, truncation, and the L-step (37d). -/
noncomputable def collide (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (src : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  lv.Xb * (EckartYoung.truncation (collidedS Δt sigS (lv.uh S Δt) lv.Xb lv.Wb src) lv.tb *
    lv.Wbᵀ * resolvent Δt sigT sigS)

variable {lv}

/-- Theorem 3 of arXiv 2111.07160 for one level: `‖u^{1/2}‖ ≤ ‖u⁰‖`. -/
lemma uh_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt : ℝ} (hS : S.CFL ρ₀ Δt) :
    ‖lv.uh S Δt‖ ≤ ‖lv.u₀‖ :=
  theorem3 S hS lv.X₀ lv.S₀ lv.W₀ hlv.hXa hlv.hWa lv.ta

/-- One collided level of arXiv 2111.07160 (proof of Theorem 4):
`(1 + Δt Σ_t) ‖u¹_ℓ‖ ≤ ‖u⁰_ℓ‖ + Δt Σ_t ‖u¹_{ℓ-1}‖`. -/
lemma scatter_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ}
    (hS : S.CFL ρ₀ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) (src : Matrix ι κ ℝ) :
    (1 + Δt * sigT) * ‖lv.scatter S Δt sigT sigS src‖ ≤ ‖lv.u₀‖ + Δt * sigT * ‖src‖ := by
  rw [scatter, Frobenius.norm_mul_transpose_of_orthonormal hlv.hWb,
    Frobenius.norm_mul_of_orthonormal hlv.hXb]
  have hpos : 0 ≤ 1 + Δt * sigT := by have := mul_nonneg hS.Δt_nonneg hsigT; linarith
  refine (mul_le_mul_of_nonneg_left (norm_truncation_le _ _) hpos).trans ?_
  refine (scatterS_norm_le hS.Δt_nonneg hsigT hsig _ hlv.hXb hlv.hWb src).trans ?_
  linarith [uh_norm_le hlv S hS]

/-- The collided flux of arXiv 2111.07160 (proof of Theorem 4):
`‖u¹_c‖ ≤ ‖u⁰_c‖ + Δt Σ_t ‖u¹_L‖`. -/
lemma collide_norm_le (hlv : lv.Orth) (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ}
    (hS : S.CFL ρ₀ Δt) (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) (src : Matrix ι κ ℝ) :
    ‖lv.collide S Δt sigT sigS src‖ ≤ ‖lv.u₀‖ + Δt * sigT * ‖src‖ := by
  rw [collide, Frobenius.norm_mul_of_orthonormal hlv.hXb]
  refine (norm_mul_resolvent_le hS.Δt_nonneg (fun k => (le_abs_self _).trans (hsig k)) _).trans ?_
  rw [Frobenius.norm_mul_transpose_of_orthonormal hlv.hWb]
  refine (norm_truncation_le _ _).trans ?_
  refine (collidedS_norm_le hS.Δt_nonneg hsigT hsig _ hlv.hXb hlv.hWb src).trans ?_
  linarith [uh_norm_le hlv S hS]

end AdaptiveLevel

/-- The solutions `u¹_ℓ` of the rank-adaptive scheme (`ℓ = 0`: the uncollided flux `ψ(t₁)`). -/
noncomputable def adaptiveSol (S : PNScheme ι κ) (Δt sigT : ℝ) (sigS : κ → ℝ)
    (lv : ℕ → AdaptiveLevel ι κ) (ψ₁ : Matrix ι κ ℝ) : ℕ → Matrix ι κ ℝ
  | 0 => ψ₁
  | ℓ + 1 => (lv (ℓ + 1)).scatter S Δt sigT sigS (adaptiveSol S Δt sigT sigS lv ψ₁ ℓ)

/-- **Theorem 4 of arXiv 2111.07160 (spatially constant density): stability of the rank-adaptive
collided-source scheme.**  Same hypotheses and conclusion as `theorem2`, for the rank-adaptive
scheme of Sec. 6: augmented streaming step (`theorem3`), augmented implicit scattering steps
with truncation for the levels, and for the collided flux the augmented step, truncation and
the L-step (37d).  Bases are arbitrary with orthonormal columns and truncation ranks arbitrary. -/
theorem theorem4 (S : PNScheme ι κ) {ρ₀ Δt sigT : ℝ} {sigS : κ → ℝ} (hS : S.CFL ρ₀ Δt)
    (hsigT : 0 ≤ sigT) (hsig : ∀ k, |sigS k| ≤ sigT) {L : ℕ} {lv : ℕ → AdaptiveLevel ι κ}
    (hlv : ∀ ℓ ∈ Finset.Icc 1 L, (lv ℓ).Orth) {c : AdaptiveLevel ι κ} (hc : c.Orth)
    {ψ₀ ψ₁ : Matrix ι κ ℝ} (hψ : (1 + Δt * sigT) * ‖ψ₁‖ ≤ ‖ψ₀‖) :
    ‖c.collide S Δt sigT sigS (adaptiveSol S Δt sigT sigS lv ψ₁ L)‖ +
        ∑ ℓ ∈ Finset.Icc 1 L, ‖adaptiveSol S Δt sigT sigS lv ψ₁ ℓ‖ + ‖ψ₁‖ ≤
      ‖c.u₀‖ + ∑ ℓ ∈ Finset.Icc 1 L, ‖(lv ℓ).u₀‖ + ‖ψ₀‖ := by
  refine level_telescope (a₁ := fun ℓ => ‖adaptiveSol S Δt sigT sigS lv ψ₁ ℓ‖) hψ ?_
    (c.collide_norm_le hc S hS hsigT hsig _)
  intro ℓ hℓ
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by simp at hℓ; omega⟩
  exact (lv (k + 1)).scatter_norm_le (hlv _ hℓ) S hS hsigT hsig _

end Scattering


/-! ### Variable density: Theorems 1 and 2 are false -/

section Counterexample

open scoped LeanDLRA.Frobenius

/-- `H = (√2/2) [[1, 1], [1, -1]]`: orthonormal eigenvectors of `A = [[0, 1], [1, 0]]`. -/
noncomputable def hMat : Matrix (Fin 2) (Fin 2) ℝ := (√2 / 2) • !![1, 1; 1, -1]

/-- `H` is symmetric (counterexample to Theorem 1 of arXiv 2111.07160). -/
lemma hMat_transpose : hMatᵀ = hMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hMat]

/-- `H² = I` (counterexample to Theorem 1 of arXiv 2111.07160). -/
lemma hMat_mul_self : hMat * hMat = 1 := by
  have h2 : (√2 / 2) * (√2 / 2) = (1 / 2 : ℝ) := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith
  rw [hMat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- `H` is orthogonal (counterexample to Theorem 1 of arXiv 2111.07160). -/
lemma hMat_orth : hMatᵀ * hMat = 1 := by rw [hMat_transpose, hMat_mul_self]

/-- The `2`-cell periodic grid in `x` (one cell in `y`) with densities `ρ = (2, 4)`, unit mesh
sizes, and the `P_1`-type flux matrices `A_x = A_y = [[0, 1], [1, 0]] = H diag(1, -1) Hᵀ`. -/
noncomputable def cexScheme : PNScheme (Fin 2) (Fin 2) where
  σx := Equiv.swap 0 1
  σy := 1
  Δx := 1
  Δy := 1
  ρ := ![2, 4]
  Vx := hMat
  lx := ![1, -1]
  Vy := hMat
  ly := ![1, -1]

/-- The flux matrix of the counterexample is `A_x = [[0, 1], [1, 0]]` (arXiv 2111.07160). -/
lemma cex_Ax : cexScheme.Ax = !![0, 1; 1, 0] := by
  have h2 : (√2 / 2) * (√2 / 2) = (1 / 2 : ℝ) := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith
  have hd : Matrix.diagonal (![1, -1] : Fin 2 → ℝ) = !![1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp only [PNScheme.Ax, cexScheme, hMat_transpose, hd]
  rw [hMat, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Its Roe matrix is `|A_x| = I` (counterexample to Theorem 1 of arXiv 2111.07160). -/
lemma cex_absAx : cexScheme.absAx = 1 := by
  have h : (fun k => |(![1, -1] : Fin 2 → ℝ) k|) = fun _ => 1 := by
    funext k; fin_cases k <;> simp
  simp only [PNScheme.absAx, cexScheme, h, Matrix.diagonal_one, Matrix.mul_one, hMat_transpose,
    hMat_mul_self]

/-- The shift matrix of the identity permutation is `I`. -/
lemma shiftMat_one {ι : Type*} [DecidableEq ι] : shiftMat (1 : Equiv.Perm ι) = 1 := by
  rw [shiftMat, Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- On the `2 × 1` grid only the numerical diffusion in `x` survives in `F`
(counterexample to Theorem 1 of arXiv 2111.07160). -/
lemma cex_flux_apply (u : Matrix (Fin 2) (Fin 2) ℝ) :
    cexScheme.flux u = T1 (Equiv.swap 0 1) 1 * cexScheme.rhoInv * u := by
  have hT2x : T2 (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by simp [T2, Equiv.swap_inv]
  have hT2y : T2 (1 : Equiv.Perm (Fin 2)) 1 = 0 := by simp [T2]
  have hT1y : T1 (1 : Equiv.Perm (Fin 2)) 1 = 0 := by
    simp only [T1, inv_one, shiftMat_one]
    rw [two_smul]; simp
  simp only [PNScheme.flux, PNScheme.L2x, PNScheme.L2y, PNScheme.L1x, PNScheme.L1y, cex_absAx]
  simp [cexScheme, hT2x, hT2y, hT1y]

/-- The initial value: unit scalar flux in both cells, zero first moment. -/
noncomputable def cexU : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 0]

/-- The full Euler step of the counterexample (arXiv 2111.07160, Theorem 1). -/
lemma cex_euler : cexScheme.euler 1 cexU = !![3 / 4, 0; 5 / 4, 0] := by
  rw [PNScheme.euler, cex_flux_apply, one_smul]
  ext i k
  rw [Matrix.sub_apply, Matrix.mul_assoc, T1_mul_apply]
  fin_cases i <;> fin_cases k <;>
    simp [PNScheme.rhoInv, cexScheme, Matrix.diagonal_mul, cexU] <;>
    norm_num

/-- The squared Frobenius norm of a `2 × 2` matrix. -/
lemma norm_sq_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖M‖ ^ 2 = M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]; simp [Fin.sum_univ_two]; ring

/-- The Euler step of the counterexample increases the norm (arXiv 2111.07160, Theorem 1). -/
lemma cex_norm_lt : ‖cexU‖ < ‖cexScheme.euler 1 cexU‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [norm_sq_fin_two, norm_sq_fin_two, cex_euler]
  simp [cexU]
  norm_num

/-- **Theorem 1 of arXiv 2111.07160 is false for spatially varying density.**  On the periodic
`2 × 1` grid with `Δx = Δy = 1`, densities `ρ = (2, 4)` (so `ρ_min = 2`), the `P_1`-type flux
matrices `A_x = A_y = [[0, 1], [1, 0]]` (eigenvalues `±1`) and `Δt = 1`, the CFL condition
`λ_max Δt / (ρ_min Δx) = 1/2 ≤ 1/2` holds, all bases are orthonormal, and yet the BUG streaming
step (here with full rank `2`, so `X^{1/2} = W^{1/2} = I` and it equals the full Euler step)
increases the norm: `‖u⁰‖² = 2 < 17/8 = ‖u^{1/2}‖²` for `u⁰ = [[1, 0], [1, 0]]`.  On this
grid the two `x`-neighbours of a cell coincide and the `y`-neighbour is the cell itself; the
stencils `T1`, `T2` are applied in operator form (contributions added), so the `y`-stencils
vanish.  The flux has the sign of the paper's proof (`PNScheme.euler`).  The paper's
proof replaces `‖(½ I + Δt M ρ̃⁻¹)‖` by `|½ + Δt λ_max(M) ρ_min⁻¹|`, which needs `ρ̃⁻¹ = Eᴴ ρ⁻¹ E`
to commute with the Fourier symbols, i.e. constant density. -/
theorem theorem1_false_of_variable_density :
    ∃ (S : PNScheme (Fin 2) (Fin 2)) (ρmin Δt : ℝ) (X₀ W₀ X W S₀ : Matrix (Fin 2) (Fin 2) ℝ),
      0 < ρmin ∧ S.ρ 0 = ρmin ∧ (∀ i, ρmin ≤ S.ρ i) ∧ 0 < S.Δx ∧ 0 < S.Δy ∧ 0 < Δt ∧
      S.Vxᵀ * S.Vx = 1 ∧ S.Vyᵀ * S.Vy = 1 ∧
      (∀ k, |S.lx k| * Δt / (ρmin * S.Δx) ≤ 1 / 2) ∧
      (∀ k, |S.ly k| * Δt / (ρmin * S.Δy) ≤ 1 / 2) ∧
      X₀ᵀ * X₀ = 1 ∧ W₀ᵀ * W₀ = 1 ∧ Xᵀ * X = 1 ∧ Wᵀ * W = 1 ∧
      ‖X₀ * S₀ * W₀ᵀ‖ < ‖X * bugStreamS S Δt X₀ S₀ W₀ X W * Wᵀ‖ := by
  have hl : ∀ k, |(![1, -1] : Fin 2 → ℝ) k| * 1 / (2 * 1) ≤ 1 / 2 := by
    intro k; fin_cases k <;> norm_num
  refine ⟨cexScheme, 2, 1, 1, 1, 1, 1, cexU, by norm_num, rfl, ?_, by simp [cexScheme],
    by simp [cexScheme], by norm_num, hMat_orth, hMat_orth, hl, hl, by simp, by simp, by simp,
    by simp, ?_⟩
  · intro i; fin_cases i <;> norm_num [cexScheme]
  · have e : bugStreamS cexScheme 1 1 cexU 1 1 1 = cexScheme.euler 1 cexU := by
      simp [bugStreamS, galerkinStart, PNScheme.euler]
    simpa [e] using cex_norm_lt

/-- The collided flux of the counterexample: full rank `2`, identity bases, `u⁰_c = cexU`. -/
noncomputable def cexCollided : FixedLevel (Fin 2) (Fin 2) := ⟨2, 2, 2, 1, cexU, 1, 1, 1, 1, 1⟩

/-- A collided level with zero data, full rank `2` and identity bases. -/
noncomputable def cexZeroLevel : FixedLevel (Fin 2) (Fin 2) := ⟨2, 2, 2, 1, 0, 1, 1, 1, 1, 1⟩

/-- `Iᵀ I = I` for `2 × 2` matrices. -/
lemma one_transpose_mul_one : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp

/-- The bases of `cexCollided` are orthonormal. -/
lemma cexCollided_orth : cexCollided.Orth :=
  ⟨one_transpose_mul_one, one_transpose_mul_one, one_transpose_mul_one, one_transpose_mul_one⟩

/-- The bases of `cexZeroLevel` are orthonormal. -/
lemma cexZeroLevel_orth : cexZeroLevel.Orth :=
  ⟨one_transpose_mul_one, one_transpose_mul_one, one_transpose_mul_one, one_transpose_mul_one⟩

/-- **Theorem 2 of arXiv 2111.07160 is false for spatially varying density.**  With the data of
`theorem1_false_of_variable_density`, one collided level (`L = 1`) with zero data, zero
uncollided flux, and isotropic scattering `Σ_t = Σ_00 = 1`, `Σ_11 = 0` (so `|Σ_kk| ≤ Σ_t` and
(41) hold), the claimed estimate fails: the right-hand side is `‖u⁰_c‖ = √2` and the left-hand
side is `‖u¹_c‖ = √(17/8)`. -/
theorem theorem2_false_of_variable_density :
    ∃ (S : PNScheme (Fin 2) (Fin 2)) (ρmin Δt sigT : ℝ) (sigS : Fin 2 → ℝ)
      (lv : ℕ → FixedLevel (Fin 2) (Fin 2)) (c : FixedLevel (Fin 2) (Fin 2))
      (ψ₀ ψ₁ : Matrix (Fin 2) (Fin 2) ℝ),
      0 < ρmin ∧ S.ρ 0 = ρmin ∧ (∀ i, ρmin ≤ S.ρ i) ∧ 0 < S.Δx ∧ 0 < S.Δy ∧ 0 < Δt ∧
      S.Vxᵀ * S.Vx = 1 ∧ S.Vyᵀ * S.Vy = 1 ∧
      (∀ k, |S.lx k| * Δt / (ρmin * S.Δx) ≤ 1 / 2) ∧
      (∀ k, |S.ly k| * Δt / (ρmin * S.Δy) ≤ 1 / 2) ∧
      0 < sigT ∧ (∀ k, |sigS k| ≤ sigT) ∧ (lv 1).Orth ∧ c.Orth ∧
      (1 + Δt * sigT) * ‖ψ₁‖ ≤ ‖ψ₀‖ ∧
      ‖c.u₀‖ + ∑ ℓ ∈ Finset.Icc 1 1, ‖(lv ℓ).u₀‖ + ‖ψ₀‖ <
        ‖c.collide S Δt sigT sigS (fixedSol S Δt sigT sigS lv ψ₁ 1)‖ +
          ∑ ℓ ∈ Finset.Icc 1 1, ‖fixedSol S Δt sigT sigS lv ψ₁ ℓ‖ + ‖ψ₁‖ := by
  have hl : ∀ k, |(![1, -1] : Fin 2 → ℝ) k| * 1 / (2 * 1) ≤ 1 / 2 := by
    intro k; fin_cases k <;> norm_num
  have hsig : ∀ k, |(![1, 0] : Fin 2 → ℝ) k| ≤ 1 := by intro k; fin_cases k <;> norm_num
  have hz : bugStreamS cexScheme 1 (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simp [bugStreamS, galerkinStart, PNScheme.flux]
  have hsol1 : fixedSol cexScheme 1 1 ![1, 0] (fun _ => cexZeroLevel) 0 1 = 0 := by
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) * scatterS 1 1 ![1, 0]
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) * bugStreamS cexScheme 1 (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) *
        (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 *
      (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 0
    rw [hz]; simp [scatterS, collidedS]
  have e1 : cexCollided.uh cexScheme 1 = cexScheme.euler 1 cexU := by
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) * bugStreamS cexScheme 1 (1 : Matrix (Fin 2) (Fin 2) ℝ)
      cexU (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = _
    simp [bugStreamS, galerkinStart, PNScheme.euler]
  have hcol : cexCollided.collide cexScheme 1 1 ![1, 0] 0 = !![3 / 4, 0; 5 / 4, 0] := by
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) * (collidedS 1 ![1, 0] (cexCollided.uh cexScheme 1)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 *
      (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * resolvent 1 1 ![1, 0]) = _
    rw [e1, cex_euler, resolvent_eq (by norm_num) (fun k => by fin_cases k <;> norm_num)]
    simp only [collidedS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]
    ext i k; fin_cases i <;> fin_cases k <;> simp
  refine ⟨cexScheme, 2, 1, 1, ![1, 0], fun _ => cexZeroLevel, cexCollided, 0, 0, by norm_num,
    rfl, ?_, by simp [cexScheme], by simp [cexScheme], by norm_num, hMat_orth, hMat_orth, hl, hl,
    by norm_num, hsig, cexZeroLevel_orth, cexCollided_orth, by simp, ?_⟩
  · intro i; fin_cases i <;> norm_num [cexScheme]
  · rw [hsol1, hcol]
    have hu : ‖cexCollided.u₀‖ = ‖cexU‖ := by
      change ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * cexU * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ = _
      simp
    have hu1 : ‖cexZeroLevel.u₀‖ = 0 := by
      change ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ) *
        (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ‖ = 0
      simp
    have := cex_norm_lt
    rw [cex_euler] at this
    simp only [hu, Finset.Icc_self, Finset.sum_singleton, hu1, hsol1, norm_zero, add_zero]
    exact this

/-- The hypotheses of the positive results can hold with `Δt > 0`: the scheme of the
counterexamples with constant density `ρ ≡ 2` satisfies the CFL condition of `theorem1`. -/
example : ({ cexScheme with ρ := fun _ => 2 } : PNScheme (Fin 2) (Fin 2)).CFL 2 1 where
  rho_eq _ := rfl
  rho_pos := by norm_num
  Δx_pos := by simp [cexScheme]
  Δy_pos := by simp [cexScheme]
  Δt_nonneg := by norm_num
  Vx_orth := hMat_orth
  Vy_orth := hMat_orth
  cflx k := by fin_cases k <;> simp [cexScheme]
  cfly k := by fin_cases k <;> simp [cexScheme]

end Counterexample

end LeanDLRA.Literature.P2111_07160
