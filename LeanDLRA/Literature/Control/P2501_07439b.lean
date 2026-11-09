import LeanDLRA.Literature.Control.P2501_07439a
import LeanDLRA.Stochastic.KalmanBucy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Results of arXiv 2501.07439 (Saluzzi–Strazzullo): Riccati sensitivity and cascade Newton–Kleinman

The Riccati part of Sections 2–3 and the factor equations of Section 4 of arXiv 2501.07439v2.
The sibling module `Literature/Control/P2501_07439a` proves Appendix A (Propositions A.2, A.4,
Corollary A.3); this module builds on it and on the core.

**Core definitions used.** `LeanDLRA.ODESolution` and the sibling's
`closedLoop_param_sensitivity` (Corollary A.3) and `closedLoop_speed_antitone` (Proposition A.4)
for the trajectories; `LeanDLRA.tangentProj` (Matrix/Projectors) for the factor equations;
`LeanDLRA.KalmanBucy.riccatiField` (Stochastic/KalmanBucy) through the bridge
`riccatiField_eq_riccatiRes`. Matrix norms are Mathlib's operator 2-norm
(`Matrix.Norms.L2Operator`), the paper's norm in Theorem 3.4; positive (semi)definiteness is
Mathlib's `Matrix.PosDef`/`Matrix.PosSemidef`.

**Local definitions** (the core has no control theory): `IsHurwitz` (stable, Definition 2.1, via
Mathlib's `spectrum` of the complexified matrix), `IsStabilizable` (Definition 2.1),
`IsDetectable` (Definition 2.2), `riccatiRes` (the residual (2.7); the core filter field
`KalmanBucy.riccatiField` is the special case `F = ρ I` of the transposed system,
`riccatiField_eq_riccatiRes`), and `colKron` (the column-wise Kronecker square `V_⊗` of
Section 4.2). The paper's `Q^{1/2}` is replaced by any `C` with `Q = Cᵀ C`; detectability of
`(A, C)` depends only on `ker C = ker Q`, so this includes `C = Q^{1/2}`.

**Main results.**
* `riccati_closedLoop_isHurwitz`: a PSD solution of the Riccati equation with `(A, C)` detectable
  is stabilizing (the standard fact behind the paper's use of [34], [19]).
* `IsHurwitz.sylvester_eq_zero`, `IsHurwitz.existsUnique_lyapunov`, `IsHurwitz.lyapunov_posDef`:
  Sylvester uniqueness, unique solvability of (3.7), and `H ≻ 0`, proved through the Cayley
  transform and Gelfand's formula (no matrix exponential).
* `isHurwitz_sub_of_lyapunov`: the Lyapunov robustness step behind Lemma 3.1 of [19].
* `newtonKleinman_tendsto` (Theorem 2.5, Kleinman): the iterates (2.9) from a stabilizing PSD
  guess converge to the unique PSD solution; `exists_newtonKleinman_seq` gives the iterates.
* `riccati_perturbation` (Theorem 3.4) and its stability part `riccati_perturbation_isHurwitz`.
* `cascade_parameter_initial`, `cascade_parameter` (Proposition 3.5), `cascade_time`
  (Proposition 3.7), `cascade_parameter_approx` (Remark 3.6), `cascade_time_approx`
  (Remark 3.8), including the Newton–Kleinman convergence claims of 3.5 and 3.7.
* `factor_eq` (4.5), `factor_eq_tangentProj` (the factor equations give the core tangent
  projection), `colKron_mul` (the step to (4.8)), `dlra_feedback_eq` ((4.7) to (4.12)).
* `riccatiField_stationary_isHurwitz`: stationary Kalman–Bucy covariances (core filter field)
  are stabilizing under detectability.

**Hypotheses.** The paper declares Assumption 3.3(b), (c) standing in Section 3 (p. 7, below
Assumption 3.3, printed as "Assumption 2 (b) and (c)"). Detectability (c) is a hypothesis
wherever it is used, at the states where it is needed (for the existence and uniqueness of the
perturbed solution in Theorem 3.4 also at the perturbed state, which lies in `Ω` in the paper).
Stabilizability (b) is never needed: a stabilizing guess already implies it. The uniqueness of
`P_{μ,t}` assumed in Theorem 3.4 is not needed either (`riccati_posSemidef_unique` proves it).
The SDRE solution map `P(x)` (PSD, solving (2.5) on `Ω`) and the trajectories are data of the
setting, as in the paper. No step of the paper's proofs is taken as a hypothesis.

**The paper is not wrong here.** An earlier draft claimed Theorem 3.4 false with the instance
`A = 1`, `F = 0`, `Q = 0`, `H = -1/2`. That instance violates the standing Assumption 3.3(b), (c)
(`F = B R⁻¹ Bᵀ = 0` forces `B = 0`; `(1, 0)` is not detectable), so it is outside the theorem.
`riccati_perturbation_needs_detectability` keeps it only to show that (c) cannot be dropped.

**Deviations, all in the stronger direction or stated.** Matrices act on `EuclideanSpace ℝ n`
through `Matrix.toEuclideanCLM`; the parameter space is any normed group (the paper restricts
to one dimension, `Δμ = ‖μ - μ̃‖`, with `μ ≠ μ̃`). Assumption 3.3(f) is used with `≤ 0`. In (3.14)
the positivity of `1 - 4 C Δt^p L_A ‖H‖`, implicit in its logarithm, is a hypothesis; in
Remark 3.8 `p` is a natural number and `C ≥ 0`. Fractions such as `1 / (2 ‖H‖)` follow Lean's
convention `1 / 0 = 0`, which only makes a degenerate condition unsatisfiable.

**Notes on the printed text** (not errors in the statements): in Proposition 3.5 "`B P_{μ,t}`"
is a misprint for `F P_{μ,t}`. The proofs of Proposition 3.7 and Remark 3.8 bound
`‖y(t + Δt) - y(t)‖` by `Δt e^{Lt} M_{μ,Δt}` and then use (3.15), which lacks `e^{Lt}`; the
statements are nevertheless true, since by Proposition A.4 the speed is nonincreasing on
`[0, t + Δt]`, which gives the bound `Δt ‖A_cl(y₀) y₀‖` directly (used here). In (4.11) the
right-hand side `Q_r` should read `-Q_r` (compare (2.5)); (4.11) is not formalized.

**Not formalized.** Theorem 2.4 (local asymptotic stability of SDRE feedback, cited from [3]),
the operator-norm identity `‖Ω_P⁻¹‖ = ‖H‖` of [25] (not needed: the robustness step is proved
directly from `H`), the SDRE (4.11) itself, Remark 4.1 and the numerical Sections 5–6.
-/

open Set Filter Topology Finset
open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace LeanDLRA.Literature.P2501_07439

variable {n : Type*} [Fintype n]

/-! ### Definitions 2.1 and 2.2, and the Riccati residual (2.7) -/

/-- **Stable (Hurwitz) matrix** (Definition 2.1 of arXiv 2501.07439): every eigenvalue of the
real matrix `M`, i.e. every point of the spectrum of `M` viewed over `ℂ`, has negative real
part. -/
def IsHurwitz [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∀ z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), z.re < 0

/-- **Stabilizable pair** (Definition 2.1 of arXiv 2501.07439): some feedback `K` makes
`A - B K` stable. -/
def IsStabilizable [DecidableEq n] {m : Type*} [Fintype m] (A : Matrix n n ℝ)
    (B : Matrix n m ℝ) : Prop :=
  ∃ K : Matrix m n ℝ, IsHurwitz (A - B * K)

/-- **Detectable pair** (Definition 2.2 of arXiv 2501.07439): `(A, C)` is detectable if
`(Aᵀ, Cᵀ)` is stabilizable. The paper takes `C` square; any number of rows is allowed here. -/
def IsDetectable [DecidableEq n] {k : Type*} [Fintype k] (A : Matrix n n ℝ)
    (C : Matrix k n ℝ) : Prop :=
  IsStabilizable Aᵀ Cᵀ

/-- The residual (2.7) of the (state-dependent) Riccati equation:
`R(P) = Aᵀ P + P A - P F P + Q`, with `F = B R⁻¹ Bᵀ` in the paper. -/
def riccatiRes (A F Q P : Matrix n n ℝ) : Matrix n n ℝ :=
  Aᵀ * P + P * A - P * F * P + Q

/-! ### Eigenvalues, real pairs and the Lyapunov criterion -/

/-- A point of the spectrum of a complex matrix is an eigenvalue. -/
theorem mem_spectrum_iff_exists_mulVec [DecidableEq n] {M : Matrix n n ℂ} {z : ℂ} :
    z ∈ spectrum ℂ M ↔ ∃ v : n → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero, eq_comm]

/-- Real part of the complexified matrix-vector product. -/
theorem re_mulVec {m : Type*} (M : Matrix m n ℝ) (v : n → ℂ) (i : m) :
    ((M.map (algebraMap ℝ ℂ) *ᵥ v) i).re = (M *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

/-- Imaginary part of the complexified matrix-vector product. -/
theorem im_mulVec {m : Type*} (M : Matrix m n ℝ) (v : n → ℂ) (i : m) :
    ((M.map (algebraMap ℝ ℂ) *ᵥ v) i).im = (M *ᵥ fun j => (v j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- A complex eigenpair `(a + i b, x + i y)` of a real matrix as a pair of real equations. -/
theorem pair_of_eigen {M : Matrix n n ℝ} {v : n → ℂ} {z : ℂ}
    (h : M.map (algebraMap ℝ ℂ) *ᵥ v = z • v) :
    M *ᵥ (fun j => (v j).re) = z.re • (fun j => (v j).re) - z.im • (fun j => (v j).im) ∧
      M *ᵥ (fun j => (v j).im) = z.im • (fun j => (v j).re) + z.re • (fun j => (v j).im) := by
  constructor <;> ext i <;> have h1 := congrFun h i
  · have h2 := congrArg Complex.re h1
    rw [re_mulVec] at h2
    simpa [Complex.mul_re] using h2
  · have h2 := congrArg Complex.im h1
    rw [im_mulVec] at h2
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im] at h2
    simp only [h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Conversely, real equations for `x`, `y` give a complex eigenpair `(a + i b, x + i y)`. -/
theorem eigen_of_pair {M : Matrix n n ℝ} {x y : n → ℝ} {a b : ℝ}
    (hx : M *ᵥ x = a • x - b • y) (hy : M *ᵥ y = b • x + a • y) :
    M.map (algebraMap ℝ ℂ) *ᵥ (fun j => (⟨x j, y j⟩ : ℂ)) =
      (⟨a, b⟩ : ℂ) • (fun j => (⟨x j, y j⟩ : ℂ)) := by
  ext i
  apply Complex.ext
  · rw [re_mulVec]
    simpa [Complex.mul_re] using congrFun hx i
  · rw [im_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im]
    have := congrFun hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [this]
    ring

/-- `xᵀ (Mᵀ H + H M) x = (M x)ᵀ H x + xᵀ H (M x)`. -/
theorem quad_lyap (M H : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Mᵀ * H + H * M) *ᵥ x) = (M *ᵥ x) ⬝ᵥ (H *ᵥ x) + x ⬝ᵥ (H *ᵥ (M *ᵥ x)) := by
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x Mᵀ, Matrix.vecMul_transpose]

/-- On a real eigenpair, the Lyapunov form is `2 a` times the `H`-form. -/
theorem quad_pair {M H : Matrix n n ℝ} {x y : n → ℝ} {a b : ℝ}
    (hx : M *ᵥ x = a • x - b • y) (hy : M *ᵥ y = b • x + a • y) :
    x ⬝ᵥ ((Mᵀ * H + H * M) *ᵥ x) + y ⬝ᵥ ((Mᵀ * H + H * M) *ᵥ y) =
      2 * a * (x ⬝ᵥ (H *ᵥ x) + y ⬝ᵥ (H *ᵥ y)) := by
  rw [quad_lyap, quad_lyap, hx, hy]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, sub_dotProduct,
    add_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

section Dec

variable [DecidableEq n]

/-- Every eigenvalue of a real matrix comes with a nonzero real pair `(x, y)`. -/
theorem exists_pair {M : Matrix n n ℝ} {z : ℂ} (hz : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ))) :
    ∃ x y : n → ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ M *ᵥ x = z.re • x - z.im • y ∧
      M *ᵥ y = z.im • x + z.re • y := by
  obtain ⟨v, hv, hMv⟩ := mem_spectrum_iff_exists_mulVec.1 hz
  refine ⟨_, _, ?_, pair_of_eigen hMv⟩
  by_contra h
  push Not at h
  apply hv
  ext j
  apply Complex.ext
  · simpa using congrFun h.1 j
  · simpa using congrFun h.2 j

/-- **Lyapunov criterion.** If `H` is positive on nonzero vectors and `Mᵀ H + H M` is negative
on nonzero vectors, then `M` is stable. -/
theorem isHurwitz_of_lyapunov {M H : Matrix n n ℝ}
    (hH : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (H *ᵥ x))
    (hM : ∀ x : n → ℝ, x ≠ 0 → x ⬝ᵥ ((Mᵀ * H + H * M) *ᵥ x) < 0) : IsHurwitz M := by
  intro z hz
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair hz
  have key := quad_pair (H := H) hx hy
  have qH : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ (H *ᵥ u) := fun u => by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (hH u hu).le
  have qM : ∀ u : n → ℝ, u ⬝ᵥ ((Mᵀ * H + H * M) *ᵥ u) ≤ 0 := fun u => by
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (hM u hu).le
  rcases hxy with h | h
  · nlinarith [hH x h, hM x h, qH y, qM y]
  · nlinarith [hH y h, hM y h, qH x, qM x]

/-! ### Hurwitz matrices: Cayley transform, Sylvester and Lyapunov equations -/

/-- A stable matrix has no eigenvalue `1`, so `1 - N` is invertible. -/
theorem IsHurwitz.det_one_sub_ne_zero {N : Matrix n n ℝ} (hN : IsHurwitz N) :
    (1 - N).det ≠ 0 := by
  intro h
  obtain ⟨x, hx, hNx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hmem : (1 : ℂ) ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)) := by
    refine mem_spectrum_iff_exists_mulVec.2 ⟨(algebraMap ℝ ℂ) ∘ x, fun h0 => hx ?_, ?_⟩
    · ext j
      simpa using congrFun h0 j
    · ext i
      have h1 : x i = (N *ᵥ x) i := by
        have := congrFun hNx i
        simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply] at this
        linarith
      rw [← RingHom.map_mulVec, ← h1, one_smul]
      rfl
  exact absurd (hN 1 hmem) (by norm_num)

/-- Spectrum of the Cayley transform lies in the open unit disc. -/
theorem norm_lt_one_of_cayley {N T : Matrix n n ℝ} (hN : IsHurwitz N) (hT : (1 - N) * T = 1 + N)
    {z : ℂ} (hz : z ∈ spectrum ℂ (T.map (algebraMap ℝ ℂ))) : ‖z‖ < 1 := by
  obtain ⟨w, hw, hTw⟩ := mem_spectrum_iff_exists_mulVec.1 hz
  set Nc := N.map (algebraMap ℝ ℂ)
  have hTc : (1 - Nc) * T.map (algebraMap ℝ ℂ) = 1 + Nc := by
    have := congrArg (algebraMap ℝ ℂ).mapMatrix hT
    simp only [map_mul, map_sub, map_add, map_one] at this
    simpa [Nc, RingHom.mapMatrix_apply] using this
  have h1 : z • w - z • (Nc *ᵥ w) = w + Nc *ᵥ w := by
    have := congrArg (fun M => M *ᵥ w) hTc
    simp only [← Matrix.mulVec_mulVec, hTw, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_sub] at this
    exact this
  have hz1 : z + 1 ≠ 0 := by
    intro hz1
    have hz' : z = -1 := by linear_combination hz1
    rw [hz'] at h1
    apply hw
    have : (2 : ℂ) • w = 0 := by
      have := h1
      rw [neg_smul, neg_smul, one_smul, one_smul] at this
      linear_combination (norm := module) -this
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have hev : Nc *ᵥ w = ((z - 1) / (z + 1)) • w := by
    have h2 : (z + 1) • (Nc *ᵥ w) = (z - 1) • w := by
      linear_combination (norm := module) -h1
    rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hz1, one_smul]
  have hre := hN _ (mem_spectrum_iff_exists_mulVec.2 ⟨w, hw, hev⟩)
  rw [Complex.div_re] at hre
  have hpos : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.2 hz1
  have hnum : (z - 1).re * (z + 1).re + (z - 1).im * (z + 1).im < 0 := by
    rw [← add_div, div_neg_iff] at hre
    rcases hre with ⟨_, h⟩ | ⟨h, _⟩
    · exact absurd h (not_lt.2 hpos.le)
    · exact h
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im,
    Complex.add_im, sub_zero, add_zero] at hnum
  have hsq : ‖z‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z]

/-- Powers of the Cayley transform of a Hurwitz matrix tend to zero. -/
theorem tendsto_pow_cayley {N T : Matrix n n ℝ} (hN : IsHurwitz N) (hT : (1 - N) * T = 1 + N) :
    Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact tendsto_const_nhds.congr fun k => Subsingleton.elim _ _
  set Tc := T.map (algebraMap ℝ ℂ)
  have hsr : spectralRadius ℂ Tc < 1 := by
    have := spectrum.spectralRadius_lt_of_forall_lt Tc (r := 1) fun z hz => by
      have := norm_lt_one_of_cayley hN hT hz
      exact_mod_cast this
    simpa using this
  rw [spectrum.spectralRadius_eq_gelfandRadius, ENNReal.ofReal_lt_one] at hsr
  obtain ⟨C, hC, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt Tc
    (r := (gelfandRadius Tc + 1) / 2) (by linarith)
  have hr0 : 0 ≤ (gelfandRadius Tc + 1) / 2 := by positivity
  have hr1 : (gelfandRadius Tc + 1) / 2 < 1 := by linarith
  have hc : Tendsto (fun k : ℕ => Tc ^ k) atTop (𝓝 0) := by
    refine squeeze_zero_norm hb ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  have hmap : ∀ k : ℕ, Tc ^ k = (T ^ k).map (algebraMap ℝ ℂ) := fun k => by
    simp only [Tc, ← RingHom.mapMatrix_apply, map_pow]
  have hc' := (tendsto_pi_nhds (A := fun _ : n => n → ℂ)).1 hc
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hci := (tendsto_pi_nhds (A := fun _ : n => ℂ)).1 (hc' i) j
  have := (Complex.continuous_re.tendsto _).comp hci
  simpa [Function.comp_def, hmap] using this


/-- Cayley transform `T = (1 + N)(1 - N)⁻¹` of a stable `N`: its powers tend to zero (Gelfand's
formula, since its spectrum lies in the open unit disc). -/
theorem IsHurwitz.cayley {N : Matrix n n ℝ} (hN : IsHurwitz N) :
    ∃ S T : Matrix n n ℝ, (1 - N) * S = 1 ∧ T = (1 + N) * S ∧
      Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 0) := by
  have hdet : IsUnit (1 - N).det := isUnit_iff_ne_zero.2 hN.det_one_sub_ne_zero
  refine ⟨(1 - N)⁻¹, (1 + N) * (1 - N)⁻¹, Matrix.mul_nonsing_inv _ hdet, rfl,
    tendsto_pow_cayley hN ?_⟩
  have hc : (1 - N) * (1 + N) = (1 + N) * (1 - N) := by noncomm_ring
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

omit [DecidableEq n] in
/-- `xᵀ (Tᵀ H T) x = (T x)ᵀ H (T x)`. -/
theorem quad_conj (T H : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Tᵀ * H * T) *ᵥ x) = (T *ᵥ x) ⬝ᵥ (H *ᵥ (T *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Cayley identity: `(1 + N₁)ᵀ D (1 + N₂) - (1 - N₁)ᵀ D (1 - N₂) = 2 (N₁ᵀ D + D N₂)`. -/
theorem cayley_expand (N₁ N₂ D : Matrix n n ℝ) :
    (1 + N₁)ᵀ * D * (1 + N₂) - (1 - N₁)ᵀ * D * (1 - N₂) = (2 : ℝ) • (N₁ᵀ * D + D * N₂) := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, two_smul]
  noncomm_ring

/-- **Sylvester uniqueness.** If `N₁`, `N₂` are stable and `N₁ᵀ D + D N₂ = 0`, then `D = 0`. -/
theorem IsHurwitz.sylvester_eq_zero {N₁ N₂ D : Matrix n n ℝ} (h₁ : IsHurwitz N₁)
    (h₂ : IsHurwitz N₂) (h : N₁ᵀ * D + D * N₂ = 0) : D = 0 := by
  obtain ⟨S₁, T₁, hS₁, hT₁d, hT₁⟩ := h₁.cayley
  obtain ⟨S₂, T₂, hS₂, hT₂d, hT₂⟩ := h₂.cayley
  have hexp : (1 + N₁)ᵀ * D * (1 + N₂) = (1 - N₁)ᵀ * D * (1 - N₂) := by
    have := cayley_expand N₁ N₂ D
    rw [h, smul_zero] at this
    exact sub_eq_zero.1 this
  have hstep : T₁ᵀ * D * T₂ = D := by
    calc T₁ᵀ * D * T₂ = S₁ᵀ * ((1 + N₁)ᵀ * D * (1 + N₂)) * S₂ := by
          simp only [hT₁d, hT₂d, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = S₁ᵀ * ((1 - N₁)ᵀ * D * (1 - N₂)) * S₂ := by rw [hexp]
      _ = ((1 - N₁) * S₁)ᵀ * D * ((1 - N₂) * S₂) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = D := by rw [hS₁, hS₂, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hk : ∀ k : ℕ, (T₁ ^ k)ᵀ * D * T₂ ^ k = D := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (T₁ ^ (k + 1))ᵀ * D * T₂ ^ (k + 1) = (T₁ ^ k)ᵀ * (T₁ᵀ * D * T₂) * T₂ ^ k := by
            rw [pow_succ' T₁, pow_succ' T₂, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = D := by rw [hstep, ih]
  have hlim : Tendsto (fun k : ℕ => (T₁ ^ k)ᵀ * D * T₂ ^ k) atTop
      (𝓝 ((0 : Matrix n n ℝ)ᵀ * D * 0)) :=
    ((((continuous_id.matrix_transpose).tendsto _).comp hT₁).mul_const D).mul hT₂
  simp only [hk, Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- Lyapunov inequality: `xᵀ H x ≥ 2 (S x)ᵀ W (S x)` with `S = (1 - N)⁻¹`. -/
theorem IsHurwitz.lyapunov_quad_ge {N H W : Matrix n n ℝ} (hN : IsHurwitz N)
    (hW : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ (W *ᵥ u)) (h : Nᵀ * H + H * N = -W) :
    ∃ S : Matrix n n ℝ, (1 - N) * S = 1 ∧
      ∀ x : n → ℝ, 2 * ((S *ᵥ x) ⬝ᵥ (W *ᵥ (S *ᵥ x))) ≤ x ⬝ᵥ (H *ᵥ x) := by
  obtain ⟨S, T, hS, hTd, hT⟩ := hN.cayley
  refine ⟨S, hS, fun x => ?_⟩
  have hexp := cayley_expand N N H
  rw [h] at hexp
  have hH : H = Sᵀ * ((1 - N)ᵀ * H * (1 - N)) * S := by
    calc H = ((1 - N) * S)ᵀ * H * ((1 - N) * S) := by
          rw [hS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hid : Tᵀ * H * T = H - (2 : ℝ) • (Sᵀ * W * S) := by
    have e1 : (1 + N)ᵀ * H * (1 + N) = (1 - N)ᵀ * H * (1 - N) + (2 : ℝ) • -W := by
      rw [← hexp]; abel
    calc Tᵀ * H * T = Sᵀ * ((1 + N)ᵀ * H * (1 + N)) * S := by
          rw [hTd]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Sᵀ * ((1 - N)ᵀ * H * (1 - N)) * S + Sᵀ * ((2 : ℝ) • -W) * S := by
          rw [e1, Matrix.mul_add, Matrix.add_mul]
      _ = H - (2 : ℝ) • (Sᵀ * W * S) := by
          rw [← hH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg,
            sub_eq_add_neg]
  set q : (n → ℝ) → ℝ := fun u => u ⬝ᵥ (H *ᵥ u) with hqdef
  have hq : ∀ u, q (T *ᵥ u) = q u - 2 * ((S *ᵥ u) ⬝ᵥ (W *ᵥ (S *ᵥ u))) := fun u => by
    have e := congrArg (fun M => u ⬝ᵥ (M *ᵥ u)) hid
    simp only [quad_conj, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at e
    simpa [hqdef] using e
  have hanti : Antitone (fun k : ℕ => q ((T ^ k) *ᵥ x)) := antitone_nat_of_succ_le fun k => by
    rw [pow_succ', ← Matrix.mulVec_mulVec, hq]
    linarith [hW (S *ᵥ ((T ^ k) *ᵥ x))]
  have hlim : Tendsto (fun k : ℕ => q ((T ^ k) *ᵥ x)) atTop (𝓝 0) := by
    have hc : Continuous fun M : Matrix n n ℝ => q (M *ᵥ x) := by
      simp only [hqdef]
      exact (continuous_id.matrix_mulVec continuous_const).dotProduct
        (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))
    have h0 : q ((0 : Matrix n n ℝ) *ᵥ x) = 0 := by simp [hqdef]
    have := (hc.tendsto 0).comp hT
    rw [h0] at this
    exact this
  have h1 := hanti.le_of_tendsto hlim 1
  simp only [pow_one] at h1
  rw [hq] at h1
  linarith

/-- The solution of a Lyapunov equation with right-hand side `-1` for a Hurwitz matrix is
symmetric positive definite. -/
theorem IsHurwitz.lyapunov_posDef {N H : Matrix n n ℝ} (hN : IsHurwitz N)
    (h : Nᵀ * H + H * N = -1) : H.PosDef := by
  have hsymm : Hᵀ = H := by
    have ht : Nᵀ * Hᵀ + Hᵀ * N = -1 := by
      have := congrArg Matrix.transpose h
      simpa [Matrix.transpose_add, Matrix.transpose_mul, add_comm] using this
    have : Nᵀ * (Hᵀ - H) + (Hᵀ - H) * N = 0 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_comm, ht, h, sub_self]
    exact sub_eq_zero.1 (hN.sylvester_eq_zero hN this)
  obtain ⟨S, hS, hq⟩ := hN.lyapunov_quad_ge (W := 1)
    (fun u => by simpa using dotProduct_self_star_nonneg u) h
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hsymm]
  · have hSx : S *ᵥ x ≠ 0 := fun h0 => hx (by
      have := congrArg (fun v => (1 - N) *ᵥ v) h0
      simpa [Matrix.mulVec_mulVec, hS] using this)
    have hpos : 0 < (S *ᵥ x) ⬝ᵥ (S *ᵥ x) := by
      rcases (dotProduct_self_star_nonneg (S *ᵥ x)).lt_or_eq with h' | h'
      · simpa using h'
      · exact absurd (dotProduct_self_eq_zero.1 (by simpa using h'.symm)) hSx
    have := hq x
    simp only [Matrix.one_mulVec] at this
    simp only [star_trivial]
    linarith

/-- The Lyapunov equation `Nᵀ H + H N = W` of a Hurwitz matrix has exactly one solution. -/
theorem IsHurwitz.existsUnique_lyapunov {N : Matrix n n ℝ} (hN : IsHurwitz N)
    (W : Matrix n n ℝ) : ∃! H : Matrix n n ℝ, Nᵀ * H + H * N = W := by
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ := LinearMap.mulLeft ℝ Nᵀ + LinearMap.mulRight ℝ N
  have hL : ∀ X, L X = Nᵀ * X + X * N := fun X => rfl
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    exact fun X hX => hN.sylvester_eq_zero hN (by rw [← hL]; exact hX)
  obtain ⟨H, hH⟩ := LinearMap.injective_iff_surjective.1 hinj W
  refine ⟨H, (hL H).symm.trans hH, fun H' hH' => hinj ?_⟩
  exact ((hL H').trans hH').trans hH.symm

/-- `|uᵀ A w| ≤ ‖A‖ ‖u‖ ‖w‖` with the operator 2-norm and Euclidean vector norms. -/
theorem abs_dotProduct_mulVec_le (A : Matrix n n ℝ) (u w : n → ℝ) :
    |u ⬝ᵥ (A *ᵥ w)| ≤ ‖A‖ * (‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 w‖) := by
  have h1 : u ⬝ᵥ (A *ᵥ w) = inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 (A *ᵥ w)) := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have h2 : ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 w‖ :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 w)
  rw [h1]
  calc _ ≤ ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 (A *ᵥ w)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 u‖ * (‖A‖ * ‖WithLp.toLp 2 w‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := by ring

/-- `‖A w‖ ≤ ‖A‖ ‖w‖` for the operator 2-norm. -/
theorem norm_toLp_mulVec_le (A : Matrix n n ℝ) (w : n → ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 w‖ :=
  Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 w)

omit [DecidableEq n] in
/-- The squared Euclidean norm is the dot product. -/
theorem norm_toLp_sq (u : n → ℝ) : ‖WithLp.toLp 2 u‖ ^ 2 = u ⬝ᵥ u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- **Lyapunov robustness** (the stability step of Theorem 3.4, Lemma 3.1 of Gahinet–Laub).
If `H` is positive definite with `Nᵀ H + H N = -I` and `‖Δ‖ < 1 / (2 ‖H‖)`, then `N - Δ` is
Hurwitz. -/
theorem isHurwitz_sub_of_lyapunov {N H Δ : Matrix n n ℝ}
    (hH : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (H *ᵥ x)) (hL : Nᵀ * H + H * N = -1)
    (hΔ : ‖Δ‖ < 1 / (2 * ‖H‖)) : IsHurwitz (N - Δ) := by
  have hHpos : 0 < ‖H‖ := by
    rcases (norm_nonneg H).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero, div_zero] at hΔ
      exact absurd hΔ (not_lt.2 (norm_nonneg _))
  have hk : ‖Δ‖ * (2 * ‖H‖) < 1 := (lt_div_iff₀ (by positivity)).1 hΔ
  refine isHurwitz_of_lyapunov hH fun x hx => ?_
  have e : (N - Δ)ᵀ * H + H * (N - Δ) = -1 - (Δᵀ * H + H * Δ) := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, ← hL]
    abel
  rw [e, Matrix.sub_mulVec, dotProduct_sub, quad_lyap, Matrix.neg_mulVec, Matrix.one_mulVec,
    dotProduct_neg]
  set nx := ‖WithLp.toLp 2 x‖
  have hnx : 0 < nx ^ 2 := by
    rw [norm_toLp_sq]
    rcases (dotProduct_self_star_nonneg x).lt_or_eq with h' | h'
    · simpa using h'
    · exact absurd (dotProduct_self_eq_zero.1 (by simpa using h'.symm)) hx
  have hΔx := norm_toLp_mulVec_le Δ x
  have t1 := abs_dotProduct_mulVec_le H (Δ *ᵥ x) x
  have t2 := abs_dotProduct_mulVec_le H x (Δ *ᵥ x)
  have hb : ‖H‖ * (‖WithLp.toLp 2 (Δ *ᵥ x)‖ * nx) ≤ ‖H‖ * (‖Δ‖ * nx * nx) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΔx (norm_nonneg _)) hHpos.le
  have hb' : ‖H‖ * (nx * ‖WithLp.toLp 2 (Δ *ᵥ x)‖) ≤ ‖H‖ * (‖Δ‖ * nx * nx) := by
    rw [mul_comm nx]; exact hb
  rw [← norm_toLp_sq]
  have := neg_abs_le ((Δ *ᵥ x) ⬝ᵥ (H *ᵥ x))
  have := neg_abs_le (x ⬝ᵥ (H *ᵥ (Δ *ᵥ x)))
  nlinarith

/-- Detectability (Definition 2.2) excludes unobservable modes with nonnegative real part:
if `x + i y ≠ 0` is an eigenvector of `A` for `a + i b` with `C x = C y = 0`, then `a < 0`. -/
theorem IsDetectable.re_neg {k : Type*} [Fintype k] {A : Matrix n n ℝ} {C : Matrix k n ℝ}
    (hd : IsDetectable A C) {x y : n → ℝ} {a b : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0)
    (hx : A *ᵥ x = a • x - b • y) (hy : A *ᵥ y = b • x + a • y) (hCx : C *ᵥ x = 0)
    (hCy : C *ᵥ y = 0) : a < 0 := by
  obtain ⟨K, hK⟩ := hd
  have hx' : (Aᵀ - Cᵀ * K)ᵀ *ᵥ x = a • x - b • y := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hCx,
      Matrix.mulVec_zero, sub_zero, hx]
  have hy' : (Aᵀ - Cᵀ * K)ᵀ *ᵥ y = b • x + a • y := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hCy,
      Matrix.mulVec_zero, sub_zero, hy]
  have hmem : (⟨a, b⟩ : ℂ) ∈ spectrum ℂ ((Aᵀ - Cᵀ * K).map (algebraMap ℝ ℂ)) := by
    rw [← Matrix.spectrum_transpose, ← Matrix.transpose_map]
    refine mem_spectrum_iff_exists_mulVec.2 ⟨_, ?_, eigen_of_pair hx' hy'⟩
    intro h0
    rcases hxy with h | h
    · exact h (funext fun j => by simpa using congrArg Complex.re (congrFun h0 j))
    · exact h (funext fun j => by simpa using congrArg Complex.im (congrFun h0 j))
  exact hK _ hmem

/-- **Stabilizing solutions via detectability.** If `(A - G)ᵀ X + X (A - G) = -W` with `X` and
`W` positive semidefinite, and `uᵀ W u = 0` forces `C u = 0` and `G u = 0`, then detectability of
`(A, C)` makes `A - G` Hurwitz. -/
theorem isHurwitz_of_lyapunov_detectable {k : Type*} [Fintype k] {A G X W : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hd : IsDetectable A C) (hX : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ (X *ᵥ u))
    (hW : ∀ u : n → ℝ, 0 ≤ u ⬝ᵥ (W *ᵥ u))
    (hW0 : ∀ u : n → ℝ, u ⬝ᵥ (W *ᵥ u) = 0 → C *ᵥ u = 0 ∧ G *ᵥ u = 0)
    (h : (A - G)ᵀ * X + X * (A - G) = -W) : IsHurwitz (A - G) := by
  intro z hz
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair hz
  by_contra ha
  push Not at ha
  have key := quad_pair (H := X) hx hy
  rw [h, Matrix.neg_mulVec, Matrix.neg_mulVec, dotProduct_neg, dotProduct_neg] at key
  have hWx : x ⬝ᵥ (W *ᵥ x) = 0 := by nlinarith [hW x, hW y, hX x, hX y]
  have hWy : y ⬝ᵥ (W *ᵥ y) = 0 := by nlinarith [hW x, hW y, hX x, hX y]
  obtain ⟨hCx, hGx⟩ := hW0 x hWx
  obtain ⟨hCy, hGy⟩ := hW0 y hWy
  have hAx : A *ᵥ x = z.re • x - z.im • y := by
    rw [← hx, Matrix.sub_mulVec, hGx, sub_zero]
  have hAy : A *ᵥ y = z.im • x + z.re • y := by
    rw [← hy, Matrix.sub_mulVec, hGy, sub_zero]
  exact absurd (hd.re_neg hxy hAx hAy hCx hCy) (not_lt.2 ha)

omit [DecidableEq n] in
/-- For a real positive semidefinite matrix, `uᵀ M u = 0` implies `M u = 0`. -/
theorem posSemidef_mulVec_eq_zero {M : Matrix n n ℝ} (hM : M.PosSemidef) {u : n → ℝ}
    (h : u ⬝ᵥ (M *ᵥ u) = 0) : M *ᵥ u = 0 :=
  hM.dotProduct_mulVec_zero_iff.1 (by simpa using h)

omit [DecidableEq n] in
/-- A real positive semidefinite matrix has a nonnegative quadratic form. -/
theorem posSemidef_quad_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) (u : n → ℝ) :
    0 ≤ u ⬝ᵥ (M *ᵥ u) := by
  simpa using hM.dotProduct_mulVec_nonneg u

omit [Fintype n] [DecidableEq n] in
/-- A real positive semidefinite matrix is symmetric. -/
theorem posSemidef_transpose_eq {M : Matrix n n ℝ} (hM : M.PosSemidef) : Mᵀ = M := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hM.1

omit [DecidableEq n] in
/-- The closed-loop identity: `(A - F P)ᵀ P + P (A - F P) = -(Q + P F P)` when `P` solves the
Riccati equation and `P`, `F` are symmetric. -/
theorem closedLoop_lyapunov {A F Q P : Matrix n n ℝ} (hP : Pᵀ = P) (hF : Fᵀ = F)
    (hric : riccatiRes A F Q P = 0) :
    (A - F * P)ᵀ * P + P * (A - F * P) = -(Q + P * F * P) := by
  have e : (A - F * P)ᵀ * P + P * (A - F * P) + (Q + P * F * P) = riccatiRes A F Q P := by
    rw [riccatiRes, Matrix.transpose_sub, Matrix.transpose_mul, hP, hF]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [hric] at e
  exact eq_neg_of_add_eq_zero_left e

/-- **A PSD solution of the Riccati equation is stabilizing under detectability.** If
`F ⪰ 0`, `Q = Cᵀ C`, `(A, C)` is detectable and `P ⪰ 0` solves `Aᵀ P + P A - P F P + Q = 0`,
then `A - F P` is Hurwitz. -/
theorem riccati_closedLoop_isHurwitz {k : Type*} [Fintype k] {A F Q P : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hP : P.PosSemidef) (hric : riccatiRes A F Q P = 0) : IsHurwitz (A - F * P) := by
  have hl := closedLoop_lyapunov (posSemidef_transpose_eq hP) (posSemidef_transpose_eq hF) hric
  have hQq : ∀ u : n → ℝ, u ⬝ᵥ (Q *ᵥ u) = (C *ᵥ u) ⬝ᵥ (C *ᵥ u) := fun u => by
    rw [hQ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hPFP : ∀ u : n → ℝ, u ⬝ᵥ ((P * F * P) *ᵥ u) = (P *ᵥ u) ⬝ᵥ (F *ᵥ (P *ᵥ u)) := fun u => by
    have := quad_conj P F u
    rwa [(posSemidef_transpose_eq hP)] at this
  refine isHurwitz_of_lyapunov_detectable hd (posSemidef_quad_nonneg hP) (W := Q + P * F * P)
    (fun u => ?_) (fun u hu => ?_) hl
  · rw [Matrix.add_mulVec, dotProduct_add, hQq, hPFP]
    exact add_nonneg (by simpa using dotProduct_self_star_nonneg (C *ᵥ u))
      ((posSemidef_quad_nonneg hF) _)
  · rw [Matrix.add_mulVec, dotProduct_add, hQq, hPFP] at hu
    have h1 := (posSemidef_quad_nonneg hF) (P *ᵥ u)
    have h2 : 0 ≤ (C *ᵥ u) ⬝ᵥ (C *ᵥ u) := by simpa using dotProduct_self_star_nonneg (C *ᵥ u)
    refine ⟨dotProduct_self_eq_zero.1 (by linarith), ?_⟩
    rw [← Matrix.mulVec_mulVec]
    exact (posSemidef_mulVec_eq_zero hF) (by linarith)

/-- The Lyapunov solution for a symmetric right-hand side is symmetric. -/
theorem IsHurwitz.lyapunov_symm {N X W : Matrix n n ℝ} (hN : IsHurwitz N) (hW : Wᵀ = W)
    (h : Nᵀ * X + X * N = W) : Xᵀ = X := by
  have ht : Nᵀ * Xᵀ + Xᵀ * N = W := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hW, add_comm] at this
  have : Nᵀ * (Xᵀ - X) + (Xᵀ - X) * N = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_comm, ht, h, sub_self]
  exact sub_eq_zero.1 (hN.sylvester_eq_zero hN this)

/-- A Lyapunov solution with positive semidefinite forcing is positive semidefinite. -/
theorem IsHurwitz.lyapunov_posSemidef {N X W : Matrix n n ℝ} (hN : IsHurwitz N)
    (hW : W.PosSemidef) (h : Nᵀ * X + X * N = -W) : X.PosSemidef := by
  have hXs : Xᵀ = X := hN.lyapunov_symm (W := -W)
    (by rw [Matrix.transpose_neg, (posSemidef_transpose_eq hW)]) h
  obtain ⟨S, -, hq⟩ := hN.lyapunov_quad_ge (posSemidef_quad_nonneg hW) h
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hXs]
  · simp only [star_trivial]
    linarith [hq x, (posSemidef_quad_nonneg hW) (S *ᵥ x)]

/-- Two positive semidefinite solutions of the Riccati equation with `(A, C)` detectable are
equal (uniqueness part of the standard theory, used in Theorems 2.5 and 3.4). -/
theorem riccati_posSemidef_unique {k : Type*} [Fintype k] {A F Q X Y : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hX : X.PosSemidef) (hXr : riccatiRes A F Q X = 0) (hY : Y.PosSemidef)
    (hYr : riccatiRes A F Q Y = 0) : X = Y := by
  have h1 := riccati_closedLoop_isHurwitz hF hQ hd hX hXr
  have h2 := riccati_closedLoop_isHurwitz hF hQ hd hY hYr
  have e : (A - F * X)ᵀ * (X - Y) + (X - Y) * (A - F * Y) =
      riccatiRes A F Q X - riccatiRes A F Q Y := by
    rw [riccatiRes, riccatiRes, Matrix.transpose_sub, Matrix.transpose_mul,
      posSemidef_transpose_eq hX, posSemidef_transpose_eq hF]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [hXr, hYr, sub_zero] at e
  exact sub_eq_zero.1 (h1.sylvester_eq_zero h2 e)

omit [DecidableEq n] in
/-- The Newton–Kleinman identity: if `X'` solves the Lyapunov step (2.9) from `X`, then
`(A - F X')ᵀ X' + X' (A - F X') = -(Q + X' F X' + (X' - X) F (X' - X))`. -/
theorem newtonKleinman_identity {A F Q X X' : Matrix n n ℝ} (hF : Fᵀ = F) (hX : Xᵀ = X)
    (hX' : X'ᵀ = X') (h : (A - F * X)ᵀ * X' + X' * (A - F * X) = -(X * F * X) - Q) :
    (A - F * X')ᵀ * X' + X' * (A - F * X') =
      -(Q + X' * F * X' + (X' - X) * F * (X' - X)) := by
  classical
  have e : (A - F * X')ᵀ * X' + X' * (A - F * X') + (Q + X' * F * X' + (X' - X) * F * (X' - X))
      = (A - F * X)ᵀ * X' + X' * (A - F * X) + (X * F * X + Q) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, hF, hX, hX']
    noncomm_ring
  rw [h] at e
  have : -(X * F * X) - Q + (X * F * X + Q) = 0 := by abel
  rw [this] at e
  exact eq_neg_of_add_eq_zero_left e

/-- **One Newton–Kleinman step** (2.9): from a stabilizing `X ⪰ 0`, the Lyapunov equation has a
solution `X' ⪰ 0`, and `X'` is again stabilizing when `(A, C)` is detectable. -/
theorem newtonKleinman_step {k : Type*} [Fintype k] {A F Q X : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hX : X.PosSemidef) (hs : IsHurwitz (A - F * X)) :
    ∃ X' : Matrix n n ℝ, X'.PosSemidef ∧ IsHurwitz (A - F * X') ∧
      (A - F * X)ᵀ * X' + X' * (A - F * X) = -(X * F * X) - Q := by
  have hQpsd : Q.PosSemidef := by
    rw [hQ]
    simpa using Matrix.posSemidef_conjTranspose_mul_self C
  have hXFX : (X * F * X).PosSemidef := by
    have := hF.conjTranspose_mul_mul_same X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, (posSemidef_transpose_eq hX)] at this
  obtain ⟨X', hX'eq, -⟩ := hs.existsUnique_lyapunov (-(X * F * X) - Q)
  have hW : (X * F * X + Q).PosSemidef := hXFX.add hQpsd
  have hX'psd : X'.PosSemidef := hs.lyapunov_posSemidef hW (by rw [hX'eq]; abel)
  refine ⟨X', hX'psd, ?_, hX'eq⟩
  have hid := newtonKleinman_identity (posSemidef_transpose_eq hF) (posSemidef_transpose_eq hX)
    (posSemidef_transpose_eq hX'psd) hX'eq
  have hDs : (X' - X)ᵀ = X' - X := by
    rw [Matrix.transpose_sub, (posSemidef_transpose_eq hX'psd), (posSemidef_transpose_eq hX)]
  have hQq : ∀ u : n → ℝ, u ⬝ᵥ (Q *ᵥ u) = (C *ᵥ u) ⬝ᵥ (C *ᵥ u) := fun u => by
    rw [hQ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hconj : ∀ (Z : Matrix n n ℝ), Zᵀ = Z → ∀ u : n → ℝ,
      u ⬝ᵥ ((Z * F * Z) *ᵥ u) = (Z *ᵥ u) ⬝ᵥ (F *ᵥ (Z *ᵥ u)) := fun Z hZ u => by
    have := quad_conj Z F u
    rwa [hZ] at this
  have hc0 : ∀ u : n → ℝ, 0 ≤ (C *ᵥ u) ⬝ᵥ (C *ᵥ u) := fun u => by
    simpa using dotProduct_self_star_nonneg (C *ᵥ u)
  refine isHurwitz_of_lyapunov_detectable hd (posSemidef_quad_nonneg hX'psd)
    (W := Q + X' * F * X' + (X' - X) * F * (X' - X)) (fun u => ?_) (fun u hu => ?_) hid
  · rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, hQq,
      hconj X' (posSemidef_transpose_eq hX'psd), hconj _ hDs]
    have := (posSemidef_quad_nonneg hF) (X' *ᵥ u)
    have := (posSemidef_quad_nonneg hF) ((X' - X) *ᵥ u)
    linarith [hc0 u]
  · rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, hQq,
      hconj X' (posSemidef_transpose_eq hX'psd), hconj _ hDs] at hu
    have h1 := (posSemidef_quad_nonneg hF) (X' *ᵥ u)
    have h2 := (posSemidef_quad_nonneg hF) ((X' - X) *ᵥ u)
    have h3 := hc0 u
    refine ⟨dotProduct_self_eq_zero.1 (by linarith), ?_⟩
    rw [← Matrix.mulVec_mulVec]
    exact (posSemidef_mulVec_eq_zero hF) (by linarith)

/-- The Newton–Kleinman sequence of (2.9) exists from any stabilizing initial guess. -/
theorem exists_newtonKleinman_seq {k : Type*} [Fintype k] {A F Q P₀ : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hP₀ : P₀.PosSemidef) (hs : IsHurwitz (A - F * P₀)) :
    ∃ P : ℕ → Matrix n n ℝ, P 0 = P₀ ∧
      ∀ j, (A - F * P j)ᵀ * P (j + 1) + P (j + 1) * (A - F * P j) = -(P j * F * P j) - Q := by
  let S := {X : Matrix n n ℝ // X.PosSemidef ∧ IsHurwitz (A - F * X)}
  have step : ∀ X : S, ∃ X' : S,
      (A - F * X.1)ᵀ * X'.1 + X'.1 * (A - F * X.1) = -(X.1 * F * X.1) - Q := fun X => by
    obtain ⟨X', h1, h2, h3⟩ := newtonKleinman_step hF hQ hd X.2.1 X.2.2
    exact ⟨⟨X', h1, h2⟩, h3⟩
  choose f hf using step
  let seq : ℕ → S := fun j => Nat.rec ⟨P₀, hP₀, hs⟩ (fun _ X => f X) j
  exact ⟨fun j => (seq j).1, rfl, fun j => hf (seq j)⟩

/-- Polarization for symmetric matrices. -/
theorem entry_eq_polarization {X : Matrix n n ℝ} (hX : Xᵀ = X) (i j : n) :
    X i j = ((Pi.single i 1 + Pi.single j 1 : n → ℝ) ⬝ᵥ
        (X *ᵥ (Pi.single i 1 + Pi.single j 1)) -
      (Pi.single i 1 : n → ℝ) ⬝ᵥ (X *ᵥ Pi.single i 1) -
      (Pi.single j 1 : n → ℝ) ⬝ᵥ (X *ᵥ Pi.single j 1)) / 2 := by
  have hji : X j i = X i j := by rw [← Matrix.transpose_apply X i j, hX]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single,
    single_dotProduct, one_mul, MulOpposite.op_one, one_smul]
  simp only [Matrix.col_apply, hji] at *
  ring

omit [Fintype n] [DecidableEq n] in
/-- The paper's control weight `F = B R⁻¹ Bᵀ` with `R ≻ 0` is positive semidefinite. -/
theorem posSemidef_of_eq [Finite n] {m : Type*} [Fintype m] [DecidableEq m] {F : Matrix n n ℝ}
    {B : Matrix n m ℝ} {R : Matrix m m ℝ} (hR : R.PosDef) (hFdef : F = B * R⁻¹ * Bᵀ) :
    F.PosSemidef := by
  have := Fintype.ofFinite n
  rw [hFdef]
  have := hR.posSemidef.inv.mul_mul_conjTranspose_same B
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Theorem 2.5 (Newton–Kleinman) of arXiv 2501.07439, for any `F ⪰ 0`.** If `Q = Cᵀ C`,
`(A, C)` is detectable, `P₀ ⪰ 0` and `A - F P₀` is stable, then the iterates of (2.9) are
positive semidefinite and stabilizing and converge to the unique positive semidefinite
solution of the Riccati equation. See `newtonKleinman_tendsto` for the paper's form. -/
theorem newtonKleinman_tendsto_of_posSemidef {k : Type*} [Fintype k] {A F Q : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    {P : ℕ → Matrix n n ℝ} (hP0 : (P 0).PosSemidef) (hs : IsHurwitz (A - F * P 0))
    (hNK : ∀ j, (A - F * P j)ᵀ * P (j + 1) + P (j + 1) * (A - F * P j) = -(P j * F * P j) - Q) :
    ∃ Pinf : Matrix n n ℝ, Pinf.PosSemidef ∧ riccatiRes A F Q Pinf = 0 ∧
      (∀ X : Matrix n n ℝ, X.PosSemidef → riccatiRes A F Q X = 0 → X = Pinf) ∧
      Tendsto P atTop (𝓝 Pinf) := by
  -- every iterate is positive semidefinite and stabilizing
  have hall : ∀ j, (P j).PosSemidef ∧ IsHurwitz (A - F * P j) := by
    intro j
    induction j with
    | zero => exact ⟨hP0, hs⟩
    | succ j ih =>
      obtain ⟨X', h1, h2, h3⟩ := newtonKleinman_step hF hQ hd ih.1 ih.2
      obtain ⟨_, -, huniq⟩ := ih.2.existsUnique_lyapunov (-(P j * F * P j) - Q)
      have : P (j + 1) = X' := (huniq _ (hNK j)).trans (huniq _ h3).symm
      rw [this]
      exact ⟨h1, h2⟩
  have hsym : ∀ j, (P j)ᵀ = P j := fun j => posSemidef_transpose_eq (hall j).1
  -- monotonicity from the first iterate on
  have hmono : ∀ j (x : n → ℝ), x ⬝ᵥ (P (j + 2) *ᵥ x) ≤ x ⬝ᵥ (P (j + 1) *ᵥ x) := by
    intro j x
    have hid := newtonKleinman_identity (posSemidef_transpose_eq hF) (hsym j) (hsym (j + 1)) (hNK j)
    have e : (A - F * P (j + 1))ᵀ * (P (j + 1) - P (j + 2)) +
        (P (j + 1) - P (j + 2)) * (A - F * P (j + 1)) =
        -((P (j + 1) - P j) * F * (P (j + 1) - P j)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_comm, hid, hNK (j + 1)]
      abel
    have hDs : (P (j + 1) - P j)ᵀ = P (j + 1) - P j := by
      rw [Matrix.transpose_sub, hsym, hsym]
    have hW : ((P (j + 1) - P j) * F * (P (j + 1) - P j)).PosSemidef := by
      have := hF.conjTranspose_mul_mul_same (P (j + 1) - P j)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hDs] at this
    have := posSemidef_quad_nonneg ((hall (j + 1)).2.lyapunov_posSemidef hW e) x
    rw [Matrix.sub_mulVec, dotProduct_sub] at this
    linarith
  -- quadratic forms converge
  have hq : ∀ x : n → ℝ, ∃ c, Tendsto (fun j => x ⬝ᵥ (P (j + 1) *ᵥ x)) atTop (𝓝 c) := by
    intro x
    have hanti : Antitone (fun j => x ⬝ᵥ (P (j + 1) *ᵥ x)) :=
      antitone_nat_of_succ_le fun j => hmono j x
    exact ⟨_, tendsto_atTop_ciInf hanti
      ⟨0, fun _ ⟨j, hj⟩ => hj ▸ posSemidef_quad_nonneg (hall (j + 1)).1 x⟩⟩
  choose c hc using hq
  let L : Matrix n n ℝ := fun i j =>
    (c (Pi.single i 1 + Pi.single j 1) - c (Pi.single i 1) - c (Pi.single j 1)) / 2
  have hlim1 : Tendsto (fun j => P (j + 1)) atTop (𝓝 L) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (((hc (Pi.single i 1 + Pi.single j 1)).sub (hc (Pi.single i 1))).sub
      (hc (Pi.single j 1))).div_const 2
    refine this.congr fun t => ?_
    exact (entry_eq_polarization (hsym (t + 1)) i j).symm
  have hlim : Tendsto P atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).1 hlim1
  -- the limit is a positive semidefinite solution
  have hLs : Lᵀ = L := by
    have h1 : Tendsto (fun j => (P (j + 1))ᵀ) atTop (𝓝 Lᵀ) :=
      ((continuous_id.matrix_transpose).tendsto _).comp hlim1
    simp only [hsym] at h1
    exact tendsto_nhds_unique h1 hlim1
  have hLpsd : L.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hLs]
    · have hcont : Continuous fun M : Matrix n n ℝ => x ⬝ᵥ (M *ᵥ x) :=
        continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
      have := (hcont.tendsto L).comp hlim
      simp only [star_trivial]
      exact ge_of_tendsto' this fun j => posSemidef_quad_nonneg (hall j).1 x
  have hLric : riccatiRes A F Q L = 0 := by
    have hcont : Continuous fun p : Matrix n n ℝ × Matrix n n ℝ =>
        (A - F * p.1)ᵀ * p.2 + p.2 * (A - F * p.1) + (p.1 * F * p.1 + Q) := by
      fun_prop
    have h1 := (hcont.tendsto (L, L)).comp (hlim.prodMk_nhds hlim1)
    have h0 : (fun j => (A - F * P j)ᵀ * P (j + 1) + P (j + 1) * (A - F * P j) +
        (P j * F * P j + Q)) = fun _ => 0 := funext fun j => by
      rw [hNK j]; abel
    simp only [Function.comp_def] at h1
    rw [h0] at h1
    have h2 := tendsto_nhds_unique tendsto_const_nhds h1
    rw [h2, riccatiRes]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, hLs, (posSemidef_transpose_eq hF)]
    noncomm_ring
  exact ⟨L, hLpsd, hLric, fun X hX hXr =>
    riccati_posSemidef_unique hF hQ hd hX hXr hLpsd hLric, hlim⟩

/-- A Lyapunov solution with right-hand side `-1` has positive operator norm. -/
theorem norm_pos_of_lyapunov [Nonempty n] {N H : Matrix n n ℝ} (h : Nᵀ * H + H * N = -1) :
    0 < ‖H‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  rw [h0, Matrix.mul_zero, Matrix.zero_mul, add_zero] at h
  obtain ⟨i⟩ := ‹Nonempty n›
  have := congrFun (congrFun h i) i
  simp at this

/-- Over an empty index type every matrix is Hurwitz (its spectrum is empty). -/
theorem isHurwitz_of_isEmpty [IsEmpty n] (M : Matrix n n ℝ) : IsHurwitz M := by
  intro z hz
  rw [spectrum.of_subsingleton] at hz
  exact absurd hz (Set.notMem_empty z)

/-- **Theorem 3.4 of arXiv 2501.07439, stability part.** Let `F` be positive semidefinite (in the
paper `F = B R⁻¹ Bᵀ`), `Q = Cᵀ C` (in the paper `C = Q^{1/2}`), and `(A, C)` detectable
(the standing Assumption 3.3(c) at the state `y(t; μ)`). Let `P ⪰ 0` solve the Riccati
equation (3.4), let `H` solve the Lyapunov equation (3.7), and let
`‖A - A'‖ < 1 / (2 ‖H‖)` (3.6), with `A = A_{μ,t}`, `A' = A_{μ̃,t̃}` and the operator 2-norm.
Then `A' - F P` is stable. The uniqueness of `P` assumed in the paper is not needed. -/
theorem riccati_perturbation_isHurwitz {k : Type*} [Fintype k] {A A' F Q P H : Matrix n n ℝ}
    {C : Matrix k n ℝ} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hP : P.PosSemidef) (hric : riccatiRes A F Q P = 0)
    (hH : (A - F * P)ᵀ * H + H * (A - F * P) = -1) (hΔ : ‖A - A'‖ < 1 / (2 * ‖H‖)) :
    IsHurwitz (A' - F * P) := by
  have hs := riccati_closedLoop_isHurwitz hF hQ hd hP hric
  have hpd := hs.lyapunov_posDef hH
  have e : A' - F * P = (A - F * P) - (A - A') := by abel
  rw [e]
  exact isHurwitz_sub_of_lyapunov (fun x hx => by simpa using hpd.dotProduct_mulVec_pos hx) hH hΔ

/-- **Theorem 2.5 (Newton–Kleinman, [Kleinman 1968]) of arXiv 2501.07439.** Let `F = B R⁻¹ Bᵀ`
with `R ≻ 0`, `Q = Cᵀ C` (the paper's `C = Q^{1/2}`) and `(A, C)` detectable (Assumption 2.3;
stabilizability of `(A, B)` is implied by the existence of `P₀`). If `P₀ ⪰ 0` and `A - F P₀` is
stable, the Newton–Kleinman iterates (2.9) converge to the unique positive semidefinite solution
of the Riccati equation. The iterates are given as any sequence satisfying (2.9); one exists by
`exists_newtonKleinman_seq`, and it is unique since each step solves a uniquely solvable
Lyapunov equation. -/
theorem newtonKleinman_tendsto {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    {A F Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ} {C : Matrix k n ℝ}
    (hR : R.PosDef) (hFdef : F = B * R⁻¹ * Bᵀ) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    {P : ℕ → Matrix n n ℝ} (hP0 : (P 0).PosSemidef) (hs : IsHurwitz (A - F * P 0))
    (hNK : ∀ j, (A - F * P j)ᵀ * P (j + 1) + P (j + 1) * (A - F * P j) = -(P j * F * P j) - Q) :
    ∃ Pinf : Matrix n n ℝ, Pinf.PosSemidef ∧ riccatiRes A F Q Pinf = 0 ∧
      (∀ X : Matrix n n ℝ, X.PosSemidef → riccatiRes A F Q X = 0 → X = Pinf) ∧
      Tendsto P atTop (𝓝 Pinf) :=
  newtonKleinman_tendsto_of_posSemidef (posSemidef_of_eq hR hFdef) hQ hd hP0 hs hNK

/-- **Theorem 3.4 of arXiv 2501.07439.** Under the standing Assumption 3.3(c) at both states
(`(A, C)` and `(A', C)` detectable, `Q = Cᵀ C`), with `F = B R⁻¹ Bᵀ` and `R ≻ 0`: if `P ⪰ 0`
solves (3.4), `H` solves (3.7) and `‖A - A'‖ < 1 / (2 ‖H‖)` (3.6), then the perturbed Riccati
equation (3.5) has a unique positive semidefinite solution and `A' - F P` is stable. -/
theorem riccati_perturbation {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    {A A' F Q P H : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ} {C : Matrix k n ℝ}
    (hR : R.PosDef) (hFdef : F = B * R⁻¹ * Bᵀ) (hQ : Q = Cᵀ * C) (hd : IsDetectable A C)
    (hd' : IsDetectable A' C) (hP : P.PosSemidef) (hric : riccatiRes A F Q P = 0)
    (hH : (A - F * P)ᵀ * H + H * (A - F * P) = -1) (hΔ : ‖A - A'‖ < 1 / (2 * ‖H‖)) :
    (∃! P' : Matrix n n ℝ, P'.PosSemidef ∧ riccatiRes A' F Q P' = 0) ∧
      IsHurwitz (A' - F * P) := by
  have hF : F.PosSemidef := posSemidef_of_eq hR hFdef
  have hs := riccati_perturbation_isHurwitz hF hQ hd hP hric hH hΔ
  obtain ⟨Pk, h0, hNK⟩ := exists_newtonKleinman_seq hF hQ hd' hP hs
  obtain ⟨Pinf, h1, h2, h3, -⟩ := newtonKleinman_tendsto_of_posSemidef hF hQ hd' (h0 ▸ hP)
    (h0 ▸ hs) hNK
  exact ⟨⟨Pinf, ⟨h1, h2⟩, fun X hX => h3 X hX.1 hX.2⟩, hs⟩

/-- The standing assumption cannot be dropped from Theorem 3.4: for `A = 1`, `F = 0`, `Q = 0`
(so `F = B R⁻¹ Bᵀ` forces `B = 0`, `(A, B)` is not stabilizable and `(A, Q^{1/2})` is not
detectable), `P = 0` is the unique positive semidefinite solution of (3.4), `H = -1/2` solves
(3.7), `ΔA = 1/2` satisfies (3.6), and `A - ΔA - F P = 1/2` is not stable. This instance lies
outside the paper's hypotheses; it only shows that Assumption 3.3(c) is needed. -/
theorem riccati_perturbation_needs_detectability :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 1
    let A' : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => 1 / 2
    let H : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => -1 / 2
    ¬ IsDetectable A (0 : Matrix (Fin 1) (Fin 1) ℝ) ∧ riccatiRes A 0 0 0 = 0 ∧
      (∀ X : Matrix (Fin 1) (Fin 1) ℝ, X.PosSemidef → riccatiRes A 0 0 X = 0 → X = 0) ∧
      (A - 0 * 0)ᵀ * H + H * (A - 0 * 0) = -1 ∧ ‖A - A'‖ < 1 / (2 * ‖H‖) ∧
      ¬ IsHurwitz (A' - 0 * 0) := by
  intro A A' H
  have hhalf : ∀ c : ℝ, 0 ≤ c → (⟨c, 0⟩ : ℂ) ∈ spectrum ℂ ((Matrix.diagonal fun _ : Fin 1 => c).map
      (algebraMap ℝ ℂ)) := fun c _ => by
    refine mem_spectrum_iff_exists_mulVec.2 ⟨fun _ => 1, fun h => by simpa using congrFun h 0, ?_⟩
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Complex.ext_iff]
  refine ⟨?_, by simp [riccatiRes], ?_, ?_, ?_, ?_⟩
  · rintro ⟨K, hK⟩
    have hA : (Aᵀ - (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * K) = Matrix.diagonal fun _ => 1 := by
      simp [A]
    rw [hA] at hK
    exact absurd (hK _ (hhalf 1 zero_le_one)) (by norm_num)
  · intro X _ hX
    ext i j
    fin_cases i; fin_cases j
    have := congrFun (congrFun hX 0) 0
    simp [riccatiRes, A] at this ⊢
    linarith
  · ext i j
    fin_cases i; fin_cases j
    simp [A, H]
  · have e : A - A' = Matrix.diagonal fun _ => 1 / 2 := by
      ext i j
      fin_cases i; fin_cases j
      simp [A, A']
      norm_num
    rw [e]
    simp only [H, Matrix.l2_opNorm_diagonal, pi_norm_const]
    norm_num
  · intro h
    have e : A' - 0 * 0 = Matrix.diagonal fun _ => 1 / 2 := by simp [A']
    rw [e] at h
    exact absurd (h _ (hhalf (1 / 2) (by norm_num))) (by norm_num)

/-- A diagonal matrix with negative entries is stable. -/
theorem isHurwitz_diagonal {d : n → ℝ} (hd : ∀ i, d i < 0) : IsHurwitz (Matrix.diagonal d) := by
  intro z hz
  obtain ⟨v, hv, hev⟩ := mem_spectrum_iff_exists_mulVec.1 hz
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have h := congrFun hev i
  simp only [Matrix.diagonal_map (map_zero _), Matrix.mulVec_diagonal, Pi.smul_apply,
    smul_eq_mul] at h
  have hz' : z = (algebraMap ℝ ℂ) (d i) := (mul_right_cancel₀ hi h).symm
  rw [hz']
  simpa using hd i

/-- Non-vacuity of Theorem 3.4: `A = 0`, `B = R = C = Q = 1` (so `F = 1`), `P = 1`,
`H = I / 2`, `A' = -I / 2`, with `‖A - A'‖ = 1/2 < 1 = 1 / (2 ‖H‖)`. -/
example : (∃! P' : Matrix (Fin 1) (Fin 1) ℝ, P'.PosSemidef ∧
      riccatiRes (Matrix.diagonal fun _ => -1 / 2) 1 1 P' = 0) ∧
    IsHurwitz ((Matrix.diagonal fun _ : Fin 1 => (-1 / 2 : ℝ)) - 1 * 1) := by
  have hd0 : IsDetectable (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    refine ⟨1, ?_⟩
    have e : (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1 =
        Matrix.diagonal fun _ => -1 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [e]
    exact isHurwitz_diagonal fun _ => by norm_num
  have hd' : IsDetectable (Matrix.diagonal fun _ : Fin 1 => (-1 / 2 : ℝ))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    refine ⟨0, ?_⟩
    have e : (Matrix.diagonal fun _ : Fin 1 => (-1 / 2 : ℝ))ᵀ -
        (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 0 = Matrix.diagonal fun _ => -1 / 2 := by simp
    rw [e]
    exact isHurwitz_diagonal fun _ => by norm_num
  refine riccati_perturbation (A := 0) (F := 1) (Q := 1) (B := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (R := 1) (C := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (P := 1)
    (H := Matrix.diagonal fun _ => 1 / 2) Matrix.PosDef.one (by simp) (by simp) hd0 hd'
    Matrix.PosSemidef.one (by simp [riccatiRes]) ?_ ?_
  · ext i j; fin_cases i; fin_cases j; simp; norm_num
  · have e : (0 : Matrix (Fin 1) (Fin 1) ℝ) - Matrix.diagonal (fun _ => -1 / 2) =
        Matrix.diagonal fun _ => 1 / 2 := by
      ext i j; fin_cases i; fin_cases j; simp; norm_num
    rw [e, Matrix.l2_opNorm_diagonal]
    simp only [pi_norm_const]
    norm_num

/-- Converting condition (3.10): if `L < -(1/t) log(2 a h)` with `t, a, h > 0`, then
`a e^{L t} < 1 / (2 h)`. -/
theorem mul_exp_lt_of_lt_neg_log {L t a h : ℝ} (ht : 0 < t) (ha : 0 < a) (hh : 0 < h)
    (hL : L < -(1 / t) * Real.log (2 * a * h)) : a * Real.exp (L * t) < 1 / (2 * h) := by
  have hX : 0 < 2 * a * h := by positivity
  have h1 : L * t < -Real.log (2 * a * h) := by
    have := mul_lt_mul_of_pos_right hL ht
    rwa [show -(1 / t) * Real.log (2 * a * h) * t = -Real.log (2 * a * h) by
      field_simp] at this
  have h2 : Real.exp (L * t) < (2 * a * h)⁻¹ := by
    rw [← Real.exp_log (inv_pos.2 hX), Real.log_inv]
    exact Real.exp_lt_exp.2 h1
  calc a * Real.exp (L * t) < a * (2 * a * h)⁻¹ := mul_lt_mul_of_pos_left h2 ha
    _ = 1 / (2 * h) := by field_simp

/-- Converting `x < 1 / (2 c h)` into `c x < 1 / (2 h)` for `c ≥ 0`, `x ≥ 0`. -/
theorem mul_lt_of_lt_one_div {c x h : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hlt : x < 1 / (2 * c * h)) : 0 < h ∧ c * x < 1 / (2 * h) := by
  have hpos : 0 < 2 * c * h := one_div_pos.1 (hx.trans_lt hlt)
  have hh : 0 < h := by
    rcases hc.lt_or_eq with hc' | hc'
    · exact pos_of_mul_pos_right hpos (by positivity)
    · rw [← hc'] at hpos; simp at hpos
  refine ⟨hh, ?_⟩
  rw [lt_div_iff₀ hpos] at hlt
  rw [lt_div_iff₀ (by positivity)]
  linarith

/-- **Proposition 3.5 of arXiv 2501.07439, initial time.** Under Assumption 3.3(c), (d), (e)
(detectability of `(A(x), C)` on `Ω`, `y₀` `L_{y0}`-Lipschitz, `A` `L_A`-Lipschitz in the
operator 2-norm) and with `P(x) ⪰ 0` solving the SDRE (2.5) on `Ω`: if `H` solves the Lyapunov
equation (3.7) at `y₀(μ)` and `‖μ - μ̃‖ < 1 / (2 L_A L_{y0} ‖H_{μ,0}‖)` (3.9), then
`A_{μ̃,0} - F P_{μ,0}` is stable. The parameter space is any normed group (the paper restricts to
one dimension) and `Δμ = ‖μ - μ̃‖`. -/
theorem cascade_parameter_initial {k : Type*} [Fintype k] {Par : Type*} [NormedAddCommGroup Par]
    {Ω : Set (EuclideanSpace ℝ n)} {A Pr : EuclideanSpace ℝ n → Matrix n n ℝ}
    {F Q : Matrix n n ℝ} {C : Matrix k n ℝ} {LA Ly0 : ℝ} {PS : Set Par}
    {y0 : Par → EuclideanSpace ℝ n} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C)
    (hPr : ∀ x ∈ Ω, (Pr x).PosSemidef ∧ riccatiRes (A x) F Q (Pr x) = 0)
    (hdet : ∀ x ∈ Ω, IsDetectable (A x) C)
    (hy0 : ∀ μ₁ ∈ PS, ∀ μ₂ ∈ PS, ‖y0 μ₁ - y0 μ₂‖ ≤ Ly0 * ‖μ₁ - μ₂‖)
    (hLA : 0 ≤ LA) (hA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖A x - A x'‖ ≤ LA * ‖x - x'‖)
    {μ μ' : Par} (hμ : μ ∈ PS) (hμ' : μ' ∈ PS) (hΩ : y0 μ ∈ Ω) (hΩ' : y0 μ' ∈ Ω)
    {H : Matrix n n ℝ}
    (hH : (A (y0 μ) - F * Pr (y0 μ))ᵀ * H + H * (A (y0 μ) - F * Pr (y0 μ)) = -1)
    (h39 : ‖μ - μ'‖ < 1 / (2 * LA * Ly0 * ‖H‖)) :
    IsHurwitz (A (y0 μ') - F * Pr (y0 μ)) := by
  have hLy : 0 ≤ LA * Ly0 := by
    have hpos : 0 < 2 * LA * Ly0 * ‖H‖ := one_div_pos.1 ((norm_nonneg _).trans_lt h39)
    by_contra hneg
    push Not at hneg
    have : 2 * LA * Ly0 * ‖H‖ ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg hneg.le (norm_nonneg H)
      nlinarith
    linarith
  obtain ⟨-, hlt⟩ := mul_lt_of_lt_one_div hLy (norm_nonneg _)
    (by simpa [mul_assoc] using h39)
  refine riccati_perturbation_isHurwitz hF hQ (hdet _ hΩ) (hPr _ hΩ).1 (hPr _ hΩ).2 hH ?_
  calc ‖A (y0 μ) - A (y0 μ')‖ ≤ LA * ‖y0 μ - y0 μ'‖ := hA _ hΩ _ hΩ'
    _ ≤ LA * (Ly0 * ‖μ - μ'‖) := mul_le_mul_of_nonneg_left (hy0 μ hμ μ' hμ') hLA
    _ = LA * Ly0 * ‖μ - μ'‖ := by ring
    _ < 1 / (2 * ‖H‖) := hlt


/-- **Proposition 3.5 of arXiv 2501.07439.** Assumption 3.3(a)–(e) on `Ω ⊆ ℝⁿ`: the closed loop
`A_cl(x) = A(x) - F P(x)` is `L_cl`-Lipschitz (a), `(A(x), C)` is detectable (c) with `Q = Cᵀ C`,
`y₀` is `L_{y0}`-Lipschitz with `L_{y0} > 0` (d), `A` is `L_A`-Lipschitz with `L_A > 0` (e);
`P(x) ⪰ 0` solves the SDRE (2.5) on `Ω`. The one-sided Lipschitz constant is `L = m + L_cl M` from
`logm(A_cl(x)) ≤ m` and `‖x‖ ≤ M` on `Ω` (Proposition A.2, `closedLoop_isOneSidedLipschitzOn`).
Let `y(·; μ)`, `y(·; μ̃)` solve `ẏ = A_cl(y) y` on `[0, T]` in `Ω`, with `μ ≠ μ̃`, and let `H_t`
solve (3.7) at `y(t; μ)`. If (3.9) holds and (3.10) `L < -(1/t) log(2 L_A L_{y0} Δμ ‖H_t‖)`
holds for `t ∈ (0, T]`, then `A_{μ̃,t} - F P_{μ,t}` is stable for all `t ∈ [0, T]`, and (with
`(A(x), C)` detectable at `y(t; μ̃)` as well) the Newton–Kleinman iteration (2.9) for the SDRE
at `y(t; μ̃)` started from `P_{μ,t}` converges to `P_{μ̃,t}`. The paper's `B P_{μ,t}` in the
second claim is a misprint for `F P_{μ,t}`. Norms of matrices are operator 2-norms; the closed
loop acts on `EuclideanSpace ℝ n` through `Matrix.toEuclideanCLM`. -/
theorem cascade_parameter {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    {Par : Type*} [NormedAddCommGroup Par]
    {Ω : Set (EuclideanSpace ℝ n)} {A Pr : EuclideanSpace ℝ n → Matrix n n ℝ}
    {F Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ} {C : Matrix k n ℝ}
    {Lcl mlog M LA Ly0 T : ℝ} {PS : Set Par} {y0 : Par → EuclideanSpace ℝ n}
    (hR : R.PosDef) (hFdef : F = B * R⁻¹ * Bᵀ) (hQ : Q = Cᵀ * C)
    (hPr : ∀ x ∈ Ω, (Pr x).PosSemidef ∧ riccatiRes (A x) F Q (Pr x) = 0)
    (hLcl : 0 ≤ Lcl)
    (hLip : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖(A x - F * Pr x) - (A x' - F * Pr x')‖ ≤ Lcl * ‖x - x'‖)
    (hlog : ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ n,
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (A x - F * Pr x) v, v⟫ ≤ mlog * ‖v‖ ^ 2)
    (hbd : ∀ x ∈ Ω, ‖x‖ ≤ M)
    (hdet : ∀ x ∈ Ω, IsDetectable (A x) C)
    (hLy0 : 0 < Ly0) (hy0 : ∀ μ₁ ∈ PS, ∀ μ₂ ∈ PS, ‖y0 μ₁ - y0 μ₂‖ ≤ Ly0 * ‖μ₁ - μ₂‖)
    (hLA : 0 < LA) (hA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖A x - A x'‖ ≤ LA * ‖x - x'‖)
    {μ μ' : Par} (hμ : μ ∈ PS) (hμ' : μ' ∈ PS) (hne : μ ≠ μ')
    {y y' : ℝ → EuclideanSpace ℝ n}
    (hsol : ODESolution (fun _ z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z) z) y 0 T)
    (hsol' : ODESolution (fun _ z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z) z) y' 0 T)
    (h0 : y 0 = y0 μ) (h0' : y' 0 = y0 μ')
    (hyΩ : ∀ t ∈ Icc 0 T, y t ∈ Ω) (hy'Ω : ∀ t ∈ Icc 0 T, y' t ∈ Ω)
    {H : ℝ → Matrix n n ℝ}
    (hH : ∀ t ∈ Icc 0 T,
      (A (y t) - F * Pr (y t))ᵀ * H t + H t * (A (y t) - F * Pr (y t)) = -1)
    (h39 : ‖μ - μ'‖ < 1 / (2 * LA * Ly0 * ‖H 0‖))
    (h310 : ∀ t ∈ Ioc 0 T,
      mlog + Lcl * M < -(1 / t) * Real.log (2 * LA * Ly0 * ‖μ - μ'‖ * ‖H t‖)) :
    ∀ t ∈ Icc 0 T, IsHurwitz (A (y' t) - F * Pr (y t)) ∧
      ∀ Pk : ℕ → Matrix n n ℝ, Pk 0 = Pr (y t) →
        (∀ j, (A (y' t) - F * Pk j)ᵀ * Pk (j + 1) + Pk (j + 1) * (A (y' t) - F * Pk j) =
          -(Pk j * F * Pk j) - Q) → Tendsto Pk atTop (𝓝 (Pr (y' t))) := by
  have hF : F.PosSemidef := posSemidef_of_eq hR hFdef
  intro t ht
  have hstab : IsHurwitz (A (y' t) - F * Pr (y t)) := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact isHurwitz_of_isEmpty _
    rcases (Set.mem_Icc.1 ht).1.eq_or_lt with h0t | h0t
    · subst h0t
      have := cascade_parameter_initial hF hQ hPr hdet hy0 hLA.le hA hμ hμ'
        (h0 ▸ hyΩ 0 ht) (h0' ▸ hy'Ω 0 ht) (h0 ▸ hH 0 ht) h39
      rwa [h0, h0']
    · -- trajectory sensitivity (Corollary A.3, proved in the sibling module)
      have hsens := closedLoop_param_sensitivity
        (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) hLcl
        (fun x hx x' hx' => by
          beta_reduce
          rw [← map_sub, Matrix.l2_opNorm_toEuclideanCLM]; exact hLip x hx x' hx')
        hlog hbd hy0 hμ hμ' hsol hsol' h0 h0'
        (fun s hs => hyΩ s (Ico_subset_Icc_self hs)) (fun s hs => hy'Ω s (Ico_subset_Icc_self hs))
        t ht
      have hHpos := norm_pos_of_lyapunov (hH t ht)
      have hD : 0 < ‖μ - μ'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hlt := mul_exp_lt_of_lt_neg_log h0t (a := LA * Ly0 * ‖μ - μ'‖) (by positivity)
        hHpos (by simpa [mul_assoc] using h310 t ⟨h0t, ht.2⟩)
      refine riccati_perturbation_isHurwitz hF hQ (hdet _ (hyΩ t ht)) (hPr _ (hyΩ t ht)).1
        (hPr _ (hyΩ t ht)).2 (hH t ht) ?_
      calc ‖A (y t) - A (y' t)‖ ≤ LA * ‖y t - y' t‖ := hA _ (hyΩ t ht) _ (hy'Ω t ht)
        _ ≤ LA * (Ly0 * ‖μ - μ'‖ * Real.exp ((mlog + Lcl * M) * t)) :=
            mul_le_mul_of_nonneg_left hsens hLA.le
        _ = LA * Ly0 * ‖μ - μ'‖ * Real.exp ((mlog + Lcl * M) * t) := by ring
        _ < 1 / (2 * ‖H t‖) := hlt
  refine ⟨hstab, fun Pk hPk0 hNK => ?_⟩
  obtain ⟨Pinf, h1, h2, h3, h4⟩ := newtonKleinman_tendsto hR hFdef hQ (hdet _ (hy'Ω t ht))
    (hPk0 ▸ (hPr _ (hyΩ t ht)).1) (hPk0 ▸ hstab) hNK
  rwa [h3 _ (hPr _ (hy'Ω t ht)).1 (hPr _ (hy'Ω t ht)).2]

/-- Displacement along the closed-loop flow: if the speed `‖A_cl(y(s)) y(s)‖` is bounded by
`M₀` on `[a, b]`, then `‖y(b) - y(a)‖ ≤ M₀ (b - a)`. -/
theorem norm_sub_le_of_speed_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Acl : E → E →L[ℝ] E} {y : ℝ → E} {a b M₀ : ℝ} (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivAt y (Acl (y s) (y s)) s)
    (hM : ∀ s ∈ Icc a b, ‖Acl (y s) (y s)‖ ≤ M₀) : ‖y b - y a‖ ≤ M₀ * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' (fun s hs => (hy s hs).hasDerivWithinAt)
    (fun s hs => hM s (Ico_subset_Icc_self hs)) b ⟨hab, le_rfl⟩

/-- **Proposition 3.7 of arXiv 2501.07439.** Assumption 3.3(c), (e), (f) on `Ω`
(`(A(x), C)` detectable with `Q = Cᵀ C`; `A` `L_A`-Lipschitz; `A_cl = A - F P` differentiable
with `logm(A_cl(x)) ≤ m₁(x)`, `logm((∇A_cl(x)) x) ≤ m₂(x)`, `m₁ + m₂ ≤ 0`), `P(x) ⪰ 0` solving
the SDRE on `Ω`, and a trajectory `ẏ = A_cl(y) y` in `Ω` on `[0, t + Δt]`. If `H` solves (3.7)
at `y(t)` and `Δt < 1 / (2 L_A ‖A_cl(y₀) y₀‖ ‖H‖)` (3.15), then `A_{μ,t+Δt} - F P_{μ,t}` is
stable, and the Newton–Kleinman iteration at `y(t + Δt)` started from `P_{μ,t}` converges to
`P_{μ,t+Δt}`. The paper's proof bounds `‖y(t + Δt) - y(t)‖` by `Δt e^{Lt} M_{μ,Δt}` and then
uses (3.15), which lacks the factor `e^{Lt}`; here the displacement is bounded directly by
`Δt ‖A_cl(y₀) y₀‖`, since the speed is nonincreasing on `[0, t + Δt]` (Proposition A.4), so the
statement holds as printed. Assumption (f) is used with `≤ 0` instead of `< 0`. -/
theorem cascade_time {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    {Ω : Set (EuclideanSpace ℝ n)} {A Pr : EuclideanSpace ℝ n → Matrix n n ℝ}
    {F Q : Matrix n n ℝ} {B : Matrix n m ℝ} {R : Matrix m m ℝ} {C : Matrix k n ℝ}
    {DA : EuclideanSpace ℝ n →
      EuclideanSpace ℝ n →L[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)}
    {m₁ m₂ : EuclideanSpace ℝ n → ℝ} {LA t Δt : ℝ}
    (hR : R.PosDef) (hFdef : F = B * R⁻¹ * Bᵀ) (hQ : Q = Cᵀ * C)
    (hPr : ∀ x ∈ Ω, (Pr x).PosSemidef ∧ riccatiRes (A x) F Q (Pr x) = 0)
    (hdet : ∀ x ∈ Ω, IsDetectable (A x) C)
    (hLA : 0 ≤ LA) (hA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖A x - A x'‖ ≤ LA * ‖x - x'‖)
    (hDA : ∀ x ∈ Ω, HasFDerivAt (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) (DA x) x)
    (hm₁ : ∀ x ∈ Ω, ∀ v, ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (A x - F * Pr x) v, v⟫ ≤ m₁ x * ‖v‖ ^ 2)
    (hm₂ : ∀ x ∈ Ω, ∀ v, ⟪DA x v x, v⟫ ≤ m₂ x * ‖v‖ ^ 2) (hf : ∀ x ∈ Ω, m₁ x + m₂ x ≤ 0)
    {y : ℝ → EuclideanSpace ℝ n} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt)
    (hy : ∀ s ∈ Icc 0 (t + Δt),
      HasDerivAt y (Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y s) - F * Pr (y s)) (y s)) s)
    (hyΩ : ∀ s ∈ Icc 0 (t + Δt), y s ∈ Ω) {H : Matrix n n ℝ}
    (hH : (A (y t) - F * Pr (y t))ᵀ * H + H * (A (y t) - F * Pr (y t)) = -1)
    (h315 : Δt <
      1 / (2 * LA * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y 0) - F * Pr (y 0)) (y 0)‖ * ‖H‖)) :
    IsHurwitz (A (y (t + Δt)) - F * Pr (y t)) ∧
      ∀ Pk : ℕ → Matrix n n ℝ, Pk 0 = Pr (y t) →
        (∀ j, (A (y (t + Δt)) - F * Pk j)ᵀ * Pk (j + 1) +
          Pk (j + 1) * (A (y (t + Δt)) - F * Pk j) = -(Pk j * F * Pk j) - Q) →
        Tendsto Pk atTop (𝓝 (Pr (y (t + Δt)))) := by
  have hF : F.PosSemidef := posSemidef_of_eq hR hFdef
  have htΩ : y t ∈ Ω := hyΩ t ⟨ht, by linarith⟩
  have htΔΩ : y (t + Δt) ∈ Ω := hyΩ _ ⟨by linarith, le_rfl⟩
  set M₀ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y 0) - F * Pr (y 0)) (y 0)‖
  -- the speed is nonincreasing (Proposition A.4, proved in the sibling module)
  have hanti := closedLoop_speed_antitone
    (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) hDA hm₁ hm₂ hf hy hyΩ
  have hspeed : ∀ s ∈ Icc t (t + Δt),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y s) - F * Pr (y s)) (y s)‖ ≤ M₀ := fun s hs =>
    hanti ⟨le_rfl, by linarith [hs.1]⟩ ⟨by linarith [hs.1], hs.2⟩ (by linarith [hs.1])
  have hdisp : ‖y (t + Δt) - y t‖ ≤ M₀ * Δt := by
    have := norm_sub_le_of_speed_le
      (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z))
      (by linarith) (fun s hs => hy s ⟨by linarith [hs.1], hs.2⟩) hspeed
    simpa using this
  obtain ⟨-, hlt⟩ := mul_lt_of_lt_one_div (mul_nonneg hLA (norm_nonneg _)) hΔt
    (by simpa [mul_assoc] using h315)
  have hstab : IsHurwitz (A (y (t + Δt)) - F * Pr (y t)) := by
    refine riccati_perturbation_isHurwitz hF hQ (hdet _ htΩ) (hPr _ htΩ).1 (hPr _ htΩ).2 hH ?_
    calc ‖A (y t) - A (y (t + Δt))‖ ≤ LA * ‖y t - y (t + Δt)‖ := hA _ htΩ _ htΔΩ
      _ = LA * ‖y (t + Δt) - y t‖ := by rw [norm_sub_rev]
      _ ≤ LA * (M₀ * Δt) := mul_le_mul_of_nonneg_left hdisp hLA
      _ = LA * M₀ * Δt := by ring
      _ < 1 / (2 * ‖H‖) := hlt
  refine ⟨hstab, fun Pk hPk0 hNK => ?_⟩
  obtain ⟨Pinf, h1, h2, h3, h4⟩ := newtonKleinman_tendsto hR hFdef hQ (hdet _ htΔΩ)
    (hPk0 ▸ (hPr _ htΩ).1) (hPk0 ▸ hstab) hNK
  rwa [h3 _ (hPr _ htΔΩ).1 (hPr _ htΔΩ).2]


/-- Converting condition (3.14): if `L < (1/t) (log a - log b)` with `t, a, b > 0`, then
`b e^{L t} < a`. -/
theorem mul_exp_lt_of_lt_log_sub {L t a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (hL : L < 1 / t * (Real.log a - Real.log b)) : b * Real.exp (L * t) < a := by
  have h1 : L * t < Real.log (a / b) := by
    have := mul_lt_mul_of_pos_right hL ht
    rwa [show 1 / t * (Real.log a - Real.log b) * t = Real.log a - Real.log b by field_simp,
      ← Real.log_div ha.ne' hb.ne'] at this
  have h2 : Real.exp (L * t) < a / b := by
    rw [← Real.exp_log (div_pos ha hb)]
    exact Real.exp_lt_exp.2 h1
  calc b * Real.exp (L * t) < b * (a / b) := mul_lt_mul_of_pos_left h2 hb
    _ = a := by field_simp

/-- **Remark 3.6 of arXiv 2501.07439.** Hypotheses of `cascade_parameter` (stability part), and
time-discrete approximations `ỹ`, `ỹ'` of `y(·; μ)`, `y(·; μ̃)` of order `p` in `Ω`:
`‖y(t) - ỹ(t)‖ ≤ C Δt^p`, `‖y'(t) - ỹ'(t)‖ ≤ C Δt^p`. Let `H_t` solve (3.7) at `ỹ(t)`. If (3.14)
`L < (1/t) [log(1 - 4 C Δt^p L_A ‖H_t‖) - log(2 L_A L_{y0} Δμ ‖H_t‖)]` holds for `t ∈ (0, T]`,
then `A(ỹ'(t)) - F P(ỹ(t))` is stable for `t ∈ (0, T]`. The positivity of
`1 - 4 C Δt^p L_A ‖H_t‖`, needed for the logarithm in (3.14) to be meaningful, is an explicit
hypothesis. -/
theorem cascade_parameter_approx {k : Type*} [Fintype k] {Par : Type*} [NormedAddCommGroup Par]
    {Ω : Set (EuclideanSpace ℝ n)} {A Pr : EuclideanSpace ℝ n → Matrix n n ℝ}
    {F Q : Matrix n n ℝ} {C : Matrix k n ℝ} {Lcl mlog M LA Ly0 T Cerr Δt : ℝ} {p : ℕ}
    {PS : Set Par} {y0 : Par → EuclideanSpace ℝ n} (hF : F.PosSemidef) (hQ : Q = Cᵀ * C)
    (hPr : ∀ x ∈ Ω, (Pr x).PosSemidef ∧ riccatiRes (A x) F Q (Pr x) = 0)
    (hLcl : 0 ≤ Lcl)
    (hLip : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖(A x - F * Pr x) - (A x' - F * Pr x')‖ ≤ Lcl * ‖x - x'‖)
    (hlog : ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ n,
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (A x - F * Pr x) v, v⟫ ≤ mlog * ‖v‖ ^ 2)
    (hbd : ∀ x ∈ Ω, ‖x‖ ≤ M) (hdet : ∀ x ∈ Ω, IsDetectable (A x) C)
    (hLy0 : 0 < Ly0) (hy0 : ∀ μ₁ ∈ PS, ∀ μ₂ ∈ PS, ‖y0 μ₁ - y0 μ₂‖ ≤ Ly0 * ‖μ₁ - μ₂‖)
    (hLA : 0 < LA) (hA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖A x - A x'‖ ≤ LA * ‖x - x'‖)
    {μ μ' : Par} (hμ : μ ∈ PS) (hμ' : μ' ∈ PS) (hne : μ ≠ μ')
    {y y' yh yh' : ℝ → EuclideanSpace ℝ n}
    (hsol : ODESolution (fun _ z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z) z) y 0 T)
    (hsol' : ODESolution (fun _ z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z) z) y' 0 T)
    (h0 : y 0 = y0 μ) (h0' : y' 0 = y0 μ')
    (hyΩ : ∀ t ∈ Icc 0 T, y t ∈ Ω) (hy'Ω : ∀ t ∈ Icc 0 T, y' t ∈ Ω)
    (happ : ∀ t ∈ Icc 0 T, ‖y t - yh t‖ ≤ Cerr * Δt ^ p)
    (happ' : ∀ t ∈ Icc 0 T, ‖y' t - yh' t‖ ≤ Cerr * Δt ^ p)
    (hyhΩ : ∀ t ∈ Icc 0 T, yh t ∈ Ω) (hyh'Ω : ∀ t ∈ Icc 0 T, yh' t ∈ Ω)
    {H : ℝ → Matrix n n ℝ}
    (hH : ∀ t ∈ Icc 0 T,
      (A (yh t) - F * Pr (yh t))ᵀ * H t + H t * (A (yh t) - F * Pr (yh t)) = -1)
    (hdom : ∀ t ∈ Ioc 0 T, 0 < 1 - 4 * Cerr * Δt ^ p * LA * ‖H t‖)
    (h314 : ∀ t ∈ Ioc 0 T, mlog + Lcl * M < 1 / t *
      (Real.log (1 - 4 * Cerr * Δt ^ p * LA * ‖H t‖) -
        Real.log (2 * LA * Ly0 * ‖μ - μ'‖ * ‖H t‖))) :
    ∀ t ∈ Ioc 0 T, IsHurwitz (A (yh' t) - F * Pr (yh t)) := by
  intro t ht
  have htc : t ∈ Icc 0 T := Ioc_subset_Icc_self ht
  rcases isEmpty_or_nonempty n with hn | hn
  · exact isHurwitz_of_isEmpty _
  have hsens := closedLoop_param_sensitivity
    (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) hLcl
    (fun x hx x' hx' => by
      beta_reduce
      rw [← map_sub, Matrix.l2_opNorm_toEuclideanCLM]; exact hLip x hx x' hx')
    hlog hbd hy0 hμ hμ' hsol hsol' h0 h0'
    (fun s hs => hyΩ s (Ico_subset_Icc_self hs)) (fun s hs => hy'Ω s (Ico_subset_Icc_self hs))
    t htc
  have hh := norm_pos_of_lyapunov (hH t htc)
  have hD : 0 < ‖μ - μ'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hb : 0 < 2 * LA * Ly0 * ‖μ - μ'‖ * ‖H t‖ := by positivity
  have hlt := mul_exp_lt_of_lt_log_sub ht.1 (hdom t ht) hb (h314 t ht)
  refine riccati_perturbation_isHurwitz hF hQ (hdet _ (hyhΩ t htc)) (hPr _ (hyhΩ t htc)).1
    (hPr _ (hyhΩ t htc)).2 (hH t htc) ?_
  have htri : ‖yh t - yh' t‖ ≤ ‖y t - y' t‖ + 2 * (Cerr * Δt ^ p) := by
    have e : yh t - yh' t = (y t - y' t) - (y t - yh t) + (y' t - yh' t) := by abel
    rw [e]
    have := norm_add_le ((y t - y' t) - (y t - yh t)) (y' t - yh' t)
    have := norm_sub_le (y t - y' t) (y t - yh t)
    linarith [happ t htc, happ' t htc]
  rw [lt_div_iff₀ (by positivity)]
  calc ‖A (yh t) - A (yh' t)‖ * (2 * ‖H t‖)
      ≤ LA * (Ly0 * ‖μ - μ'‖ * Real.exp ((mlog + Lcl * M) * t) + 2 * (Cerr * Δt ^ p)) *
          (2 * ‖H t‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ‖A (yh t) - A (yh' t)‖ ≤ LA * ‖yh t - yh' t‖ := hA _ (hyhΩ t htc) _ (hyh'Ω t htc)
          _ ≤ _ := mul_le_mul_of_nonneg_left (htri.trans (by linarith [hsens])) hLA.le
    _ = 2 * LA * Ly0 * ‖μ - μ'‖ * ‖H t‖ * Real.exp ((mlog + Lcl * M) * t) +
          4 * Cerr * Δt ^ p * LA * ‖H t‖ := by ring
    _ < 1 := by linarith

/-- **Remark 3.8 of arXiv 2501.07439.** Hypotheses of `cascade_time` (stability part), and a
time-discrete approximation `ỹ` of order `p ≥ 1` with `‖y(s) - ỹ(s)‖ ≤ C Δt^p` at `s = t` and
`s = t + Δt`, `C ≥ 0`, `Δt < 1`. Let `H` solve (3.7) at `ỹ(t)`. If
`Δt < 1 / (2 L_A (M + 2 C) ‖H‖)` with `M = ‖A_cl(y₀) y₀‖` (`= M_{μ,Δt}` by Proposition A.4),
then `A(ỹ(t + Δt)) - F P(ỹ(t))` is stable. As in Proposition 3.7, the paper's intermediate bound
carries a factor `e^{Lt}` that its final condition drops; the displacement bound used here
does not need it. -/
theorem cascade_time_approx {k : Type*} [Fintype k]
    {Ω : Set (EuclideanSpace ℝ n)} {A Pr : EuclideanSpace ℝ n → Matrix n n ℝ}
    {F Q : Matrix n n ℝ} {C : Matrix k n ℝ}
    {DA : EuclideanSpace ℝ n →
      EuclideanSpace ℝ n →L[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)}
    {m₁ m₂ : EuclideanSpace ℝ n → ℝ} {LA t Δt Cerr : ℝ} {p : ℕ}
    (hF : F.PosSemidef) (hQ : Q = Cᵀ * C)
    (hPr : ∀ x ∈ Ω, (Pr x).PosSemidef ∧ riccatiRes (A x) F Q (Pr x) = 0)
    (hdet : ∀ x ∈ Ω, IsDetectable (A x) C)
    (hLA : 0 ≤ LA) (hA : ∀ x ∈ Ω, ∀ x' ∈ Ω, ‖A x - A x'‖ ≤ LA * ‖x - x'‖)
    (hDA : ∀ x ∈ Ω,
      HasFDerivAt (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) (DA x) x)
    (hm₁ : ∀ x ∈ Ω, ∀ v,
      ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (A x - F * Pr x) v, v⟫ ≤ m₁ x * ‖v‖ ^ 2)
    (hm₂ : ∀ x ∈ Ω, ∀ v, ⟪DA x v x, v⟫ ≤ m₂ x * ‖v‖ ^ 2) (hf : ∀ x ∈ Ω, m₁ x + m₂ x ≤ 0)
    {y yh : ℝ → EuclideanSpace ℝ n} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt) (hΔt1 : Δt < 1)
    (hp : 1 ≤ p) (hC : 0 ≤ Cerr)
    (hy : ∀ s ∈ Icc 0 (t + Δt),
      HasDerivAt y (Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y s) - F * Pr (y s)) (y s)) s)
    (hyΩ : ∀ s ∈ Icc 0 (t + Δt), y s ∈ Ω)
    (happ : ‖y t - yh t‖ ≤ Cerr * Δt ^ p) (happ' : ‖y (t + Δt) - yh (t + Δt)‖ ≤ Cerr * Δt ^ p)
    (hyhΩ : yh t ∈ Ω) (hyh'Ω : yh (t + Δt) ∈ Ω) {H : Matrix n n ℝ}
    (hH : (A (yh t) - F * Pr (yh t))ᵀ * H + H * (A (yh t) - F * Pr (yh t)) = -1)
    (h : Δt < 1 / (2 * LA *
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y 0) - F * Pr (y 0)) (y 0)‖ + 2 * Cerr) * ‖H‖)) :
    IsHurwitz (A (yh (t + Δt)) - F * Pr (yh t)) := by
  set M₀ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y 0) - F * Pr (y 0)) (y 0)‖
  have hanti := closedLoop_speed_antitone
    (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z)) hDA hm₁ hm₂ hf hy hyΩ
  have hspeed : ∀ s ∈ Icc t (t + Δt),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A (y s) - F * Pr (y s)) (y s)‖ ≤ M₀ := fun s hs =>
    hanti ⟨le_rfl, by linarith [hs.1]⟩ ⟨by linarith [hs.1], hs.2⟩ (by linarith [hs.1])
  have hdisp : ‖y (t + Δt) - y t‖ ≤ M₀ * Δt := by
    have := norm_sub_le_of_speed_le
      (Acl := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (A z - F * Pr z))
      (by linarith) (fun s hs => hy s ⟨by linarith [hs.1], hs.2⟩) hspeed
    simpa using this
  have hpow : Δt ^ p ≤ Δt := pow_le_of_le_one hΔt hΔt1.le (by omega)
  have htri : ‖yh (t + Δt) - yh t‖ ≤ (M₀ + 2 * Cerr) * Δt := by
    have e : yh (t + Δt) - yh t =
        (y (t + Δt) - y t) - (y (t + Δt) - yh (t + Δt)) + (y t - yh t) := by abel
    rw [e]
    have := norm_add_le ((y (t + Δt) - y t) - (y (t + Δt) - yh (t + Δt))) (y t - yh t)
    have := norm_sub_le (y (t + Δt) - y t) (y (t + Δt) - yh (t + Δt))
    nlinarith [mul_le_mul_of_nonneg_left hpow hC]
  obtain ⟨-, hlt⟩ := mul_lt_of_lt_one_div
    (mul_nonneg hLA (add_nonneg (norm_nonneg _) (mul_nonneg zero_le_two hC))) hΔt
    (by simpa [mul_assoc] using h)
  refine riccati_perturbation_isHurwitz hF hQ (hdet _ hyhΩ) (hPr _ hyhΩ).1 (hPr _ hyhΩ).2 hH ?_
  calc ‖A (yh t) - A (yh (t + Δt))‖ ≤ LA * ‖yh t - yh (t + Δt)‖ := hA _ hyhΩ _ hyh'Ω
    _ = LA * ‖yh (t + Δt) - yh t‖ := by rw [norm_sub_rev]
    _ ≤ LA * ((M₀ + 2 * Cerr) * Δt) := mul_le_mul_of_nonneg_left htri hLA
    _ = LA * (M₀ + 2 * Cerr) * Δt := by ring
    _ < 1 / (2 * ‖H‖) := hlt

end Dec

/-! ### Bridge to the core Kalman–Bucy Riccati field -/

/-- The core filter Riccati field is the residual (2.7) of the transposed system with
`F = ρ I`: `A P + P Aᵀ - ρ P² + Qn = riccatiRes Aᵀ (ρ • 1) Qn P`. -/
theorem riccatiField_eq_riccatiRes {d : ℕ} (A Qn P : Matrix (Fin d) (Fin d) ℝ) (ρ t : ℝ) :
    KalmanBucy.riccatiField A ρ Qn t P = riccatiRes Aᵀ (ρ • 1) Qn P := by
  simp [KalmanBucy.riccatiField, riccatiRes]

/-- **Stationary Kalman–Bucy covariances are stabilizing.** If `P ⪰ 0` is a zero of the core
filter Riccati field `A P + P Aᵀ - ρ P² + Qn` with `ρ ≥ 0`, `Qn = Cᵀ C` and `(Aᵀ, C)`
detectable, then `Aᵀ - ρ P` is Hurwitz (`riccati_closedLoop_isHurwitz` through the bridge). -/
theorem riccatiField_stationary_isHurwitz {d : ℕ} {k : Type*} [Fintype k]
    {A Qn P : Matrix (Fin d) (Fin d) ℝ} {ρ : ℝ} {C : Matrix k (Fin d) ℝ} (hρ : 0 ≤ ρ)
    (hQ : Qn = Cᵀ * C) (hd : IsDetectable Aᵀ C) (hP : P.PosSemidef)
    (h : KalmanBucy.riccatiField A ρ Qn 0 P = 0) : IsHurwitz (Aᵀ - ρ • P) := by
  rw [riccatiField_eq_riccatiRes] at h
  have hF : (ρ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hρ
  have := riccati_closedLoop_isHurwitz hF hQ hd hP h
  rwa [Matrix.smul_mul, Matrix.one_mul] at this

/-! ### Section 4: factor equations of the DLRA -/

/-- **Equation (4.5) of arXiv 2501.07439.** If `Ẏ = U̇ Zᵀ + U Żᵀ` with `Uᵀ U = I`, the gauge
`Uᵀ U̇ = 0`, and `C = Zᵀ Z` invertible, then `U̇ = (I - U Uᵀ) Ẏ Z C⁻¹` and `Ż = Ẏᵀ U`. -/
theorem factor_eq {N p r : Type*} [Fintype N] [Fintype p] [Fintype r] [DecidableEq N]
    [DecidableEq r] {U U' : Matrix N r ℝ} {Z Z' : Matrix p r ℝ} {Y' : Matrix N p ℝ}
    (hU : Uᵀ * U = 1) (hg : Uᵀ * U' = 0) (hC : IsUnit (Zᵀ * Z).det)
    (hY : Y' = U' * Zᵀ + U * Z'ᵀ) :
    U' = (1 - U * Uᵀ) * Y' * Z * (Zᵀ * Z)⁻¹ ∧ Z' = Y'ᵀ * U := by
  have h1 : (1 - U * Uᵀ) * Y' = U' * Zᵀ := by
    rw [hY, Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_assoc U Uᵀ (U' * Zᵀ), ← Matrix.mul_assoc Uᵀ U', hg, Matrix.mul_assoc U Uᵀ,
      ← Matrix.mul_assoc Uᵀ U, hU]
    simp
  refine ⟨?_, ?_⟩
  · rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ,
      Matrix.mul_nonsing_inv _ hC, Matrix.mul_one]
  · have h2 : Uᵀ * Y' = Z'ᵀ := by
      rw [hY, Matrix.mul_add, ← Matrix.mul_assoc, hg, ← Matrix.mul_assoc, hU]
      simp
    rw [← Matrix.transpose_transpose Z', ← h2, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The factor equations (4.5) produce the core tangent projection: with
`U̇ = (I - U Uᵀ) Ẏ Z C⁻¹` and `Ż = Ẏᵀ U`, `U̇ Zᵀ + U Żᵀ = P_Y Ẏ = tangentProj U V Ẏ` for any `V`
whose columns span the range of `Z` orthonormally (`V Vᵀ = Z C⁻¹ Zᵀ`). -/
theorem factor_eq_tangentProj {N p r r' : Type*} [Fintype N] [Fintype p] [Fintype r]
    [Fintype r'] [DecidableEq N] [DecidableEq r] {U : Matrix N r ℝ} {Z : Matrix p r ℝ}
    {V : Matrix p r' ℝ} (hV : V * Vᵀ = Z * (Zᵀ * Z)⁻¹ * Zᵀ) (Y' : Matrix N p ℝ) :
    ((1 - U * Uᵀ) * Y' * Z * (Zᵀ * Z)⁻¹) * Zᵀ + U * (Y'ᵀ * U)ᵀ = tangentProj U V Y' := by
  rw [tangentProj_apply, Matrix.transpose_mul, Matrix.transpose_transpose]
  have e : (1 - U * Uᵀ) * Y' * Z * (Zᵀ * Z)⁻¹ * Zᵀ = (1 - U * Uᵀ) * Y' * (V * Vᵀ) := by
    rw [hV]; simp only [Matrix.mul_assoc]
  rw [e]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The column-wise Kronecker square `V_⊗(Z) = [Z₁ ⊗ Z₁, …, Z_p ⊗ Z_p]` of Section 4.2. -/
def colKron {r p : Type*} (Z : Matrix r p ℝ) : Matrix (r × r) p ℝ :=
  fun ij j => Z ij.1 j * Z ij.2 j

/-- `(U z) ⊗ (U z) = (U ⊗ U)(z ⊗ z)` column by column (the step to (4.8)). -/
theorem colKron_mul {N r p : Type*} [Fintype r] (U : Matrix N r ℝ) (Z : Matrix r p ℝ) :
    colKron (U * Z) = Matrix.kroneckerMap (· * ·) U U * colKron Z := by
  ext ⟨a, b⟩ j
  simp only [colKron, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Equations (4.7) to (4.12) of arXiv 2501.07439.** For `f(y) = A y + T (y ⊗ y)` applied
column-wise (`F(Y) = A Y + T V_⊗(Y)`), the reduced state `Y = U Z̃`, the feedback
`𝒰 = -R⁻¹ B_rᵀ P̃_Z` with `B_r = Uᵀ B`, and `C = Z̃ Z̃ᵀ` invertible, the right-hand sides of
(4.7) equal those of (4.12): `(I - U Uᵀ) Ẏ Z̃ᵀ C⁻¹ = (I - U Uᵀ)(A U + T (U ⊗ U) V(Z̃) - S(Z̃) C⁻¹)`
with `V(Z̃) = V_⊗(Z̃) Z̃ᵀ C⁻¹`, `S(Z̃) = B R⁻¹ B_rᵀ P̃_Z Z̃ᵀ`, and
`Uᵀ Ẏ = A_r Z̃ + T_r V_⊗(Z̃) - F_r P̃_Z` with `A_r = Uᵀ A U`, `T_r = Uᵀ T (U ⊗ U)`,
`F_r = B_r R⁻¹ B_rᵀ`. Here `Ẏ = F(U Z̃) + B 𝒰`. -/
theorem dlra_feedback_eq {N r p m : Type*} [Fintype N] [Fintype r] [Fintype p] [Fintype m]
    [DecidableEq N] [DecidableEq r] [DecidableEq m] (A : Matrix N N ℝ) (T : Matrix N (N × N) ℝ)
    (B : Matrix N m ℝ) (R : Matrix m m ℝ) (U : Matrix N r ℝ) (Zt PZ : Matrix r p ℝ)
    (hC : IsUnit (Zt * Ztᵀ).det) :
    let Yd := A * (U * Zt) + T * colKron (U * Zt) + B * (-(R⁻¹ * (Uᵀ * B)ᵀ * PZ))
    (1 - U * Uᵀ) * Yd * Ztᵀ * (Zt * Ztᵀ)⁻¹ =
        (1 - U * Uᵀ) * (A * U + T * Matrix.kroneckerMap (· * ·) U U *
          (colKron Zt * Ztᵀ * (Zt * Ztᵀ)⁻¹) -
          B * R⁻¹ * (Uᵀ * B)ᵀ * PZ * Ztᵀ * (Zt * Ztᵀ)⁻¹) ∧
      Uᵀ * Yd = (Uᵀ * A * U) * Zt + (Uᵀ * T * Matrix.kroneckerMap (· * ·) U U) * colKron Zt -
        (Uᵀ * B) * R⁻¹ * (Uᵀ * B)ᵀ * PZ := by
  intro Yd
  have hZ : Zt * Ztᵀ * (Zt * Ztᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  refine ⟨?_, ?_⟩
  · simp only [Yd, colKron_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_sub, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Zt Ztᵀ (Zt * Ztᵀ)⁻¹, hZ, Matrix.mul_one]
    abel
  · simp only [Yd, colKron_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc]
    abel

end LeanDLRA.Literature.P2501_07439
