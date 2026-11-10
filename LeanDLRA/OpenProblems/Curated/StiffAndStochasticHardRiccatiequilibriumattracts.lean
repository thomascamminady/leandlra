import LeanDLRA.OpenProblems.Curated.StiffAndStochasticDefs
import LeanDLRA.Foundations.OneSided
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Dynamics.ContinuousDLRA
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Stochastic.KalmanBucy

/-!
# `riccati_equilibrium_attracts`
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

section Fan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ℓ : ℝ}

end Fan

section Stiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {ℓ : ℝ}

end Stiff

section AP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end AP

section Riccati

open scoped Matrix LeanDLRA.Frobenius

variable {d : ℕ}

/- Proved in `LeanDLRA/Stochastic/KalmanBucy.lean` (OP-SL-01):
`LeanDLRA.KalmanBucy.riccatiField_isOneSidedLipschitzOn` (one-sided Lipschitz on the PSD cone)
and `LeanDLRA.KalmanBucy.dlrKalmanBucy_covariance_error_uniform` (uniform-in-time DLR-KBP
covariance error), with the JMCO variant `jmcoKalmanBucy_covariance_error_uniform`. -/

/-- The Lyapunov operator `X ↦ B X + X Bᵀ` of a strictly dissipative matrix has trivial kernel. -/
private theorem lyapunov_eq_zero {B X : Matrix (Fin d) (Fin d) ℝ} {μ : ℝ}
    (hB : ∀ x : Fin d → ℝ, x ⬝ᵥ ((B + Bᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0)
    (hX : B * X + X * Bᵀ = 0) : X = 0 := by
  have e1 := KalmanBucy.inner_mul_left_le hB X
  have e2 := KalmanBucy.inner_mul_transpose_le hB X
  have e3 : ⟪B * X, X⟫ + ⟪X * Bᵀ, X⟫ = 0 := by
    rw [← inner_add_left, hX, inner_zero_left]
  have h0 : ‖X‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖X‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h0 (sq_nonneg _)))

/-- The Lyapunov equation of a strictly dissipative matrix is solvable (finite dimensions:
injective implies surjective). -/
private theorem lyapunov_surjective {B : Matrix (Fin d) (Fin d) ℝ} {μ : ℝ}
    (hB : ∀ x : Fin d → ℝ, x ⬝ᵥ ((B + Bᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0)
    (C : Matrix (Fin d) (Fin d) ℝ) : ∃ X : Matrix (Fin d) (Fin d) ℝ, B * X + X * Bᵀ = C := by
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    LinearMap.mulLeft ℝ B + LinearMap.mulRight ℝ Bᵀ
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    exact fun X hX => lyapunov_eq_zero hB hμ hX
  exact LinearMap.injective_iff_surjective.1 hinj C

/-- A solution of a Lyapunov equation with symmetric right-hand side is symmetric. -/
private theorem lyapunov_symm {B X C : Matrix (Fin d) (Fin d) ℝ} {μ : ℝ}
    (hB : ∀ x : Fin d → ℝ, x ⬝ᵥ ((B + Bᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0)
    (hC : Cᵀ = C) (hX : B * X + X * Bᵀ = C) : Xᵀ = X := by
  have ht : B * Xᵀ + Xᵀ * Bᵀ = C := by
    have := congrArg Matrix.transpose hX
    rwa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hC, add_comm] at this
  have h0 : B * (Xᵀ - X) + (Xᵀ - X) * Bᵀ = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_comm, ht, hX, sub_self]
  exact sub_eq_zero.1 (lyapunov_eq_zero hB hμ h0)

/-- **Positivity for the Lyapunov equation**, without any integral: if `X` is symmetric and
`B X + X Bᵀ = -C` with `C ⪰ 0`, then evaluating at a unit eigenvector `v` of `X` with eigenvalue
`λ` gives `λ vᵀ (B + Bᵀ) v = -vᵀ C v ≤ 0`, which excludes `λ < 0` since
`vᵀ (B + Bᵀ) v ≤ μ < 0`. -/
private theorem lyapunov_posSemidef {B X C : Matrix (Fin d) (Fin d) ℝ} {μ : ℝ}
    (hB : ∀ x : Fin d → ℝ, x ⬝ᵥ ((B + Bᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0)
    (hXs : Xᵀ = X) (hC : C.PosSemidef) (hX : B * X + X * Bᵀ = -C) : X.PosSemidef := by
  have hH : X.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hXs]
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  have hl : hH.eigenvalues i < 0 := not_le.1 hneg
  set v : Fin d → ℝ := ⇑(hH.eigenvectorBasis i) with hv
  have hev : X *ᵥ v = hH.eigenvalues i • v := hH.mulVec_eigenvectorBasis i
  have hvv : v ⬝ᵥ v = 1 := by
    have h1 : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    have h2 := EuclideanSpace.real_norm_sq_eq (hH.eigenvectorBasis i)
    rw [h1] at h2
    simpa [dotProduct, sq] using h2.symm
  have h1 : v ⬝ᵥ ((B * X) *ᵥ v) = hH.eigenvalues i * (v ⬝ᵥ (B *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : v ⬝ᵥ ((X * Bᵀ) *ᵥ v) = hH.eigenvalues i * (v ⬝ᵥ (Bᵀ *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hXs, hev,
      smul_dotProduct, smul_eq_mul]
  have h3 : v ⬝ᵥ ((B * X + X * Bᵀ) *ᵥ v) = hH.eigenvalues i * (v ⬝ᵥ ((B + Bᵀ) *ᵥ v)) := by
    rw [Matrix.add_mulVec, dotProduct_add, h1, h2, Matrix.add_mulVec, dotProduct_add]
    ring
  have h4 : 0 ≤ v ⬝ᵥ (C *ᵥ v) := by simpa using hC.dotProduct_mulVec_nonneg v
  rw [hX, Matrix.neg_mulVec, dotProduct_neg] at h3
  have h5 := hB v
  rw [hvv, mul_one] at h5
  nlinarith

/-- Cauchy–Schwarz for the entries of a PSD matrix. -/
private theorem sq_apply_le_of_posSemidef {D : Matrix (Fin d) (Fin d) ℝ} (hD : D.PosSemidef)
    (i j : Fin d) : D i j ^ 2 ≤ D i i * D j j := by
  have hsymm : D j i = D i j := by simpa using hD.1.apply i j
  have hq : ∀ t : ℝ, 0 ≤ D i i * (t * t) + (2 * D i j) * t + D j j := fun t => by
    have h := hD.dotProduct_mulVec_nonneg (Pi.single i t + Pi.single j 1)
    simp only [Matrix.mulVec_add, Matrix.mulVec_single, dotProduct_add, add_dotProduct,
      single_dotProduct, star_trivial, Pi.smul_apply, Matrix.col_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at h
    rw [hsymm] at h
    linarith
  have h := discrim_le_zero hq
  rw [discrim] at h
  nlinarith

/-- The Frobenius norm of a PSD matrix is at most its trace. -/
private theorem norm_le_trace_of_posSemidef {D : Matrix (Fin d) (Fin d) ℝ} (hD : D.PosSemidef) :
    ‖D‖ ≤ D.trace := by
  have htr : 0 ≤ D.trace := hD.trace_nonneg
  have h : ‖D‖ ^ 2 ≤ D.trace ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, sq, Matrix.trace, Finset.sum_mul_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      sq_apply_le_of_posSemidef hD i j
  exact (sq_le_sq₀ (norm_nonneg D) htr).1 h

/-- A Loewner-decreasing sequence of PSD matrices converges to a PSD matrix: the Frobenius norms
of the increments are bounded by the increments of the trace, so they are summable. -/
private theorem exists_tendsto_of_antitone_posSemidef {u : ℕ → Matrix (Fin d) (Fin d) ℝ}
    (hu : ∀ n, (u n).PosSemidef) (hanti : ∀ n, (u n - u (n + 1)).PosSemidef) :
    ∃ L : Matrix (Fin d) (Fin d) ℝ, L.PosSemidef ∧ Tendsto u atTop (𝓝 L) := by
  have hsum : ∀ n, ∑ k ∈ Finset.range n, ‖u k - u (k + 1)‖ ≤ (u 0).trace := fun n => by
    calc ∑ k ∈ Finset.range n, ‖u k - u (k + 1)‖
        ≤ ∑ k ∈ Finset.range n, ((u k).trace - (u (k + 1)).trace) :=
          Finset.sum_le_sum fun k _ => by
            rw [← Matrix.trace_sub]
            exact norm_le_trace_of_posSemidef (hanti k)
      _ = (u 0).trace - (u n).trace := Finset.sum_range_sub' _ _
      _ ≤ (u 0).trace := by linarith [(hu n).trace_nonneg]
  have hsummable : Summable fun n => ‖u n - u (n + 1)‖ :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) hsum
  have hc : CauchySeq u := by
    refine cauchySeq_of_summable_dist ?_
    simpa only [dist_eq_norm, Nat.succ_eq_add_one] using hsummable
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hE : ∀ i j, Tendsto (fun n => u n i j) atTop (𝓝 (L i j)) := fun i j => by
    have h0 : Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hL
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0)
    rw [Real.norm_eq_abs]
    exact Frobenius.abs_apply_le_norm (u n - L) i j
  have hsymm : Lᵀ = L := by
    ext i j
    refine tendsto_nhds_unique (hE j i) ?_
    have : (fun n => u n j i) = fun n => u n i j := funext fun n => by
      have := (hu n).1.apply i j
      simpa using this
    rw [this]
    exact hE i j
  have hH : L.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hsymm]
  refine ⟨L, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_, hL⟩
  have hq : Tendsto (fun n => x ⬝ᵥ (u n *ᵥ x)) atTop (𝓝 (x ⬝ᵥ (L *ᵥ x))) := by
    simp only [dotProduct, Matrix.mulVec]
    exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
      (tendsto_finsetSum _ fun j _ => (hE i j).mul tendsto_const_nhds)
  simpa using ge_of_tendsto' hq fun n => by simpa using (hu n).dotProduct_mulVec_nonneg x

/-- Subtracting a PSD multiple keeps the dissipativity constant. -/
private theorem dissipative_sub {A P : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hρ : 0 ≤ ρ)
    (hP : P.PosSemidef) (x : Fin d → ℝ) :
    x ⬝ᵥ (((A - ρ • P) + (A - ρ • P)ᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x) := by
  have hPs : Pᵀ = P := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.1
  have e : (A - ρ • P) + (A - ρ • P)ᵀ = (A + Aᵀ) - (2 * ρ) • P := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hPs, two_mul, add_smul]
    abel
  have h1 : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by simpa using hP.dotProduct_mulVec_nonneg x
  rw [e, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  nlinarith [hA x, mul_nonneg hρ h1]

/-- One Newton–Kleinman step: from `P ⪰ 0` solve the Lyapunov equation
`(A - ρ P) P' + P' (A - ρ P)ᵀ + ρ P² + Qn = 0` for `P' ⪰ 0`. -/
private theorem newton_step {A Qn P : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    (hQ : Qn.PosSemidef) (hP : P.PosSemidef) :
    ∃ P' : Matrix (Fin d) (Fin d) ℝ, P'.PosSemidef ∧
      (A - ρ • P) * P' + P' * (A - ρ • P)ᵀ + ρ • (P * P) + Qn = 0 := by
  have hB := dissipative_sub hA hρ hP
  have hPs : Pᵀ = P := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.1
  have hQs : Qnᵀ = Qn := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.1
  have hPP : (P * P).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self P
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hPs] at this
  have hC : (ρ • (P * P) + Qn).PosSemidef := (hPP.smul hρ).add hQ
  obtain ⟨X, hX⟩ := lyapunov_surjective hB hμ (-(ρ • (P * P) + Qn))
  have hCs : (-(ρ • (P * P) + Qn))ᵀ = -(ρ • (P * P) + Qn) := by
    rw [Matrix.transpose_neg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      hPs, hQs]
  have hXs := lyapunov_symm hB hμ hCs hX
  refine ⟨X, lyapunov_posSemidef hB hμ hXs hC hX, ?_⟩
  rw [add_assoc, hX, neg_add_cancel]

/-- Newton–Kleinman iterates decrease after the first step: with `S' = A - ρ P'`,
`S' (P' - P'') + (P' - P'') S'ᵀ = R(P') = -ρ (P' - P)²`. -/
private theorem newton_antitone {A Qn P P' P'' : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    (hP : P.PosSemidef) (hP' : P'.PosSemidef) (hP'' : P''.PosSemidef)
    (h1 : (A - ρ • P) * P' + P' * (A - ρ • P)ᵀ + ρ • (P * P) + Qn = 0)
    (h2 : (A - ρ • P') * P'' + P'' * (A - ρ • P')ᵀ + ρ • (P' * P') + Qn = 0) :
    (P' - P'').PosSemidef := by
  have hB := dissipative_sub hA hρ hP'
  have hPs : Pᵀ = P := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.1
  have hPs' : P'ᵀ = P' := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP'.1
  have hPs'' : P''ᵀ = P'' := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP''.1
  have hsub : ((P' - P'')ᵀ) = P' - P'' := by rw [Matrix.transpose_sub, hPs', hPs'']
  have hDs : (P' - P)ᵀ = P' - P := by rw [Matrix.transpose_sub, hPs', hPs]
  have hDD : ((P' - P) * (P' - P)).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (P' - P)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hDs] at this
  refine lyapunov_posSemidef hB hμ hsub (hDD.smul hρ) ?_
  have h3 : (A - ρ • P') * (P' - P'') + (P' - P'') * (A - ρ • P')ᵀ + ρ • ((P' - P) * (P' - P)) =
      ((A - ρ • P) * P' + P' * (A - ρ • P)ᵀ + ρ • (P * P) + Qn) -
        ((A - ρ • P') * P'' + P'' * (A - ρ • P')ᵀ + ρ • (P' * P') + Qn) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, hPs, hPs', Matrix.mul_sub,
      Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  rw [h1, h2, sub_zero] at h3
  exact eq_neg_of_add_eq_zero_left h3

/-- **Existence of the stationary covariance** by Newton–Kleinman iteration from `P₀ = 0`. -/
private theorem exists_stationary {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    (hQ : Qn.PosSemidef) :
    ∃ L : Matrix (Fin d) (Fin d) ℝ, L.PosSemidef ∧ A * L + L * Aᵀ - ρ • (L * L) + Qn = 0 := by
  let Psd := {P : Matrix (Fin d) (Fin d) ℝ // P.PosSemidef}
  have step : ∀ P : Psd, ∃ P' : Psd,
      (A - ρ • P.1) * P'.1 + P'.1 * (A - ρ • P.1)ᵀ + ρ • (P.1 * P.1) + Qn = 0 := fun P => by
    obtain ⟨P', h1, h2⟩ := newton_step hA hμ hρ hQ P.2
    exact ⟨⟨P', h1⟩, h2⟩
  choose next hnext using step
  let s : ℕ → Psd := fun n => next^[n] ⟨0, Matrix.PosSemidef.zero⟩
  have hs : ∀ n, s (n + 1) = next (s n) := fun n => Function.iterate_succ_apply' next n _
  have hN : ∀ n, (A - ρ • (s n).1) * (s (n + 1)).1 + (s (n + 1)).1 * (A - ρ • (s n).1)ᵀ +
      ρ • ((s n).1 * (s n).1) + Qn = 0 := fun n => by
    rw [hs n]
    exact hnext _
  obtain ⟨L, hLpsd, hL⟩ := exists_tendsto_of_antitone_posSemidef (u := fun n => (s (n + 1)).1)
    (fun n => (s (n + 1)).2)
    (fun n => newton_antitone hA hμ hρ (s n).2 (s (n + 1)).2 (s (n + 2)).2 (hN n) (hN (n + 1)))
  have hL0 : Tendsto (fun n => (s n).1) atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).1 hL
  have hmul : ∀ {X Y : ℕ → Matrix (Fin d) (Fin d) ℝ} {X' Y' : Matrix (Fin d) (Fin d) ℝ},
      Tendsto X atTop (𝓝 X') → Tendsto Y atTop (𝓝 Y') →
        Tendsto (fun n => X n * Y n) atTop (𝓝 (X' * Y')) := fun hX hY =>
    (Frobenius.mulCLM.continuous₂.tendsto (_, _)).comp (hX.prodMk_nhds hY)
  have htr : ∀ {X : ℕ → Matrix (Fin d) (Fin d) ℝ} {X' : Matrix (Fin d) (Fin d) ℝ},
      Tendsto X atTop (𝓝 X') → Tendsto (fun n => (X n)ᵀ) atTop (𝓝 X'ᵀ) := fun hX =>
    (Frobenius.transposeCLM.continuous.tendsto _).comp hX
  have hS : Tendsto (fun n => A - ρ • (s n).1) atTop (𝓝 (A - ρ • L)) :=
    tendsto_const_nhds.sub (hL0.const_smul ρ)
  have hlim := (((hmul hS hL).add (hmul hL (htr hS))).add ((hmul hL0 hL0).const_smul ρ)).add
    (tendsto_const_nhds (x := Qn))
  have h0 : (A - ρ • L) * L + L * (A - ρ • L)ᵀ + ρ • (L * L) + Qn = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp only [hN]
    exact tendsto_const_nhds
  have hLs : Lᵀ = L := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hLpsd.1
  refine ⟨L, hLpsd, ?_⟩
  rw [← h0, Matrix.transpose_sub, Matrix.transpose_smul, hLs]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  abel

/-- **Exponential attraction to the algebraic Riccati solution** (source: OP-SL-32,
dissipative special case; DRE paper Fig. 8).  For strictly dissipative drift (`μ < 0`),
`ρ ≥ 0` and PSD noise `Qn`, the algebraic Riccati equation `R(P) = 0` has a unique PSD solution
`P∞`, and every PSD solution of the Riccati ODE converges to it at rate `e^{μ t}`, independently
of the initial covariance. -/
theorem riccati_equilibrium_attracts {A Qn : Matrix (Fin d) (Fin d) ℝ} {ρ μ : ℝ}
    (hA : ∀ x : Fin d → ℝ, x ⬝ᵥ ((A + Aᵀ) *ᵥ x) ≤ μ * (x ⬝ᵥ x)) (hμ : μ < 0) (hρ : 0 ≤ ρ)
    (hQ : Qn.PosSemidef) :
    ∃ Pinf : Matrix (Fin d) (Fin d) ℝ, Pinf.PosSemidef ∧ riccatiField A ρ Qn 0 Pinf = 0 ∧
      (∀ P' : Matrix (Fin d) (Fin d) ℝ, P'.PosSemidef → riccatiField A ρ Qn 0 P' = 0 →
        P' = Pinf) ∧
      ∀ (P : ℝ → Matrix (Fin d) (Fin d) ℝ) (a b : ℝ), ODESolution (riccatiField A ρ Qn) P a b →
        (∀ t ∈ Icc a b, (P t).PosSemidef) →
        ∀ t ∈ Icc a b, ‖P t - Pinf‖ ≤ Real.exp (μ * (t - a)) * ‖P a - Pinf‖ := by
  obtain ⟨Pinf, hPSD, hR⟩ := exists_stationary hA hμ hρ hQ
  have e : riccatiField A ρ Qn 0 Pinf = 0 := hR
  refine ⟨Pinf, hPSD, e, fun P' hP' e' => ?_, fun P a b hP hpsd => ?_⟩
  · exact KalmanBucy.riccati_stationary_unique hA hμ hρ hP' hPSD e' e
  · exact KalmanBucy.riccati_attracts_stationary hA hρ hPSD e hP hpsd

end Riccati

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Adjoint

end LeanDLRA
