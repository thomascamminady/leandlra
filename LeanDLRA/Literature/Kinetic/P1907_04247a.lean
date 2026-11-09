import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Classical.SVD

/-!
# Results of arXiv 1907.04247: DLRA for linear Boltzmann in the diffusion limit

Ding, Einkemmer and Li analyse the projector-splitting integrator for the linear Boltzmann equation
at fixed mesh, `ε → 0`, by a formal Hilbert expansion.  This module proves their results
rigorously, for the fully discrete scheme: `IsIEStep` is Algorithm 2.1, (2.18), (2.21), (2.25), and
`IsCNIEStep` is Algorithm 2.2, (2.19), (2.22), (2.25), and nothing about the `ε`-dependence of the
factors is assumed beyond uniform bounds.  All implicit substeps have the common form
`Y + (τ/ε) ∑ₖ Gₖ Y Mₖ + (τ/ε²) W Y (1 - w wᵀ) = F`, and `stiff_main` is an a priori estimate for it,
with `Y = (Y w) wᵀ + O(ε)` and the limit equation `(1 - (τ/d) ∑ₖ Gₖ W⁻¹ Gₖ) (Y w) = F w + O(ε)`.
Proved: `theorem_3_2`, with `IsIELimit.rho_two_thirds` (3.26) and `IsIELimit.norm_sub_le` for the
error `O((Δt)² / (Δx)⁴)`, and `theorem_3_2_skew`; `theorem_3_3`, its strengthening
`theorem_3_3_unprepared`, and `cayley_cancel`; Lemma A.1 as `kernel_right_factor`,
`leading_order_L`, `leading_order_SK`, `lemma_A1`, `lemma_A1_K`; Lemma B.1 as `lemma_B1` and
`lemma_B1_IE`; and `Assumption1.capture`, `Capture.assumption1`: Assumption 1 is equivalent to
`e_n ∈ range V + O(ε²)`, `Π_k e_n ∈ range V + O(ε)`, which is all the proofs use of it.
Differences from the paper, also in the docstrings: the inverses of the limit operators are
hypotheses (`Stable`), and `theorem_3_2_counterexample` shows that they cannot be dropped:
Theorem 3.2, which puts no condition on `Δt`, is false as stated in one instance (`d = 1`, two
grid points, a skew `D` with `D² = -1`, `Δt = 1`, where `I + (Δt / d) 𝓛 = 0`); well-prepared
data are not needed in Theorem 3.3; the proof of Lemma B.1 replaces the one of the paper, which
treats only the first column of `A*_{∂_m}` after (B.15).  `exists_IEStep`, `exists_CNIEStep`,
`exists_IELimit` and `lemma_B1_hypotheses` show that the hypotheses can be met.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P1907_04247

open LeanDLRA Matrix

section Core

variable {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] {d : ℕ}

/-- The transport term `∑ₖ Gₖ Y Mₖ`. -/
noncomputable def transport (G : Fin d → Matrix m m ℝ) (M : Fin d → Matrix p p ℝ)
    (Y : Matrix m p ℝ) : Matrix m p ℝ := ∑ k, G k * Y * M k

/-- The limit operator `1 - (τ / d) ∑ₖ Gₖ W⁻¹ Gₖ`. -/
noncomputable def limitOp (G : Fin d → Matrix m m ℝ) (Winv : Matrix m m ℝ) (τ : ℝ) :
    Matrix m m ℝ := 1 - (τ / d) • ∑ k, G k * Winv * G k

/-- The common form of all implicit substeps. -/
def IsStiffSolution (G : Fin d → Matrix m m ℝ) (W : Matrix m m ℝ) (M : Fin d → Matrix p p ℝ)
    (w : Matrix p Unit ℝ) (τ ε : ℝ) (Y F : Matrix m p ℝ) : Prop :=
  Y + (τ / ε) • transport G M Y + (τ / ε ^ 2) • (W * Y * (1 - w * wᵀ)) = F

/-- The bounds under which the a priori estimate holds, at one value of `ε`. -/
structure StiffHyp (G : Fin d → Matrix m m ℝ) (W Winv : Matrix m m ℝ)
    (M : Fin d → Matrix p p ℝ) (w : Matrix p Unit ℝ) (g h h' μ ν c ε : ℝ) : Prop where
  inv : Winv * W = 1
  g0 : 0 ≤ g
  μ0 : 0 ≤ μ
  hG : ∀ k, ‖G k‖ ≤ g
  hWinv : ‖Winv‖ ≤ h
  hW : ‖W‖ ≤ h'
  hM : ∀ k, ‖M k‖ ≤ μ
  hw : ‖w‖ ≤ ν
  hδ : ‖(1 : Matrix Unit Unit ℝ) - wᵀ * w‖ ≤ c * ε ^ 3
  hm1 : ∀ k, ‖wᵀ * (M k * w)‖ ≤ c * ε ^ 2
  hm2 : ∀ j k, ‖wᵀ * (M j * (M k * w)) -
    (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)‖ ≤ c * ε

private theorem norm_mul3_le {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (A : Matrix a b ℝ) (B : Matrix b c ℝ) (C : Matrix c e ℝ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ :=
  (Frobenius.norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (Frobenius.norm_mul_le _ _) (norm_nonneg _))

private theorem stiff_Z {G : Fin d → Matrix m m ℝ} {W Winv : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε : ℝ} {Y F : Matrix m p ℝ}
    (hinv : Winv * W = 1) (hτ : τ ≠ 0) (hε : ε ≠ 0) (h : IsStiffSolution G W M w τ ε Y F) :
    Y * (1 - w * wᵀ) =
      (ε ^ 2 / τ) • (Winv * (F - Y)) - ε • (Winv * transport G M Y) := by
  have h1 : (τ / ε ^ 2) • (W * (Y * (1 - w * wᵀ))) = F - Y - (τ / ε) • transport G M Y := by
    rw [← h, Matrix.mul_assoc]; abel
  have h2 : Winv * ((τ / ε ^ 2) • (W * (Y * (1 - w * wᵀ)))) =
      (τ / ε ^ 2) • (Y * (1 - w * wᵀ)) := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  rw [h1, Matrix.mul_sub, Matrix.mul_smul] at h2
  have h3 := congrArg (fun A => (ε ^ 2 / τ) • A) h2
  simp only [smul_smul, smul_sub] at h3
  have e1 : ε ^ 2 / τ * (τ / ε ^ 2) = 1 := by field_simp
  have e2 : ε ^ 2 / τ * (τ / ε) = ε := by field_simp
  rw [e1, e2, one_smul] at h3
  exact h3.symm

omit [DecidableEq m] in
private theorem stiff_w {G : Fin d → Matrix m m ℝ} {W : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε : ℝ} {Y F : Matrix m p ℝ}
    (h : IsStiffSolution G W M w τ ε Y F) :
    Y * w + (τ / ε) • (transport G M Y * w) + (τ / ε ^ 2) • (W * (Y * w) * (1 - wᵀ * w)) =
      F * w := by
  have h1 := congrArg (· * w) h
  simp only [Matrix.add_mul, Matrix.smul_mul] at h1
  have e : W * Y * (1 - w * wᵀ) * w = W * (Y * w) * (1 - wᵀ * w) := by
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]
  rwa [e] at h1

omit [DecidableEq m] in
private theorem split_mul (G : Matrix m m ℝ) (Y : Matrix m p ℝ) (w x : Matrix p Unit ℝ) :
    G * Y * x = G * (Y * w) * (wᵀ * x) + G * (Y * (1 - w * wᵀ)) * x := by
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one]
  abel

private theorem stiff_identity {G : Fin d → Matrix m m ℝ} {W Winv : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε : ℝ} {Y F : Matrix m p ℝ}
    (hinv : Winv * W = 1) (hτ : τ ≠ 0) (hε : ε ≠ 0) (h : IsStiffSolution G W M w τ ε Y F) :
    limitOp G Winv τ * (Y * w) - F * w =
      - ((τ / ε ^ 2) • (W * (Y * w) * (1 - wᵀ * w)))
      - (τ / ε) • (∑ k, G k * (Y * w) * (wᵀ * (M k * w)))
      - ε • (∑ k, G k * Winv * (F - Y) * (M k * w))
      + τ • (∑ k, ∑ j, G k * Winv * G j * (Y * w) * (wᵀ * (M j * (M k * w)) -
          (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)))
      + τ • (∑ k, ∑ j, G k * Winv * (G j * (Y * (1 - w * wᵀ)) * (M j * (M k * w)))) := by
  set Z := Y * (1 - w * wᵀ) with hZ
  set R1 := ∑ k, G k * (Y * w) * (wᵀ * (M k * w)) with hR1
  set R2 := ∑ k, G k * Winv * (F - Y) * (M k * w) with hR2
  set R3 := ∑ k, ∑ j, G k * Winv * G j * (Y * w) * (wᵀ * (M j * (M k * w)) -
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) with hR3
  set R4 := ∑ k, ∑ j, G k * Winv * (G j * Z * (M j * (M k * w))) with hR4
  set B := ∑ k, G k * Winv * G k with hB
  -- step a
  have ha : transport G M Y * w = R1 + ∑ k, G k * Z * (M k * w) := by
    rw [hR1, ← Finset.sum_add_distrib, transport, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc (G k * Y)]
    exact split_mul _ _ _ _
  -- step c
  have hc : ∀ k, transport G M Y * (M k * w) =
      ∑ j, (G j * (Y * w) * (wᵀ * (M j * (M k * w))) + G j * Z * (M j * (M k * w))) := by
    intro k
    rw [transport, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_assoc (G j * Y)]
    exact split_mul _ _ _ _
  have hb : ∑ k, G k * Winv * (transport G M Y * (M k * w)) =
      (d : ℝ)⁻¹ • (B * (Y * w)) + R3 + R4 := by
    have e1 : ∀ k, G k * Winv * (transport G M Y * (M k * w)) =
        (d : ℝ)⁻¹ • ((G k * Winv * G k) * (Y * w)) +
        ∑ j, G k * Winv * G j * (Y * w) * (wᵀ * (M j * (M k * w)) -
          (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) +
        ∑ j, G k * Winv * (G j * Z * (M j * (M k * w))) := by
      intro k
      rw [hc, Matrix.mul_sum]
      have e2 : ∀ j, G k * Winv * (G j * (Y * w) * (wᵀ * (M j * (M k * w))) +
            G j * Z * (M j * (M k * w))) =
          (if j = k then ((d : ℝ)⁻¹) else 0) • ((G k * Winv * G j) * (Y * w)) +
          G k * Winv * G j * (Y * w) * (wᵀ * (M j * (M k * w)) -
            (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) +
          G k * Winv * (G j * Z * (M j * (M k * w))) := by
        intro j
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
      simp only [e2, Finset.sum_add_distrib]
      congr 2
      simp [ite_smul]
    simp only [e1, Finset.sum_add_distrib, hR3, hR4, hB, Matrix.sum_mul, Finset.smul_sum]
  have hS : ∑ k, G k * Z * (M k * w) =
      (ε ^ 2 / τ) • R2 - ε • ∑ k, G k * Winv * (transport G M Y * (M k * w)) := by
    rw [hR2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hZ, stiff_Z hinv hτ hε h]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have hw := stiff_w h
  rw [ha, hS, hb] at hw
  have hlim : limitOp G Winv τ * (Y * w) = Y * w - τ • ((d : ℝ)⁻¹ • (B * (Y * w))) := by
    rw [limitOp, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, smul_smul, div_eq_mul_inv]
  rw [hlim, ← hw]
  have e1 : (τ / ε) * (ε ^ 2 / τ) = ε := by field_simp
  have e2 : (τ / ε) * ε = τ := by field_simp
  have e3 : ∀ x : ℝ, τ / ε * (ε * x) = τ * x := fun x => by field_simp
  simp only [smul_add, smul_sub, smul_smul, e1, e2, e3]
  abel

private theorem norm_sum_fin_le {E : Type*} [SeminormedAddCommGroup E] {f : Fin d → E} {b : ℝ}
    (h : ∀ k, ‖f k‖ ≤ b) : ‖∑ k, f k‖ ≤ d * b := by
  refine (norm_sum_le_of_le _ fun k _ => h k).trans (le_of_eq ?_)
  simp

/-- The constant of the first-order remainder. -/
noncomputable def stiffA₁ (d : ℕ) (τ g h μ : ℝ) : ℝ := h / |τ| + h * d * g * μ

/-- The constant of the limit equation. -/
noncomputable def stiffA₂ (d : ℕ) (τ g h h' μ ν c : ℝ) : ℝ :=
  |τ| * h' * ν * c + |τ| * d * g * ν * c + d * g * h * μ * ν + |τ| * d * d * g * h * g * ν * c +
    |τ| * d * d * g * h * g * μ * μ * ν * stiffA₁ d τ g h μ

/-- The constant of the second-order remainder. -/
noncomputable def stiffA₃ (d : ℕ) (τ g h μ : ℝ) : ℝ :=
  h / |τ| + d * h * g * μ * stiffA₁ d τ g h μ

private theorem stiff_estimate {G : Fin d → Matrix m m ℝ} {W Winv : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε g h h' μ ν c : ℝ} {Y F : Matrix m p ℝ}
    (hτ : τ ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) (hH : StiffHyp G W Winv M w g h h' μ ν c ε)
    (hs : IsStiffSolution G W M w τ ε Y F) :
    ‖Y * (1 - w * wᵀ)‖ ≤ ε * stiffA₁ d τ g h μ * (‖F‖ + ‖Y‖) ∧
    ‖limitOp G Winv τ * (Y * w) - F * w‖ ≤ ε * stiffA₂ d τ g h h' μ ν c * (‖F‖ + ‖Y‖) ∧
    ‖Y * (1 - w * wᵀ) + ε • ∑ k, Winv * G k * (Y * w) * wᵀ * M k‖ ≤
      ε ^ 2 * stiffA₃ d τ g h μ * (‖F‖ + ‖Y‖) := by
  obtain ⟨hinv, hg0, hμ0, hG, hWinv, hW, hM, hw, hδ, hm1, hm2⟩ := hH
  have hτ' : 0 < |τ| := abs_pos.mpr hτ
  have hε0 : ε ≠ 0 := hε.ne'
  set D : ℝ := (d : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg d
  have hh0 : 0 ≤ h := (norm_nonneg _).trans hWinv
  have hh'0 : 0 ≤ h' := (norm_nonneg _).trans hW
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans hw
  have hc0 : 0 ≤ c := by
    have := (norm_nonneg _).trans hδ
    have h3 : 0 < ε ^ 3 := by positivity
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith
  set N := ‖F‖ + ‖Y‖ with hN
  have hYN : ‖Y‖ ≤ N := le_add_of_nonneg_left (norm_nonneg F)
  have hN0 : 0 ≤ N := (norm_nonneg Y).trans hYN
  have hFY : ‖F - Y‖ ≤ N := norm_sub_le _ _
  set l := Y * w with hl
  have hlN : ‖l‖ ≤ N * ν :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hYN hw (norm_nonneg _) hN0)
  have hT : ‖Winv * transport G M Y‖ ≤ h * (D * g * μ) * N := by
    have h1 : ‖transport G M Y‖ ≤ D * (g * N * μ) := by
      refine norm_sum_fin_le fun k => (norm_mul3_le _ _ _).trans ?_
      have := hG k
      have := hM k
      gcongr
    refine (Frobenius.norm_mul_le _ _).trans ((mul_le_mul hWinv h1 (norm_nonneg _) hh0).trans ?_)
    exact le_of_eq (by ring)
  have hZe := stiff_Z hinv hτ hε0 hs
  set Z := Y * (1 - w * wᵀ) with hZdef
  set A₁ := stiffA₁ d τ g h μ with hA₁
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁, stiffA₁]; positivity
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hFst : ‖(ε ^ 2 / τ) • (Winv * (F - Y))‖ ≤ ε ^ 2 * (h / |τ|) * N := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ε ^ 2)]
    have h1 : ‖Winv * (F - Y)‖ ≤ h * N :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul hWinv hFY (norm_nonneg _) hh0)
    calc ε ^ 2 / |τ| * ‖Winv * (F - Y)‖ ≤ ε ^ 2 / |τ| * (h * N) := by gcongr
      _ = _ := by field_simp
  have hZ : ‖Z‖ ≤ ε * A₁ * N := by
    rw [hZe]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul (ε) (Winv * transport G M Y), Real.norm_eq_abs, abs_of_pos hε]
    have h2 : ε ^ 2 * (h / |τ|) * N ≤ ε * (h / |τ|) * N := by gcongr
    have h3 : ε * ‖Winv * transport G M Y‖ ≤ ε * (h * (D * g * μ) * N) := by gcongr
    have h4 : ε * A₁ * N = ε * (h / |τ|) * N + ε * (h * (D * g * μ) * N) := by
      rw [hA₁, stiffA₁]; ring
    rw [h4]
    linarith
  refine ⟨hZ, ?_, ?_⟩
  · rw [stiff_identity hinv hτ hε0 hs]
    have t1 : ‖(τ / ε ^ 2) • (W * l * (1 - wᵀ * w))‖ ≤ ε * (|τ| * h' * ν * c) * N := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ε ^ 2)]
      have h1 : ‖W * l * (1 - wᵀ * w)‖ ≤ h' * (N * ν) * (c * ε ^ 3) := by
        refine (norm_mul3_le _ _ _).trans ?_
        gcongr
      calc |τ| / ε ^ 2 * ‖W * l * (1 - wᵀ * w)‖ ≤ |τ| / ε ^ 2 * (h' * (N * ν) * (c * ε ^ 3)) := by
            gcongr
        _ = _ := by field_simp
    have t2 : ‖(τ / ε) • (∑ k, G k * l * (wᵀ * (M k * w)))‖ ≤ ε * (|τ| * D * g * ν * c) * N := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hε]
      have h1 : ‖∑ k, G k * l * (wᵀ * (M k * w))‖ ≤ D * (g * (N * ν) * (c * ε ^ 2)) := by
        refine norm_sum_fin_le fun k => (norm_mul3_le _ _ _).trans ?_
        have := hG k
        have := hm1 k
        gcongr
      calc |τ| / ε * ‖∑ k, G k * l * (wᵀ * (M k * w))‖ ≤
            |τ| / ε * (D * (g * (N * ν) * (c * ε ^ 2))) := by gcongr
        _ = _ := by field_simp
    have t3 : ‖ε • (∑ k, G k * Winv * (F - Y) * (M k * w))‖ ≤ ε * (D * g * h * μ * ν) * N := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      have h1 : ‖∑ k, G k * Winv * (F - Y) * (M k * w)‖ ≤ D * (g * h * N * (μ * ν)) := by
        refine norm_sum_fin_le fun k => (norm_mul3_le _ _ _).trans ?_
        have h2 : ‖G k * Winv‖ ≤ g * h :=
          (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hG k) hWinv (norm_nonneg _) hg0)
        have h3 : ‖M k * w‖ ≤ μ * ν :=
          (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hM k) hw (norm_nonneg _) hμ0)
        gcongr
      calc ε * ‖∑ k, G k * Winv * (F - Y) * (M k * w)‖ ≤ ε * (D * (g * h * N * (μ * ν))) := by
            gcongr
        _ = _ := by ring
    have hGWG : ∀ k j, ‖G k * Winv * G j‖ ≤ g * h * g := fun k j => by
      refine (norm_mul3_le _ _ _).trans ?_
      have := hG k
      have := hG j
      gcongr
    have t4 : ‖τ • (∑ k, ∑ j, G k * Winv * G j * l * (wᵀ * (M j * (M k * w)) -
        (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)))‖ ≤
        ε * (|τ| * D * D * g * h * g * ν * c) * N := by
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : ‖∑ k, ∑ j, G k * Winv * G j * l * (wᵀ * (M j * (M k * w)) -
          (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ))‖ ≤
          D * (D * (g * h * g * (N * ν) * (c * ε))) := by
        refine norm_sum_fin_le fun k => norm_sum_fin_le fun j => (norm_mul3_le _ _ _).trans ?_
        have := hGWG k j
        have := hm2 j k
        gcongr
      calc _ ≤ |τ| * (D * (D * (g * h * g * (N * ν) * (c * ε)))) := by gcongr
        _ = _ := by ring
    have t5 : ‖τ • (∑ k, ∑ j, G k * Winv * (G j * Z * (M j * (M k * w))))‖ ≤
        ε * (|τ| * D * D * g * h * g * μ * μ * ν * A₁) * N := by
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : ‖∑ k, ∑ j, G k * Winv * (G j * Z * (M j * (M k * w)))‖ ≤
          D * (D * (g * h * (g * (ε * A₁ * N) * (μ * (μ * ν))))) := by
        refine norm_sum_fin_le fun k => norm_sum_fin_le fun j =>
          (Frobenius.norm_mul_le _ _).trans ?_
        have h2 : ‖G k * Winv‖ ≤ g * h :=
          (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hG k) hWinv (norm_nonneg _) hg0)
        have h3 : ‖M j * (M k * w)‖ ≤ μ * (μ * ν) := by
          refine (Frobenius.norm_mul_le _ _).trans ?_
          have h4 : ‖M k * w‖ ≤ μ * ν :=
            (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hM k) hw (norm_nonneg _) hμ0)
          exact mul_le_mul (hM j) h4 (norm_nonneg _) hμ0
        have h5 : ‖G j * Z * (M j * (M k * w))‖ ≤ g * (ε * A₁ * N) * (μ * (μ * ν)) := by
          refine (norm_mul3_le _ _ _).trans ?_
          have := hG j
          gcongr
        gcongr
      calc _ ≤ |τ| * (D * (D * (g * h * (g * (ε * A₁ * N) * (μ * (μ * ν)))))) := by gcongr
        _ = _ := by ring
    have hsum : ε * stiffA₂ d τ g h h' μ ν c * N =
        ε * (|τ| * h' * ν * c) * N + ε * (|τ| * D * g * ν * c) * N +
        ε * (D * g * h * μ * ν) * N + ε * (|τ| * D * D * g * h * g * ν * c) * N +
        ε * (|τ| * D * D * g * h * g * μ * μ * ν * A₁) * N := by
      rw [stiffA₂]; ring
    rw [hsum]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ?_ t2)) t3)) t4)) t5)
    rw [norm_neg]
    exact t1
  · have e1 : Winv * transport G M Y = (∑ k, Winv * G k * l * wᵀ * M k) +
        ∑ k, Winv * (G k * Z * M k) := by
      rw [transport, Matrix.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Y = l * wᵀ + Z := by
        rw [hZdef, hl]
        simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
        abel
      calc Winv * (G k * Y * M k) = Winv * (G k * (l * wᵀ + Z) * M k) := by rw [← this]
        _ = _ := by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    have e2 : Z + ε • ∑ k, Winv * G k * l * wᵀ * M k =
        (ε ^ 2 / τ) • (Winv * (F - Y)) - ε • ∑ k, Winv * (G k * Z * M k) := by
      have h3 := hZe
      rw [e1, smul_add] at h3
      calc Z + ε • ∑ k, Winv * G k * l * wᵀ * M k
          = (ε ^ 2 / τ) • (Winv * (F - Y)) - (ε • ∑ k, Winv * G k * l * wᵀ * M k +
              ε • ∑ k, Winv * (G k * Z * M k)) + ε • ∑ k, Winv * G k * l * wᵀ * M k :=
            congrArg (· + ε • ∑ k, Winv * G k * l * wᵀ * M k) h3
        _ = _ := by abel
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul ε, Real.norm_eq_abs, abs_of_pos hε]
    have h1 : ‖∑ k, Winv * (G k * Z * M k)‖ ≤ D * (h * (g * (ε * A₁ * N) * μ)) := by
      refine norm_sum_fin_le fun k => (Frobenius.norm_mul_le _ _).trans ?_
      have h5 : ‖G k * Z * M k‖ ≤ g * (ε * A₁ * N) * μ := by
        refine (norm_mul3_le _ _ _).trans ?_
        have := hG k
        have := hM k
        gcongr
      gcongr
    have h2 : ε * ‖∑ k, Winv * (G k * Z * M k)‖ ≤ ε * (D * (h * (g * (ε * A₁ * N) * μ))) := by
      gcongr
    have h3 : ε ^ 2 * stiffA₃ d τ g h μ * N =
        ε ^ 2 * (h / |τ|) * N + ε * (D * (h * (g * (ε * A₁ * N) * μ))) := by
      rw [stiffA₃]; ring
    rw [h3]
    linarith

private theorem stiff_bound {G : Fin d → Matrix m m ℝ} {W Winv : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε g h h' μ ν c b : ℝ}
    {Y F : Matrix m p ℝ}
    (hτ : τ ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) (hH : StiffHyp G W Winv M w g h h' μ ν c ε)
    (hb : 0 ≤ b) (hstab : ∀ x : Matrix m Unit ℝ, ‖x‖ ≤ b * ‖limitOp G Winv τ * x‖)
    (hsmall : ε * (b * ν * stiffA₂ d τ g h h' μ ν c + stiffA₁ d τ g h μ) ≤ 1 / 2)
    (hs : IsStiffSolution G W M w τ ε Y F) :
    ‖Y‖ ≤ (2 * b * ν ^ 2 + 1) * ‖F‖ := by
  obtain ⟨hZ, hL, -⟩ := stiff_estimate hτ hε hε1 hH hs
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans hH.hw
  set A₁ := stiffA₁ d τ g h μ
  set A₂ := stiffA₂ d τ g h h' μ ν c
  set N := ‖F‖ + ‖Y‖ with hN
  have hN0 : 0 ≤ N := by positivity
  have h1 : ‖Y * w‖ ≤ b * (‖F‖ * ν + ε * A₂ * N) := by
    refine (hstab _).trans ?_
    have h2 : ‖limitOp G Winv τ * (Y * w)‖ ≤ ‖F * w‖ + ε * A₂ * N := by
      have := norm_sub_norm_le (limitOp G Winv τ * (Y * w)) (F * w)
      linarith
    have h3 : ‖F * w‖ ≤ ‖F‖ * ν :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hH.hw (norm_nonneg _))
    gcongr
    linarith
  have hdec : Y = Y * w * wᵀ + Y * (1 - w * wᵀ) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have h2 : ‖Y‖ ≤ ‖Y * w‖ * ν + ε * A₁ * N := by
    calc ‖Y‖ = ‖Y * w * wᵀ + Y * (1 - w * wᵀ)‖ := by rw [← hdec]
      _ ≤ ‖Y * w * wᵀ‖ + ‖Y * (1 - w * wᵀ)‖ := norm_add_le _ _
      _ ≤ ‖Y * w‖ * ν + ε * A₁ * N := by
        refine add_le_add ((Frobenius.norm_mul_le _ _).trans ?_) hZ
        rw [Frobenius.norm_transpose]
        exact mul_le_mul_of_nonneg_left hH.hw (norm_nonneg _)
  have h3 : ‖Y‖ ≤ b * ν ^ 2 * ‖F‖ + ε * (b * ν * A₂ + A₁) * N := by
    have : ‖Y * w‖ * ν ≤ b * (‖F‖ * ν + ε * A₂ * N) * ν := by gcongr
    nlinarith
  have h4 : ε * (b * ν * A₂ + A₁) * N ≤ 1 / 2 * N := by gcongr
  have h5 : ‖Y‖ ≤ b * ν ^ 2 * ‖F‖ + 1 / 2 * (‖F‖ + ‖Y‖) := h3.trans (by linarith)
  nlinarith

/-- **The a priori estimate of the implicit substeps.**  Fix bounds.  There are `C, ε₀` such that
for every `ε < ε₀` and every solution `Y` of `Y + (τ/ε) ∑ₖ Gₖ Y Mₖ + (τ/ε²) W Y (1 - w wᵀ) = F`:
`‖Y‖ ≲ ‖F‖`, `Y = (Y w) wᵀ + O(ε)`, the limit equation `T (Y w) = F w + O(ε)` holds, and
`Y = (Y w) wᵀ - ε ∑ₖ W⁻¹ Gₖ (Y w) wᵀ Mₖ + O(ε²)`.  The bound `2 b ν² + 1` does not depend on
`τ`. -/
theorem stiff_main (d : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (g h h' μ ν c b : ℝ) (hb : 0 ≤ b) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (G : Fin d → Matrix m m ℝ) (W Winv : Matrix m m ℝ) (M : Fin d → Matrix p p ℝ)
        (w : Matrix p Unit ℝ) (Y F : Matrix m p ℝ),
        StiffHyp G W Winv M w g h h' μ ν c ε →
        (∀ x : Matrix m Unit ℝ, ‖x‖ ≤ b * ‖limitOp G Winv τ * x‖) →
        IsStiffSolution G W M w τ ε Y F →
        ‖Y‖ ≤ (2 * b * ν ^ 2 + 1) * ‖F‖ ∧
        ‖Y - Y * w * wᵀ‖ ≤ C * ε * ‖F‖ ∧
        ‖limitOp G Winv τ * (Y * w) - F * w‖ ≤ C * ε * ‖F‖ ∧
        ‖Y - Y * w * wᵀ + ε • ∑ k, Winv * G k * (Y * w) * wᵀ * M k‖ ≤ C * ε ^ 2 * ‖F‖ := by
  set A₁ := |stiffA₁ d τ g h μ|
  set A₂ := |stiffA₂ d τ g h h' μ ν c|
  set A₃ := |stiffA₃ d τ g h μ|
  set C₀ := 2 * b * ν ^ 2 + 2 with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  set K := b * |ν| * A₂ + A₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(A₁ + A₂ + A₃) * C₀, min 1 (1 / (2 * K + 1)), by positivity,
    lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro ε hε hε0 G W Winv M w Y F hH hstab hs
  have hε1 : ε ≤ 1 := (hε0.trans_le (min_le_left _ _)).le
  have hν : 0 ≤ ν := (norm_nonneg _).trans hH.hw
  have hsmall : ε * (b * ν * stiffA₂ d τ g h h' μ ν c + stiffA₁ d τ g h μ) ≤ 1 / 2 := by
    have h1 : ε < 1 / (2 * K + 1) := hε0.trans_le (min_le_right _ _)
    have h2 : b * ν * stiffA₂ d τ g h h' μ ν c + stiffA₁ d τ g h μ ≤ K := by
      rw [hK, abs_of_nonneg hν]
      have := le_abs_self (stiffA₂ d τ g h h' μ ν c)
      have := le_abs_self (stiffA₁ d τ g h μ)
      gcongr
    have h3 : ε * (2 * K + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hY := stiff_bound hτ hε hε1 hH hb hstab hsmall hs
  obtain ⟨hZ, hL, hS⟩ := stiff_estimate hτ hε hε1 hH hs
  have hN : ‖F‖ + ‖Y‖ ≤ C₀ * ‖F‖ := by rw [hC₀]; nlinarith [norm_nonneg F]
  have hdec : Y - Y * w * wᵀ = Y * (1 - w * wᵀ) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hA₁ := le_abs_self (stiffA₁ d τ g h μ)
  have hA₂ := le_abs_self (stiffA₂ d τ g h h' μ ν c)
  have hA₃ := le_abs_self (stiffA₃ d τ g h μ)
  have hA₁0 : 0 ≤ A₁ := abs_nonneg _
  have hA₂0 : 0 ≤ A₂ := abs_nonneg _
  have hA₃0 : 0 ≤ A₃ := abs_nonneg _
  have hF := norm_nonneg F
  have hN0 : 0 ≤ ‖F‖ + ‖Y‖ := by positivity
  refine ⟨hY, ?_, ?_, ?_⟩
  · rw [hdec]
    calc _ ≤ ε * stiffA₁ d τ g h μ * (‖F‖ + ‖Y‖) := hZ
      _ ≤ ε * A₁ * (C₀ * ‖F‖) := by gcongr
      _ ≤ (A₁ + A₂ + A₃) * C₀ * ε * ‖F‖ := by
        have : 0 ≤ (A₂ + A₃) * C₀ * ε * ‖F‖ := by positivity
        nlinarith
  · calc _ ≤ ε * stiffA₂ d τ g h h' μ ν c * (‖F‖ + ‖Y‖) := hL
      _ ≤ ε * A₂ * (C₀ * ‖F‖) := by gcongr
      _ ≤ (A₁ + A₂ + A₃) * C₀ * ε * ‖F‖ := by
        have : 0 ≤ (A₁ + A₃) * C₀ * ε * ‖F‖ := by positivity
        nlinarith
  · rw [hdec]
    calc _ ≤ ε ^ 2 * stiffA₃ d τ g h μ * (‖F‖ + ‖Y‖) := hS
      _ ≤ ε ^ 2 * A₃ * (C₀ * ‖F‖) := by gcongr
      _ ≤ (A₁ + A₂ + A₃) * C₀ * ε ^ 2 * ‖F‖ := by
        have : 0 ≤ (A₁ + A₂) * C₀ * ε ^ 2 * ‖F‖ := by positivity
        nlinarith

end Core

section Moments

variable {n q : Type*} [Fintype n] [Fintype q] [DecidableEq q] {d : ℕ}

private theorem norm_tmm_le {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (x : Matrix a Unit ℝ) (A : Matrix a b ℝ) (y : Matrix b c ℝ) :
    ‖xᵀ * (A * y)‖ ≤ ‖x‖ * ‖A‖ * ‖y‖ := by
  refine (Frobenius.norm_mul_le _ _).trans ?_
  rw [Frobenius.norm_transpose, mul_assoc]
  exact mul_le_mul_of_nonneg_left (Frobenius.norm_mul_le _ _) (norm_nonneg _)

/-- A matrix with orthonormal columns has squared Frobenius norm equal to the number of columns. -/
theorem norm_sq_of_orthonormal {V : Matrix n q ℝ} (hV : Vᵀ * V = 1) :
    ‖V‖ ^ 2 = Fintype.card q := by
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, hV, Matrix.trace_one]

private theorem moments_capture {π : Fin d → Matrix n n ℝ} {e : Matrix n Unit ℝ}
    {V : Matrix n q ℝ} {μ C p₀ ε : ℝ} (hV : Vᵀ * V = 1) (he : eᵀ * e = 1) (hen : ‖e‖ ≤ 1)
    (hm1 : ∀ k, eᵀ * (π k * e) = 0)
    (hm2 : ∀ j k, eᵀ * (π j * (π k * e)) =
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ))
    (hμ : ∀ k, ‖π k‖ ≤ μ) (hμ0 : 0 ≤ μ) (hC0 : 0 ≤ C) (hp : ‖V * Vᵀ‖ ≤ p₀) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hc1 : ‖e - V * (Vᵀ * e)‖ ≤ C * ε ^ 2)
    (hc2 : ∀ k, ‖π k * e - V * (Vᵀ * (π k * e))‖ ≤ C * ε) :
    ‖(1 : Matrix Unit Unit ℝ) - (Vᵀ * e)ᵀ * (Vᵀ * e)‖ ≤ C ^ 2 * ε ^ 3 ∧
    (∀ k, ‖(Vᵀ * e)ᵀ * ((Vᵀ * π k * V) * (Vᵀ * e))‖ ≤ (2 * μ * C + μ * C ^ 2) * ε ^ 2) ∧
    ∀ j k, ‖(Vᵀ * e)ᵀ * ((Vᵀ * π j * V) * ((Vᵀ * π k * V) * (Vᵀ * e))) -
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)‖ ≤
      (μ * C + μ * p₀ * μ * C + C * μ * μ + C ^ 2 * μ + C ^ 2 * μ ^ 2 * p₀) * ε := by
  generalize hα : Vᵀ * e = α at *
  obtain ⟨r, hr⟩ : ∃ r, r = e - V * α := ⟨_, rfl⟩
  rw [← hr] at hc1
  have hp0 : 0 ≤ p₀ := (norm_nonneg _).trans hp
  have ha : V * α = e - r := by rw [hr]; abel
  have ht : (V * α)ᵀ = αᵀ * Vᵀ := Matrix.transpose_mul _ _
  have hαt : αᵀ = eᵀ * V := by rw [← hα, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hrn : ‖r‖ ≤ C * ε ^ 2 := hc1
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 2 ≤ 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (1 : Matrix Unit Unit ℝ) - αᵀ * α = rᵀ * r := by
      have e1 : eᵀ * (V * α) = αᵀ * α := by rw [hαt, Matrix.mul_assoc]
      have e2 : (V * α)ᵀ * e = αᵀ * α := by rw [ht, Matrix.mul_assoc, hα]
      have e3 : (V * α)ᵀ * (V * α) = αᵀ * α := by
        rw [ht, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
      rw [hr, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, he, e1, e2, e3]
      abel
    rw [h1]
    calc ‖rᵀ * r‖ ≤ ‖rᵀ‖ * ‖r‖ := Frobenius.norm_mul_le _ _
      _ = ‖r‖ * ‖r‖ := by rw [Frobenius.norm_transpose]
      _ ≤ (C * ε ^ 2) * (C * ε ^ 2) := by gcongr
      _ = C ^ 2 * ε ^ 3 * ε := by ring
      _ ≤ C ^ 2 * ε ^ 3 * 1 := by gcongr
      _ = _ := mul_one _
  · intro k
    have h1 : αᵀ * ((Vᵀ * π k * V) * α) = (V * α)ᵀ * (π k * (V * α)) := by
      rw [ht]; simp only [Matrix.mul_assoc]
    have h2 : (V * α)ᵀ * (π k * (V * α)) =
        - (eᵀ * (π k * r)) - (rᵀ * (π k * e)) + rᵀ * (π k * r) := by
      rw [ha, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_sub,
        hm1]
      abel
    rw [h1, h2]
    have t1 : ‖eᵀ * (π k * r)‖ ≤ 1 * μ * (C * ε ^ 2) := by
      refine (norm_tmm_le _ _ _).trans ?_
      have := hμ k
      gcongr
    have t2 : ‖rᵀ * (π k * e)‖ ≤ (C * ε ^ 2) * μ * 1 := by
      refine (norm_tmm_le _ _ _).trans ?_
      have := hμ k
      gcongr
    have t3 : ‖rᵀ * (π k * r)‖ ≤ (C * ε ^ 2) * μ * (C * ε ^ 2) := by
      refine (norm_tmm_le _ _ _).trans ?_
      have := hμ k
      gcongr
    have t4 : (C * ε ^ 2) * μ * (C * ε ^ 2) ≤ (C * ε ^ 2) * μ * (C * 1) := by gcongr
    calc _ ≤ ‖eᵀ * (π k * r)‖ + ‖rᵀ * (π k * e)‖ + ‖rᵀ * (π k * r)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
          rw [norm_neg]
      _ ≤ _ := by nlinarith
  · intro j k
    obtain ⟨P, hP⟩ : ∃ P, P = V * Vᵀ := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, s = π k * e - V * (Vᵀ * (π k * e)) := ⟨_, rfl⟩
    rw [← hP] at hp
    have h1 : αᵀ * ((Vᵀ * π j * V) * ((Vᵀ * π k * V) * α)) =
        (V * α)ᵀ * (π j * (P * (π k * (V * α)))) := by
      rw [ht, hP]; simp only [Matrix.mul_assoc]
    have hPe : P * (π k * e) = π k * e - s := by
      rw [hs, hP, Matrix.mul_assoc]; abel
    have h2 : (V * α)ᵀ * (π j * (P * (π k * (V * α)))) -
        (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ) =
        - (eᵀ * (π j * s)) - (eᵀ * (π j * (P * (π k * r)))) - rᵀ * (π j * (π k * e)) +
          rᵀ * (π j * s) + rᵀ * (π j * (P * (π k * r))) := by
      rw [ha, Matrix.transpose_sub, Matrix.sub_mul]
      simp only [Matrix.mul_sub, hPe]
      rw [hm2 j k]
      abel
    rw [h1, h2]
    have hsn : ‖s‖ ≤ C * ε := by rw [hs]; exact hc2 k
    have hπj := hμ j
    have hπk := hμ k
    have hA : ‖π j * (P * π k)‖ ≤ μ * (p₀ * μ) := by
      refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul hπj ?_ (norm_nonneg _) hμ0)
      exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul hp hπk (norm_nonneg _) hp0)
    have hAe : π j * (P * (π k * r)) = (π j * (P * π k)) * r := by
      simp only [Matrix.mul_assoc]
    have t1 : ‖eᵀ * (π j * s)‖ ≤ 1 * μ * (C * ε) := by
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have t2 : ‖eᵀ * (π j * (P * (π k * r)))‖ ≤ 1 * (μ * (p₀ * μ)) * (C * ε ^ 2) := by
      rw [hAe]
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have t3 : ‖rᵀ * (π j * (π k * e))‖ ≤ (C * ε ^ 2) * (μ * μ) * 1 := by
      rw [← Matrix.mul_assoc (π j)]
      refine (norm_tmm_le _ _ _).trans ?_
      have : ‖π j * π k‖ ≤ μ * μ :=
        (Frobenius.norm_mul_le _ _).trans (mul_le_mul hπj hπk (norm_nonneg _) hμ0)
      gcongr
    have t4 : ‖rᵀ * (π j * s)‖ ≤ (C * ε ^ 2) * μ * (C * ε) := by
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have t5 : ‖rᵀ * (π j * (P * (π k * r)))‖ ≤ (C * ε ^ 2) * (μ * (p₀ * μ)) * (C * ε ^ 2) := by
      rw [hAe]
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have h3 : ‖- (eᵀ * (π j * s)) - (eᵀ * (π j * (P * (π k * r)))) - rᵀ * (π j * (π k * e)) +
          rᵀ * (π j * s) + rᵀ * (π j * (P * (π k * r)))‖ ≤
        ‖eᵀ * (π j * s)‖ + ‖eᵀ * (π j * (P * (π k * r)))‖ + ‖rᵀ * (π j * (π k * e))‖ +
          ‖rᵀ * (π j * s)‖ + ‖rᵀ * (π j * (P * (π k * r)))‖ := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)) le_rfl)) le_rfl)
      rw [norm_neg]
    refine h3.trans ?_
    have u2 : 1 * (μ * (p₀ * μ)) * (C * ε ^ 2) ≤ 1 * (μ * (p₀ * μ)) * (C * ε) := by gcongr
    have u3 : (C * ε ^ 2) * (μ * μ) * 1 ≤ (C * ε) * (μ * μ) * 1 := by gcongr
    have u4 : (C * ε ^ 2) * μ * (C * ε) ≤ (C * ε) * μ * (C * 1) := by gcongr
    have u5 : (C * ε ^ 2) * (μ * (p₀ * μ)) * (C * ε ^ 2) ≤
        (C * ε) * (μ * (p₀ * μ)) * (C * 1) := by gcongr
    nlinarith

end Moments

section Scheme

variable {Nx Nv r d : ℕ}

/-- The vector `e = (1, …, 1)ᵀ ∈ ℝ^{N_v}` of the paper. -/
def eOne (Nv : ℕ) : Matrix (Fin Nv) Unit ℝ := Matrix.of fun _ _ => 1

/-- The normalized vector `e_n = e / √N_v` of the paper. -/
noncomputable def eNorm (Nv : ℕ) : Matrix (Fin Nv) Unit ℝ := (√(Nv : ℝ))⁻¹ • eOne Nv

/-- The velocity matrix `Π_{v_k} = diag(𝒱_k)` of (2.20); `v k j` is the `k`-th coordinate of the
`j`-th velocity. -/
def velPi (v : Fin d → Fin Nv → ℝ) (k : Fin d) : Matrix (Fin Nv) (Fin Nv) ℝ :=
  Matrix.diagonal (v k)

/-- The collision matrix `C = e eᵀ / N_v - I` of (2.20). -/
noncomputable def collC (Nv : ℕ) : Matrix (Fin Nv) (Fin Nv) ℝ :=
  (Nv : ℝ)⁻¹ • (eOne Nv * (eOne Nv)ᵀ) - 1

/-- The two identities of the rectangle rule on the sphere that the paper uses:
`e_nᵀ Π_k e_n = 0` and `e_nᵀ Π_j Π_k e_n = δ_{jk} / d`. -/
structure IsQuadrature (v : Fin d → Fin Nv → ℝ) : Prop where
  pos : 0 < Nv
  mean : ∀ k, ∑ j, v k j = 0
  cov : ∀ k l, (Nv : ℝ)⁻¹ * ∑ j, v k j * v l j = if k = l then (d : ℝ)⁻¹ else 0

/-- `A_{∂_k} = Xᵀ D_k X` of (2.20). -/
def AD (X : Matrix (Fin Nx) (Fin r) ℝ) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (k : Fin d) :
    Matrix (Fin r) (Fin r) ℝ := Xᵀ * D k * X

/-- `A_σ = Xᵀ Σ X` of (2.20). -/
def Asig (X : Matrix (Fin Nx) (Fin r) ℝ) (σ : Fin Nx → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Xᵀ * Matrix.diagonal σ * X

/-- `Ξ_{v_k} = Vᵀ Π_{v_k} V` of (2.23). -/
def Xi (v : Fin d → Fin Nv → ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ) (k : Fin d) :
    Matrix (Fin r) (Fin r) ℝ := Vᵀ * velPi v k * V

/-- `Γ = Vᵀ C V` of (2.23). -/
noncomputable def Gam (V : Matrix (Fin Nv) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Vᵀ * collC Nv * V

/-- The implicit Euler `L`-step (2.18). -/
def IsLStepIE (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) (v : Fin d → Fin Nv → ℝ)
    (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ) : Prop :=
  Δt⁻¹ • (L₁ - L) + ε⁻¹ • ∑ k, AD X D k * L₁ * velPi v k =
    (ε ^ 2)⁻¹ • (Asig X σ * L₁ * collC Nv)

/-- The Crank–Nicolson `L`-step (2.19). -/
def IsLStepCN (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) (v : Fin d → Fin Nv → ℝ)
    (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ) : Prop :=
  Δt⁻¹ • (L₁ - L) + ε⁻¹ • ∑ k, AD X D k * ((2 : ℝ)⁻¹ • (L₁ + L)) * velPi v k =
    (ε ^ 2)⁻¹ • (Asig X σ * ((2 : ℝ)⁻¹ • (L₁ + L)) * collC Nv)

/-- The implicit Euler `S`-step (2.21); note the backward sign of the projector splitting. -/
def IsSStepIE (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) (v : Fin d → Fin Nv → ℝ)
    (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
    (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  Δt⁻¹ • (S₂ - S₁) - ε⁻¹ • ∑ k, AD X D k * S₂ * Xi v V k =
    -((ε ^ 2)⁻¹ • (Asig X σ * S₂ * Gam V))

/-- The Crank–Nicolson `S`-step (2.22). -/
def IsSStepCN (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) (v : Fin d → Fin Nv → ℝ)
    (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
    (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  Δt⁻¹ • (S₂ - S₁) - ε⁻¹ • ∑ k, AD X D k * ((2 : ℝ)⁻¹ • (S₂ + S₁)) * Xi v V k =
    -((ε ^ 2)⁻¹ • (Asig X σ * ((2 : ℝ)⁻¹ • (S₂ + S₁)) * Gam V))

/-- The implicit Euler `K`-step (2.25). -/
def IsKStep (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) (v : Fin d → Fin Nv → ℝ)
    (Δt ε : ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ) (K₂ K₃ : Matrix (Fin Nx) (Fin r) ℝ) : Prop :=
  Δt⁻¹ • (K₃ - K₂) + ε⁻¹ • ∑ k, D k * K₃ * Xi v V k =
    (ε ^ 2)⁻¹ • (Matrix.diagonal σ * K₃ * Gam V)

theorem eNorm_apply (j : Fin Nv) (u : Unit) : eNorm Nv j u = (√(Nv : ℝ))⁻¹ := by
  simp [eNorm, eOne]

private theorem sqrt_inv_mul_self : (√(Nv : ℝ))⁻¹ * (√(Nv : ℝ))⁻¹ = (Nv : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem velPi_mul_eNorm_apply (v : Fin d → Fin Nv → ℝ) (k : Fin d) (j : Fin Nv) (u : Unit) :
    (velPi v k * eNorm Nv) j u = v k j * (√(Nv : ℝ))⁻¹ := by
  rw [velPi, Matrix.diagonal_mul, eNorm_apply]

theorem eNorm_transpose_mul (hNv : 0 < Nv) : (eNorm Nv)ᵀ * eNorm Nv = 1 := by
  have h : (Nv : ℝ) ≠ 0 := by exact_mod_cast hNv.ne'
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eNorm_apply, sqrt_inv_mul_self]
  simp [h]

theorem norm_eNorm (hNv : 0 < Nv) : ‖eNorm Nv‖ = 1 := by
  have h := norm_sq_of_orthonormal (eNorm_transpose_mul hNv)
  simp only [Fintype.card_unit, Nat.cast_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem eNorm_moment1 {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (k : Fin d) :
    (eNorm Nv)ᵀ * (velPi v k * eNorm Nv) = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, eNorm_apply, velPi_mul_eNorm_apply, Matrix.zero_apply]
  have h : ∀ x, (√(Nv : ℝ))⁻¹ * (v k x * (√(Nv : ℝ))⁻¹) = (Nv : ℝ)⁻¹ * v k x := fun x => by
    rw [← sqrt_inv_mul_self]; ring
  simp only [h, ← Finset.mul_sum, hv.mean k, mul_zero]

theorem eNorm_moment2 {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (j k : Fin d) :
    (eNorm Nv)ᵀ * (velPi v j * (velPi v k * eNorm Nv)) =
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ) := by
  ext a b
  rw [Matrix.mul_apply]
  have e : ∀ x, (velPi v j * (velPi v k * eNorm Nv)) x b = v j x * (v k x * (√(Nv : ℝ))⁻¹) :=
    fun x => by rw [velPi, Matrix.diagonal_mul, velPi_mul_eNorm_apply]
  simp only [Matrix.transpose_apply, eNorm_apply, e, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ x, (√(Nv : ℝ))⁻¹ * (v j x * (v k x * (√(Nv : ℝ))⁻¹)) =
      (Nv : ℝ)⁻¹ * (v j x * v k x) := fun x => by
    rw [← sqrt_inv_mul_self]; ring
  simp only [h, ← Finset.mul_sum, hv.cov j k]
  simp

theorem collC_eq : collC Nv = eNorm Nv * (eNorm Nv)ᵀ - 1 := by
  rw [collC, eNorm, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrt_inv_mul_self]

theorem Gam_eq {V : Matrix (Fin Nv) (Fin r) ℝ} (hV : Vᵀ * V = 1) :
    Gam V = (Vᵀ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ - 1 := by
  rw [Gam, collC_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

section Bridge

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]

omit [DecidableEq p] in
private theorem bridge_aux [DecidableEq p] {G : Fin d → Matrix m m ℝ} {W : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ}
    {w : Matrix p Unit ℝ} {τ ε : ℝ} (hτ : τ ≠ 0) {Y F : Matrix m p ℝ}
    (h : τ⁻¹ • (Y - F) + ε⁻¹ • transport G M Y = (ε ^ 2)⁻¹ • (W * Y * (w * wᵀ - 1))) :
    IsStiffSolution G W M w τ ε Y F := by
  have h1 := congrArg (fun A => τ • A) h
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hτ, one_smul] at h1
  have e : W * Y * (1 - w * wᵀ) = -(W * Y * (w * wᵀ - 1)) := by
    rw [← Matrix.mul_neg, neg_sub]
  rw [IsStiffSolution, e, smul_neg, div_eq_mul_inv, div_eq_mul_inv, ← h1]
  abel

end Bridge

/-- Equation (2.18) in stiff form. -/
theorem IsLStepIE.stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {L L₁ : Matrix (Fin r) (Fin Nv) ℝ} (h : IsLStepIE D σ v Δt ε X L L₁) (hΔt : Δt ≠ 0) :
    IsStiffSolution (AD X D) (Asig X σ) (velPi v) (eNorm Nv) Δt ε L₁ L := by
  refine bridge_aux hΔt ?_
  rw [transport, ← collC_eq]
  exact h

/-- Equation (2.19) in stiff form: the midpoint solves the problem with `τ = Δt / 2`. -/
theorem IsLStepCN.stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {L L₁ : Matrix (Fin r) (Fin Nv) ℝ} (h : IsLStepCN D σ v Δt ε X L L₁) (hΔt : Δt ≠ 0) :
    IsStiffSolution (AD X D) (Asig X σ) (velPi v) (eNorm Nv) (Δt / 2) ε
      ((2 : ℝ)⁻¹ • (L₁ + L)) L := by
  refine bridge_aux (by positivity) ?_
  rw [transport, ← collC_eq]
  have e : (Δt / 2)⁻¹ • ((2 : ℝ)⁻¹ • (L₁ + L) - L) = Δt⁻¹ • (L₁ - L) := by
    have : (2 : ℝ)⁻¹ • (L₁ + L) - L = (2 : ℝ)⁻¹ • (L₁ - L) := by
      have h2 : L = (2 : ℝ)⁻¹ • (L + L) := by
        rw [← two_smul ℝ L, smul_smul]; norm_num
      calc (2 : ℝ)⁻¹ • (L₁ + L) - L = (2 : ℝ)⁻¹ • (L₁ + L) - (2 : ℝ)⁻¹ • (L + L) := by rw [← h2]
        _ = _ := by rw [← smul_sub]; congr 1; abel
    rw [this, smul_smul]
    congr 1
    field_simp
  rw [e]
  exact h

/-- Equation (2.21) in stiff form, with `τ = -Δt`. -/
theorem IsSStepIE.stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} {S₁ S₂ : Matrix (Fin r) (Fin r) ℝ}
    (h : IsSStepIE D σ v Δt ε X V S₁ S₂) (hΔt : Δt ≠ 0) (hV : Vᵀ * V = 1) :
    IsStiffSolution (AD X D) (Asig X σ) (Xi v V) (Vᵀ * eNorm Nv) (-Δt) ε S₂ S₁ := by
  refine bridge_aux (neg_ne_zero.mpr hΔt) ?_
  rw [transport, ← Gam_eq hV, inv_neg, neg_smul]
  have h1 := congrArg Neg.neg h
  rw [neg_neg, neg_sub] at h1
  rw [← h1]
  abel

/-- Equation (2.22) in stiff form: the midpoint solves the problem with `τ = -Δt / 2`. -/
theorem IsSStepCN.stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} {S₁ S₂ : Matrix (Fin r) (Fin r) ℝ}
    (h : IsSStepCN D σ v Δt ε X V S₁ S₂) (hΔt : Δt ≠ 0) (hV : Vᵀ * V = 1) :
    IsStiffSolution (AD X D) (Asig X σ) (Xi v V) (Vᵀ * eNorm Nv) (-Δt / 2) ε
      ((2 : ℝ)⁻¹ • (S₂ + S₁)) S₁ := by
  refine bridge_aux (by simpa using hΔt) ?_
  rw [transport, ← Gam_eq hV]
  have e : (-Δt / 2)⁻¹ • ((2 : ℝ)⁻¹ • (S₂ + S₁) - S₁) = -(Δt⁻¹ • (S₂ - S₁)) := by
    have : (2 : ℝ)⁻¹ • (S₂ + S₁) - S₁ = (2 : ℝ)⁻¹ • (S₂ - S₁) := by
      have h2 : S₁ = (2 : ℝ)⁻¹ • (S₁ + S₁) := by
        rw [← two_smul ℝ S₁, smul_smul]; norm_num
      calc (2 : ℝ)⁻¹ • (S₂ + S₁) - S₁ = (2 : ℝ)⁻¹ • (S₂ + S₁) - (2 : ℝ)⁻¹ • (S₁ + S₁) := by
            rw [← h2]
        _ = _ := by rw [← smul_sub]; congr 1; abel
    rw [this, smul_smul, ← neg_smul]
    congr 1
    field_simp
  rw [e]
  have h1 := congrArg Neg.neg h
  rw [neg_neg, neg_sub] at h1
  rw [← h1]
  abel

/-- Equation (2.25) in stiff form. -/
theorem IsKStep.stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {V : Matrix (Fin Nv) (Fin r) ℝ}
    {K₂ K₃ : Matrix (Fin Nx) (Fin r) ℝ} (h : IsKStep D σ v Δt ε V K₂ K₃) (hΔt : Δt ≠ 0)
    (hV : Vᵀ * V = 1) :
    IsStiffSolution D (Matrix.diagonal σ) (Xi v V) (Vᵀ * eNorm Nv) Δt ε K₃ K₂ := by
  refine bridge_aux hΔt ?_
  rw [transport, ← Gam_eq hV]
  exact h

end Scheme

section Bounds

variable {Nx Nv r d : ℕ}

/-- A square matrix that is bounded below on column vectors is invertible. -/
private theorem isUnit_det_of_bddBelow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {s : ℝ} (hs : 0 < s) (h : ∀ y : Matrix n Unit ℝ, s * ‖y‖ ≤ ‖A * y‖) :
    IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  set y : Matrix n Unit ℝ := Matrix.of fun a _ => x a with hy
  have h0 : A * y = 0 := by
    ext a b
    have := congrFun hAx a
    simpa [Matrix.mul_apply, hy, Matrix.mulVec, dotProduct] using this
  have h1 := h y
  rw [h0, norm_zero] at h1
  have h2 : ‖y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg y]) (norm_nonneg _)
  have h3 : y = 0 := norm_eq_zero.mp h2
  apply hi
  have := congrFun (congrFun h3 i) ()
  simpa [hy] using this

private theorem norm_one_fin : ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ = √(r : ℝ) := by
  have h := norm_sq_of_orthonormal (V := (1 : Matrix (Fin r) (Fin r) ℝ)) (by simp)
  simp only [Fintype.card_fin] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_of_orthonormal {q : Type*} [Fintype q] [DecidableEq q] {n : Type*} [Fintype n]
    {V : Matrix n q ℝ} (hV : Vᵀ * V = 1) : ‖V‖ = √(Fintype.card q : ℝ) := by
  rw [← norm_sq_of_orthonormal hV, Real.sqrt_sq (norm_nonneg _)]

private theorem inner_diagonal_ge {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n]
    {σ : n → ℝ} {s : ℝ} (hσ : ∀ i, s ≤ σ i) (Z : Matrix n q ℝ) :
    s * ‖Z‖ ^ 2 ≤ ⟪Z, Matrix.diagonal σ * Z⟫ := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.inner_def, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.diagonal_mul]
  nlinarith [hσ i, sq_nonneg (Z i j)]

/-- The Galerkin scattering matrix is uniformly invertible: `s ‖y‖ ≤ ‖A_σ y‖`. -/
theorem Asig_bddBelow {q : Type*} [Fintype q] {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ}
    {s : ℝ} (hX : Xᵀ * X = 1) (hσ : ∀ i, s ≤ σ i) (y : Matrix (Fin r) q ℝ) :
    s * ‖y‖ ≤ ‖Asig X σ * y‖ := by
  by_cases hy : ‖y‖ = 0
  · rw [hy, mul_zero]; exact norm_nonneg _
  have hy' : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
  have h1 := inner_diagonal_ge hσ (X * y)
  rw [Frobenius.norm_mul_of_orthonormal hX, Frobenius.inner_mul_left] at h1
  have h2 : Xᵀ * (Matrix.diagonal σ * (X * y)) = Asig X σ * y := by
    simp only [Asig, Matrix.mul_assoc]
  rw [h2] at h1
  have h3 := real_inner_le_norm y (Asig X σ * y)
  have h4 : s * ‖y‖ * ‖y‖ ≤ ‖Asig X σ * y‖ * ‖y‖ := by nlinarith
  exact le_of_mul_le_mul_right h4 hy'

theorem Asig_isUnit {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ}
    {s : ℝ} (hs : 0 < s) (hX : Xᵀ * X = 1) (hσ : ∀ i, s ≤ σ i) : IsUnit (Asig X σ).det :=
  isUnit_det_of_bddBelow _ hs (Asig_bddBelow hX hσ)

theorem norm_Asig_inv_le {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ}
    {s : ℝ} (hs : 0 < s) (hX : Xᵀ * X = 1) (hσ : ∀ i, s ≤ σ i) :
    ‖(Asig X σ)⁻¹‖ ≤ √(r : ℝ) / s := by
  have h1 := Asig_bddBelow hX hσ (Asig X σ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (Asig_isUnit hs hX hσ), norm_one_fin] at h1
  rw [le_div_iff₀ hs]
  linarith

theorem norm_Asig_le {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ} (hX : Xᵀ * X = 1) :
    ‖Asig X σ‖ ≤ r * ‖Matrix.diagonal σ‖ := by
  have h := norm_of_orthonormal hX
  simp only [Fintype.card_fin] at h
  refine (norm_mul3_le _ _ _).trans (le_of_eq ?_)
  rw [Frobenius.norm_transpose, h, mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg r)]

theorem norm_AD_le {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    (hX : Xᵀ * X = 1) (k : Fin d) : ‖AD X D k‖ ≤ r * ∑ i, ‖D i‖ := by
  have h := norm_of_orthonormal hX
  simp only [Fintype.card_fin] at h
  have h1 : ‖D k‖ ≤ ∑ i, ‖D i‖ :=
    Finset.single_le_sum (f := fun i => ‖D i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  refine (norm_mul3_le _ _ _).trans ?_
  rw [Frobenius.norm_transpose, h]
  rw [mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg r)]
  gcongr

theorem norm_Xi_le {v : Fin d → Fin Nv → ℝ} {V : Matrix (Fin Nv) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) (k : Fin d) : ‖Xi v V k‖ ≤ r * ∑ i, ‖velPi v i‖ := by
  have h := norm_of_orthonormal hV
  simp only [Fintype.card_fin] at h
  have h1 : ‖velPi v k‖ ≤ ∑ i, ‖velPi v i‖ :=
    Finset.single_le_sum (f := fun i => ‖velPi v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ k)
  refine (norm_mul3_le _ _ _).trans ?_
  rw [Frobenius.norm_transpose, h]
  rw [mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg r)]
  gcongr

theorem norm_alpha_le (hNv : 0 < Nv) {V : Matrix (Fin Nv) (Fin r) ℝ} (hV : Vᵀ * V = 1) :
    ‖Vᵀ * eNorm Nv‖ ≤ √(r : ℝ) := by
  have h := norm_of_orthonormal hV
  simp only [Fintype.card_fin] at h
  refine (Frobenius.norm_mul_le _ _).trans ?_
  rw [Frobenius.norm_transpose, h, norm_eNorm hNv, mul_one]

/-- The velocity basis captures `e_n` to order `ε²` and `Π_k e_n` to order `ε`.  This is what the
proofs use of Assumption 1. -/
structure Capture (v : Fin d → Fin Nv → ℝ) (ε C : ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ) : Prop where
  e : ‖eNorm Nv - V * (Vᵀ * eNorm Nv)‖ ≤ C * ε ^ 2
  vel : ∀ k, ‖velPi v k * eNorm Nv - V * (Vᵀ * (velPi v k * eNorm Nv))‖ ≤ C * ε

/-- The constant of the moments of `α`. -/
noncomputable def momC (r : ℕ) (μ C : ℝ) : ℝ :=
  C ^ 2 + (2 * μ * C + μ * C ^ 2) +
    (μ * C + μ * r * μ * C + C * μ * μ + C ^ 2 * μ + C ^ 2 * μ ^ 2 * r)

private theorem moments_alpha {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v)
    {V : Matrix (Fin Nv) (Fin r) ℝ} {ε C : ℝ} (hV : Vᵀ * V = 1) (hC0 : 0 ≤ C) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hc : Capture v ε C V) :
    ‖(1 : Matrix Unit Unit ℝ) - (Vᵀ * eNorm Nv)ᵀ * (Vᵀ * eNorm Nv)‖ ≤
      momC r (∑ i, ‖velPi v i‖) C * ε ^ 3 ∧
    (∀ k, ‖(Vᵀ * eNorm Nv)ᵀ * (Xi v V k * (Vᵀ * eNorm Nv))‖ ≤
      momC r (∑ i, ‖velPi v i‖) C * ε ^ 2) ∧
    ∀ j k, ‖(Vᵀ * eNorm Nv)ᵀ * (Xi v V j * (Xi v V k * (Vᵀ * eNorm Nv))) -
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)‖ ≤
      momC r (∑ i, ‖velPi v i‖) C * ε := by
  set μ := ∑ i, ‖velPi v i‖ with hμ
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hP : ‖V * Vᵀ‖ ≤ (r : ℝ) := by
    have h := norm_of_orthonormal hV
    simp only [Fintype.card_fin] at h
    refine (Frobenius.norm_mul_le _ _).trans (le_of_eq ?_)
    rw [Frobenius.norm_transpose, h, Real.mul_self_sqrt hr0]
  obtain ⟨h1, h2, h3⟩ := moments_capture (π := velPi v) (e := eNorm Nv) (V := V) (μ := μ)
    (C := C) (p₀ := r) (ε := ε) hV (eNorm_transpose_mul hv.pos) (norm_eNorm hv.pos).le
    (eNorm_moment1 hv) (eNorm_moment2 hv)
    (fun k => Finset.single_le_sum (f := fun i => ‖velPi v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ k)) hμ0 hC0 hP hε hε1 hc.e hc.vel
  have ha : 0 ≤ C ^ 2 := by positivity
  have hb : 0 ≤ 2 * μ * C + μ * C ^ 2 := by positivity
  have hc' : 0 ≤ μ * C + μ * r * μ * C + C * μ * μ + C ^ 2 * μ + C ^ 2 * μ ^ 2 * r := by positivity
  refine ⟨h1.trans ?_, fun k => (h2 k).trans ?_, fun j k => (h3 j k).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by rw [momC]; linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by rw [momC]; linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by rw [momC]; linarith) hε

/-- The hypotheses of the a priori estimate for the `L`-step. -/
theorem stiffHyp_L {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {s ε : ℝ} (hs : 0 < s) (hσ : ∀ i, s ≤ σ i)
    {X : Matrix (Fin Nx) (Fin r) ℝ} (hX : Xᵀ * X = 1) :
    StiffHyp (AD X D) (Asig X σ) (Asig X σ)⁻¹ (velPi v) (eNorm Nv) (r * ∑ i, ‖D i‖) (√(r : ℝ) / s)
      (r * ‖Matrix.diagonal σ‖) (∑ i, ‖velPi v i‖) 1 0 ε where
  inv := Matrix.nonsing_inv_mul _ (Asig_isUnit hs hX hσ)
  g0 := by positivity
  μ0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  hG := norm_AD_le hX
  hWinv := norm_Asig_inv_le hs hX hσ
  hW := norm_Asig_le hX
  hM k := Finset.single_le_sum (f := fun i => ‖velPi v i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ k)
  hw := (norm_eNorm hv.pos).le
  hδ := by rw [eNorm_transpose_mul hv.pos]; simp
  hm1 k := by rw [eNorm_moment1 hv]; simp
  hm2 j k := by rw [eNorm_moment2 hv]; simp

/-- The hypotheses of the a priori estimate for the `S`-step. -/
theorem stiffHyp_S {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {s ε C : ℝ} (hs : 0 < s) (hσ : ∀ i, s ≤ σ i)
    {X : Matrix (Fin Nx) (Fin r) ℝ} (hX : Xᵀ * X = 1) {V : Matrix (Fin Nv) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) (hC0 : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : Capture v ε C V) :
    StiffHyp (AD X D) (Asig X σ) (Asig X σ)⁻¹ (Xi v V) (Vᵀ * eNorm Nv) (r * ∑ i, ‖D i‖)
      (√(r : ℝ) / s) (r * ‖Matrix.diagonal σ‖) (r * ∑ i, ‖velPi v i‖) (√(r : ℝ))
      (momC r (∑ i, ‖velPi v i‖) C) ε where
  inv := Matrix.nonsing_inv_mul _ (Asig_isUnit hs hX hσ)
  g0 := by positivity
  μ0 := mul_nonneg (Nat.cast_nonneg r) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  hG := norm_AD_le hX
  hWinv := norm_Asig_inv_le hs hX hσ
  hW := norm_Asig_le hX
  hM := norm_Xi_le hV
  hw := norm_alpha_le hv.pos hV
  hδ := (moments_alpha hv hV hC0 hε hε1 hc).1
  hm1 := (moments_alpha hv hV hC0 hε hε1 hc).2.1
  hm2 := (moments_alpha hv hV hC0 hε hε1 hc).2.2

/-- The hypotheses of the a priori estimate for the `K`-step. -/
theorem stiffHyp_K {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {ε C : ℝ} (hσ : ∀ i, 0 < σ i)
    {V : Matrix (Fin Nv) (Fin r) ℝ}
    (hV : Vᵀ * V = 1) (hC0 : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : Capture v ε C V) :
    StiffHyp D (Matrix.diagonal σ) (Matrix.diagonal σ)⁻¹ (Xi v V) (Vᵀ * eNorm Nv)
      (∑ i, ‖D i‖) ‖(Matrix.diagonal σ)⁻¹‖ ‖Matrix.diagonal σ‖ (r * ∑ i, ‖velPi v i‖) (√(r : ℝ))
      (momC r (∑ i, ‖velPi v i‖) C) ε where
  inv := by
    refine Matrix.nonsing_inv_mul _ ?_
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hσ i).ne'
  g0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  μ0 := mul_nonneg (Nat.cast_nonneg r) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  hG k := Finset.single_le_sum (f := fun i => ‖D i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  hWinv := le_rfl
  hW := le_rfl
  hM := norm_Xi_le hV
  hw := norm_alpha_le hv.pos hV
  hδ := (moments_alpha hv hV hC0 hε hε1 hc).1
  hm1 := (moments_alpha hv hV hC0 hε hε1 hc).2.1
  hm2 := (moments_alpha hv hV hC0 hε hε1 hc).2.2

end Bounds

section Limit

variable {Nx Nv r d : ℕ}

/-- The operator `𝓛 = ∑ₖ X A_{∂_k} A_σ⁻¹ A_{∂_k} Xᵀ` of the paper, see (3.26). -/
noncomputable def limL (X : Matrix (Fin Nx) (Fin r) ℝ) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (σ : Fin Nx → ℝ) : Matrix (Fin Nx) (Fin Nx) ℝ :=
  ∑ k, X * AD X D k * (Asig X σ)⁻¹ * AD X D k * Xᵀ

/-- The discrete diffusion operator `∑ₖ D_k Σ⁻¹ D_k` of (3.11). -/
noncomputable def limD (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ) :
    Matrix (Fin Nx) (Fin Nx) ℝ :=
  ∑ k, D k * (Matrix.diagonal σ)⁻¹ * D k

/-- The operator `T` has a bounded inverse on `ℝ^{N_x}`, with bound `B`.  Theorems 3.2 and 3.3 are
stated in terms of `(I ± (Δt / d) 𝓛)⁻¹`; this is what those inverses mean quantitatively. -/
def Stable (T : Matrix (Fin Nx) (Fin Nx) ℝ) (B : ℝ) : Prop :=
  ∀ x : Matrix (Fin Nx) Unit ℝ, ‖x‖ ≤ B * ‖T * x‖

/-- The density `ρ = u e / N_v = u e_n / √N_v`. -/
noncomputable def density (u : Matrix (Fin Nx) (Fin Nv) ℝ) : Matrix (Fin Nx) Unit ℝ :=
  (√(Nv : ℝ))⁻¹ • (u * eNorm Nv)

theorem X_limitOp {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    {σ : Fin Nx → ℝ} (hX : Xᵀ * X = 1) (τ : ℝ) :
    X * limitOp (AD X D) (Asig X σ)⁻¹ τ = (1 - (τ / d) • limL X D σ) * X := by
  rw [limitOp, limL, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_assoc (X * AD X D k * (Asig X σ)⁻¹ * AD X D k), hX, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem stable_lift {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    {σ : Fin Nx → ℝ} (hX : Xᵀ * X = 1) {τ B : ℝ} (h : Stable (1 - (τ / d) • limL X D σ) B)
    (y : Matrix (Fin r) Unit ℝ) : ‖y‖ ≤ B * ‖limitOp (AD X D) (Asig X σ)⁻¹ τ * y‖ := by
  have h1 := h (X * y)
  rw [← Matrix.mul_assoc, ← X_limitOp hX, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hX,
    Frobenius.norm_mul_of_orthonormal hX] at h1
  exact h1

private theorem stable_neg {T : Matrix (Fin Nx) (Fin Nx) ℝ} {c B : ℝ} (h : Stable (1 + c • T) B) :
    Stable (1 - (-c) • T) B := by
  rwa [neg_smul, sub_neg_eq_add]

private theorem limit_eq_sub {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℝ}
    {a b : Matrix n Unit ℝ} {Δt : ℝ} {c : ℝ} (hΔt : Δt ≠ 0)
    (h : Δt⁻¹ • (a - b) - c • (T * a) = 0) : (1 - (Δt * c) • T) * a = b := by
  have h1 := congrArg (fun A => Δt • A) h
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hΔt, one_smul, smul_zero] at h1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have h2 : a - (Δt * c) • (T * a) - b = a - b - (Δt * c) • (T * a) := by abel
  exact sub_eq_zero.mp (h2.trans h1)

private theorem limit_eq_add {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℝ}
    {a b : Matrix n Unit ℝ} {Δt : ℝ} {c : ℝ} (hΔt : Δt ≠ 0)
    (h : Δt⁻¹ • (a - b) + c • (T * a) = 0) : (1 + (Δt * c) • T) * a = b := by
  have h1 := congrArg (fun A => Δt • A) h
  simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hΔt, one_smul, smul_zero] at h1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have h2 : a + (Δt * c) • (T * a) - b = a - b + (Δt * c) • (T * a) := by abel
  exact sub_eq_zero.mp (h2.trans h1)

private theorem exists_lower_bound {σ : Fin Nx → ℝ} (hσ : ∀ i, 0 < σ i) :
    ∃ s : ℝ, 0 < s ∧ ∀ i, s ≤ σ i := by
  by_cases h : Nonempty (Fin Nx)
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min σ
    exact ⟨σ i₀, hσ i₀, hi₀⟩
  · exact ⟨1, one_pos, fun i => (h ⟨i⟩).elim⟩

private theorem sqrt_Nv_ge (hNv : 0 < Nv) : (1 : ℝ) ≤ √(Nv : ℝ) := by
  rw [Real.one_le_sqrt]
  exact_mod_cast hNv

private theorem sqrt_Nv_inv_le (hNv : 0 < Nv) : (√(Nv : ℝ))⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (sqrt_Nv_ge hNv)

private theorem norm_dens_le (hNv : 0 < Nv) {X : Matrix (Fin Nx) (Fin r) ℝ} (hX : Xᵀ * X = 1)
    (y : Matrix (Fin r) Unit ℝ) : ‖(√(Nv : ℝ))⁻¹ • (X * y)‖ ≤ ‖y‖ := by
  rw [norm_smul, Frobenius.norm_mul_of_orthonormal hX, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sqrt_Nv_inv_le hNv)

private theorem dens_err {X : Matrix (Fin Nx) (Fin r) ℝ} {Tr : Matrix (Fin r) (Fin r) ℝ}
    {T : Matrix (Fin Nx) (Fin Nx) ℝ} {B s : ℝ} (hT : X * Tr = T * X) (hst : Stable T B)
    (y : Matrix (Fin r) Unit ℝ) {b c : Matrix (Fin Nx) Unit ℝ} (hb : T * b = c) :
    ‖s • (X * y) - b‖ ≤ B * ‖s • (X * (Tr * y)) - c‖ := by
  have h := hst (s • (X * y) - b)
  rw [Matrix.mul_sub, Matrix.mul_smul, hb, ← Matrix.mul_assoc T, ← hT, Matrix.mul_assoc] at h
  exact h

theorem eOne_eq (hNv : 0 < Nv) : eOne Nv = √(Nv : ℝ) • eNorm Nv := by
  have h : √(Nv : ℝ) ≠ 0 := by have := sqrt_Nv_ge hNv; positivity
  rw [eNorm, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- The last substep of both integrators, implicit Euler for `K`. -/
private theorem kStep_final (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : Δt ≠ 0)
    {CA B : ℝ} (hCA : 0 ≤ CA) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (S₂ : Matrix (Fin r) (Fin r) ℝ) (K₃ : Matrix (Fin Nx) (Fin r) ℝ)
        (ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Capture v ε CA V → IsKStep D σ v Δt ε V (X * S₂) K₃ →
        Stable (1 - (Δt / d) • limD D σ) B →
        Δt⁻¹ • (ρ₃ - ρ₂) - (d : ℝ)⁻¹ • (limD D σ * ρ₃) = 0 →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤
          C * (ε * ‖S₂‖ + ‖(√(Nv : ℝ))⁻¹ • (X * (S₂ * (Vᵀ * eNorm Nv))) - ρ₂‖) := by
  have hNv := hv.pos
  have hsq := sqrt_Nv_ge hNv
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := stiff_main (m := Fin Nx) (p := Fin r) d hΔt
    (∑ i, ‖D i‖) ‖(Matrix.diagonal σ)⁻¹‖ ‖Matrix.diagonal σ‖ (r * ∑ i, ‖velPi v i‖) (√(r : ℝ))
    (momC r (∑ i, ‖velPi v i‖) CA) B hB
  set B₀ := 2 * B * (√(r : ℝ)) ^ 2 + 1 with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set s := (√(Nv : ℝ))⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := sqrt_Nv_inv_le hNv
  refine ⟨C₃ + B₀ * √(r : ℝ) * CA + √(Nv : ℝ) * B * C₃ + √(Nv : ℝ) * B, ε₃, by positivity, hε₃,
    hε₃1, ?_⟩
  intro ε hε hεε X V S₂ K₃ ρ₂ ρ₃ hX hV hc hK hst hlim
  have hε1 : ε ≤ 1 := (hεε.trans_le hε₃1).le
  have hH := stiffHyp_K (D := D) hv hσ hV hCA hε.le hε1 hc
  obtain ⟨b1, b2, b3, -⟩ := h3 ε hε hεε _ _ _ _ _ _ _ hH hst (hK.stiff hΔt hV)
  rw [Frobenius.norm_mul_of_orthonormal hX] at b1 b2 b3
  set α := Vᵀ * eNorm Nv with hα
  set l := K₃ * α with hl
  have hα1 : ‖α‖ ≤ √(r : ℝ) := norm_alpha_le hNv hV
  have hsmul : √(Nv : ℝ) • (s • (l * (eNorm Nv)ᵀ)) = l * (eNorm Nv)ᵀ := by
    rw [smul_smul, hs, mul_inv_cancel₀ (by positivity), one_smul]
  have hρ : (1 - (Δt / d) • limD D σ) * ρ₃ = ρ₂ := by
    rw [div_eq_mul_inv]
    exact limit_eq_sub hΔt hlim
  -- the density error
  have h1 : ‖s • l - ρ₃‖ ≤ B * (C₃ * ε * ‖S₂‖ + ‖s • (X * (S₂ * α)) - ρ₂‖) := by
    have h2 := hst (s • l - ρ₃)
    rw [Matrix.mul_sub, Matrix.mul_smul, hρ] at h2
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hB)
    have e : s • ((1 - (Δt / d) • limD D σ) * l) - ρ₂ =
        s • ((1 - (Δt / d) • limD D σ) * l - X * (S₂ * α)) + (s • (X * (S₂ * α)) - ρ₂) := by
      rw [smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    have : ‖(1 - (Δt / d) • limD D σ) * l - X * (S₂ * α)‖ ≤ C₃ * ε * ‖S₂‖ := by
      rw [← Matrix.mul_assoc X]; exact b3
    calc s * ‖(1 - (Δt / d) • limD D σ) * l - X * (S₂ * α)‖ ≤
          1 * (C₃ * ε * ‖S₂‖) := by gcongr
      _ = _ := one_mul _
  have hdec : K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ =
      (K₃ - l * αᵀ) * Vᵀ - l * (eNorm Nv - V * α)ᵀ + √(Nv : ℝ) • ((s • l - ρ₃) * (eNorm Nv)ᵀ) := by
    rw [eOne_eq hNv, Matrix.transpose_smul, Matrix.mul_smul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.smul_mul, smul_sub, hsmul, Matrix.transpose_sub, Matrix.mul_sub,
      Matrix.transpose_mul V α, ← Matrix.mul_assoc l αᵀ Vᵀ]
    abel
  have t1 : ‖(K₃ - l * αᵀ) * Vᵀ‖ ≤ C₃ * ε * ‖S₂‖ := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV]; exact b2
  have hl : ‖l‖ ≤ (B₀ * ‖S₂‖) * √(r : ℝ) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul b1 hα1 (norm_nonneg _) (by positivity))
  have t2 : ‖l * (eNorm Nv - V * α)ᵀ‖ ≤ (B₀ * ‖S₂‖) * √(r : ℝ) * (CA * ε) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    have h2 : ‖eNorm Nv - V * α‖ ≤ CA * ε ^ 2 := hc.e
    have h3 : CA * ε ^ 2 ≤ CA * ε := by
      have : ε ^ 2 ≤ ε := by nlinarith
      gcongr
    exact mul_le_mul hl (h2.trans h3) (norm_nonneg _) (by positivity)
  have t3 : ‖√(Nv : ℝ) • ((s • l - ρ₃) * (eNorm Nv)ᵀ)‖ ≤ √(Nv : ℝ) * ‖s • l - ρ₃‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose, norm_eNorm hNv, mul_one]
  rw [hdec]
  set e₂ := ‖s • (X * (S₂ * α)) - ρ₂‖ with he₂
  have he₂0 : 0 ≤ e₂ := norm_nonneg _
  have hS0 := norm_nonneg S₂
  have h4 : √(Nv : ℝ) * ‖s • l - ρ₃‖ ≤ √(Nv : ℝ) * (B * (C₃ * ε * ‖S₂‖ + e₂)) := by gcongr
  calc _ ≤ ‖(K₃ - l * αᵀ) * Vᵀ‖ + ‖l * (eNorm Nv - V * α)ᵀ‖ +
        ‖√(Nv : ℝ) • ((s • l - ρ₃) * (eNorm Nv)ᵀ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C₃ * ε * ‖S₂‖ + (B₀ * ‖S₂‖) * √(r : ℝ) * (CA * ε) +
        √(Nv : ℝ) * (B * (C₃ * ε * ‖S₂‖ + e₂)) := by linarith
    _ ≤ _ := by
      have : 0 ≤ (C₃ + B₀ * √(r : ℝ) * CA + √(Nv : ℝ) * B * C₃) * e₂ +
          √(Nv : ℝ) * B * (ε * ‖S₂‖) := by positivity
      nlinarith

/-- One step of the implicit Euler integrator, Algorithm 2.1: (2.18), QR, (2.21), (2.25).  The
output is `u^{n+1} = K₃ Vᵀ`.  The triangular factor of the QR decomposition plays no role, so
`L₁ = S₁ Vᵀ` with orthonormal `V` is all that is required. -/
structure IsIEStep (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ)
    (v : Fin d → Fin Nv → ℝ) (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (L L₁ : Matrix (Fin r) (Fin Nv) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix (Fin Nv) (Fin r) ℝ) (S₂ : Matrix (Fin r) (Fin r) ℝ)
    (K₃ : Matrix (Fin Nx) (Fin r) ℝ) : Prop where
  lStep : IsLStepIE D σ v Δt ε X L L₁
  qr : L₁ = S₁ * Vᵀ
  orth : Vᵀ * V = 1
  sStep : IsSStepIE D σ v Δt ε X V S₁ S₂
  kStep : IsKStep D σ v Δt ε V (X * S₂) K₃

/-- The limit scheme (3.16), (3.20), (3.25) of the implicit Euler integrator. -/
structure IsIELimit (X : Matrix (Fin Nx) (Fin r) ℝ) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (σ : Fin Nx → ℝ) (Δt : ℝ) (ρ ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ) : Prop where
  step1 : Δt⁻¹ • (ρ₁ - ρ) - (d : ℝ)⁻¹ • (limL X D σ * ρ₁) = 0
  step2 : Δt⁻¹ • (ρ₂ - ρ₁) + (d : ℝ)⁻¹ • (limL X D σ * ρ₂) = 0
  step3 : Δt⁻¹ • (ρ₃ - ρ₂) - (d : ℝ)⁻¹ • (limD D σ * ρ₃) = 0

private theorem theorem_3_2_capture (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : Δt ≠ 0)
    {BL CA B : ℝ} (hBL : 0 ≤ BL) (hCA : 0 ≤ CA) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ → Capture v ε CA V →
        Stable (1 - (Δt / d) • limL X D σ) B → Stable (1 + (Δt / d) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        IsIELimit X D σ Δt (density (X * L)) ρ₁ ρ₂ ρ₃ →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * ε ∧ ‖density (X * S₂ * Vᵀ) - ρ₂‖ ≤ C * ε := by
  have hNv := hv.pos
  obtain ⟨s₀, hs₀, hσs⟩ := exists_lower_bound hσ
  obtain ⟨C₁, ε₁, hC₁, hε₁, hε₁1, h1⟩ := stiff_main (m := Fin r) (p := Fin Nv) d hΔt
    (r * ∑ i, ‖D i‖) (√(r : ℝ) / s₀) (r * ‖Matrix.diagonal σ‖) (∑ i, ‖velPi v i‖) 1 0 B hB
  obtain ⟨C₂, ε₂, hC₂, hε₂, hε₂1, h2⟩ := stiff_main (m := Fin r) (p := Fin r) d
    (neg_ne_zero.mpr hΔt) (r * ∑ i, ‖D i‖) (√(r : ℝ) / s₀) (r * ‖Matrix.diagonal σ‖)
    (r * ∑ i, ‖velPi v i‖) (√(r : ℝ)) (momC r (∑ i, ‖velPi v i‖) CA) B hB
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := kStep_final (r := r) D hσ hv hΔt hCA hB
  set B₁ := 2 * B * (1 : ℝ) ^ 2 + 1 with hB₁
  set B₂ := 2 * B * (√(r : ℝ)) ^ 2 + 1 with hB₂
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  set E₂ := B * (C₂ * (B₁ * BL) + (B₁ * BL) * CA + B * (C₁ * BL)) with hE₂
  have hE₂0 : 0 ≤ E₂ := by positivity
  refine ⟨C₃ * (B₂ * (B₁ * BL) + E₂) + E₂, min ε₁ (min ε₂ ε₃), by positivity,
    lt_min hε₁ (lt_min hε₂ hε₃), (min_le_left _ _).trans hε₁1, ?_⟩
  intro ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₁ ρ₂ ρ₃ hX hLB hstep hc hst1 hst2 hst3 hlim
  have hεε₁ : ε < ε₁ := hεε.trans_le (min_le_left _ _)
  have hεε₂ : ε < ε₂ := hεε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₃ : ε < ε₃ := hεε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (hεε₁.trans_le hε₁1).le
  have hV := hstep.orth
  obtain ⟨a1, -, a3, -⟩ := h1 ε hε hεε₁ _ _ _ _ _ _ _ (stiffHyp_L (D := D) hv hs₀ hσs hX)
    (stable_lift hX hst1) (hstep.lStep.stiff hΔt)
  obtain ⟨b1, -, b3, -⟩ := h2 ε hε hεε₂ _ _ _ _ _ _ _
    (stiffHyp_S (D := D) hv hs₀ hσs hX hV hCA hε.le hε1 hc)
    (stable_lift hX (by rw [neg_div]; exact stable_neg hst2)) (hstep.sStep.stiff hΔt hV)
  have hS₁ : ‖S₁‖ = ‖L₁‖ := by
    rw [hstep.qr, Frobenius.norm_mul_transpose_of_orthonormal hV]
  have hLn : ‖L₁‖ ≤ B₁ * BL := a1.trans (by gcongr)
  have hSn : ‖S₁‖ ≤ B₁ * BL := hS₁.le.trans hLn
  have hS₂n : ‖S₂‖ ≤ B₂ * (B₁ * BL) := b1.trans (by gcongr)
  set α := Vᵀ * eNorm Nv with hα
  set s := (√(Nv : ℝ))⁻¹ with hs
  have hs0 : 0 ≤ s := by positivity
  set y₁ := L₁ * eNorm Nv with hy₁
  set y₂ := S₂ * α with hy₂
  set T₁ := limitOp (AD X D) (Asig X σ)⁻¹ Δt with hT₁
  set T₂ := limitOp (AD X D) (Asig X σ)⁻¹ (-Δt) with hT₂
  have hL₁V : S₁ * α - y₁ = -(L₁ * (eNorm Nv - V * α)) := by
    have e : L₁ * (V * α) = S₁ * α := by
      rw [hstep.qr, Matrix.mul_assoc S₁ Vᵀ, ← Matrix.mul_assoc Vᵀ V α, hV, Matrix.one_mul]
    rw [hy₁, Matrix.mul_sub, neg_sub, e]
  have hres : ‖S₁ * α - y₁‖ ≤ (B₁ * BL) * (CA * ε) := by
    rw [hL₁V, norm_neg]
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul hLn ?_ (norm_nonneg _) (by positivity))
    have h4 : ‖eNorm Nv - V * α‖ ≤ CA * ε ^ 2 := hc.e
    have h5 : ε ^ 2 ≤ ε := by nlinarith
    exact h4.trans (by gcongr)
  have hρ₁ : (1 - (Δt / d) • limL X D σ) * ρ₁ = density (X * L) := by
    rw [div_eq_mul_inv]; exact limit_eq_sub hΔt hlim.step1
  have hρ₂ : (1 - (-Δt / d) • limL X D σ) * ρ₂ = ρ₁ := by
    have := limit_eq_add hΔt hlim.step2
    rw [neg_div, neg_smul, sub_neg_eq_add, div_eq_mul_inv]
    exact this
  have ha1 : ‖s • (X * y₁) - ρ₁‖ ≤ B * (C₁ * ε * BL) := by
    refine (dens_err (X_limitOp hX Δt) hst1 y₁ hρ₁).trans (mul_le_mul_of_nonneg_left ?_ hB)
    have e : s • (X * (T₁ * y₁)) - density (X * L) = s • (X * (T₁ * y₁ - L * eNorm Nv)) := by
      rw [density, Matrix.mul_sub, smul_sub, Matrix.mul_assoc X L]
    rw [e]
    refine (norm_dens_le hNv hX _).trans (a3.trans ?_)
    gcongr
  have ha2 : ‖s • (X * y₂) - ρ₂‖ ≤ B * (C₂ * ε * (B₁ * BL) + (B₁ * BL) * (CA * ε) +
      B * (C₁ * ε * BL)) := by
    have hst2' : Stable (1 - (-Δt / d) • limL X D σ) B := by
      rw [neg_div]; exact stable_neg hst2
    refine (dens_err (X_limitOp hX (-Δt)) hst2' y₂ hρ₂).trans (mul_le_mul_of_nonneg_left ?_ hB)
    have e : s • (X * (T₂ * y₂)) - ρ₁ = s • (X * (T₂ * y₂ - S₁ * α)) +
        s • (X * (S₁ * α - y₁)) + (s • (X * y₁) - ρ₁) := by
      simp only [Matrix.mul_sub, smul_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ha1)
    · refine (norm_dens_le hNv hX _).trans (b3.trans ?_)
      gcongr
    · exact (norm_dens_le hNv hX _).trans hres
  have hdens : density (X * S₂ * Vᵀ) = s • (X * y₂) := by
    rw [density, hy₂, hα]
    simp only [Matrix.mul_assoc]
    rfl
  have hE : ‖s • (X * y₂) - ρ₂‖ ≤ E₂ * ε := by
    refine ha2.trans (le_of_eq ?_)
    rw [hE₂]; ring
  constructor
  · have hk : ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C₃ * (ε * ‖S₂‖ + ‖s • (X * y₂) - ρ₂‖) :=
      h3 ε hε hεε₃ X V S₂ K₃ ρ₂ ρ₃ hX hV hc hstep.kStep hst3 hlim.step3
    refine hk.trans ?_
    have h4 : ε * ‖S₂‖ + ‖s • (X * y₂) - ρ₂‖ ≤ ε * (B₂ * (B₁ * BL)) + E₂ * ε := by gcongr
    calc _ ≤ C₃ * (ε * (B₂ * (B₁ * BL)) + E₂ * ε) := by gcongr
      _ ≤ _ := by
        have : 0 ≤ E₂ * ε := by positivity
        nlinarith
  · rw [hdens]
    exact hE.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hε.le)

end Limit

section CN

variable {Nx Nv r d : ℕ}

private theorem limitOp_add_neg {m : Type*} [Fintype m] [DecidableEq m]
    (G : Fin d → Matrix m m ℝ) (Winv : Matrix m m ℝ) (τ : ℝ) (z : Matrix m Unit ℝ) :
    limitOp G Winv τ * z = (2 : ℝ) • z - limitOp G Winv (-τ) * z := by
  simp only [limitOp, neg_div, neg_smul, sub_neg_eq_add, Matrix.sub_mul, Matrix.add_mul,
    Matrix.one_mul]
  module

private theorem norm_limitOp_le {m : Type*} [Fintype m] [DecidableEq m]
    {G : Fin d → Matrix m m ℝ} {Winv : Matrix m m ℝ} {g h : ℝ} (hg0 : 0 ≤ g) (hG : ∀ k, ‖G k‖ ≤ g)
    (hh : ‖Winv‖ ≤ h) (τ : ℝ) : ‖limitOp G Winv τ‖ ≤ ‖(1 : Matrix m m ℝ)‖ + |τ| * (g * h * g) := by
  have hh0 : 0 ≤ h := (norm_nonneg _).trans hh
  rw [limitOp]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [CharP.cast_eq_zero, div_zero, zero_smul, norm_zero]
    positivity
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd']
  have h1 : ‖∑ k, G k * Winv * G k‖ ≤ d * (g * h * g) := by
    refine norm_sum_fin_le fun k => (norm_mul3_le _ _ _).trans ?_
    have := hG k
    gcongr
  calc |τ| / d * ‖∑ k, G k * Winv * G k‖ ≤ |τ| / d * (d * (g * h * g)) := by gcongr
    _ = _ := by field_simp

/-- One step of the Crank–Nicolson–implicit Euler integrator, Algorithm 2.2: (2.19), QR, (2.22),
(2.25).  The output is `u^{n+1} = K₃ Vᵀ`. -/
structure IsCNIEStep (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (σ : Fin Nx → ℝ)
    (v : Fin d → Fin Nv → ℝ) (Δt ε : ℝ) (X : Matrix (Fin Nx) (Fin r) ℝ)
    (L L₁ : Matrix (Fin r) (Fin Nv) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix (Fin Nv) (Fin r) ℝ) (S₂ : Matrix (Fin r) (Fin r) ℝ)
    (K₃ : Matrix (Fin Nx) (Fin r) ℝ) : Prop where
  lStep : IsLStepCN D σ v Δt ε X L L₁
  qr : L₁ = S₁ * Vᵀ
  orth : Vᵀ * V = 1
  sStep : IsSStepCN D σ v Δt ε X V S₁ S₂
  kStep : IsKStep D σ v Δt ε V (X * S₂) K₃

private theorem two_smul_mid {m p : Type*} {A B : Matrix m p ℝ} :
    A = (2 : ℝ) • ((2 : ℝ)⁻¹ • (A + B)) - B := by
  rw [smul_smul]
  norm_num

private theorem cayley_key {n : Type*} [Fintype n] {T₁ T₂ : Matrix n n ℝ}
    (e3 : ∀ z : Matrix n Unit ℝ, T₁ * z = (2 : ℝ) • z - T₂ * z)
    {sα y m₁ m₂ s₂ l₁ : Matrix n Unit ℝ} (e0 : s₂ = (2 : ℝ) • m₂ - sα)
    (e1 : l₁ = (2 : ℝ) • m₁ - y) :
    T₂ * (s₂ - y) = (2 : ℝ) • (T₁ * m₁ - y) + T₁ * (sα - l₁) + (2 : ℝ) • (T₂ * m₂ - sα) := by
  subst e0 e1
  simp only [Matrix.mul_sub, Matrix.mul_smul]
  rw [e3 sα, e3 y]
  module

/-- The two Crank–Nicolson substeps: the density comes back, up to `O(ε)`. -/
private theorem cn_density (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    {BL CA B : ℝ} (hBL : 0 ≤ BL) (hCA : 0 ≤ CA) (hB : 0 ≤ B) :
    ∃ M E ε₀ : ℝ, 0 ≤ M ∧ 0 ≤ E ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsLStepCN D σ v Δt ε X L L₁ → L₁ = S₁ * Vᵀ → Vᵀ * V = 1 →
        IsSStepCN D σ v Δt ε X V S₁ S₂ → Capture v ε CA V →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B → Stable (1 + (Δt / (2 * d)) • limL X D σ) B →
        ‖L₁‖ ≤ M ∧ ‖S₁‖ ≤ M ∧ ‖S₂‖ ≤ M ∧
          ‖S₂ * (Vᵀ * eNorm Nv) - L * eNorm Nv‖ ≤ E * ε := by
  have hτ : Δt / 2 ≠ 0 := by positivity
  have hτ' : -Δt / 2 ≠ 0 := by simpa using hΔt.ne'
  obtain ⟨s₀, hs₀, hσs⟩ := exists_lower_bound hσ
  obtain ⟨C₁, ε₁, hC₁, hε₁, hε₁1, h1⟩ := stiff_main (m := Fin r) (p := Fin Nv) d hτ
    (r * ∑ i, ‖D i‖) (√(r : ℝ) / s₀) (r * ‖Matrix.diagonal σ‖) (∑ i, ‖velPi v i‖) 1 0 B hB
  obtain ⟨C₂, ε₂, hC₂, hε₂, hε₂1, h2⟩ := stiff_main (m := Fin r) (p := Fin r) d hτ'
    (r * ∑ i, ‖D i‖) (√(r : ℝ) / s₀) (r * ‖Matrix.diagonal σ‖)
    (r * ∑ i, ‖velPi v i‖) (√(r : ℝ)) (momC r (∑ i, ‖velPi v i‖) CA) B hB
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = 2 * B * (1 : ℝ) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = 2 * B * (√(r : ℝ)) ^ 2 + 1 := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = 2 * c₁ * BL + BL := ⟨_, rfl⟩
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  obtain ⟨g, hg⟩ : ∃ g, g = (r : ℝ) * ∑ i, ‖D i‖ := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  obtain ⟨h, hh⟩ : ∃ h, h = √(r : ℝ) / s₀ := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, N₁ = ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ + |Δt / 2| * (g * h * g) :=
    ⟨_, rfl⟩
  have hN₁0 : 0 ≤ N₁ := by rw [hN₁]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = B * (2 * (C₁ * BL) + N₁ * (B₁ * CA) + 2 * (C₂ * B₁)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hM2 : 0 ≤ (2 * c₂ + 1) * B₁ := by positivity
  refine ⟨B₁ + (2 * c₂ + 1) * B₁, E, min ε₁ ε₂, by positivity, hE0, lt_min hε₁ hε₂,
    (min_le_left _ _).trans hε₁1, ?_⟩
  intro ε hε hεε X L L₁ S₁ S₂ V hX hLB hstepL hqr hV hstepS hc hst1 hst2
  have hεε₁ : ε < ε₁ := hεε.trans_le (min_le_left _ _)
  have hεε₂ : ε < ε₂ := hεε.trans_le (min_le_right _ _)
  have hε1 : ε ≤ 1 := (hεε₁.trans_le hε₁1).le
  have hdd : Δt / 2 / (d : ℝ) = Δt / (2 * d) := by rw [div_div]
  have hst1' : Stable (1 - (Δt / 2 / d) • limL X D σ) B := by rwa [hdd]
  have hst2' : Stable (1 - (-Δt / 2 / d) • limL X D σ) B := by
    rw [neg_div, neg_div, hdd]
    exact stable_neg hst2
  obtain ⟨a1, -, a3, -⟩ := h1 ε hε hεε₁ _ _ _ _ _ _ _ (stiffHyp_L (D := D) hv hs₀ hσs hX)
    (stable_lift hX hst1') (hstepL.stiff hΔt.ne')
  obtain ⟨b1, -, b3, -⟩ := h2 ε hε hεε₂ _ _ _ _ _ _ _
    (stiffHyp_S (D := D) hv hs₀ hσs hX hV hCA hε.le hε1 hc)
    (stable_lift hX hst2') (hstepS.stiff hΔt.ne' hV)
  rw [← hc₁] at a1
  rw [← hc₂] at b1
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁, Y₁ = (2 : ℝ)⁻¹ • (L₁ + L) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂, Y₂ = (2 : ℝ)⁻¹ • (S₂ + S₁) := ⟨_, rfl⟩
  rw [← hY₁] at a1 a3
  rw [← hY₂] at b1 b3
  have hL₁ : L₁ = (2 : ℝ) • Y₁ - L := by rw [hY₁]; exact two_smul_mid
  have hS₂ : S₂ = (2 : ℝ) • Y₂ - S₁ := by rw [hY₂]; exact two_smul_mid
  have hLn : ‖L₁‖ ≤ B₁ := by
    have h4 : ‖L₁‖ ≤ 2 * ‖Y₁‖ + ‖L‖ := by
      calc ‖L₁‖ = ‖(2 : ℝ) • Y₁ - L‖ := congrArg _ hL₁
        _ ≤ ‖(2 : ℝ) • Y₁‖ + ‖L‖ := norm_sub_le _ _
        _ = 2 * ‖Y₁‖ + ‖L‖ := by rw [norm_smul]; norm_num
    have h5 : ‖Y₁‖ ≤ c₁ * BL := a1.trans (by gcongr)
    rw [hB₁]
    linarith
  have hS₁ : ‖S₁‖ = ‖L₁‖ := by
    rw [hqr, Frobenius.norm_mul_transpose_of_orthonormal hV]
  have hSn : ‖S₁‖ ≤ B₁ := hS₁.le.trans hLn
  have hS₂n : ‖S₂‖ ≤ (2 * c₂ + 1) * B₁ := by
    have h4 : ‖S₂‖ ≤ 2 * ‖Y₂‖ + ‖S₁‖ := by
      calc ‖S₂‖ = ‖(2 : ℝ) • Y₂ - S₁‖ := congrArg _ hS₂
        _ ≤ ‖(2 : ℝ) • Y₂‖ + ‖S₁‖ := norm_sub_le _ _
        _ = 2 * ‖Y₂‖ + ‖S₁‖ := by rw [norm_smul]; norm_num
    have h5 : ‖Y₂‖ ≤ c₂ * B₁ := b1.trans (by gcongr)
    calc ‖S₂‖ ≤ 2 * (c₂ * B₁) + B₁ := by linarith
      _ = _ := by ring
  refine ⟨hLn.trans (le_add_of_nonneg_right hM2), hSn.trans (le_add_of_nonneg_right hM2),
    hS₂n.trans (le_add_of_nonneg_left hB₁0), ?_⟩
  obtain ⟨α, hα⟩ : ∃ α, α = Vᵀ * eNorm Nv := ⟨_, rfl⟩
  rw [← hα] at b3 ⊢
  have hcapt : ‖eNorm Nv - V * α‖ ≤ CA * ε ^ 2 := by rw [hα]; exact hc.e
  have hR₁n : ‖S₁ * α - L₁ * eNorm Nv‖ ≤ B₁ * (CA * ε) := by
    have e : L₁ * (V * α) = S₁ * α := by
      rw [hqr, Matrix.mul_assoc S₁ Vᵀ, ← Matrix.mul_assoc Vᵀ V α, hV, Matrix.one_mul]
    have e' : S₁ * α - L₁ * eNorm Nv = -(L₁ * (eNorm Nv - V * α)) := by
      rw [Matrix.mul_sub, neg_sub, e]
    rw [e', norm_neg]
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul hLn ?_ (norm_nonneg _) hB₁0)
    have h5 : ε ^ 2 ≤ ε := by nlinarith
    exact hcapt.trans (by gcongr)
  have hkey := cayley_key (T₁ := limitOp (AD X D) (Asig X σ)⁻¹ (Δt / 2))
    (T₂ := limitOp (AD X D) (Asig X σ)⁻¹ (-Δt / 2))
    (fun z => by
      have := limitOp_add_neg (AD X D) (Asig X σ)⁻¹ (Δt / 2) z
      rwa [← neg_div] at this)
    (sα := S₁ * α) (y := L * eNorm Nv) (m₁ := Y₁ * eNorm Nv) (m₂ := Y₂ * α) (s₂ := S₂ * α)
    (l₁ := L₁ * eNorm Nv)
    (by rw [← Matrix.smul_mul, ← Matrix.sub_mul, ← hS₂])
    (by rw [← Matrix.smul_mul, ← Matrix.sub_mul, ← hL₁])
  have h5 : ‖limitOp (AD X D) (Asig X σ)⁻¹ (Δt / 2) * (S₁ * α - L₁ * eNorm Nv)‖ ≤
      N₁ * (B₁ * (CA * ε)) := by
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul ?_ hR₁n (norm_nonneg _) hN₁0)
    rw [hN₁]
    exact norm_limitOp_le hg0 (by rw [hg]; exact norm_AD_le hX)
      (by rw [hh]; exact norm_Asig_inv_le hs₀ hX hσs) _
  have h4 := stable_lift hX hst2' (S₂ * α - L * eNorm Nv)
  rw [hkey] at h4
  refine h4.trans ?_
  have a3' : ‖limitOp (AD X D) (Asig X σ)⁻¹ (Δt / 2) * (Y₁ * eNorm Nv) - L * eNorm Nv‖ ≤
      C₁ * ε * BL := a3.trans (by gcongr)
  have b3' : ‖limitOp (AD X D) (Asig X σ)⁻¹ (-Δt / 2) * (Y₂ * α) - S₁ * α‖ ≤ C₂ * ε * B₁ :=
    b3.trans (by gcongr)
  have h6 := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_smul_le (2 : ℝ) (limitOp (AD X D) (Asig X σ)⁻¹ (Δt / 2) * (Y₁ * eNorm Nv) -
      L * eNorm Nv)) h5))
    (norm_smul_le (2 : ℝ) (limitOp (AD X D) (Asig X σ)⁻¹ (-Δt / 2) * (Y₂ * α) - S₁ * α)))
  have h7 : ‖(2 : ℝ)‖ = 2 := by norm_num
  rw [h7] at h6
  calc _ ≤ B * (2 * (C₁ * ε * BL) + N₁ * (B₁ * (CA * ε)) + 2 * (C₂ * ε * B₁)) := by
        refine mul_le_mul_of_nonneg_left (h6.trans ?_) hB
        gcongr
    _ = _ := by rw [hE]; ring

private theorem theorem_3_3_capture (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    {BL CA B : ℝ} (hBL : 0 ≤ BL) (hCA : 0 ≤ CA) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₀ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsCNIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ → Capture v ε CA V →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B → Stable (1 + (Δt / (2 * d)) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        Δt⁻¹ • (ρ₃ - ρ₀) - (d : ℝ)⁻¹ • (limD D σ * ρ₃) = 0 →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * (ε + ‖density (X * L) - ρ₀‖) ∧
        ‖density (X * S₂ * Vᵀ) - density (X * L)‖ ≤ C * ε := by
  have hNv := hv.pos
  obtain ⟨M, E, ε₁, hM, hE0, hε₁, hε₁1, h1⟩ := cn_density (r := r) D hσ hv hΔt hBL hCA hB
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := kStep_final (r := r) D hσ hv hΔt.ne' hCA hB
  refine ⟨C₃ * (M + E + 1) + E, min ε₁ ε₃, by positivity, lt_min hε₁ hε₃,
    (min_le_left _ _).trans hε₁1, ?_⟩
  intro ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₀ ρ₃ hX hLB hstep hc hst1 hst2 hst3 hlim
  have hεε₁ : ε < ε₁ := hεε.trans_le (min_le_left _ _)
  have hεε₃ : ε < ε₃ := hεε.trans_le (min_le_right _ _)
  obtain ⟨-, -, hS₂n, hdiff⟩ := h1 ε hε hεε₁ X L L₁ S₁ S₂ V hX hLB hstep.lStep hstep.qr hstep.orth
    hstep.sStep hc hst1 hst2
  obtain ⟨α, hα⟩ : ∃ α, α = Vᵀ * eNorm Nv := ⟨_, rfl⟩
  rw [← hα] at hdiff
  obtain ⟨y, hy⟩ : ∃ y, y = L * eNorm Nv := ⟨_, rfl⟩
  rw [← hy] at hdiff
  obtain ⟨s, hs⟩ : ∃ s, s = (√(Nv : ℝ))⁻¹ := ⟨_, rfl⟩
  have hdens : density (X * S₂ * Vᵀ) = s • (X * (S₂ * α)) := by
    rw [density, hα, hs]
    simp only [Matrix.mul_assoc]
  have hdens' : density (X * L) = s • (X * y) := by
    rw [density, hy, Matrix.mul_assoc, hs]
  have hdiff' : ‖s • (X * (S₂ * α)) - s • (X * y)‖ ≤ E * ε := by
    rw [← smul_sub, ← Matrix.mul_sub, hs]
    exact (norm_dens_le hNv hX _).trans hdiff
  have hk := h3 ε hε hεε₃ X V S₂ K₃ ρ₀ ρ₃ hX hstep.orth hc hstep.kStep hst3 hlim
  rw [← hα, ← hs] at hk
  constructor
  · refine hk.trans ?_
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = ‖density (X * L) - ρ₀‖ := ⟨_, rfl⟩
    rw [← hδ]
    have hδ0 : 0 ≤ δ := by rw [hδ]; exact norm_nonneg _
    have h4 : ‖s • (X * (S₂ * α)) - ρ₀‖ ≤ E * ε + δ := by
      have e : s • (X * (S₂ * α)) - ρ₀ = (s • (X * (S₂ * α)) - s • (X * y)) +
          (density (X * L) - ρ₀) := by rw [hdens']; abel
      rw [e, hδ]
      exact (norm_add_le _ _).trans (add_le_add hdiff' le_rfl)
    have h5 : ε * ‖S₂‖ + ‖s • (X * (S₂ * α)) - ρ₀‖ ≤ (M + E + 1) * (ε + δ) := by
      have h6 : ε * ‖S₂‖ ≤ ε * M := by gcongr
      have h7 : 0 ≤ (M + E) * δ := by positivity
      nlinarith
    calc _ ≤ C₃ * ((M + E + 1) * (ε + δ)) := by gcongr
      _ ≤ _ := by
        have : 0 ≤ E * (ε + δ) := by positivity
        nlinarith
  · rw [hdens, hdens']
    exact hdiff'.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hε.le)

end CN

section Assumption

variable {Nx Nv r d : ℕ}

/-- The normalized velocity coordinate `𝒱_{k,n} = (√d / √N_v) 𝒱_k` of the paper. -/
noncomputable def velNorm (v : Fin d → Fin Nv → ℝ) (k : Fin d) : Matrix (Fin Nv) Unit ℝ :=
  (√(d : ℝ) / √(Nv : ℝ)) • Matrix.of fun j _ => v k j

/-- Column `i` of `A`, as a column vector. -/
def colOf {n q : Type*} (A : Matrix n q ℝ) (i : q) : Matrix n Unit ℝ := Matrix.of fun j _ => A j i

/-- **Assumption 1** of the paper, (3.3) and (3.4), at one value of `ε`, with `C` the constant in
the `O(·)`: there is an orthogonal `Q` such that the first `d + 1` columns of `V Q` are
`e_n, 𝒱_{1,n} + ε a₁, …, 𝒱_{d,n} + ε a_d` up to `C ε²`, with `‖a_k‖ ≤ C`, `|e_nᵀ a_k| ≤ C ε`, and
such that the other columns `V*_i` satisfy `|𝒱_{k,n}ᵀ V*_i| ≤ C ε` and `|e_nᵀ V*_i| ≤ C ε²`.
The paper reads this for an `ε`-independent `C`: see the quantifiers of the theorems below. -/
def Assumption1 (v : Fin d → Fin Nv → ℝ) (hr : d + 1 ≤ r) (ε C : ℝ)
    (V : Matrix (Fin Nv) (Fin r) ℝ) : Prop :=
  ∃ (Q : Matrix (Fin r) (Fin r) ℝ) (a : Fin d → Matrix (Fin Nv) Unit ℝ),
    Qᵀ * Q = 1 ∧
    ‖colOf (V * Q) (Fin.castLE hr 0) - eNorm Nv‖ ≤ C * ε ^ 2 ∧
    (∀ k, ‖colOf (V * Q) (Fin.castLE hr k.succ) - (velNorm v k + ε • a k)‖ ≤ C * ε ^ 2) ∧
    (∀ k, ‖a k‖ ≤ C) ∧
    (∀ k, ‖(eNorm Nv)ᵀ * a k‖ ≤ C * ε) ∧
    ∀ i : Fin r, d + 1 ≤ i.val →
      (∀ k, ‖(velNorm v k)ᵀ * colOf (V * Q) i‖ ≤ C * ε) ∧
      ‖(eNorm Nv)ᵀ * colOf (V * Q) i‖ ≤ C * ε ^ 2

theorem velNorm_eq (v : Fin d → Fin Nv → ℝ) (k : Fin d) :
    velNorm v k = √(d : ℝ) • (velPi v k * eNorm Nv) := by
  ext j u
  simp only [velNorm, Matrix.smul_apply, Matrix.of_apply, velPi_mul_eNorm_apply, smul_eq_mul]
  ring

theorem colOf_sub {n q : Type*} (A B : Matrix n q ℝ) (i : q) :
    colOf (A - B) i = colOf A i - colOf B i := by
  ext j u
  simp [colOf]

theorem colOf_mul {n q q' : Type*} [Fintype q] (A : Matrix n q ℝ) (B : Matrix q q' ℝ) (i : q') :
    colOf (A * B) i = A * colOf B i := by
  ext j u
  simp [colOf, Matrix.mul_apply]

/-- The component orthogonal to the range of `V`. -/
noncomputable def perp {n q : Type*} [Fintype n] [Fintype q] (V : Matrix n q ℝ)
    (x : Matrix n Unit ℝ) : Matrix n Unit ℝ := x - V * (Vᵀ * x)

section Perp

variable {n q : Type*} [Fintype n] [Fintype q]

theorem perp_add (V : Matrix n q ℝ) (x y : Matrix n Unit ℝ) :
    perp V (x + y) = perp V x + perp V y := by
  simp only [perp, Matrix.mul_add]
  abel

theorem perp_sub (V : Matrix n q ℝ) (x y : Matrix n Unit ℝ) :
    perp V (x - y) = perp V x - perp V y := by
  simp only [perp, Matrix.mul_sub]
  abel

theorem perp_smul (V : Matrix n q ℝ) (c : ℝ) (x : Matrix n Unit ℝ) :
    perp V (c • x) = c • perp V x := by
  simp only [perp, Matrix.mul_smul, smul_sub]

theorem perp_smul_neg (V : Matrix n q ℝ) (c : ℝ) (x : Matrix n Unit ℝ) :
    perp V (-(c • x)) = -(c • perp V x) := by
  simp only [perp, Matrix.mul_neg, Matrix.mul_smul, smul_sub]
  abel

theorem perp_mul [DecidableEq q] {V : Matrix n q ℝ} (hV : Vᵀ * V = 1) (y : Matrix q Unit ℝ) :
    perp V (V * y) = 0 := by
  rw [perp, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, sub_self]

theorem norm_perp_le [DecidableEq q] {V : Matrix n q ℝ} (hV : Vᵀ * V = 1)
    (x : Matrix n Unit ℝ) : ‖perp V x‖ ≤ ‖x‖ := by
  classical
  have h := (isOrthProj_leftProj (n := Unit) hV).compl.norm_le x
  simpa [perp, Matrix.mul_assoc] using h

theorem transpose_mul_perp [DecidableEq q] {V : Matrix n q ℝ} (hV : Vᵀ * V = 1)
    (x y : Matrix n Unit ℝ) : xᵀ * perp V y = (perp V x)ᵀ * perp V y := by
  have h1 : (V * (Vᵀ * x))ᵀ * perp V y = 0 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, perp, Matrix.mul_sub, ← Matrix.mul_assoc Vᵀ, hV,
      Matrix.one_mul, sub_self, Matrix.mul_zero]
  have e : perp V x = x - V * (Vᵀ * x) := rfl
  rw [e, Matrix.transpose_sub, Matrix.sub_mul, h1, sub_zero]

end Perp

theorem Assumption1.capture {v : Fin d → Fin Nv → ℝ} {hr : d + 1 ≤ r} {ε C : ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} (h : Assumption1 v hr ε C V) (hV : Vᵀ * V = 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : Capture v ε (2 * C) V := by
  obtain ⟨Q, a, -, h0, hk, ha, -, -⟩ := h
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans h0
    by_contra hneg
    have h2 := not_le.mp hneg
    have h3 : 0 < ε ^ 2 := by positivity
    nlinarith
  constructor
  · have e1 : perp V (eNorm Nv) =
        -(perp V (colOf (V * Q) (Fin.castLE hr 0) - eNorm Nv)) := by
      rw [perp_sub, colOf_mul, perp_mul hV]
      simp
    change ‖perp V (eNorm Nv)‖ ≤ _
    rw [e1, norm_neg]
    refine (norm_perp_le hV _).trans (h0.trans ?_)
    have : 0 ≤ C * ε ^ 2 := by positivity
    nlinarith
  · intro k
    change ‖perp V (velPi v k * eNorm Nv)‖ ≤ _
    have hd : (1 : ℝ) ≤ √(d : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast (Nat.succ_le_of_lt k.pos)
    have e1 : perp V (velNorm v k) =
        -(perp V (colOf (V * Q) (Fin.castLE hr k.succ) - (velNorm v k + ε • a k))) -
          ε • perp V (a k) := by
      rw [perp_sub, perp_add, perp_smul, colOf_mul, perp_mul hV]
      abel
    have e2 : ‖perp V (velNorm v k)‖ ≤ C * ε ^ 2 + ε * C := by
      rw [e1]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_neg]
        exact (norm_perp_le hV _).trans (hk k)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        have := (norm_perp_le hV (a k)).trans (ha k)
        gcongr
    have e3 : ‖perp V (velNorm v k)‖ = √(d : ℝ) * ‖perp V (velPi v k * eNorm Nv)‖ := by
      rw [velNorm_eq, perp_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have h5 := norm_nonneg (perp V (velPi v k * eNorm Nv))
    have h6 : ε ^ 2 ≤ ε := by nlinarith
    have h7 : C * ε ^ 2 ≤ C * ε := by gcongr
    calc ‖perp V (velPi v k * eNorm Nv)‖ ≤ √(d : ℝ) * ‖perp V (velPi v k * eNorm Nv)‖ :=
          le_mul_of_one_le_left h5 hd
      _ ≤ C * ε ^ 2 + ε * C := e3 ▸ e2
      _ ≤ 2 * C * ε := by nlinarith

private theorem norm_diagonal_le {k : ℕ} {a b : Fin k → ℝ} (h : ∀ i, |a i| ≤ |b i|) :
    ‖Matrix.diagonal a‖ ≤ ‖Matrix.diagonal b‖ := by
  have h1 : ‖Matrix.diagonal a‖ ^ 2 ≤ ‖Matrix.diagonal b‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact sq_le_sq.mpr (h i)
    · simp [Matrix.diagonal_apply_ne _ hij]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

/-- A matrix that is close to having orthonormal columns is close to one that has: the polar
factor, obtained from the singular value decomposition. -/
private theorem exists_polar {m : Type*} [Fintype m] {k : ℕ} (B : Matrix m (Fin k) ℝ)
    (hB : ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Bᵀ * B‖ < 1) :
    ∃ Q₁ : Matrix m (Fin k) ℝ, Q₁ᵀ * Q₁ = 1 ∧
      ‖B - Q₁‖ ≤ ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Bᵀ * B‖ := by
  have hbelow : ∀ y : Matrix (Fin k) Unit ℝ,
      (1 - ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Bᵀ * B‖) * ‖y‖ ≤ ‖(Bᵀ * B) * y‖ := fun y => by
    have e : y = (1 - Bᵀ * B) * y + (Bᵀ * B) * y := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    have h1 : ‖y‖ ≤ ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Bᵀ * B‖ * ‖y‖ + ‖(Bᵀ * B) * y‖ := by
      calc ‖y‖ = ‖(1 - Bᵀ * B) * y + (Bᵀ * B) * y‖ := by rw [← e]
        _ ≤ ‖(1 - Bᵀ * B) * y‖ + ‖(Bᵀ * B) * y‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact Frobenius.norm_mul_le _ _
    linarith
  have hunit := isUnit_det_of_bddBelow _ (sub_pos.mpr hB) hbelow
  have hrank : B.rank = k := by
    rw [← Matrix.rank_transpose_mul_self,
      Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hunit)]
    simp
  obtain ⟨U, W, s, hU, hW, -, hs, -, hB'⟩ := SVD.exists_svd B hrank
  have hW' : W * Wᵀ = 1 := mul_transpose_eq_one_of_transpose_mul_eq_one hW
  refine ⟨U * Wᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ,
      hU, Matrix.one_mul, hW']
  · have e1 : B - U * Wᵀ = U * (Matrix.diagonal (fun i => s i - 1) * Wᵀ) := by
      have : Matrix.diagonal (fun i => s i - 1) = Matrix.diagonal s - 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [this, hB', Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    have e2 : (1 : Matrix (Fin k) (Fin k) ℝ) - Bᵀ * B =
        W * (Matrix.diagonal (fun i => 1 - s i ^ 2) * Wᵀ) := by
      have : Matrix.diagonal (fun i => 1 - s i ^ 2) =
          1 - Matrix.diagonal s * Matrix.diagonal s := by
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst hij; simp [sq]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      have hBB : Bᵀ * B = W * (Matrix.diagonal s * Matrix.diagonal s) * Wᵀ := by
        rw [hB', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.diagonal_transpose]
        calc W * (Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Wᵀ)
            = W * (Matrix.diagonal s * ((Uᵀ * U) * (Matrix.diagonal s * Wᵀ))) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hU, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      rw [this, hBB, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hW', Matrix.mul_assoc]
    rw [e1, e2, Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_mul_of_orthonormal hW,
      Frobenius.norm_mul_transpose_of_orthonormal hW,
      Frobenius.norm_mul_transpose_of_orthonormal hW]
    refine norm_diagonal_le fun i => ?_
    have hi := hs i
    have e3 : 1 - s i ^ 2 = -(s i - 1) * (s i + 1) := by ring
    rw [e3, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < s i + 1)]
    exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)

/-- An isometry extends to an orthogonal matrix. -/
private theorem exists_orthogonal_extension {k r : ℕ} (hr : k ≤ r) (Q₁ : Matrix (Fin r) (Fin k) ℝ)
    (hQ₁ : Q₁ᵀ * Q₁ = 1) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ, Qᵀ * Q = 1 ∧
      ∀ j : Fin k, colOf Q (Fin.castLE hr j) = colOf Q₁ j := by
  let u : Fin r → EuclideanSpace ℝ (Fin r) := fun i =>
    if h : i.val < k then WithLp.toLp 2 (Q₁.col ⟨i, h⟩) else 0
  have hu : Orthonormal ℝ (Set.domRestrict {i : Fin r | i.val < k} u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i.val < k := hi
    have hj' : j.val < k := hj
    simp only [Set.domRestrict, u, hi', hj', ↓reduceDIte]
    rw [inner_toLp_col_col, hQ₁, Matrix.one_apply]
    simp [Fin.ext_iff]
  obtain ⟨b, hb⟩ := hu.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨ofCols b, transpose_ofCols_mul_ofCols b.orthonormal, fun j => ?_⟩
  ext a w
  have h1 := hb (Fin.castLE hr j) j.isLt
  have h2 : u (Fin.castLE hr j) = WithLp.toLp 2 (Q₁.col j) := by
    simp [u]
  simp only [colOf, Matrix.of_apply, ofCols_apply, h1, h2]
  rfl

private theorem norm_colOf_le {n q : Type*} [Fintype n] [Fintype q] (A : Matrix n q ℝ) (i : q) :
    ‖colOf A i‖ ≤ ‖A‖ := by
  have h : ‖colOf A i‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    simp only [colOf, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
    exact Finset.single_le_sum (f := fun j => A a j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

private theorem norm_sq_eq_sum_colOf {n : Type*} [Fintype n] {k : ℕ} (A : Matrix n (Fin k) ℝ) :
    ‖A‖ ^ 2 = ∑ j, ‖colOf A j‖ ^ 2 := by
  simp only [Frobenius.norm_sq_eq_sum, colOf, Matrix.of_apply]
  rw [Finset.sum_comm]
  simp

theorem eNorm_velNorm {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (k : Fin d) :
    (eNorm Nv)ᵀ * velNorm v k = 0 := by
  rw [velNorm_eq, Matrix.mul_smul, eNorm_moment1 hv, smul_zero]

theorem velNorm_velNorm {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (k l : Fin d) :
    (velNorm v k)ᵀ * velNorm v l = (if k = l then (1 : ℝ) else 0) • (1 : Matrix Unit Unit ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by
    have : 0 < d := k.pos
    positivity
  have e : (velPi v k * eNorm Nv)ᵀ = (eNorm Nv)ᵀ * velPi v k := by
    rw [Matrix.transpose_mul, velPi, Matrix.diagonal_transpose]
  rw [velNorm_eq, velNorm_eq, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, e,
    Matrix.mul_assoc, eNorm_moment2 hv, smul_smul, smul_smul,
    Real.mul_self_sqrt (Nat.cast_nonneg d)]
  congr 1
  split_ifs <;> simp [hd]

/-- The columns `e_n, 𝒱_{1,n}, …, 𝒱_{d,n}`. -/
private noncomputable def targetCol (v : Fin d → Fin Nv → ℝ) :
    Fin (d + 1) → Matrix (Fin Nv) Unit ℝ :=
  Fin.cases (eNorm Nv) (velNorm v)

private noncomputable def targetMat (v : Fin d → Fin Nv → ℝ) : Matrix (Fin Nv) (Fin (d + 1)) ℝ :=
  Matrix.of fun a j => targetCol v j a ()

private theorem colOf_targetMat (v : Fin d → Fin Nv → ℝ) (j : Fin (d + 1)) :
    colOf (targetMat v) j = targetCol v j := by
  ext a u
  rfl

private theorem mul_apply_colOf {n p q : Type*} [Fintype n] (A : Matrix n p ℝ) (B : Matrix n q ℝ)
    (i : p) (j : q) : (Aᵀ * B) i j = ((colOf A i)ᵀ * colOf B j) () () := by
  simp [Matrix.mul_apply, colOf]

private theorem targetMat_orth {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) :
    (targetMat v)ᵀ * targetMat v = 1 := by
  ext i j
  rw [mul_apply_colOf, colOf_targetMat, colOf_targetMat]
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · simp [targetCol, eNorm_transpose_mul hv.pos]
  · simp only [targetCol, Fin.cases_zero, Fin.cases_succ, eNorm_velNorm hv]
    simp [Fin.ext_iff]
  · have : (velNorm v k)ᵀ * eNorm Nv = ((eNorm Nv)ᵀ * velNorm v k)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [targetCol, Fin.cases_zero, Fin.cases_succ, this, eNorm_velNorm hv]
    simp [Fin.ext_iff]
  · simp only [targetCol, Fin.cases_succ, velNorm_velNorm hv]
    by_cases h : k = l
    · subst h; simp
    · have h' : k.succ ≠ l.succ := fun e => h (Fin.succ_injective _ e)
      simp [h, Matrix.one_apply_ne h']

/-- The constant of the near-orthonormality of `Vᵀ (e_n, 𝒱_{1,n}, …, 𝒱_{d,n})`. -/
private noncomputable def capκ (d : ℕ) (C : ℝ) : ℝ := ((d : ℝ) + 1) * ((√(d : ℝ) + 1) * C) ^ 2

/-- **Capture implies Assumption 1**: from `e_n ∈ range V + O(ε²)`, `Π_k e_n ∈ range V + O(ε)` one
recovers the orthogonal `Q` and the vectors `a_k` of (3.3), (3.4). -/
theorem Capture.assumption1 {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (hr : d + 1 ≤ r)
    {ε C : ℝ} {V : Matrix (Fin Nv) (Fin r) ℝ} (hV : Vᵀ * V = 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) (hsmall : capκ d C * ε ^ 2 < 1) (h : Capture v ε C V) :
    Assumption1 v hr ε
      (C + √(r : ℝ) * capκ d C + √(d : ℝ) * C + √(d : ℝ) * C ^ 2 + capκ d C) V := by
  have hNv := hv.pos
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = capκ d C := ⟨_, rfl⟩
  rw [← hκ] at hsmall ⊢
  have hκ0 : 0 ≤ κ := by rw [hκ, capκ]; positivity
  have hsd : 0 ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hsr : 0 ≤ √(r : ℝ) := Real.sqrt_nonneg _
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hperp_e : ‖perp V (eNorm Nv)‖ ≤ C * ε ^ 2 := h.e
  have hperp_v : ∀ k, ‖perp V (velNorm v k)‖ ≤ √(d : ℝ) * C * ε := fun k => by
    rw [velNorm_eq, perp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsd, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.vel k) hsd
  obtain ⟨E, hE⟩ : ∃ E, E = targetMat v := ⟨_, rfl⟩
  have hEE : Eᵀ * E = 1 := by rw [hE]; exact targetMat_orth hv
  have hEc : ∀ j, colOf E j = targetCol v j := fun j => by rw [hE]; exact colOf_targetMat v j
  obtain ⟨B, hB⟩ : ∃ B, B = Vᵀ * E := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = E - V * B := ⟨_, rfl⟩
  have hBc : ∀ j, colOf B j = Vᵀ * targetCol v j := fun j => by rw [hB, colOf_mul, hEc]
  have hWc : ∀ j, colOf W j = perp V (targetCol v j) := fun j => by
    rw [hW, colOf_sub, colOf_mul, hEc, hBc]
    rfl
  have hWn : ‖W‖ ^ 2 ≤ κ * ε ^ 2 := by
    rw [norm_sq_eq_sum_colOf]
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))),
        ‖colOf W j‖ ^ 2 ≤ ((√(d : ℝ) + 1) * C * ε) ^ 2 := fun j _ => by
      rw [hWc]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [targetCol, Fin.cases_zero]
        refine hperp_e.trans ?_
        have h2 : C * ε ^ 2 ≤ C * ε := by gcongr
        have h3 : 0 ≤ √(d : ℝ) * C * ε := by positivity
        nlinarith
      · simp only [targetCol, Fin.cases_succ]
        refine (hperp_v k).trans ?_
        have h3 : 0 ≤ C * ε := by positivity
        nlinarith
    calc ∑ j, ‖colOf W j‖ ^ 2 ≤ ∑ _j : Fin (d + 1), ((√(d : ℝ) + 1) * C * ε) ^ 2 :=
          Finset.sum_le_sum h1
      _ = κ * ε ^ 2 := by
        rw [hκ, capκ]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have hBB : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) - Bᵀ * B = Wᵀ * W := by
    have e1 : Eᵀ * V = Bᵀ := by rw [hB, Matrix.transpose_mul, Matrix.transpose_transpose]
    have e2 : Vᵀ * E = B := hB.symm
    rw [hW, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hEE,
      Matrix.transpose_mul, ← Matrix.mul_assoc Eᵀ, e1, Matrix.mul_assoc Bᵀ Vᵀ E, e2,
      Matrix.mul_assoc Bᵀ Vᵀ (V * B), ← Matrix.mul_assoc Vᵀ V B, hV, Matrix.one_mul]
    abel
  have hBn : ‖(1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) - Bᵀ * B‖ ≤ κ * ε ^ 2 := by
    rw [hBB]
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose, ← sq]
    exact hWn
  obtain ⟨Q₁, hQ₁, hQ₁B⟩ := exists_polar B (hBn.trans_lt hsmall)
  obtain ⟨Q, hQ, hQc⟩ := exists_orthogonal_extension hr Q₁ hQ₁
  have hBQ : ‖B - Q₁‖ ≤ κ * ε ^ 2 := hQ₁B.trans hBn
  have hδ : ∀ j, ‖colOf (Q₁ - B) j‖ ≤ κ * ε ^ 2 := fun j => by
    refine (norm_colOf_le _ _).trans ?_
    rw [norm_sub_rev]
    exact hBQ
  have hVn : ∀ x : Matrix (Fin r) Unit ℝ, ‖V * x‖ = ‖x‖ := fun x =>
    Frobenius.norm_mul_of_orthonormal hV x
  have hcol : ∀ j, colOf (V * Q) (Fin.castLE hr j) =
      targetCol v j - perp V (targetCol v j) + V * colOf (Q₁ - B) j := fun j => by
    have e1 : colOf Q₁ j = colOf B j + colOf (Q₁ - B) j := by
      ext a u
      simp [colOf]
    rw [colOf_mul, hQc, e1, Matrix.mul_add, hBc, perp]
    abel
  have hqn : ∀ i, ‖colOf Q i‖ ≤ √(r : ℝ) := fun i => by
    have h1 := norm_of_orthonormal hQ
    simp only [Fintype.card_fin] at h1
    exact (norm_colOf_le _ _).trans h1.le
  have hortho : ∀ (j : Fin (d + 1)) (i : Fin r), d + 1 ≤ i.val →
      ‖(targetCol v j)ᵀ * colOf (V * Q) i‖ ≤ √(r : ℝ) * κ * ε ^ 2 := fun j i hi => by
    have e0 : (colOf Q₁ j)ᵀ * colOf Q i = 0 := by
      ext a b
      have hne : Fin.castLE hr j ≠ i := fun e => by
        have : (Fin.castLE hr j).val = i.val := congrArg _ e
        simp only [Fin.val_castLE] at this
        omega
      have := congrFun (congrFun hQ (Fin.castLE hr j)) i
      rw [mul_apply_colOf, Matrix.one_apply_ne hne, hQc] at this
      exact this
    have e1 : (targetCol v j)ᵀ * colOf (V * Q) i = -((colOf (Q₁ - B) j)ᵀ * colOf Q i) := by
      have e2 : (targetCol v j)ᵀ * V = (colOf B j)ᵀ := by
        rw [hBc, Matrix.transpose_mul, Matrix.transpose_transpose]
      have e3 : colOf B j = colOf Q₁ j - colOf (Q₁ - B) j := by
        ext a u
        simp [colOf]
      rw [colOf_mul, ← Matrix.mul_assoc, e2, e3, Matrix.transpose_sub, Matrix.sub_mul, e0, zero_sub]
    rw [e1, norm_neg]
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    calc _ ≤ (κ * ε ^ 2) * √(r : ℝ) := mul_le_mul (hδ j) (hqn i) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨Q, fun k => -(ε⁻¹ • perp V (velNorm v k)), hQ, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 := hcol 0
    simp only [targetCol, Fin.cases_zero] at e1
    rw [e1]
    have e2 : eNorm Nv - perp V (eNorm Nv) + V * colOf (Q₁ - B) 0 - eNorm Nv =
        V * colOf (Q₁ - B) 0 - perp V (eNorm Nv) := by abel
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    rw [hVn]
    have h3 := hδ 0
    have h4 : 0 ≤ ε ^ 2 := by positivity
    have h5 : ‖colOf (Q₁ - B) 0‖ ≤ √(r : ℝ) * κ * ε ^ 2 + κ * ε ^ 2 := by
      have : 0 ≤ √(r : ℝ) * κ * ε ^ 2 := by positivity
      linarith
    have h6 : 0 ≤ √(d : ℝ) * C * ε ^ 2 + √(d : ℝ) * C ^ 2 * ε ^ 2 := by positivity
    nlinarith
  · intro k
    have e1 := hcol k.succ
    simp only [targetCol, Fin.cases_succ] at e1
    rw [e1]
    have e2 : velNorm v k - perp V (velNorm v k) + V * colOf (Q₁ - B) k.succ -
        (velNorm v k + ε • -(ε⁻¹ • perp V (velNorm v k))) = V * colOf (Q₁ - B) k.succ := by
      rw [smul_neg, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
      abel
    rw [e2, hVn]
    refine (hδ _).trans ?_
    have h4 : 0 ≤ ε ^ 2 := by positivity
    have h6 : 0 ≤ (C + √(r : ℝ) * κ + √(d : ℝ) * C + √(d : ℝ) * C ^ 2) * ε ^ 2 := by positivity
    nlinarith
  · intro k
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    have h3 := hperp_v k
    have h4 : ε⁻¹ * ‖perp V (velNorm v k)‖ ≤ ε⁻¹ * (√(d : ℝ) * C * ε) := by gcongr
    have h5 : ε⁻¹ * (√(d : ℝ) * C * ε) = √(d : ℝ) * C := by field_simp
    rw [h5] at h4
    have h6 : 0 ≤ C + √(r : ℝ) * κ + √(d : ℝ) * C ^ 2 + κ := by positivity
    linarith
  · intro k
    rw [Matrix.mul_neg, Matrix.mul_smul, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε), transpose_mul_perp hV]
    have h3 : ‖(perp V (eNorm Nv))ᵀ * perp V (velNorm v k)‖ ≤
        (C * ε ^ 2) * (√(d : ℝ) * C * ε) := by
      refine (Frobenius.norm_mul_le _ _).trans ?_
      rw [Frobenius.norm_transpose]
      exact mul_le_mul hperp_e (hperp_v k) (norm_nonneg _) (by positivity)
    have h4 : ε⁻¹ * ‖(perp V (eNorm Nv))ᵀ * perp V (velNorm v k)‖ ≤
        ε⁻¹ * ((C * ε ^ 2) * (√(d : ℝ) * C * ε)) := by gcongr
    have h5 : ε⁻¹ * ((C * ε ^ 2) * (√(d : ℝ) * C * ε)) = √(d : ℝ) * C ^ 2 * ε ^ 2 := by
      field_simp
    rw [h5] at h4
    have h6 : √(d : ℝ) * C ^ 2 * ε ^ 2 ≤ √(d : ℝ) * C ^ 2 * ε := by gcongr
    have h7 : 0 ≤ (C + √(r : ℝ) * κ + √(d : ℝ) * C + κ) * ε := by positivity
    nlinarith
  · intro i hi
    constructor
    · intro k
      have h3 := hortho k.succ i hi
      simp only [targetCol, Fin.cases_succ] at h3
      refine h3.trans ?_
      have h4 : √(r : ℝ) * κ * ε ^ 2 ≤ √(r : ℝ) * κ * ε := by gcongr
      have h7 : 0 ≤ (C + √(d : ℝ) * C + √(d : ℝ) * C ^ 2 + κ) * ε := by positivity
      nlinarith
    · have h3 := hortho 0 i hi
      simp only [targetCol, Fin.cases_zero] at h3
      refine h3.trans ?_
      have h7 : 0 ≤ (C + √(d : ℝ) * C + √(d : ℝ) * C ^ 2 + κ) * ε ^ 2 := by positivity
      nlinarith

end Assumption

section Main

variable {Nx Nv r d : ℕ}

theorem Capture.mono {v : Fin d → Fin Nv → ℝ} {ε C C' : ℝ} {V : Matrix (Fin Nv) (Fin r) ℝ}
    (h : Capture v ε C V) (hε : 0 ≤ ε) (hC : C ≤ C') : Capture v ε C' V where
  e := h.e.trans (by gcongr)
  vel k := (h.vel k).trans (by gcongr)

private theorem Assumption1.capture' {v : Fin d → Fin Nv → ℝ} {hr : d + 1 ≤ r} {ε C : ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} (h : Assumption1 v hr ε C V) (hV : Vᵀ * V = 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : Capture v ε (2 * |C|) V :=
  (h.capture hV hε hε1).mono hε.le (by linarith [le_abs_self C])

/-- **Theorem 3.2 of arXiv 1907.04247.**  Fix the mesh: `D_k`, `σ > 0`, a quadrature `v`, `Δt > 0`.
Given bounds `BL, CA, B` there are `C, ε₀`, independent of `ε`, such that for every `ε < ε₀`: if
`u^{n+1} = K₃ Vᵀ` is computed from `u^n = X L` by the implicit Euler integrator (2.18), (2.21),
(2.25), if the new basis `V` satisfies Assumption 1 with constant `CA`, and if `ρ₁, ρ₂, ρ₃` solve
the limit scheme (3.16), (3.20), (3.11) started from the density of `u^n`, then
`‖u^{n+1} - ρ₃ eᵀ‖ ≤ C ε`, and the numerical density after the first two substeps is within `C ε`
of `ρ₂`.

Differences from the paper.  The proof is rigorous, not a Hilbert expansion: nothing is assumed
about the `ε`-dependence of `X, L, V`, which may vary with `ε` as they do along a run; only the
bounds `‖L‖ ≤ BL` and the constant `CA` are uniform.  The conclusion is in the Frobenius norm, which
dominates the paper's `‖·‖₂`.  The inverses `(I ∓ (Δt / d) 𝓛)⁻¹`, `(I - (Δt / d) ∑ₖ D_k Σ⁻¹ D_k)⁻¹`
that the paper writes in (3.26) and uses tacitly are assumptions here, as the bounds `Stable · B`;
`theorem_3_2_counterexample` shows they cannot be dropped.  For skew `D_k` they hold, see
`theorem_3_2_skew`.  The density is `u e / N_v`; the paper's "`ρ^n = u^n e`" misses the factor. -/
theorem theorem_3_2 (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ r) {BL CA B : ℝ} (hBL : 0 ≤ BL) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ →
        Assumption1 v hr ε CA V →
        Stable (1 - (Δt / d) • limL X D σ) B → Stable (1 + (Δt / d) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        IsIELimit X D σ Δt (density (X * L)) ρ₁ ρ₂ ρ₃ →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * ε ∧ ‖density (X * S₂ * Vᵀ) - ρ₂‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hC, hε₀, hε₀1, h⟩ := theorem_3_2_capture (r := r) D hσ hv hΔt.ne' hBL
    (mul_nonneg zero_le_two (abs_nonneg CA)) hB
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₁ ρ₂ ρ₃ hX hL hs hA h1 h2 h3 hl => ?_⟩
  exact h ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₁ ρ₂ ρ₃ hX hL hs
    (hA.capture' hs.orth hε (hεε.trans_le hε₀1).le) h1 h2 h3 hl

/-- **Equation (3.26) of arXiv 1907.04247.**  The density after the first two substeps of the limit
scheme solves `(I - (Δt / d)² 𝓛²) ρ₂ = ρ`: rank one, but the error `(Δt / d)² 𝓛² ρ₂` is that of a
second-order perturbation of the identity, and it is not small unless `Δt ≪ (Δx)²`. -/
theorem IsIELimit.rho_two_thirds {X : Matrix (Fin Nx) (Fin r) ℝ}
    {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ} {Δt : ℝ}
    {ρ ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ} (h : IsIELimit X D σ Δt ρ ρ₁ ρ₂ ρ₃) (hΔt : Δt ≠ 0) :
    (1 - (Δt / d) ^ 2 • (limL X D σ * limL X D σ)) * ρ₂ = ρ := by
  have h1 := limit_eq_sub hΔt h.step1
  have h2 := limit_eq_add hΔt h.step2
  rw [← div_eq_mul_inv] at h1 h2
  rw [← h1, ← h2, ← Matrix.mul_assoc]
  congr 1
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul, sq]
  abel

/-- `‖𝓛‖ ≤ C_d / ((Δx)² min σ)`, the bound after (3.26) of arXiv 1907.04247, here with a constant
that also depends on `r` because the norm is the Frobenius norm. -/
theorem norm_limL_le {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    {σ : Fin Nx → ℝ} {s : ℝ} (hX : Xᵀ * X = 1) (hs : 0 < s) (hσ : ∀ i, s ≤ σ i) {b : ℝ}
    (hb : ∀ k, ‖D k‖ ≤ b) (hb0 : 0 ≤ b) :
    ‖limL X D σ‖ ≤ d * (r ^ 3 * √(r : ℝ) * b ^ 2) / s := by
  have hX1 := norm_of_orthonormal hX
  simp only [Fintype.card_fin] at hX1
  have hA : ∀ k, ‖AD X D k‖ ≤ r * b := fun k => by
    refine (norm_mul3_le _ _ _).trans ?_
    rw [Frobenius.norm_transpose, hX1, mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg r)]
    have := hb k
    gcongr
  have hinv := norm_Asig_inv_le hs hX hσ
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hsr : √(r : ℝ) * √(r : ℝ) = r := Real.mul_self_sqrt hr0
  have h1 : ‖limL X D σ‖ ≤ d * (√(r : ℝ) * (r * b) * (√(r : ℝ) / s) * (r * b) * √(r : ℝ)) := by
    refine norm_sum_fin_le fun k => ?_
    have e : ‖X * AD X D k * (Asig X σ)⁻¹ * AD X D k * Xᵀ‖ ≤
        ‖X‖ * ‖AD X D k‖ * ‖(Asig X σ)⁻¹‖ * ‖AD X D k‖ * ‖Xᵀ‖ := by
      refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact norm_mul3_le _ _ _
    refine e.trans ?_
    rw [Frobenius.norm_transpose, hX1]
    have := hA k
    gcongr
  refine h1.trans (le_of_eq ?_)
  have e : √(r : ℝ) * (r * b) * (√(r : ℝ) / s) * (r * b) * √(r : ℝ) =
      (√(r : ℝ) * √(r : ℝ)) * (r ^ 2 * √(r : ℝ) * b ^ 2) / s := by ring
  rw [e, hsr]
  ring

/-- **The `O((Δt)² / (Δx)⁴)` bound of Theorem 3.2 of arXiv 1907.04247**, for the limit scheme: if
`‖D_k‖ ≤ b / Δx`, then `‖ρ₂ - ρ‖ ≤ K (Δt)² / (Δx)⁴ ‖ρ‖`, with `K` explicit.  With the second
conclusion of `theorem_3_2` this is the claim `‖ρ^{n+2/3} - ρ^n‖ = O((Δt)² / (Δx)⁴) + O(ε)`. -/
theorem IsIELimit.norm_sub_le {X : Matrix (Fin Nx) (Fin r) ℝ}
    {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ} {Δt Δx s b B : ℝ}
    {ρ ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ} (h : IsIELimit X D σ Δt ρ ρ₁ ρ₂ ρ₃) (hΔt : Δt ≠ 0)
    (hΔx : 0 < Δx) (hX : Xᵀ * X = 1) (hs : 0 < s) (hσ : ∀ i, s ≤ σ i) (hb0 : 0 ≤ b)
    (hb : ∀ k, ‖D k‖ ≤ b / Δx) (hB : 0 ≤ B) (hst1 : Stable (1 - (Δt / d) • limL X D σ) B)
    (hst2 : Stable (1 + (Δt / d) • limL X D σ) B) :
    ‖ρ₂ - ρ‖ ≤ (B ^ 2 * (r ^ 3 * √(r : ℝ) * b ^ 2 / s) ^ 2) * ((Δt) ^ 2 / (Δx) ^ 4) * ‖ρ‖ := by
  have hd : (d : ℝ) ≠ 0 ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (by positivity)
  have h1 := limit_eq_sub hΔt h.step1
  have h2 := limit_eq_add hΔt h.step2
  rw [← div_eq_mul_inv] at h1 h2
  have h3 := h.rho_two_thirds hΔt
  have hn1 : ‖ρ₁‖ ≤ B * ‖ρ‖ := by
    have := hst1 ρ₁
    rwa [h1] at this
  have hn2 : ‖ρ₂‖ ≤ B * ‖ρ₁‖ := by
    have := hst2 ρ₂
    rwa [h2] at this
  have hn3 : ‖ρ₂‖ ≤ B ^ 2 * ‖ρ‖ := by
    refine hn2.trans ?_
    calc B * ‖ρ₁‖ ≤ B * (B * ‖ρ‖) := by gcongr
      _ = _ := by ring
  have e : ρ₂ - ρ = (Δt / d) ^ 2 • (limL X D σ * limL X D σ * ρ₂) := by
    rw [← h3, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hL : ‖limL X D σ‖ ≤ d * (r ^ 3 * √(r : ℝ) * (b / Δx) ^ 2) / s :=
    norm_limL_le hX hs hσ hb (by positivity)
  have hLL : ‖limL X D σ * limL X D σ * ρ₂‖ ≤ ‖limL X D σ‖ ^ 2 * ‖ρ₂‖ := by
    rw [sq]
    exact norm_mul3_le _ _ _
  rcases hd with hd | hd
  · calc (Δt / d) ^ 2 * ‖limL X D σ * limL X D σ * ρ₂‖
        ≤ (Δt / d) ^ 2 * ((d * (r ^ 3 * √(r : ℝ) * (b / Δx) ^ 2) / s) ^ 2 * (B ^ 2 * ‖ρ‖)) := by
          gcongr
          exact hLL.trans (by gcongr)
      _ = _ := by field_simp
  · subst hd
    simp only [Nat.cast_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul]
    positivity

private theorem density_add_le {u u' : Matrix (Fin Nx) (Fin Nv) ℝ} :
    density (u - u') = density u - density u' := by
  simp only [density, Matrix.sub_mul, smul_sub]

private theorem density_rank_one (hNv : 0 < Nv) (ρ : Matrix (Fin Nx) Unit ℝ) :
    density (ρ * (eOne Nv)ᵀ) = ρ := by
  have h : √(Nv : ℝ) ≠ 0 := by have := sqrt_Nv_ge hNv; positivity
  rw [density, eOne_eq hNv, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, eNorm_transpose_mul hNv, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ h, one_smul]

private theorem norm_density_le (hNv : 0 < Nv) (u : Matrix (Fin Nx) (Fin Nv) ℝ) :
    ‖density u‖ ≤ ‖u‖ := by
  rw [density, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖u * eNorm Nv‖ ≤ ‖u‖ := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [norm_eNorm hNv, mul_one]
  calc (√(Nv : ℝ))⁻¹ * ‖u * eNorm Nv‖ ≤ 1 * ‖u‖ := by
        gcongr
        exact sqrt_Nv_inv_le hNv
    _ = _ := one_mul _

/-- **Theorem 3.3 of arXiv 1907.04247.**  Fix the mesh and `Δt > 0`.  There are `C, ε₀` independent
of `ε` such that for `ε < ε₀`: if `u^{n+1} = K₃ Vᵀ` is computed from `u^n = X L` by the
Crank–Nicolson–implicit Euler integrator (2.19), (2.22), (2.25), if `u^n = ρ₀ eᵀ + O(ε)`, if
Assumption 1 holds for the new basis `V` and if `(ρ₃ - ρ₀) / Δt = (1 / d) ∑ₖ D_k Σ⁻¹ D_k ρ₃`, then
`‖u^{n+1} - ρ₃ eᵀ‖ ≤ C ε`, and the two Crank–Nicolson substeps return the density `ρ₀` up to
`C ε`.  So the limit is implicit Euler for the diffusion equation.

Differences from the paper.  As in `theorem_3_2` the proof is rigorous, with no expansion in `ε`.
The bounds on `(I ∓ (Δt / (2 d)) 𝓛)⁻¹` are assumed: the paper writes these inverses in (A.12),
(A.13).  Hence "independent of `Δt`" must be read with care: `C` depends on `Δt` through `B`, and
the second inverse does not exist when `2 d / Δt` is an eigenvalue of `-𝓛`, a discrete set of `Δt`
at which the proof breaks down; whether the conclusion survives there is not decided here.  Away
from that set there is no restriction `Δt ≪ (Δx)²`, and `B = 1` in the first and the third bound
for skew `D_k`.  The hypothesis of well-prepared data can be dropped altogether under
Assumption 1, see `theorem_3_3_unprepared`: Assumption 1 on the new basis does that work. -/
theorem theorem_3_3 (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ r) {BL CA B C₀ : ℝ} (hBL : 0 ≤ BL) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₀ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → ‖X * L - ρ₀ * (eOne Nv)ᵀ‖ ≤ C₀ * ε →
        IsCNIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ → Assumption1 v hr ε CA V →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B → Stable (1 + (Δt / (2 * d)) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        Δt⁻¹ • (ρ₃ - ρ₀) - (d : ℝ)⁻¹ • (limD D σ * ρ₃) = 0 →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * ε ∧ ‖density (X * S₂ * Vᵀ) - ρ₀‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hC, hε₀, hε₀1, h⟩ := theorem_3_3_capture (r := r) D hσ hv hΔt hBL
    (mul_nonneg zero_le_two (abs_nonneg CA)) hB
  refine ⟨(C + 1) * (1 + C₀) , ε₀, by positivity, hε₀,
    fun ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₀ ρ₃ hX hL hwp hs hA h1 h2 h3 hl => ?_⟩
  have hδ : ‖density (X * L) - ρ₀‖ ≤ C₀ * ε := by
    have e : density (X * L) - ρ₀ = density (X * L - ρ₀ * (eOne Nv)ᵀ) := by
      rw [density_add_le, density_rank_one hv.pos]
    rw [e]
    exact (norm_density_le hv.pos _).trans hwp
  obtain ⟨a, b⟩ := h ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₀ ρ₃ hX hL hs
    (hA.capture' hs.orth hε (hεε.trans_le hε₀1).le) h1 h2 h3 hl
  constructor
  · refine a.trans ?_
    calc C * (ε + ‖density (X * L) - ρ₀‖) ≤ C * (ε + C₀ * ε) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hC₀ hε.le, mul_nonneg (mul_nonneg hC hC₀) hε.le]
  · have e : density (X * S₂ * Vᵀ) - ρ₀ =
        (density (X * S₂ * Vᵀ) - density (X * L)) + (density (X * L) - ρ₀) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add b hδ).trans ?_)
    nlinarith [mul_nonneg hC₀ hε.le, mul_nonneg (mul_nonneg hC hC₀) hε.le]

/-- **Theorem 3.3 of arXiv 1907.04247 without well-prepared data.**  Under Assumption 1 on the new
velocity basis the hypothesis `u^n = ρ₀ eᵀ + O(ε)` is not needed: `ρ₀` may be replaced by the
density of `u^n`, whatever `u^n` is.  The final implicit `K`-step relaxes to rank one, and the two
Crank–Nicolson substeps return the density.  This is stronger than the paper, which says in its
Remark 7 that well-prepared data are needed; what is needed is Assumption 1, and it is for the
propagation of that assumption, `lemma_B1`, that the structure of `u^n` matters. -/
theorem theorem_3_3_unprepared (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ r) {BL CA B : ℝ} (hBL : 0 ≤ BL) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsCNIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ →
        Assumption1 v hr ε CA V →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B → Stable (1 + (Δt / (2 * d)) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        Δt⁻¹ • (ρ₃ - density (X * L)) - (d : ℝ)⁻¹ • (limD D σ * ρ₃) = 0 →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * ε ∧
          ‖density (X * S₂ * Vᵀ) - density (X * L)‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hC, hε₀, hε₀1, h⟩ := theorem_3_3_capture (r := r) D hσ hv hΔt hBL
    (mul_nonneg zero_le_two (abs_nonneg CA)) hB
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₃ hX hL hs hA h1 h2 h3 hl => ?_⟩
  obtain ⟨a, b⟩ := h ε hε hεε X L L₁ S₁ S₂ V K₃ (density (X * L)) ρ₃ hX hL hs
    (hA.capture' hs.orth hε (hεε.trans_le hε₀1).le) h1 h2 h3 hl
  rw [sub_self, norm_zero, add_zero] at a
  exact ⟨a, b⟩

/-- **The Cayley cancellation of arXiv 1907.04247**, (A.12)–(A.14), for the limit scheme: if
`(I - c 𝓛) ρ₁ = (I + c 𝓛) ρ` and `(I + c 𝓛) ρ₂ = (I - c 𝓛) ρ₁`, and `I + c 𝓛` is injective, then
`ρ₂ = ρ`.  No commutativity is needed. -/
theorem cayley_cancel {T : Matrix (Fin Nx) (Fin Nx) ℝ} {c B : ℝ}
    {ρ ρ₁ ρ₂ : Matrix (Fin Nx) Unit ℝ} (hst : Stable (1 + c • T) B)
    (h1 : (1 - c • T) * ρ₁ = (1 + c • T) * ρ) (h2 : (1 + c • T) * ρ₂ = (1 - c • T) * ρ₁) :
    ρ₂ = ρ := by
  have h3 := hst (ρ₂ - ρ)
  rw [Matrix.mul_sub, h2, h1, sub_self, norm_zero, mul_zero] at h3
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h3 (norm_nonneg _)))

end Main

section Skew

variable {Nx Nv r d : ℕ}

/-- For skew `G_k` and a positive `W⁻¹`, `∑ₖ G_k W⁻¹ G_k ≤ 0`, so `1 - c ∑ₖ G_k W⁻¹ G_k` is bounded
below by one. -/
theorem stable_of_skew {n : Type*} [Fintype n] [DecidableEq n] {G : Fin d → Matrix n n ℝ}
    {Wi : Matrix n n ℝ} (hG : ∀ k, (G k)ᵀ = -G k)
    (hWi : ∀ z : Matrix n Unit ℝ, 0 ≤ ⟪z, Wi * z⟫) {c : ℝ} (hc : 0 ≤ c) (x : Matrix n Unit ℝ) :
    ‖x‖ ≤ ‖(1 - c • ∑ k, G k * Wi * G k) * x‖ := by
  by_cases hx : ‖x‖ = 0
  · rw [hx]; exact norm_nonneg _
  have hx' : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have h1 : ∀ k, ⟪x, (G k * Wi * G k) * x⟫ ≤ 0 := fun k => by
    have e : (G k * Wi * G k) * x = G k * (Wi * (G k * x)) := by simp only [Matrix.mul_assoc]
    rw [e, Frobenius.inner_mul_left', hG k, Matrix.neg_mul, inner_neg_left]
    have := hWi (G k * x)
    linarith
  have h2 : ‖x‖ ^ 2 ≤ ⟪x, (1 - c • ∑ k, G k * Wi * G k) * x⟫ := by
    rw [Matrix.sub_mul, Matrix.one_mul, inner_sub_right, real_inner_self_eq_norm_sq,
      Matrix.smul_mul, inner_smul_right, Matrix.sum_mul, inner_sum]
    have h3 : ∑ k, ⟪x, (G k * Wi * G k) * x⟫ ≤ 0 := Finset.sum_nonpos fun k _ => h1 k
    nlinarith
  have h3 := real_inner_le_norm x ((1 - c • ∑ k, G k * Wi * G k) * x)
  have h4 : ‖x‖ * ‖x‖ ≤ ‖(1 - c • ∑ k, G k * Wi * G k) * x‖ * ‖x‖ := by nlinarith
  exact le_of_mul_le_mul_right h4 hx'

theorem AD_skew {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    (hD : ∀ k, (D k)ᵀ = -D k) (k : Fin d) : (AD X D k)ᵀ = -AD X D k := by
  simp only [AD, Matrix.transpose_mul, Matrix.transpose_transpose, hD k, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.mul_assoc]

private theorem inner_inv_nonneg {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (hpos : ∀ y : Matrix n Unit ℝ, 0 ≤ ⟪y, A * y⟫) (z : Matrix n Unit ℝ) :
    0 ≤ ⟪z, A⁻¹ * z⟫ := by
  have h := hpos (A⁻¹ * z)
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul] at h
  rwa [real_inner_comm]

/-- `I - c 𝓛` is stable for skew `D_k`, for all `c ≥ 0`: the discrete diffusion is dissipative. -/
theorem stable_limL {X : Matrix (Fin Nx) (Fin r) ℝ} {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    {σ : Fin Nx → ℝ} {s : ℝ} (hX : Xᵀ * X = 1) (hs : 0 < s) (hσ : ∀ i, s ≤ σ i)
    (hD : ∀ k, (D k)ᵀ = -D k) {c : ℝ} (hc : 0 ≤ c) : Stable (1 - c • limL X D σ) 1 := by
  intro x
  rw [one_mul]
  have e : limL X D σ =
      ∑ k, (X * AD X D k * Xᵀ) * (X * (Asig X σ)⁻¹ * Xᵀ) * (X * AD X D k * Xᵀ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    calc X * AD X D k * (Asig X σ)⁻¹ * AD X D k * Xᵀ
        = X * AD X D k * (Xᵀ * X) * (Asig X σ)⁻¹ * (Xᵀ * X) * AD X D k * Xᵀ := by
          rw [hX]; simp only [Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  refine stable_of_skew (fun k => ?_) (fun z => ?_) hc x
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, AD_skew hD]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · have h1 := inner_inv_nonneg (Asig_isUnit hs hX hσ) (fun y => by
      have := inner_diagonal_ge (fun i => (hσ i)) (X * y)
      have h2 : ⟪y, Asig X σ * y⟫ = ⟪X * y, Matrix.diagonal σ * (X * y)⟫ := by
        rw [Frobenius.inner_mul_left, Asig]
        simp only [Matrix.mul_assoc]
      rw [h2]
      have h3 : 0 ≤ s * ‖X * y‖ ^ 2 := by positivity
      linarith) (Xᵀ * z)
    have e2 : (X * (Asig X σ)⁻¹ * Xᵀ) * z = X * ((Asig X σ)⁻¹ * (Xᵀ * z)) := by
      simp only [Matrix.mul_assoc]
    rw [e2, Frobenius.inner_mul_left']
    exact h1

/-- `I - c ∑ₖ D_k Σ⁻¹ D_k` is stable for skew `D_k`, for all `c ≥ 0`. -/
theorem stable_limD {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) (hD : ∀ k, (D k)ᵀ = -D k) {c : ℝ} (hc : 0 ≤ c) :
    Stable (1 - c • limD D σ) 1 := by
  intro x
  rw [one_mul]
  refine stable_of_skew hD (fun z => ?_) hc x
  refine inner_inv_nonneg ?_ (fun y => ?_) z
  · rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hσ i).ne'
  · have := inner_diagonal_ge (s := 0) (fun i => (hσ i).le) y
    simpa using this

theorem Stable.mono {T : Matrix (Fin Nx) (Fin Nx) ℝ} {B B' : ℝ} (h : Stable T B) (hB : B ≤ B') :
    Stable T B' := fun x =>
  (h x).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))

/-- A small perturbation of the identity is stable. -/
theorem stable_one_add {T : Matrix (Fin Nx) (Fin Nx) ℝ} (hT : ‖T‖ ≤ 1 / 2) : Stable (1 + T) 2 := by
  intro x
  have e : x = (1 + T) * x - T * x := by rw [Matrix.add_mul, Matrix.one_mul]; abel
  have h1 : ‖x‖ ≤ ‖(1 + T) * x‖ + ‖T * x‖ := by
    calc ‖x‖ = ‖(1 + T) * x - T * x‖ := by rw [← e]
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖T * x‖ ≤ 1 / 2 * ‖x‖ :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  linarith

/-- **Theorem 3.2 of arXiv 1907.04247 for skew `D_k` under the parabolic condition.**  If the
`D_k` are skew (central differences, say) and `Δt ≲ (Δx)²` in the sense that
`Δt r³ √r b² / s ≤ 1 / 2`, where `‖D_k‖ ≤ b` and `s ≤ σ`, the stability hypotheses of `theorem_3_2`
hold with `B = 2`, uniformly in `X`, and the statement holds without them. -/
theorem theorem_3_2_skew (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ r) (hD : ∀ k, (D k)ᵀ = -D k) {b s : ℝ} (hb0 : 0 ≤ b) (hb : ∀ k, ‖D k‖ ≤ b)
    (hs : 0 < s) (hσs : ∀ i, s ≤ σ i)
    (hsmall : Δt * (r ^ 3 * √(r : ℝ) * b ^ 2 / s) ≤ 1 / 2) {BL CA : ℝ} (hBL : 0 ≤ BL) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (L L₁ : Matrix (Fin r) (Fin Nv) ℝ)
        (S₁ S₂ : Matrix (Fin r) (Fin r) ℝ) (V : Matrix (Fin Nv) (Fin r) ℝ)
        (K₃ : Matrix (Fin Nx) (Fin r) ℝ) (ρ₁ ρ₂ ρ₃ : Matrix (Fin Nx) Unit ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → IsIEStep D σ v Δt ε X L L₁ S₁ V S₂ K₃ →
        Assumption1 v hr ε CA V →
        IsIELimit X D σ Δt (density (X * L)) ρ₁ ρ₂ ρ₃ →
        ‖K₃ * Vᵀ - ρ₃ * (eOne Nv)ᵀ‖ ≤ C * ε ∧ ‖density (X * S₂ * Vᵀ) - ρ₂‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hC, hε₀, h⟩ := theorem_3_2 D hσ hv hΔt hr (CA := CA) hBL (B := 2) zero_le_two
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₁ ρ₂ ρ₃ hX hL hst hA hl => ?_⟩
  have hc : 0 ≤ Δt / d := by positivity
  refine h ε hε hεε X L L₁ S₁ S₂ V K₃ ρ₁ ρ₂ ρ₃ hX hL hst hA
    ((stable_limL hX hs hσs hD hc).mono one_le_two) ?_
    ((stable_limD hσ hD hc).mono one_le_two) hl
  refine stable_one_add ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have h1 := norm_limL_le hX hs hσs hb hb0
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0
    simp
  have hd : (0 : ℝ) < d := by exact_mod_cast h0
  calc Δt / d * ‖limL X D σ‖ ≤ Δt / d * (d * (r ^ 3 * √(r : ℝ) * b ^ 2) / s) := by gcongr
    _ = Δt * (r ^ 3 * √(r : ℝ) * b ^ 2 / s) := by field_simp
    _ ≤ _ := hsmall

end Skew

section LemmaB1

variable {Nx Nv r d : ℕ}

/-- The matrix with columns `f i`. -/
def colsOf {n : Type*} (f : Fin d → Matrix n Unit ℝ) : Matrix n (Fin d) ℝ :=
  Matrix.of fun a i => f i a ()

/-- The matrix `(D₁ k, …, D_d k)`. -/
def dirMat (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (k : Matrix (Fin Nx) Unit ℝ) :
    Matrix (Fin Nx) (Fin d) ℝ := colsOf fun i => D i * k

/-- The matrix `𝓗(k)` of (B.4), `𝓗(k)_{ij} = (D_i k)ᵀ (D_j k)`. -/
def Hmat (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (k : Matrix (Fin Nx) Unit ℝ) :
    Matrix (Fin d) (Fin d) ℝ := (dirMat D k)ᵀ * dirMat D k

/-- The matrix with columns `Π_i e_n`. -/
noncomputable def velMat (v : Fin d → Fin Nv → ℝ) : Matrix (Fin Nv) (Fin d) ℝ :=
  colsOf fun i => velPi v i * eNorm Nv

/-- The `j`-th unit vector. -/
def iota (j : Fin d) : Matrix (Fin d) Unit ℝ := Matrix.of fun i _ => if i = j then 1 else 0

section Cols

variable {n : Type*}

theorem colOf_colsOf (f : Fin d → Matrix n Unit ℝ) (i : Fin d) : colOf (colsOf f) i = f i := by
  ext a u
  rfl

theorem mul_colsOf {m : Type*} [Fintype n] (A : Matrix m n ℝ) (f : Fin d → Matrix n Unit ℝ) :
    A * colsOf f = colsOf fun i => A * f i := by
  ext a i
  simp [colsOf, Matrix.mul_apply]

theorem colsOf_mul_iota (f : Fin d → Matrix n Unit ℝ) (j : Fin d) :
    colsOf f * iota j = f j := by
  ext a u
  simp [colsOf, iota, Matrix.mul_apply]

theorem colsOf_add (f g : Fin d → Matrix n Unit ℝ) :
    colsOf (fun i => f i + g i) = colsOf f + colsOf g := by
  ext a i
  simp [colsOf]

theorem colsOf_sub (f g : Fin d → Matrix n Unit ℝ) :
    colsOf (fun i => f i - g i) = colsOf f - colsOf g := by
  ext a i
  simp [colsOf]

theorem colsOf_smul (c : ℝ) (f : Fin d → Matrix n Unit ℝ) :
    colsOf (fun i => c • f i) = c • colsOf f := by
  ext a i
  simp [colsOf]

theorem sum_mul_velMat {m : Type*} (v : Fin d → Fin Nv → ℝ) (g : Fin d → Matrix m Unit ℝ) :
    ∑ k, g k * (eNorm Nv)ᵀ * velPi v k = colsOf g * (velMat v)ᵀ := by
  ext a j
  rw [Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [velPi, Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.transpose_apply, eNorm_apply, colsOf,
    velMat, Matrix.of_apply, velPi_mul_eNorm_apply]
  ring

theorem norm_sq_colsOf [Fintype n] (f : Fin d → Matrix n Unit ℝ) :
    ‖colsOf f‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [norm_sq_eq_sum_colOf]
  simp only [colOf_colsOf]

theorem norm_colsOf_le [Fintype n] {f : Fin d → Matrix n Unit ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i, ‖f i‖ ≤ b) : ‖colsOf f‖ ≤ d * b := by
  have h : ‖colsOf f‖ ^ 2 ≤ (d * b) ^ 2 := by
    rw [norm_sq_colsOf]
    calc ∑ i, ‖f i‖ ^ 2 ≤ ∑ _i : Fin d, b ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2
      _ = d * b ^ 2 := by simp
      _ ≤ (d * b) ^ 2 := by
        have h1 : (d : ℝ) ≤ d ^ 2 := by
          exact_mod_cast Nat.le_self_pow two_ne_zero d
        have h2 : 0 ≤ b ^ 2 := by positivity
        calc (d : ℝ) * b ^ 2 ≤ d ^ 2 * b ^ 2 := by gcongr
          _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

theorem norm_iota (j : Fin d) : ‖iota j‖ = 1 := by
  have h : ‖iota j‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [iota, ite_pow]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

end Cols

section Block

variable {m n₁ n₂ : Type*} [Fintype m] [Fintype n₁] [Fintype n₂]

private theorem norm_sq_fromRows (a : Matrix n₁ m ℝ) (b : Matrix n₂ m ℝ) :
    ‖Matrix.fromRows a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [Frobenius.norm_sq_eq_sum, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr]

private theorem norm_sq_fromCols (a : Matrix m n₁ ℝ) (b : Matrix m n₂ ℝ) :
    ‖Matrix.fromCols a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [← Frobenius.norm_transpose, Matrix.transpose_fromCols, norm_sq_fromRows,
    Frobenius.norm_transpose, Frobenius.norm_transpose]

private theorem norm_fromCols_le (a : Matrix m n₁ ℝ) (b : Matrix m n₂ ℝ) :
    ‖Matrix.fromCols a b‖ ≤ ‖a‖ + ‖b‖ := by
  have h : ‖Matrix.fromCols a b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    rw [norm_sq_fromCols]
    nlinarith [norm_nonneg a, norm_nonneg b]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

end Block

/-- A matrix bounded below has a transpose with a bounded right inverse. -/
private theorem exists_test_vector {n q : Type*} [Fintype n] [Fintype q]
    (c : Matrix n q ℝ) {lam : ℝ} (hlam : 0 < lam) (h : ∀ z : Matrix q Unit ℝ, lam * ‖z‖ ≤ ‖c * z‖)
    (y : Matrix q Unit ℝ) : ∃ b : Matrix n Unit ℝ, cᵀ * b = y ∧ lam * ‖b‖ ≤ ‖y‖ := by
  classical
  have hnorm : ∀ z : Matrix q Unit ℝ, ‖c * z‖ ^ 2 = ⟪z, (cᵀ * c) * z⟫ := fun z => by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, Matrix.mul_assoc]
  have hG : ∀ z : Matrix q Unit ℝ, lam ^ 2 * ‖z‖ ≤ ‖(cᵀ * c) * z‖ := fun z => by
    by_cases hz : ‖z‖ = 0
    · rw [hz, mul_zero]; exact norm_nonneg _
    have hz' : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have h1 := h z
    have h2 := real_inner_le_norm z ((cᵀ * c) * z)
    rw [← hnorm] at h2
    have h3 : (lam * ‖z‖) ^ 2 ≤ ‖c * z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h4 : lam ^ 2 * ‖z‖ * ‖z‖ ≤ ‖(cᵀ * c) * z‖ * ‖z‖ := by nlinarith
    exact le_of_mul_le_mul_right h4 hz'
  have hU := isUnit_det_of_bddBelow (cᵀ * c) (by positivity) hG
  obtain ⟨z, hz⟩ : ∃ z, z = (cᵀ * c)⁻¹ * y := ⟨_, rfl⟩
  have hGz : (cᵀ * c) * z = y := by
    rw [hz, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  refine ⟨c * z, by rw [← Matrix.mul_assoc, hGz], ?_⟩
  by_cases hb : ‖c * z‖ = 0
  · rw [hb, mul_zero]; exact norm_nonneg _
  have hb' : 0 < ‖c * z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
  have h1 := hnorm z
  rw [hGz] at h1
  have h2 := real_inner_le_norm z y
  have h3 := h z
  have h4 : lam * ‖c * z‖ * ‖c * z‖ ≤ ‖y‖ * ‖c * z‖ := by
    calc lam * ‖c * z‖ * ‖c * z‖ = lam * ‖c * z‖ ^ 2 := by ring
      _ ≤ lam * (‖z‖ * ‖y‖) := by rw [h1]; gcongr
      _ = (lam * ‖z‖) * ‖y‖ := by ring
      _ ≤ ‖c * z‖ * ‖y‖ := by gcongr
      _ = _ := mul_comm _ _
  exact le_of_mul_le_mul_right h4 hb'

private theorem skew_inner {D : Matrix (Fin Nx) (Fin Nx) ℝ} (hD : Dᵀ = -D)
    (k : Matrix (Fin Nx) Unit ℝ) : kᵀ * (D * k) = 0 := by
  have h1 : (kᵀ * (D * k))ᵀ = -(kᵀ * (D * k)) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have h2 : (kᵀ * (D * k))ᵀ = kᵀ * (D * k) := by
    ext a b
    rfl
  rw [h2] at h1
  ext a b
  have h3 := congrFun (congrFun h1 a) b
  simp only [Matrix.neg_apply] at h3
  simp only [Matrix.zero_apply]
  linarith

private theorem gram_lower {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} (hD : ∀ k, (D k)ᵀ = -D k)
    (k : Matrix (Fin Nx) Unit ℝ) {a₀ b₀ : ℝ} (ha0 : 0 ≤ a₀) (ha : a₀ ≤ ‖k‖) (hb0 : 0 ≤ b₀)
    (hb : ∀ y : Matrix (Fin d) Unit ℝ, b₀ * ‖y‖ ≤ ‖dirMat D k * y‖)
    (z : Matrix (Unit ⊕ Fin d) Unit ℝ) :
    min a₀ b₀ * ‖z‖ ≤ ‖Matrix.fromCols k (dirMat D k) * z‖ := by
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = z.toRows₁ := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂, z₂ = z.toRows₂ := ⟨_, rfl⟩
  have hz : z = Matrix.fromRows z₁ z₂ := by rw [hz₁, hz₂, Matrix.fromRows_toRows]
  have e : Matrix.fromCols k (dirMat D k) * z = k * z₁ + dirMat D k * z₂ := by
    rw [hz, Matrix.fromCols_mul_fromRows]
  have hn : ‖z‖ ^ 2 = ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 := by rw [hz, norm_sq_fromRows]
  have hkE : kᵀ * dirMat D k = 0 := by
    rw [dirMat, mul_colsOf]
    ext a i
    have := congrFun (congrFun (skew_inner (hD i) k) a) ()
    exact this
  have horth : ⟪k * z₁, dirMat D k * z₂⟫ = 0 := by
    rw [Frobenius.inner_mul_left, ← Matrix.mul_assoc, hkE, Matrix.zero_mul, inner_zero_right]
  have hsum : ‖k * z₁ + dirMat D k * z₂‖ ^ 2 =
      ‖k * z₁‖ ^ 2 + ‖dirMat D k * z₂‖ ^ 2 := by
    rw [norm_add_sq_real, horth]
    ring
  have hk₁ : ‖k * z₁‖ = ‖k‖ * ‖z₁‖ := by
    have e1 : k * z₁ = z₁ () () • k := by
      ext a u
      simp [Matrix.mul_apply, mul_comm]
    have e2 : ‖z₁‖ = |z₁ () ()| := by
      rw [Frobenius.norm_def]
      simp [Real.sqrt_sq_eq_abs]
    rw [e1, norm_smul, e2, Real.norm_eq_abs, mul_comm]
  set lam := min a₀ b₀ with hlam
  have hlam0 : 0 ≤ lam := le_min ha0 hb0
  have h1 : lam * ‖z₁‖ ≤ ‖k * z₁‖ := by
    rw [hk₁]
    exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans ha) (norm_nonneg _)
  have h2 : lam * ‖z₂‖ ≤ ‖dirMat D k * z₂‖ :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans (hb z₂)
  have h3 : (lam * ‖z‖) ^ 2 ≤ ‖k * z₁ + dirMat D k * z₂‖ ^ 2 := by
    rw [hsum, mul_pow, hn]
    have h4 := pow_le_pow_left₀ (by positivity) h1 2
    have h5 := pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow] at h4 h5
    linarith
  rw [e]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h3

private theorem moments_test {n q : Type*} [Fintype n] [Fintype q]
    {π : Fin d → Matrix n n ℝ} {e : Matrix n Unit ℝ} {V : Matrix n q ℝ} {μ C ε : ℝ}
    (hen : ‖e‖ ≤ 1) (hm1 : ∀ k, eᵀ * (π k * e) = 0)
    (hm2 : ∀ j k, eᵀ * (π j * (π k * e)) =
      (if j = k then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ))
    (hμ : ∀ k, ‖π k‖ ≤ μ) (hμ0 : 0 ≤ μ) (hC0 : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc1 : ‖e - V * (Vᵀ * e)‖ ≤ C * ε ^ 2) (hc2 : ∀ k, ‖π k * e - V * (Vᵀ * (π k * e))‖ ≤ C * ε)
    (i j : Fin d) :
    ‖(Vᵀ * e)ᵀ * (Vᵀ * (π j * e))‖ ≤ C * μ * ε ^ 2 ∧
    ‖(Vᵀ * e)ᵀ * ((Vᵀ * π i * V) * (Vᵀ * (π j * e))) -
      (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)‖ ≤
      (μ * C + C * μ * μ + C * μ * C) * ε := by
  generalize hα : Vᵀ * e = α at *
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = e - V * α := ⟨_, rfl⟩
  rw [← hr₀] at hc1
  have ha : V * α = e - r₀ := by rw [hr₀]; abel
  have ht : (V * α)ᵀ = αᵀ * Vᵀ := Matrix.transpose_mul _ _
  have hπj := hμ j
  have hπi := hμ i
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hπe : ‖π j * e‖ ≤ μ * 1 :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hπj hen (norm_nonneg _) hμ0)
  constructor
  · have e1 : αᵀ * (Vᵀ * (π j * e)) = -(r₀ᵀ * (π j * e)) := by
      rw [← Matrix.mul_assoc αᵀ, ← ht, ha, Matrix.transpose_sub, Matrix.sub_mul, hm1, zero_sub]
    rw [e1, norm_neg]
    calc ‖r₀ᵀ * (π j * e)‖ ≤ ‖r₀‖ * ‖π j‖ * ‖e‖ := norm_tmm_le _ _ _
      _ ≤ (C * ε ^ 2) * μ * 1 := by gcongr
      _ = _ := by ring
  · obtain ⟨s, hs⟩ : ∃ s, s = π j * e - V * (Vᵀ * (π j * e)) := ⟨_, rfl⟩
    have hsn : ‖s‖ ≤ C * ε := by rw [hs]; exact hc2 j
    have hP : V * (Vᵀ * (π j * e)) = π j * e - s := by rw [hs]; abel
    have e1 : αᵀ * ((Vᵀ * π i * V) * (Vᵀ * (π j * e))) =
        (V * α)ᵀ * (π i * (V * (Vᵀ * (π j * e)))) := by
      rw [ht]; simp only [Matrix.mul_assoc]
    have e2 : (V * α)ᵀ * (π i * (V * (Vᵀ * (π j * e)))) -
        (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ) =
        - (eᵀ * (π i * s)) - r₀ᵀ * (π i * (π j * e)) + r₀ᵀ * (π i * s) := by
      rw [hP, ha, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.mul_sub, hm2 i j]
      abel
    rw [e1, e2]
    have t1 : ‖eᵀ * (π i * s)‖ ≤ 1 * μ * (C * ε) := by
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have t2 : ‖r₀ᵀ * (π i * (π j * e))‖ ≤ (C * ε ^ 2) * μ * (μ * 1) := by
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have t3 : ‖r₀ᵀ * (π i * s)‖ ≤ (C * ε ^ 2) * μ * (C * ε) := by
      refine (norm_tmm_le _ _ _).trans ?_
      gcongr
    have u2 : (C * ε ^ 2) * μ * (μ * 1) ≤ (C * ε) * μ * (μ * 1) := by gcongr
    have u3 : (C * ε ^ 2) * μ * (C * ε) ≤ (C * ε) * μ * (C * 1) := by gcongr
    calc _ ≤ ‖eᵀ * (π i * s)‖ + ‖r₀ᵀ * (π i * (π j * e))‖ + ‖r₀ᵀ * (π i * s)‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
          rw [norm_neg]
      _ ≤ _ := by nlinarith

private theorem norm_mul3_le' {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (A : Matrix a b ℝ) (B : Matrix b c ℝ) (C : Matrix c e ℝ) :
    ‖A * (B * C)‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  rw [← Matrix.mul_assoc]
  exact norm_mul3_le _ _ _

private theorem diag_one_inv : (Matrix.diagonal fun _ : Fin Nx => (1 : ℝ))⁻¹ = 1 := by
  rw [Matrix.diagonal_one]
  exact inv_one

private theorem Asig_one {X : Matrix (Fin Nx) (Fin r) ℝ} (hX : Xᵀ * X = 1) :
    Asig X (fun _ => 1) = 1 := by
  rw [Asig, Matrix.diagonal_one, Matrix.mul_one, hX]

private theorem kStep_B1 (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (hD : ∀ k, (D k)ᵀ = -D k)
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt) {B₀ CA : ℝ}
    (hB₀ : 0 ≤ B₀) (hCA : 0 ≤ CA) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ),
        Vᵀ * V = 1 → Capture v ε CA V → IsKStep D (fun _ => 1) v Δt ε V Km K → ‖Km‖ ≤ B₀ →
        ‖K‖ ≤ (2 * (√(r : ℝ)) ^ 2 + 1) * B₀ ∧
        ‖K - K * (Vᵀ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ + ε • ∑ i, D i * (K * (Vᵀ * eNorm Nv)) *
          (Vᵀ * eNorm Nv)ᵀ * Xi v V i‖ ≤ C * ε ^ 2 := by
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := stiff_main (m := Fin Nx) (p := Fin r) d hΔt.ne'
    (∑ i, ‖D i‖) ‖(Matrix.diagonal fun _ : Fin Nx => (1 : ℝ))⁻¹‖
    ‖Matrix.diagonal fun _ : Fin Nx => (1 : ℝ)‖ (r * ∑ i, ‖velPi v i‖) (√(r : ℝ))
    (momC r (∑ i, ‖velPi v i‖) CA) 1 zero_le_one
  refine ⟨C₃ * B₀, ε₃, by positivity, hε₃, hε₃1, ?_⟩
  intro ε hε hεε V Km K hV hc hK hB
  have hε1 : ε ≤ 1 := (hεε.trans_le hε₃1).le
  have hH := stiffHyp_K (D := D) hv (σ := fun _ => 1) (fun _ => one_pos) hV hCA hε.le hε1 hc
  have hst : ∀ x : Matrix (Fin Nx) Unit ℝ,
      ‖x‖ ≤ 1 * ‖limitOp D (Matrix.diagonal fun _ : Fin Nx => (1 : ℝ))⁻¹ Δt * x‖ :=
    fun x => stable_limD (σ := fun _ => 1) (fun _ => one_pos) hD (c := Δt / d) (by positivity) x
  obtain ⟨b1, -, -, b4⟩ := h3 ε hε hεε _ _ _ _ _ _ _ hH hst (hK.stiff hΔt.ne' hV)
  rw [diag_one_inv] at b4
  simp only [Matrix.one_mul, mul_one] at b4 b1
  refine ⟨b1.trans (by gcongr), b4.trans ?_⟩
  have h2 : 0 ≤ ε ^ 2 := by positivity
  calc C₃ * ε ^ 2 * ‖Km‖ ≤ C₃ * ε ^ 2 * B₀ := by gcongr
    _ = _ := by ring

/-- The columns of `K`: from the expansion of `K`, testing with `Vᵀ Π_j e_n` isolates `D_j k`. -/
private theorem K_test {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {v : Fin d → Fin Nv → ℝ}
    (hv : IsQuadrature v) {V : Matrix (Fin Nv) (Fin r) ℝ} {K : Matrix (Fin Nx) (Fin r) ℝ}
    {ε CA C M Dm : ℝ} (hV : Vᵀ * V = 1) (hCA : 0 ≤ CA) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : Capture v ε CA V) (hM : ‖K * (Vᵀ * eNorm Nv)‖ ≤ M) (hDm : ∀ i, ‖D i‖ ≤ Dm)
    (hDm0 : 0 ≤ Dm)
    (hE : ‖K - K * (Vᵀ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ + ε • ∑ i, D i * (K * (Vᵀ * eNorm Nv)) *
      (Vᵀ * eNorm Nv)ᵀ * Xi v V i‖ ≤ C * ε ^ 2) (j : Fin d) :
    ‖K * (Vᵀ * (velPi v j * eNorm Nv)) + (ε * (d : ℝ)⁻¹) • (D j * (K * (Vᵀ * eNorm Nv)))‖ ≤
      (C * (∑ i, ‖velPi v i‖) + M * (CA * (∑ i, ‖velPi v i‖)) +
        d * (Dm * M * ((∑ i, ‖velPi v i‖) * CA + CA * (∑ i, ‖velPi v i‖) * (∑ i, ‖velPi v i‖) +
          CA * (∑ i, ‖velPi v i‖) * CA))) * ε ^ 2 := by
  set μ := ∑ i, ‖velPi v i‖ with hμ
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hπ : ∀ k, ‖velPi v k‖ ≤ μ := fun k =>
    Finset.single_le_sum (f := fun i => ‖velPi v i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have hm := fun i => moments_test (π := velPi v) (e := eNorm Nv) (V := V) (μ := μ) (C := CA)
    (ε := ε) (norm_eNorm hv.pos).le (eNorm_moment1 hv) (eNorm_moment2 hv) hπ hμ0 hCA hε hε1 hc.e
    hc.vel i j
  obtain ⟨α, hα⟩ : ∃ α, α = Vᵀ * eNorm Nv := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, c = Vᵀ * (velPi v j * eNorm Nv) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = K * α := ⟨_, rfl⟩
  rw [← hα, ← hc'] at hm
  rw [← hα, ← hk] at hE hM
  rw [← hα, ← hc', ← hk]
  obtain ⟨Er, hEr⟩ : ∃ Er, Er = K - k * αᵀ + ε • ∑ i, D i * k * αᵀ * Xi v V i := ⟨_, rfl⟩
  rw [← hEr] at hE
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hcn : ‖c‖ ≤ μ := by
    rw [hc']
    refine (norm_transpose_mul_le hV _).trans ?_
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [norm_eNorm hv.pos, mul_one]
    exact hπ j
  have e1 : ∀ i, D i * k * αᵀ * Xi v V i * c = D i * k * (αᵀ * (Xi v V i * c)) := fun i => by
    simp only [Matrix.mul_assoc]
  have e2 : K = Er + k * αᵀ - ε • ∑ i, D i * k * αᵀ * Xi v V i := by rw [hEr]; abel
  have e3 : ∑ i, D i * k * (αᵀ * (Xi v V i * c)) =
      (d : ℝ)⁻¹ • (D j * k) + ∑ i, D i * k * (αᵀ * (Xi v V i * c) -
        (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) := by
    have e4 : ∀ i, D i * k * (αᵀ * (Xi v V i * c)) =
        (if i = j then ((d : ℝ)⁻¹) else 0) • (D i * k) + D i * k * (αᵀ * (Xi v V i * c) -
          (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) := fun i => by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      abel
    rw [Finset.sum_congr rfl fun i _ => e4 i, Finset.sum_add_distrib]
    congr 1
    simp [ite_smul]
  have e5 : K * c + (ε * (d : ℝ)⁻¹) • (D j * k) = Er * c + k * (αᵀ * c) -
      ε • ∑ i, D i * k * (αᵀ * (Xi v V i * c) -
        (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ)) := by
    have e6 : K * c = Er * c + k * (αᵀ * c) - ε • ∑ i, D i * k * (αᵀ * (Xi v V i * c)) := by
      conv_lhs => rw [e2]
      rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul, Matrix.mul_assoc k]
      simp only [e1]
    rw [e6, e3, smul_add, smul_smul]
    abel
  rw [e5]
  have t1 : ‖Er * c‖ ≤ (C * ε ^ 2) * μ :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hE hcn (norm_nonneg _)
      ((norm_nonneg _).trans hE))
  have t2 : ‖k * (αᵀ * c)‖ ≤ M * (CA * μ * ε ^ 2) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hM (hm j).1 (norm_nonneg _) hM0)
  have t3 : ‖ε • ∑ i, D i * k * (αᵀ * (Xi v V i * c) -
      (if i = j then ((d : ℝ)⁻¹) else 0) • (1 : Matrix Unit Unit ℝ))‖ ≤
      ε * (d * (Dm * M * ((μ * CA + CA * μ * μ + CA * μ * CA) * ε))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    refine mul_le_mul_of_nonneg_left (norm_sum_fin_le fun i => ?_) hε
    refine (norm_mul3_le _ _ _).trans ?_
    have := hDm i
    have := (hm i).2
    rw [← Xi] at this
    gcongr
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3).trans
    (le_of_eq (by ring)))

/-- `k` and the `D_j k` lie in the range of `X` (the second up to `O(ε)`). -/
private theorem perp_D_le {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    (hX : Xᵀ * X = 1) (hd : 0 < d) {K : Matrix (Fin Nx) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    (hKS : K = X * S) {k : Matrix (Fin Nx) Unit ℝ} {c : Matrix (Fin r) Unit ℝ} {ε C : ℝ}
    (hε : 0 < ε) {j : Fin d} (h : ‖K * c + (ε * (d : ℝ)⁻¹) • (D j * k)‖ ≤ C * ε ^ 2) :
    ‖perp X (D j * k)‖ ≤ d * C * ε := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : perp X (K * c + (ε * (d : ℝ)⁻¹) • (D j * k)) = (ε * (d : ℝ)⁻¹) • perp X (D j * k) := by
    rw [perp_add, perp_smul, hKS, Matrix.mul_assoc, perp_mul hX, zero_add]
  have h1 : ‖(ε * (d : ℝ)⁻¹) • perp X (D j * k)‖ ≤ C * ε ^ 2 := by
    rw [← e]
    exact (norm_perp_le hX _).trans h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have h2 : ‖perp X (D j * k)‖ = d * ε⁻¹ * ((ε * (d : ℝ)⁻¹) * ‖perp X (D j * k)‖) := by
    field_simp
  rw [h2]
  calc d * ε⁻¹ * ((ε * (d : ℝ)⁻¹) * ‖perp X (D j * k)‖) ≤ d * ε⁻¹ * (C * ε ^ 2) := by gcongr
    _ = _ := by field_simp

/-- If the row space of `L₊` is what the expansion says and the vectors involved are independent,
then the new basis captures `e_n` and `Π_k e_n`. -/
private theorem capture_of_structure {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {X : Matrix (Fin Nx) (Fin r) ℝ}
    (hX : Xᵀ * X = 1) {k : Matrix (Fin Nx) Unit ℝ} {ζ : Matrix (Fin r) Unit ℝ}
    {Vp : Matrix (Fin Nv) (Fin r) ℝ} {Sp : Matrix (Fin r) (Fin r) ℝ}
    {Lp : Matrix (Fin r) (Fin Nv) ℝ} {lam₀ ϖ ϑ g C₆ ε : ℝ} (hlam : 0 < lam₀)
    (hlow : ∀ z : Matrix (Unit ⊕ Fin d) Unit ℝ, lam₀ * ‖z‖ ≤ ‖Matrix.fromCols k (dirMat D k) * z‖)
    (hXk : X * (Xᵀ * k) = k) (hperp : ∀ j, ‖perp X (D j * k)‖ ≤ ϖ)
    (hg : ∀ i, ‖AD X D i‖ ≤ g) (hg0 : 0 ≤ g) (hϖ : 0 ≤ ϖ) (hζ : ‖ζ‖ ≤ ϑ)
    (hsmall : (1 + d * g) * ϑ + d * ϖ ≤ lam₀ / 2)
    (hS : ‖Lp - ((Xᵀ * k + ζ) * (eNorm Nv)ᵀ -
      ε • (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) * (velMat v)ᵀ)‖ ≤ C₆ * ε ^ 2)
    (hqr : Lp = Sp * Vpᵀ) (hVp : Vpᵀ * Vp = 1) (hε : 0 < ε) : Capture v ε (2 * C₆ / lam₀) Vp := by
  have hNv := hv.pos
  have hϑ : 0 ≤ ϑ := (norm_nonneg _).trans hζ
  have hC₆ : 0 ≤ C₆ := by
    have h1 := (norm_nonneg _).trans hS
    by_contra hneg
    have h2 := not_le.mp hneg
    have h3 : 0 < ε ^ 2 := by positivity
    nlinarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = Xᵀ * k + ζ := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Matrix.fromCols c₀ c' := ⟨_, rfl⟩
  obtain ⟨Zm, hZm⟩ : ∃ Zm, Zm = Matrix.fromCols ζ (colsOf fun i => AD X D i * ζ) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = Matrix.fromCols (0 : Matrix (Fin Nx) Unit ℝ)
      (colsOf fun i => perp X (D i * k)) := ⟨_, rfl⟩
  have hZn : ‖Zm‖ ≤ (1 + d * g) * ϑ := by
    rw [hZm]
    refine (norm_fromCols_le _ _).trans ?_
    have h1 : ‖colsOf fun i => AD X D i * ζ‖ ≤ d * (g * ϑ) := by
      refine norm_colsOf_le (by positivity) fun i => ?_
      exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hg i) hζ (norm_nonneg _) hg0)
    nlinarith
  have hWn : ‖W‖ ≤ d * ϖ := by
    rw [hW]
    refine (norm_fromCols_le _ _).trans ?_
    rw [norm_zero, zero_add]
    exact norm_colsOf_le hϖ hperp
  have heq : Matrix.fromCols k (dirMat D k) = X * c + W - X * Zm := by
    have e1 : X * c = Matrix.fromCols (X * c₀) (X * c') := by
      rw [hc, Matrix.mul_fromCols]
    have e2 : X * Zm = Matrix.fromCols (X * ζ) (X * colsOf fun i => AD X D i * ζ) := by
      rw [hZm, Matrix.mul_fromCols]
    have e3 : k = X * c₀ + 0 - X * ζ := by
      rw [hc₀, Matrix.mul_add, hXk]
      abel
    have e4 : dirMat D k = X * c' + (colsOf fun i => perp X (D i * k)) -
        X * colsOf fun i => AD X D i * ζ := by
      rw [hc', mul_colsOf, mul_colsOf, dirMat, ← colsOf_add, ← colsOf_sub]
      congr 1
      ext1 i
      rw [perp, Matrix.mul_add]
      abel
    rw [e1, e2, hW]
    ext a j
    rcases j with u | i
    · simpa using congrFun (congrFun e3 a) u
    · simpa using congrFun (congrFun e4 a) i
  have hlowc : ∀ z : Matrix (Unit ⊕ Fin d) Unit ℝ, (lam₀ / 2) * ‖z‖ ≤ ‖c * z‖ := fun z => by
    have h1 := hlow z
    have e1 : Matrix.fromCols k (dirMat D k) * z = X * (c * z) + W * z - X * (Zm * z) := by
      rw [heq, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [e1] at h1
    have h2 : ‖X * (c * z) + W * z - X * (Zm * z)‖ ≤
        ‖c * z‖ + d * ϖ * ‖z‖ + (1 + d * g) * ϑ * ‖z‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · exact (Frobenius.norm_mul_of_orthonormal hX _).le
      · exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hWn (norm_nonneg _))
      · rw [Frobenius.norm_mul_of_orthonormal hX]
        exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hZn (norm_nonneg _))
    have h3 := norm_nonneg z
    nlinarith
  have hkey : ∀ (y₁ : Matrix Unit Unit ℝ) (y₂ : Matrix (Fin d) Unit ℝ),
      ∃ (b : Matrix (Fin r) Unit ℝ), (lam₀ / 2) * ‖b‖ ≤ ‖Matrix.fromRows y₁ y₂‖ ∧
        perp Vp (eNorm Nv * y₁ - ε • (velMat v * y₂)) =
          -perp Vp ((Lp - ((Xᵀ * k + ζ) * (eNorm Nv)ᵀ -
            ε • (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) * (velMat v)ᵀ))ᵀ * b) := by
    intro y₁ y₂
    obtain ⟨b, hb, hbn⟩ := exists_test_vector c (by positivity) hlowc (Matrix.fromRows y₁ y₂)
    refine ⟨b, hbn, ?_⟩
    rw [hc, Matrix.transpose_fromCols, Matrix.fromRows_mul] at hb
    obtain ⟨hb₁, hb₂⟩ := Matrix.fromRows_inj hb
    rw [← hc₀, ← hc']
    have e1 : Lpᵀ * b = Vp * (Spᵀ * b) := by
      rw [hqr, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    have e2 : (Lp - (c₀ * (eNorm Nv)ᵀ - ε • c' * (velMat v)ᵀ))ᵀ * b =
        Lpᵀ * b - (eNorm Nv * y₁ - ε • (velMat v * y₂)) := by
      rw [← hb₁, ← hb₂]
      simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_smul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.smul_mul]
    rw [e2, perp_sub Vp (Lpᵀ * b), e1, perp_mul hVp, zero_sub, neg_neg]
  have hb_err : ∀ b : Matrix (Fin r) Unit ℝ, (lam₀ / 2) * ‖b‖ ≤ 1 →
      ‖perp Vp ((Lp - ((Xᵀ * k + ζ) * (eNorm Nv)ᵀ -
        ε • (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) * (velMat v)ᵀ))ᵀ * b)‖ ≤
        2 * C₆ / lam₀ * ε ^ 2 := fun b hb => by
    refine (norm_perp_le hVp _).trans ?_
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    have h1 : ‖b‖ ≤ 2 / lam₀ := by
      rw [le_div_iff₀ hlam]
      linarith
    calc _ ≤ (C₆ * ε ^ 2) * (2 / lam₀) := mul_le_mul hS h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  constructor
  · obtain ⟨b, hbn, he⟩ := hkey 1 0
    have hn : ‖Matrix.fromRows (1 : Matrix Unit Unit ℝ) (0 : Matrix (Fin d) Unit ℝ)‖ = 1 := by
      have h1 := norm_sq_fromRows (1 : Matrix Unit Unit ℝ) (0 : Matrix (Fin d) Unit ℝ)
      have h2 : ‖(1 : Matrix Unit Unit ℝ)‖ = 1 := by
        have := norm_sq_of_orthonormal (V := (1 : Matrix Unit Unit ℝ)) (by simp)
        simp only [Fintype.card_unit, Nat.cast_one] at this
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
      rw [h2, norm_zero] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [h1]; norm_num)
    rw [hn] at hbn
    have e : eNorm Nv * (1 : Matrix Unit Unit ℝ) - ε • (velMat v * (0 : Matrix (Fin d) Unit ℝ)) =
        eNorm Nv := by simp
    rw [e] at he
    change ‖perp Vp (eNorm Nv)‖ ≤ _
    rw [he, norm_neg]
    exact hb_err b hbn
  · intro j
    obtain ⟨b, hbn, he⟩ := hkey 0 (iota j)
    have hn : ‖Matrix.fromRows (0 : Matrix Unit Unit ℝ) (iota j)‖ = 1 := by
      have h1 := norm_sq_fromRows (0 : Matrix Unit Unit ℝ) (iota j)
      rw [norm_iota, norm_zero] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [h1]; norm_num)
    rw [hn] at hbn
    have e : eNorm Nv * (0 : Matrix Unit Unit ℝ) - ε • (velMat v * iota j) =
        -(ε • (velPi v j * eNorm Nv)) := by
      rw [velMat, colsOf_mul_iota]
      simp
    rw [e, perp_smul_neg] at he
    change ‖perp Vp (velPi v j * eNorm Nv)‖ ≤ _
    have h1 := hb_err b hbn
    rw [← neg_injective he, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h1
    have h2 : ε * ‖perp Vp (velPi v j * eNorm Nv)‖ ≤ ε * (2 * C₆ / lam₀ * ε) := by
      calc _ ≤ 2 * C₆ / lam₀ * ε ^ 2 := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 hε

private theorem lStep_B1 (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) (hD : ∀ k, (D k)ᵀ = -D k)
    {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (Y F : Matrix (Fin r) (Fin Nv) ℝ), Xᵀ * X = 1 →
        IsStiffSolution (AD X D) (Asig X fun _ => 1) (velPi v) (eNorm Nv) τ ε Y F →
        ‖Y * eNorm Nv - F * eNorm Nv‖ ≤
          τ * (((r : ℝ) * ∑ i, ‖D i‖) * ((r : ℝ) * ∑ i, ‖D i‖)) *
            (‖F * eNorm Nv‖ + C * ε * ‖F‖) + C * ε * ‖F‖ ∧
        ‖Y - ((Y * eNorm Nv) * (eNorm Nv)ᵀ -
          ε • (colsOf fun i => AD X D i * (Y * eNorm Nv)) * (velMat v)ᵀ)‖ ≤ C * ε ^ 2 * ‖F‖ := by
  obtain ⟨g, hg⟩ : ∃ g, g = (r : ℝ) * ∑ i, ‖D i‖ := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  obtain ⟨C, ε₀, hC, hε₀, hε₀1, h⟩ := stiff_main (m := Fin r) (p := Fin Nv) d hτ.ne'
    ((r : ℝ) * ∑ i, ‖D i‖) (√(r : ℝ) / 1) ((r : ℝ) * ‖Matrix.diagonal fun _ : Fin Nx => (1 : ℝ)‖)
    (∑ i, ‖velPi v i‖) 1 0 1 zero_le_one
  rw [← hg] at h ⊢
  refine ⟨C, ε₀, hC, hε₀, hε₀1, ?_⟩
  intro ε hε hεε X Y F hX hs
  have hH := stiffHyp_L (D := D) (σ := fun _ => 1) (s := 1) (ε := ε) hv one_pos (fun _ => le_rfl) hX
  rw [← hg] at hH
  have hst := fun x => stable_lift (D := D) (σ := fun _ => 1) (τ := τ) (B := 1) hX
    (stable_limL (D := D) (σ := fun _ => 1) (s := 1) hX one_pos (fun _ => le_rfl) hD
      (c := τ / d) (by positivity)) x
  obtain ⟨-, -, a3, a4⟩ := h ε hε hεε _ _ _ _ _ _ _ hH hst hs
  have hinv : (Asig X fun _ => 1)⁻¹ = 1 := by
    rw [Asig_one hX]
    exact inv_one
  rw [hinv] at a3 a4 hst
  simp only [Matrix.one_mul] at a4
  rw [sum_mul_velMat v (fun i => AD X D i * (Y * eNorm Nv))] at a4
  obtain ⟨m, hm⟩ : ∃ m, m = Y * eNorm Nv := ⟨_, rfl⟩
  rw [← hm] at a3 a4 ⊢
  constructor
  · obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin r) (Fin r) ℝ, T = limitOp (AD X D) 1 τ := ⟨_, rfl⟩
    rw [← hT] at a3
    have hTm : ‖m‖ ≤ ‖F * eNorm Nv‖ + C * ε * ‖F‖ := by
      have h1 := hst m
      rw [one_mul, ← hT] at h1
      have h2 := norm_sub_norm_le (T * m) (F * eNorm Nv)
      linarith
    have e2 : m - F * eNorm Nv = (T * m - F * eNorm Nv) +
        (τ / d) • ((∑ k, AD X D k * 1 * AD X D k) * m) := by
      rw [hT, limitOp, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
      abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    have e3 : ‖(τ / d) • ((∑ k, AD X D k * 1 * AD X D k) * m)‖ ≤ τ * (g * g) * ‖m‖ := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp only [Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_mul, smul_zero, norm_zero]
        positivity
      have hd : (0 : ℝ) < d := by exact_mod_cast h0
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h1 : ‖(∑ k, AD X D k * 1 * AD X D k) * m‖ ≤ d * (g * g) * ‖m‖ := by
        refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        refine norm_sum_fin_le fun k => ?_
        rw [Matrix.mul_one]
        have h2 := norm_AD_le (D := D) hX k
        rw [← hg] at h2
        exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul h2 h2 (norm_nonneg _) hg0)
      calc τ / d * ‖(∑ k, AD X D k * 1 * AD X D k) * m‖ ≤ τ / d * (d * (g * g) * ‖m‖) := by gcongr
        _ = _ := by field_simp
    have e4 : τ * (g * g) * ‖m‖ ≤ τ * (g * g) * (‖F * eNorm Nv‖ + C * ε * ‖F‖) := by gcongr
    linarith
  · have e2 : Y - (m * (eNorm Nv)ᵀ - ε • (colsOf fun i => AD X D i * m) * (velMat v)ᵀ) =
        Y - m * (eNorm Nv)ᵀ + ε • ((colsOf fun i => AD X D i * m) * (velMat v)ᵀ) := by
      rw [Matrix.smul_mul]
      abel
    rw [e2]
    exact a4

/-- The Gram matrix of `k, D₁ k, …, D_d k` is `diag(‖k‖², 𝓗(k))` for skew `D_i`, so a bound on
`𝓗(k)⁻¹` is a lower bound for the matrix `(k, D₁ k, …, D_d k)`. -/
private theorem gram_bound (hd : 0 < d) {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ}
    (hD : ∀ k, (D k)ᵀ = -D k) {k : Matrix (Fin Nx) Unit ℝ} {M BH' : ℝ} (hBH'0 : 0 < BH')
    (hM0 : 0 ≤ M) (hkn : ‖k‖ ≤ M) (hdet : (Hmat D k).det ≠ 0) (hBH : ‖(Hmat D k)⁻¹‖ ≤ BH')
    (z : Matrix (Unit ⊕ Fin d) Unit ℝ) :
    min (√(1 / (BH' * (∑ i, ‖D i‖ ^ 2 + 1))))
      (1 / (BH' * (√(∑ i, ‖D i‖ ^ 2 + 1) * M + 1))) * ‖z‖ ≤
      ‖Matrix.fromCols k (dirMat D k) * z‖ := by
  obtain ⟨D₂, hD₂⟩ : ∃ D₂, D₂ = ∑ i, ‖D i‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hD₂0 : 0 < D₂ := by rw [hD₂]; positivity
  rw [← hD₂]
  obtain ⟨E', hE'def⟩ : ∃ E', E' = dirMat D k := ⟨_, rfl⟩
  have hH : Hmat D k = E'ᵀ * E' := by rw [hE'def, Hmat]
  have hU : IsUnit (Hmat D k).det := isUnit_iff_ne_zero.mpr hdet
  have hinv : (Hmat D k)⁻¹ * Hmat D k = 1 := Matrix.nonsing_inv_mul _ hU
  have hEn2 : ‖E'‖ ^ 2 ≤ D₂ * ‖k‖ ^ 2 := by
    rw [hE'def, dirMat, norm_sq_colsOf, hD₂, add_mul, one_mul, Finset.sum_mul]
    have h1 : ∑ i, ‖D i * k‖ ^ 2 ≤ ∑ i, ‖D i‖ ^ 2 * ‖k‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (Frobenius.norm_mul_le _ _) 2
    have h2 := sq_nonneg ‖k‖
    linarith
  have hEn : ‖E'‖ ≤ √D₂ * M := by
    have h1 : ‖E'‖ ≤ √(D₂ * ‖k‖ ^ 2) := Real.le_sqrt_of_sq_le hEn2
    rw [Real.sqrt_mul hD₂0.le, Real.sqrt_sq (norm_nonneg _)] at h1
    exact h1.trans (by gcongr)
  have hak : √(1 / (BH' * D₂)) ≤ ‖k‖ := by
    have hd1 : (1 : ℝ) ≤ √(d : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hd
    have h1 : √(d : ℝ) ≤ BH' * (D₂ * ‖k‖ ^ 2) := by
      rw [← norm_one_fin, ← hinv]
      refine (Frobenius.norm_mul_le _ _).trans ?_
      have h2 : ‖Hmat D k‖ ≤ ‖E'‖ ^ 2 := by
        rw [hH, sq]
        refine (Frobenius.norm_mul_le _ _).trans ?_
        rw [Frobenius.norm_transpose]
      exact mul_le_mul hBH (h2.trans hEn2) (norm_nonneg _) hBH'0.le
    have h3 : 1 / (BH' * D₂) ≤ ‖k‖ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, h3⟩
  have hby : ∀ y : Matrix (Fin d) Unit ℝ, 1 / (BH' * (√D₂ * M + 1)) * ‖y‖ ≤ ‖E' * y‖ := fun y => by
    have h1 : ‖y‖ ≤ BH' * (√D₂ * M + 1) * ‖E' * y‖ := by
      have e : y = (Hmat D k)⁻¹ * (E'ᵀ * (E' * y)) := by
        rw [← Matrix.mul_assoc E'ᵀ, ← hH, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      calc ‖y‖ = ‖(Hmat D k)⁻¹ * (E'ᵀ * (E' * y))‖ := by rw [← e]
        _ ≤ ‖(Hmat D k)⁻¹‖ * ‖E'ᵀ‖ * ‖E' * y‖ := norm_mul3_le' _ _ _
        _ ≤ BH' * (√D₂ * M + 1) * ‖E' * y‖ := by
          rw [Frobenius.norm_transpose]
          have : ‖E'‖ ≤ √D₂ * M + 1 := by linarith
          gcongr
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    exact h1
  rw [hE'def] at hby
  exact gram_lower hD k (by positivity) hak (by positivity) hby z

/-- The expansion `Lⁿ = Sⁿ (Vⁿ)ᵀ = Xᵀ k e_nᵀ - ε ∑ᵢ Xᵀ D_i k e_nᵀ Π_i + O(ε²)`. -/
private theorem L_expansion {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {v : Fin d → Fin Nv → ℝ}
    (hv : IsQuadrature v) {X : Matrix (Fin Nx) (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} {K : Matrix (Fin Nx) (Fin r) ℝ} {ε CA C₃ M Dm : ℝ}
    (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1) (hKS : K = X * S) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hCA : 0 ≤ CA) (hc : Capture v ε CA V) (hM : ‖K * (Vᵀ * eNorm Nv)‖ ≤ M)
    (hDm : ∀ i, ‖D i‖ ≤ Dm) (hDm0 : 0 ≤ Dm)
    (hE : ‖K - K * (Vᵀ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ + ε • ∑ i, D i * (K * (Vᵀ * eNorm Nv)) *
      (Vᵀ * eNorm Nv)ᵀ * Xi v V i‖ ≤ C₃ * ε ^ 2) :
    ‖S * Vᵀ - ((Xᵀ * (K * (Vᵀ * eNorm Nv))) * (eNorm Nv)ᵀ -
      ε • (colsOf fun i => Xᵀ * (D i * (K * (Vᵀ * eNorm Nv)))) * (velMat v)ᵀ)‖ ≤
      (C₃ + M * CA + d * (Dm * M * (CA + CA * (∑ i, ‖velPi v i‖) * r))) * ε ^ 2 := by
  have hNv := hv.pos
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ i, ‖velPi v i‖ := ⟨_, rfl⟩
  rw [← hμ]
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hπ : ∀ i, ‖velPi v i‖ ≤ μ := fun i => by
    rw [hμ]
    exact Finset.single_le_sum (f := fun i => ‖velPi v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hPn : ‖V * Vᵀ‖ ≤ (r : ℝ) := by
    have h := norm_of_orthonormal hV
    simp only [Fintype.card_fin] at h
    refine (Frobenius.norm_mul_le _ _).trans (le_of_eq ?_)
    rw [Frobenius.norm_transpose, h, Real.mul_self_sqrt hr0]
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  obtain ⟨α, hα⟩ : ∃ α, α = Vᵀ * eNorm Nv := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = K * α := ⟨_, rfl⟩
  rw [← hα, ← hk] at hE hM ⊢
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨Er, hEr⟩ : ∃ Er, Er = K - k * αᵀ + ε • ∑ i, D i * k * αᵀ * Xi v V i := ⟨_, rfl⟩
  rw [← hEr] at hE
  obtain ⟨g, hg⟩ : ∃ g : Fin d → Matrix (Fin r) Unit ℝ, g = fun i => Xᵀ * (D i * k) := ⟨_, rfl⟩
  have hS : S = Xᵀ * K := by rw [hKS, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = eNorm Nv - V * α := ⟨_, rfl⟩
  have hr₀n : ‖r₀‖ ≤ CA * ε ^ 2 := by rw [hr₀, hα]; exact hc.e
  have h1 : αᵀ * Vᵀ = (eNorm Nv)ᵀ - r₀ᵀ := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_sub, hr₀]
    congr 1
    abel
  have hsym : ∀ i, (velPi v i)ᵀ = velPi v i := fun i => by rw [velPi, Matrix.diagonal_transpose]
  have h2 : ∀ i, αᵀ * Xi v V i * Vᵀ - (eNorm Nv)ᵀ * velPi v i =
      -(velPi v i * eNorm Nv - V * (Vᵀ * (velPi v i * eNorm Nv)))ᵀ -
        r₀ᵀ * (velPi v i * (V * Vᵀ)) := fun i => by
    have e1 : αᵀ * Xi v V i * Vᵀ = (αᵀ * Vᵀ) * (velPi v i * (V * Vᵀ)) := by
      rw [Xi]; simp only [Matrix.mul_assoc]
    have e2 : (eNorm Nv)ᵀ * (velPi v i * (V * Vᵀ)) =
        (V * (Vᵀ * (velPi v i * eNorm Nv)))ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
    have e3 : (velPi v i * eNorm Nv)ᵀ = (eNorm Nv)ᵀ * velPi v i := by
      rw [Matrix.transpose_mul, hsym]
    rw [e1, h1, Matrix.sub_mul, e2, Matrix.transpose_sub, e3]
    abel
  have h3 : ∀ i, ‖αᵀ * Xi v V i * Vᵀ - (eNorm Nv)ᵀ * velPi v i‖ ≤ (CA + CA * μ * r) * ε :=
      fun i => by
    rw [h2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, Frobenius.norm_transpose]
    have t1 := hc.vel i
    have t2 : ‖r₀ᵀ * (velPi v i * (V * Vᵀ))‖ ≤ (CA * ε ^ 2) * μ * r := by
      refine (norm_tmm_le _ _ _).trans ?_
      have := hπ i
      gcongr
    have t3 : (CA * ε ^ 2) * μ * r ≤ (CA * ε) * μ * r := by gcongr
    nlinarith
  have hkey : S * Vᵀ - ((Xᵀ * k) * (eNorm Nv)ᵀ - ε • (colsOf g) * (velMat v)ᵀ) =
      Xᵀ * Er * Vᵀ - (Xᵀ * k) * r₀ᵀ -
        ε • ∑ i, g i * (αᵀ * Xi v V i * Vᵀ - (eNorm Nv)ᵀ * velPi v i) := by
    have e1 : K = Er + k * αᵀ - ε • ∑ i, D i * k * αᵀ * Xi v V i := by rw [hEr]; abel
    have e2 : Xᵀ * K * Vᵀ = Xᵀ * Er * Vᵀ + (Xᵀ * k) * (αᵀ * Vᵀ) -
        ε • ∑ i, g i * (αᵀ * Xi v V i * Vᵀ) := by
      conv_lhs => rw [e1]
      rw [hg]
      simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    have e3 : ∑ i, g i * (αᵀ * Xi v V i * Vᵀ - (eNorm Nv)ᵀ * velPi v i) =
        ∑ i, g i * (αᵀ * Xi v V i * Vᵀ) - colsOf g * (velMat v)ᵀ := by
      rw [← sum_mul_velMat, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_sub, Matrix.mul_assoc (g i) (eNorm Nv)ᵀ]
    rw [hS, e2, h1, e3, Matrix.smul_mul, Matrix.mul_sub, smul_sub]
    abel
  rw [← show g = fun i => Xᵀ * (D i * k) from hg, hkey]
  have t1 : ‖Xᵀ * Er * Vᵀ‖ ≤ C₃ * ε ^ 2 := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV]
    exact (norm_transpose_mul_le hX _).trans hE
  have t2 : ‖(Xᵀ * k) * r₀ᵀ‖ ≤ M * (CA * ε ^ 2) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    exact mul_le_mul ((norm_transpose_mul_le hX _).trans hM) hr₀n (norm_nonneg _) hM0
  have t3 : ‖ε • ∑ i, g i * (αᵀ * Xi v V i * Vᵀ - (eNorm Nv)ᵀ * velPi v i)‖ ≤
      ε * (d * (Dm * M * ((CA + CA * μ * r) * ε))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    refine mul_le_mul_of_nonneg_left (norm_sum_fin_le fun i => ?_) hε
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul ?_ (h3 i) (norm_nonneg _) (by positivity))
    rw [hg]
    refine (norm_transpose_mul_le hX _).trans ?_
    exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hDm i) hM (norm_nonneg _) hDm0)
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3).trans
    (le_of_eq (by ring)))

/-- What the `K`-step of the previous time step leaves behind, in the setting of Lemma B.1. -/
private theorem kSide (hd : 0 < d) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (hD : ∀ k, (D k)ᵀ = -D k) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {B₀ CA BH : ℝ}
    (hB₀ : 0 ≤ B₀) (hCA : 0 ≤ CA) :
    ∃ M lam₀ : ℝ, 0 ≤ M ∧ 0 < lam₀ ∧ ∀ Δt, 0 < Δt → ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Capture v ε CA V → IsKStep D (fun _ => 1) v Δt ε V Km K →
        ‖Km‖ ≤ B₀ → K = X * S → (Hmat D (K * (Vᵀ * eNorm Nv))).det ≠ 0 →
        ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH →
        X * (Xᵀ * (K * (Vᵀ * eNorm Nv))) = K * (Vᵀ * eNorm Nv) ∧
        ‖Xᵀ * (K * (Vᵀ * eNorm Nv))‖ ≤ M ∧ ‖S * Vᵀ‖ ≤ M ∧
        (S * Vᵀ) * eNorm Nv = Xᵀ * (K * (Vᵀ * eNorm Nv)) ∧
        (∀ j, ‖perp X (D j * (K * (Vᵀ * eNorm Nv)))‖ ≤ C * ε) ∧
        (∀ z : Matrix (Unit ⊕ Fin d) Unit ℝ, lam₀ * ‖z‖ ≤
          ‖Matrix.fromCols (K * (Vᵀ * eNorm Nv)) (dirMat D (K * (Vᵀ * eNorm Nv))) * z‖) ∧
        ‖S * Vᵀ - ((Xᵀ * (K * (Vᵀ * eNorm Nv))) * (eNorm Nv)ᵀ -
          ε • (colsOf fun i => Xᵀ * (D i * (K * (Vᵀ * eNorm Nv)))) * (velMat v)ᵀ)‖ ≤ C * ε ^ 2 := by
  have hNv := hv.pos
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, M₀ = (2 * (√(r : ℝ)) ^ 2 + 1) * B₀ := ⟨_, rfl⟩
  have hM₀0 : 0 ≤ M₀ := by rw [hM₀]; positivity
  obtain ⟨M, hM⟩ : ∃ M, M = M₀ * (√(r : ℝ) + 1) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hsqr : 0 ≤ √(r : ℝ) := Real.sqrt_nonneg _
  have hMM₀ : M₀ ≤ M := by rw [hM]; nlinarith
  have hMr : M₀ * √(r : ℝ) ≤ M := by rw [hM]; nlinarith
  obtain ⟨BH', hBH'⟩ : ∃ BH', BH' = |BH| + 1 := ⟨_, rfl⟩
  have hBH'0 : 0 < BH' := by rw [hBH']; positivity
  refine ⟨M, min (√(1 / (BH' * (∑ i, ‖D i‖ ^ 2 + 1))))
    (1 / (BH' * (√(∑ i, ‖D i‖ ^ 2 + 1) * M + 1))), hM0,
    lt_min (by positivity) (by positivity), fun Δt hΔt => ?_⟩
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := kStep_B1 (r := r) D hD hv hΔt hB₀ hCA
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ i, ‖velPi v i‖ := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨Dm, hDm⟩ : ∃ Dm, Dm = ∑ i, ‖D i‖ := ⟨_, rfl⟩
  have hDm0 : 0 ≤ Dm := by rw [hDm]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hDk : ∀ i, ‖D i‖ ≤ Dm := fun i => by
    rw [hDm]
    exact Finset.single_le_sum (f := fun i => ‖D i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  obtain ⟨C₄, hC₄⟩ : ∃ C₄, C₄ = C₃ * μ + M * (CA * μ) +
      d * (Dm * M * (μ * CA + CA * μ * μ + CA * μ * CA)) := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; positivity
  obtain ⟨C₇, hC₇⟩ : ∃ C₇, C₇ = C₃ + M * CA + d * (Dm * M * (CA + CA * μ * r)) := ⟨_, rfl⟩
  have hC₇0 : 0 ≤ C₇ := by rw [hC₇]; positivity
  refine ⟨d * C₄ + C₇, ε₃, by positivity, hε₃, hε₃1, ?_⟩
  intro ε hε hεε X S V Km K hX hV hc hKs hKm hKS hdet hHn
  have hε1 : ε ≤ 1 := (hεε.trans_le hε₃1).le
  obtain ⟨hKn, hE⟩ := h3 ε hε hεε V Km K hV hc hKs hKm
  rw [← hM₀] at hKn
  have hαn : ‖Vᵀ * eNorm Nv‖ ≤ √(r : ℝ) := norm_alpha_le hNv hV
  have hkn : ‖K * (Vᵀ * eNorm Nv)‖ ≤ M := by
    refine ((Frobenius.norm_mul_le _ _).trans ?_).trans hMr
    gcongr
  have hE' := fun j => K_test (D := D) hv hV hCA hε.le hε1 hc hkn hDk hDm0 hE j
  have hL := L_expansion (D := D) hv hX hV hKS hε.le hε1 hCA hc hkn hDk hDm0 hE
  rw [← hμ, ← hC₄] at hE'
  rw [← hμ, ← hC₇] at hL
  have hS : Xᵀ * K = S := by rw [hKS, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  have hXk : X * (Xᵀ * (K * (Vᵀ * eNorm Nv))) = K * (Vᵀ * eNorm Nv) := by
    rw [← Matrix.mul_assoc Xᵀ, hS, hKS, Matrix.mul_assoc]
  have hy₀ : (S * Vᵀ) * eNorm Nv = Xᵀ * (K * (Vᵀ * eNorm Nv)) := by
    rw [← Matrix.mul_assoc Xᵀ, hS, Matrix.mul_assoc]
  have hSn : ‖S * Vᵀ‖ ≤ M := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV,
      ← Frobenius.norm_mul_of_orthonormal hX S, ← hKS]
    exact hKn.trans hMM₀
  have hBH : ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH' :=
    hHn.trans (by rw [hBH']; linarith [le_abs_self BH])
  refine ⟨hXk, (norm_transpose_mul_le hX _).trans hkn, hSn, hy₀, fun j => ?_,
    gram_bound hd hD hBH'0 hM0 hkn hdet hBH, hL.trans ?_⟩
  · refine (perp_D_le hX hd hKS hε (hE' j)).trans ?_
    have : 0 ≤ C₇ * ε := by positivity
    nlinarith
  · have : 0 ≤ d * C₄ * ε ^ 2 := by positivity
    nlinarith

private theorem lemma_B1_capture (hd : 0 < d) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (hD : ∀ k, (D k)ᵀ = -D k) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {B₀ CA BH θ : ℝ}
    (hB₀ : 0 ≤ B₀) (hCA : 0 ≤ CA) (hθ : 1 ≤ θ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Δt, 0 < Δt → Δt < κ → ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ)
        (Y Lp : Matrix (Fin r) (Fin Nv) ℝ) (Sp : Matrix (Fin r) (Fin r) ℝ)
        (Vp : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Capture v ε CA V → IsKStep D (fun _ => 1) v Δt ε V Km K →
        ‖Km‖ ≤ B₀ → K = X * S → (Hmat D (K * (Vᵀ * eNorm Nv))).det ≠ 0 →
        ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH →
        IsStiffSolution (AD X D) (Asig X fun _ => 1) (velPi v) (eNorm Nv) (Δt / θ) ε Y (S * Vᵀ) →
        Lp = θ • Y - (θ - 1) • (S * Vᵀ) → Lp = Sp * Vpᵀ → Vpᵀ * Vp = 1 → Capture v ε C Vp := by
  obtain ⟨M, lam₀, hM, hlam, hK⟩ := kSide (r := r) hd D hD hv (BH := BH) hB₀ hCA
  obtain ⟨g, hg⟩ : ∃ g, g = (r : ℝ) * ∑ i, ‖D i‖ := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hg]; positivity
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = (1 + d * g) * (g * g) * (M + 1) := ⟨_, rfl⟩
  have hX₀0 : 0 ≤ X₀ := by rw [hX₀]; positivity
  refine ⟨lam₀ / (4 * X₀ + 1), by positivity, fun Δt hΔt hκ => ?_⟩
  have hκ' : Δt * (4 * X₀ + 1) < lam₀ := (lt_div_iff₀ (by positivity)).mp hκ
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 0 ≤ θ - 1 := by linarith
  obtain ⟨C₇, ε₇, hC₇, hε₇, hε₇1, h7⟩ := hK Δt hΔt
  obtain ⟨C₅, ε₅, hC₅, hε₅, hε₅1, h5⟩ := lStep_B1 (Nx := Nx) (r := r) D hD hv (τ := Δt / θ)
    (by positivity)
  rw [← hg] at h5
  obtain ⟨C₈, hC₈⟩ : ∃ C₈, C₈ = (1 + d * g) * (θ * (C₅ * M)) + d * C₇ := ⟨_, rfl⟩
  have hC₈0 : 0 ≤ C₈ := by rw [hC₈]; positivity
  obtain ⟨C₆, hC₆⟩ : ∃ C₆, C₆ = θ * (C₅ * M) + (θ - 1) * C₇ := ⟨_, rfl⟩
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆]; positivity
  refine ⟨2 * C₆ / lam₀, min ε₇ (min ε₅ (min (1 / (C₅ * M + 1)) (lam₀ / (4 * C₈ + 1)))),
    by positivity, lt_min hε₇ (lt_min hε₅ (lt_min (by positivity) (by positivity))),
    (min_le_left _ _).trans hε₇1, ?_⟩
  intro ε hε hεε X S V Km K Y Lp Sp Vp hX hV hc hKs hKm hKS hdet hHn hY hLp hqr hVp
  have hεε₇ : ε < ε₇ := hεε.trans_le (min_le_left _ _)
  have hεε₅ : ε < ε₅ := hεε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεe₁ : ε < 1 / (C₅ * M + 1) :=
    hεε.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεe₂ : ε < lam₀ / (4 * C₈ + 1) :=
    hεε.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hXk, hy₀n, hSn, hy₀, hperp, hlow, hLexp⟩ :=
    h7 ε hε hεε₇ X S V Km K hX hV hc hKs hKm hKS hdet hHn
  obtain ⟨b1, b2⟩ := h5 ε hε hεε₅ X Y (S * Vᵀ) hX hY
  obtain ⟨k, hk⟩ : ∃ k, k = K * (Vᵀ * eNorm Nv) := ⟨_, rfl⟩
  rw [← hk] at hXk hy₀n hy₀ hperp hlow hLexp
  obtain ⟨y₀, hy₀def⟩ : ∃ y₀, y₀ = Xᵀ * k := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = S * Vᵀ := ⟨_, rfl⟩
  rw [← hL] at b1 b2 hSn hy₀ hLexp hLp
  rw [hy₀] at b1
  rw [← hy₀def] at b1 hy₀n hLexp
  obtain ⟨m, hm⟩ : ∃ m, m = Y * eNorm Nv := ⟨_, rfl⟩
  rw [← hm] at b1 b2
  have hsm : C₅ * ε * M ≤ 1 := by
    have h1 : ε * (C₅ * M + 1) < 1 := (lt_div_iff₀ (by positivity)).mp hεe₁
    have e : ε * (C₅ * M + 1) = C₅ * ε * M + ε := by ring
    linarith
  have hCL : C₅ * ε * ‖L‖ ≤ C₅ * ε * M := by gcongr
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = θ • (m - y₀) := ⟨_, rfl⟩
  have hmy : ‖m - y₀‖ ≤ Δt / θ * (g * g) * (M + 1) + C₅ * ε * M := by
    refine b1.trans ?_
    have h1 : ‖y₀‖ + C₅ * ε * ‖L‖ ≤ M + 1 := by linarith
    have h2 : Δt / θ * (g * g) * (‖y₀‖ + C₅ * ε * ‖L‖) ≤ Δt / θ * (g * g) * (M + 1) := by gcongr
    linarith
  have hζn : ‖ζ‖ ≤ Δt * (g * g) * (M + 1) + θ * (C₅ * ε * M) := by
    rw [hζ, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0]
    calc θ * ‖m - y₀‖ ≤ θ * (Δt / θ * (g * g) * (M + 1) + C₅ * ε * M) := by gcongr
      _ = _ := by field_simp
  have hsmall : (1 + d * g) * (Δt * (g * g) * (M + 1) + θ * (C₅ * ε * M)) + d * (C₇ * ε) ≤
      lam₀ / 2 := by
    have h1 : ε * (4 * C₈ + 1) < lam₀ := (lt_div_iff₀ (by positivity)).mp hεe₂
    have h2 : (1 + d * g) * (Δt * (g * g) * (M + 1) + θ * (C₅ * ε * M)) + d * (C₇ * ε) =
        Δt * X₀ + ε * C₈ := by
      rw [hX₀, hC₈]; ring
    rw [h2]
    have e1 : Δt * (4 * X₀ + 1) = 4 * (Δt * X₀) + Δt := by ring
    have e2 : ε * (4 * C₈ + 1) = 4 * (ε * C₈) + ε := by ring
    linarith
  have hAy : ∀ i, AD X D i * y₀ = Xᵀ * (D i * k) := fun i => by
    rw [hy₀def, AD]
    simp only [Matrix.mul_assoc]
    rw [hXk]
  have hcols : (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) =
      θ • (colsOf fun i => AD X D i * m) - (θ - 1) • colsOf fun i => Xᵀ * (D i * k) := by
    rw [← colsOf_smul, ← colsOf_smul, ← colsOf_sub]
    congr 1
    ext1 i
    rw [hζ, Matrix.mul_smul, Matrix.mul_sub, hAy]
    module
  have hc₀ : Xᵀ * k + ζ = θ • m - (θ - 1) • y₀ := by
    rw [← hy₀def, hζ]
    module
  have hS : ‖Lp - ((Xᵀ * k + ζ) * (eNorm Nv)ᵀ -
      ε • (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) * (velMat v)ᵀ)‖ ≤ C₆ * ε ^ 2 := by
    obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = (colsOf fun i => AD X D i * m) * (velMat v)ᵀ := ⟨_, rfl⟩
    obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = (colsOf fun i => Xᵀ * (D i * k)) * (velMat v)ᵀ := ⟨_, rfl⟩
    have e : Lp - ((Xᵀ * k + ζ) * (eNorm Nv)ᵀ -
        ε • (colsOf fun i => Xᵀ * (D i * k) + AD X D i * ζ) * (velMat v)ᵀ) =
        θ • (Y - (m * (eNorm Nv)ᵀ - ε • (colsOf fun i => AD X D i * m) * (velMat v)ᵀ)) -
        (θ - 1) • (L - (y₀ * (eNorm Nv)ᵀ -
          ε • (colsOf fun i => Xᵀ * (D i * k)) * (velMat v)ᵀ)) := by
      rw [hcols, hc₀, hLp]
      simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, ← hA₁, ← hA₂]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hθ0,
      abs_of_nonneg hθ1]
    have h1 : C₅ * ε ^ 2 * ‖L‖ ≤ C₅ * ε ^ 2 * M := by gcongr
    calc _ ≤ θ * (C₅ * ε ^ 2 * M) + (θ - 1) * (C₇ * ε ^ 2) := by
          have h2 := b2.trans h1
          have h3 : ‖L - (y₀ * (eNorm Nv)ᵀ - ε • (colsOf fun i => Xᵀ * (D i * k)) * (velMat v)ᵀ)‖ ≤
              C₇ * ε ^ 2 := hLexp
          gcongr
      _ = _ := by rw [hC₆]; ring
  exact capture_of_structure hv hX hlam hlow hXk hperp
    (fun i => by rw [hg]; exact norm_AD_le hX i) hg0 (by positivity) hζn hsmall hS hqr hVp hε

private theorem lemma_B1_aux (hd : 0 < d) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (hD : ∀ k, (D k)ᵀ = -D k) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (hr : d + 1 ≤ r)
    {B₀ CA BH θ : ℝ} (hB₀ : 0 ≤ B₀) (hθ : 1 ≤ θ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Δt, 0 < Δt → Δt < κ → ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ)
        (Y Lp : Matrix (Fin r) (Fin Nv) ℝ) (Sp : Matrix (Fin r) (Fin r) ℝ)
        (Vp : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Assumption1 v hr ε CA V →
        IsKStep D (fun _ => 1) v Δt ε V Km K →
        ‖Km‖ ≤ B₀ → K = X * S → (Hmat D (K * (Vᵀ * eNorm Nv))).det ≠ 0 →
        ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH →
        IsStiffSolution (AD X D) (Asig X fun _ => 1) (velPi v) (eNorm Nv) (Δt / θ) ε Y (S * Vᵀ) →
        Lp = θ • Y - (θ - 1) • (S * Vᵀ) → Lp = Sp * Vpᵀ → Vpᵀ * Vp = 1 →
        Assumption1 v hr ε C Vp := by
  obtain ⟨κ, hκ, h⟩ := lemma_B1_capture (r := r) hd D hD hv (BH := BH) hB₀
    (mul_nonneg zero_le_two (abs_nonneg CA)) hθ
  refine ⟨κ, hκ, fun Δt hΔt hΔκ => ?_⟩
  obtain ⟨C, ε₀, hC, hε₀, hε₀1, h1⟩ := h Δt hΔt hΔκ
  obtain ⟨c, hc⟩ : ∃ c, c = capκ d C := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc, capκ]; positivity
  refine ⟨C + √(r : ℝ) * capκ d C + √(d : ℝ) * C + √(d : ℝ) * C ^ 2 + capκ d C,
    min ε₀ (1 / (c + 1)), by rw [← hc]; positivity, lt_min hε₀ (by positivity), ?_⟩
  intro ε hε hεε X S V Km K Y Lp Sp Vp hX hV hA hKs hKm hKS hdet hHn hY hLp hqr hVp
  have hεε₀ : ε < ε₀ := hεε.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hεε₀.trans_le hε₀1).le
  have hcap := h1 ε hε hεε₀ X S V Km K Y Lp Sp Vp hX hV (hA.capture' hV hε hε1) hKs hKm hKS hdet
    hHn hY hLp hqr hVp
  refine hcap.assumption1 hv hr hVp hε hε1 hC ?_
  rw [← hc]
  have h2 : ε < 1 / (c + 1) := hεε.trans_le (min_le_right _ _)
  have h3 : ε * (c + 1) < 1 := (lt_div_iff₀ (by positivity)).mp h2
  have h4 : ε ^ 2 ≤ ε := by nlinarith
  nlinarith

/-- **Lemma B.1 of arXiv 1907.04247** (propagation of Assumption 1), for the Crank–Nicolson
`L`-step used by Algorithm 3.1 from the second step on.  Take `σ = 1` and skew `D_i`, as in the
paper.  Given bounds `B₀, CA, BH`, there is `κ > 0` such that for `Δt < κ` there are `C, ε₀` with
the following property for `ε < ε₀`.  Let `V = Vⁿ` satisfy Assumption 1 with constant `CA` and let
`K = Kⁿ` solve (2.25) with `V`, from `‖Km‖ ≤ B₀`, with `K = X S` (QR).  Put `k = K Vᵀ e_n` and
assume `det 𝓗(k) ≠ 0`, with `‖𝓗(k)⁻¹‖ ≤ BH`.  Let `Lp = L^{n+1/3}` solve (2.19) with `L = S Vᵀ`, and
let `Lp = Sp Vpᵀ` with orthonormal `Vp = V^{n+1}`.  Then `Vp` satisfies Assumption 1 with constant
`C`.

Differences from the paper.  `kⁿ` is the exact `Kⁿ αⁿ`, whose limit is the paper's `kⁿ`; the bound
`BH` makes `det 𝓗 ≠ 0` uniform in `ε`, and `κ` (the "`Δt / (Δx)²` small enough") depends on the
mesh through these bounds.  The proof avoids the matrix `P` of (B.8), which need not be well
conditioned, and it does not use the step after (B.15), which looks only at the first column of
`A*_{∂_m}` although `l*` has other components: it shows directly that `(k, D₁ k, …, D_d k)`, whose
Gram matrix is `diag(‖k‖², 𝓗(k))`, is perturbed by little.  See also `lemma_B1_IE`. -/
theorem lemma_B1 (hd : 0 < d) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (hD : ∀ k, (D k)ᵀ = -D k) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (hr : d + 1 ≤ r)
    {B₀ CA BH : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Δt, 0 < Δt → Δt < κ → ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ)
        (Lp : Matrix (Fin r) (Fin Nv) ℝ) (Sp : Matrix (Fin r) (Fin r) ℝ)
        (Vp : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Assumption1 v hr ε CA V →
        IsKStep D (fun _ => 1) v Δt ε V Km K →
        ‖Km‖ ≤ B₀ → K = X * S → (Hmat D (K * (Vᵀ * eNorm Nv))).det ≠ 0 →
        ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH →
        IsLStepCN D (fun _ => 1) v Δt ε X (S * Vᵀ) Lp → Lp = Sp * Vpᵀ → Vpᵀ * Vp = 1 →
        Assumption1 v hr ε C Vp := by
  obtain ⟨κ, hκ, h⟩ := lemma_B1_aux (Nx := Nx) hd D hD hv hr (CA := CA) (BH := BH) (θ := 2) hB₀
    one_le_two
  refine ⟨κ, hκ, fun Δt hΔt hΔκ => ?_⟩
  obtain ⟨C, ε₀, hC, hε₀, h1⟩ := h Δt hΔt hΔκ
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεε X S V Km K Lp Sp Vp hX hV hA hKs hKm hKS hdet hHn hL hqr hVp
    => ?_⟩
  refine h1 ε hε hεε X S V Km K ((2 : ℝ)⁻¹ • (Lp + S * Vᵀ)) Lp Sp Vp hX hV hA hKs hKm hKS hdet hHn
    (hL.stiff hΔt.ne') ?_ hqr hVp
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e, one_smul]
  exact two_smul_mid

/-- **Lemma B.1 of arXiv 1907.04247 for the implicit Euler `L`-step (2.18)**: the same statement
as `lemma_B1`.  This covers the first step of Algorithm 3.1. -/
theorem lemma_B1_IE (hd : 0 < d) (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ)
    (hD : ∀ k, (D k)ᵀ = -D k) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (hr : d + 1 ≤ r)
    {B₀ CA BH : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Δt, 0 < Δt → Δt < κ → ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ) (Km K : Matrix (Fin Nx) (Fin r) ℝ)
        (Lp : Matrix (Fin r) (Fin Nv) ℝ) (Sp : Matrix (Fin r) (Fin r) ℝ)
        (Vp : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → Vᵀ * V = 1 → Assumption1 v hr ε CA V →
        IsKStep D (fun _ => 1) v Δt ε V Km K →
        ‖Km‖ ≤ B₀ → K = X * S → (Hmat D (K * (Vᵀ * eNorm Nv))).det ≠ 0 →
        ‖(Hmat D (K * (Vᵀ * eNorm Nv)))⁻¹‖ ≤ BH →
        IsLStepIE D (fun _ => 1) v Δt ε X (S * Vᵀ) Lp → Lp = Sp * Vpᵀ → Vpᵀ * Vp = 1 →
        Assumption1 v hr ε C Vp := by
  obtain ⟨κ, hκ, h⟩ := lemma_B1_aux (Nx := Nx) hd D hD hv hr (CA := CA) (BH := BH) (θ := 1) hB₀
    le_rfl
  refine ⟨κ, hκ, fun Δt hΔt hΔκ => ?_⟩
  obtain ⟨C, ε₀, hC, hε₀, h1⟩ := h Δt hΔt hΔκ
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεε X S V Km K Lp Sp Vp hX hV hA hKs hKm hKS hdet hHn hL hqr hVp
    => ?_⟩
  refine h1 ε hε hεε X S V Km K Lp Lp Sp Vp hX hV hA hKs hKm hKS hdet hHn
    (by rw [div_one]; exact hL.stiff hΔt.ne') (by simp) hqr hVp

end LemmaB1

section LemmaA1

variable {Nx Nv r d : ℕ}

/-- **The kernel computation behind Lemma A.1 of arXiv 1907.04247**, (3.14), (3.18), (3.23): for
invertible `W`, `ker (Z ↦ W Z (P - 1)) = {Z : Z P = Z}`. -/
theorem kernel_right_factor {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]
    {W Winv : Matrix m m ℝ} (hW : Winv * W = 1) (P : Matrix p p ℝ) (Z : Matrix m p ℝ) :
    W * Z * (P - 1) = 0 ↔ Z * P = Z := by
  constructor
  · intro h
    have h1 := congrArg (fun A => Winv * A) h
    simp only [Matrix.mul_zero] at h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one] at h1
    exact sub_eq_zero.mp h1
  · intro h
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, h, sub_self, Matrix.mul_zero]

/-- **The leading-order structure of (3.14), arXiv 1907.04247**: the `O(ε⁻²)` part `A_σ L₀ C = 0`
of the `L`-step holds iff `L₀ = l₀ e_nᵀ`, with `l₀ = L₀ e_n`. -/
theorem leading_order_L {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ} {s : ℝ} (hs : 0 < s)
    (hX : Xᵀ * X = 1) (hσ : ∀ i, s ≤ σ i) (Z : Matrix (Fin r) (Fin Nv) ℝ) :
    Asig X σ * Z * collC Nv = 0 ↔ Z = (Z * eNorm Nv) * (eNorm Nv)ᵀ := by
  rw [collC_eq, kernel_right_factor (Matrix.nonsing_inv_mul _ (Asig_isUnit hs hX hσ)),
    Matrix.mul_assoc, eq_comm]

/-- **The leading-order structure of (3.18) and (3.23), arXiv 1907.04247**: the `O(ε⁻²)` parts
`A_σ S₀ Γ = 0` and `Σ K₀ Γ = 0` of the `S`- and `K`-step hold iff `S₀ = s₀ αᵀ`, `K₀ = k₀ αᵀ`, with
`α = Vᵀ e_n`. -/
theorem leading_order_SK {X : Matrix (Fin Nx) (Fin r) ℝ} {σ : Fin Nx → ℝ} {s : ℝ} (hs : 0 < s)
    (hX : Xᵀ * X = 1) (hσ : ∀ i, s ≤ σ i) {V : Matrix (Fin Nv) (Fin r) ℝ} (hV : Vᵀ * V = 1)
    (Z : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin Nx) (Fin r) ℝ) :
    (Asig X σ * Z * Gam V = 0 ↔ Z = (Z * (Vᵀ * eNorm Nv)) * (Vᵀ * eNorm Nv)ᵀ) ∧
    (Matrix.diagonal σ * Y * Gam V = 0 ↔ Y = (Y * (Vᵀ * eNorm Nv)) * (Vᵀ * eNorm Nv)ᵀ) := by
  have hσ0 : ∀ i, 0 < σ i := fun i => hs.trans_le (hσ i)
  have hU : IsUnit (Matrix.diagonal σ).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hσ0 i).ne'
  constructor
  · rw [Gam_eq hV, kernel_right_factor (Matrix.nonsing_inv_mul _ (Asig_isUnit hs hX hσ)),
      ← Matrix.mul_assoc Z, eq_comm]
  · rw [Gam_eq hV, kernel_right_factor (Matrix.nonsing_inv_mul _ hU), ← Matrix.mul_assoc Y, eq_comm]

/-- **Lemma A.1 of arXiv 1907.04247, the `L`- and `S`-part**, as an estimate.  If `Lⁿ` is rank one
with right factor `e_n` up to `O(ε)`, then so is `L^{n+1/3}` from the Crank–Nicolson step (2.19),
and `S^{n+1/3} = s (α^{n+1})ᵀ + O(ε)`.  The paper states this for the leading order of the formal
expansion; here `s = L^{n+1/3} e_n`.  With `lemma_A1_K` this is the induction (A.7)–(A.9). -/
theorem lemma_A1 (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    {BL B C₀ : ℝ} (hBL : 0 ≤ BL) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin r) ℝ) (l : Matrix (Fin r) Unit ℝ)
        (L L₁ : Matrix (Fin r) (Fin Nv) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ)
        (V : Matrix (Fin Nv) (Fin r) ℝ),
        Xᵀ * X = 1 → ‖L‖ ≤ BL → ‖L - l * (eNorm Nv)ᵀ‖ ≤ C₀ * ε →
        IsLStepCN D σ v Δt ε X L L₁ → L₁ = S₁ * Vᵀ → Vᵀ * V = 1 →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B →
        ‖L₁ - (L₁ * eNorm Nv) * (eNorm Nv)ᵀ‖ ≤ C * ε ∧
        ‖S₁ - (L₁ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ‖ ≤ C * ε := by
  have hNv := hv.pos
  have he : (eNorm Nv)ᵀ * eNorm Nv = 1 := eNorm_transpose_mul hNv
  have hen : ‖eNorm Nv‖ = 1 := norm_eNorm hNv
  obtain ⟨s₀, hs₀, hσs⟩ := exists_lower_bound hσ
  obtain ⟨C₁, ε₁, hC₁, hε₁, hε₁1, h1⟩ := stiff_main (m := Fin r) (p := Fin Nv) d
    (by positivity : Δt / 2 ≠ 0) (r * ∑ i, ‖D i‖) (√(r : ℝ) / s₀) (r * ‖Matrix.diagonal σ‖)
    (∑ i, ‖velPi v i‖) 1 0 B hB
  refine ⟨2 * (C₁ * BL) + 2 * C₀, ε₁, by positivity, hε₁, ?_⟩
  intro ε hε hεε X l L L₁ S₁ V hX hLB hwp hs hqr hV hst
  have hdd : Δt / 2 / (d : ℝ) = Δt / (2 * d) := by rw [div_div]
  have hst' : Stable (1 - (Δt / 2 / d) • limL X D σ) B := by rwa [hdd]
  obtain ⟨-, a2, -, -⟩ := h1 ε hε hεε _ _ _ _ _ _ _ (stiffHyp_L (D := D) hv hs₀ hσs hX)
    (stable_lift hX hst') (hs.stiff hΔt.ne')
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (2 : ℝ)⁻¹ • (L₁ + L) := ⟨_, rfl⟩
  rw [← hY] at a2
  have hL₁ : L₁ = (2 : ℝ) • Y - L := by rw [hY]; exact two_smul_mid
  obtain ⟨G, hG⟩ : ∃ G, G = L - l * (eNorm Nv)ᵀ := ⟨_, rfl⟩
  have hLG : L = l * (eNorm Nv)ᵀ + G := by rw [hG]; abel
  have e1 : L - (L * eNorm Nv) * (eNorm Nv)ᵀ = G - (G * eNorm Nv) * (eNorm Nv)ᵀ := by
    have e2 : (l * (eNorm Nv)ᵀ * eNorm Nv) * (eNorm Nv)ᵀ = l * (eNorm Nv)ᵀ := by
      rw [Matrix.mul_assoc l, he, Matrix.mul_one]
    conv_lhs => rw [hLG]
    rw [Matrix.add_mul, Matrix.add_mul, e2]
    abel
  have e2 : ‖L - (L * eNorm Nv) * (eNorm Nv)ᵀ‖ ≤ 2 * (C₀ * ε) := by
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have h3 : ‖G * eNorm Nv * (eNorm Nv)ᵀ‖ ≤ ‖G‖ := by
      refine (norm_mul3_le _ _ _).trans (le_of_eq ?_)
      rw [Frobenius.norm_transpose, hen, mul_one, mul_one]
    have h4 : ‖G‖ ≤ C₀ * ε := by rw [hG]; exact hwp
    linarith
  have e3 : L₁ - (L₁ * eNorm Nv) * (eNorm Nv)ᵀ =
      (2 : ℝ) • (Y - Y * eNorm Nv * (eNorm Nv)ᵀ) - (L - (L * eNorm Nv) * (eNorm Nv)ᵀ) := by
    rw [hL₁]
    simp only [Matrix.sub_mul, Matrix.smul_mul]
    module
  have e4 : ‖L₁ - (L₁ * eNorm Nv) * (eNorm Nv)ᵀ‖ ≤ (2 * (C₁ * BL) + 2 * C₀) * ε := by
    rw [e3]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have h2 : ‖Y - Y * eNorm Nv * (eNorm Nv)ᵀ‖ ≤ C₁ * ε * BL := a2.trans (by gcongr)
    have h3 : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [h3]
    calc _ ≤ 2 * (C₁ * ε * BL) + 2 * (C₀ * ε) := by linarith
      _ = _ := by ring
  refine ⟨e4, ?_⟩
  have hS : S₁ = L₁ * V := by
    rw [hqr, Matrix.mul_assoc, hV, Matrix.mul_one]
  have e5 : S₁ - (L₁ * eNorm Nv) * (Vᵀ * eNorm Nv)ᵀ =
      (L₁ - (L₁ * eNorm Nv) * (eNorm Nv)ᵀ) * V := by
    rw [Matrix.sub_mul, ← hS, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [e5]
  exact (norm_mul_le_of_orthonormal hV _).trans e4

/-- **Lemma A.1 of arXiv 1907.04247, the base case and the last step of the induction**, (A.3),
(A.4), (A.7).  After the implicit Euler `K`-step, whatever its input, the new `L = S Vᵀ` has the
form `l e_nᵀ + O(ε)`, if `V` satisfies Assumption 1. -/
theorem lemma_A1_K (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ r) {BF CA B : ℝ} (hBF : 0 ≤ BF) (hB : 0 ≤ B) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (V : Matrix (Fin Nv) (Fin r) ℝ) (F K X : Matrix (Fin Nx) (Fin r) ℝ)
        (S : Matrix (Fin r) (Fin r) ℝ),
        Vᵀ * V = 1 → Assumption1 v hr ε CA V → ‖F‖ ≤ BF → IsKStep D σ v Δt ε V F K →
        Stable (1 - (Δt / d) • limD D σ) B → K = X * S → Xᵀ * X = 1 →
        ‖S * Vᵀ - (S * Vᵀ * eNorm Nv) * (eNorm Nv)ᵀ‖ ≤ C * ε := by
  have hNv := hv.pos
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * |CA| := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨C₃, ε₃, hC₃, hε₃, hε₃1, h3⟩ := stiff_main (m := Fin Nx) (p := Fin r) d hΔt.ne'
    (∑ i, ‖D i‖) ‖(Matrix.diagonal σ)⁻¹‖ ‖Matrix.diagonal σ‖ (r * ∑ i, ‖velPi v i‖) (√(r : ℝ))
    (momC r (∑ i, ‖velPi v i‖) c) B hB
  obtain ⟨M, hM⟩ : ∃ M, M = (2 * B * (√(r : ℝ)) ^ 2 + 1) * BF * √(r : ℝ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨C₃ * BF + M * c, ε₃, by positivity, hε₃, ?_⟩
  intro ε hε hεε V F K X S hV hA hF hK hst hKS hX
  have hε1 : ε ≤ 1 := (hεε.trans_le hε₃1).le
  have hcap : Capture v ε c V := by rw [hc]; exact hA.capture' hV hε hε1
  obtain ⟨b1, b2, -, -⟩ := h3 ε hε hεε _ _ _ _ _ _ _
    (stiffHyp_K (D := D) hv hσ hV hc0 hε.le hε1 hcap) hst (hK.stiff hΔt.ne' hV)
  obtain ⟨α, hα⟩ : ∃ α, α = Vᵀ * eNorm Nv := ⟨_, rfl⟩
  have hαn : ‖α‖ ≤ √(r : ℝ) := by rw [hα]; exact norm_alpha_le hNv hV
  have hcapt : ‖eNorm Nv - V * α‖ ≤ c * ε ^ 2 := by rw [hα]; exact hcap.e
  rw [← hα] at b2
  have hS : S = Xᵀ * K := by rw [hKS, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  obtain ⟨k, hk⟩ : ∃ k, k = K * α := ⟨_, rfl⟩
  rw [← hk] at b2
  have hkn : ‖k‖ ≤ M := by
    rw [hk, hM]
    refine (Frobenius.norm_mul_le _ _).trans ?_
    have h1 : ‖K‖ ≤ (2 * B * (√(r : ℝ)) ^ 2 + 1) * BF := b1.trans (by gcongr)
    gcongr
  have e1 : S * Vᵀ - (S * Vᵀ * eNorm Nv) * (eNorm Nv)ᵀ =
      Xᵀ * (K - k * αᵀ) * Vᵀ - (Xᵀ * k) * (eNorm Nv - V * α)ᵀ := by
    have e2 : S * Vᵀ * eNorm Nv = Xᵀ * k := by
      rw [hS, hk, hα]
      simp only [Matrix.mul_assoc]
    rw [e2, hS, Matrix.transpose_sub, Matrix.transpose_mul V α, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_sub (Xᵀ * k)]
    simp only [Matrix.mul_assoc]
    abel
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  have t1 : ‖Xᵀ * (K - k * αᵀ) * Vᵀ‖ ≤ C₃ * ε * BF := by
    rw [Frobenius.norm_mul_transpose_of_orthonormal hV]
    exact (norm_transpose_mul_le hX _).trans (b2.trans (by gcongr))
  have t2 : ‖(Xᵀ * k) * (eNorm Nv - V * α)ᵀ‖ ≤ M * (c * ε) := by
    refine (Frobenius.norm_mul_le _ _).trans ?_
    rw [Frobenius.norm_transpose]
    have h5 : ε ^ 2 ≤ ε := by nlinarith
    exact mul_le_mul ((norm_transpose_mul_le hX _).trans hkn) (hcapt.trans (by gcongr))
      (norm_nonneg _) hM0
  calc _ ≤ C₃ * ε * BF + M * (c * ε) := add_le_add t1 t2
    _ = _ := by ring

end LemmaA1

section Converse

variable {Nx Nv r d : ℕ}

private theorem bridge_converse {m p : Type*} [Fintype p] [DecidableEq p]
    {G : Fin d → Matrix m m ℝ} [Fintype m] {W : Matrix m m ℝ}
    {M : Fin d → Matrix p p ℝ} {w : Matrix p Unit ℝ} {τ ε : ℝ} (hτ : τ ≠ 0) {Y F : Matrix m p ℝ}
    (h : IsStiffSolution G W M w τ ε Y F) :
    τ⁻¹ • (Y - F) + ε⁻¹ • transport G M Y = (ε ^ 2)⁻¹ • (W * Y * (w * wᵀ - 1)) := by
  have e : W * Y * (1 - w * wᵀ) = -(W * Y * (w * wᵀ - 1)) := by
    rw [← Matrix.mul_neg, neg_sub]
  rw [IsStiffSolution, e, smul_neg] at h
  rw [← h]
  have e1 : τ⁻¹ * (τ / ε) = ε⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hτ, one_mul]
  have e2 : τ⁻¹ * (τ / ε ^ 2) = (ε ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hτ, one_mul]
  have e3 : Y - (Y + (τ / ε) • transport G M Y + -((τ / ε ^ 2) • (W * Y * (w * wᵀ - 1)))) =
      (τ / ε ^ 2) • (W * Y * (w * wᵀ - 1)) - (τ / ε) • transport G M Y := by abel
  rw [e3, smul_sub, smul_smul, smul_smul, e1, e2]
  abel

private theorem cn_smul {m p : Type*} {Δt : ℝ} (hΔt : Δt ≠ 0) (A B : Matrix m p ℝ) :
    (Δt / 2)⁻¹ • ((2 : ℝ)⁻¹ • (A + B) - B) = Δt⁻¹ • (A - B) := by
  have e : (2 : ℝ)⁻¹ • (A + B) - B = (2 : ℝ)⁻¹ • (A - B) := by module
  rw [e, smul_smul]
  congr 1
  field_simp

theorem IsLStepIE.of_stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {L L₁ : Matrix (Fin r) (Fin Nv) ℝ} (hΔt : Δt ≠ 0)
    (h : IsStiffSolution (AD X D) (Asig X σ) (velPi v) (eNorm Nv) Δt ε L₁ L) :
    IsLStepIE D σ v Δt ε X L L₁ := by
  have h1 := bridge_converse hΔt h
  rw [transport, ← collC_eq] at h1
  exact h1

theorem IsLStepCN.of_stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {L L₁ : Matrix (Fin r) (Fin Nv) ℝ} (hΔt : Δt ≠ 0)
    (h : IsStiffSolution (AD X D) (Asig X σ) (velPi v) (eNorm Nv) (Δt / 2) ε
      ((2 : ℝ)⁻¹ • (L₁ + L)) L) :
    IsLStepCN D σ v Δt ε X L L₁ := by
  have h1 := bridge_converse (div_ne_zero hΔt two_ne_zero) h
  rw [transport, ← collC_eq, cn_smul hΔt] at h1
  exact h1

theorem IsSStepIE.of_stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} {S₁ S₂ : Matrix (Fin r) (Fin r) ℝ} (hΔt : Δt ≠ 0)
    (hV : Vᵀ * V = 1)
    (h : IsStiffSolution (AD X D) (Asig X σ) (Xi v V) (Vᵀ * eNorm Nv) (-Δt) ε S₂ S₁) :
    IsSStepIE D σ v Δt ε X V S₁ S₂ := by
  have h1 := bridge_converse (neg_ne_zero.mpr hΔt) h
  rw [transport, ← Gam_eq hV, inv_neg, neg_smul] at h1
  rw [IsSStepIE, ← h1]
  abel

theorem IsSStepCN.of_stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {V : Matrix (Fin Nv) (Fin r) ℝ} {S₁ S₂ : Matrix (Fin r) (Fin r) ℝ} (hΔt : Δt ≠ 0)
    (hV : Vᵀ * V = 1)
    (h : IsStiffSolution (AD X D) (Asig X σ) (Xi v V) (Vᵀ * eNorm Nv) (-Δt / 2) ε
      ((2 : ℝ)⁻¹ • (S₂ + S₁)) S₁) :
    IsSStepCN D σ v Δt ε X V S₁ S₂ := by
  have h1 := bridge_converse (by simpa using hΔt) h
  rw [transport, ← Gam_eq hV, cn_smul (neg_ne_zero.mpr hΔt) S₂ S₁, inv_neg, neg_smul] at h1
  rw [IsSStepCN, ← h1]
  abel

theorem IsKStep.of_stiff {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ}
    {v : Fin d → Fin Nv → ℝ} {Δt ε : ℝ} {V : Matrix (Fin Nv) (Fin r) ℝ}
    {K₂ K₃ : Matrix (Fin Nx) (Fin r) ℝ} (hΔt : Δt ≠ 0) (hV : Vᵀ * V = 1)
    (h : IsStiffSolution D (Matrix.diagonal σ) (Xi v V) (Vᵀ * eNorm Nv) Δt ε K₃ K₂) :
    IsKStep D σ v Δt ε V K₂ K₃ := by
  have h1 := bridge_converse hΔt h
  rw [transport, ← Gam_eq hV] at h1
  exact h1

/-- The implicit substeps are solvable as soon as they are uniquely solvable. -/
theorem exists_stiff_solution {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]
    {G : Fin d → Matrix m m ℝ} {W : Matrix m m ℝ} {M : Fin d → Matrix p p ℝ}
    {w : Matrix p Unit ℝ} {τ ε : ℝ} (hinj : ∀ Y, IsStiffSolution G W M w τ ε Y 0 → Y = 0)
    (F : Matrix m p ℝ) : ∃ Y, IsStiffSolution G W M w τ ε Y F := by
  let Φ : Matrix m p ℝ →ₗ[ℝ] Matrix m p ℝ :=
    { toFun := fun Y => Y + (τ / ε) • transport G M Y + (τ / ε ^ 2) • (W * Y * (1 - w * wᵀ))
      map_add' := fun A B => by
        simp only [transport, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
        module
      map_smul' := fun c A => by
        simp only [transport, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
          RingHom.id_apply]
        module }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    exact fun Y hY => hinj Y hY
  obtain ⟨Y, hY⟩ := LinearMap.injective_iff_surjective.mp hΦ F
  exact ⟨Y, hY⟩

theorem capture_one (v : Fin d → Fin Nv → ℝ) (ε : ℝ) :
    Capture v ε 0 (1 : Matrix (Fin Nv) (Fin Nv) ℝ) where
  e := by simp
  vel k := by simp

/-- The full basis `V = 1` satisfies Assumption 1, with constant `0`. -/
theorem assumption1_one {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) (hr : d + 1 ≤ Nv) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) : Assumption1 v hr ε 0 (1 : Matrix (Fin Nv) (Fin Nv) ℝ) := by
  have h := (capture_one v ε).assumption1 hv hr (by simp) hε hε1 le_rfl (by simp [capκ])
  simpa [capκ] using h

private theorem exists_of_bound {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p]
    {G : Fin d → Matrix m m ℝ} {W : Matrix m m ℝ} {M : Fin d → Matrix p p ℝ}
    {w : Matrix p Unit ℝ} {τ ε c : ℝ}
    (hb : ∀ Y F, IsStiffSolution G W M w τ ε Y F → ‖Y‖ ≤ c * ‖F‖) (F : Matrix m p ℝ) :
    ∃ Y, IsStiffSolution G W M w τ ε Y F :=
  exists_stiff_solution (fun Y hY => by
    have h := hb Y 0 hY
    rw [norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))) F

/-- **Non-vacuity of `theorem_3_2`.**  With the full velocity basis `r = N_v`, `V = 1`, every datum
`X, L` has a step of the implicit Euler integrator for small `ε`, and Assumption 1 holds. -/
theorem exists_IEStep (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ Nv) {B : ℝ} (hB : 0 ≤ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin Nv) ℝ) (L : Matrix (Fin Nv) (Fin Nv) ℝ), Xᵀ * X = 1 →
        Stable (1 - (Δt / d) • limL X D σ) B → Stable (1 + (Δt / d) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        ∃ L₁ S₁ S₂ K₃, IsIEStep D σ v Δt ε X L L₁ S₁ 1 S₂ K₃ ∧ Assumption1 v hr ε 0 1 := by
  obtain ⟨s₀, hs₀, hσs⟩ := exists_lower_bound hσ
  obtain ⟨C₁, ε₁, -, hε₁, hε₁1, h1⟩ := stiff_main (m := Fin Nv) (p := Fin Nv) d hΔt.ne'
    (Nv * ∑ i, ‖D i‖) (√(Nv : ℝ) / s₀) (Nv * ‖Matrix.diagonal σ‖) (∑ i, ‖velPi v i‖) 1 0 B hB
  obtain ⟨C₂, ε₂, -, hε₂, -, h2⟩ := stiff_main (m := Fin Nv) (p := Fin Nv) d
    (neg_ne_zero.mpr hΔt.ne')
    (Nv * ∑ i, ‖D i‖) (√(Nv : ℝ) / s₀) (Nv * ‖Matrix.diagonal σ‖)
    (Nv * ∑ i, ‖velPi v i‖) (√(Nv : ℝ)) (momC Nv (∑ i, ‖velPi v i‖) 0) B hB
  obtain ⟨C₃, ε₃, -, hε₃, -, h3⟩ := stiff_main (m := Fin Nx) (p := Fin Nv) d hΔt.ne'
    (∑ i, ‖D i‖) ‖(Matrix.diagonal σ)⁻¹‖ ‖Matrix.diagonal σ‖ (Nv * ∑ i, ‖velPi v i‖) (√(Nv : ℝ))
    (momC Nv (∑ i, ‖velPi v i‖) 0) B hB
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro ε hε hεε X L hX hst1 hst2 hst3
  have hεε₁ : ε < ε₁ := hεε.trans_le (min_le_left _ _)
  have hεε₂ : ε < ε₂ := hεε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₃ : ε < ε₃ := hεε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (hεε₁.trans_le hε₁1).le
  have hV : (1 : Matrix (Fin Nv) (Fin Nv) ℝ)ᵀ * 1 = 1 := by simp
  obtain ⟨L₁, hL₁⟩ := exists_of_bound (fun Y F hs =>
    (h1 ε hε hεε₁ _ _ _ _ _ Y F (stiffHyp_L (D := D) hv hs₀ hσs hX) (stable_lift hX hst1) hs).1) L
  have hst2' : Stable (1 - (-Δt / d) • limL X D σ) B := by
    rw [neg_div]
    exact stable_neg hst2
  obtain ⟨S₂, hS₂⟩ := exists_of_bound (fun Y F hs =>
    (h2 ε hε hεε₂ _ _ _ _ _ Y F
      (stiffHyp_S (D := D) hv hs₀ hσs hX hV le_rfl hε.le hε1 (capture_one v ε))
      (stable_lift hX hst2') hs).1) L₁
  obtain ⟨K₃, hK₃⟩ := exists_of_bound (fun Y F hs =>
    (h3 ε hε hεε₃ _ _ _ _ _ Y F
      (stiffHyp_K (D := D) hv hσ hV le_rfl hε.le hε1 (capture_one v ε)) hst3 hs).1) (X * S₂)
  exact ⟨L₁, L₁, S₂, K₃, ⟨IsLStepIE.of_stiff hΔt.ne' hL₁, by simp, hV,
    IsSStepIE.of_stiff hΔt.ne' hV hS₂, IsKStep.of_stiff hΔt.ne' hV hK₃⟩,
    assumption1_one hv hr hε hε1⟩

/-- **Non-vacuity of `theorem_3_3`.**  With the full velocity basis `r = N_v`, `V = 1`, every datum
`X, L` has a step of the Crank–Nicolson–implicit Euler integrator for small `ε`, and Assumption 1
holds. -/
theorem exists_CNIEStep (D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ) {σ : Fin Nx → ℝ}
    (hσ : ∀ i, 0 < σ i) {v : Fin d → Fin Nv → ℝ} (hv : IsQuadrature v) {Δt : ℝ} (hΔt : 0 < Δt)
    (hr : d + 1 ≤ Nv) {B : ℝ} (hB : 0 ≤ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (X : Matrix (Fin Nx) (Fin Nv) ℝ) (L : Matrix (Fin Nv) (Fin Nv) ℝ), Xᵀ * X = 1 →
        Stable (1 - (Δt / (2 * d)) • limL X D σ) B → Stable (1 + (Δt / (2 * d)) • limL X D σ) B →
        Stable (1 - (Δt / d) • limD D σ) B →
        ∃ L₁ S₁ S₂ K₃, IsCNIEStep D σ v Δt ε X L L₁ S₁ 1 S₂ K₃ ∧ Assumption1 v hr ε 0 1 := by
  obtain ⟨s₀, hs₀, hσs⟩ := exists_lower_bound hσ
  have hτ : Δt / 2 ≠ 0 := by positivity
  have hτ' : -Δt / 2 ≠ 0 := by simpa using hΔt.ne'
  obtain ⟨C₁, ε₁, -, hε₁, hε₁1, h1⟩ := stiff_main (m := Fin Nv) (p := Fin Nv) d hτ
    (Nv * ∑ i, ‖D i‖) (√(Nv : ℝ) / s₀) (Nv * ‖Matrix.diagonal σ‖) (∑ i, ‖velPi v i‖) 1 0 B hB
  obtain ⟨C₂, ε₂, -, hε₂, -, h2⟩ := stiff_main (m := Fin Nv) (p := Fin Nv) d hτ'
    (Nv * ∑ i, ‖D i‖) (√(Nv : ℝ) / s₀) (Nv * ‖Matrix.diagonal σ‖)
    (Nv * ∑ i, ‖velPi v i‖) (√(Nv : ℝ)) (momC Nv (∑ i, ‖velPi v i‖) 0) B hB
  obtain ⟨C₃, ε₃, -, hε₃, -, h3⟩ := stiff_main (m := Fin Nx) (p := Fin Nv) d hΔt.ne'
    (∑ i, ‖D i‖) ‖(Matrix.diagonal σ)⁻¹‖ ‖Matrix.diagonal σ‖ (Nv * ∑ i, ‖velPi v i‖) (√(Nv : ℝ))
    (momC Nv (∑ i, ‖velPi v i‖) 0) B hB
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro ε hε hεε X L hX hst1 hst2 hst3
  have hεε₁ : ε < ε₁ := hεε.trans_le (min_le_left _ _)
  have hεε₂ : ε < ε₂ := hεε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεε₃ : ε < ε₃ := hεε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (hεε₁.trans_le hε₁1).le
  have hV : (1 : Matrix (Fin Nv) (Fin Nv) ℝ)ᵀ * 1 = 1 := by simp
  have hdd : Δt / 2 / (d : ℝ) = Δt / (2 * d) := by rw [div_div]
  have hst1' : Stable (1 - (Δt / 2 / d) • limL X D σ) B := by rwa [hdd]
  have hst2' : Stable (1 - (-Δt / 2 / d) • limL X D σ) B := by
    rw [neg_div, neg_div, hdd]
    exact stable_neg hst2
  obtain ⟨Y₁, hY₁⟩ := exists_of_bound (fun Y F hs =>
    (h1 ε hε hεε₁ _ _ _ _ _ Y F (stiffHyp_L (D := D) hv hs₀ hσs hX) (stable_lift hX hst1') hs).1) L
  have hmid : ∀ A B : Matrix (Fin Nv) (Fin Nv) ℝ, (2 : ℝ)⁻¹ • ((2 : ℝ) • A - B + B) = A :=
    fun A B => by module
  obtain ⟨Y₂, hY₂⟩ := exists_of_bound (fun Y F hs =>
    (h2 ε hε hεε₂ _ _ _ _ _ Y F
      (stiffHyp_S (D := D) hv hs₀ hσs hX hV le_rfl hε.le hε1 (capture_one v ε))
      (stable_lift hX hst2') hs).1) ((2 : ℝ) • Y₁ - L)
  obtain ⟨K₃, hK₃⟩ := exists_of_bound (fun Y F hs =>
    (h3 ε hε hεε₃ _ _ _ _ _ Y F
      (stiffHyp_K (D := D) hv hσ hV le_rfl hε.le hε1 (capture_one v ε)) hst3 hs).1)
    (X * ((2 : ℝ) • Y₂ - ((2 : ℝ) • Y₁ - L)))
  refine ⟨(2 : ℝ) • Y₁ - L, (2 : ℝ) • Y₁ - L, (2 : ℝ) • Y₂ - ((2 : ℝ) • Y₁ - L), K₃,
    ⟨IsLStepCN.of_stiff hΔt.ne' (by rw [hmid]; exact hY₁), by simp, hV,
      IsSStepCN.of_stiff hΔt.ne' hV (by rw [hmid]; exact hY₂), IsKStep.of_stiff hΔt.ne' hV hK₃⟩,
    assumption1_one hv hr hε hε1⟩

/-- **Non-vacuity of the limit scheme.**  Under the stability hypotheses of `theorem_3_2` the limit
scheme (3.16), (3.20), (3.11) has a solution for every initial density. -/
theorem exists_IELimit {Nx r d : ℕ} {X : Matrix (Fin Nx) (Fin r) ℝ}
    {D : Fin d → Matrix (Fin Nx) (Fin Nx) ℝ} {σ : Fin Nx → ℝ} {Δt B : ℝ} (hΔt : Δt ≠ 0) (hB : 0 < B)
    (h1 : Stable (1 - (Δt / d) • limL X D σ) B) (h2 : Stable (1 + (Δt / d) • limL X D σ) B)
    (h3 : Stable (1 - (Δt / d) • limD D σ) B) (ρ : Matrix (Fin Nx) Unit ℝ) :
    ∃ ρ₁ ρ₂ ρ₃, IsIELimit X D σ Δt ρ ρ₁ ρ₂ ρ₃ := by
  have key : ∀ {T : Matrix (Fin Nx) (Fin Nx) ℝ}, Stable T B →
      ∀ y : Matrix (Fin Nx) Unit ℝ, ∃ x : Matrix (Fin Nx) Unit ℝ, T * x = y := by
    intro T hT y
    have hU := isUnit_det_of_bddBelow T (s := B⁻¹) (inv_pos.mpr hB) fun x => by
      rw [inv_mul_le_iff₀ hB]
      exact hT x
    exact ⟨T⁻¹ * y, by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]⟩
  have hc : Δt⁻¹ * (Δt / d) = (d : ℝ)⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hΔt, one_mul]
  obtain ⟨ρ₁, e1⟩ := key h1 ρ
  obtain ⟨ρ₂, e2⟩ := key h2 ρ₁
  obtain ⟨ρ₃, e3⟩ := key h3 ρ₂
  refine ⟨ρ₁, ρ₂, ρ₃, ?_, ?_, ?_⟩
  · rw [← e1, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_sub_cancel, smul_smul, hc,
      sub_self]
  · rw [← e2, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, sub_add_cancel_left, smul_neg,
      smul_smul, hc, neg_add_cancel]
  · rw [← e3, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_sub_cancel, smul_smul, hc,
      sub_self]

end Converse

section Counterexample

/-- The central difference on two periodic points, up to scaling: the mesh of the counterexample
`theorem_3_2_counterexample`.  `D² = -1`. -/
def cxD : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ := fun _ => !![0, 1; -1, 0]

/-- The velocities `±1`. -/
def cxv : Fin 1 → Fin 2 → ℝ := fun _ => ![1, -1]

theorem cxD_skew (k : Fin 1) : (cxD k)ᵀ = -cxD k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxD]

theorem cxv_quadrature : IsQuadrature cxv where
  pos := by norm_num
  mean k := by simp [cxv, Fin.sum_univ_two]
  cov k l := by
    have h : k = l := Subsingleton.elim _ _
    subst h
    simp only [cxv, Fin.sum_univ_two]
    norm_num

private theorem cxD_sq : cxD 0 * cxD 0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cxPi_sq : velPi cxv 0 * velPi cxv 0 = 1 := by
  rw [velPi, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxv]

/-- The first unit vector. -/
def cxl : Matrix (Fin 2) Unit ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

private theorem norm_cxl : ‖cxl‖ = 1 := by
  have h : ‖cxl‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [cxl]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- `f = Π e_n`. -/
noncomputable def cxf : Matrix (Fin 2) Unit ℝ := velPi cxv 0 * eNorm 2

private theorem cxe_Pi : (eNorm 2)ᵀ * velPi cxv 0 = cxfᵀ := by
  rw [cxf, Matrix.transpose_mul, velPi, Matrix.diagonal_transpose]

private theorem cxf_Pi : cxfᵀ * velPi cxv 0 = (eNorm 2)ᵀ := by
  rw [← cxe_Pi, Matrix.mul_assoc, cxPi_sq, Matrix.mul_one]

private theorem cxf_e : cxfᵀ * eNorm 2 = 0 := by
  rw [← cxe_Pi, Matrix.mul_assoc]
  exact eNorm_moment1 cxv_quadrature 0

/-- The two-dimensional subspace on which the substeps act explicitly. -/
noncomputable def cxM (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  p • (cxl * (eNorm 2)ᵀ) + q • ((cxD 0 * cxl) * cxfᵀ)

private theorem cxM_mul_e (p q : ℝ) : cxM p q * eNorm 2 = p • cxl := by
  rw [cxM, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    eNorm_transpose_mul (by norm_num), cxf_e, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero]

private theorem cx_stiff (τ ε p q : ℝ) :
    IsStiffSolution cxD 1 (velPi cxv) (eNorm 2) τ ε (cxM p q)
      (cxM (p - τ / ε * q) (τ / ε * p + (1 + τ / ε ^ 2) * q)) := by
  have he : (eNorm 2)ᵀ * eNorm 2 = 1 := eNorm_transpose_mul (by norm_num)
  have hA : cxD 0 * (cxl * (eNorm 2)ᵀ) * velPi cxv 0 = (cxD 0 * cxl) * cxfᵀ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc, cxe_Pi]
  have hB : cxD 0 * ((cxD 0 * cxl) * cxfᵀ) * velPi cxv 0 = -(cxl * (eNorm 2)ᵀ) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc, cxf_Pi, ← Matrix.mul_assoc (cxD 0), cxD_sq]
    simp
  have hT : transport cxD (velPi cxv) (cxM p q) =
      p • ((cxD 0 * cxl) * cxfᵀ) - q • (cxl * (eNorm 2)ᵀ) := by
    simp only [transport, Fin.sum_univ_one]
    rw [cxM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hA, hB, smul_neg, sub_eq_add_neg]
  have hP : 1 * cxM p q * (1 - eNorm 2 * (eNorm 2)ᵀ) = q • ((cxD 0 * cxl) * cxfᵀ) := by
    have e1 : (cxl * (eNorm 2)ᵀ) * (eNorm 2 * (eNorm 2)ᵀ) = cxl * (eNorm 2)ᵀ := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc cxl, he, Matrix.mul_one]
    have e2 : ((cxD 0 * cxl) * cxfᵀ) * (eNorm 2 * (eNorm 2)ᵀ) = 0 := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (cxD 0 * cxl), cxf_e, Matrix.mul_zero,
        Matrix.zero_mul]
    rw [Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, cxM, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, e1, e2]
    module
  rw [IsStiffSolution, hT, hP, cxM, cxM]
  module

private theorem AD_one : AD (1 : Matrix (Fin 2) (Fin 2) ℝ) cxD = cxD := by
  funext k
  simp [AD]

private theorem Asig_one' : Asig (1 : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 1) = 1 := by
  simp [Asig]

private theorem Xi_one : Xi cxv (1 : Matrix (Fin 2) (Fin 2) ℝ) = velPi cxv := by
  funext k
  simp [Xi]

private theorem alpha_one : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * eNorm 2 = eNorm 2 := by
  simp

private theorem cx_hr : (1 + 1 : ℕ) ≤ 2 := le_refl _

/-- **Theorem 3.2 of arXiv 1907.04247 needs `I + (Δt / d) 𝓛` to be invertible, and it is not
implied by the hypotheses of the paper.**  Take `d = 1`, two space points with the skew matrix
`cxD`, `D² = -1`, velocities `±1`, `σ = 1`, `Δt = 1`, `X = V = 1`, so that `r = N_v = 2` and
Assumption 1 holds exactly.  Then `I + (Δt / d) 𝓛 = 0`, the implicit Euler step exists for all
`ε > 0` from a fixed rank-one `u^n`, and `u^{n+1}` blows up like `ε⁻²`: for every `ρ` and `C`, the
estimate `‖u^{n+1} - ρ eᵀ‖ ≤ C ε` fails for arbitrarily small `ε`.

So the paper's statement needs a restriction on `Δt`; here `Δt = d / λ` for the eigenvalue
`-λ = -1` of `𝓛`, and its (3.26) takes the inverse for granted.  `cxD` is skew like a central
difference but is not a difference stencil of a two-point grid; the paper leaves `D_k` open ("the
discrete approximation of `∂ₓ`").  That every mesh fails at every `Δt = d / λ` is not claimed. -/
theorem theorem_3_2_counterexample :
    (∀ B, ¬ Stable (1 + ((1 : ℝ) / ((1 : ℕ) : ℝ)) •
      limL (1 : Matrix (Fin 2) (Fin 2) ℝ) cxD (fun _ => 1)) B) ∧
    ∀ (ρ : Matrix (Fin 2) Unit ℝ) (C ε₀ : ℝ), 0 < ε₀ → ∃ ε, 0 < ε ∧ ε < ε₀ ∧
      ∃ L₁ S₁ S₂ K₃, IsIEStep cxD (fun _ => 1) cxv 1 ε 1 (cxM 1 0) L₁ S₁ 1 S₂ K₃ ∧
        Assumption1 cxv cx_hr ε 0 1 ∧
        C * ε < ‖K₃ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - ρ * (eOne 2)ᵀ‖ := by
  constructor
  · intro B h
    have e : limL (1 : Matrix (Fin 2) (Fin 2) ℝ) cxD (fun _ => 1) = -1 := by
      simp only [limL, Fin.sum_univ_one, Asig_one', AD_one]
      simp [cxD_sq]
    have h1 := h cxl
    rw [e] at h1
    have h2 : (1 + ((1 : ℝ) / ((1 : ℕ) : ℝ)) • (-1 : Matrix (Fin 2) (Fin 2) ℝ)) * cxl = 0 := by
      simp
    rw [h2, norm_zero, mul_zero, norm_cxl] at h1
    exact absurd h1 (by norm_num)
  · intro ρ C ε₀ hε₀
    obtain ⟨A, hA⟩ : ∃ A, A = ‖ρ * (eOne 2)ᵀ‖ + |C| + 1 := ⟨_, rfl⟩
    have hA1 : 1 ≤ A := by
      rw [hA]
      have := abs_nonneg C
      have := norm_nonneg (ρ * (eOne 2)ᵀ)
      linarith
    obtain ⟨ε, hε⟩ : ∃ ε, ε = min (ε₀ / 2) (1 / (12 * A)) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
    have hεlt : ε < ε₀ := by
      calc ε ≤ ε₀ / 2 := by rw [hε]; exact min_le_left _ _
        _ < ε₀ := by linarith
    have hεA : ε ≤ 1 / (12 * A) := by rw [hε]; exact min_le_right _ _
    have hεA' : 12 * A * ε ≤ 1 := by
      have := (le_div_iff₀ (by positivity : 0 < 12 * A)).mp hεA
      linarith
    have hε12 : ε ≤ 1 / 12 := by nlinarith
    obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = (ε ^ 2 + 1) / (ε ^ 2 + 2) := ⟨_, rfl⟩
    obtain ⟨q₁, hq₁⟩ : ∃ q₁, q₁ = -ε / (ε ^ 2 + 2) := ⟨_, rfl⟩
    obtain ⟨q₂, hq₂⟩ : ∃ q₂, q₂ = q₁ + p₁ / ε := ⟨_, rfl⟩
    obtain ⟨p₂, hp₂⟩ : ∃ p₂, p₂ = p₁ - q₂ / ε := ⟨_, rfl⟩
    obtain ⟨q₃, hq₃⟩ : ∃ q₃, q₃ = ε ^ 2 * (q₂ - p₂ / ε) / (ε ^ 2 + 2) := ⟨_, rfl⟩
    obtain ⟨p₃, hp₃⟩ : ∃ p₃, p₃ = p₂ + q₃ / ε := ⟨_, rfl⟩
    have hψ : ε ^ 2 + 2 ≠ 0 := by positivity
    have hε' : ε ≠ 0 := hε0.ne'
    have h11 : p₁ - 1 / ε * q₁ = 1 := by rw [hp₁, hq₁]; field_simp; ring
    have h12 : 1 / ε * p₁ + (1 + 1 / ε ^ 2) * q₁ = 0 := by rw [hp₁, hq₁]; field_simp; ring
    have h21 : p₂ - (-1) / ε * q₂ = p₁ := by rw [hp₂]; field_simp; ring
    have h22 : (-1) / ε * p₂ + (1 + (-1) / ε ^ 2) * q₂ = q₁ := by
      rw [hp₂, hq₂]; field_simp; ring
    have h31 : p₃ - 1 / ε * q₃ = p₂ := by rw [hp₃]; field_simp; ring
    have h32 : 1 / ε * p₃ + (1 + 1 / ε ^ 2) * q₃ = q₂ := by
      rw [hp₃, hq₃]; field_simp; ring
    have hclosed : p₃ = (ε ^ 2 * (ε ^ 2 + 1) ^ 2 - 1) / (ε ^ 2 * (ε ^ 2 + 2) ^ 2) := by
      rw [hp₃, hq₃, hp₂, hq₂, hp₁, hq₁]
      field_simp
      ring
    have hV : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp
    have hd1 : Matrix.diagonal (fun _ : Fin 2 => (1 : ℝ)) = 1 := Matrix.diagonal_one
    refine ⟨ε, hε0, hεlt, cxM p₁ q₁, cxM p₁ q₁, cxM p₂ q₂, cxM p₃ q₃, ⟨?_, by simp, hV, ?_, ?_⟩,
      assumption1_one cxv_quadrature cx_hr hε0 (by linarith), ?_⟩
    · refine IsLStepIE.of_stiff one_ne_zero ?_
      rw [AD_one, Asig_one']
      have h := cx_stiff 1 ε p₁ q₁
      rwa [h11, h12] at h
    · refine IsSStepIE.of_stiff one_ne_zero hV ?_
      rw [AD_one, Asig_one', Xi_one, alpha_one]
      have h := cx_stiff (-1) ε p₂ q₂
      rwa [h21, h22] at h
    · refine IsKStep.of_stiff one_ne_zero hV ?_
      rw [Xi_one, alpha_one, Matrix.one_mul, hd1]
      have h := cx_stiff 1 ε p₃ q₃
      rwa [h31, h32] at h
    · -- the blow-up
      have hsq : ε ^ 2 ≤ 1 / 144 := by nlinarith
      have hε2 : 0 < ε ^ 2 := by positivity
      have hnum : ε ^ 2 * (ε ^ 2 + 1) ^ 2 - 1 ≤ -(1 / 2) := by nlinarith
      have hden : ε ^ 2 * (ε ^ 2 + 2) ^ 2 ≤ 6 * ε ^ 2 := by
        have h7 : (ε ^ 2 + 2) ^ 2 ≤ 6 := by nlinarith
        calc ε ^ 2 * (ε ^ 2 + 2) ^ 2 ≤ ε ^ 2 * 6 := by gcongr
          _ = _ := by ring
      have hden0 : 0 < ε ^ 2 * (ε ^ 2 + 2) ^ 2 := by positivity
      have hp3 : p₃ ≤ -(1 / (12 * ε ^ 2)) := by
        rw [hclosed, div_le_iff₀ hden0, neg_mul, div_mul_eq_mul_div, one_mul,
          le_neg, div_le_iff₀ (by positivity)]
        nlinarith
      have hp4 : A ≤ |p₃| := by
        have h1 : 1 / (12 * ε ^ 2) ≤ -p₃ := by linarith
        have h2 : A ≤ 1 / (12 * ε ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        exact (h2.trans h1).trans (neg_le_abs p₃)
      have hK : |p₃| ≤ ‖cxM p₃ q₃‖ := by
        have h1 : ‖cxM p₃ q₃ * eNorm 2‖ = |p₃| := by
          rw [cxM_mul_e, norm_smul, norm_cxl, mul_one, Real.norm_eq_abs]
        rw [← h1]
        refine (Frobenius.norm_mul_le _ _).trans ?_
        rw [norm_eNorm (by norm_num), mul_one]
      have h5 : ‖cxM p₃ q₃‖ - ‖ρ * (eOne 2)ᵀ‖ ≤
          ‖cxM p₃ q₃ * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - ρ * (eOne 2)ᵀ‖ := by
        rw [Matrix.transpose_one, Matrix.mul_one]
        exact norm_sub_norm_le _ _
      have h6 : C * ε ≤ |C| := by
        have h7 : ε ≤ 1 := by linarith
        calc C * ε ≤ |C| * ε := by gcongr; exact le_abs_self C
          _ ≤ |C| * 1 := by gcongr
          _ = _ := mul_one _
      rw [hA] at hp4
      linarith

/-- **Non-vacuity of `lemma_B1`.**  For all `Δt, ε > 0` the mesh of `cxD` with velocities `±1`
carries data satisfying all hypotheses of Lemma B.1 with `B₀ = 1 + Δt`, `BH = 1`. -/
theorem lemma_B1_hypotheses {Δt ε : ℝ} (hΔt : 0 < Δt) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (X S V Km K Lp Sp Vp : Matrix (Fin 2) (Fin 2) ℝ),
      Xᵀ * X = 1 ∧ Vᵀ * V = 1 ∧ Assumption1 cxv cx_hr ε 0 V ∧
      IsKStep cxD (fun _ => 1) cxv Δt ε V Km K ∧ ‖Km‖ ≤ 1 + Δt ∧ K = X * S ∧
      (Hmat cxD (K * (Vᵀ * eNorm 2))).det ≠ 0 ∧ ‖(Hmat cxD (K * (Vᵀ * eNorm 2)))⁻¹‖ ≤ 1 ∧
      IsLStepCN cxD (fun _ => 1) cxv Δt ε X (S * Vᵀ) Lp ∧ Lp = Sp * Vpᵀ ∧ Vpᵀ * Vp = 1 := by
  have hV : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = 1 := by simp
  have hd1 : Matrix.diagonal (fun _ : Fin 2 => (1 : ℝ)) = 1 := Matrix.diagonal_one
  obtain ⟨q, hq⟩ : ∃ q, q = -(ε * Δt) / (ε ^ 2 + Δt) := ⟨_, rfl⟩
  have hψ : ε ^ 2 + Δt ≠ 0 := by positivity
  have hε' : ε ≠ 0 := hε.ne'
  obtain ⟨P, hP⟩ : ∃ P, P = 1 + Δt ^ 2 / (ε ^ 2 + Δt) := ⟨_, rfl⟩
  have h1 : 1 - Δt / ε * q = P := by rw [hq, hP]; field_simp; ring
  have h2 : Δt / ε * 1 + (1 + Δt / ε ^ 2) * q = 0 := by rw [hq]; field_simp; ring
  have hKs : IsKStep cxD (fun _ => 1) cxv Δt ε 1 (cxM P 0) (cxM 1 q) := by
    refine IsKStep.of_stiff hΔt.ne' hV ?_
    rw [Xi_one, alpha_one, hd1]
    have h := cx_stiff Δt ε 1 q
    rwa [h1, h2] at h
  have hPb : ‖cxM P 0‖ ≤ 1 + Δt := by
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    have h3 : P ≤ 1 + Δt := by
      rw [hP]
      have h4 : Δt ^ 2 / (ε ^ 2 + Δt) ≤ Δt := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ε]
      linarith
    have h5 : ‖cxl * (eNorm 2)ᵀ‖ ≤ 1 := by
      refine (Frobenius.norm_mul_le _ _).trans ?_
      rw [Frobenius.norm_transpose, norm_cxl, norm_eNorm (by norm_num), one_mul]
    rw [cxM, zero_smul, add_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hP0]
    calc P * ‖cxl * (eNorm 2)ᵀ‖ ≤ P * 1 := by gcongr
      _ ≤ _ := by linarith
  have hk : cxM 1 q * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * eNorm 2) = cxl := by
    rw [alpha_one, cxM_mul_e, one_smul]
  have hH : Hmat cxD cxl = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp [Hmat, dirMat, colsOf, Matrix.mul_apply, Fin.sum_univ_two, cxD, cxl]
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Δt / 2 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ', Δ' = 1 + τ / ε ^ 2 + τ ^ 2 / ε ^ 2 := ⟨_, rfl⟩
  have hΔ'0 : Δ' ≠ 0 := by rw [hΔ']; positivity
  obtain ⟨q', hq'⟩ : ∃ q', q' = (q - τ / ε) / Δ' := ⟨_, rfl⟩
  obtain ⟨p', hp'⟩ : ∃ p', p' = 1 + τ / ε * q' := ⟨_, rfl⟩
  have h3 : p' - τ / ε * q' = 1 := by rw [hp']; ring
  have h4 : τ / ε * p' + (1 + τ / ε ^ 2) * q' = q := by
    have e : τ / ε * p' + (1 + τ / ε ^ 2) * q' = τ / ε + q' * Δ' := by
      rw [hp', hΔ']; field_simp; ring
    rw [e, hq', div_mul_cancel₀ _ hΔ'0]
    ring
  have hmid : (2 : ℝ)⁻¹ • ((2 : ℝ) • cxM p' q' - cxM 1 q + cxM 1 q) = cxM p' q' := by module
  refine ⟨1, cxM 1 q, 1, cxM P 0, cxM 1 q, (2 : ℝ) • cxM p' q' - cxM 1 q,
    (2 : ℝ) • cxM p' q' - cxM 1 q, 1, hV, hV, ?_, hKs, hPb, by simp, ?_, ?_, ?_, by simp, hV⟩
  · exact assumption1_one cxv_quadrature cx_hr hε hε1
  · rw [hk, hH]
    simp
  · rw [hk, hH, inv_one]
    have h5 := norm_of_orthonormal (V := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (by simp)
    simp only [Fintype.card_fin, Nat.cast_one, Real.sqrt_one] at h5
    exact h5.le
  · refine IsLStepCN.of_stiff hΔt.ne' ?_
    rw [AD_one, Asig_one', Matrix.transpose_one, Matrix.mul_one, hmid, ← hτ]
    have h := cx_stiff τ ε p' q'
    rwa [h3, h4] at h

end Counterexample

end LeanDLRA.Literature.P1907_04247
