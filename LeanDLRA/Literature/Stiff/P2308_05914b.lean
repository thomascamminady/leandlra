import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2308.05914: Semi-implicit DLR discontinuous Galerkin for emission/absorption

Formalizes **Lemma 4.11** (Yin, Endeve, Hauck, Schnake, arXiv 2308.05914) in matrix form, as
`lemma_4_11_chi_alignment`.

Setting. The paper's weighted Frobenius norm `‖W‖²_M = (WM, W)_F = tr(W M Wᵀ)` (Definition 3.2)
is `wNormSq`, and its root is `wNorm`. The `Aχ`-projector `P_Eχ = E (Eᵀ Aχ E)⁻¹ Eᵀ` of (4.32)
is `chiProj`. The rows `(E^Eq)ᵀ ∈ R^{1×n}` are `Matrix (Fin 1) (Fin n) ℝ`.

Statement. For every `α ∈ (0,1)` there is `γ* ∈ (α,1)`, given explicitly by
`γ* = 1 - (1-α)² χmin / (8 χmax)`, which depends only on `χmax/χmin` and `α`. For every `n`, `r`,
SPD `A1`, `Aχ`, and every `E ∈ R^{n×r}` with `Eᵀ A1 E = I_r`, and every row `X = (E^Eq)ᵀ` with
`X A1 Xᵀ = 1`: if `‖X A1 E Eᵀ‖_{A1} ≥ γ*` then `‖X Aχ P_Eχ‖_{A1} ≥ α`.

Hypotheses taken from the paper.
* `Aχ` is SPD.
* `hRay` is the Rayleigh form of the paper's (C.2) for rows, `χmin ‖W‖²_{A1} ≤ ‖W‖²_{Aχ} ≤
  χmax ‖W‖²_{A1}`. It is the `m₁ = 1` case of (C.2), which follows from Assumption 2.1
  (`0 < χmin ≤ χ ≤ χmax`) through the definition of `Aχ` as a weighted Gram matrix. That
  derivation needs the DG basis and is not formalized here, so it is an input.
* `X A1 Xᵀ = 1` is the normalization (4.23) of `E^Eq`.

Proof. The paper proves the lemma through its Lemma C.5 and a Young-inequality bound. Here
`X Aχ P_Eχ = R1 + W` with `R1 = X A1 E Eᵀ` and `W = (X - R1) Aχ P_Eχ`. The proof bounds
`‖W‖²_{A1} ≤ (χmax/χmin)(1 - ‖R1‖²_{A1})` using that `P_Eχ Aχ` is an `Aχ`-orthogonal projector,
and then applies Cauchy–Schwarz to `‖R1 + W‖_{A1}`. No appendix lemma is needed.

Core definitions. The file imports `LeanDLRA.Integrators.BUG` and `LeanDLRA.Matrix.Projectors`. The
core has no weighted Frobenius norm and no `Aχ`-projector, so `wNormSq`, `wNorm` and `chiProj` are
defined locally. No core definition is duplicated.

Left out.
* **Theorem 4.12** (multi-step geometric convergence). Its induction uses the one-step estimate
  (Theorem 4.10) and the projection bounds (Lemmas 4.6–4.8). These depend on the DG operators of
  Sections 2–4, which are not in the library, so this module neither states nor proves it.
* The norm equivalence (C.2) from Assumption 2.1, as noted above.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2308_05914

variable {n r ℓ : ℕ}

/-- The `M`-weighted squared Frobenius norm `‖W‖²_M = tr(W M Wᵀ)` (paper Definition 3.2). -/
noncomputable def wNormSq (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin ℓ) (Fin n) ℝ) : ℝ :=
  (W * M * Wᵀ).trace

/-- The `M`-weighted Frobenius norm `‖W‖_M` (paper Definition 3.2). -/
noncomputable def wNorm (M : Matrix (Fin n) (Fin n) ℝ) (W : Matrix (Fin ℓ) (Fin n) ℝ) : ℝ :=
  Real.sqrt (wNormSq M W)

/-- The projector `P_Eχ = E (Eᵀ Aχ E)⁻¹ Eᵀ` of paper (4.32). -/
noncomputable def chiProj (Aχ : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin r) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  E * (Eᵀ * Aχ * E)⁻¹ * Eᵀ

lemma trace_swap {M : Matrix (Fin n) (Fin n) ℝ} (hMs : Mᵀ = M) (X Y : Matrix (Fin ℓ) (Fin n) ℝ) :
    (Y * M * Xᵀ).trace = (X * M * Yᵀ).trace := by
  rw [← Matrix.trace_transpose]
  simp [Matrix.transpose_mul, Matrix.mul_assoc, hMs]

lemma wNormSq_nonneg {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (W : Matrix (Fin ℓ) (Fin n) ℝ) : 0 ≤ wNormSq M W := by
  have h := (hM.mul_mul_conjTranspose_same W).trace_nonneg
  simpa [wNormSq, Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- Cauchy–Schwarz for the `M`-weighted inner product on rows. -/
lemma cs_trace {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) (X Y : Matrix (Fin ℓ) (Fin n) ℝ) :
    ((X * M * Yᵀ).trace) ^ 2 ≤ wNormSq M X * wNormSq M Y := by
  have hMs : Mᵀ = M := by
    have := hM.1.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have key : ∀ t : ℝ, 0 ≤ wNormSq M Y * (t * t) + (-2 * (X * M * Yᵀ).trace) * t + wNormSq M X := by
    intro t
    have h0 := wNormSq_nonneg hM (X - t • Y)
    have hexp : wNormSq M (X - t • Y)
        = wNormSq M X - 2 * t * (X * M * Yᵀ).trace + t * t * wNormSq M Y := by
      have hs := trace_swap hMs X Y
      unfold wNormSq at hs ⊢
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.transpose_sub, Matrix.transpose_smul, Matrix.trace_sub, Matrix.trace_smul,
        smul_eq_mul]
      rw [hs]
      ring
    rw [hexp] at h0
    linarith [h0, mul_comm (wNormSq M Y) (t * t)]
  have hd := discrim_le_zero (a := wNormSq M Y) (b := -2 * (X * M * Yᵀ).trace)
    (c := wNormSq M X) key
  unfold discrim at hd
  have h4 : (-2 * (X * M * Yᵀ).trace) ^ 2 = 4 * ((X * M * Yᵀ).trace) ^ 2 := by ring
  linarith [hd, h4]

/-- Lemma 4.11 of arXiv 2308.05914 (matrix form). For `α ∈ (0,1)` there is `γ* ∈ (α,1)`,
depending only on `χmax/χmin` and `α`, such that: if `Eᵀ A1 E = I`, `X A1 Xᵀ = 1` and
`‖X A1 E Eᵀ‖_{A1} ≥ γ*`, then `‖X Aχ P_Eχ‖_{A1} ≥ α`. Here `A1`, `Aχ` are SPD, `hRay` is the
Rayleigh form (C.2) of Assumption 2.1 (see the module docstring), and `γ*` is explicit. -/
theorem lemma_4_11_chi_alignment (χmin χmax α : ℝ) (hmin : 0 < χmin) (hle : χmin ≤ χmax)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γs : ℝ, α < γs ∧ γs < 1 ∧
      ∀ (A1 Aχ : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin r) ℝ)
        (X : Matrix (Fin 1) (Fin n) ℝ),
        A1.PosDef → Aχ.PosDef →
        (∀ W : Matrix (Fin 1) (Fin n) ℝ,
          χmin * wNormSq A1 W ≤ wNormSq Aχ W ∧ wNormSq Aχ W ≤ χmax * wNormSq A1 W) →
        Eᵀ * A1 * E = 1 → wNormSq A1 X = 1 →
        γs ≤ wNorm A1 (X * A1 * E * Eᵀ) →
        α ≤ wNorm A1 (X * Aχ * chiProj Aχ E) := by
  have hχmax : 0 < χmax := lt_of_lt_of_le hmin hle
  have hd0 : 0 < (1 - α) ^ 2 * χmin / (8 * χmax) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hdle : (1 - α) ^ 2 * χmin / (8 * χmax) < 1 - α := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : (1 - α) ^ 2 ≤ 1 - α := by nlinarith
    have h2 : (1 - α) ^ 2 * χmin ≤ (1 - α) * χmax := by
      have h0 : 0 < 1 - α := by linarith
      exact le_trans (mul_le_mul_of_nonneg_right h1 hmin.le)
        (mul_le_mul_of_nonneg_left hle h0.le)
    nlinarith
  refine ⟨1 - (1 - α) ^ 2 * χmin / (8 * χmax), by linarith, by linarith, ?_⟩
  intro A1 Aχ E X hA1 hAχ hRay hE hX hγ
  -- the abbreviation d = (1-α)² χmin / (8 χmax) and its basic bounds
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (1 - α) ^ 2 * χmin / (8 * χmax) := ⟨_, rfl⟩
  rw [← hd] at hd0 hdle hγ
  have hd8 : d * (8 * χmax) = (1 - α) ^ 2 * χmin := by
    rw [hd]; field_simp
  have hd_small : 8 * d ≤ 1 - α := by
    have h1 : (1 - α) ^ 2 ≤ 1 - α := by nlinarith
    have h2 : (1 - α) ^ 2 * χmin ≤ (1 - α) * χmax := by
      have h0 : 0 < 1 - α := by linarith
      exact le_trans (mul_le_mul_of_nonneg_right h1 hmin.le)
        (mul_le_mul_of_nonneg_left hle h0.le)
    nlinarith
  -- symmetry and definiteness
  have hA1s : A1ᵀ = A1 := by
    have := hA1.1.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hAs : Aχᵀ = Aχ := by
    have := hAχ.1.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hA1psd : A1.PosSemidef := hA1.posSemidef
  have hinj : Function.Injective (E.mulVec) := by
    have key : ∀ u : Fin r → ℝ, Eᵀ *ᵥ (A1 *ᵥ (E *ᵥ u)) = u := by
      intro u
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
    intro u v huv
    calc u = Eᵀ *ᵥ (A1 *ᵥ (E *ᵥ u)) := (key u).symm
      _ = Eᵀ *ᵥ (A1 *ᵥ (E *ᵥ v)) := by rw [huv]
      _ = v := key v
  have hBpos : (Eᵀ * Aχ * E).PosDef := by
    have h := Matrix.PosDef.conjTranspose_mul_mul_same hAχ hinj
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hBu : IsUnit (Eᵀ * Aχ * E).det := (Matrix.isUnit_iff_isUnit_det _).mp hBpos.isUnit
  have hBB : (Eᵀ * Aχ * E) * (Eᵀ * Aχ * E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have hBB' : (Eᵀ * Aχ * E)⁻¹ * (Eᵀ * Aχ * E) = 1 := Matrix.nonsing_inv_mul _ hBu
  have hBs : (Eᵀ * Aχ * E)ᵀ = Eᵀ * Aχ * E := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, hAs]
  -- projector identities
  have hPs : (chiProj Aχ E)ᵀ = chiProj Aχ E := by
    unfold chiProj
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hBs]
    simp only [Matrix.mul_assoc]
  have hPAP : chiProj Aχ E * Aχ * chiProj Aχ E = chiProj Aχ E := by
    have e : chiProj Aχ E * Aχ * chiProj Aχ E
        = E * ((Eᵀ * Aχ * E)⁻¹ * (Eᵀ * Aχ * E) * (Eᵀ * Aχ * E)⁻¹) * Eᵀ := by
      unfold chiProj
      simp only [Matrix.mul_assoc]
    rw [e, hBB']
    simp only [Matrix.one_mul, Matrix.mul_assoc, chiProj]
  -- the row R1 = X A1 E Eᵀ and the splitting X = R1 + R2
  set R1 : Matrix (Fin 1) (Fin n) ℝ := X * A1 * E * Eᵀ with hR1def
  set R2 : Matrix (Fin 1) (Fin n) ℝ := X - R1 with hR2def
  set P : Matrix (Fin n) (Fin n) ℝ := chiProj Aχ E with hPdef
  set W : Matrix (Fin 1) (Fin n) ℝ := R2 * Aχ * P with hWdef
  have hR1P : R1 * Aχ * P = R1 := by
    have e : R1 * Aχ * P = (X * A1 * E) * ((Eᵀ * Aχ * E) * (Eᵀ * Aχ * E)⁻¹) * Eᵀ := by
      rw [hR1def, hPdef, chiProj]
      simp only [Matrix.mul_assoc]
    rw [e, hBB, Matrix.mul_one]
  have hXsplit : X * Aχ * P = R1 + W := by
    have hX' : X = R1 + R2 := by rw [hR2def]; abel
    calc X * Aχ * P = (R1 + R2) * Aχ * P := by rw [← hX']
      _ = R1 * Aχ * P + R2 * Aχ * P := by simp only [Matrix.add_mul]
      _ = R1 + W := by rw [hR1P]
  -- the quantities of the proof
  have hM1 : X * A1 * R1ᵀ = (X * A1 * E) * (Eᵀ * A1 * X ᵀ) := by
    rw [hR1def]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA1s, Matrix.mul_assoc]
  have hM2 : R1 * A1 * R1ᵀ = (X * A1 * E) * (Eᵀ * A1 * X ᵀ) := by
    have e : R1 * A1 * R1ᵀ = (X * A1 * E) * (Eᵀ * A1 * E) * (Eᵀ * A1 * Xᵀ) := by
      rw [hR1def]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA1s, Matrix.mul_assoc]
    rw [e, hE, Matrix.mul_one]
  have hq1nn : 0 ≤ wNormSq A1 R1 := wNormSq_nonneg hA1psd R1
  have hq2 : wNormSq A1 R2 = 1 - wNormSq A1 R1 := by
    have hs := trace_swap hA1s X R1
    have hM1t : (X * A1 * R1ᵀ).trace = (R1 * A1 * R1ᵀ).trace := by rw [hM1, hM2]
    unfold wNormSq at hX ⊢
    rw [hR2def]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.trace_sub]
    linarith
  have hq2nn : 0 ≤ wNormSq A1 R2 := wNormSq_nonneg hA1psd R2
  have hPt : Pᵀ = P := hPs
  have hPP : P * Aχ * P = P := hPAP
  have hWt : Wᵀ = P * Aχ * R2ᵀ := by
    rw [hWdef]
    simp only [Matrix.transpose_mul, hAs, hPt, Matrix.mul_assoc]
  have hK1 : W * Aχ * Wᵀ = R2 * Aχ * P * Aχ * R2ᵀ := by
    have e : W * Aχ * Wᵀ = R2 * Aχ * (P * Aχ * P) * Aχ * R2ᵀ := by
      rw [hWt, hWdef]
      simp only [Matrix.mul_assoc]
    rw [e, hPP]
  have hK2 : R2 * Aχ * Wᵀ = R2 * Aχ * P * Aχ * R2ᵀ := by
    rw [hWt]
    simp only [Matrix.mul_assoc]
  have hWK : wNormSq Aχ W = (R2 * Aχ * P * Aχ * R2ᵀ).trace := by
    unfold wNormSq
    rw [hK1]
  -- projection step: ‖W‖_{Aχ} ≤ ‖R2‖_{Aχ}
  have hW1 : wNormSq Aχ W ≤ wNormSq Aχ R2 := by
    have hs2 := trace_swap hAs R2 W
    have hT := (hRay (R2 - W)).1
    have hT0 : 0 ≤ wNormSq A1 (R2 - W) := wNormSq_nonneg hA1psd _
    have hexp : wNormSq Aχ (R2 - W)
        = wNormSq Aχ R2 - 2 * (R2 * Aχ * P * Aχ * R2ᵀ).trace
          + (R2 * Aχ * P * Aχ * R2ᵀ).trace := by
      have h1' : (R2 * Aχ * Wᵀ).trace = (R2 * Aχ * P * Aχ * R2ᵀ).trace := by rw [hK2]
      have h2' : (W * Aχ * Wᵀ).trace = (R2 * Aχ * P * Aχ * R2ᵀ).trace := by rw [hK1]
      unfold wNormSq
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.trace_sub]
      linarith
    have hpos : 0 ≤ wNormSq Aχ (R2 - W) := le_trans (mul_nonneg hmin.le hT0) hT
    linarith
  have hW2 : wNormSq Aχ R2 ≤ χmax * wNormSq A1 R2 := (hRay R2).2
  have hW3 : χmin * wNormSq A1 W ≤ wNormSq Aχ W := (hRay W).1
  have hcs : (R1 * A1 * Wᵀ).trace ^ 2 ≤ wNormSq A1 R1 * wNormSq A1 W := cs_trace hA1psd R1 W
  have hZexp : wNormSq A1 (R1 + W)
      = wNormSq A1 R1 + 2 * (R1 * A1 * Wᵀ).trace + wNormSq A1 W := by
    have hs3 := trace_swap hA1s R1 W
    unfold wNormSq
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add, Matrix.trace_add]
    linarith
  -- the scalar estimate
  have hγg : 1 - d ≤ Real.sqrt (wNormSq A1 R1) := hγ
  have hg2 : (Real.sqrt (wNormSq A1 R1)) ^ 2 = wNormSq A1 R1 := Real.sq_sqrt hq1nn
  have hw2 : (Real.sqrt (wNormSq A1 W)) ^ 2 = wNormSq A1 W :=
    Real.sq_sqrt (wNormSq_nonneg hA1psd W)
  have hg0 : 0 ≤ Real.sqrt (wNormSq A1 R1) := Real.sqrt_nonneg _
  have hw0 : 0 ≤ Real.sqrt (wNormSq A1 W) := Real.sqrt_nonneg _
  set g := Real.sqrt (wNormSq A1 R1) with hgdef
  set w := Real.sqrt (wNormSq A1 W) with hwdef
  have hq1le : g ^ 2 ≤ 1 := by rw [hg2]; linarith
  have hg1 : g ≤ 1 := by nlinarith
  have hkey : χmax * (1 - g ^ 2) ≤ χmin * (g - α) ^ 2 := by
    have hA : 1 - g ^ 2 ≤ 2 * (1 - g) := by nlinarith
    have hB : 1 - g ≤ d := by linarith
    have hC : (1 - α) / 2 ≤ g - α := by linarith
    have hD : χmax * (1 - g ^ 2) ≤ χmax * (2 * d) :=
      mul_le_mul_of_nonneg_left (by linarith) hχmax.le
    have hE' : χmax * (2 * d) = (1 - α) ^ 2 * χmin / 4 := by
      linear_combination hd8 / 4
    have hF : (1 - α) ^ 2 / 4 ≤ (g - α) ^ 2 := by nlinarith
    have hG : χmin * ((1 - α) ^ 2 / 4) ≤ χmin * (g - α) ^ 2 :=
      mul_le_mul_of_nonneg_left hF hmin.le
    linarith
  have hchain : χmin * wNormSq A1 W ≤ χmax * (1 - g ^ 2) := by
    rw [hg2]
    rw [hq2] at hW2
    linarith
  have hqW : wNormSq A1 W ≤ (g - α) ^ 2 :=
    le_of_mul_le_mul_left (le_trans hchain hkey) hmin
  have hw_le : w ≤ g - α := by
    have h0 : 0 ≤ g - α := by linarith
    by_contra hcon
    have hcon' : g - α < w := not_le.mp hcon
    have h5 := mul_self_lt_mul_self h0 hcon'
    have e1 : w * w = w ^ 2 := (sq w).symm
    have e2 : (g - α) * (g - α) = (g - α) ^ 2 := (sq _).symm
    linarith
  have hc : -(g * w) ≤ (R1 * A1 * Wᵀ).trace := by
    have hcs' : (R1 * A1 * Wᵀ).trace ^ 2 ≤ (g * w) ^ 2 := by
      rw [mul_pow, hg2, hw2]; exact hcs
    exact (abs_le_of_sq_le_sq' hcs' (mul_nonneg hg0 hw0)).1
  have hsq : α ^ 2 ≤ wNormSq A1 (R1 + W) := by
    rw [hZexp, ← hg2, ← hw2]
    have hp := mul_nonneg (by linarith : (0:ℝ) ≤ g - w - α) (by linarith : (0:ℝ) ≤ g - w + α)
    have h6 : (g - w - α) * (g - w + α) = g ^ 2 - 2 * (g * w) + w ^ 2 - α ^ 2 := by ring
    linarith [hp, h6, hc]
  rw [hXsplit]
  unfold wNorm
  calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα0.le).symm
    _ ≤ Real.sqrt (wNormSq A1 (R1 + W)) := Real.sqrt_le_sqrt hsq

/-- Non-vacuity: the hypotheses of `lemma_4_11_chi_alignment` hold for `n = r = 1`, `A1 = 1`,
`Aχ = (3/2) · 1` (so `χmin = 1 ≤ 3/2 ≤ 2 = χmax`), `E = 1`, `X = 1`. -/
example : ∃ (A1 Aχ E X : Matrix (Fin 1) (Fin 1) ℝ), A1.PosDef ∧ Aχ.PosDef ∧
    (∀ W : Matrix (Fin 1) (Fin 1) ℝ,
      1 * wNormSq A1 W ≤ wNormSq Aχ W ∧ wNormSq Aχ W ≤ 2 * wNormSq A1 W) ∧
    Eᵀ * A1 * E = 1 ∧ wNormSq A1 X = 1 := by
  refine ⟨1, (3 / 2 : ℝ) • 1, 1, 1, Matrix.PosDef.one, ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosDef.one.smul (by norm_num)
  · intro W
    simp only [wNormSq, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_fin_one, smul_eq_mul]
    have h1 : (W * Wᵀ) 0 0 = W 0 0 * W 0 0 := by simp [Matrix.mul_apply]
    rw [h1]
    constructor <;> nlinarith [mul_self_nonneg (W 0 0)]
  · simp
  · simp [wNormSq]

end LeanDLRA.Literature.P2308_05914
