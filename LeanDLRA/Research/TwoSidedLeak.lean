import LeanDLRA.Research.AugmentationRank

/-!
# The rank-adaptive BUG step for fields with a two-sided term: a leak bound

## Setting

`F(Y) = 𝒜 Y + Y ℬ + C Y D` on `m × n` matrices with constant coefficients, one step of the
rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, arXiv:2104.05247;
`MatrixBUG.IsRankAdaptiveStep`) from `Y₀ = U₀ S₀ V₀ᵀ`.  For `C = 0` the Galerkin space of the
step contains the exact solution (`capture_of_sylvester`).  A two-sided term destroys this exact
capture unless `C` maps the range of `U₀` into itself and `D` maps the row space of `V₀` into
itself.  The amount by which it does not is measured by the *leaks*

* `‖(1 - U₀ U₀ᵀ) C U₀ S₀‖` and `‖S₀ V₀ᵀ D (1 - V₀ V₀ᵀ)‖` (weighted by the singular values), and
* `‖(1 - U₀ U₀ᵀ) C U₀‖`, `‖V₀ᵀ D (1 - V₀ V₀ᵀ)‖` (unweighted; only their product enters).

## Main results

* `kField_of_twoSided`: the K-step field is `𝒜 K + K (V₀ᵀ ℬ V₀) + C K (V₀ᵀ D V₀)`.
* `hasDerivWithinAt_kCurve_add_of_twoSided`: with the auxiliary flow `P` of the Sylvester case
  and a correction `Z`, the curve `W = K P + U₀ Z` solves `W' = F(W) + δ` with an explicit defect
  `δ = (1 - U₀ U₀ᵀ) C K (N P - P D) - 𝒜 U₀ Z - C U₀ Z D`, `N = V₀ᵀ D V₀`.
* `norm_sub_leftProj_le_of_twoSided`: the left capture defect of the step,
  `‖A(t₁) - Û Ûᵀ A(t₁)‖ ≤ h e^{L h} (ε₀ + h Γ₁ (ν_C + ν_D + ℓ_C ℓ_D) + h² Γ₂)`, where `ε₀` bounds
  the normal component of `F` at `Y₀`, `ν_C`, `ν_D` the weighted leaks and `ℓ_C`, `ℓ_D` the
  unweighted ones; `Γ₁`, `Γ₂` depend only on bounds of the coefficients, of `‖S₀‖` and of the
  first and second increments of the substep solutions.  No singular value enters.
* `norm_sub_rightProj_le_of_twoSided`: the same bound for the row side (by transposition).
* `error_le_of_twoSided`: the local error of the step,
  `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ` with `θ` twice the bound above.  So the
  step is of local order three (global order two) when the leaks are `O(h)` and the normal
  component vanishes at the start, and of local order two otherwise.

## Implementation notes

The auxiliary flows `P`, `Z` (row side: `Q`, `Zr`) are hypotheses, as in `capture_of_sylvester`;
their existence (linear equations with continuous coefficients) is not formalised.  The bounds
on the increments of the K- and L-step solutions are hypotheses as well.

## References

* Ceruti–Kusch–Lubich, arXiv:2104.05247 (rank-adaptive BUG integrator).
* Ceruti–Einkemmer–Kusch–Lubich, arXiv:2402.08607, Section 5.2 (a field with a two-sided term
  on which the rank-adaptive BUG integrator shows order two).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

section TwoSided

open MatrixBUG

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {r : ℕ}

/-! ### Contractions -/

private theorem norm_transpose_mul_le' {U : Matrix m (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (X : Matrix m p ℝ) : ‖Uᵀ * X‖ ≤ ‖X‖ := by
  rw [← Frobenius.norm_mul_of_orthonormal hU (Uᵀ * X), ← Matrix.mul_assoc]
  have h := (isOrthProj_leftProj (n := p) hU).norm_le X
  rwa [leftProj_apply] at h

private theorem norm_mul_le' {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix p n ℝ) : ‖X * V‖ ≤ ‖X‖ := by
  rw [← Frobenius.norm_transpose, Matrix.transpose_mul, ← Frobenius.norm_transpose X]
  exact norm_transpose_mul_le' hV Xᵀ

private theorem norm_one_sub_mul_le [DecidableEq m] {U : Matrix m (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (X : Matrix m p ℝ) : ‖(1 - U * Uᵀ) * X‖ ≤ ‖X‖ := by
  have h := (isOrthProj_leftProj (n := p) hU).compl.norm_le X
  have e : (1 - leftProj (n := p) U) X = (1 - U * Uᵀ) * X := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    rfl
  rwa [e] at h

private theorem norm_mul_one_sub_le [DecidableEq n] {V : Matrix n (Fin r) ℝ} (hV : Vᵀ * V = 1)
    (X : Matrix p n ℝ) : ‖X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  have h : (X * (1 - V * Vᵀ))ᵀ = (1 - V * Vᵀ) * Xᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  rw [← Frobenius.norm_transpose, h, ← Frobenius.norm_transpose X]
  exact norm_one_sub_mul_le hV Xᵀ

private theorem norm_mul_mul_le (X : Matrix m n ℝ) (Y : Matrix n p ℝ) {x y : ℝ}
    (hx : ‖X‖ ≤ x) (hy : ‖Y‖ ≤ y) : ‖X * Y‖ ≤ x * y :=
  (Frobenius.norm_mul_le X Y).trans
    (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {𝒜 C : Matrix m m ℝ} {ℬ D : Matrix n n ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {t₀ t₁ : ℝ}

/-! ### The comparison curve -/

/-- For a field with a two-sided term, `F(Y) = 𝒜 Y + Y ℬ + C Y D`, the K-step equation is
linear: `K' = 𝒜 K + K (V₀ᵀ ℬ V₀) + C K (V₀ᵀ D V₀)`. -/
theorem kField_of_twoSided (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D)
    (hV₀ : V₀ᵀ * V₀ = 1) (t : ℝ) (K : Matrix m (Fin r) ℝ) :
    kField V₀ F t K = 𝒜 * K + K * (V₀ᵀ * ℬ * V₀) + C * K * (V₀ᵀ * D * V₀) := by
  rw [kField, hFS]
  simp only [Matrix.add_mul, Matrix.mul_assoc, hV₀, Matrix.mul_one]

/-- **The defect of the comparison curve.**  Let `K` solve the K-step equation, `P` the linear
equation `P' = P ℬ - (V₀ᵀ ℬ V₀) P` of the Sylvester case, and `Z` the linear equation
`Z' = Z ℬ - U₀ᵀ C K (N P - P D)` with `N = V₀ᵀ D V₀`.  Then the curve `W = K P + U₀ Z` has the
derivative `F(W) + (1 - U₀ U₀ᵀ) C K (N P - P D) - 𝒜 U₀ Z - C U₀ Z D`.  For `C = 0` the defect
vanishes and `K P` is the exact solution (`odeSolution_kCurve`). -/
theorem hasDerivWithinAt_kCurve_add_of_twoSided [DecidableEq m]
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hV₀ : V₀ᵀ * V₀ = 1)
    {K : ℝ → Matrix m (Fin r) ℝ} (hK : ODESolution (kField V₀ F) K t₀ t₁)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁)
    {Z : ℝ → Matrix (Fin r) n ℝ}
    (hZ : ODESolution
      (fun t X => X * ℬ - U₀ᵀ * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))) Z t₀ t₁)
    {t : ℝ} (ht : t ∈ Ico t₀ t₁) :
    HasDerivWithinAt (fun s => K s * P s + U₀ * Z s)
      (F t (K t * P t + U₀ * Z t) + ((1 - U₀ * U₀ᵀ) * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))
        - 𝒜 * U₀ * Z t - C * U₀ * Z t * D)) (Ici t) t := by
  refine ((Frobenius.hasDerivWithinAt_mul (hK.deriv t ht) (hP.deriv t ht)).add
    (Frobenius.hasDerivWithinAt_const_mul U₀ (hZ.deriv t ht))).congr_deriv ?_
  simp only [hFS, kField_of_twoSided hFS hV₀, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The comparison curve is continuous. -/
private theorem continuousOn_kCurve_add {K : ℝ → Matrix m (Fin r) ℝ}
    {P : ℝ → Matrix (Fin r) n ℝ} {Z : ℝ → Matrix (Fin r) n ℝ} (hK : ContinuousOn K (Icc t₀ t₁))
    (hP : ContinuousOn P (Icc t₀ t₁)) (hZ : ContinuousOn Z (Icc t₀ t₁)) :
    ContinuousOn (fun s => K s * P s + U₀ * Z s) (Icc t₀ t₁) :=
  (((Frobenius.mulCLM (m := m) (l := Fin r) (n := n)).continuous.comp_continuousOn
    hK).clm_apply hP).add ((Frobenius.leftMulCLM U₀).continuous.comp_continuousOn hZ)

/-! ### Pointwise bounds of the defect -/

omit [Fintype n] in
/-- Splitting of the leaked part `(1 - U₀ U₀ᵀ) C K E` of the defect at one time, with
`τ = t - t₀`: the part through `U₀ S₀`, the part through `U₀ U₀ᵀ (K - U₀ S₀)`, the first-order part
`τ K₁` of the increment and its remainder. -/
private theorem leftDefect_split [DecidableEq m] (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (C : Matrix m m ℝ)
    (Kt K₁ : Matrix m (Fin r) ℝ) (E E₀ : Matrix (Fin r) n ℝ) (τ : ℝ) :
    (1 - U₀ * U₀ᵀ) * (C * Kt * E)
      = (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * E₀ + (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (E - E₀)
        + (1 - U₀ * U₀ᵀ) * C * U₀ * (U₀ᵀ * (Kt - U₀ * S₀)) * E₀
        + (1 - U₀ * U₀ᵀ) * C * U₀ * (U₀ᵀ * (Kt - U₀ * S₀)) * (E - E₀)
        + τ • ((1 - U₀ * U₀ᵀ) * C * ((1 - U₀ * U₀ᵀ) * K₁ * E₀))
        + τ • ((1 - U₀ * U₀ᵀ) * C * ((1 - U₀ * U₀ᵀ) * K₁ * (E - E₀)))
        + (1 - U₀ * U₀ᵀ) * C * ((1 - U₀ * U₀ᵀ) * (Kt - U₀ * S₀ - τ • K₁)) * E := by
  simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub]
  abel

/-- The leaked part of the defect of the comparison curve at time `t₀ + τ`: the normal
component `ε₀` at the start, terms of first order in `τ` proportional to the leaks, and terms of
higher order. -/
private theorem norm_leftDefect_le [DecidableEq m] {𝒜 C : Matrix m m ℝ} {D : Matrix n n ℝ}
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    {Kt K₁ : Matrix m (Fin r) ℝ} {E E₀ Zt : Matrix (Fin r) n ℝ}
    {τ h a c δ σ κ κ₂ π ζ ε₀ νC νD ℓC ℓD : ℝ} (hτ : 0 ≤ τ) (hτh : τ ≤ h)
    (h𝒜 : ‖𝒜‖ ≤ a) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ) (hκ : 0 ≤ κ)
    (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hK₁ : ‖Kt - U₀ * S₀‖ ≤ κ * τ) (hK₂ : ‖Kt - U₀ * S₀ - τ • K₁‖ ≤ κ₂ * τ ^ 2)
    (hE : ‖E - E₀‖ ≤ 2 * δ * π * τ) (hE₀δ : ‖E₀‖ ≤ δ) (hE₀ℓ : ‖E₀‖ ≤ ℓD)
    (hT1 : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * E₀‖ ≤ ε₀)
    (hKE : ‖(1 - U₀ * U₀ᵀ) * K₁ * E₀‖ ≤ a * νD + νC * δ ^ 2)
    (hKn : ‖(1 - U₀ * U₀ᵀ) * K₁‖ ≤ a * σ + c * σ * δ)
    (hνC : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ νC) (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC)
    (hZt : ‖Zt‖ ≤ ζ) :
    ‖(1 - U₀ * U₀ᵀ) * (C * Kt * E) - 𝒜 * U₀ * Zt - C * U₀ * Zt * D‖
      ≤ ε₀ + τ * ((2 * δ * π + c * δ ^ 2) * νC + c * a * νD + κ * (ℓC * ℓD))
        + τ * h * (2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ)
        + τ * h ^ 2 * (2 * c * κ₂ * δ * π) + (a + c * δ) * ζ := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hC
  have ha : 0 ≤ a := (norm_nonneg _).trans h𝒜
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hD
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have hνC0 : 0 ≤ νC := (norm_nonneg _).trans hνC
  have hℓD0 : 0 ≤ ℓD := (norm_nonneg _).trans hE₀ℓ
  have hPiC : ‖(1 - U₀ * U₀ᵀ) * C‖ ≤ c := (norm_one_sub_mul_le hU₀ C).trans hC
  have hPiCU : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ c := (norm_mul_le' hU₀ _).trans hPiC
  have hUK : ‖U₀ᵀ * (Kt - U₀ * S₀)‖ ≤ κ * τ := (norm_transpose_mul_le' hU₀ _).trans hK₁
  have hPiR : ‖(1 - U₀ * U₀ᵀ) * (Kt - U₀ * S₀ - τ • K₁)‖ ≤ κ₂ * τ ^ 2 :=
    (norm_one_sub_mul_le hU₀ _).trans hK₂
  have hEn : ‖E‖ ≤ δ + 2 * δ * π * τ := by
    have := norm_add_le E₀ (E - E₀)
    rw [add_sub_cancel] at this
    linarith
  -- the seven pieces
  have t1 := hT1
  have t2 := norm_mul_mul_le _ _ hνC hE
  have t3 := norm_mul_mul_le _ _ (norm_mul_mul_le _ _ hℓC hUK) hE₀ℓ
  have t3' := norm_mul_mul_le _ _ (norm_mul_mul_le _ _ hPiCU hUK) hE
  have t4 : ‖τ • ((1 - U₀ * U₀ᵀ) * C * ((1 - U₀ * U₀ᵀ) * K₁ * E₀))‖
      ≤ τ * (c * (a * νD + νC * δ ^ 2)) := by
    rw [norm_smul, Real.norm_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left (norm_mul_mul_le _ _ hPiC hKE) hτ
  have t5 : ‖τ • ((1 - U₀ * U₀ᵀ) * C * ((1 - U₀ * U₀ᵀ) * K₁ * (E - E₀)))‖
      ≤ τ * (c * ((a * σ + c * σ * δ) * (2 * δ * π * τ))) := by
    rw [norm_smul, Real.norm_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left (norm_mul_mul_le _ _ hPiC (norm_mul_mul_le _ _ hKn hE)) hτ
  have t6 := norm_mul_mul_le _ _ (norm_mul_mul_le _ _ hPiC hPiR) hEn
  have tz1 : ‖𝒜 * U₀ * Zt‖ ≤ a * ζ := by
    rw [Matrix.mul_assoc]
    exact norm_mul_mul_le _ _ h𝒜 (by rwa [Frobenius.norm_mul_of_orthonormal hU₀])
  have tz2 : ‖C * U₀ * Zt * D‖ ≤ c * ζ * δ := by
    refine norm_mul_mul_le _ _ ?_ hD
    rw [Matrix.mul_assoc]
    exact norm_mul_mul_le _ _ hC (by rwa [Frobenius.norm_mul_of_orthonormal hU₀])
  -- triangle inequality over the seven pieces and the two correction terms
  rw [leftDefect_split U₀ S₀ C Kt K₁ E E₀ τ]
  refine (norm_sub_le_of_le (norm_sub_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le t1 t2) t3) t3')
      t4) t5) t6) tz1) tz2).trans ?_
  -- the polynomial comparison, with `τ ≤ h`
  have hd2 : 0 ≤ τ * h - τ ^ 2 := by
    have := mul_nonneg hτ (sub_nonneg.2 hτh)
    linarith only [this]
  have hd3 : 0 ≤ τ * h ^ 2 - τ ^ 3 := by
    have := mul_nonneg (mul_nonneg hτ (sub_nonneg.2 hτh)) (add_nonneg (hτ.trans hτh) hτ)
    linarith only [this]
  have b1 := mul_nonneg (mul_nonneg (mul_nonneg hc hκ) (mul_nonneg hδ hπ)) hd2
  have b2 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc hδ) (mul_nonneg hπ hσ0))
    (add_nonneg ha (mul_nonneg hc hδ))) hd2
  have b3 := mul_nonneg (mul_nonneg (mul_nonneg hc hκ₂) hδ) hd2
  have b4 := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc hκ₂) hδ) hπ) hd3
  linarith only [b1, b2, b3, b4]

/-- The source of the correction `Z` at time `t₀ + τ`: the weighted leak of `D` plus terms of
first and second order. -/
private theorem norm_zSource_le {C : Matrix m m ℝ} {U₀ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) {Kt : Matrix m (Fin r) ℝ}
    {E E₀ : Matrix (Fin r) n ℝ} {τ h c δ σ κ π νD : ℝ} (hτ : 0 ≤ τ) (hτh : τ ≤ h)
    (hC : ‖C‖ ≤ c) (hσ : ‖S₀‖ ≤ σ) (hκ : 0 ≤ κ) (hπ : 0 ≤ π)
    (hK₁ : ‖Kt - U₀ * S₀‖ ≤ κ * τ) (hE : ‖E - E₀‖ ≤ 2 * δ * π * τ) (hE₀δ : ‖E₀‖ ≤ δ)
    (hSE : ‖S₀ * E₀‖ ≤ νD) :
    ‖U₀ᵀ * (C * Kt * E)‖
      ≤ c * νD + h * (2 * c * σ * δ * π + c * κ * δ) + h ^ 2 * (2 * c * κ * δ * π) := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hC
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hE₀δ
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have hUC : ‖U₀ᵀ * C‖ ≤ c := (norm_transpose_mul_le' hU₀ C).trans hC
  have hUCU : ‖U₀ᵀ * C * U₀‖ ≤ c := (norm_mul_le' hU₀ _).trans hUC
  have hEn : ‖E‖ ≤ δ + 2 * δ * π * τ := by
    have := norm_add_le E₀ (E - E₀)
    rw [add_sub_cancel] at this
    linarith
  have hsplit : U₀ᵀ * (C * Kt * E) = U₀ᵀ * C * U₀ * (S₀ * E₀)
      + U₀ᵀ * C * U₀ * S₀ * (E - E₀) + U₀ᵀ * C * (Kt - U₀ * S₀) * E := by
    simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hsplit]
  refine (norm_add_le_of_le (norm_add_le_of_le (norm_mul_mul_le _ _ hUCU hSE)
    (norm_mul_mul_le _ _ (norm_mul_mul_le _ _ hUCU hσ) hE))
    (norm_mul_mul_le _ _ (norm_mul_mul_le _ _ hUC hK₁) hEn)).trans ?_
  have hτ2 : τ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hτ hτh 2
  nlinarith [mul_le_mul_of_nonneg_left hτh (mul_nonneg (mul_nonneg (mul_nonneg hc hσ0) hδ) hπ),
    mul_le_mul_of_nonneg_left hτh (mul_nonneg (mul_nonneg hc hκ) hδ),
    mul_le_mul_of_nonneg_left hτ2 (mul_nonneg (mul_nonneg (mul_nonneg hc hκ) hδ) hπ)]

/-! ### The left capture defect -/

/-- **Left capture defect of the rank-adaptive BUG step for a field with a two-sided term.**
Let `F(Y) = 𝒜 Y + Y ℬ + C Y D` be `L`-Lipschitz, `A` the exact solution from
`Y₀ = U₀ S₀ V₀ᵀ`, `K` the K-step solution, and let `Û` (`Ua`) have orthonormal columns whose
range contains those of `U₀` and `K(t₁)`.  Let `P`, `Z` be the auxiliary flows of
`hasDerivWithinAt_kCurve_add_of_twoSided` with `P(t₀) = V₀ᵀ`, `Z(t₀) = 0`.  Then

    ‖A(t₁) - Û Ûᵀ A(t₁)‖ ≤ h e^{L h} (ε₀ + h Γ₁ (ν_C + ν_D + ℓ_C ℓ_D) + h² Γ₂),

where `ε₀` bounds the normal component `(1 - U₀ U₀ᵀ) F(Y₀) (1 - V₀ V₀ᵀ)`, `ν_C` and `ν_D` bound
the weighted leaks `(1 - U₀ U₀ᵀ) C U₀ S₀` and `S₀ V₀ᵀ D (1 - V₀ V₀ᵀ)`, and `ℓ_C`, `ℓ_D` the
unweighted leaks `(1 - U₀ U₀ᵀ) C U₀` and `V₀ᵀ D (1 - V₀ V₀ᵀ)`.  `Γ₁` and `Γ₂` depend only on
bounds `a, b, c, δ` of `‖𝒜‖, ‖ℬ‖, ‖C‖, ‖D‖`, a bound `σ` of `‖S₀‖`, an upper bound of `h` and the
increment constants `κ, κ₂, π`; no singular value of `S₀` enters.

The increment bounds `‖K(t) - U₀ S₀‖ ≤ κ (t - t₀)`,
`‖K(t) - U₀ S₀ - (t - t₀) K'(t₀)‖ ≤ κ₂ (t - t₀)²` and `‖P(t) - V₀ᵀ‖ ≤ π (t - t₀)` are hypotheses
on the substep solutions; for a field bounded on the relevant set they hold with constants built
from that bound and the coefficients, which is not formalised here.  The proof compares `A` with
the curve `K P + U₀ Z`, which lies in the range of `Û` at `t₁` (Grönwall,
`norm_sub_le_gronwallBound`). -/
theorem norm_sub_leftProj_le_of_twoSided [DecidableEq m] [DecidableEq n] {k : Type*} [Fintype k]
    [DecidableEq k] {L h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {K : ℝ → Matrix m (Fin r) ℝ} (hK : ODESolution (kField V₀ F) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀) {Ua : Matrix m k ℝ} (hUa : Uaᵀ * Ua = 1)
    (hcapK : Ua * Uaᵀ * K t₁ = K t₁) (hcapU : Ua * Uaᵀ * U₀ = U₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    {Z : ℝ → Matrix (Fin r) n ℝ}
    (hZ : ODESolution
      (fun t X => X * ℬ - U₀ᵀ * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))) Z t₀ t₁)
    (hZ₀ : Z t₀ = 0) {a b c δ σ κ κ₂ π ε₀ νC νD ℓC ℓD Γ₁ Γ₂ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hK₁ : ∀ t ∈ Icc t₀ t₁, ‖K t - U₀ * S₀‖ ≤ κ * (t - t₀))
    (hK₂ : ∀ t ∈ Icc t₀ t₁,
      ‖K t - U₀ * S₀ - (t - t₀) • kField V₀ F t₀ (U₀ * S₀)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hPπ : ∀ t ∈ Icc t₀ t₁, ‖P t - V₀ᵀ‖ ≤ π * (t - t₀))
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hνC : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ νC)
    (hνD : ‖S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ νD)
    (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC) (hℓD : ‖V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ ℓD)
    (hΓ₁ : 2 * δ * π + c * δ ^ 2 + c * a + (a + c * δ) * c * Real.exp (b * h) + κ ≤ Γ₁)
    (hΓ₂ : 2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ
      + (a + c * δ) * Real.exp (b * h) * (2 * c * σ * δ * π + c * κ * δ)
      + h * (2 * c * κ₂ * δ * π + (a + c * δ) * Real.exp (b * h) * (2 * c * κ * δ * π))
        ≤ Γ₂) :
    ‖A t₁ - Ua * Uaᵀ * A t₁‖
      ≤ h * Real.exp (L * h) * (ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂) := by
  have ha : 0 ≤ a := (norm_nonneg _).trans h𝒜
  have hb : 0 ≤ b := (norm_nonneg _).trans hℬ
  have hc : 0 ≤ c := (norm_nonneg _).trans hC
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hD
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans hσ
  have hε0 : 0 ≤ ε₀ := (norm_nonneg _).trans hε₀
  have hνC0 : 0 ≤ νC := (norm_nonneg _).trans hνC
  have hνD0 : 0 ≤ νD := (norm_nonneg _).trans hνD
  have hℓC0 : 0 ≤ ℓC := (norm_nonneg _).trans hℓC
  have hℓD0 : 0 ≤ ℓD := (norm_nonneg _).trans hℓD
  have hexp : 0 ≤ Real.exp (b * h) := (Real.exp_pos _).le
  have hle : t₀ ≤ t₁ := by linarith
  -- algebraic facts at the start
  have hU0 : ∀ X : Matrix (Fin r) (Fin r) ℝ, (1 - U₀ * U₀ᵀ) * (U₀ * X) = 0 := fun X => by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, hU₀,
      Matrix.one_mul, sub_self]
  have hU0' : ∀ X : Matrix (Fin r) n ℝ, (1 - U₀ * U₀ᵀ) * (U₀ * X) = 0 := fun X => by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, hU₀,
      Matrix.one_mul, sub_self]
  have hV0 : V₀ᵀ * (1 - V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV₀, Matrix.one_mul, sub_self]
  have hE₀eq : V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D = -(V₀ᵀ * D * (1 - V₀ * V₀ᵀ)) := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hE₀ℓ : ‖V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D‖ ≤ ℓD := by rw [hE₀eq, norm_neg]; exact hℓD
  have hE₀δ : ‖V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D‖ ≤ δ := by
    rw [hE₀eq, norm_neg]
    exact (norm_mul_one_sub_le hV₀ _).trans ((norm_transpose_mul_le' hV₀ D).trans hD)
  have hSE₀ : ‖S₀ * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)‖ ≤ νD := by
    rw [hE₀eq, Matrix.mul_neg, norm_neg]
    simpa only [Matrix.mul_assoc] using hνD
  have hN : ‖V₀ᵀ * D * V₀‖ ≤ δ :=
    (norm_mul_le' hV₀ _).trans ((norm_transpose_mul_le' hV₀ D).trans hD)
  have hnc : (1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)
      = (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (V₀ᵀ * D * (1 - V₀ * V₀ᵀ)) := by
    rw [hFS]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hU0', hV0, Matrix.mul_zero,
      zero_add, add_zero]
  have hT1 : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)‖ ≤ ε₀ := by
    rw [hE₀eq, Matrix.mul_neg, norm_neg, ← hnc]
    exact hε₀
  have hPiA : ‖(1 - U₀ * U₀ᵀ) * 𝒜 * U₀‖ ≤ a :=
    (norm_mul_le' hU₀ _).trans ((norm_one_sub_mul_le hU₀ 𝒜).trans h𝒜)
  have hPiCUS : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ c * σ :=
    norm_mul_mul_le _ _ ((norm_mul_le' hU₀ _).trans ((norm_one_sub_mul_le hU₀ C).trans hC)) hσ
  have hK1eq : (1 - U₀ * U₀ᵀ) * kField V₀ F t₀ (U₀ * S₀)
      = (1 - U₀ * U₀ᵀ) * 𝒜 * U₀ * S₀ + (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (V₀ᵀ * D * V₀) := by
    rw [kField_of_twoSided hFS hV₀]
    simp only [Matrix.mul_add, Matrix.mul_assoc, hU0, add_zero]
  have hKn : ‖(1 - U₀ * U₀ᵀ) * kField V₀ F t₀ (U₀ * S₀)‖ ≤ a * σ + c * σ * δ := by
    rw [hK1eq]
    exact norm_add_le_of_le (norm_mul_mul_le _ _ hPiA hσ) (norm_mul_mul_le _ _ hPiCUS hN)
  have hKE : ‖(1 - U₀ * U₀ᵀ) * kField V₀ F t₀ (U₀ * S₀) * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)‖
      ≤ a * νD + νC * δ ^ 2 := by
    rw [hK1eq, Matrix.add_mul]
    have e1 : (1 - U₀ * U₀ᵀ) * 𝒜 * U₀ * S₀ * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)
        = (1 - U₀ * U₀ᵀ) * 𝒜 * U₀ * (S₀ * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)) := by
      rw [Matrix.mul_assoc]
    have e2 : (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (V₀ᵀ * D * V₀) * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)
        = (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * ((V₀ᵀ * D * V₀) * (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)) := by
      rw [Matrix.mul_assoc]
    rw [e1, e2]
    refine (norm_add_le_of_le (norm_mul_mul_le _ _ hPiA hSE₀)
      (norm_mul_mul_le _ _ hνC (norm_mul_mul_le _ _ hN hE₀δ))).trans (le_of_eq ?_)
    ring
  -- the increments of `E = N P - P D`
  have hEinc : ∀ s ∈ Icc t₀ t₁, ‖(V₀ᵀ * D * V₀ * P s - P s * D)
      - (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)‖ ≤ 2 * δ * π * (s - t₀) := fun s hs => by
    have e : (V₀ᵀ * D * V₀ * P s - P s * D) - (V₀ᵀ * D * V₀ * V₀ᵀ - V₀ᵀ * D)
        = V₀ᵀ * D * V₀ * (P s - V₀ᵀ) - (P s - V₀ᵀ) * D := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e]
    refine (norm_sub_le_of_le (norm_mul_mul_le _ _ hN (hPπ s hs))
      (norm_mul_mul_le _ _ (hPπ s hs) hD)).trans (le_of_eq ?_)
    ring
  -- the correction `Z`
  set ηZ := c * νD + h * (2 * c * σ * δ * π + c * κ * δ) + h ^ 2 * (2 * c * κ * δ * π)
    with hηZ
  have p2 : (0 : ℝ) ≤ 2 := two_pos.le
  have hηZ0 : 0 ≤ ηZ := by
    rw [hηZ]
    exact add_nonneg (add_nonneg (mul_nonneg hc hνD0) (mul_nonneg hh (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p2 hc) hσ0) hδ) hπ)
      (mul_nonneg (mul_nonneg hc hκ) hδ))))
      (mul_nonneg (sq_nonneg h) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p2 hc) hκ) hδ) hπ))
  have hX₁ : 0 ≤ (2 * δ * π + c * δ ^ 2) * νC + c * a * νD + κ * (ℓC * ℓD) :=
    add_nonneg (add_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg p2 hδ) hπ)
      (mul_nonneg hc (sq_nonneg δ))) hνC0) (mul_nonneg (mul_nonneg hc ha) hνD0))
      (mul_nonneg hκ (mul_nonneg hℓC0 hℓD0))
  have hX₂ : 0 ≤ 2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ :=
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p2 hc) hδ) hπ) hκ)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p2 hc) hδ) hπ) hσ0)
        (add_nonneg ha (mul_nonneg hc hδ)))) (mul_nonneg (mul_nonneg hc hκ₂) hδ)
  have hX₃ : 0 ≤ 2 * c * κ₂ * δ * π :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg p2 hc) hκ₂) hδ) hπ
  have hZb : ∀ s ∈ Icc t₀ t₁, ‖Z s‖ ≤ Real.exp (b * h) * (ηZ * h) := by
    have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := Z) (δ := 0) (K := b)
      (ε := ηZ) hZ.cont (fun s hs => hZ.deriv s hs) (by rw [hZ₀, norm_zero])
      (fun s hs => by
        have hs' : s ∈ Icc t₀ t₁ := Ico_subset_Icc_self hs
        have hτ : 0 ≤ s - t₀ := by linarith [hs.1]
        have hτh : s - t₀ ≤ h := by linarith [hs.2]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖Z s * ℬ‖ ≤ b * ‖Z s‖ := by
          rw [mul_comm]; exact norm_mul_mul_le _ _ le_rfl hℬ
        have h2 := norm_zSource_le hU₀ hτ hτh hC hσ hκ hπ (hK₁ s hs') (hEinc s hs') hE₀δ hSE₀
        rw [hηZ]
        linarith only [h1, h2])
    intro s hs
    refine (hg s hs).trans ((gronwallBound_le_exp_mul hb hηZ0).trans ?_)
    have hτh : s - t₀ ≤ h := by linarith [hs.2]
    have hτ : 0 ≤ s - t₀ := by linarith [hs.1]
    rw [zero_add]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτh hb))
      (mul_le_mul_of_nonneg_left hτh hηZ0) (mul_nonneg hηZ0 hτ) hexp
  -- the defect of the comparison curve
  set η := ε₀ + h * ((2 * δ * π + c * δ ^ 2) * νC + c * a * νD + κ * (ℓC * ℓD))
    + h * h * (2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ)
    + h * h ^ 2 * (2 * c * κ₂ * δ * π) + (a + c * δ) * (Real.exp (b * h) * (ηZ * h)) with hη
  have hdef : ∀ s ∈ Ico t₀ t₁, ‖(F s (K s * P s + U₀ * Z s)
      + ((1 - U₀ * U₀ᵀ) * (C * K s * (V₀ᵀ * D * V₀ * P s - P s * D)) - 𝒜 * U₀ * Z s
        - C * U₀ * Z s * D)) - F s (K s * P s + U₀ * Z s)‖ ≤ η := fun s hs => by
    have hs' : s ∈ Icc t₀ t₁ := Ico_subset_Icc_self hs
    have hτ : 0 ≤ s - t₀ := by linarith [hs.1]
    have hτh : s - t₀ ≤ h := by linarith [hs.2]
    rw [add_sub_cancel_left]
    refine (norm_leftDefect_le hU₀ hτ hτh h𝒜 hC hD hσ hκ hκ₂ hπ (hK₁ s hs') (hK₂ s hs')
      (hEinc s hs') hE₀δ hE₀ℓ hT1 hKE hKn hνC hℓC (hZb s hs')).trans ?_
    rw [hη]
    linarith only [mul_le_mul_of_nonneg_right hτh hX₁,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτh hh) hX₂,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτh (sq_nonneg h)) hX₃]
  have hη0 : 0 ≤ η := by
    rw [hη]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg hε0 (mul_nonneg hh hX₁))
      (mul_nonneg (mul_nonneg hh hh) hX₂)) (mul_nonneg (mul_nonneg hh (sq_nonneg h)) hX₃))
      (mul_nonneg (add_nonneg ha (mul_nonneg hc hδ)) (mul_nonneg hexp (mul_nonneg hηZ0 hh)))
  -- Grönwall for `A - (K P + U₀ Z)`
  have hW₀ : ‖(K t₀ * P t₀ + U₀ * Z t₀) - A t₀‖ ≤ 0 := by
    rw [hK₀, hP₀, hZ₀, hA₀, Matrix.mul_zero, add_zero, sub_self, norm_zero]
  have hgr := norm_sub_le_gronwallBound hF hL (ηy := η) (ηz := 0)
    (continuousOn_kCurve_add hK.cont hP.cont hZ.cont)
    (fun s hs => hasDerivWithinAt_kCurve_add_of_twoSided hFS hV₀ hK hP hZ hs) hdef
    hA.cont hA.deriv (fun _ _ => by simp) hW₀ t₁ (right_mem_Icc.2 hle)
  have hth : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [add_zero, hth] at hgr
  have hgr' := hgr.trans (gronwallBound_le_exp_mul hL hη0)
  -- the comparison curve lies in the range of `Û` at `t₁`
  have hfix : leftProj Ua (K t₁ * P t₁ + U₀ * Z t₁) = K t₁ * P t₁ + U₀ * Z t₁ := by
    rw [leftProj_apply, Matrix.mul_add, ← Matrix.mul_assoc, hcapK, ← Matrix.mul_assoc, hcapU]
  have hcap := (isOrthProj_leftProj (n := n) hUa).norm_sub_le_of_mem_range (A t₁) _ hfix
  rw [leftProj_apply] at hcap
  -- `η` against the stated bound
  have g1 : 2 * δ * π + c * δ ^ 2 ≤ Γ₁ := by
    linarith only [hΓ₁, mul_nonneg hc ha, mul_nonneg (mul_nonneg (add_nonneg ha
      (mul_nonneg hc hδ)) hc) hexp, hκ]
  have g2 : c * a + (a + c * δ) * c * Real.exp (b * h) ≤ Γ₁ := by
    linarith only [hΓ₁, mul_nonneg (mul_nonneg two_pos.le hδ) hπ, mul_nonneg hc (sq_nonneg δ), hκ]
  have g3 : κ ≤ Γ₁ := by
    linarith only [hΓ₁, mul_nonneg (mul_nonneg two_pos.le hδ) hπ, mul_nonneg hc (sq_nonneg δ),
      mul_nonneg hc ha, mul_nonneg (mul_nonneg (add_nonneg ha (mul_nonneg hc hδ)) hc) hexp]
  have hΓ₁ν : (2 * δ * π + c * δ ^ 2) * νC + (c * a + (a + c * δ) * c * Real.exp (b * h)) * νD
      + κ * (ℓC * ℓD) ≤ Γ₁ * (νC + νD + ℓC * ℓD) := by
    linarith only [mul_le_mul_of_nonneg_right g1 hνC0, mul_le_mul_of_nonneg_right g2 hνD0,
      mul_le_mul_of_nonneg_right g3 (mul_nonneg hℓC0 hℓD0)]
  have hηeq : η = ε₀ + h * ((2 * δ * π + c * δ ^ 2) * νC
      + (c * a + (a + c * δ) * c * Real.exp (b * h)) * νD + κ * (ℓC * ℓD))
      + h ^ 2 * (2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ
        + (a + c * δ) * Real.exp (b * h) * (2 * c * σ * δ * π + c * κ * δ)
        + h * (2 * c * κ₂ * δ * π + (a + c * δ) * Real.exp (b * h) * (2 * c * κ * δ * π))) := by
    rw [hη, hηZ]
    ring
  have hηle : η ≤ ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂ := by
    rw [hηeq]
    linarith only [mul_le_mul_of_nonneg_left hΓ₁ν hh, mul_le_mul_of_nonneg_left hΓ₂ (sq_nonneg h)]
  calc ‖A t₁ - Ua * Uaᵀ * A t₁‖ ≤ ‖K t₁ * P t₁ + U₀ * Z t₁ - A t₁‖ :=
        hcap.trans_eq (norm_sub_rev _ _)
    _ ≤ Real.exp (L * h) * (0 + η * h) := hgr'
    _ = h * Real.exp (L * h) * η := by ring
    _ ≤ h * Real.exp (L * h) * (ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂) :=
      mul_le_mul_of_nonneg_left hηle (mul_nonneg hh (Real.exp_pos _).le)

/-! ### The row side, by transposition -/

/-- Transposition maps solutions of `X' = G(t, X)` to solutions of `Xᵀ' = G'(t, Xᵀ)` when
`G'(t, Y(t)ᵀ) = G(t, Y(t))ᵀ` along the solution. -/
private theorem odeSolution_transpose {a b : Type*} [Fintype a] [Fintype b]
    {G : ℝ → Matrix a b ℝ → Matrix a b ℝ} {G' : ℝ → Matrix b a ℝ → Matrix b a ℝ}
    {Y : ℝ → Matrix a b ℝ} (hY : ODESolution G Y t₀ t₁)
    (hG : ∀ t ∈ Ico t₀ t₁, G' t (Y t)ᵀ = (G t (Y t))ᵀ) :
    ODESolution G' (fun t => (Y t)ᵀ) t₀ t₁ where
  cont := (Frobenius.transposeCLM (m := a) (n := b)).continuous.comp_continuousOn hY.cont
  deriv t ht := by
    rw [hG t ht]
    exact Frobenius.hasDerivWithinAt_transpose (hY.deriv t ht)

/-- The transposed field `X ↦ F(t, Xᵀ)ᵀ` of a field with a two-sided term. -/
private theorem transpose_field_of_twoSided (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D)
    (t : ℝ) (X : Matrix n m ℝ) :
    (F t Xᵀ)ᵀ = ℬᵀ * X + X * 𝒜ᵀ + Dᵀ * X * Cᵀ := by
  rw [hFS]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  abel

/-- **Row capture defect of the rank-adaptive BUG step for a field with a two-sided term**: the
mirror image of `norm_sub_leftProj_le_of_twoSided`, obtained by transposition.  `Q` is the
auxiliary flow of `capture_of_sylvester` (`Q' = 𝒜 Q - Q (U₀ᵀ 𝒜 U₀)`, `Q(t₀) = U₀`) and `Zr` the
row-side correction.  The increment bounds of the L-step solution and of `Q` are hypotheses, as
in `norm_sub_leftProj_le_of_twoSided`. -/
theorem norm_sub_rightProj_le_of_twoSided [DecidableEq m] [DecidableEq n] {k' : Type*}
    [Fintype k'] [DecidableEq k'] {L h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {Lf : ℝ → Matrix n (Fin r) ℝ} (hLf : ODESolution (lField U₀ F) Lf t₀ t₁)
    (hLf₀ : Lf t₀ = V₀ * S₀ᵀ) {Va : Matrix n k' ℝ} (hVa : Vaᵀ * Va = 1)
    (hcapL : Va * Vaᵀ * Lf t₁ = Lf t₁) (hcapV : Va * Vaᵀ * V₀ = V₀)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun _ X => 𝒜 * X - X * (U₀ᵀ * 𝒜 * U₀)) Q t₀ t₁) (hQ₀ : Q t₀ = U₀)
    {Zr : ℝ → Matrix m (Fin r) ℝ}
    (hZr : ODESolution
      (fun t X => 𝒜 * X - (Q t * (U₀ᵀ * C * U₀) - C * Q t) * (Lf t)ᵀ * D * V₀) Zr t₀ t₁)
    (hZr₀ : Zr t₀ = 0) {a b c δ σ κ κ₂ π ε₀ νC νD ℓC ℓD Γ₁ Γ₂ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hL₁ : ∀ t ∈ Icc t₀ t₁, ‖Lf t - V₀ * S₀ᵀ‖ ≤ κ * (t - t₀))
    (hL₂ : ∀ t ∈ Icc t₀ t₁,
      ‖Lf t - V₀ * S₀ᵀ - (t - t₀) • lField U₀ F t₀ (V₀ * S₀ᵀ)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hQπ : ∀ t ∈ Icc t₀ t₁, ‖Q t - U₀‖ ≤ π * (t - t₀))
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hνC : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ νC)
    (hνD : ‖S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ νD)
    (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC) (hℓD : ‖V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ ℓD)
    (hΓ₁ : 2 * c * π + δ * c ^ 2 + δ * b + (b + δ * c) * δ * Real.exp (a * h) + κ ≤ Γ₁)
    (hΓ₂ : 2 * δ * c * π * κ + 2 * δ * c * π * σ * (b + δ * c) + δ * κ₂ * c
      + (b + δ * c) * Real.exp (a * h) * (2 * δ * σ * c * π + δ * κ * c)
      + h * (2 * δ * κ₂ * c * π + (b + δ * c) * Real.exp (a * h) * (2 * δ * κ * c * π))
        ≤ Γ₂) :
    ‖A t₁ - A t₁ * Va * Vaᵀ‖
      ≤ h * Real.exp (L * h) * (ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂) := by
  set G : ℝ → Matrix n m ℝ → Matrix n m ℝ := fun t X => (F t Xᵀ)ᵀ with hGdef
  have hGS : ∀ t X, G t X = ℬᵀ * X + X * 𝒜ᵀ + Dᵀ * X * Cᵀ := fun t X =>
    transpose_field_of_twoSided hFS t X
  have hG : IsLipschitzField G L := fun t X Y => by
    simp only [hGdef]
    rw [← Matrix.transpose_sub, Frobenius.norm_transpose, ← Frobenius.norm_transpose (X - Y),
      Matrix.transpose_sub]
    exact hF t Xᵀ Yᵀ
  have hkl : kField U₀ G = lField U₀ F := by
    funext t Lm
    simp only [kField, lField, hGdef, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hb := norm_sub_leftProj_le_of_twoSided (F := G) (𝒜 := ℬᵀ) (ℬ := 𝒜ᵀ) (C := Dᵀ)
    (D := Cᵀ) (U₀ := V₀) (S₀ := S₀ᵀ) (V₀ := U₀) (K := Lf) (Ua := Va)
    (A := fun t => (A t)ᵀ) (P := fun t => (Q t)ᵀ) (Z := fun t => (Zr t)ᵀ)
    (a := b) (b := a) (c := δ) (δ := c) (σ := σ) (κ := κ) (κ₂ := κ₂) (π := π) (ε₀ := ε₀)
    (νC := νD) (νD := νC) (ℓC := ℓD) (ℓD := ℓC) (Γ₁ := Γ₁) (Γ₂ := Γ₂) hGS hG hL ht₁ hh hV₀ hU₀
    (by rwa [hkl]) hLf₀ hVa hcapL hcapV
    (odeSolution_transpose hA fun t _ => by simp only [hGdef, Matrix.transpose_transpose])
    (by rw [hA₀]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc])
    (odeSolution_transpose hQ fun t _ => by
      simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc])
    (by simp only [hQ₀])
    (odeSolution_transpose hZr fun t _ => by
      simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_assoc])
    (by simp only [hZr₀, Matrix.transpose_zero])
    (by rwa [Frobenius.norm_transpose]) (by rwa [Frobenius.norm_transpose])
    (by rwa [Frobenius.norm_transpose]) (by rwa [Frobenius.norm_transpose])
    (by rwa [Frobenius.norm_transpose]) hκ hκ₂ hπ hL₁
    (by rwa [hkl])
    (fun t ht => by rw [← Matrix.transpose_sub, Frobenius.norm_transpose]; exact hQπ t ht)
    (by
      rw [← Frobenius.norm_transpose]
      convert hε₀ using 2
      simp only [hGdef, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
    (by
      rw [← Frobenius.norm_transpose]
      convert hνD using 2
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
    (by
      rw [← Frobenius.norm_transpose]
      convert hνC using 2
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
    (by
      rw [← Frobenius.norm_transpose]
      convert hℓD using 2
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
    (by
      rw [← Frobenius.norm_transpose]
      convert hℓC using 2
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.transpose_transpose, Matrix.mul_assoc])
    hΓ₁ hΓ₂
  have e : A t₁ - A t₁ * Va * Vaᵀ = ((A t₁)ᵀ - Va * Vaᵀ * (A t₁)ᵀ)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [e, Frobenius.norm_transpose]
  refine hb.trans (le_of_eq ?_)
  ring

/-! ### The local error of the step -/

/-- `galerkinProj Ub Vb X = leftProj Ub (rightProj Vb X)`, by definition. -/
private theorem galerkinProj_eq' {b b' : Type*} [Fintype b] [Fintype b'] (Ub : Matrix m b ℝ)
    (Vb : Matrix n b' ℝ) (X : Matrix m n ℝ) :
    galerkinProj Ub Vb X = leftProj Ub (rightProj Vb X) := rfl

/-- **Local error of the rank-adaptive BUG step for a field with a two-sided term.**  For
`F(Y) = 𝒜 Y + Y ℬ + C Y D`, `L`-Lipschitz, and every step of the rank-adaptive BUG integrator
(Ceruti–Kusch–Lubich, arXiv:2104.05247; `MatrixBUG.IsRankAdaptiveStep`) with truncation
tolerance `ϑ`,

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ,
    θ = 2 h e^{L h} (ε₀ + h Γ₁ (ν_C + ν_D + ℓ_C ℓ_D) + h² Γ₂),

with the quantities of `norm_sub_leftProj_le_of_twoSided` (`ε₀` the normal component of `F` at
the start, `ν_C`, `ν_D` the weighted and `ℓ_C`, `ℓ_D` the unweighted leaks of the two-sided term)
and `M₂` a bound of the derivative of `t ↦ F(t, A(t))`.  So the local error is `O(h³)`, the order
of a second-order method, when `ε₀ = 0` and the leaks are `O(h)`.  For `C = 0` the field does
not depend on `D`, so `D = 0` may be taken: then `ε₀` and all leaks vanish, `Z = Zr = 0` are
admissible, and the bound is `O(h³)`, the order of `error_le_of_sylvester`.  This
is a sufficient condition for second order, not a characterisation.  The auxiliary flows `P`,
`Z`, `Q`, `Zr` and the increment bounds `κ`, `κ₂`, `π` of the substep solutions are hypotheses;
for a field bounded on the relevant set the increment bounds hold with constants built from that
bound and the coefficients, which is not formalised here.  No singular value of `S₀` enters.

The bound is not sharp in every case: for `ℬ = 0` and `V₀ᵀ D (1 - V₀ V₀ᵀ) = 0` the defect of
`hasDerivWithinAt_kCurve_add_of_twoSided` vanishes with `P = V₀ᵀ`, `Z = 0`, so `K(t) V₀ᵀ` is
the exact solution and the capture is exact whatever the leak of `C`, while the bound above
keeps a term `h² ν_C`. -/
theorem error_le_of_twoSided [DecidableEq m] [DecidableEq n] {k k' : Type*} [Fintype k]
    [Fintype k'] [DecidableEq k]
    [DecidableEq k'] {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ}
    {Lf : ℝ → Matrix n (Fin r) ℝ} {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ} {ϑ L h : ℝ}
    (hFS : ∀ t Y, F t Y = 𝒜 * Y + Y * ℬ + C * Y * D) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hs : IsRankAdaptiveStep F ϑ t₀ t₁ U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    {P : ℝ → Matrix (Fin r) n ℝ}
    (hP : ODESolution (fun _ X => X * ℬ - V₀ᵀ * ℬ * V₀ * X) P t₀ t₁) (hP₀ : P t₀ = V₀ᵀ)
    {Z : ℝ → Matrix (Fin r) n ℝ}
    (hZ : ODESolution
      (fun t X => X * ℬ - U₀ᵀ * (C * K t * (V₀ᵀ * D * V₀ * P t - P t * D))) Z t₀ t₁)
    (hZ₀ : Z t₀ = 0) {Q : ℝ → Matrix m (Fin r) ℝ}
    (hQ : ODESolution (fun _ X => 𝒜 * X - X * (U₀ᵀ * 𝒜 * U₀)) Q t₀ t₁) (hQ₀ : Q t₀ = U₀)
    {Zr : ℝ → Matrix m (Fin r) ℝ}
    (hZr : ODESolution
      (fun t X => 𝒜 * X - (Q t * (U₀ᵀ * C * U₀) - C * Q t) * (Lf t)ᵀ * D * V₀) Zr t₀ t₁)
    (hZr₀ : Zr t₀ = 0) {a₂ : ℝ → Matrix m n ℝ} {M₂ : ℝ}
    (ha : ContinuousOn (fun t => F t (A t)) (Icc t₀ t₁))
    (ha' : ∀ s ∈ Ico t₀ t₁, HasDerivWithinAt (fun t => F t (A t)) (a₂ s) (Ici s) s)
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b c δ σ κ κ₂ π ε₀ νC νD ℓC ℓD Γ₁ Γ₂ θ : ℝ}
    (h𝒜 : ‖𝒜‖ ≤ a) (hℬ : ‖ℬ‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ δ) (hσ : ‖S₀‖ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hπ : 0 ≤ π)
    (hK₁ : ∀ t ∈ Icc t₀ t₁, ‖K t - U₀ * S₀‖ ≤ κ * (t - t₀))
    (hK₂ : ∀ t ∈ Icc t₀ t₁,
      ‖K t - U₀ * S₀ - (t - t₀) • kField V₀ F t₀ (U₀ * S₀)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hL₁ : ∀ t ∈ Icc t₀ t₁, ‖Lf t - V₀ * S₀ᵀ‖ ≤ κ * (t - t₀))
    (hL₂ : ∀ t ∈ Icc t₀ t₁,
      ‖Lf t - V₀ * S₀ᵀ - (t - t₀) • lField U₀ F t₀ (V₀ * S₀ᵀ)‖ ≤ κ₂ * (t - t₀) ^ 2)
    (hPπ : ∀ t ∈ Icc t₀ t₁, ‖P t - V₀ᵀ‖ ≤ π * (t - t₀))
    (hQπ : ∀ t ∈ Icc t₀ t₁, ‖Q t - U₀‖ ≤ π * (t - t₀))
    (hε₀ : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε₀)
    (hνC : ‖(1 - U₀ * U₀ᵀ) * C * U₀ * S₀‖ ≤ νC)
    (hνD : ‖S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ νD)
    (hℓC : ‖(1 - U₀ * U₀ᵀ) * C * U₀‖ ≤ ℓC) (hℓD : ‖V₀ᵀ * D * (1 - V₀ * V₀ᵀ)‖ ≤ ℓD)
    (hΓ₁ : 2 * δ * π + c * δ ^ 2 + c * a + (a + c * δ) * c * Real.exp (b * h) + κ ≤ Γ₁)
    (hΓ₂ : 2 * c * δ * π * κ + 2 * c * δ * π * σ * (a + c * δ) + c * κ₂ * δ
      + (a + c * δ) * Real.exp (b * h) * (2 * c * σ * δ * π + c * κ * δ)
      + h * (2 * c * κ₂ * δ * π + (a + c * δ) * Real.exp (b * h) * (2 * c * κ * δ * π))
        ≤ Γ₂)
    (hΓ₁' : 2 * c * π + δ * c ^ 2 + δ * b + (b + δ * c) * δ * Real.exp (a * h) + κ ≤ Γ₁)
    (hΓ₂' : 2 * δ * c * π * κ + 2 * δ * c * π * σ * (b + δ * c) + δ * κ₂ * c
      + (b + δ * c) * Real.exp (a * h) * (2 * δ * σ * c * π + δ * κ * c)
      + h * (2 * δ * κ₂ * c * π + (b + δ * c) * Real.exp (a * h) * (2 * δ * κ * c * π))
        ≤ Γ₂)
    (hθ : θ = 2 * (h * Real.exp (L * h) * (ε₀ + h * Γ₁ * (νC + νD + ℓC * ℓD) + h ^ 2 * Γ₂))) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ := by
  have hle : t₀ ≤ t₁ := by linarith
  have hθL := norm_sub_leftProj_le_of_twoSided hFS hF hL ht₁ hh hs.orthU₀ hs.orthV₀ hs.kSol
    hs.kStart hs.orthUa hs.kCap hs.augU hA hA₀ hP hP₀ hZ hZ₀ h𝒜 hℬ hC hD hσ hκ hκ₂ hπ hK₁ hK₂
    hPπ hε₀ hνC hνD hℓC hℓD hΓ₁ hΓ₂
  have hθR := norm_sub_rightProj_le_of_twoSided hFS hF hL ht₁ hh hs.orthU₀ hs.orthV₀ hs.lSol
    hs.lStart hs.orthVa hs.lCap hs.augV hA hA₀ hQ hQ₀ hZr hZr₀ h𝒜 hℬ hC hD hσ hκ hκ₂ hπ hL₁ hL₂
    hQπ hε₀ hνC hνD hℓC hℓD hΓ₁' hΓ₂'
  have hR : IsOrthProj (galerkinProj Ua Va : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
    isOrthProj_galerkinProj hs.orthUa hs.orthVa
  -- the capture defect of the Galerkin space
  have hcap : ‖galerkinProj Ua Va (A t₁) - A t₁‖ ≤ θ := by
    have e : A t₁ - galerkinProj Ua Va (A t₁)
        = (A t₁ - Ua * Uaᵀ * A t₁) + Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ) := by
      rw [galerkinProj_eq', leftProj_apply, rightProj_apply, Matrix.mul_sub]
      abel
    have hc2 : ‖Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ)‖ ≤ ‖A t₁ - A t₁ * Va * Vaᵀ‖ := by
      have := (isOrthProj_leftProj (n := n) hs.orthUa).norm_le (A t₁ - A t₁ * Va * Vaᵀ)
      rwa [leftProj_apply] at this
    rw [norm_sub_rev, e, hθ]
    linarith [norm_add_le (A t₁ - Ua * Uaᵀ * A t₁) (Ua * Uaᵀ * (A t₁ - A t₁ * Va * Vaᵀ))]
  have hRA : galerkinProj Ua Va (A t₀) = A t₀ := by
    rw [galerkinProj_eq', hA₀, hs.aug_right, hs.aug_left]
  have hfix : galerkinProj Ua Va (galerkinProj Ua Va (A t₁)) = galerkinProj Ua Va (A t₁) :=
    hR.idem _
  have hYS : ODESolution (fun t x => galerkinProj Ua Va (F t x)) (fun t => Ua * Sa t * Vaᵀ)
      t₀ t₁ := by
    have h1 := odeSolution_sField hs.sSol
    simp only [galerkinProj_eq']
    exact h1
  have hS₀ : (fun t => Ua * Sa t * Vaᵀ) t₀ = A t₀ := hs.start_eq.trans hA₀.symm
  have hb := galerkin_error_of_predictor (E := Matrix m n ℝ) (R := galerkinProj Ua Va)
    (YS := fun t => Ua * Sa t * Vaᵀ) hR hF hL ht₁ hh hA hRA ha ha' hM₂ hfix hcap hYS hS₀
  have hb' : ‖Ua * Sa t₁ * Vaᵀ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ := hb
  have htri := norm_sub_le_norm_sub_add_norm_sub Y₁ (Ua * Sa t₁ * Vaᵀ) (A t₁)
  linarith [hs.trunc]

end TwoSided

/-! ### A step with a leaking two-sided term -/

namespace Examples

/-- The left factor `C = E₂₁` on `ℝ²`; it maps `e₁` to `e₂`, so the range of `e₁` leaks. -/
noncomputable def leakLeft : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The starting basis `e₁ ∈ ℝ²`. -/
noncomputable def leakStart : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The leak direction `e₂ ∈ ℝ²`. -/
noncomputable def leakDir : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The curve `t ↦ (1, t)ᵀ`: exact solution, K-step solution and Galerkin solution of the field
`Y ↦ E₂₁ Y` from `e₁`. -/
noncomputable def leakCurve (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := leakStart + t • leakDir

end Examples

section LeakExample

open MatrixBUG Examples

private theorem leakLeft_mul_leakStart : leakLeft * leakStart = leakDir := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [leakLeft, leakStart, leakDir, Matrix.mul_apply]

private theorem leakLeft_mul_leakDir : leakLeft * leakDir = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [leakLeft, leakDir, Matrix.mul_apply]

private theorem leakStart_orth : leakStartᵀ * leakStart = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [leakStart, Matrix.mul_apply]

private theorem leakDir_transpose_mul_leakStart : leakDirᵀ * leakStart = 0 := by
  ext i j; fin_cases i; fin_cases j; simp [leakStart, leakDir, Matrix.mul_apply]

private theorem leakStart_transpose_mul_leakDir : leakStartᵀ * leakDir = 0 := by
  ext i j; fin_cases i; fin_cases j; simp [leakStart, leakDir, Matrix.mul_apply]

private theorem leakStart_compress : leakStartᵀ * leakLeft * leakStart = 0 := by
  rw [Matrix.mul_assoc, leakLeft_mul_leakStart]
  ext i j; fin_cases i; fin_cases j; simp [leakStart, leakDir, Matrix.mul_apply]

/-- The leak of the example: `(1 - e₁ e₁ᵀ) E₂₁ e₁ = e₂`, so the unweighted and the weighted
leak of `C` are `‖e₂‖ = 1` (with `S₀ = 1`). -/
theorem leak_leakLeft : (1 - leakStart * leakStartᵀ) * leakLeft * leakStart = leakDir := by
  rw [Matrix.mul_assoc, leakLeft_mul_leakStart, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    leakStart_transpose_mul_leakDir, Matrix.mul_zero, sub_zero]

private theorem hasDerivAt_leakCurve (t : ℝ) : HasDerivAt leakCurve leakDir t := by
  have h1 := ((hasDerivAt_id t).smul_const leakDir).const_add leakStart
  rw [one_smul] at h1
  exact h1

private theorem leakLeft_mul_leakCurve (t : ℝ) : leakLeft * leakCurve t = leakDir := by
  rw [leakCurve, Matrix.mul_add, Matrix.mul_smul, leakLeft_mul_leakStart, leakLeft_mul_leakDir,
    smul_zero, add_zero]

/-- A curve with derivative `Y'` everywhere solves `X' = G(t, X)` if `G(t, Y(t)) = Y'`. -/
private theorem odeSolution_of_hasDerivAt {a b : Type*} [Fintype a] [Fintype b]
    {G : ℝ → Matrix a b ℝ → Matrix a b ℝ} {Y : ℝ → Matrix a b ℝ} {Y' : Matrix a b ℝ}
    (hY : ∀ t, HasDerivAt Y Y' t) (hG : ∀ t, G t (Y t) = Y') (h : ℝ) :
    ODESolution G Y 0 h where
  cont := fun t _ => (hY t).continuousAt.continuousWithinAt
  deriv t _ := by rw [hG t]; exact (hY t).hasDerivWithinAt

private theorem lField_leak (t : ℝ) :
    lField leakStart (fun _ Y => leakLeft * Y) t (1 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
  simp only [lField, Matrix.transpose_one, Matrix.mul_one, leakLeft_mul_leakStart,
    leakDir_transpose_mul_leakStart]

/-- The field `Y ↦ E₂₁ Y` on `2 × 1` matrices is Lipschitz with constant `‖E₂₁‖`. -/
theorem isLipschitzField_leakLeft :
    IsLipschitzField (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 1) ℝ) => leakLeft * Y) ‖leakLeft‖ :=
  fun _ X Y => by
    rw [← Matrix.mul_sub]
    exact Frobenius.norm_mul_le _ _

/-- A rank-adaptive BUG step for `Y ↦ E₂₁ Y` from `e₁` (`S₀ = 1`, `V₀ = 1`): `K = L-curve`
`(1, t)ᵀ`, `L(t) = 1`, `Û = I₂`, `V̂ = 1`, `Ŝ(t) = (1, t)ᵀ`, no truncation. -/
theorem isRankAdaptiveStep_leakLeft (h : ℝ) :
    IsRankAdaptiveStep (fun _ Y => leakLeft * Y) 0 0 h leakStart 1 1
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) leakCurve (fun _ => 1)
      leakCurve ((1 : Matrix (Fin 2) (Fin 2) ℝ) * leakCurve h * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ)
      where
  orthU₀ := leakStart_orth
  orthV₀ := by simp
  kSol := odeSolution_of_hasDerivAt hasDerivAt_leakCurve
    (fun t => by simp only [kField, Matrix.transpose_one, Matrix.mul_one, leakLeft_mul_leakCurve])
    h
  kStart := by simp [leakCurve]
  lSol := odeSolution_of_hasDerivAt (fun _ => hasDerivAt_const _ _) (fun t => lField_leak t) h
  lStart := by simp
  orthUa := by simp
  kCap := by simp
  augU := by simp
  orthVa := by simp
  lCap := by simp
  augV := by simp
  sSol := odeSolution_of_hasDerivAt hasDerivAt_leakCurve
    (fun t => by simp only [sField, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      leakLeft_mul_leakCurve]) h
  sStart := by simp [leakCurve]
  trunc := by simp

/-- **Non-vacuity of `error_le_of_twoSided`** with a leaking two-sided term: the field
`Y ↦ E₂₁ Y` written as `0 Y + Y 0 + E₂₁ Y 1`, the step of `isRankAdaptiveStep_leakLeft`, the exact
solution `(1, t)ᵀ`, the auxiliary flows `P = 1`, `Z = 0`, `Q = e₁`, `Zr(t) = t e₂`, and the
increment constants `κ = ‖e₂‖`, `κ₂ = π = 0`.  The leak of `C` is `‖e₂‖ = 1` (`leak_leakLeft`). -/
example (h : ℝ) (hh : 0 ≤ h) : ∃ θ : ℝ,
    ‖(1 : Matrix (Fin 2) (Fin 2) ℝ) * leakCurve h * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ - leakCurve h‖
      ≤ (Real.exp (‖leakLeft‖ * h) - 1) * (θ + 0 * h ^ 2) + θ + 0 := by
  have hcurve : (fun t => leakLeft * leakCurve t) = fun _ => leakDir :=
    funext leakLeft_mul_leakCurve
  have hinc : ∀ t ∈ Icc (0 : ℝ) h,
      ‖leakCurve t - leakStart * (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ ‖leakDir‖ * (t - 0) :=
    fun t ht => by
      rw [Matrix.mul_one, leakCurve, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1,
        sub_zero, mul_comm]
  refine ⟨_, error_le_of_twoSided (F := fun _ Y => leakLeft * Y) (𝒜 := 0) (ℬ := 0)
    (C := leakLeft) (D := 1) (A := leakCurve) (P := fun _ => 1) (Z := fun _ => 0)
    (Q := fun _ => leakStart) (Zr := fun t => t • leakDir) (a₂ := fun _ => 0) (M₂ := 0)
    (a := 0) (b := 0) (c := ‖leakLeft‖) (δ := ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖)
    (σ := ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖) (κ := ‖leakDir‖) (κ₂ := 0) (π := 0)
    (fun _ Y => by simp) isLipschitzField_leakLeft (norm_nonneg _) (zero_add h).symm hh
    (isRankAdaptiveStep_leakLeft h)
    (odeSolution_of_hasDerivAt hasDerivAt_leakCurve leakLeft_mul_leakCurve h)
    (by simp [leakCurve])
    (odeSolution_of_hasDerivAt (fun _ => hasDerivAt_const _ _) (fun _ => by simp) h)
    (by simp)
    (odeSolution_of_hasDerivAt (fun _ => hasDerivAt_const _ _) (fun _ => by simp) h) rfl
    (odeSolution_of_hasDerivAt (fun _ => hasDerivAt_const _ _) (fun _ => by simp) h) rfl
    (odeSolution_of_hasDerivAt
      (fun t => by
        have h1 := (hasDerivAt_id t).smul_const leakDir
        rw [one_smul] at h1
        exact h1)
      (fun _ => by simp [leakStart_compress, leakLeft_mul_leakStart]) h)
    (by simp)
    (by
      show ContinuousOn (fun t => leakLeft * leakCurve t) _
      rw [hcurve]; exact continuousOn_const)
    (fun s _ => by
      show HasDerivWithinAt (fun t => leakLeft * leakCurve t) 0 _ s
      rw [hcurve]; exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => by simp) (by simp) (by simp) le_rfl le_rfl le_rfl (norm_nonneg _) le_rfl le_rfl
    hinc
    (fun t _ => by simp [kField, leakLeft_mul_leakStart, leakCurve])
    (fun t ht => by simpa using mul_nonneg (norm_nonneg leakDir) ht.1)
    (fun t _ => by simp [lField_leak])
    (fun t _ => by simp) (fun t _ => by simp) le_rfl le_rfl le_rfl le_rfl le_rfl
    (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _) rfl⟩

end LeakExample

end AugmentationRank

end LeanDLRA
