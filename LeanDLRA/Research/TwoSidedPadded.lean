import LeanDLRA.Research.TwoSidedLeak

/-!
# The rank-adaptive BUG step from a start padded with the images of a two-sided term

## Setting

`F(Y) = 𝒜 Y + Y ℬ + C Y D` on `m × n` matrices, `Y₀ = U₀ S₀ V₀ᵀ`.  The bound
`error_le_of_twoSided` of one step of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich,
arXiv:2104.05247) contains the normal component `ε₀` of `F` at `Y₀`, the weighted leaks
`‖(1 - U₀ U₀ᵀ) C U₀ S₀‖`, `‖S₀ V₀ᵀ D (1 - V₀ V₀ᵀ)‖` and the product `ℓ_C ℓ_D` of the unweighted
leaks.  Write the same matrix in bases `Ũ`, `Ṽ` whose ranges contain those of `U₀`, `C U₀` and
of `V₀`, `Dᵀ V₀`, with the coefficient matrix `S̃ = Ũᵀ U₀ S₀ V₀ᵀ Ṽ` (the old coefficients padded
with zeros).  Then `Ũ S̃ Ṽᵀ = Y₀`, and both weighted leaks and the normal component vanish for
the padded factors.  The augmentation of the bases by the column and row spaces of the field
is the merged prediction space of Appelö–Cheng (arXiv:2402.05347, Algorithm 4), which also
contains the images `C U₀`.

## Main results

* `mul_paddedCoeff_mul_transpose_eq`: `Ũ S̃ Ṽᵀ = U₀ S₀ V₀ᵀ`.
* `leftLeak_paddedCoeff_eq_zero`, `rightLeak_paddedCoeff_eq_zero`: the weighted leaks of the
  padded factors vanish.
* `error_le_of_twoSided_of_leaks_eq_zero`: the local error of a rank-adaptive BUG step whose
  start has vanishing weighted leaks,
  `‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ`, `θ = 2 h e^{L h} (h Γ₁ ℓ_C ℓ_D + h² Γ₂)`.
  The product `ℓ_C ℓ_D` of the unweighted leaks of the padded bases remains, so the bound is of
  third order in `h` only when that product is `O(h)`; this is a sufficient condition, not a
  characterisation.

## Implementation notes

The auxiliary flows and the increment bounds are hypotheses, as in `error_le_of_twoSided`.  The
padded bases must have the same number of columns (the step of `MatrixBUG.IsRankAdaptiveStep`
has a square coefficient matrix); a basis can be padded by further orthonormal columns.

## References

* Ceruti–Kusch–Lubich, arXiv:2104.05247 (rank-adaptive BUG integrator).
* Appelö–Cheng, arXiv:2402.05347, Section 3.1 (bases merged with the column and row spaces of
  the field).
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace AugmentationRank

section Padded

open MatrixBUG

variable {m n : Type*} [Fintype m] [Fintype n] {r r' : ℕ}

/-! ### The padded start -/

/-- The padded factors represent the same matrix: if the ranges of `Ũ` and `Ṽ` contain those of
`U₀` and `V₀`, then `Ũ (Ũᵀ U₀ S₀ V₀ᵀ Ṽ) Ṽᵀ = U₀ S₀ V₀ᵀ`. -/
theorem mul_paddedCoeff_mul_transpose_eq {U₀ : Matrix m (Fin r) ℝ}
    {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Ut : Matrix m (Fin r') ℝ}
    {Vt : Matrix n (Fin r') ℝ} (hU : Ut * Utᵀ * U₀ = U₀) (hV : Vt * Vtᵀ * V₀ = V₀) :
    Ut * (Utᵀ * U₀ * S₀ * V₀ᵀ * Vt) * Vtᵀ = U₀ * S₀ * V₀ᵀ := by
  have hV' : V₀ᵀ * (Vt * Vtᵀ) = V₀ᵀ := by
    have h := congrArg Matrix.transpose hV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h
  calc Ut * (Utᵀ * U₀ * S₀ * V₀ᵀ * Vt) * Vtᵀ = Ut * Utᵀ * U₀ * S₀ * (V₀ᵀ * (Vt * Vtᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = U₀ * S₀ * V₀ᵀ := by rw [hU, hV']

/-- The weighted left leak of the padded factors vanishes when the range of `Ũ` contains those
of `U₀` and `C U₀`: `(1 - Ũ Ũᵀ) C Ũ S̃ = 0` for `S̃ = Ũᵀ U₀ S₀ V₀ᵀ Ṽ`. -/
theorem leftLeak_paddedCoeff_eq_zero [DecidableEq m] {C : Matrix m m ℝ}
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    {Ut : Matrix m (Fin r') ℝ} (Vt : Matrix n (Fin r') ℝ) (hU : Ut * Utᵀ * U₀ = U₀)
    (hCU : Ut * Utᵀ * (C * U₀) = C * U₀) :
    (1 - Ut * Utᵀ) * C * Ut * (Utᵀ * U₀ * S₀ * V₀ᵀ * Vt) = 0 := by
  have h1 : (1 - Ut * Utᵀ) * (C * U₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hCU, sub_self]
  calc (1 - Ut * Utᵀ) * C * Ut * (Utᵀ * U₀ * S₀ * V₀ᵀ * Vt)
        = (1 - Ut * Utᵀ) * (C * (Ut * Utᵀ * U₀)) * (S₀ * V₀ᵀ * Vt) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hU, h1, Matrix.zero_mul]

/-- The weighted right leak of the padded factors vanishes when the range of `Ṽ` contains those
of `V₀` and `Dᵀ V₀`: `S̃ Ṽᵀ D (1 - Ṽ Ṽᵀ) = 0` for `S̃ = Ũᵀ U₀ S₀ V₀ᵀ Ṽ`. -/
theorem rightLeak_paddedCoeff_eq_zero [DecidableEq n] {D : Matrix n n ℝ}
    {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (Ut : Matrix m (Fin r') ℝ) {Vt : Matrix n (Fin r') ℝ} (hV : Vt * Vtᵀ * V₀ = V₀)
    (hDV : Vt * Vtᵀ * (Dᵀ * V₀) = Dᵀ * V₀) :
    Utᵀ * U₀ * S₀ * V₀ᵀ * Vt * Vtᵀ * D * (1 - Vt * Vtᵀ) = 0 := by
  have hV' : V₀ᵀ * (Vt * Vtᵀ) = V₀ᵀ := by
    have h := congrArg Matrix.transpose hV
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using h
  have h2 : (1 - Vt * Vtᵀ) * (Dᵀ * V₀) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hDV, sub_self]
  have h3 : V₀ᵀ * (D * (1 - Vt * Vtᵀ)) = 0 := by
    have h := congrArg Matrix.transpose h2
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, Matrix.transpose_zero, Matrix.mul_assoc] using h
  calc Utᵀ * U₀ * S₀ * V₀ᵀ * Vt * Vtᵀ * D * (1 - Vt * Vtᵀ)
        = Utᵀ * U₀ * S₀ * (V₀ᵀ * (Vt * Vtᵀ)) * (D * (1 - Vt * Vtᵀ)) := by
          simp only [Matrix.mul_assoc]
    _ = Utᵀ * U₀ * S₀ * (V₀ᵀ * (D * (1 - Vt * Vtᵀ))) := by
          rw [hV']
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h3, Matrix.mul_zero]

/-! ### The local error from a start without weighted leaks -/

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {𝒜 C : Matrix m m ℝ} {ℬ D : Matrix n n ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {t₀ t₁ : ℝ}

/-- **Local error of the rank-adaptive BUG step from a start without weighted leaks.**  For
`F(Y) = 𝒜 Y + Y ℬ + C Y D`, `L`-Lipschitz, and a step of the rank-adaptive BUG integrator
(`MatrixBUG.IsRankAdaptiveStep`, tolerance `ϑ`) from `Y₀ = U₀ S₀ V₀ᵀ` with
`(1 - U₀ U₀ᵀ) C U₀ S₀ = 0` and `S₀ V₀ᵀ D (1 - V₀ V₀ᵀ) = 0`,

    ‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ + ϑ,   θ = 2 h e^{L h} (h Γ₁ ℓ_C ℓ_D + h² Γ₂),

with the quantities of `error_le_of_twoSided`.  The normal component of `F` at `Y₀` vanishes
under the two hypotheses, so this is `error_le_of_twoSided` with `ε₀ = ν_C = ν_D = 0`.  A start
padded with the images `C U₀` and `Dᵀ V₀` has these properties (`leftLeak_paddedCoeff_eq_zero`,
`rightLeak_paddedCoeff_eq_zero`).  The product `ℓ_C ℓ_D` of the unweighted leaks remains: the
bound is `O(h³)` when that product is `O(h)`, and `O(h²)` in general. -/
theorem error_le_of_twoSided_of_leaks_eq_zero [DecidableEq m] [DecidableEq n] {k k' : Type*}
    [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k'] {Ua : Matrix m k ℝ}
    {Va : Matrix n k' ℝ} {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
    {Sa : ℝ → Matrix k k' ℝ} {Y₁ : Matrix m n ℝ} {ϑ L h : ℝ}
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
    (hM₂ : ∀ s ∈ Ico t₀ t₁, ‖a₂ s‖ ≤ M₂) {a b c δ σ κ κ₂ π ℓC ℓD Γ₁ Γ₂ θ : ℝ}
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
    (hνC : (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ = 0) (hνD : S₀ * V₀ᵀ * D * (1 - V₀ * V₀ᵀ) = 0)
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
    (hθ : θ = 2 * (h * Real.exp (L * h) * (h * Γ₁ * (ℓC * ℓD) + h ^ 2 * Γ₂))) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ + ϑ := by
  have hV0 : V₀ᵀ * (1 - V₀ * V₀ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hs.orthV₀, Matrix.one_mul, sub_self]
  have hU0 : (1 - U₀ * U₀ᵀ) * U₀ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hs.orthU₀, Matrix.mul_one, sub_self]
  have hnc : (1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ) = 0 := by
    have e : (1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)
        = (1 - U₀ * U₀ᵀ) * 𝒜 * U₀ * S₀ * (V₀ᵀ * (1 - V₀ * V₀ᵀ))
          + (1 - U₀ * U₀ᵀ) * U₀ * (S₀ * V₀ᵀ * ℬ * (1 - V₀ * V₀ᵀ))
          + (1 - U₀ * U₀ᵀ) * C * U₀ * S₀ * (V₀ᵀ * D * (1 - V₀ * V₀ᵀ)) := by
      rw [hFS]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [e, hV0, hU0, hνC]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  exact error_le_of_twoSided (ε₀ := 0) (νC := 0) (νD := 0) hFS hF hL ht₁ hh hs hA hA₀ hP hP₀ hZ
    hZ₀ hQ hQ₀ hZr hZr₀ ha ha' hM₂ h𝒜 hℬ hC hD hσ hκ hκ₂ hπ hK₁ hK₂ hL₁ hL₂ hPπ hQπ
    (by rw [hnc, norm_zero]) (by rw [hνC, norm_zero]) (by rw [hνD, norm_zero])
    hℓC hℓD hΓ₁ hΓ₂ hΓ₁' hΓ₂' (by rw [hθ]; ring)

end Padded

/-! ### A step from a padded start -/

section PaddedExample

open MatrixBUG Examples

local notation "I₂" => (1 : Matrix (Fin 2) (Fin 2) ℝ)
local notation "I₁" => (1 : Matrix (Fin 1) (Fin 1) ℝ)

/-- The original start `e₁` leaks under `C = E₂₁`, while the start padded with `C e₁ = e₂`
(here the whole space, `Ũ = Ṽ = I₂`) has no weighted leak. -/
example : (1 - leakStart * leakStartᵀ) * leakLeft * leakStart = leakDir ∧
    (1 - I₂ * I₂ᵀ) * leakLeft * I₂ * (I₂ᵀ * leakStart * I₁ * leakStartᵀ * I₂) = 0 ∧
    I₂ᵀ * leakStart * I₁ * leakStartᵀ * I₂ * I₂ᵀ * I₂ * (1 - I₂ * I₂ᵀ) = 0 ∧
    I₂ * (I₂ᵀ * leakStart * I₁ * leakStartᵀ * I₂) * I₂ᵀ = leakStart * I₁ * leakStartᵀ :=
  ⟨leak_leakLeft, leftLeak_paddedCoeff_eq_zero I₂ (by simp) (by simp),
    rightLeak_paddedCoeff_eq_zero I₂ (by simp) (by simp),
    mul_paddedCoeff_mul_transpose_eq (by simp) (by simp)⟩

local notation "Spad" => leakStart * leakStartᵀ
local notation "Wk" => leakDir * leakStartᵀ
local notation "Wl" => leakStart * leakDirᵀ

private theorem leakLeft_mul_kCurve (t : ℝ) :
    leakLeft * (leakCurve t * leakStartᵀ) = Wk := by
  have h1 : leakLeft * leakStart = leakDir := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [leakLeft, leakStart, leakDir, Matrix.mul_apply]
  have h2 : leakLeft * leakDir = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [leakLeft, leakDir, Matrix.mul_apply]
  rw [← Matrix.mul_assoc, leakCurve, Matrix.mul_add, Matrix.mul_smul, h1, h2, smul_zero,
    add_zero]

private theorem leakLeft_mul_paddedCoeff : leakLeft * Spad = Wk := by
  simpa [leakCurve] using leakLeft_mul_kCurve 0

private theorem kCurve_eq (t : ℝ) : leakCurve t * leakStartᵀ = Spad + t • Wk := by
  rw [leakCurve, Matrix.add_mul, Matrix.smul_mul]

private theorem lCurve_eq (t : ℝ) : leakStart * (leakCurve t)ᵀ = Spad + t • Wl := by
  rw [leakCurve, Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.mul_smul]

private theorem lField_lCurve (t : ℝ) :
    lField I₂ (fun _ Y => leakLeft * Y) t (leakStart * (leakCurve t)ᵀ) = Wl := by
  have e : (leakStart * (leakCurve t)ᵀ)ᵀ = leakCurve t * leakStartᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [lField, Matrix.one_mul, Matrix.mul_one]
  rw [e, leakLeft_mul_kCurve, Matrix.transpose_mul, Matrix.transpose_transpose]

private theorem paddedCoeff_transpose : Spadᵀ = Spad := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

private theorem lField_paddedCoeff (t : ℝ) : lField I₂ (fun _ Y => leakLeft * Y) t Spad = Wl := by
  simp only [lField, Matrix.one_mul, Matrix.mul_one]
  rw [paddedCoeff_transpose, leakLeft_mul_paddedCoeff, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- **Non-vacuity of `error_le_of_twoSided_of_leaks_eq_zero`.**  The field `Y ↦ E₂₁ Y` on
`2 × 2` matrices, written as `0 Y + Y 0 + E₂₁ Y I₂` (`L = ‖E₂₁‖`), from `e₁ e₁ᵀ` in the padded
bases `Ũ = Ṽ = I₂` (coefficients `S̃ = e₁ e₁ᵀ`); K-step, S-step and exact solution
`(e₁ + t e₂) e₁ᵀ`, L-step `e₁ (e₁ + t e₂)ᵀ`, auxiliary flows `P = Q = I₂`, `Z = Zr = 0`,
`a = b = κ₂ = π = 0`, `ℓ_C = ℓ_D = 0`, `M₂ = 0`.  The step is exact, so the left-hand side is
`0`; the example shows that the hypotheses hold with a start whose unpadded basis `e₁` leaks
(`leak_leakLeft`), not that the bound is attained. -/
example (h : ℝ) (hh : 0 ≤ h) : ∃ Γ₁ Γ₂ : ℝ,
    ‖I₂ * (leakCurve h * leakStartᵀ) * I₂ᵀ - leakCurve h * leakStartᵀ‖
      ≤ (Real.exp (‖leakLeft‖ * h) - 1)
          * (2 * (h * Real.exp (‖leakLeft‖ * h) * (h * Γ₁ * (0 * 0) + h ^ 2 * Γ₂)) + 0 * h ^ 2)
        + 2 * (h * Real.exp (‖leakLeft‖ * h) * (h * Γ₁ * (0 * 0) + h ^ 2 * Γ₂)) + 0 := by
  have hdK : ∀ t, HasDerivAt (fun s => leakCurve s * leakStartᵀ) Wk t := fun t => by
    have h1 := ((hasDerivAt_id t).smul_const Wk).const_add Spad
    rw [one_smul] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => kCurve_eq s)
  have hdL : ∀ t, HasDerivAt (fun s => leakStart * (leakCurve s)ᵀ) Wl t := fun t => by
    have h1 := ((hasDerivAt_id t).smul_const Wl).const_add Spad
    rw [one_smul] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => lCurve_eq s)
  have ode : ∀ {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ}
      {Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {Y' : Matrix (Fin 2) (Fin 2) ℝ},
      (∀ t, HasDerivAt Y Y' t) → (∀ t, G t (Y t) = Y') → ODESolution G Y 0 h :=
    fun hY hG => ⟨fun t _ => (hY t).continuousAt.continuousWithinAt,
      fun t _ => by rw [hG t]; exact (hY t).hasDerivWithinAt⟩
  have hconst : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, ∀ t, HasDerivAt (fun _ : ℝ => X) 0 t :=
    fun X t => hasDerivAt_const t X
  have hFA : (fun t => leakLeft * (leakCurve t * leakStartᵀ)) = fun _ => Wk :=
    funext leakLeft_mul_kCurve
  have hF : IsLipschitzField (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => leakLeft * Y)
      ‖leakLeft‖ := fun _ X Y => by
    change ‖leakLeft * X - leakLeft * Y‖ ≤ ‖leakLeft‖ * ‖X - Y‖
    rw [← Matrix.mul_sub]
    exact Frobenius.norm_mul_le _ _
  have hK₁ : ∀ t ∈ Icc (0 : ℝ) h,
      ‖leakCurve t * leakStartᵀ - I₂ * Spad‖ ≤ (‖Wk‖ + ‖Wl‖) * (t - 0) := fun t ht => by
    rw [kCurve_eq, Matrix.one_mul, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1,
      sub_zero]
    nlinarith [mul_nonneg ht.1 (norm_nonneg Wl)]
  have hL₁ : ∀ t ∈ Icc (0 : ℝ) h,
      ‖leakStart * (leakCurve t)ᵀ - I₂ * Spadᵀ‖ ≤ (‖Wk‖ + ‖Wl‖) * (t - 0) := fun t ht => by
    rw [paddedCoeff_transpose, lCurve_eq, Matrix.one_mul, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.1, sub_zero]
    nlinarith [mul_nonneg ht.1 (norm_nonneg Wk)]
  have hstep : IsRankAdaptiveStep (fun _ Y => leakLeft * Y) 0 0 h I₂ Spad I₂ I₂ I₂
      (fun t => leakCurve t * leakStartᵀ) (fun t => leakStart * (leakCurve t)ᵀ)
      (fun t => leakCurve t * leakStartᵀ) (I₂ * (leakCurve h * leakStartᵀ) * I₂ᵀ) :=
    { orthU₀ := by simp
      orthV₀ := by simp
      kSol := ode hdK fun t => by
        simp only [kField, Matrix.transpose_one, Matrix.mul_one, leakLeft_mul_kCurve]
      kStart := by simp [kCurve_eq]
      lSol := ode hdL fun t => lField_lCurve t
      lStart := by simp [lCurve_eq]
      orthUa := by simp
      kCap := by simp
      augU := by simp
      orthVa := by simp
      lCap := by simp
      augV := by simp
      sSol := ode hdK fun t => by
        simp only [sField, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
          leakLeft_mul_kCurve]
      sStart := by simp [kCurve_eq]
      trunc := by simp }
  exact ⟨_, _, error_le_of_twoSided_of_leaks_eq_zero (F := fun _ Y => leakLeft * Y) (𝒜 := 0)
    (ℬ := 0) (C := leakLeft) (D := 1) (a := 0) (b := 0) (c := ‖leakLeft‖) (δ := ‖I₂‖)
    (σ := ‖Spad‖) (κ := ‖Wk‖ + ‖Wl‖) (κ₂ := 0) (π := 0) (ℓC := 0) (ℓD := 0) (M₂ := 0)
    (a₂ := fun _ => 0) (P := fun _ => 1) (Z := fun _ => 0) (Q := fun _ => 1)
    (Zr := fun _ => 0) (fun _ Y => by simp) hF (norm_nonneg _) (zero_add h).symm hh hstep
    (ode hdK leakLeft_mul_kCurve) (by simp [kCurve_eq])
    (ode (hconst 1) fun _ => by simp) (by simp)
    (ode (hconst 0) fun _ => by simp) rfl
    (ode (hconst 1) fun _ => by simp) rfl
    (ode (hconst 0) fun _ => by simp) rfl
    (by rw [hFA]; exact continuousOn_const)
    (fun s _ => by rw [hFA]; exact hasDerivWithinAt_const _ _ _)
    (fun _ _ => by simp) (by simp) (by simp) le_rfl le_rfl le_rfl
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) le_rfl le_rfl
    hK₁ (fun t _ => by simp [kField, kCurve_eq, leakLeft_mul_paddedCoeff])
    hL₁ (fun t _ => by simp [lCurve_eq, lField_paddedCoeff])
    (fun t _ => by simp) (fun t _ => by simp) (by simp) (by simp) (by simp) (by simp)
    (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _) rfl⟩

end PaddedExample

end AugmentationRank

end LeanDLRA
