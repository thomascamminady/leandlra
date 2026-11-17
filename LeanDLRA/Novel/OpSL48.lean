import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius

/-!
# Projected local conservation laws in Vlasov–Poisson DLRA: what they are, and how a
continuity defect feeds the electric energy (OP-SL-48)

Open problem OP-SL-48 of `docs/catalogue/survey/open-problems.json` (Einkemmer–Lubich, arXiv
1807.02338, Sec. 6, Figs. 1–2): enforcing the *projected* local conservation laws
`P_X (∂ₜ ρ + ∇·j) = 0`, `P_X (∂ₜ j + ∇·m₂ + E ρ) = 0` in the substeps of the projector-splitting
integrator gives a qualitatively correct long-time electric energy (two-stream instability, rank
15, `t = 300`), whereas the uncorrected scheme and the globally corrected one lose it.  No theory
is given there.

This module isolates the exact mechanism on the discrete model: `f ∈ ℝ^{x × v}` with a skew
derivative matrix `D` in space, `f = X S Wᵀ` with orthonormal `X`, `W`, velocity moments `f U`
(columns of `U`: the weights of `1`, `v`, …), the discrete Vlasov field
`F(f) = -D f V + diag(E) f Dᵥᵀ` (`vlasovField`), Gauss's law `D² φ = ρ - c` with `c ∈ ker D` and
`E = -D φ`, electric energy `½ ⟪E, E⟫`.

## What is proved

* **The projected laws are the moment laws of the unsplit Dirac–Frenkel flow.**  For the
  tangent projector `P(f) Z = X Xᵀ Z - X Xᵀ Z W Wᵀ + Z W Wᵀ` one has `Xᵀ P(f) Z = Xᵀ Z`
  (`transpose_mul_tangentProj`), hence `Xᵀ (P(f) Z) U = Xᵀ Z U` for *every* weight matrix `U`
  (`tangentProj_moment`, `hasDerivAt_moment`), with defect exactly the normal part
  `-(1 - X Xᵀ) Z (1 - W Wᵀ) U` (`tangentProj_moment_defect`).  So the projected ODE
  `∂ₜ f = P(f) F(f)` satisfies the projected continuity, momentum and every higher moment law
  without any correction; the laws of arXiv 1807.02338 are those of the unsplit flow.
* **The splitting breaks them, with explicit defects.**  The K-, backward S- and L-step fields
  `Z W Wᵀ`, `-(X Xᵀ Z W Wᵀ)`, `X Xᵀ Z` sum to `P(f) Z` (`kField_add_sField_add_lField`); the
  projected moment defects are `-Xᵀ Z (1 - W Wᵀ) U`, `+Xᵀ Z (1 - W Wᵀ) U` and `0`
  (`kField_moment_defect`, `sField_moment_defect`, `lField_moment`, `substep_defects_sum`).  The
  L-step therefore needs no correction for *any* moment (the paper's `b_i = 0` of Step 3; the
  same identity gives `d_i = 0`), and the K-step needs none when the weights lie in the velocity
  basis (`kField_moment_of_mem`, the mechanism of Einkemmer–Joseph 2021 and arXiv 2206.09374).
* **What the correction does.**  With the correction `X Λ Wᵀ` of eqs. (13), (17), the projected
  laws hold iff `Λ (Wᵀ U) = Xᵀ Z (1 - W Wᵀ) U` (`kFieldCorr_law_iff`, the systems (16)), and then
  the moments of the corrected K-field are *exactly* those of the tangent projector,
  `(K-field + X Λ Wᵀ) U = P(f) Z U` (`kFieldCorr_moment_eq_tangentProj`,
  `kFieldCorr_mulVec_eq_tangentProj`), while the corrected S-step has the moments `-(X Xᵀ Z U)`
  of the negative L-step (`sFieldCorr_moment_eq`).  The minimal-norm multiplier is
  `lamMin = B (AᵀA)⁻¹ Aᵀ` (`lamMin_mul`, `lamMin_norm_le`; see also the literature slice of
  arXiv 1807.02338 for Remarks 1–2).
* **How a continuity defect reaches the electric energy.**  If `ρ' = -D j + s` then
  `d/dt ½ ⟪E, E⟫ = ⟪E, j⟫ - ⟪φ, s⟫` (`electric_rate`, `hasDerivAt_electricEnergy`): the
  exchange term `⟪E, j⟫` of the full system, plus the defect tested against the *potential*.
  Under the projected continuity law `Xᵀ s = 0` only the part of `φ` outside the spatial basis
  sees the defect, `⟪φ, s⟫ = ⟪(1 - X Xᵀ) φ, s⟫`, `⟪φ, s⟫² ≤ ‖(1 - X Xᵀ) φ‖² ‖s‖²`
  (`dotProduct_eq_of_proj`, `sq_dotProduct_le_of_proj`); for the tangent projector the error
  vanishes whenever `X Xᵀ φ = φ` (`dotProduct_tangent_defect_eq_zero`).  Since `ρ = f w` always
  lies in `span X` and `φ` is two derivatives smoother than `ρ`, this is the quantity the local
  correction makes small, and the one the uncorrected K-step does not control.
* **A sharp instance** (`Fin 4 × Fin 4`, rank 3, rational data): `D₀` the periodic central
  difference, `X₀` three Hadamard vectors, `W₀ = [e₀ e₁ e₂]` (so `1 ∉ span W₀`),
  `f₀ = X₀ S₀ W₀ᵀ`, `ρ₀ = (2, 1, 1, 0)`, `φ₀ = -(1, 1, -1, -1)/2`, `E₀ = (1, -1, -1, 1)/2`,
  electric energy `1/2` (`energy₀`).  The full model has `s = 0` and rate `⟪E₀, j₀⟫ = 0`
  (`instance_full`); the corrected K-step, for every multiplier solving the (1, v)-system, has
  rate `0` (`instance_corrected`, solvable by `instance_multiplier_exists`); the uncorrected
  K-step has `Xᵀ s₀ = (0, 1/4, 0) ≠ 0` and produces electric energy at the rate `1/4`, i.e. half
  the electric energy per unit time (`instance_uncorrected`, with explicit Poisson data
  `instance_poisson_rate`).

## What stays open

The identities explain *where* the uncorrected scheme injects or removes electric energy (through
`⟪P_X φ, s⟫`, of size `O(‖φ‖ ‖F(f)‖ ‖(1 - W Wᵀ) 1‖)` with no smallness from the basis) and that
the corrected and the unsplit flows do not.  They do not prove that the electric energy of the
corrected scheme stays bounded over long times, nor the sign of the drift: this needs nonlinear
Vlasov–Poisson analysis.  In a throwaway Lie-splitting discretization of the two-stream problem
(rank 15, `64 × 128`, `τ = 0.025`) the uncorrected scheme lost two orders of magnitude of electric
energy by `t = 300`, as in the paper; the local correction kept it to `t ≈ 220` and then lost it
too, while a velocity basis containing `1, v` kept it throughout.  These observations are not
part of the formal content.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpSL48

open LeanDLRA LeanDLRA.Frobenius Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {x v r r' m : Type*} [Fintype x] [Fintype v] [Fintype r] [Fintype r'] [Fintype m]
  [DecidableEq x] [DecidableEq v] [DecidableEq r] [DecidableEq r']

/-! ### The tangent projector satisfies every projected moment law -/

section Moments

variable {X : Matrix x r ℝ} {W : Matrix v r' ℝ}

/-- `Xᵀ P(f) Z = Xᵀ Z`: the spatial basis does not see the tangent projection. -/
theorem transpose_mul_tangentProj (hX : Xᵀ * X = 1) (W : Matrix v r' ℝ) (Z : Matrix x v ℝ) :
    Xᵀ * tangentProj X W Z = Xᵀ * Z := by
  rw [tangentProj_apply]
  simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  abel

/-- `P(f) Z W = Z W`: the velocity basis does not see the tangent projection. -/
theorem tangentProj_mul_right (X : Matrix x r ℝ) (hW : Wᵀ * W = 1) (Z : Matrix x v ℝ) :
    tangentProj X W Z * W = Z * W := by
  rw [tangentProj_apply]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hW, Matrix.mul_one]
  abel

/-- **Projected moment laws of the tangent projector.**  For every matrix of velocity weights `U`
(columns `1`, `v`, `v²`, …), the moments of `P(f) Z` tested against the spatial basis agree with
those of `Z`: `Xᵀ (P(f) Z) U = Xᵀ Z U`. -/
theorem tangentProj_moment (hX : Xᵀ * X = 1) (W : Matrix v r' ℝ) (Z : Matrix x v ℝ)
    (U : Matrix v m ℝ) : Xᵀ * (tangentProj X W Z * U) = Xᵀ * (Z * U) := by
  rw [← Matrix.mul_assoc, transpose_mul_tangentProj hX, Matrix.mul_assoc]

/-- The moment defect of the tangent projector is the normal part:
`P(f) Z U - Z U = -(1 - X Xᵀ) Z (1 - W Wᵀ) U`. -/
theorem tangentProj_moment_defect (X : Matrix x r ℝ) (W : Matrix v r' ℝ) (Z : Matrix x v ℝ)
    (U : Matrix v m ℝ) :
    tangentProj X W Z * U - Z * U = -((1 - X * Xᵀ) * Z * (1 - W * Wᵀ) * U) := by
  rw [tangentProj_apply]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

/-- Along a differentiable path `f` with `f' = P(f) Z`, the moments `f U` move with velocity
`P(f) Z U`, whose projection onto the spatial basis is `Xᵀ Z U`. -/
theorem hasDerivAt_moment {f : ℝ → Matrix x v ℝ} {Z : Matrix x v ℝ} {t : ℝ}
    (hf : HasDerivAt f (tangentProj X W Z) t) (hX : Xᵀ * X = 1) (U : Matrix v m ℝ) :
    HasDerivAt (fun τ => f τ * U) (tangentProj X W Z * U) t ∧
      Xᵀ * (tangentProj X W Z * U) = Xᵀ * (Z * U) :=
  ⟨hasDerivAt_mul_const U hf, tangentProj_moment hX W Z U⟩

end Moments

/-! ### The three substeps of the projector splitting and their moment defects -/

section Substeps

variable (X : Matrix x r ℝ) (W : Matrix v r' ℝ)

/-- The K-step field: the velocity basis is frozen, `Z ↦ Z W Wᵀ`. -/
def kField (Z : Matrix x v ℝ) : Matrix x v ℝ := Z * (W * Wᵀ)

/-- The (backward) S-step field, `Z ↦ -(X Xᵀ Z W Wᵀ)`. -/
def sField (Z : Matrix x v ℝ) : Matrix x v ℝ := -(X * Xᵀ * Z * (W * Wᵀ))

/-- The L-step field: the spatial basis is frozen, `Z ↦ X Xᵀ Z`. -/
def lField (Z : Matrix x v ℝ) : Matrix x v ℝ := X * Xᵀ * Z

/-- The Lie splitting `K`, `S` (backward), `L` reassembles the tangent projector. -/
theorem kField_add_sField_add_lField (Z : Matrix x v ℝ) :
    kField W Z + sField X W Z + lField X Z = tangentProj X W Z := by
  rw [tangentProj_apply, kField, sField, lField]
  simp only [Matrix.mul_assoc]
  abel

variable {X W}

/-- Moment defect of the K-step: `Xᵀ (Z W Wᵀ) U - Xᵀ Z U = -Xᵀ Z (1 - W Wᵀ) U`, which is in
general not zero. -/
theorem kField_moment_defect (Z : Matrix x v ℝ) (U : Matrix v m ℝ) :
    Xᵀ * (kField W Z * U) - Xᵀ * (Z * U) = -(Xᵀ * Z * (1 - W * Wᵀ) * U) := by
  rw [kField]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- If the velocity basis contains the weights (`W Wᵀ U = U`: `1`, `v` in the velocity basis,
Einkemmer–Joseph 2021), the K-step satisfies the *unprojected* moment law exactly. -/
theorem kField_moment_of_mem (Z : Matrix x v ℝ) {U : Matrix v m ℝ} (hU : W * Wᵀ * U = U) :
    kField W Z * U = Z * U := by
  rw [kField, Matrix.mul_assoc, hU]

/-- Moment defect of the backward S-step: `Xᵀ (S-field) U + Xᵀ Z U = Xᵀ Z (1 - W Wᵀ) U`. -/
theorem sField_moment_defect (hX : Xᵀ * X = 1) (Z : Matrix x v ℝ) (U : Matrix v m ℝ) :
    Xᵀ * (sField X W Z * U) + Xᵀ * (Z * U) = Xᵀ * Z * (1 - W * Wᵀ) * U := by
  rw [sField]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Xᵀ X, hX, Matrix.one_mul]
  abel

/-- The L-step satisfies every projected moment law without correction: `Xᵀ (X Xᵀ Z) U = Xᵀ Z U`
(the paper's `b_i = 0` in Step 3; the same holds for the momentum moment). -/
theorem lField_moment (hX : Xᵀ * X = 1) (Z : Matrix x v ℝ) (U : Matrix v m ℝ) :
    Xᵀ * (lField X Z * U) = Xᵀ * (Z * U) := by
  rw [lField]
  simp only [← Matrix.mul_assoc, hX, Matrix.one_mul]

/-- The sum of the three substep defects is the defect of the tangent projector. -/
theorem substep_defects_sum (Z : Matrix x v ℝ) (U : Matrix v m ℝ) :
    (kField W Z * U - Z * U) + (sField X W Z * U + lField X Z * U) =
      tangentProj X W Z * U - Z * U := by
  rw [← kField_add_sField_add_lField X W Z]
  simp only [Matrix.add_mul]
  abel

end Substeps

/-! ### The Einkemmer–Lubich correction `Σ λ_ij X_i V_j` -/

section Correction

variable (X : Matrix x r ℝ) (W : Matrix v r' ℝ)

/-- The corrected K-step field `Z W Wᵀ + X Λ Wᵀ` (arXiv 1807.02338, eq. (13)). -/
def kFieldCorr (Λ : Matrix r r' ℝ) (Z : Matrix x v ℝ) : Matrix x v ℝ :=
  Z * (W * Wᵀ) + X * Λ * Wᵀ

/-- The corrected backward S-step field `-(X Xᵀ Z W Wᵀ) - X Λ Wᵀ` (eq. (17)). -/
def sFieldCorr (Λ : Matrix r r' ℝ) (Z : Matrix x v ℝ) : Matrix x v ℝ :=
  -(X * Xᵀ * Z * (W * Wᵀ)) - X * Λ * Wᵀ

variable {X W}

/-- Projected moments of the corrected K-step. -/
theorem kFieldCorr_moment (hX : Xᵀ * X = 1) (Λ : Matrix r r' ℝ) (Z : Matrix x v ℝ)
    (U : Matrix v m ℝ) :
    Xᵀ * (kFieldCorr X W Λ Z * U) = Xᵀ * (Z * (W * Wᵀ * U)) + Λ * (Wᵀ * U) := by
  rw [kFieldCorr, Matrix.add_mul, Matrix.mul_add]
  congr 1
  · simp only [Matrix.mul_assoc]
  · simp only [← Matrix.mul_assoc, hX, Matrix.one_mul]

/-- **The multiplier equation.**  The corrected K-step satisfies the projected moment laws for
the weights `U` iff `Λ (Wᵀ U) = Xᵀ Z (1 - W Wᵀ) U` (the systems (16) of arXiv 1807.02338, one per
row). -/
theorem kFieldCorr_law_iff (hX : Xᵀ * X = 1) (Λ : Matrix r r' ℝ) (Z : Matrix x v ℝ)
    (U : Matrix v m ℝ) :
    Xᵀ * (kFieldCorr X W Λ Z * U) = Xᵀ * (Z * U) ↔
      Λ * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U := by
  rw [kFieldCorr_moment hX]
  constructor
  · intro h
    have : Λ * (Wᵀ * U) = Xᵀ * (Z * U) - Xᵀ * (Z * (W * Wᵀ * U)) := by
      rw [← h]; abel
    rw [this]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  · intro h
    rw [h]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel

/-- **What the correction does.**  Whenever the multiplier equation holds, the moments `U` of the
corrected K-step field are *exactly* those of the tangent projector: the correction turns the
K-step into the unsplit Dirac–Frenkel flow as far as the moments `U` are concerned. -/
theorem kFieldCorr_moment_eq_tangentProj {Λ : Matrix r r' ℝ} {Z : Matrix x v ℝ}
    {U : Matrix v m ℝ} (hΛ : Λ * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U) :
    kFieldCorr X W Λ Z * U = tangentProj X W Z * U := by
  rw [kFieldCorr, Matrix.add_mul, Matrix.mul_assoc (X * Λ), Matrix.mul_assoc X Λ, hΛ,
    tangentProj_apply]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- The corrected backward S-step has the moments `-(X Xᵀ Z U)`, the negative of the L-step's. -/
theorem sFieldCorr_moment_eq {Λ : Matrix r r' ℝ} {Z : Matrix x v ℝ} {U : Matrix v m ℝ}
    (hΛ : Λ * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U) :
    sFieldCorr X W Λ Z * U = -(lField X Z * U) := by
  rw [sFieldCorr, lField, Matrix.sub_mul, Matrix.mul_assoc (X * Λ), Matrix.mul_assoc X Λ, hΛ]
  simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- The minimal-norm multiplier `Λ₀ = B (Aᵀ A)⁻¹ Aᵀ` with `A = Wᵀ U` and
`B = Xᵀ Z (1 - W Wᵀ) U` (the pseudo-inverse solution of arXiv 1807.02338, Sec. 3). -/
noncomputable def lamMin [DecidableEq m] (X : Matrix x r ℝ) (W : Matrix v r' ℝ)
    (U : Matrix v m ℝ) (Z : Matrix x v ℝ) : Matrix r r' ℝ :=
  Xᵀ * Z * (1 - W * Wᵀ) * U * ((Wᵀ * U)ᵀ * (Wᵀ * U))⁻¹ * (Wᵀ * U)ᵀ

/-- If `Wᵀ U` has full column rank (`(Wᵀ U)ᵀ (Wᵀ U)` invertible; `r ≥ 1 + d` and independent
moment rows), `lamMin` solves the multiplier equation. -/
theorem lamMin_mul {U : Matrix v m ℝ} [DecidableEq m] (hA : IsUnit ((Wᵀ * U)ᵀ * (Wᵀ * U)).det)
    (Z : Matrix x v ℝ) : lamMin X W U Z * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U := by
  rw [lamMin, Matrix.mul_assoc _ (Wᵀ * U)ᵀ, Matrix.mul_assoc _ _ ((Wᵀ * U)ᵀ * (Wᵀ * U)),
    Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

/-- `lamMin` has minimal Frobenius norm among all solutions of the multiplier equation:
`‖Λ‖² = ‖Λ₀‖² + ‖Λ - Λ₀‖²`. -/
theorem lamMin_norm_le {U : Matrix v m ℝ} [DecidableEq m] (hA : IsUnit ((Wᵀ * U)ᵀ * (Wᵀ * U)).det)
    (Z : Matrix x v ℝ) {Λ : Matrix r r' ℝ} (hΛ : Λ * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U) :
    ‖Λ‖ ^ 2 = ‖lamMin X W U Z‖ ^ 2 + ‖Λ - lamMin X W U Z‖ ^ 2 ∧ ‖lamMin X W U Z‖ ≤ ‖Λ‖ := by
  have hN : (Λ - lamMin X W U Z) * (Wᵀ * U) = 0 := by
    rw [Matrix.sub_mul, hΛ, lamMin_mul hA, sub_self]
  have horth : ⟪lamMin X W U Z, Λ - lamMin X W U Z⟫ = 0 := by
    rw [show ⟪lamMin X W U Z, Λ - lamMin X W U Z⟫ =
        ⟪(Xᵀ * Z * (1 - W * Wᵀ) * U * ((Wᵀ * U)ᵀ * (Wᵀ * U))⁻¹) * (Wᵀ * U)ᵀ,
          Λ - lamMin X W U Z⟫ from rfl,
      inner_mul_right, Matrix.transpose_transpose, hN, inner_zero_right]
  have hpyth : ‖Λ‖ ^ 2 = ‖lamMin X W U Z‖ ^ 2 + ‖Λ - lamMin X W U Z‖ ^ 2 := by
    have : Λ = lamMin X W U Z + (Λ - lamMin X W U Z) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real, horth]; ring
  refine ⟨hpyth, ?_⟩
  nlinarith [sq_nonneg ‖Λ - lamMin X W U Z‖, norm_nonneg (lamMin X W U Z), norm_nonneg Λ]

/-- The multiplier equation for the weight matrix `U` implies the vector form for each of its
columns `u = U eᵢ`: `Λ (Wᵀ u) = Xᵀ Z (u - W Wᵀ u)`. -/
theorem multiplier_col {Λ : Matrix r r' ℝ} {Z : Matrix x v ℝ} {U : Matrix v m ℝ} [DecidableEq m]
    (hΛ : Λ * (Wᵀ * U) = Xᵀ * Z * (1 - W * Wᵀ) * U) (i : m) :
    Λ *ᵥ (Wᵀ *ᵥ (U *ᵥ Pi.single i 1)) =
      Xᵀ *ᵥ (Z *ᵥ ((U *ᵥ Pi.single i 1) - W *ᵥ (Wᵀ *ᵥ (U *ᵥ Pi.single i 1)))) := by
  have h := congrArg (fun M => M *ᵥ Pi.single i (1 : ℝ)) hΛ
  simp only [← mulVec_mulVec] at h
  rw [h, sub_mulVec, one_mulVec, ← mulVec_mulVec]

/-- Vector form of `kFieldCorr_moment_eq_tangentProj`: for a single weight `u`, the corrected
K-step moves the moment `f u` exactly as the tangent projector does. -/
theorem kFieldCorr_mulVec_eq_tangentProj {Λ : Matrix r r' ℝ} {Z : Matrix x v ℝ} {u : v → ℝ}
    (hΛ : Λ *ᵥ (Wᵀ *ᵥ u) = Xᵀ *ᵥ (Z *ᵥ (u - W *ᵥ (Wᵀ *ᵥ u)))) :
    kFieldCorr X W Λ Z *ᵥ u = tangentProj X W Z *ᵥ u := by
  rw [kFieldCorr, add_mulVec, tangentProj_apply, sub_mulVec, add_mulVec]
  simp only [← mulVec_mulVec]
  rw [hΛ]
  simp only [mulVec_sub]
  abel

end Correction

/-! ### The electric energy sees a continuity defect only through the potential -/

section Electric

variable {D : Matrix x x ℝ}

private theorem mulVec_dotProduct' {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℝ)
    (a : β → ℝ) (b : α → ℝ) : (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Aᵀ *ᵥ b) := by
  rw [dotProduct_mulVec a Aᵀ b, vecMul_transpose]

private theorem dotProduct_mulVec' {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℝ)
    (a : α → ℝ) (b : β → ℝ) : a ⬝ᵥ (A *ᵥ b) = (Aᵀ *ᵥ a) ⬝ᵥ b := by
  rw [dotProduct_mulVec a A b, mulVec_transpose]

/-- **Electric-energy production identity.**  Let `D` be skew (`Dᵀ = -D`, a periodic derivative
matrix), let the potential solve the discrete Poisson equation `D² φ = ρ - c` with `c` in the
kernel of `D` (the background/mean part) and `φ ⊥ ker D`, and let `E = -D φ`.  If the charge
density moves with velocity `ρ' = -D j + s`, where `j` is the current and `s` the continuity
defect, then the rate of the electric energy `½ ⟪E, E⟫` is

  `⟪E, E'⟫ = ⟪E, j⟫ - ⟪φ, s⟫`.

`⟪E, j⟫` is the exchange with the kinetic energy of the full Vlasov–Poisson system; the defect
enters only through its inner product with the potential. -/
theorem electric_rate (hD : Dᵀ = -D) {ρ' j s φ φ' c' : x → ℝ}
    (hP : D *ᵥ (D *ᵥ φ') = ρ' - c') (hc : D *ᵥ c' = 0)
    (hφ : ∀ z, D *ᵥ z = 0 → φ ⬝ᵥ z = 0) (hρ : ρ' = -(D *ᵥ j) + s) :
    (-(D *ᵥ φ)) ⬝ᵥ (-(D *ᵥ φ')) = (-(D *ᵥ φ)) ⬝ᵥ j - φ ⬝ᵥ s := by
  have h1 : (D *ᵥ φ) ⬝ᵥ (D *ᵥ φ') = -(φ ⬝ᵥ ρ') := by
    rw [mulVec_dotProduct', hD, neg_mulVec, hP, dotProduct_neg, dotProduct_sub, hφ c' hc,
      sub_zero]
  have h2 : (D *ᵥ φ) ⬝ᵥ j = -(φ ⬝ᵥ (D *ᵥ j)) := by
    rw [mulVec_dotProduct', hD, neg_mulVec, dotProduct_neg]
  rw [neg_dotProduct, dotProduct_neg, neg_neg, h1, neg_dotProduct, h2, hρ, dotProduct_add,
    dotProduct_neg]
  ring

/-- Under the projected continuity law `Xᵀ s = 0`, the production error is seen only by the
part of the potential outside the spatial basis: `⟪φ, s⟫ = ⟪(1 - X Xᵀ) φ, s⟫`. -/
theorem dotProduct_eq_of_proj {X : Matrix x r ℝ} {s φ : x → ℝ} (hs : Xᵀ *ᵥ s = 0) :
    φ ⬝ᵥ s = (φ - X *ᵥ (Xᵀ *ᵥ φ)) ⬝ᵥ s := by
  rw [sub_dotProduct, mulVec_dotProduct', hs, dotProduct_zero, sub_zero]

/-- Cauchy–Schwarz form: under the projected law the production error is bounded by the part of
the potential outside the spatial basis, `⟪φ, s⟫² ≤ ‖(1 - X Xᵀ) φ‖² ‖s‖²`. -/
theorem sq_dotProduct_le_of_proj {X : Matrix x r ℝ} {s φ : x → ℝ} (hs : Xᵀ *ᵥ s = 0) :
    (φ ⬝ᵥ s) ^ 2 ≤ ((φ - X *ᵥ (Xᵀ *ᵥ φ)) ⬝ᵥ (φ - X *ᵥ (Xᵀ *ᵥ φ))) * (s ⬝ᵥ s) := by
  rw [dotProduct_eq_of_proj hs]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (φ - X *ᵥ (Xᵀ *ᵥ φ)) s
  simpa only [dotProduct, pow_two] using this

/-- The tangent projector produces no electric energy error when the potential lies in the
spatial basis: `⟪φ, (P(f) Z - Z) w⟫ = 0` if `X Xᵀ φ = φ`. -/
theorem dotProduct_tangent_defect_eq_zero {X : Matrix x r ℝ} {W : Matrix v r' ℝ}
    (Z : Matrix x v ℝ) {φ : x → ℝ} (hφ : X *ᵥ (Xᵀ *ᵥ φ) = φ) (w : v → ℝ) :
    φ ⬝ᵥ ((tangentProj X W Z - Z) *ᵥ w) = 0 := by
  have h : tangentProj X W Z - Z = -((1 - X * Xᵀ) * (Z * (1 - W * Wᵀ))) := by
    rw [tangentProj_apply]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [h, neg_mulVec, dotProduct_neg, ← mulVec_mulVec, dotProduct_mulVec', Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose, sub_mulVec,
    one_mulVec, ← mulVec_mulVec, hφ, sub_self, zero_dotProduct, neg_zero]

private theorem hasDerivAt_mulVec {φ : ℝ → x → ℝ} {φ' : x → ℝ} {t : ℝ} (A : Matrix x x ℝ)
    (h : HasDerivAt φ φ' t) : HasDerivAt (fun τ => A *ᵥ φ τ) (A *ᵥ φ') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have := HasDerivAt.sum (u := (Finset.univ : Finset x))
    fun k _ => (hasDerivAt_pi.1 h k).const_mul (A i k)
  convert this using 1
  · funext τ
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  · simp [Matrix.mulVec, dotProduct]

private theorem hasDerivAt_half_dotProduct_self {E : ℝ → x → ℝ} {E' : x → ℝ} {t : ℝ}
    (h : HasDerivAt E E' t) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * (E τ ⬝ᵥ E τ)) (E t ⬝ᵥ E') t := by
  have := (HasDerivAt.sum (u := (Finset.univ : Finset x))
    fun i _ => (hasDerivAt_pi.1 h i).mul (hasDerivAt_pi.1 h i)).const_mul (1 / 2 : ℝ)
  convert this using 1
  · funext τ
    simp [dotProduct, Finset.sum_apply]
  · simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **Electric energy along a trajectory.**  With `D` skew, Gauss's law `D² φ(τ) = ρ(τ) - c(τ)`,
`D c(τ) = 0`, `φ(t) ⊥ ker D`, and `ρ'(t) = -D j + s`, the electric energy `½ ⟪E, E⟫`,
`E = -D φ`, has derivative `⟪E, j⟫ - ⟪φ, s⟫` at `t`. -/
theorem hasDerivAt_electricEnergy (hD : Dᵀ = -D) {φ ρ c : ℝ → x → ℝ} {φ' ρ' c' j s : x → ℝ}
    {t : ℝ} (hφt : HasDerivAt φ φ' t) (hρt : HasDerivAt ρ ρ' t) (hct : HasDerivAt c c' t)
    (hP : ∀ τ, D *ᵥ (D *ᵥ φ τ) = ρ τ - c τ) (hker : ∀ τ, D *ᵥ c τ = 0)
    (hφ : ∀ z, D *ᵥ z = 0 → φ t ⬝ᵥ z = 0) (hρ : ρ' = -(D *ᵥ j) + s) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * ((-(D *ᵥ φ τ)) ⬝ᵥ (-(D *ᵥ φ τ))))
      ((-(D *ᵥ φ t)) ⬝ᵥ j - φ t ⬝ᵥ s) t := by
  have hE : HasDerivAt (fun τ => -(D *ᵥ φ τ)) (-(D *ᵥ φ')) t := (hasDerivAt_mulVec D hφt).neg
  have hP' : D *ᵥ (D *ᵥ φ') = ρ' - c' := by
    have h1 : HasDerivAt (fun τ => D *ᵥ (D *ᵥ φ τ)) (D *ᵥ (D *ᵥ φ')) t :=
      hasDerivAt_mulVec D (hasDerivAt_mulVec D hφt)
    have h1' : HasDerivAt (fun τ => ρ τ - c τ) (D *ᵥ (D *ᵥ φ')) t := by
      simpa only [hP] using h1
    exact h1'.unique (hρt.sub hct)
  have hc' : D *ᵥ c' = 0 := by
    have h1 : HasDerivAt (fun τ => D *ᵥ c τ) (D *ᵥ c') t := hasDerivAt_mulVec D hct
    have h1' : HasDerivAt (fun _ : ℝ => (0 : x → ℝ)) (D *ᵥ c') t := by
      simpa only [hker] using h1
    exact h1'.unique (hasDerivAt_const t 0)
  rw [← electric_rate hD hP' hc' hφ hρ]
  exact hasDerivAt_half_dotProduct_self hE

end Electric

/-! ### The discrete Vlasov field and an explicit instance -/

section Instance

/-- The discrete Vlasov field `F(f) = -(D f V) + diag(E) f Dᵥᵀ`, the matrix form of
`∂ₜ f = -v ∂ₓ f + E ∂ᵥ f` (`D`, `Dᵥ` derivative matrices, `V = diag(v)`). -/
def vlasovField (D : Matrix x x ℝ) (Dv V : Matrix v v ℝ) (E : x → ℝ) (f : Matrix x v ℝ) :
    Matrix x v ℝ :=
  -(D * f * V) + Matrix.diagonal E * f * Dvᵀ

/-- **Discrete continuity equation of the full model.**  If `Dᵥᵀ w = 0` (discrete integration by
parts for the weights `w`), the moment `w` of the field is `-D j` with `j = f (V w)`. -/
theorem vlasovField_mulVec (D : Matrix x x ℝ) (Dv V : Matrix v v ℝ) (E : x → ℝ)
    (f : Matrix x v ℝ) {w : v → ℝ} (hw : Dvᵀ *ᵥ w = 0) :
    vlasovField D Dv V E f *ᵥ w = -(D *ᵥ (f *ᵥ (V *ᵥ w))) := by
  rw [vlasovField, add_mulVec, neg_mulVec]
  simp only [← mulVec_mulVec]
  rw [hw, mulVec_zero, mulVec_zero, add_zero]

noncomputable section Data

/-- Spatial basis: the Hadamard vectors `(1,1,1,1)/2`, `(1,1,-1,-1)/2`, `(1,-1,1,-1)/2`. -/
def X₀ : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1 / 2, 1 / 2, 1 / 2; 1 / 2, 1 / 2, -1 / 2; 1 / 2, -1 / 2, 1 / 2; 1 / 2, -1 / 2, -1 / 2]

/-- Velocity basis: the first three unit vectors (so `1 ∉ span W₀`). -/
def W₀ : Matrix (Fin 4) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- Coefficients. -/
def S₀ : Matrix (Fin 3) (Fin 3) ℝ := !![2, 0, 0; 0, 1, 0; 0, 0, 1]

/-- Periodic central difference on four points (`h = 1`), skew. -/
def D₀ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1 / 2, 0, -1 / 2; -1 / 2, 0, 1 / 2, 0; 0, -1 / 2, 0, 1 / 2; 1 / 2, 0, -1 / 2, 0]

/-- Quadrature weights (the function `1`). -/
def w₀ : Fin 4 → ℝ := ![1, 1, 1, 1]

/-- Velocity grid. -/
def v₀ : Fin 4 → ℝ := ![-2, -1, 0, 1]

/-- Weights of the two conserved moments `1`, `v`. -/
def U₀ : Matrix (Fin 4) (Fin 2) ℝ := !![1, -2; 1, -1; 1, 0; 1, 1]

/-- The potential `-(1,1,-1,-1)/2`. -/
def φ₀ : Fin 4 → ℝ := ![-1 / 2, -1 / 2, 1 / 2, 1 / 2]

/-- The kernel part of the density (mean and alternating mode). -/
def c₀ : Fin 4 → ℝ := ![3 / 2, 1 / 2, 3 / 2, 1 / 2]

def f₀ : Matrix (Fin 4) (Fin 4) ℝ := X₀ * S₀ * W₀ᵀ
def ρ₀ : Fin 4 → ℝ := f₀ *ᵥ w₀
def E₀ : Fin 4 → ℝ := -(D₀ *ᵥ φ₀)
def j₀ : Fin 4 → ℝ := f₀ *ᵥ (Matrix.diagonal v₀ *ᵥ w₀)
def F₀ : Matrix (Fin 4) (Fin 4) ℝ := vlasovField D₀ D₀ (Matrix.diagonal v₀) E₀ f₀
/-- Density rate of the uncorrected K-step and its continuity defect. -/
def ρ'₀ : Fin 4 → ℝ := kField W₀ F₀ *ᵥ w₀
def s₀ : Fin 4 → ℝ := ρ'₀ + D₀ *ᵥ j₀

end Data

theorem X₀_orth : X₀ᵀ * X₀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [X₀, Matrix.mul_apply, Fin.sum_univ_four]

theorem W₀_orth : W₀ᵀ * W₀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [W₀, Matrix.mul_apply, Fin.sum_univ_four]

theorem D₀_skew : D₀ᵀ = -D₀ := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [D₀]

theorem D₀_w₀ : D₀ᵀ *ᵥ w₀ = 0 := by
  ext i; fin_cases i <;> norm_num [D₀, w₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem ρ₀_eq : ρ₀ = ![2, 1, 1, 0] := by
  ext i; fin_cases i <;>
    norm_num [ρ₀, f₀, X₀, S₀, W₀, w₀, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_three]

theorem poisson₀ : D₀ *ᵥ (D₀ *ᵥ φ₀) = ρ₀ - c₀ := by
  rw [ρ₀_eq]
  ext i; fin_cases i <;> norm_num [D₀, φ₀, c₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem D₀_c₀ : D₀ *ᵥ c₀ = 0 := by
  ext i; fin_cases i <;> norm_num [D₀, c₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem φ₀_orth_ker : ∀ z, D₀ *ᵥ z = 0 → φ₀ ⬝ᵥ z = 0 := by
  intro z hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  simp [D₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1
  simp [φ₀, dotProduct, Fin.sum_univ_four]
  linarith

theorem φ₀_mem : X₀ *ᵥ (X₀ᵀ *ᵥ φ₀) = φ₀ := by
  ext i; fin_cases i <;>
    norm_num [X₀, φ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_three]

theorem E₀_eq : E₀ = ![1 / 2, -1 / 2, -1 / 2, 1 / 2] := by
  ext i; fin_cases i <;> norm_num [E₀, D₀, φ₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem f₀_eq : f₀ = !![1, 1 / 2, 1 / 2, 0; 1, 1 / 2, -1 / 2, 0; 1, -1 / 2, 1 / 2, 0;
    1, -1 / 2, -1 / 2, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [f₀, X₀, S₀, W₀, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem j₀_eq : j₀ = ![-5 / 2, -5 / 2, -3 / 2, -3 / 2] := by
  rw [j₀, f₀_eq]
  ext i; fin_cases i <;>
    norm_num [v₀, w₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mulVec_diagonal]

theorem E₀_j₀ : E₀ ⬝ᵥ j₀ = 0 := by
  rw [E₀_eq, j₀_eq]; norm_num [dotProduct, Fin.sum_univ_four]

theorem F₀_eq : F₀ = !![1 / 8, 3 / 8, -1 / 8, 1 / 8; -1 / 8, -1 / 8, 1 / 8, -3 / 8;
    1 / 8, -3 / 8, -1 / 8, -1 / 8; -1 / 8, 1 / 8, 1 / 8, 3 / 8] := by
  have h1 : D₀ * f₀ = !![0, 1 / 2, 0, 0; 0, -1 / 2, 0, 0; 0, -1 / 2, 0, 0; 0, 1 / 2, 0, 0] := by
    rw [f₀_eq]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [D₀, Matrix.mul_apply, Fin.sum_univ_four]
  have h2 : f₀ * D₀ᵀ = !![1 / 4, -1 / 4, -1 / 4, 1 / 4; 1 / 4, -3 / 4, -1 / 4, 3 / 4;
      -1 / 4, -1 / 4, 1 / 4, 1 / 4; -1 / 4, -3 / 4, 1 / 4, 3 / 4] := by
    rw [f₀_eq]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [D₀, Matrix.mul_apply, Fin.sum_univ_four]
  rw [F₀, vlasovField, h1, Matrix.mul_assoc (Matrix.diagonal E₀), h2, E₀_eq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] <;>
    norm_num [v₀]

theorem PW₀_eq : W₀ * W₀ᵀ = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [W₀, Matrix.mul_apply, Fin.sum_univ_three]

theorem F₀PW₀_eq : F₀ * (W₀ * W₀ᵀ) = !![1 / 8, 3 / 8, -1 / 8, 0; -1 / 8, -1 / 8, 1 / 8, 0;
    1 / 8, -3 / 8, -1 / 8, 0; -1 / 8, 1 / 8, 1 / 8, 0] := by
  rw [F₀_eq, PW₀_eq]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]

theorem ρ'₀_eq : ρ'₀ = ![3 / 8, -1 / 8, -3 / 8, 1 / 8] := by
  rw [ρ'₀, kField, F₀PW₀_eq]
  ext i; fin_cases i <;> norm_num [w₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem s₀_eq : s₀ = ![-1 / 8, 3 / 8, 1 / 8, -3 / 8] := by
  rw [s₀, ρ'₀_eq, j₀_eq]
  ext i; fin_cases i <;> norm_num [D₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem φ₀_s₀ : φ₀ ⬝ᵥ s₀ = -1 / 4 := by
  rw [s₀_eq]; norm_num [φ₀, dotProduct, Fin.sum_univ_four]

theorem X₀_s₀ : X₀ᵀ *ᵥ s₀ = ![0, 1 / 4, 0] := by
  rw [s₀_eq]
  ext i; fin_cases i <;> norm_num [X₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem energy₀ : (1 / 2 : ℝ) * (E₀ ⬝ᵥ E₀) = 1 / 2 := by
  rw [E₀_eq]; norm_num [dotProduct, Fin.sum_univ_four]

theorem U₀_col : U₀ *ᵥ Pi.single 0 1 = w₀ := by
  ext i; fin_cases i <;> norm_num [U₀, w₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem gram₀_det : IsUnit ((W₀ᵀ * U₀)ᵀ * (W₀ᵀ * U₀)).det := by
  have h : (W₀ᵀ * U₀)ᵀ * (W₀ᵀ * U₀) = !![3, -3; -3, 5] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [W₀, U₀, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [h, Matrix.det_fin_two, isUnit_iff_ne_zero]
  norm_num

/-- **The instance, full model.**  The discrete continuity equation holds (`s = 0`), so the
electric-energy rate of the full model at `f₀` is `⟪E₀, j₀⟫ = 0`: the electric energy is
stationary. -/
theorem instance_full : F₀ *ᵥ w₀ = -(D₀ *ᵥ j₀) ∧ E₀ ⬝ᵥ j₀ = 0 :=
  ⟨vlasovField_mulVec _ _ _ _ _ D₀_w₀, E₀_j₀⟩

/-- **The instance, uncorrected K-step.**  The continuity defect `s₀` has a nonzero component
in the spatial basis, `X₀ᵀ s₀ = (0, 1/4, 0)`, and the electric energy (equal to `1/2`) is
produced at the rate `⟪E₀, j₀⟫ - ⟪φ₀, s₀⟫ = 1/4`. -/
theorem instance_uncorrected : X₀ᵀ *ᵥ s₀ ≠ 0 ∧ E₀ ⬝ᵥ j₀ - φ₀ ⬝ᵥ s₀ = 1 / 4 := by
  refine ⟨?_, by rw [E₀_j₀, φ₀_s₀]; norm_num⟩
  rw [X₀_s₀]
  intro h
  have := congrFun h 1
  norm_num at this

/-- Explicit Poisson data for the uncorrected rate: `D₀² φ' = ρ'₀ - 0`. -/
theorem instance_poisson_rate :
    D₀ *ᵥ (D₀ *ᵥ ![-3 / 8, 1 / 8, 3 / 8, -1 / 8]) = ρ'₀ - 0 ∧
      E₀ ⬝ᵥ (-(D₀ *ᵥ ![-3 / 8, 1 / 8, 3 / 8, -1 / 8])) = 1 / 4 := by
  rw [ρ'₀_eq, E₀_eq]
  constructor
  · ext i; fin_cases i <;> norm_num [D₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · norm_num [D₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- **The instance, corrected K-step.**  For every multiplier satisfying the Einkemmer–Lubich
equation for the moments `(1, v)`, the continuity defect is orthogonal to the potential, so the
corrected K-step produces no electric energy: rate `0`, as in the full model. -/
theorem instance_corrected {Λ : Matrix (Fin 3) (Fin 3) ℝ}
    (hΛ : Λ * (W₀ᵀ * U₀) = X₀ᵀ * F₀ * (1 - W₀ * W₀ᵀ) * U₀) :
    E₀ ⬝ᵥ j₀ - φ₀ ⬝ᵥ (kFieldCorr X₀ W₀ Λ F₀ *ᵥ w₀ + D₀ *ᵥ j₀) = 0 := by
  have hcol := multiplier_col hΛ 0
  rw [U₀_col] at hcol
  rw [kFieldCorr_mulVec_eq_tangentProj hcol, E₀_j₀]
  have hF : F₀ *ᵥ w₀ = -(D₀ *ᵥ j₀) := vlasovField_mulVec _ _ _ _ _ D₀_w₀
  have : tangentProj X₀ W₀ F₀ *ᵥ w₀ + D₀ *ᵥ j₀ = (tangentProj X₀ W₀ F₀ - F₀) *ᵥ w₀ := by
    rw [sub_mulVec, hF]; abel
  rw [this, dotProduct_tangent_defect_eq_zero F₀ φ₀_mem w₀, sub_zero]

/-- The multiplier equation of the instance is solvable (by `lamMin`), so `instance_corrected`
is not vacuous. -/
theorem instance_multiplier_exists :
    ∃ Λ : Matrix (Fin 3) (Fin 3) ℝ, Λ * (W₀ᵀ * U₀) = X₀ᵀ * F₀ * (1 - W₀ * W₀ᵀ) * U₀ :=
  ⟨lamMin X₀ W₀ U₀ F₀, lamMin_mul gram₀_det F₀⟩

end Instance

end LeanDLRA.Novel.OpSL48
