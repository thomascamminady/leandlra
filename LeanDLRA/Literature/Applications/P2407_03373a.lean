import Mathlib
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2407.03373: low-rank plus diagonal approximations for Riccati-like ODEs

Bonnabel, Lambert, Bach, *Low-rank plus diagonal approximations for Riccati-like matrix
differential equations* (arXiv:2407.03373). The file proves matrix-algebra cores of the results
on real `d × d` matrices with the Frobenius norm, `Uᵀ U = 1`, `Π = U Uᵀ`, `Q = 1 - Π`.

* Prop. 1 (symmetric tangent projection): `prop1_factor_eq` (closed form in the factor form
  (9)–(10)), `prop1_closed_form_eq_tangentProj` (the closed form is `LeanDLRA.tangentProj U U H`),
  `prop1_best_approx` (best approximation over the tangent vectors), `prop1_residual_norm_sq`
  (the cost `Tr(QHQH)`).
* Prop. 2 (PPCA projection, `Y = U(R - sI)Uᵀ + sI`): `ppca_attained` (the closed form `P(H)` is the
  tangent vector at the parameters (15)), `prop2_best_approx` (minimality among the PPCA tangent
  vectors (14)).
* Prop. 3 (FA projection): `fa_optimal_generic`, `prop3_fa_optimal`, `prop3_fa_best_approx`. The
  diagonal term is taken to solve the normal equations (26), `(Q ∘ Q) x = diag(Q H Q)`, which is
  how the derivation of (26) is used; the results hold for every solution `x`. The existence of a
  solution (the Moore–Penrose choice of the paper) is not formalized.
* Prop. 5 (PPCA-Riccati): `ppca_riccati_ds` (39), `ppca_riccati_dU` (40), `ppca_riccati_dR` (41).
* Prop. 6 (FA-Riccati): `ppca_faRiccati_normal` (the right-hand side of (26) for `ψ̇`),
  `ppca_faRiccati_dU`, `ppca_faRiccati_dR`.

Not formalized: Prop. 4 (linear cost, Woodbury (36)) and the timings of Table 1; the remark of
Prop. 5 that `s` stays positive (`s = 0 ⇒ ṡ > 0` when `(I - UUᵀ) Q ≠ 0`; it needs a PSD square
root, which is not set up here); the existence of the pseudo-inverse solution of (26); Eq. (27) and
the Kalman-filter examples of Sec. 5.2 and Prop. 7 (stochastic). Props. 8 and 9 are not
formalized.

Differences from the paper: `ψ` in Props. 3 and 6 is a general `d × d` matrix (the diagonal
structure is not used), and `S` in Props. 5 and 6 is a general matrix (the paper's `CᵀN⁻¹C`).
Props. 1 and 2 minimize over all `δU`, `δR` (the paper's constraints `δU = (I-UUᵀ)Γ` and `δR`
symmetric are not needed), which is stronger. Props. 2 and 5 keep the paper's assumptions `R`
symmetric and `R - sI` invertible; Prop. 2 also needs `p < d` for the division by `d - p`.

Core definitions used: `LeanDLRA.tangentProj`, `LeanDLRA.tangentProj_apply`,
`LeanDLRA.tangentProj_eq_self_iff`, `LeanDLRA.isOrthProj_tangentProj`, `LeanDLRA.IsOrthProj`
(`norm_sub_le_of_mem_range`, `norm_sub_le`) and the Frobenius inner product `LeanDLRA.Frobenius`
(`inner_eq_trace`, `inner_mul_left`, `inner_mul_right`). Local definitions: `ppcaShift`, `ppcaTan`,
`ppcaProj`, `ppcaRes`.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2407_03373

variable {d p : Type*} [Fintype d] [Fintype p] [DecidableEq d] [DecidableEq p]

/-! ### Projector identities for `Π = U Uᵀ` and `Q = 1 - U Uᵀ` -/

section Projectors

variable {U : Matrix d p ℝ}

omit [DecidableEq d] in
/-- `Uᵀ (U X) = X` for `Uᵀ U = 1`. -/
lemma UT_mul_U_mul (hU : Uᵀ * U = 1) {n : Type*} (X : Matrix p n ℝ) : Uᵀ * (U * X) = X := by
  rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma Q_mul_Q (hU : Uᵀ * U = 1) : (1 - U * Uᵀ) * (1 - U * Uᵀ) = 1 - U * Uᵀ := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    UT_mul_U_mul hU]
  abel

lemma Q_mul_Q_mul (hU : Uᵀ * U = 1) (Y : Matrix d d ℝ) :
    (1 - U * Uᵀ) * ((1 - U * Uᵀ) * Y) = (1 - U * Uᵀ) * Y := by
  rw [← Matrix.mul_assoc, Q_mul_Q hU]

lemma Q_mul_U (hU : Uᵀ * U = 1) : (1 - U * Uᵀ) * U = 0 := by
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]

lemma transpose_mul_Q (hU : Uᵀ * U = 1) : Uᵀ * (1 - U * Uᵀ) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, UT_mul_U_mul hU, sub_self]

omit [DecidableEq p] [Fintype d] in
lemma Q_symm : (1 - U * Uᵀ)ᵀ = 1 - U * Uᵀ := by
  simp [Matrix.transpose_sub]

omit [DecidableEq p] in
lemma trace_Q_mul (H : Matrix d d ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * H) = Matrix.trace H - Matrix.trace (Uᵀ * H * U) := by
  have h : Matrix.trace (U * Uᵀ * H) = Matrix.trace (Uᵀ * H * U) := by
    rw [Matrix.mul_assoc U Uᵀ H, Matrix.trace_mul_comm]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, h]

lemma trace_Q (hU : Uᵀ * U = 1) :
    Matrix.trace (1 - U * Uᵀ : Matrix d d ℝ) = (Fintype.card d : ℝ) - Fintype.card p := by
  rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_mul_comm, hU, Matrix.trace_one]

lemma trace_QHQ (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * H * (1 - U * Uᵀ))
      = Matrix.trace H - Matrix.trace (Uᵀ * H * U) := by
  rw [Matrix.trace_mul_comm ((1 - U * Uᵀ) * H) (1 - U * Uᵀ), ← Matrix.mul_assoc, Q_mul_Q hU,
    trace_Q_mul]

end Projectors

/-! ### Proposition 1: symmetric tangent projection -/

section Prop1

variable {U : Matrix d p ℝ}

/-- arXiv:2407.03373, Prop. 1, factor form (9)–(10).
Closed form of the symmetric tangent projection in the factor form (9)-(10):
`δU R Uᵀ + U δR Uᵀ + U R δUᵀ = H U Uᵀ + U Uᵀ H - U Uᵀ H U Uᵀ` for `δU = (1-UUᵀ) H U R⁻¹`,
`δR = Uᵀ H U`, `R` symmetric invertible and `H` symmetric. -/
theorem prop1_factor_eq {R : Matrix p p ℝ} (hRs : Rᵀ = R)
    (hR : IsUnit R.det) {H : Matrix d d ℝ} (hH : Hᵀ = H) :
    (1 - U * Uᵀ) * H * U * R⁻¹ * R * Uᵀ + U * (Uᵀ * H * U) * Uᵀ
        + U * R * ((1 - U * Uᵀ) * H * U * R⁻¹)ᵀ
      = H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ := by
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRi' : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRT : R⁻¹ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRs]
  have hδT : ((1 - U * Uᵀ) * H * U * R⁻¹)ᵀ = R⁻¹ * (Uᵀ * (H * (1 - U * Uᵀ))) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, hH, hRT, Matrix.mul_assoc]
  have h1 : (1 - U * Uᵀ) * H * U * R⁻¹ * R = (1 - U * Uᵀ) * H * U := by
    rw [Matrix.mul_assoc _ R⁻¹ R, hRi', Matrix.mul_one]
  have h2 : U * R * (R⁻¹ * (Uᵀ * (H * (1 - U * Uᵀ)))) = U * (Uᵀ * (H * (1 - U * Uᵀ))) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R⁻¹, hRi, Matrix.one_mul]
  rw [hδT, h1, h2]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [DecidableEq d] [DecidableEq p] in
/-- Proposition 1: the closed form `H U Uᵀ + U Uᵀ H - U Uᵀ H U Uᵀ` is the tangent-space projector
`LeanDLRA.tangentProj U U` applied to `H`. -/
theorem prop1_closed_form_eq_tangentProj (H : Matrix d d ℝ) :
    LeanDLRA.tangentProj U U H = H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ := by
  rw [LeanDLRA.tangentProj_apply]
  abel

omit [DecidableEq d] in
/-- arXiv:2407.03373, Prop. 1, best approximation (8)–(11).
Best approximation in the symmetric tangent space: for every tangent vector
`δU R Uᵀ + U δR Uᵀ + U R δUᵀ` (any `δU`, `δR`, `R`), the projection
`P(H) = H U Uᵀ + U Uᵀ H - U Uᵀ H U Uᵀ` is at least as close to `H`. -/
theorem prop1_best_approx (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) (R : Matrix p p ℝ)
    (δU : Matrix d p ℝ) (δR : Matrix p p ℝ) :
    ‖H - (H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ)‖
      ≤ ‖H - (δU * R * Uᵀ + U * δR * Uᵀ + U * R * (δU)ᵀ)‖ := by
  have hy : LeanDLRA.tangentProj U U (δU * R * Uᵀ + U * δR * Uᵀ + U * R * (δU)ᵀ)
      = δU * R * Uᵀ + U * δR * Uᵀ + U * R * (δU)ᵀ := by
    rw [LeanDLRA.tangentProj_eq_self_iff hU hU]
    exact ⟨R * (δU)ᵀ, δU * R + U * δR, by simp only [Matrix.add_mul, Matrix.mul_assoc]; abel⟩
  rw [← prop1_closed_form_eq_tangentProj H]
  exact (LeanDLRA.isOrthProj_tangentProj hU hU).norm_sub_le_of_mem_range H _ hy

end Prop1

/-! ### Proposition 2: PPCA projection -/

section Prop2

variable {U : Matrix d p ℝ}

/-- The PPCA shift `δs = (Tr H - Tr(Uᵀ H U)) / (d - p)`. -/
noncomputable def ppcaShift (U : Matrix d p ℝ) (H : Matrix d d ℝ) : ℝ :=
  (Matrix.trace H - Matrix.trace (Uᵀ * H * U)) / ((Fintype.card d : ℝ) - Fintype.card p)

/-- The PPCA tangent vector (14) for the parameters `(δU, δR, δs)` at `Y = U (R - sI) Uᵀ + sI`. -/
noncomputable def ppcaTan (U : Matrix d p ℝ) (R : Matrix p p ℝ) (s : ℝ) (δU : Matrix d p ℝ)
    (δR : Matrix p p ℝ) (δs : ℝ) : Matrix d d ℝ :=
  δU * (R - s • (1 : Matrix p p ℝ)) * Uᵀ + U * (δR - δs • (1 : Matrix p p ℝ)) * Uᵀ
    + U * (R - s • (1 : Matrix p p ℝ)) * (δU)ᵀ + δs • (1 : Matrix d d ℝ)

/-- The PPCA projection of `H` of Proposition 2. -/
noncomputable def ppcaProj (U : Matrix d p ℝ) (H : Matrix d d ℝ) : Matrix d d ℝ :=
  H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ + ppcaShift U H • (1 - U * Uᵀ)

omit [Fintype d] in
lemma ppcaTan_eq (R : Matrix p p ℝ) (s : ℝ) (δU : Matrix d p ℝ) (δR : Matrix p p ℝ) (δs : ℝ) :
    ppcaTan U R s δU δR δs
      = (δU * (R - s • (1 : Matrix p p ℝ)) + U * δR) * Uᵀ
        + U * ((R - s • (1 : Matrix p p ℝ)) * (δU)ᵀ) + δs • (1 - U * Uᵀ) := by
  unfold ppcaTan
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub, Matrix.mul_assoc]
  abel

/-- arXiv:2407.03373, Prop. 2, closed form (15)–(16).
The PPCA projection is the tangent vector at the parameters of Proposition 2. -/
theorem ppca_attained {R : Matrix p p ℝ} (hRs : Rᵀ = R) (s : ℝ)
    (hR : IsUnit (R - s • (1 : Matrix p p ℝ)).det) {H : Matrix d d ℝ} (hH : Hᵀ = H) :
    ppcaTan U R s ((1 - U * Uᵀ) * H * U * (R - s • (1 : Matrix p p ℝ))⁻¹) (Uᵀ * H * U)
        (ppcaShift U H) = ppcaProj U H := by
  have hM : (R - s • (1 : Matrix p p ℝ))ᵀ = R - s • (1 : Matrix p p ℝ) := by
    simp [Matrix.transpose_sub, Matrix.transpose_smul, hRs]
  have key := prop1_factor_eq (U := U) hM hR hH
  have key2 : ((1 - U * Uᵀ) * H * U * (R - s • (1 : Matrix p p ℝ))⁻¹
        * (R - s • (1 : Matrix p p ℝ)) + U * (Uᵀ * H * U)) * Uᵀ
      + U * ((R - s • (1 : Matrix p p ℝ)) * ((1 - U * Uᵀ) * H * U
        * (R - s • (1 : Matrix p p ℝ))⁻¹)ᵀ)
      = H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ := by
    rw [← key]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [ppcaTan_eq, key2]
  rfl

/-- The residual `H - P(H)` of Proposition 2, written as `(1-UUᵀ) H (1-UUᵀ) - δs (1-UUᵀ)`. -/
noncomputable def ppcaRes (U : Matrix d p ℝ) (H : Matrix d d ℝ) : Matrix d d ℝ :=
  (1 - U * Uᵀ) * H * (1 - U * Uᵀ) - ppcaShift U H • (1 - U * Uᵀ)

omit [DecidableEq p] in
lemma H_sub_ppcaProj (H : Matrix d d ℝ) : H - ppcaProj U H = ppcaRes U H := by
  unfold ppcaProj ppcaRes
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_sub,
    Matrix.mul_assoc]
  abel

omit [DecidableEq p] in
lemma ppcaRes_symm (hH : Hᵀ = H) : (ppcaRes U H)ᵀ = ppcaRes U H := by
  unfold ppcaRes
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_transpose, hH, Matrix.mul_assoc]

lemma ppcaRes_mul_U (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) : ppcaRes U H * U = 0 := by
  unfold ppcaRes
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hU, sub_self, smul_zero]

lemma transpose_mul_ppcaRes (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    Uᵀ * ppcaRes U H = 0 := by
  unfold ppcaRes
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_assoc, UT_mul_U_mul hU, sub_self, smul_sub]

lemma ppcaRes_mul_Q (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    ppcaRes U H * (1 - U * Uᵀ) = ppcaRes U H := by
  unfold ppcaRes
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, UT_mul_U_mul hU, smul_sub]
  abel

/-- The inner product of the residual with `Q = 1 - UUᵀ` vanishes for the PPCA shift. -/
lemma ppcaRes_inner_Q (hU : Uᵀ * U = 1) (hH : Hᵀ = H)
    (hpd : (Fintype.card p : ℝ) < Fintype.card d) :
    ⟪ppcaRes U H, (1 - U * Uᵀ : Matrix d d ℝ)⟫ = 0 := by
  have hne : (Fintype.card d : ℝ) - Fintype.card p ≠ 0 := (sub_pos.2 hpd).ne'
  rw [LeanDLRA.Frobenius.inner_eq_trace, ppcaRes_symm hH, ppcaRes_mul_Q hU H]
  unfold ppcaRes
  rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, trace_QHQ hU, trace_Q hU]
  unfold ppcaShift
  rw [div_mul_cancel₀ _ hne, sub_self]

/-- The residual is orthogonal to every PPCA tangent vector. -/
lemma ppca_inner_tan (hU : Uᵀ * U = 1) (hH : Hᵀ = H)
    (hpd : (Fintype.card p : ℝ) < Fintype.card d) (R : Matrix p p ℝ) (s : ℝ)
    (δU : Matrix d p ℝ) (δR : Matrix p p ℝ) (δs : ℝ) :
    ⟪ppcaRes U H, ppcaTan U R s δU δR δs⟫ = 0 := by
  have h1 : ∀ X : Matrix d p ℝ, ⟪ppcaRes U H, X * Uᵀ⟫ = 0 := fun X => by
    rw [← LeanDLRA.Frobenius.inner_mul_right, ppcaRes_mul_U hU H, inner_zero_left]
  have h2 : ∀ Y : Matrix p d ℝ, ⟪ppcaRes U H, U * Y⟫ = 0 := fun Y => by
    rw [real_inner_comm, LeanDLRA.Frobenius.inner_mul_left, transpose_mul_ppcaRes hU H,
      inner_zero_right]
  rw [ppcaTan_eq, inner_add_right, inner_add_right, h1, h2, real_inner_smul_right,
    ppcaRes_inner_Q hU hH hpd]
  simp

/-- arXiv:2407.03373, Prop. 2, minimality (14)–(16).
Proposition 2 (PPCA projection, minimality): for every PPCA tangent vector
`δY(δU, δR, δs)` at `Y = U (R - sI) Uᵀ + sI` with `R` symmetric and `R - sI` invertible,
`‖H - P(H)‖ ≤ ‖H - δY‖`, where `P(H)` is the closed form of Proposition 2. -/
theorem prop2_best_approx (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (hRs : Rᵀ = R) (s : ℝ)
    (hR : IsUnit (R - s • (1 : Matrix p p ℝ)).det) {H : Matrix d d ℝ} (hH : Hᵀ = H)
    (hpd : (Fintype.card p : ℝ) < Fintype.card d) (δU : Matrix d p ℝ) (δR : Matrix p p ℝ)
    (δs : ℝ) :
    ‖H - ppcaProj U H‖ ≤ ‖H - ppcaTan U R s δU δR δs‖ := by
  have hP := ppca_attained (U := U) hRs s hR hH
  have horthP : ⟪ppcaRes U H, ppcaProj U H⟫ = 0 := by
    rw [← hP]
    exact ppca_inner_tan hU hH hpd R s _ _ _
  have horthY := ppca_inner_tan hU hH hpd R s δU δR δs
  have key : H - ppcaTan U R s δU δR δs
      = ppcaRes U H + (ppcaProj U H - ppcaTan U R s δU δR δs) := by
    rw [← H_sub_ppcaProj]
    abel
  have hsq : ‖ppcaRes U H‖ ^ 2 ≤ ‖H - ppcaTan U R s δU δR δs‖ ^ 2 := by
    rw [key, norm_add_sq_real, inner_sub_right, horthP, horthY]
    nlinarith [sq_nonneg ‖ppcaProj U H - ppcaTan U R s δU δR δs‖]
  rw [H_sub_ppcaProj]
  nlinarith [norm_nonneg (ppcaRes U H), norm_nonneg (H - ppcaTan U R s δU δR δs)]

end Prop2

/-! ### Proposition 3: optimal diagonal term in the FA form -/

section Prop3

variable {U : Matrix d p ℝ}

omit [DecidableEq p] in
/-- The residual `Z - P_T(Z)` of a matrix `Z` under the tangent projector of `U`. -/
lemma resid_Z (Z : Matrix d d ℝ) :
    Z - (U * Uᵀ * Z + Z * U * Uᵀ - U * Uᵀ * Z * U * Uᵀ) = (1 - U * Uᵀ) * Z * (1 - U * Uᵀ) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

omit [DecidableEq d] in
lemma entry_sub_sandwich (A B C : Matrix d d ℝ) (k : d) :
    (A * (B - C) * A) k k = (A * B * A) k k - (A * C * A) k k := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]

lemma diag_sandwich {A : Matrix d d ℝ} (hA : Aᵀ = A) (x : d → ℝ) (k : d) :
    (A * Matrix.diagonal x * A) k k = ∑ j, A k j * A k j * x j := by
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using h
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, hsym k j]
  ring

lemma inner_sandwich_diag {A M : Matrix d d ℝ} (hM : Mᵀ = M) (hMA : A * M * A = M)
    (w : d → ℝ) : ⟪M, A * Matrix.diagonal w * A⟫ = ∑ k, w k * M k k := by
  rw [LeanDLRA.Frobenius.inner_eq_trace, hM, ← Matrix.mul_assoc M (A * Matrix.diagonal w) A,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc (A * M) A (Matrix.diagonal w), hMA]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Least squares for the diagonal term, for a symmetric idempotent `A`: if `x` solves the normal
equations `(A ∘ A) x = diag (A H A)`, then `x` minimizes `‖A (H - diag y) A‖` over `y`. -/
theorem fa_optimal_generic {A H : Matrix d d ℝ} (hA : Aᵀ = A) (hAA : A * A = A) (hH : Hᵀ = H)
    {x : d → ℝ} (hx : (Matrix.hadamard A A) *ᵥ x = Matrix.diag (A * H * A)) (y : d → ℝ) :
    ‖A * (H - Matrix.diagonal x) * A‖ ≤ ‖A * (H - Matrix.diagonal y) * A‖ := by
  have hAAY : ∀ Y : Matrix d d ℝ, A * (A * Y) = A * Y := fun Y => by
    rw [← Matrix.mul_assoc, hAA]
  obtain ⟨M, hM⟩ : ∃ M : Matrix d d ℝ, M = A * (H - Matrix.diagonal x) * A := ⟨_, rfl⟩
  rw [← hM]
  have hMs : Mᵀ = M := by
    rw [hM]
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, hA, hH, Matrix.diagonal_transpose]
    exact (Matrix.mul_assoc _ _ _).symm
  have hMA : A * M * A = M := by
    rw [hM]
    simp only [Matrix.mul_assoc, hAAY, hAA]
  have hkk : ∀ k, M k k = 0 := by
    intro k
    have hk := congrFun hx k
    simp only [Matrix.mulVec, dotProduct, Matrix.hadamard_apply, Matrix.diag_apply] at hk
    rw [hM, entry_sub_sandwich, diag_sandwich hA x k, hk, sub_self]
  have hdiag : Matrix.diagonal (y - x) = Matrix.diagonal y - Matrix.diagonal x := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have hZ : A * (H - Matrix.diagonal y) * A = M - A * Matrix.diagonal (y - x) * A := by
    rw [hM, hdiag]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hip : ⟪M, A * Matrix.diagonal (y - x) * A⟫ = 0 := by
    rw [inner_sandwich_diag hMs hMA]
    simp [hkk]
  rw [hZ]
  have hsq : ‖M‖ ^ 2 ≤ ‖M - A * Matrix.diagonal (y - x) * A‖ ^ 2 := by
    rw [norm_sub_sq_real, hip]
    nlinarith [sq_nonneg ‖A * Matrix.diagonal (y - x) * A‖]
  nlinarith [norm_nonneg M, norm_nonneg (M - A * Matrix.diagonal (y - x) * A)]

/-- arXiv:2407.03373, Prop. 3, normal equations (26).
Proposition 3 (FA projection, optimality of the diagonal term): if `δψ = x` solves the normal
equations `((I-UUᵀ) ∘ (I-UUᵀ)) x = diag((I-UUᵀ) H (I-UUᵀ))` (equation (26)), then for every
diagonal `y`, `‖(I-UUᵀ)(H - diag x)(I-UUᵀ)‖ ≤ ‖(I-UUᵀ)(H - diag y)(I-UUᵀ)‖`. -/
theorem prop3_fa_optimal (hU : Uᵀ * U = 1) {H : Matrix d d ℝ} (hH : Hᵀ = H) {x : d → ℝ}
    (hx : Matrix.hadamard (1 - U * Uᵀ) (1 - U * Uᵀ) *ᵥ x
      = Matrix.diag ((1 - U * Uᵀ) * H * (1 - U * Uᵀ))) (y : d → ℝ) :
    ‖(1 - U * Uᵀ) * (H - Matrix.diagonal x) * (1 - U * Uᵀ)‖
      ≤ ‖(1 - U * Uᵀ) * (H - Matrix.diagonal y) * (1 - U * Uᵀ)‖ :=
  fa_optimal_generic (Q_symm (U := U)) (Q_mul_Q hU) hH hx y

/-- arXiv:2407.03373, Prop. 3, (25)–(26).
Proposition 3, best approximation in the FA tangent space: with
`δU = (I-UUᵀ)(H - diag x) U R⁻¹`, `δR = Uᵀ (H - diag x) U` and `δψ = x` solving (26), the FA
tangent vector
`δU R Uᵀ + U δR Uᵀ + U R δUᵀ + diag x` is at least as close to `H` as any FA tangent vector
`δU' R Uᵀ + U δR' Uᵀ + U R δU'ᵀ + diag y`. -/
theorem prop3_fa_best_approx (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (hRs : Rᵀ = R)
    (hR : IsUnit R.det) {H : Matrix d d ℝ} (hH : Hᵀ = H) {x : d → ℝ}
    (hx : Matrix.hadamard (1 - U * Uᵀ) (1 - U * Uᵀ) *ᵥ x
      = Matrix.diag ((1 - U * Uᵀ) * H * (1 - U * Uᵀ))) (y : d → ℝ)
    (δU' : Matrix d p ℝ) (δR' : Matrix p p ℝ) :
    ‖H - ((1 - U * Uᵀ) * (H - Matrix.diagonal x) * U * R⁻¹ * R * Uᵀ
        + U * (Uᵀ * (H - Matrix.diagonal x) * U) * Uᵀ
        + U * R * ((1 - U * Uᵀ) * (H - Matrix.diagonal x) * U * R⁻¹)ᵀ + Matrix.diagonal x)‖
      ≤ ‖H - (δU' * R * Uᵀ + U * δR' * Uᵀ + U * R * (δU')ᵀ + Matrix.diagonal y)‖ := by
  have hsym : (H - Matrix.diagonal x)ᵀ = H - Matrix.diagonal x := by
    rw [Matrix.transpose_sub, hH, Matrix.diagonal_transpose]
  have hfac := prop1_factor_eq (U := U) hRs hR hsym
  have hL : H - ((1 - U * Uᵀ) * (H - Matrix.diagonal x) * U * R⁻¹ * R * Uᵀ
        + U * (Uᵀ * (H - Matrix.diagonal x) * U) * Uᵀ
        + U * R * ((1 - U * Uᵀ) * (H - Matrix.diagonal x) * U * R⁻¹)ᵀ + Matrix.diagonal x)
      = (1 - U * Uᵀ) * (H - Matrix.diagonal x) * (1 - U * Uᵀ) := by
    rw [hfac, ← resid_Z (H - Matrix.diagonal x)]
    abel
  have hS : LeanDLRA.tangentProj U U (δU' * R * Uᵀ + U * δR' * Uᵀ + U * R * (δU')ᵀ)
      = δU' * R * Uᵀ + U * δR' * Uᵀ + U * R * (δU')ᵀ := by
    rw [LeanDLRA.tangentProj_eq_self_iff hU hU]
    exact ⟨R * (δU')ᵀ, δU' * R + U * δR', by simp only [Matrix.add_mul, Matrix.mul_assoc]; abel⟩
  have hproj := (LeanDLRA.isOrthProj_tangentProj hU hU).norm_sub_le_of_mem_range
    (H - Matrix.diagonal y) _ hS
  rw [LeanDLRA.tangentProj_apply, resid_Z] at hproj
  rw [hL]
  calc ‖(1 - U * Uᵀ) * (H - Matrix.diagonal x) * (1 - U * Uᵀ)‖
      ≤ ‖(1 - U * Uᵀ) * (H - Matrix.diagonal y) * (1 - U * Uᵀ)‖ :=
        prop3_fa_optimal hU hH hx y
    _ ≤ ‖(H - Matrix.diagonal y) - (δU' * R * Uᵀ + U * δR' * Uᵀ + U * R * (δU')ᵀ)‖ := hproj
    _ = ‖H - (δU' * R * Uᵀ + U * δR' * Uᵀ + U * R * (δU')ᵀ + Matrix.diagonal y)‖ := by
        congr 1
        abel

end Prop3

/-! ### Proposition 5: PPCA-Riccati vector field -/

section Prop5

variable {U : Matrix d p ℝ}

omit [DecidableEq d] [DecidableEq p] in
/-- Core of the `U̇` formula: with `Qc Y = s Qc` and `Y U = U R`, the projected numerator
`Qc (F) U` of the Riccati field `F = A Y + Y Aᵀ + Q - Y S Y` is
`Qc (A U R + Q U + s Aᵀ U - s S U R)`. -/
lemma riccati_dU_core {Qc Y : Matrix d d ℝ} {R : Matrix p p ℝ} {s : ℝ}
    (hQY : Qc * Y = s • Qc) (hYU : Y * U = U * R) (A S Q0 : Matrix d d ℝ) :
    Qc * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * U
      = Qc * (A * U * R + Q0 * U + s • (Aᵀ * U) - s • (S * U * R)) := by
  have hQYX : ∀ X : Matrix d p ℝ, Qc * (Y * X) = s • (Qc * X) := fun X => by
    rw [← Matrix.mul_assoc, hQY, Matrix.smul_mul]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc,
    hYU, hQYX, Matrix.mul_smul]
  abel

omit [DecidableEq d] [DecidableEq p] in
/-- Core of the `Ṙ` formula: with `Uᵀ Y = R Uᵀ` and `Y U = U R`. -/
lemma riccati_dR_core {Y : Matrix d d ℝ} {R : Matrix p p ℝ}
    (hYU : Y * U = U * R) (hUY : Uᵀ * Y = R * Uᵀ) (A S Q0 : Matrix d d ℝ) :
    Uᵀ * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * U
      = Uᵀ * A * U * R + R * Uᵀ * Aᵀ * U + Uᵀ * Q0 * U - R * Uᵀ * S * U * R := by
  have hUYX : ∀ X : Matrix d p ℝ, Uᵀ * (Y * X) = R * (Uᵀ * X) := fun X => by
    rw [← Matrix.mul_assoc, hUY, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc,
    hYU, hUYX]

/-- `Y = U R Uᵀ + s (I - UUᵀ)` satisfies `Qc Y = s Qc` and `Y U = U R`, with `Qc = I - UUᵀ`. -/
lemma ppcaY_facts (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (s : ℝ) {Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + s • (1 - U * Uᵀ)) :
    (1 - U * Uᵀ) * Y = s • (1 - U * Uᵀ) ∧ Y * U = U * R ∧ Uᵀ * Y = R * Uᵀ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hY]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, Q_mul_Q hU]
    rw [← Matrix.mul_assoc (1 - U * Uᵀ) U (R * Uᵀ), Q_mul_U hU]
    simp
  · rw [hY]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hU, Matrix.mul_one,
      Q_mul_U hU, smul_zero, add_zero]
  · rw [hY]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, UT_mul_U_mul hU,
      transpose_mul_Q hU, smul_zero, add_zero]

/-- arXiv:2407.03373, Prop. 5, eq. (40).
Proposition 5, the `U̇` formula (40): the PPCA projection gives
`U̇ = (I-UUᵀ)(A U R + Q U + s Aᵀ U - s S U R)(R - sI)⁻¹` for `Ẏ = F(Y)`. -/
theorem ppca_riccati_dU (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (s : ℝ) {Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + s • (1 - U * Uᵀ)) (A S Q0 : Matrix d d ℝ) :
    (1 - U * Uᵀ) * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * U * (R - s • (1 : Matrix p p ℝ))⁻¹
      = (1 - U * Uᵀ) * (A * U * R + Q0 * U + s • (Aᵀ * U) - s • (S * U * R))
          * (R - s • (1 : Matrix p p ℝ))⁻¹ := by
  obtain ⟨h1, h2, _⟩ := ppcaY_facts hU s hY
  rw [riccati_dU_core h1 h2]

/-- arXiv:2407.03373, Prop. 5, eq. (41).
Proposition 5, the `Ṙ` formula (41): `Ṙ = δR = Uᵀ F(Y) U
= Uᵀ A U R + R Uᵀ Aᵀ U + Uᵀ Q U - R Uᵀ S U R`. -/
theorem ppca_riccati_dR (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (s : ℝ) {Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + s • (1 - U * Uᵀ)) (A S Q0 : Matrix d d ℝ) :
    Uᵀ * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * U
      = Uᵀ * A * U * R + R * Uᵀ * Aᵀ * U + Uᵀ * Q0 * U - R * Uᵀ * S * U * R := by
  obtain ⟨_, h2, h3⟩ := ppcaY_facts hU s hY
  exact riccati_dR_core h2 h3 A S Q0

/-- Trace of the projected Riccati field, `Tr((I-UUᵀ) F(Y))`. -/
lemma trace_Q_URUT (hU : Uᵀ * U = 1) (X : Matrix d d ℝ) (R : Matrix p p ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * (X * (U * R * Uᵀ))) = 0 := by
  have e : (1 - U * Uᵀ) * (X * (U * R * Uᵀ)) = ((1 - U * Uᵀ) * X * U * R) * Uᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, transpose_mul_Q hU, Matrix.zero_mul, Matrix.trace_zero]

lemma trace_Q_sandwich (hU : Uᵀ * U = 1) (X : Matrix d d ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * (X * (1 - U * Uᵀ))) = Matrix.trace ((1 - U * Uᵀ) * X) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm ((1 - U * Uᵀ) * X) (1 - U * Uᵀ),
    ← Matrix.mul_assoc, Q_mul_Q hU]

omit [DecidableEq p] in
lemma trace_Q_transpose (X : Matrix d d ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * Xᵀ) = Matrix.trace ((1 - U * Uᵀ) * X) := by
  rw [← Matrix.trace_transpose ((1 - U * Uᵀ) * Xᵀ), Matrix.transpose_mul,
    Matrix.transpose_transpose, Q_symm, Matrix.trace_mul_comm]

/-- arXiv:2407.03373, Prop. 5, eq. (39).
Proposition 5, the shift `ṡ` (39): `ṡ = Tr((I-UUᵀ)(2sA + Q - s²S)) / (d - p)`. -/
theorem ppca_riccati_ds (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (s : ℝ) {Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + s • (1 - U * Uᵀ)) (A S Q0 : Matrix d d ℝ) :
    ppcaShift U (A * Y + Y * Aᵀ + Q0 - Y * S * Y)
      = Matrix.trace ((1 - U * Uᵀ) * ((2 * s) • A + Q0 - (s ^ 2) • S))
          / ((Fintype.card d : ℝ) - Fintype.card p) := by
  obtain ⟨h1, _, _⟩ := ppcaY_facts hU s hY
  have P1 : Matrix.trace ((1 - U * Uᵀ) * (A * Y)) = s * Matrix.trace ((1 - U * Uᵀ) * A) := by
    rw [hY]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    rw [trace_Q_URUT hU, trace_Q_sandwich hU, zero_add]
  have P2 : Matrix.trace ((1 - U * Uᵀ) * (Y * Aᵀ)) = s * Matrix.trace ((1 - U * Uᵀ) * A) := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_Q_transpose]
  have hQYX : ∀ X : Matrix d d ℝ, (1 - U * Uᵀ) * (Y * X) = s • ((1 - U * Uᵀ) * X) :=
    fun X => by rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have P3 : Matrix.trace ((1 - U * Uᵀ) * (S * Y)) = s * Matrix.trace ((1 - U * Uᵀ) * S) := by
    rw [hY]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    rw [trace_Q_URUT hU, zero_add, trace_Q_sandwich hU]
  have P4 : Matrix.trace ((1 - U * Uᵀ) * (Y * S * Y))
      = s ^ 2 * Matrix.trace ((1 - U * Uᵀ) * S) := by
    rw [Matrix.mul_assoc Y S Y, hQYX, Matrix.trace_smul, smul_eq_mul, P3]
    ring
  unfold ppcaShift
  rw [← trace_Q_mul]
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  rw [P1, P2, P4]
  ring

end Prop5

/-! ### Proposition 6: FA-Riccati vector field -/

section Prop6

variable {U : Matrix d p ℝ}

/-- For `Y = U R Uᵀ + ψ`: the products of `Y` with `1 - UUᵀ`, `U` and `Uᵀ` used in Proposition 6. -/
lemma faY_facts (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} {ψ Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + ψ) :
    (1 - U * Uᵀ) * Y = (1 - U * Uᵀ) * ψ ∧ Y * (1 - U * Uᵀ) = ψ * (1 - U * Uᵀ)
      ∧ Y * U = U * R + ψ * U ∧ Uᵀ * Y = R * Uᵀ + Uᵀ * ψ := by
  have hQ : (1 - U * Uᵀ) * (U * R * Uᵀ) = 0 := by
    simp only [← Matrix.mul_assoc, Q_mul_U hU, Matrix.zero_mul]
  have hQ' : (U * R * Uᵀ) * (1 - U * Uᵀ) = 0 := by
    simp only [Matrix.mul_assoc, transpose_mul_Q hU, Matrix.mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hY, Matrix.mul_add, hQ, zero_add]
  · rw [hY, Matrix.add_mul, hQ', zero_add]
  · rw [hY, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  · rw [hY, Matrix.mul_add]
    simp only [Matrix.mul_assoc, UT_mul_U_mul hU]

omit [DecidableEq d] [DecidableEq p] in
/-- Core of the `U̇` formula (before multiplying by `R⁻¹`), for a generic `Qc` with `Qc Y = Qc ψ`:
`Qc (F - D) U = Qc ((A ψ + ψ Aᵀ + Q - ψ S ψ - D) U + (A U R - ψ S U R))`. -/
lemma fa_dU_core {Qc Y ψ : Matrix d d ℝ} {R : Matrix p p ℝ} (D : Matrix d d ℝ)
    (hQY : Qc * Y = Qc * ψ) (hYU : Y * U = U * R + ψ * U) (A S Q0 : Matrix d d ℝ) :
    Qc * (A * Y + Y * Aᵀ + Q0 - Y * S * Y - D) * U
      = Qc * ((A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ - D) * U + (A * U * R - ψ * S * U * R)) := by
  have hQYX : ∀ X : Matrix d p ℝ, Qc * (Y * X) = Qc * (ψ * X) := fun X => by
    rw [← Matrix.mul_assoc, hQY, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc,
    hYU, hQYX]
  abel

omit [DecidableEq d] in
/-- Core of the normal equations: for a generic `Qc` with `Qc Y = Qc ψ` and `Y Qc = ψ Qc`,
`Qc F(Y) Qc = Qc M Qc`. -/
lemma fa_normal_core {Qc Y ψ : Matrix d d ℝ} (hQY : Qc * Y = Qc * ψ) (hYQ : Y * Qc = ψ * Qc)
    (A S Q0 : Matrix d d ℝ) :
    Qc * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * Qc
      = Qc * (A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ) * Qc := by
  have hQYX : ∀ X : Matrix d d ℝ, Qc * (Y * X) = Qc * (ψ * X) := fun X => by
    rw [← Matrix.mul_assoc, hQY, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc,
    hQYX, hYQ]

omit [DecidableEq d] [DecidableEq p] in
/-- Core of the `Ṙ` formula, before subtracting the diagonal part. -/
lemma fa_dR_core {Y ψ : Matrix d d ℝ} {R : Matrix p p ℝ}
    (hYU : Y * U = U * R + ψ * U) (hUY : Uᵀ * Y = R * Uᵀ + Uᵀ * ψ) (A S Q0 : Matrix d d ℝ) :
    Uᵀ * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * U
      = Uᵀ * (A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ) * U - Uᵀ * ψ * S * U * R
        - R * Uᵀ * S * ψ * U - R * Uᵀ * S * U * R + Uᵀ * A * U * R + R * Uᵀ * Aᵀ * U := by
  have hUYX : ∀ X : Matrix d p ℝ, Uᵀ * (Y * X) = R * (Uᵀ * X) + Uᵀ * (ψ * X) := fun X => by
    rw [← Matrix.mul_assoc, hUY, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc,
    hYU, hUYX]
  abel

/-- arXiv:2407.03373, Prop. 6, right-hand side of (26) for ψ̇.
Proposition 6, the normal-equation data: `(I-UUᵀ) F(Y) (I-UUᵀ) = (I-UUᵀ) M (I-UUᵀ)` with
`M = Aψ + ψAᵀ + Q - ψSψ`, so `diag ψ̇` solves (26) with the right-hand side built from `M`. -/
theorem ppca_faRiccati_normal (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} {ψ Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + ψ) (A S Q0 : Matrix d d ℝ) :
    (1 - U * Uᵀ) * (A * Y + Y * Aᵀ + Q0 - Y * S * Y) * (1 - U * Uᵀ)
      = (1 - U * Uᵀ) * (A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ) * (1 - U * Uᵀ) := by
  obtain ⟨h1, h2, _, _⟩ := faY_facts hU hY
  exact fa_normal_core h1 h2 A S Q0

/-- arXiv:2407.03373, Prop. 6, U̇.
Proposition 6, the `U̇` formula: with `δU = (I-UUᵀ)(F(Y) - D) U R⁻¹` for any `D`,
`δU = (I-UUᵀ)(M - D) U R⁻¹ + (I-UUᵀ)(A U - ψ S U)`. -/
theorem ppca_faRiccati_dU (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} (hR : IsUnit R.det)
    {ψ Y : Matrix d d ℝ} (hY : Y = U * R * Uᵀ + ψ) (A S Q0 D : Matrix d d ℝ) :
    (1 - U * Uᵀ) * (A * Y + Y * Aᵀ + Q0 - Y * S * Y - D) * U * R⁻¹
      = (1 - U * Uᵀ) * (A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ - D) * U * R⁻¹
        + (1 - U * Uᵀ) * (A * U - ψ * S * U) := by
  obtain ⟨h1, _, h3, _⟩ := faY_facts hU hY
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hR' : (A * U * R - ψ * S * U * R) * R⁻¹ = A * U - ψ * S * U := by
    simp only [Matrix.sub_mul, Matrix.mul_assoc, hRi, Matrix.mul_one]
  rw [fa_dU_core D h1 h3 A S Q0, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc (1 - U * Uᵀ) (A * U * R - ψ * S * U * R) R⁻¹, hR']
  simp only [Matrix.mul_assoc]

omit [DecidableEq d] in
/-- arXiv:2407.03373, Prop. 6, Ṙ.
Proposition 6, the `Ṙ` formula: `δR = Uᵀ (F(Y) - D) U` equals
`Uᵀ (M - D) U - Uᵀ ψ S U R - R Uᵀ S ψ U - R Uᵀ S U R + Uᵀ A U R + R Uᵀ Aᵀ U`. -/
theorem ppca_faRiccati_dR (hU : Uᵀ * U = 1) {R : Matrix p p ℝ} {ψ Y : Matrix d d ℝ}
    (hY : Y = U * R * Uᵀ + ψ) (A S Q0 D : Matrix d d ℝ) :
    Uᵀ * (A * Y + Y * Aᵀ + Q0 - Y * S * Y - D) * U
      = Uᵀ * (A * ψ + ψ * Aᵀ + Q0 - ψ * S * ψ - D) * U - Uᵀ * ψ * S * U * R
        - R * Uᵀ * S * ψ * U - R * Uᵀ * S * U * R + Uᵀ * A * U * R + R * Uᵀ * Aᵀ * U := by
  classical
  have hfa := faY_facts (R := R) hU hY
  rw [Matrix.mul_sub, Matrix.sub_mul, fa_dR_core hfa.2.2.1 hfa.2.2.2 A S Q0]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

end Prop6

/-! ### Proposition 1, residual norm, and a non-vacuity example -/

section Residual

variable {U : Matrix d p ℝ}

/-- arXiv:2407.03373, Prop. 1, cost (11).
Proposition 1 (cost): for symmetric `H`, the squared distance from `H` to its tangent
projection is `Tr((I-UUᵀ) H (I-UUᵀ) H)`. -/
theorem prop1_residual_norm_sq (hU : Uᵀ * U = 1) {H : Matrix d d ℝ} (hH : Hᵀ = H) :
    ‖H - (H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ)‖ ^ 2
      = Matrix.trace ((1 - U * Uᵀ) * H * (1 - U * Uᵀ) * H) := by
  have hres : H - (H * U * Uᵀ + U * Uᵀ * H - U * Uᵀ * H * U * Uᵀ)
      = (1 - U * Uᵀ) * H * (1 - U * Uᵀ) := by
    rw [← resid_Z (U := U) H]
    abel
  have hT : ((1 - U * Uᵀ) * H * (1 - U * Uᵀ))ᵀ = (1 - U * Uᵀ) * H * (1 - U * Uᵀ) := by
    simp only [Matrix.transpose_mul, Q_symm, hH, Matrix.mul_assoc]
  have e1 : (1 - U * Uᵀ) * H * (1 - U * Uᵀ) * ((1 - U * Uᵀ) * H * (1 - U * Uᵀ))
      = (1 - U * Uᵀ) * H * ((1 - U * Uᵀ) * (1 - U * Uᵀ)) * H * (1 - U * Uᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [hres, ← real_inner_self_eq_norm_sq, LeanDLRA.Frobenius.inner_eq_trace, hT, e1,
    Q_mul_Q hU, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Q_mul_Q_mul hU]

end Residual

/-- Non-vacuity: a concrete orthonormal `U ∈ ℝ^{2×1}`, so the hypotheses `Uᵀ U = 1` of the
results above are satisfiable. -/
example : ∃ U : Matrix (Fin 2) (Fin 1) ℝ, Uᵀ * U = 1 :=
  ⟨Matrix.of ![![1], ![0]], by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]⟩

end LeanDLRA.Literature.P2407_03373
