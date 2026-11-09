import LeanDLRA.Matrix.Frobenius

/-!
# Results of arXiv 2607.27432: Dynamical low-rank filters for data assimilation

This module formalizes the deterministic core of the reduced Kalman-Bucy equation of the
DLRA-JMCO filter, Sec. 3.6 of arXiv 2607.27432, eqs. (39)-(40), in the affine-drift case.

Setting: `U(t) ∈ ℝ^{k×d}` has orthonormal rows (`U Uᵀ = 1`), `C_Y(t) ∈ ℝ^{k×k}` is an invertible
symmetric matrix, `C(t) = Uᵀ C_Y U ∈ ℝ^{d×d}`, `P_U = Uᵀ U`, `P_U^⊥ = 1 - P_U`. The file proves:

* `reducedCov_hasDerivAt`: if `U` and `C_Y` are differentiable at `t` and their derivatives are the
  reduced system (39) of the paper, then `C` has derivative
  `A C + C Aᵀ + Q - P_C^⊥ Q P_C^⊥ - C Hᵀ R⁻¹ H C`, where `P_C` is any symmetric idempotent with
  range equal to the range of `C` (the orthogonal projector onto `range C`). The paper's `dC` is the
  time derivative of this identity; the `dt` form is the derivative at `t`.
* `reducedCov_instance`: a non-vacuous instance (`k = 1`, `d = 2`) where the hypotheses hold and
  the derivative of `C` is zero.
* `printed40_not_hasDerivAt`: the printed form `A C + Aᵀ C + ...` of (40) fails in an instance of
  (39) (`ce_hasDerivAt` is the derivative given by `reducedCov_hasDerivAt` there).
* Helper lemmas: `range_UtU_eq` (range of `Uᵀ U` equals range of `C` when `C_Y` is invertible),
  `proj_eq_of_range` (orthogonal projectors are determined by their range), and `alg_identity`
  (the matrix algebra that turns the product rule into (40)).

Differences from the paper, all deliberate:

* The printed (40) (and the last line of (38)) reads `A(t) C + A(t)ᵀ C`. The first line of (38)
  and the symmetry of `C` give `A C + C Aᵀ`, which is what is proved here. The printed form is not
  the derivative in general: `printed40_not_hasDerivAt` gives an instance of (39) (`U = 1`,
  `A = [[0,1],[0,0]]`, `C_Y(0) = diag(1,2)`, `Q = H = 0`) where `C` does not have the printed
  derivative.
* The printed (40) writes the observation term as `C H(t) R⁻¹ H(t) C`, which only type-checks when
  `H` is square. The file uses `C Hᵀ R⁻¹ H C`, as in (38) and (39).
* The reduced system (39) is taken as hypotheses at time `t`. Its derivation from the Itô
  calculus of (28)-(29) is not formalized. Coefficients `A`, `Q`, `H`, `R⁻¹` are fixed matrices
  (their values at `t`).
* `C_Y` and `Q` are symmetric by hypothesis: they are a covariance and a noise covariance, and
  symmetry is not derivable from the deterministic system.
* `R⁻¹` enters only as an arbitrary matrix `Rinv`, so no invertibility of `R` is assumed.

Core definitions: the file reuses `LeanDLRA.Frobenius.hasDerivAt_transpose` and
`LeanDLRA.Frobenius.hasDerivAt_mul_mul` for the product rule on matrix-valued curves. The
projectors `Uᵀ U` and `1 - Uᵀ U` are written as plain matrices, because the core `leftProj` and
`rightProj` act on `m × n` matrices, not on the `d × d` matrix `C`.

Left out, not formalized: Prop. 3.1 (DLRA-JMCO increments, a first-order minimization over
stochastic quantities), the continuous limit (27)-(30) and its Itô derivation, Lemma 4.1 (local
mean-square error, which needs the stochastic error analysis), Prop. 4.2, and Lemma 5.2 (range
invariance of the particle-filter basis, which needs the algorithm steps and Appendix C).
-/

open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2607_27432

variable {k d m : Type*} [Fintype k] [Fintype d] [Fintype m] [DecidableEq k] [DecidableEq d]

omit [DecidableEq d] in
/-- Cancellation `U (Uᵀ Z) = Z` for `U Uᵀ = 1`. -/
lemma UUt_cancel {U : Matrix k d ℝ} (hUU : U * Uᵀ = 1) (Z : Matrix k d ℝ) :
    U * (Uᵀ * Z) = Z := by
  rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]

omit [DecidableEq d] in
/-- A symmetric idempotent `P` with `P * P = P` is determined by its range: if `P` and `R` have the
same range (as maps `v ↦ P v`), then `P = R`. -/
theorem proj_eq_of_range {P R : Matrix d d ℝ} (hP : Pᵀ = P) (hPi : P * P = P) (hR : Rᵀ = R)
    (hRi : R * R = R) (hr : Set.range (fun v => P *ᵥ v) = Set.range (fun v => R *ᵥ v)) :
    P = R := by
  classical
  have key : ∀ T S : Matrix d d ℝ, T * T = T →
      Set.range (fun v => S *ᵥ v) ⊆ Set.range (fun v => T *ᵥ v) → T * S = S := by
    intro T S hT hsub
    refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    change (T * S) *ᵥ y = S *ᵥ y
    obtain ⟨z, hz⟩ := hsub (Set.mem_range_self y)
    have hz' : T *ᵥ z = S *ᵥ y := hz
    rw [← Matrix.mulVec_mulVec, ← hz', Matrix.mulVec_mulVec, hT]
  have h1 : P * R = R := key P R hPi hr.symm.subset
  have h2 : R * P = P := key R P hRi hr.subset
  have h3 : R * P = R := by
    have h := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, hP, hR] at h
  exact h2.symm.trans h3

omit [DecidableEq d] in
/-- The range of `Uᵀ U` equals the range of `Uᵀ C_Y U` when `U Uᵀ = 1` and `C_Y` is invertible
(`X Y = 1` with `Y = X⁻¹`). -/
theorem range_UtU_eq (U : Matrix k d ℝ) (X Y : Matrix k k ℝ) (hUU : U * Uᵀ = 1)
    (hXY : X * Y = 1) :
    Set.range (fun v => (Uᵀ * U) *ᵥ v) = Set.range (fun v => (Uᵀ * X * U) *ᵥ v) := by
  have hXYU : ∀ Z : Matrix k d ℝ, X * (Y * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hM : (Uᵀ * X * U) * (Uᵀ * Y * U) = Uᵀ * U := by
    simp only [Matrix.mul_assoc, UUt_cancel hUU, hXYU]
  have hPC : (Uᵀ * U) * (Uᵀ * X * U) = Uᵀ * X * U := by
    simp only [Matrix.mul_assoc, UUt_cancel hUU]
  ext z
  simp only [Set.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(Uᵀ * Y * U) *ᵥ y, by rw [Matrix.mulVec_mulVec, hM]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(Uᵀ * X * U) *ᵥ y, by rw [Matrix.mulVec_mulVec, hPC]⟩

/-- Matrix algebra behind eq. (40): the product rule for `Uᵀ X U` with the reduced system (39)
gives `A C + C Aᵀ + Q - P⊥ Q P⊥ - C W C` with `C = Uᵀ X U`, `P = Uᵀ U`, `W` the observation term. -/
theorem alg_identity (U : Matrix k d ℝ) (X Y : Matrix k k ℝ)
    (A Q W : Matrix d d ℝ) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hYs : Yᵀ = Y) (hQ : Qᵀ = Q) :
    ((U * Aᵀ + Y * U * Q) * (1 - Uᵀ * U))ᵀ * X * U
      + Uᵀ * (U * A * Uᵀ * X + X * U * Aᵀ * Uᵀ - X * U * W * Uᵀ * X + U * Q * Uᵀ) * U
      + Uᵀ * X * ((U * Aᵀ + Y * U * Q) * (1 - Uᵀ * U))
    = A * (Uᵀ * X * U) + (Uᵀ * X * U) * Aᵀ + Q - (1 - Uᵀ * U) * Q * (1 - Uᵀ * U)
      - (Uᵀ * X * U) * W * (Uᵀ * X * U) := by
  have hYXU : Y * (X * U) = U := by rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have hXYZ : ∀ Z : Matrix d d ℝ, X * (Y * (U * Z)) = U * Z := fun Z => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have h1 : ((U * Aᵀ + Y * U * Q) * (1 - Uᵀ * U))ᵀ * X * U
      = (1 - Uᵀ * U) * (A * (Uᵀ * X * U) + Q * (Uᵀ * U)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_transpose, hYs, hQ, Matrix.mul_assoc,
      Matrix.add_mul, Matrix.mul_add, hYXU]
  have h2 : Uᵀ * (U * A * Uᵀ * X + X * U * Aᵀ * Uᵀ - X * U * W * Uᵀ * X + U * Q * Uᵀ) * U
      = (Uᵀ * U) * A * (Uᵀ * X * U) + (Uᵀ * X * U) * Aᵀ * (Uᵀ * U)
        - (Uᵀ * X * U) * W * (Uᵀ * X * U) + (Uᵀ * U) * Q * (Uᵀ * U) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have h3 : Uᵀ * X * ((U * Aᵀ + Y * U * Q) * (1 - Uᵀ * U))
      = ((Uᵀ * X * U) * Aᵀ + (Uᵀ * U) * Q) * (1 - Uᵀ * U) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_assoc, hXYZ]
  rw [h1, h2, h3]
  generalize hC : Uᵀ * X * U = C
  generalize hP : Uᵀ * U = P
  noncomm_ring

/-- Eq. (40) of arXiv 2607.27432 (Sec. 3.6), in the affine-drift case, at a time `t`.

Let `U : ℝ → ℝ^{k×d}` and `C_Y : ℝ → ℝ^{k×k}` be differentiable at `t` with derivatives `U'` and
`C_Y'`. Assume `U(t) Uᵀ(t) = 1`, `C_Y(t)` symmetric and invertible, and `Q` symmetric. Assume the
reduced system (39) at `t`:
`U' = (U Aᵀ + C_Y⁻¹ U Q) P_U^⊥` and
`C_Y' = U A Uᵀ C_Y + C_Y U Aᵀ Uᵀ - C_Y U Hᵀ R⁻¹ H Uᵀ C_Y + U Q Uᵀ`.
Let `P_C` be the orthogonal projector onto the range of `C = Uᵀ C_Y U` (symmetric, idempotent, with
range equal to that of `C`). Then `C(s) = U(s)ᵀ C_Y(s) U(s)` has derivative at `t`
`A C + C Aᵀ + Q - P_C^⊥ Q P_C^⊥ - C Hᵀ R⁻¹ H C`, with `P_C^⊥ = 1 - P_C`.

The paper prints `A C + Aᵀ C` and `C H R⁻¹ H C`; see the module docstring and
`printed40_not_hasDerivAt` for why `C Aᵀ` and `C Hᵀ R⁻¹ H C` are proved instead. -/
theorem reducedCov_hasDerivAt (A : Matrix d d ℝ) (Q : Matrix d d ℝ)
    (H : Matrix m d ℝ) (Rinv : Matrix m m ℝ) (U : ℝ → Matrix k d ℝ) (CY : ℝ → Matrix k k ℝ)
    (U' : Matrix k d ℝ) (CY' : Matrix k k ℝ) (PC : Matrix d d ℝ) {t : ℝ}
    (hU : HasDerivAt U U' t) (hCY : HasDerivAt CY CY' t)
    (hUU : U t * (U t)ᵀ = 1) (hCYsym : (CY t)ᵀ = CY t) (hdet : IsUnit (CY t).det)
    (hQsym : Qᵀ = Q)
    (hU' : U' = (U t * Aᵀ + (CY t)⁻¹ * U t * Q) * (1 - (U t)ᵀ * U t))
    (hCY' : CY' = U t * A * (U t)ᵀ * CY t + CY t * U t * Aᵀ * (U t)ᵀ
      - CY t * U t * (Hᵀ * Rinv * H) * (U t)ᵀ * CY t + U t * Q * (U t)ᵀ)
    (hPCsym : PCᵀ = PC) (hPCidem : PC * PC = PC)
    (hPCrange : Set.range (fun v => PC *ᵥ v)
      = Set.range (fun v => ((U t)ᵀ * CY t * U t) *ᵥ v)) :
    HasDerivAt (fun s => (U s)ᵀ * CY s * U s)
      (A * ((U t)ᵀ * CY t * U t) + ((U t)ᵀ * CY t * U t) * Aᵀ + Q
        - (1 - PC) * Q * (1 - PC) - ((U t)ᵀ * CY t * U t) * (Hᵀ * Rinv * H)
        * ((U t)ᵀ * CY t * U t)) t := by
  have hUT : HasDerivAt (fun s => (U s)ᵀ) U'ᵀ t := LeanDLRA.Frobenius.hasDerivAt_transpose hU
  have hd := LeanDLRA.Frobenius.hasDerivAt_mul_mul hUT hCY hU
  have hUsym : ((U t)ᵀ * U t)ᵀ = (U t)ᵀ * U t := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hUidem : (U t)ᵀ * U t * ((U t)ᵀ * U t) = (U t)ᵀ * U t := by
    simp only [Matrix.mul_assoc, UUt_cancel hUU]
  have hPCeq : PC = (U t)ᵀ * U t :=
    proj_eq_of_range hPCsym hPCidem hUsym hUidem
      (hPCrange.trans (range_UtU_eq (U t) (CY t) ((CY t)⁻¹) hUU
        (Matrix.mul_nonsing_inv _ hdet)).symm)
  have hYs : ((CY t)⁻¹)ᵀ = (CY t)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hCYsym]
  refine hd.congr_deriv ?_
  subst hPCeq
  rw [hU', hCY']
  exact alg_identity (U t) (CY t) ((CY t)⁻¹) A Q (Hᵀ * Rinv * H)
    (Matrix.mul_nonsing_inv _ hdet) (Matrix.nonsing_inv_mul _ hdet) hYs hQsym

/-! ### A non-vacuous instance

`k = 1`, `d = 2`, `U = (1 0)`, `C_Y = 1`, `A = H = 0`, `Q = diag(0, 1)`, `R⁻¹ = 1`. Here `U` and
`C_Y` are constant, `U' = 0` and `C_Y' = 0` solve the reduced system (39), and the reduced
covariance `C = Uᵀ C_Y U = diag(1, 0)` has derivative `0`, which is the right-hand side of (40). -/

/-- The row `U = (1 0)` of the instance. -/
def instU : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

/-- The noise matrix `Q = diag(0, 1)` of the instance. -/
def instQ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

theorem instU_mul_transpose : instU * instUᵀ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [instU, Matrix.mul_apply, Fin.sum_univ_two]

theorem instQ_transpose : instQᵀ = instQ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [instQ]

/-- In the instance, `C = Uᵀ C_Y U` is stationary: the derivative of `C` is zero, which is the
right-hand side of (40) for this instance. -/
theorem reducedCov_instance :
    HasDerivAt (fun _ : ℝ => instUᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * instU) 0 0 := by
  have hU' : (0 : Matrix (Fin 1) (Fin 2) ℝ)
      = (instU * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ + (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * instU
        * instQ) * (1 - instUᵀ * instU) := by
    ext i j
    fin_cases i
    fin_cases j <;> simp [instU, instQ, Matrix.mul_apply, Fin.sum_univ_two, inv_one]
  have hCY' : (0 : Matrix (Fin 1) (Fin 1) ℝ) = instU * (0 : Matrix (Fin 2) (Fin 2) ℝ) * instUᵀ
      * (1 : Matrix (Fin 1) (Fin 1) ℝ) + (1 : Matrix (Fin 1) (Fin 1) ℝ) * instU
      * (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * instUᵀ
      - (1 : Matrix (Fin 1) (Fin 1) ℝ) * instU * ((0 : Matrix (Fin 1) (Fin 2) ℝ)ᵀ
      * (1 : Matrix (Fin 1) (Fin 1) ℝ) * (0 : Matrix (Fin 1) (Fin 2) ℝ)) * instUᵀ
      * (1 : Matrix (Fin 1) (Fin 1) ℝ) + instU * instQ * instUᵀ := by
    ext i j
    fin_cases i
    fin_cases j
    simp [instU, instQ, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h := reducedCov_hasDerivAt (k := Fin 1) (d := Fin 2) (m := Fin 1) 0 instQ 0 1
    (fun _ => instU) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 (instUᵀ * instU) (t := 0)
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) instU_mul_transpose (by simp) (by simp)
    instQ_transpose hU' hCY' (by rw [Matrix.transpose_mul, Matrix.transpose_transpose])
    (by simp only [Matrix.mul_assoc, LeanDLRA.Literature.P2607_27432.UUt_cancel
      instU_mul_transpose])
    (range_UtU_eq instU (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 instU_mul_transpose (by simp))
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [instU, instQ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The printed form of (40) is not the derivative

`k = d = 2`, `m = 1`, `U = 1` (constant), `A = [[0,1],[0,0]]`, `Q = 0`, `H = 0`, `R⁻¹ = 0`,
`C_Y(s) = C₀ + s (A C₀ + C₀ Aᵀ)` with `C₀ = diag(1, 2)`. Then (39) holds at `t = 0`, `P_C = 1`, and
`C = C_Y` has derivative `A C₀ + C₀ Aᵀ = [[0,2],[2,0]]` at `0`, while the printed right-hand side
`A C₀ + Aᵀ C₀ = [[0,2],[1,0]]` differs in the entry `(1, 0)`. -/

/-- The drift `A = [[0,1],[0,0]]` of the counterexample. -/
def ceA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The reduced covariance `C₀ = diag(1, 2)` at time `0` in the counterexample. -/
def ceC0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

/-- The curve `C_Y(s) = C₀ + s (A C₀ + C₀ Aᵀ)` of the counterexample. -/
def ceCY (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := ceC0 + s • (ceA * ceC0 + ceC0 * ceAᵀ)

theorem ceCY_zero : ceCY 0 = ceC0 := by simp [ceCY]

theorem ceC0_det : IsUnit ceC0.det := by
  simp [ceC0, Matrix.det_fin_two]

/-- `reducedCov_hasDerivAt` in the counterexample: the hypotheses (39) hold at `t = 0`, and the
derivative of `C = Uᵀ C_Y U` is `A C₀ + C₀ Aᵀ`. -/
theorem ce_hasDerivAt :
    HasDerivAt (fun s => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY s * 1)
      (ceA * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)
        + ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1) * ceAᵀ + 0
        - (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) * 0 * (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)
        - ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)
          * ((0 : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * (0 : Matrix (Fin 1) (Fin 1) ℝ)
            * (0 : Matrix (Fin 1) (Fin 2) ℝ))
          * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)) 0 := by
  have hdet : IsUnit (ceCY 0).det := by rw [ceCY_zero]; exact ceC0_det
  have hCY : HasDerivAt ceCY (ceA * ceC0 + ceC0 * ceAᵀ) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (ceA * ceC0 + ceC0 * ceAᵀ)).const_add ceC0
    rw [one_smul] at h
    exact h
  refine reducedCov_hasDerivAt (k := Fin 2) (d := Fin 2) (m := Fin 1) ceA 0 0 0
    (fun _ => 1) ceCY 0 (ceA * ceC0 + ceC0 * ceAᵀ) ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)
    (hasDerivAt_const _ _) hCY (by simp) ?_ hdet (by simp) (by simp) ?_ (by simp) (by simp)
    (range_UtU_eq 1 (ceCY 0) (ceCY 0)⁻¹ (by simp) (Matrix.mul_nonsing_inv _ hdet))
  · rw [ceCY_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ceC0]
  · rw [ceCY_zero]
    simp

/-- The printed right-hand side of (40), `A C + Aᵀ C + Q - P_C^⊥ Q P_C^⊥ - C Hᵀ R⁻¹ H C`, is not
the derivative of `C = Uᵀ C_Y U` in the instance `ce_hasDerivAt` of the reduced system (39). -/
theorem printed40_not_hasDerivAt :
    ¬ HasDerivAt (fun s => (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY s * 1)
      (ceA * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)
        + ceAᵀ * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1) + 0
        - (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1) * 0 * (1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1)
        - ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)
          * ((0 : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * (0 : Matrix (Fin 1) (Fin 1) ℝ)
            * (0 : Matrix (Fin 1) (Fin 2) ℝ))
          * ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * ceCY 0 * 1)) 0 := by
  intro h
  have h10 := congrFun (congrFun (h.unique ce_hasDerivAt) 1) 0
  rw [ceCY_zero] at h10
  norm_num [ceA, ceC0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h10

end LeanDLRA.Literature.P2607_27432
