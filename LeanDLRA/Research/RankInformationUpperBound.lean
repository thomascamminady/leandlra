import LeanDLRA.Research.InformationLowerBound
import LeanDLRA.DLRA.QuasiOptimalitySpeedSharp

/-!
# An upper bound for a method that evaluates the field on low-rank matrices only

Every method that uses `F` only through its values on the matrices of rank at most `k` has error
at least `L ∫₀ᵀ dist(A(s), M_{≤ k}) ds` for one of two `L`-Lipschitz fields
(`LeanDLRA/Research/InformationLowerBound.lean`). This file has an upper bound of the same form
for a method of this kind whose state is a full matrix: a curve `Z` with

    ‖Ż(t) - F(t, Z(t))‖ ≤ L dist(Z(t), M_{≤ k}) + η,

for example `Ż(t) = F(t, W(t))` with `W(t)` a best approximation of rank at most `k` of `Z(t)`
(`η = 0`) or the interpolant of an explicit Euler method with these field values (`η` its
consistency error), satisfies

    ‖Z(T) - A(T)‖ ≤ e^{2LT} ‖Z(0) - A(0)‖ + ∫₀ᵀ e^{2L(T-s)} (L dist(A(s), M_{≤ k}) + η) ds.

No singular value of `A` or `Z` and no gap enters. A best approximation of rank at most `r` of
`Z(T)` has error at most `dist(A(T), M_{≤ r}) + 2 ‖Z(T) - A(T)‖`.

For the rotating projector `X(t) = u(t) u(t)ᵀ` of `LeanDLRA/DLRA/QuasiOptimalitySpeedSharp.lean`
and the data `A(t) = X(t) + ε (1 - X(0))`, with the field `F(t, Z) = Ẋ(t)` (Lipschitz constant
`0`), `X` is the solution of rank one of the projected equation from the best approximation
`X(0)` of `A(0) = diag(1, ε)`. Its error is `ε` for all times, also at `t = π/2`, where
`A(π/2) = (1 + ε) X(π/2)` has rank one, while the curve `Z = A` of the bound above has error `0`.

## Main results

* `RankInformationUpperBound.norm_sub_le_mul_distLR_of_norm_sub_eq`: the defect of
  `Ż = F(t, W)` for a best approximation `W` of `Z`.
* `RankInformationUpperBound.norm_sub_le_exp_mul_add_integral_distLR`: the error bound.
* `RankInformationUpperBound.norm_sub_le_distLR_add_two_mul`: truncation of the result.
* `RankInformationUpperBoundExample.isDLRASolution_rotProj`, `odeSolution_hiddenData`,
  `norm_hiddenData_sub`, `rank_hiddenData_pi_div_two`, `distLR_hiddenData_zero`: the example.
-/

open Set MeasureTheory
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.RankInformationUpperBound

variable {m n : Type*} [Fintype m] [Fintype n]

/-- If `W` is at the distance `dist(Z, M_{≤ k})` from `Z` (a best approximation), then the field
value at `W` differs from the field value at `Z` by at most `L dist(Z, M_{≤ k})`. -/
theorem norm_sub_le_mul_distLR_of_norm_sub_eq {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L : ℝ}
    {k : ℕ} (hF : IsLipschitzField F L) (t : ℝ) {Z W : Matrix m n ℝ}
    (hW : ‖W - Z‖ = distLR k Z) :
    ‖F t W - F t Z‖ ≤ L * distLR k Z := by
  rw [← hW]
  exact hF t W Z

/-- **Error of a curve driven by field values at low-rank matrices.** Let `F` be `L`-Lipschitz,
let `A` solve `y' = F(t, y)` on `[0, T]` and let the curve `Z` have right derivatives `Z'` with
`‖Z'(t) - F(t, Z(t))‖ ≤ L dist(Z(t), M_{≤ k}) + η`. Then
`‖Z(T) - A(T)‖ ≤ e^{2LT} ‖Z(0) - A(0)‖ + ∫₀ᵀ e^{2L(T-s)} (L dist(A(s), M_{≤ k}) + η) ds`. -/
theorem norm_sub_le_exp_mul_add_integral_distLR {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A Z Z' : ℝ → Matrix m n ℝ} {L T η : ℝ} {k : ℕ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hA : ODESolution F A 0 T) (hZc : ContinuousOn Z (Icc 0 T))
    (hZ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt Z (Z' t) (Ici t) t)
    (hdef : ∀ t ∈ Ico (0 : ℝ) T, ‖Z' t - F t (Z t)‖ ≤ L * distLR k (Z t) + η)
    (hT : 0 ≤ T) :
    ‖Z T - A T‖ ≤ Real.exp (2 * L * T) * ‖Z 0 - A 0‖ +
      ∫ s in (0 : ℝ)..T, Real.exp (2 * L * (T - s)) * (L * distLR k (A s) + η) := by
  set g : ℝ → ℝ :=
    fun s => L * distLR k (IccExtend hT ((Icc (0 : ℝ) T).domRestrict A) s) + η with hg
  have hgc : Continuous g := (continuous_const.mul
    ((lipschitzWith_distLR k).continuous.comp hA.cont.domRestrict.Icc_extend')).add continuous_const
  have hgA : ∀ s ∈ Icc (0 : ℝ) T, g s = L * distLR k (A s) + η := fun s hs => by
    simp only [hg, IccExtend_of_mem _ _ hs, domRestrict_apply]
  have hf' : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun x : ℝ => Z x - A x) (Z' x - F x (A x)) (Ici x) x :=
    fun x hx => (hZ x hx).sub (hA.deriv x hx)
  have key := norm_le_exp_integral_mul_add_integral_exp_integral_mul
    (f := fun x : ℝ => Z x - A x) (f' := fun x => Z' x - F x (A x)) (δ := ‖Z 0 - A 0‖) (a := 0)
    (b := T) (k := fun _ => 2 * L) (g := g) continuous_const hgc (hZc.sub hA.cont) hf' le_rfl
    (fun x hx => by
      rw [hgA x (Ico_subset_Icc_self hx)]
      have h1 := hdef x hx
      have h2 := hF x (Z x) (A x)
      have h3 := distLR_le_add (r := k) (Z x) (A x)
      have h4 : ‖Z' x - F x (A x)‖ ≤ ‖Z' x - F x (Z x)‖ + ‖F x (Z x) - F x (A x)‖ := by
        have e : Z' x - F x (A x) = Z' x - F x (Z x) + (F x (Z x) - F x (A x)) := by abel
        rw [e]
        exact norm_add_le _ _
      nlinarith [mul_le_mul_of_nonneg_left h3 hL]) T (right_mem_Icc.2 hT)
  have hint : ∫ s in (0 : ℝ)..T, Real.exp (∫ _ in s..T, 2 * L) * g s =
      ∫ s in (0 : ℝ)..T, Real.exp (2 * L * (T - s)) * (L * distLR k (A s) + η) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    rw [hgA s hs, intervalIntegral.integral_const, smul_eq_mul,
      show (T - s) * (2 * L) = 2 * L * (T - s) by ring]
  rw [hint, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    show T * (2 * L) = 2 * L * T by ring] at key
  exact key

/-- **Truncation of the result.** If `X` is a best approximation of `Z` in `M_{≤ r}`, then
`‖X - A‖ ≤ dist(A, M_{≤ r}) + 2 ‖Z - A‖`. -/
theorem norm_sub_le_distLR_add_two_mul {r : ℕ} {A Z X : Matrix m n ℝ}
    (hX : ‖X - Z‖ = distLR r Z) : ‖X - A‖ ≤ distLR r A + 2 * ‖Z - A‖ := by
  have h1 := distLR_le_add (r := r) Z A
  have h2 : ‖X - A‖ ≤ ‖X - Z‖ + ‖Z - A‖ := by
    have e : X - A = X - Z + (Z - A) := by abel
    rw [e]
    exact norm_add_le _ _
  linarith

/-- The hypotheses of `norm_sub_le_exp_mul_add_integral_distLR` hold with `L = 1` for a constant
field and its solution. -/
example (B : Matrix m n ℝ) :
    ‖(1 : ℝ) • B - (1 : ℝ) • B‖ ≤ Real.exp (2 * 1 * 1) * ‖(0 : ℝ) • B - (0 : ℝ) • B‖ +
      ∫ s in (0 : ℝ)..1, Real.exp (2 * 1 * (1 - s)) * (1 * distLR 0 (s • B) + 1) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun x : ℝ => x • B) B t := fun t => by
    simpa using (hasDerivAt_id t).smul_const B
  have hc : Continuous fun x : ℝ => x • B := by fun_prop
  have hF : IsLipschitzField (fun (_ : ℝ) (_ : Matrix m n ℝ) => B) 1 := fun t x y => by simp
  have hdef : ∀ t ∈ Ico (0 : ℝ) 1, ‖B - B‖ ≤ 1 * distLR 0 (t • B) + 1 := fun t _ => by
    have h : 0 ≤ distLR 0 (t • B) := distLR_nonneg
    rw [sub_self, norm_zero]
    linarith
  exact norm_sub_le_exp_mul_add_integral_distLR (F := fun _ _ => B) (A := fun x : ℝ => x • B)
    (Z := fun x : ℝ => x • B) (Z' := fun _ => B) (L := 1) (T := 1) (η := 1) (k := 0) hF
    zero_le_one ⟨hc.continuousOn, fun t _ => (hd t).hasDerivWithinAt⟩ hc.continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) hdef zero_le_one

end LeanDLRA.RankInformationUpperBound

/-! ### The rotating projector with a hidden part -/

namespace LeanDLRA.RankInformationUpperBoundExample

open LeanDLRA.QuasiOptimalitySpeedExample

/-- The data `A t = X t + ε (1 - X 0)`: the rotating projector and a constant part. -/
noncomputable def hiddenData (ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotProj t + ε • (1 - rotProj 0)

/-- `X` is the solution of rank one of the projected equation for the field `F(t, Z) = Ẋ(t)`. -/
theorem isDLRASolution_rotProj (T : ℝ) :
    IsDLRASolution 1 (fun t _ => rotProjDeriv t) rotProj 0 T := by
  refine ⟨⟨fun t _ => (hasDerivAt_rotProj t).continuousAt.continuousWithinAt, fun t _ => ?_⟩,
    fun t _ => rank_rotProj t⟩
  beta_reduce
  rw [tangentProjAt_rotProjDeriv]
  exact (hasDerivAt_rotProj t).hasDerivWithinAt

/-- The data solve `y' = Ẋ(t)`. -/
theorem odeSolution_hiddenData (ε T : ℝ) :
    ODESolution (fun t _ => rotProjDeriv t) (hiddenData ε) 0 T := by
  have hd : ∀ t, HasDerivAt (hiddenData ε) (rotProjDeriv t) t := fun t =>
    (hasDerivAt_rotProj t).add_const _
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- The error of `X` is `ε` at all times. -/
theorem norm_hiddenData_sub {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : ‖hiddenData ε t - rotProj t‖ = ε := by
  rw [hiddenData, add_sub_cancel_left, norm_smul, norm_one_sub_rotProj, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hε]

/-- At `t = π/2` the data are `(1 + ε) X(π/2)`. -/
theorem hiddenData_pi_div_two (ε : ℝ) :
    hiddenData ε (Real.pi / 2) = (1 + ε) • rotProj (Real.pi / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hiddenData, rotProj_eq_of]

/-- At `t = π/2` the data have rank at most one. -/
theorem rank_hiddenData_pi_div_two (ε : ℝ) : (hiddenData ε (Real.pi / 2)).rank ≤ 1 := by
  have e : hiddenData ε (Real.pi / 2) =
      rotCol (Real.pi / 2) * ((1 + ε) • (rotCol (Real.pi / 2))ᵀ) := by
    rw [hiddenData_pi_div_two, Matrix.mul_smul, rotProj]
  rw [e]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_width _).trans (by simp))

/-- The start `X 0` is at the distance `ε = dist(A 0, M_{≤ 1})` from `A 0 = diag(1, ε)`. -/
theorem distLR_hiddenData_zero {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    distLR 1 (hiddenData ε 0) = ε := by
  have e : hiddenData ε 0 = Matrix.diagonal ![1, ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hiddenData, rotProj_eq_of]
  rw [e]
  exact InformationLowerBoundExample.distLR_one_diagonal hε hε1

/-- **The projected equation keeps the initial error.** For `0 ≤ ε ≤ 1`: `X` solves the projected
equation of rank one from a best approximation of `A 0`, the data `A` solve the equation with a
field of Lipschitz constant `0`, `A(π/2)` has rank at most one, and `‖A(π/2) - X(π/2)‖ = ε`. -/
theorem dlra_error_eq_at_rank_one {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsDLRASolution 1 (fun t _ => rotProjDeriv t) rotProj 0 (Real.pi / 2) ∧
      ODESolution (fun t _ => rotProjDeriv t) (hiddenData ε) 0 (Real.pi / 2) ∧
      IsLipschitzField (fun t (_ : Matrix (Fin 2) (Fin 2) ℝ) => rotProjDeriv t) 0 ∧
      ‖hiddenData ε 0 - rotProj 0‖ = distLR 1 (hiddenData ε 0) ∧
      (hiddenData ε (Real.pi / 2)).rank ≤ 1 ∧
      ‖hiddenData ε (Real.pi / 2) - rotProj (Real.pi / 2)‖ = ε := by
  refine ⟨isDLRASolution_rotProj _, odeSolution_hiddenData ε _, fun t x y => by simp, ?_,
    rank_hiddenData_pi_div_two ε, norm_hiddenData_sub hε _⟩
  rw [norm_hiddenData_sub hε, distLR_hiddenData_zero hε hε1]

end LeanDLRA.RankInformationUpperBoundExample
