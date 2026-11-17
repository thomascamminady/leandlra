import LeanDLRA.Stability.Energy
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Projectors
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Open problems OP-SB-41, OP-SB-43, OP-SB-44, OP-SB-45
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.OpenProblems.Stability

/-- **OP-SB-41 (i)** (arXiv 2407.11792).  A chemical-master-equation generator (nonnegative
off-diagonal rates, zero column sums) need not be dissipative in `ℓ²`: there are such `Q` and
`p` with `⟪Q p, p⟫ > 0`, so `ℓ²` energy arguments cannot explain the stability of explicit Euler
DLRA for the CME; a weighted norm or `ℓ¹`/positivity argument is required. -/
theorem cme_not_dissipative :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ), (∀ i j, i ≠ j → 0 ≤ Q i j) ∧
      (∀ j, ∑ i, Q i j = 0) ∧ 0 < p ⬝ᵥ (Q *ᵥ p) := by
  refine ⟨!![-1, 0; 1, 0], ![1, 2], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]

/-- **OP-SB-41 (ii)** (arXiv 2611.04360).  Non-multiplying scattering does not give `γ = 0` in
the velocity-weighted quadratic norm: for the two-group collision matrix
`C = [[-1, 5], [0, -5]]` (all of group 2 up-scatters into group 1; scattering out of each group
never exceeds its removal) and *every* choice of group speeds `v > 0`, the symmetrised
`V^{1/2}`-weighted collision matrix is indefinite. -/
theorem upscattering_indefinite (v : Fin 2 → ℝ) (hv : ∀ i, 0 < v i) :
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 5; 0, -5]
    let M := Matrix.diagonal (fun i => Real.sqrt (v i)) * C *
      Matrix.diagonal (fun i => Real.sqrt (v i))
    (∀ j, ∑ i, (if i = j then 0 else C i j) ≤ -C j j) ∧ ∃ x : Fin 2 → ℝ, 0 < x ⬝ᵥ (M *ᵥ x) := by
  intro C M
  refine ⟨?_, ![2 * Real.sqrt (v 1), Real.sqrt (v 0)], ?_⟩
  · intro j
    fin_cases j <;> simp [C, Fin.sum_univ_two]
  · have h0 := Real.sq_sqrt (hv 0).le
    have h1 := Real.sq_sqrt (hv 1).le
    have p := mul_pos (hv 0) (hv 1)
    simp [M, C, dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.mul_apply]
    nlinarith

section Nystrom

open scoped LeanDLRA.Frobenius

/-- **OP-SB-43, non-robust DGN assembly** (arXiv 2410.17091, 2409.06384).  For
`Z = diag(1, σ)`, sketches `Ω = e₂`, `Ψ = e₁ + e₂`, `B = Z Ω`, `C = Zᵀ Ψ`, `D = Ψᵀ Z Ω = σ`, a
perturbation `η e₁` of `B` changes the assembly `B D⁻¹ Cᵀ` by `|η| √(1 + σ²) / σ`: the error is of
order `η / σ_r` and not robust to small singular values. -/
theorem dgn_perturbation {σ η : ℝ} (hσ : 0 < σ) :
    let Z : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, σ]
    let Ω : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
    let Ψ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]
    let B := Z * Ω
    let C := Zᵀ * Ψ
    let D := Ψᵀ * Z * Ω
    let e : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    ‖(B + η • e) * D⁻¹ * Cᵀ - B * D⁻¹ * Cᵀ‖ = |η| * Real.sqrt (1 + σ ^ 2) / σ := by
  intro Z Ω Ψ B C D e
  have hD : D = !![σ] := by
    ext i j
    fin_cases i; fin_cases j
    simp [D, Z, Ω, Ψ, Matrix.mul_apply, Fin.sum_univ_two]
  have hDi : D⁻¹ = !![σ⁻¹] := by
    rw [hD]; ext i j
    fin_cases i; fin_cases j
    simp [Ring.inverse_eq_inv]
  have hB : B = !![0; σ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, Z, Ω]
  have hC : C = !![1; σ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, Z, Ψ, Matrix.mul_apply, Fin.sum_univ_two]
  have key : (B + η • e) * D⁻¹ * Cᵀ - B * D⁻¹ * Cᵀ = !![η / σ, η; 0, 0] := by
    rw [hDi, hB, hC]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e,
          Function.swap, Matrix.vecHead, Matrix.vecTail] <;> field_simp
  rw [key, Frobenius.norm_def]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  have h1 : (0:ℝ) ≤ 1 + σ ^ 2 := by positivity
  have hsq := Real.sq_sqrt h1
  have hr : (η / σ) ^ 2 + η ^ 2 = (|η| * Real.sqrt (1 + σ ^ 2) / σ) ^ 2 := by
    rw [div_pow (|η| * _), mul_pow, hsq, sq_abs]
    field_simp
  rw [hr]
  exact Real.sqrt_sq (by positivity)

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [DecidableEq k]
  [DecidableEq l]

/-- **OP-SB-43, robust Galerkin core** (arXiv 2410.17091).  A Galerkin core on orthonormal
bases (BUG-type S-step) is robust: a perturbation `Δ` of the data changes
`U Uᵀ Z V Vᵀ` by at most `‖Δ‖`, independently of singular values. -/
theorem galerkinCore_perturbation {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) {V : Matrix n l ℝ}
    (hV : Vᵀ * V = 1) (Z Δ : Matrix m n ℝ) :
    ‖U * Uᵀ * (Z + Δ) * V * Vᵀ - U * Uᵀ * Z * V * Vᵀ‖ ≤ ‖Δ‖ := by
  have h := (isOrthProj_leftProj_mul_rightProj (n := n) hU hV).norm_le Δ
  have e : U * Uᵀ * (Z + Δ) * V * Vᵀ - U * Uᵀ * Z * V * Vᵀ =
      (leftProj U * rightProj V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) Δ := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [e]
  exact h

end Nystrom

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **OP-SB-44** (arXiv 2407.01404).  Meta-theorem for Petrov–Galerkin DLR: if both iterates lie
in the test space `W` and the step equation `v - u - h G` is orthogonal to `W`, then the full-order
energy identity `‖v‖² - ‖u‖² + ‖v - u‖² = 2 h ⟪G, v⟫` holds verbatim; every property proved by
testing with `span {uⁿ, uⁿ⁺¹}` transfers. -/
theorem pg_energy_identity {W : Submodule ℝ E} {u v G : E} {h : ℝ} (hu : u ∈ W) (hv : v ∈ W)
    (hstep : ∀ w ∈ W, ⟪v - u - h • G, w⟫ = 0) :
    ‖v‖ ^ 2 - ‖u‖ ^ 2 + ‖v - u‖ ^ 2 = 2 * h * ⟪G, v⟫ := by
  have h1 := hstep (v - u) (W.sub_mem hv hu)
  have h2 := hstep v hv
  have e1 : ‖v - u‖ ^ 2 = ⟪v - u, v - u⟫ := (real_inner_self_eq_norm_sq _).symm
  have e2 : ‖v‖ ^ 2 = ⟪v, v⟫ := (real_inner_self_eq_norm_sq _).symm
  have e3 : ‖u‖ ^ 2 = ⟪u, u⟫ := (real_inner_self_eq_norm_sq _).symm
  simp only [inner_sub_left, inner_sub_right, inner_smul_left] at h1 h2
  simp only [RCLike.conj_to_real] at h1 h2
  rw [e1, e2, e3]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm u v] at *
  nlinarith

/-- **OP-SB-45** (arXiv 1906.01369, Sec. 6.3; spectral gap as hypothesis).  In imaginary time
`y' = -H y`, with `H` self-adjoint and commuting with the orthogonal projector `Pa` onto the
anti-symmetric subspace, `H ≥ E_F` there, and a symmetric eigenvector `H φ = E_B φ`
(`Pa φ = 0`), a start `a + φ` evolves with `(1 - Pa) y(t) = e^{-E_B t} φ` and
`‖Pa y(t)‖ ≤ e^{-E_F t} ‖a‖`: symmetric components grow relative to the fermionic part like
`e^{(E_F - E_B) t}`, so the anti-symmetric state is unstable under round-off. -/
theorem imaginaryTime_symmetric_growth {H Pa : E →L[ℝ] E} (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hPa : IsOrthProj Pa) (hc : ∀ x, Pa (H x) = H (Pa x)) {EF EB : ℝ}
    (hEF : ∀ x, Pa x = x → EF * ‖x‖ ^ 2 ≤ ⟪H x, x⟫) {φ a : E} (hφ : H φ = EB • φ)
    (hPφ : Pa φ = 0) (ha : Pa a = a) {T : ℝ} {y : ℝ → E}
    (hy : ODESolution (fun _ x => -H x) y 0 T) (hy₀ : y 0 = a + φ) :
    ∀ t ∈ Icc 0 T, y t - Pa (y t) = Real.exp (-EB * t) • φ ∧
      ‖Pa (y t)‖ ≤ Real.exp (-EF * t) * ‖a‖ := by
  have _ := hH
  have hPaa : Pa (a + φ) = a := by rw [map_add, ha, hPφ, add_zero]
  have hder : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt y (-H (y t)) (Ici t) t :=
    fun t ht => hy.deriv t ht
  have hPaPa : ∀ x, Pa (Pa x) = Pa x := hPa.idem
  -- the symmetric part
  have hq : ∀ t ∈ Icc (0:ℝ) T, y t - Pa (y t) - Real.exp (-EB * t) • φ = 0 := by
    intro t ht
    have h := norm_le_exp_of_inner_deriv_le (a := 0) (b := T) (ℓ := ‖H‖)
      (y := fun t => y t - Pa (y t) - Real.exp (-EB * t) • φ)
      (v := fun t => -H (y t - Pa (y t) - Real.exp (-EB * t) • φ))
      ((hy.cont.sub (Pa.continuous.comp_continuousOn hy.cont)).sub
        ((Continuous.continuousOn (by fun_prop))))
      (by
        intro t ht
        have h1 := hder t ht
        have h2 := Pa.hasFDerivAt.comp_hasDerivWithinAt t h1
        have h3 : HasDerivAt (fun t : ℝ => Real.exp (-EB * t))
            (Real.exp (-EB * t) * (-EB)) t := by
          simpa using ((hasDerivAt_id t).const_mul (-EB)).exp
        have h4 := (h3.smul_const φ).hasDerivWithinAt (s := Ici t)
        have h5 := (h1.sub h2).sub h4
        refine h5.congr_deriv ?_
        simp only [map_neg, map_sub, map_smul, hc, hφ]
        module)
      (by
        intro t ht
        refine (real_inner_le_norm _ _).trans ?_
        have := H.le_opNorm (y t - Pa (y t) - Real.exp (-EB * t) • φ)
        rw [norm_neg, sq]
        nlinarith [norm_nonneg (y t - Pa (y t) - Real.exp (-EB * t) • φ)])
      t ht
    have h0 : y 0 - Pa (y 0) - Real.exp (-EB * 0) • φ = 0 := by
      rw [hy₀, hPaa]; simp
    rw [h0, norm_zero, mul_zero] at h
    exact norm_eq_zero.1 (le_antisymm h (norm_nonneg _))
  intro t ht
  refine ⟨sub_eq_zero.1 (hq t ht), ?_⟩
  have h := norm_le_exp_of_inner_deriv_le (a := 0) (b := T) (ℓ := -EF)
    (y := fun t => Pa (y t)) (v := fun t => -H (Pa (y t)))
    (Pa.continuous.comp_continuousOn hy.cont)
    (by
      intro t ht
      have h2 := Pa.hasFDerivAt.comp_hasDerivWithinAt t (hder t ht)
      refine h2.congr_deriv ?_
      rw [map_neg, hc])
    (by
      intro t _
      have := hEF (Pa (y t)) (hPaPa _)
      rw [inner_neg_left]
      linarith)
    t ht
  simpa [hy₀, hPaa, mul_comm] using h

end Abstract

section Kalman

variable {n : Type*} [Fintype n] [DecidableEq n]

end Kalman

section Cross

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

end Cross

section Abstract2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract2

section Abstract3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Abstract3

section Multiplier

variable {m k : Type*} [Fintype m] [Fintype k]

end Multiplier

end LeanDLRA.OpenProblems.Stability
