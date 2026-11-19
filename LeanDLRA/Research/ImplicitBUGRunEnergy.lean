import LeanDLRA.Research.ImplicitBUGRationalKrylov
import LeanDLRA.Matrix.Curvature

/-!
# Runs of the implicit BUG integrator for the Sylvester heat field: summable stiff energies

For the field `F(Z) = -BᵀB Z - Z CᵀC` (two symmetric negative semidefinite matrices of any norm)
the S-step of the BUG integrator with backward Euler substeps satisfies the energy identity
`‖Ŷ‖² + h ‖B Ŷ‖² + h ‖Ŷ Cᵀ‖² = ⟪Y₀, Ŷ⟫` (`IsMatrixImplicitBUGStep.energy_eq_inner_of_sylvester`).
A truncation by the singular value decomposition is a multiplication by an orthogonal projector
from the left and, at the same time, by one from the right; it increases neither the norm nor the
stiff energy `h (‖B Y‖² + ‖Y Cᵀ‖²)`. Hence along a run

  `‖Y_N‖² / 2 + ∑ j < N, h (‖B Yⱼ₊₁‖² + ‖Yⱼ₊₁ Cᵀ‖²) ≤ ‖Y₀‖² / 2`,

whatever the bases are and however large `B` and `C` are. If the residual bound `δⱼ` of the run
theorem `norm_implicitBUG_run_sub_le_of_sylvester_residual` has the form
`a ‖Yⱼ‖ + b (h ‖B Yⱼ‖² + h ‖Yⱼ Cᵀ‖²)^{1/2}` (for bases that contain the factors of `k` ADI steps
with shifts of the interval `[1/2, 1/2 + R]`, a spectral splitting of the ADI residual gives
`a = ρ_k`, the Zolotarev number of that interval, and `b = R^{-1/2}`), then the sum of the
residual bounds is at most `a N ‖Y₀‖ + b ((h ‖B Y₀‖² + h ‖Y₀ Cᵀ‖²)^{1/2} + (N/2)^{1/2} ‖Y₀‖)`:
the distance to the backward Euler run on the full matrix is bounded without any bound of `B`
or `C`.

## Main results

* `IsMatrixImplicitBUGStep.half_sq_norm_add_energy_le_of_sylvester`: one step followed by a
  truncation by orthogonal projectors.
* `half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester`: the energies of a run are
  summable.
* `norm_implicitBUG_run_sub_le_of_sylvester_energy_residual`: the run bound with residual bounds
  of the form `a ‖Yⱼ‖ + b (energy of Yⱼ)^{1/2}`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
* ADI and Zolotarev numbers: arXiv 1609.09494 (Beckermann, Townsend), Corollary 3.2.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

open Matrix

namespace LeanDLRA

open Curvature

section Step

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {B : Matrix p m ℝ} {C : Matrix q n ℝ} {ε τ ϑ t₁ h : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ : Matrix m n ℝ}

/-- **One step with a projector truncation does not increase norm plus stiff energy.** For
`F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0` and any new bases: if the result `Y₁` of the step is obtained
from the Galerkin result `U₁ S₁ V₁ᵀ` by an orthogonal projector `T` from the left and also by an
orthogonal projector `T'` from the right (a truncated singular value decomposition is both), then

  `‖Y₁‖² / 2 + h (‖B Y₁‖² + ‖Y₁ Cᵀ‖²) ≤ ‖Y₀‖² / 2`,  `Y₀ = U₀ S₀ V₀ᵀ`.

No bound of `B` or `C` is used. -/
theorem IsMatrixImplicitBUGStep.half_sq_norm_add_energy_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    {T : Matrix m m ℝ} {T' : Matrix n n ℝ} (hT : IsOrthProjMat T) (hT' : IsOrthProjMat T')
    (hY : Y₁ = T * (U₁ * S₁ * V₁ᵀ)) (hY' : Y₁ = U₁ * S₁ * V₁ᵀ * T') :
    ‖Y₁‖ ^ 2 / 2 + h * (‖B * Y₁‖ ^ 2 + ‖Y₁ * Cᵀ‖ ^ 2) ≤ ‖U₀ * S₀ * V₀ᵀ‖ ^ 2 / 2 := by
  have e := hs.energy_eq_inner_of_sylvester
  have hi := real_inner_le_norm (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
  have h1 : ‖Y₁‖ ≤ ‖U₁ * S₁ * V₁ᵀ‖ := by
    rw [hY]
    exact hT.norm_mul_le _
  have h2 : ‖B * Y₁‖ ≤ ‖B * (U₁ * S₁ * V₁ᵀ)‖ := by
    rw [hY', ← Matrix.mul_assoc]
    exact hT'.norm_mul_le' _
  have h3 : ‖Y₁ * Cᵀ‖ ≤ ‖U₁ * S₁ * V₁ᵀ * Cᵀ‖ := by
    rw [hY, Matrix.mul_assoc]
    exact hT.norm_mul_le _
  have s1 := mul_self_le_mul_self (norm_nonneg _) h1
  have s2 := mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg _) h2) hh
  have s3 := mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg _) h3) hh
  nlinarith [sq_nonneg (‖U₀ * S₀ * V₀ᵀ‖ - ‖U₁ * S₁ * V₁ᵀ‖)]

end Step

section Run

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ} {ε τ ϑ t : ℕ → ℝ}
  {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
  {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → Matrix m (Fin r) ℝ} {L : ℕ → Matrix n (Fin r) ℝ}
  {U' : ℕ → Matrix m k₁ ℝ} {V' : ℕ → Matrix n k₂ ℝ} {S' : ℕ → Matrix k₁ k₂ ℝ}
  {T : ℕ → Matrix m m ℝ} {T' : ℕ → Matrix n n ℝ}

/-- **The stiff energies of a truncated run are summable.** For `F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0`,
any intermediate bases and truncations by orthogonal projectors (from the left and from the
right, as for a truncated singular value decomposition):

  `‖Y_N‖² / 2 + ∑ j < N, h (‖B Yⱼ₊₁‖² + ‖Yⱼ₊₁ Cᵀ‖²) ≤ ‖Y₀‖² / 2`. -/
theorem half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester {N : ℕ}
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) (ε j) (τ j) (ϑ j) (t j) h (U j) (S j) (V j) (K j) (L j)
      (U' j) (V' j) (S' j) (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ))
    (hh : 0 ≤ h) (hT : ∀ j < N, IsOrthProjMat (T j)) (hT' : ∀ j < N, IsOrthProjMat (T' j))
    (hY : ∀ j < N, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ = T j * (U' j * S' j * (V' j)ᵀ))
    (hY' : ∀ j < N, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ = U' j * S' j * (V' j)ᵀ * T' j) :
    ‖U N * S N * (V N)ᵀ‖ ^ 2 / 2 + ∑ j ∈ Finset.range N,
        h * (‖B * (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ)‖ ^ 2 +
          ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ * Cᵀ‖ ^ 2) ≤
      ‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      (fun j hj => hT j (Nat.lt_succ_of_lt hj)) (fun j hj => hT' j (Nat.lt_succ_of_lt hj))
      (fun j hj => hY j (Nat.lt_succ_of_lt hj)) (fun j hj => hY' j (Nat.lt_succ_of_lt hj))
    have hs := (hstep N (Nat.lt_succ_self N)).half_sq_norm_add_energy_le_of_sylvester hh
      (hT N (Nat.lt_succ_self N)) (hT' N (Nat.lt_succ_self N)) (hY N (Nat.lt_succ_self N))
      (hY' N (Nat.lt_succ_self N))
    rw [Finset.sum_range_succ]
    linarith

/-- **Run bound with residual bounds in the norm and the stiff energy.** For
`F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0`, a run `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` of the implicit BUG integrator with any
intermediate bases and truncations by orthogonal projectors (from the left and from the right),
and the backward Euler run `Xⱼ` on the full matrix: if in step `j` some matrix `U'ⱼ Gⱼ V'ⱼᵀ` of the
intermediate bases has a residual for the backward Euler equation with right-hand side `Yⱼ` of norm
at most `a ‖Yⱼ‖ + b (h ‖B Yⱼ‖² + h ‖Yⱼ Cᵀ‖²)^{1/2}` (`a, b ≥ 0`), then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑ j < N, ϑⱼ + N a ‖Y₀‖`
    `+ b ((h ‖B Y₀‖² + h ‖Y₀ Cᵀ‖²)^{1/2} + (N/2)^{1/2} ‖Y₀‖)`.

The energies of the later iterates are controlled by the run itself
(`half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester`); no bound of `B` or `C` enters. -/
theorem norm_implicitBUG_run_sub_le_of_sylvester_energy_residual {N : ℕ}
    {G : ℕ → Matrix k₁ k₂ ℝ} {X : ℕ → Matrix m n ℝ} {a b : ℝ}
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) (ε j) (τ j) (ϑ j) (t j) h (U j) (S j) (V j) (K j) (L j)
      (U' j) (V' j) (S' j) (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ))
    (hh : 0 ≤ h) (hT : ∀ j < N, IsOrthProjMat (T j)) (hT' : ∀ j < N, IsOrthProjMat (T' j))
    (hY : ∀ j < N, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ = T j * (U' j * S' j * (V' j)ᵀ))
    (hY' : ∀ j < N, U (j + 1) * S (j + 1) * (V (j + 1))ᵀ = U' j * S' j * (V' j)ᵀ * T' j)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hres : ∀ j < N, ‖U j * S j * (V j)ᵀ - (U' j * G j * (V' j)ᵀ +
      h • (Bᵀ * B * (U' j * G j * (V' j)ᵀ) + U' j * G j * (V' j)ᵀ * (Cᵀ * C)))‖ ≤
        a * ‖U j * S j * (V j)ᵀ‖ +
          b * √(h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2))) :
    ‖U N * S N * (V N)ᵀ - X N‖ ≤
      ‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + ∑ j ∈ Finset.range N, ϑ j + N * a * ‖U 0 * S 0 * (V 0)ᵀ‖ +
        b * (√(h * (‖B * (U 0 * S 0 * (V 0)ᵀ)‖ ^ 2 + ‖U 0 * S 0 * (V 0)ᵀ * Cᵀ‖ ^ 2)) +
          √((N : ℝ) / 2) * ‖U 0 * S 0 * (V 0)ᵀ‖) := by
  have run := norm_implicitBUG_run_sub_le_of_sylvester_residual (B := B) (C := C) (N := N)
    (δ := fun j => a * ‖U j * S j * (V j)ᵀ‖ +
      b * √(h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2)))
    hstep hh hX hres
  have pref : ∀ M ≤ N, ‖U M * S M * (V M)ᵀ‖ ^ 2 / 2 + ∑ j ∈ Finset.range M,
      h * (‖B * (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ)‖ ^ 2 +
        ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ * Cᵀ‖ ^ 2) ≤ ‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 / 2 :=
    fun M hM => half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester (N := M)
      (fun j hj => hstep j (by omega)) hh (fun j hj => hT j (by omega))
      (fun j hj => hT' j (by omega)) (fun j hj => hY j (by omega)) (fun j hj => hY' j (by omega))
  have hE0 : ∀ j, 0 ≤ h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2) :=
    fun j => mul_nonneg hh (by positivity)
  have hYle : ∀ j ≤ N, ‖U j * S j * (V j)ᵀ‖ ≤ ‖U 0 * S 0 * (V 0)ᵀ‖ := by
    intro j hj
    have h1 := pref j hj
    have h2 : 0 ≤ ∑ i ∈ Finset.range j, h * (‖B * (U (i + 1) * S (i + 1) * (V (i + 1))ᵀ)‖ ^ 2 +
        ‖U (i + 1) * S (i + 1) * (V (i + 1))ᵀ * Cᵀ‖ ^ 2) :=
      Finset.sum_nonneg fun i _ => hE0 (i + 1)
    nlinarith [norm_nonneg (U j * S j * (V j)ᵀ), norm_nonneg (U 0 * S 0 * (V 0)ᵀ)]
  have hsumY : ∑ j ∈ Finset.range N, ‖U j * S j * (V j)ᵀ‖ ≤ N * ‖U 0 * S 0 * (V 0)ᵀ‖ := by
    calc ∑ j ∈ Finset.range N, ‖U j * S j * (V j)ᵀ‖
        ≤ ∑ _j ∈ Finset.range N, ‖U 0 * S 0 * (V 0)ᵀ‖ :=
          Finset.sum_le_sum fun j hj => hYle j (Finset.mem_range.1 hj).le
      _ = N * ‖U 0 * S 0 * (V 0)ᵀ‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumE : ∑ j ∈ Finset.range N,
      √(h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2)) ≤
        √(h * (‖B * (U 0 * S 0 * (V 0)ᵀ)‖ ^ 2 + ‖U 0 * S 0 * (V 0)ᵀ * Cᵀ‖ ^ 2)) +
          √((N : ℝ) / 2) * ‖U 0 * S 0 * (V 0)ᵀ‖ := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div, Real.sqrt_zero,
        zero_mul, add_zero]
      exact Real.sqrt_nonneg _
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have cs := Real.sum_sqrt_mul_sqrt_le (Finset.range M)
      (f := fun j => h * (‖B * (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ)‖ ^ 2 +
        ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ * Cᵀ‖ ^ 2)) (g := fun _ => (1 : ℝ))
      (fun j => hE0 (j + 1)) (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at cs
    have hp := pref M (by omega)
    have hsum : ∑ j ∈ Finset.range M, h * (‖B * (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ)‖ ^ 2 +
        ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ * Cᵀ‖ ^ 2) ≤ ‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 / 2 := by
      nlinarith [sq_nonneg ‖U M * S M * (V M)ᵀ‖]
    have k1 := Real.sqrt_le_sqrt hsum
    have k2 : √(M : ℝ) ≤ √((M : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have k3 : √(‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 / 2) * √((M : ℝ) + 1) =
        √(((M + 1 : ℕ) : ℝ) / 2) * ‖U 0 * S 0 * (V 0)ᵀ‖ := by
      rw [← Real.sqrt_mul (by positivity), Nat.cast_add, Nat.cast_one,
        show ‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 / 2 * ((M : ℝ) + 1) =
          ‖U 0 * S 0 * (V 0)ᵀ‖ ^ 2 * (((M : ℝ) + 1) / 2) by ring,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (norm_nonneg _), mul_comm]
    have k4 := mul_le_mul k1 k2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  have e1 : ∑ j ∈ Finset.range N, ((fun j => a * ‖U j * S j * (V j)ᵀ‖ +
      b * √(h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2))) j + ϑ j) =
      a * ∑ j ∈ Finset.range N, ‖U j * S j * (V j)ᵀ‖ +
        b * ∑ j ∈ Finset.range N,
          √(h * (‖B * (U j * S j * (V j)ᵀ)‖ ^ 2 + ‖U j * S j * (V j)ᵀ * Cᵀ‖ ^ 2)) +
        ∑ j ∈ Finset.range N, ϑ j := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e1] at run
  have m1 := mul_le_mul_of_nonneg_left hsumY ha
  have m2 := mul_le_mul_of_nonneg_left hsumE hb
  nlinarith [m1, m2]

end Run

section Example

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq m]
  [DecidableEq n] {r : ℕ} {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}

/-- The hypotheses of `IsMatrixImplicitBUGStep.half_sq_norm_add_energy_le_of_sylvester` hold for
all sizes of `B`, `C`, every `h ≥ 0` and every start: the step with the new bases equal to the old
ones and no truncation (`T = 1`, `T' = 1`). -/
example (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ) :
    ∃ S₁ : Matrix (Fin r) (Fin r) ℝ, ‖U₀ * S₁ * V₀ᵀ‖ ^ 2 / 2 +
      h * (‖B * (U₀ * S₁ * V₀ᵀ)‖ ^ 2 + ‖U₀ * S₁ * V₀ᵀ * Cᵀ‖ ^ 2) ≤ ‖U₀ * S₀ * V₀ᵀ‖ ^ 2 / 2 := by
  obtain ⟨K, L, S₁, ε, τ, hs⟩ :=
    exists_isMatrixImplicitBUGStep_of_sylvester B C hh hU₀ hV₀ hU₀ hV₀ S₀ 0
  exact ⟨S₁, hs.half_sq_norm_add_energy_le_of_sylvester hh ⟨transpose_one, Matrix.mul_one 1⟩
    ⟨transpose_one, Matrix.mul_one 1⟩ (Matrix.one_mul _).symm (Matrix.mul_one _).symm⟩

/-- The hypotheses of `half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester` and of
`norm_implicitBUG_run_sub_le_of_sylvester_energy_residual` (with `a = b = 1`) hold for every
number of steps, all sizes of `B`, `C` and every `h ≥ 0`: the run with the new bases equal to the
old ones, no truncation (`T = 1`, `T' = 1`) and `G = 0` (the residual is then `Yⱼ` itself). -/
example (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (X₀ : Matrix m n ℝ) (N : ℕ) :
    ∃ (S : ℕ → Matrix (Fin r) (Fin r) ℝ) (X : ℕ → Matrix m n ℝ), S 0 = S₀ ∧ X 0 = X₀ ∧
      ‖U₀ * S N * V₀ᵀ‖ ^ 2 / 2 + ∑ j ∈ Finset.range N,
          h * (‖B * (U₀ * S (j + 1) * V₀ᵀ)‖ ^ 2 + ‖U₀ * S (j + 1) * V₀ᵀ * Cᵀ‖ ^ 2) ≤
        ‖U₀ * S 0 * V₀ᵀ‖ ^ 2 / 2 ∧
      ‖U₀ * S N * V₀ᵀ - X N‖ ≤ ‖U₀ * S 0 * V₀ᵀ - X 0‖ + ∑ _j ∈ Finset.range N, (0 : ℝ) +
        N * 1 * ‖U₀ * S 0 * V₀ᵀ‖ + 1 * (√(h * (‖B * (U₀ * S 0 * V₀ᵀ)‖ ^ 2 +
          ‖U₀ * S 0 * V₀ᵀ * Cᵀ‖ ^ 2)) + √((N : ℝ) / 2) * ‖U₀ * S 0 * V₀ᵀ‖) := by
  choose K L S₁ ε τ hstep using fun S : Matrix (Fin r) (Fin r) ℝ =>
    exists_isMatrixImplicitBUGStep_of_sylvester B C hh hU₀ hV₀ hU₀ hV₀ S 0
  choose Rf hRf using fun Y : Matrix m n ℝ => exists_add_smul_sylvester_eq B C hh Y
  have hX : ∀ j, Rf^[j + 1] X₀ + h • (Bᵀ * B * Rf^[j + 1] X₀ + Rf^[j + 1] X₀ * (Cᵀ * C)) =
      Rf^[j] X₀ := fun j => by
    rw [Function.iterate_succ_apply']
    exact hRf _
  have hst : ∀ j, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) (ε (S₁^[j] S₀)) (τ (S₁^[j] S₀)) 0 0 h U₀ (S₁^[j] S₀) V₀
      (K (S₁^[j] S₀)) (L (S₁^[j] S₀)) U₀ V₀ (S₁ (S₁^[j] S₀)) (U₀ * S₁^[j + 1] S₀ * V₀ᵀ) :=
    fun j => by
      rw [Function.iterate_succ_apply']
      exact hstep _
  have hI : IsOrthProjMat (1 : Matrix m m ℝ) := ⟨transpose_one, Matrix.mul_one 1⟩
  have hI' : IsOrthProjMat (1 : Matrix n n ℝ) := ⟨transpose_one, Matrix.mul_one 1⟩
  have hY : ∀ j < N, U₀ * S₁^[j + 1] S₀ * V₀ᵀ =
      (1 : Matrix m m ℝ) * (U₀ * S₁ (S₁^[j] S₀) * V₀ᵀ) :=
    fun j _ => by rw [Matrix.one_mul, Function.iterate_succ_apply']
  have hY' : ∀ j < N, U₀ * S₁^[j + 1] S₀ * V₀ᵀ =
      U₀ * S₁ (S₁^[j] S₀) * V₀ᵀ * (1 : Matrix n n ℝ) :=
    fun j _ => by rw [Matrix.mul_one, Function.iterate_succ_apply']
  refine ⟨fun j => S₁^[j] S₀, fun j => Rf^[j] X₀, rfl, rfl, ?_, ?_⟩
  · exact half_sq_norm_add_sum_energy_implicitBUG_run_le_of_sylvester (B := B) (C := C) (N := N)
      (ε := fun j => ε (S₁^[j] S₀)) (τ := fun j => τ (S₁^[j] S₀)) (ϑ := fun _ => 0)
      (t := fun _ => 0) (U := fun _ => U₀) (S := fun j => S₁^[j] S₀) (V := fun _ => V₀)
      (K := fun j => K (S₁^[j] S₀)) (L := fun j => L (S₁^[j] S₀)) (U' := fun _ => U₀)
      (V' := fun _ => V₀) (S' := fun j => S₁ (S₁^[j] S₀)) (T := fun _ => 1) (T' := fun _ => 1)
      (fun j _ => hst j) hh (fun _ _ => hI) (fun _ _ => hI') hY hY'
  · exact norm_implicitBUG_run_sub_le_of_sylvester_energy_residual (B := B) (C := C) (N := N)
      (ε := fun j => ε (S₁^[j] S₀)) (τ := fun j => τ (S₁^[j] S₀)) (ϑ := fun _ => 0)
      (t := fun _ => 0) (U := fun _ => U₀) (S := fun j => S₁^[j] S₀) (V := fun _ => V₀)
      (K := fun j => K (S₁^[j] S₀)) (L := fun j => L (S₁^[j] S₀)) (U' := fun _ => U₀)
      (V' := fun _ => V₀) (S' := fun j => S₁ (S₁^[j] S₀)) (T := fun _ => 1) (T' := fun _ => 1)
      (G := fun _ => 0) (X := fun j => Rf^[j] X₀) (a := 1) (b := 1)
      (fun j _ => hst j) hh (fun _ _ => hI) (fun _ _ => hI') hY hY' (fun j _ => hX j)
      zero_le_one zero_le_one (fun j _ => by
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, smul_zero, sub_zero, one_mul]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _))

end Example

end LeanDLRA
