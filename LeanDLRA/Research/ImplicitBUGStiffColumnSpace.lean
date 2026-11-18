import LeanDLRA.Research.ImplicitBUGStiffDamped
import LeanDLRA.Matrix.Curvature

/-!
# Backward Euler of a stiff linear problem: the error inside and outside the column space

Let `F(Z) = M Z - Z CᵀC + G` with `M` dissipative and bounded by `μ` and `C` arbitrary (the matrix
`-CᵀC` acting on the rows is the stiffness), let `𝒫 Z = Z - h M Z + h Z CᵀC` be the operator of a
backward Euler step, and let `A_j` be a reference with `𝒫 A_{j+1} = A_j + g_j + δ_j`. For a
sequence `Y_j` and orthogonal projectors `T_j` acting from the left with `T_j Y_j = Y_j` (the
projectors onto the column spaces, or onto larger spaces), the error splits orthogonally,

  `‖Y_j - A_j‖² = ‖Y_j - T_j A_j‖² + ‖A_j - T_j A_j‖²`,

into the distance to the best approximation of the reference with columns in the range of `T_j`
and the part of the reference outside that range. This file shows that the first part
satisfies, with the backward Euler steps `𝒫 W_j = Y_j + g_j` of the full problem from `Y_j`,

  `‖Y_N - T_N A_N‖ ≤ ‖Y₀ - T₀ A₀‖`
  `    + ∑_{j<N} ((h μ + γ_j) ‖A_j - T_j A_j‖ + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖)`,

where `γ_j ≥ ‖T_{j+1} (1 - T_j)‖₂` measures the rotation of the range in step `j`. For a run with
truncation, `Y_{j+1} = T_{j+1} Ŷ_{j+1}`, the last term is at most the local error
`‖Ŷ_{j+1} - W_j‖` before the truncation: the truncated parts `(1 - T_{j+1}) Ŷ_{j+1}` do not enter.
What enters instead is the part of the reference outside the range, weighted by `h μ` and by the
rotation of the range. Neither `C` nor a singular value enters.

## Main results

* `ImplicitBUGStiffColumnSpace.norm_proj_mul_le_of_backwardEuler`: a backward Euler step maps a
  matrix outside the range of a projector `T` to a matrix whose part inside the range is at most
  `h μ` times the norm of the right-hand side.
* `ImplicitBUGStiffColumnSpace.norm_proj_mul_sub_proj_mul_le_add_norm_proj_mul`,
  `norm_proj_mul_sub_proj_mul_le_of_backwardEuler`: one step, with the exact coupling
  `‖T₁ V‖`, `𝒫 V = A₀ - T₀ A₀`, and with its bound `(h μ + γ) ‖A₀ - T₀ A₀‖`.
* `ImplicitBUGStiffColumnSpace.norm_sub_proj_mul_le_add_sum_norm_proj_mul_of_backwardEuler`,
  `norm_sub_proj_mul_le_add_sum_of_backwardEuler`: the run bounds for any sequence, and
  `norm_sub_le_sqrt_add_of_backwardEuler` the form for `‖Y_N - A_N‖`.
* `ImplicitBUGStiffColumnSpace.norm_sub_proj_mul_le_pow_mul_of_backwardEuler_of_lipschitz`: the
  run bound with a Lipschitz non-stiff part evaluated explicitly.
* `ImplicitBUGStiffColumnSpace.norm_implicitBUG_truncated_run_sub_proj_mul_le_of_sylvester`,
  `norm_implicitBUG_truncated_run_sub_le_sqrt_of_sylvester`: runs of the BUG integrator with
  backward Euler substeps and truncation by projectors acting from the left.

## Implementation notes

The left projector `T` commutes with the right multiplication by `CᵀC`, so the commutator of `T`
with the backward Euler step is `h` times a commutator with `M` alone: if `𝒫 V = R` and `T R = 0`
then `𝒫 (T V) = h (T M - M T) V`, and `‖(T M - M T) V‖ ≤ μ ‖V‖` because the two parts
`T M (1 - T) V` and `(1 - T) M T V` are orthogonal.

## References

* [CerutiLubich2022], [CerutiKuschLubich2022] for the BUG integrator and its rank-adaptive
  variant; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix Finset

namespace LeanDLRA

open ImplicitBUGStiffLemmas ImplicitBUGStiffLocal ImplicitBUGStiffDamped Curvature

namespace ImplicitBUGStiffColumnSpace

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ}

/-! ### The orthogonal splitting of the error -/

/-- **The error splits orthogonally at the column space**: if `T` is an orthogonal projector with
`T Y = Y`, then `‖Y - A‖² = ‖Y - T A‖² + ‖A - T A‖²`. -/
theorem sq_norm_sub_eq_sq_norm_sub_proj_mul_add {T : Matrix m m ℝ} (hT : IsOrthProjMat T)
    {Y A : Matrix m n ℝ} (hY : T * Y = Y) :
    ‖Y - A‖ ^ 2 = ‖Y - T * A‖ ^ 2 + ‖A - T * A‖ ^ 2 := by
  have h1 := sq_norm_proj_mul_add hT.idem hT.symm (Y - A)
  have e : Y - A - (Y - T * A) = -(A - T * A) := by abel
  rw [Matrix.mul_sub, hY, e, norm_neg] at h1
  exact h1.symm

/-! ### The commutator of a left projector with a backward Euler step -/

/-- **A backward Euler step keeps a matrix outside the range of a left projector up to `h μ`.**
If `V - h M V + h V CᵀC = R` with `M` dissipative and bounded by `μ`, and `T R = 0` for an
orthogonal projector `T`, then `‖T V‖ ≤ h μ ‖R‖`, whatever `C` is. -/
theorem norm_proj_mul_le_of_backwardEuler {T : Matrix m m ℝ} (hT : T * T = T) (hTt : Tᵀ = T)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h) {V R : Matrix m n ℝ}
    (heq : V - h • (M * V) + h • (V * (Cᵀ * C)) = R) (hR : T * R = 0) :
    ‖T * V‖ ≤ h * μ * ‖R‖ := by
  have h0 : T * V - h • (T * (M * V)) + h • (T * (V * (Cᵀ * C))) = 0 := by
    rw [← hR, ← heq, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
  have e : T * V - h • (M * (T * V)) + h • (T * V * (Cᵀ * C)) =
      h • (T * (M * V) - M * (T * V)) := by
    rw [Matrix.mul_assoc T V, smul_sub]
    calc T * V - h • (M * (T * V)) + h • (T * (V * (Cᵀ * C)))
        = T * V - h • (T * (M * V)) + h • (T * (V * (Cᵀ * C))) +
          (h • (T * (M * V)) - h • (M * (T * V))) := by abel
      _ = h • (T * (M * V)) - h • (M * (T * V)) := by rw [h0, zero_add]
  have n1 := norm_le_of_backwardEuler hdiss hh e
  rw [norm_smul, Real.norm_of_nonneg hh] at n1
  have hAB : T * (M * V) - M * (T * V) =
      T * (M * (V - T * V)) - (M * (T * V) - T * (M * (T * V))) := by
    rw [Matrix.mul_sub, Matrix.mul_sub]
    abel
  have hTB : T * (M * (T * V) - T * (M * (T * V))) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc T T, hT, sub_self]
  have hz : ⟪T * (M * (V - T * V)), M * (T * V) - T * (M * (T * V))⟫ = 0 := by
    rw [inner_proj_mul hTt, hTB, inner_zero_right]
  have nA : ‖T * (M * (V - T * V))‖ ≤ μ * ‖V - T * V‖ :=
    (norm_proj_mul_le hT hTt _).trans (norm_mul_le_mul_norm hμ0 hμ _)
  have nB : ‖M * (T * V) - T * (M * (T * V))‖ ≤ μ * ‖T * V‖ :=
    (norm_sub_proj_mul_le hT hTt _).trans (norm_mul_le_mul_norm hμ0 hμ _)
  have hpy := sq_norm_proj_mul_add hT hTt V
  have hsq : ‖T * (M * V) - M * (T * V)‖ ^ 2 ≤ (μ * ‖V‖) ^ 2 := by
    rw [hAB, norm_sub_sq_real, hz]
    have a2 := pow_le_pow_left₀ (norm_nonneg _) nA 2
    have b2 := pow_le_pow_left₀ (norm_nonneg _) nB 2
    have e2 : (μ * ‖V‖) ^ 2 = (μ * ‖V - T * V‖) ^ 2 + (μ * ‖T * V‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, ← hpy]; ring
    linarith
  have ncomm : ‖T * (M * V) - M * (T * V)‖ ≤ μ * ‖V‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hμ0 (norm_nonneg _)) two_ne_zero).1 hsq
  have nV := norm_le_of_backwardEuler hdiss hh heq
  calc ‖T * V‖ ≤ h * ‖T * (M * V) - M * (T * V)‖ := n1
    _ ≤ h * (μ * ‖R‖) :=
      mul_le_mul_of_nonneg_left (ncomm.trans (mul_le_mul_of_nonneg_left nV hμ0)) hh
    _ = h * μ * ‖R‖ := by ring

/-! ### One step -/

section Step

variable [DecidableEq m]

/-- **A backward Euler step of a matrix outside the range of `T₀`, seen inside the range of
`T₁`.** If `V - h M V + h V CᵀC = R` with `M` dissipative and bounded by `μ`, `T₀ R = 0` and
`‖T₁ (1 - T₀)‖₂ ≤ γ` for orthogonal projectors `T₀`, `T₁`, then `‖T₁ V‖ ≤ (h μ + γ) ‖R‖`. -/
theorem norm_proj_mul_le_of_backwardEuler_of_specNorm_le {T₀ T₁ : Matrix m m ℝ}
    (hT₀ : IsOrthProjMat T₀) (hT₁ : IsOrthProjMat T₁)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    {V R : Matrix m n ℝ} {γ : ℝ} (hV : V - h • (M * V) + h • (V * (Cᵀ * C)) = R)
    (hR : T₀ * R = 0) (hγ : specNorm (T₁ * (1 - T₀)) ≤ γ) :
    ‖T₁ * V‖ ≤ (h * μ + γ) * ‖R‖ := by
  have n2 := norm_proj_mul_le_of_backwardEuler hT₀.idem hT₀.symm hdiss hμ0 hμ hh hV hR
  have nV := norm_le_of_backwardEuler hdiss hh hV
  have hγ0 : 0 ≤ γ := (specNorm_nonneg _).trans hγ
  have eV : T₁ * V = T₁ * (T₀ * V) + T₁ * (1 - T₀) * V := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_add]
    congr 1
    abel
  have n4 : ‖T₁ * (T₀ * V)‖ ≤ ‖T₀ * V‖ := norm_proj_mul_le hT₁.idem hT₁.symm _
  have n5 : ‖T₁ * (1 - T₀) * V‖ ≤ γ * ‖R‖ :=
    (frob_mul_le _ _).trans (mul_le_mul hγ nV (norm_nonneg _) hγ0)
  have n7 := norm_add_le (T₁ * (T₀ * V)) (T₁ * (1 - T₀) * V)
  rw [eV]
  linarith

omit [DecidableEq m] in
/-- **One backward Euler step, seen inside the new range: the exact coupling.** Let `M` be
dissipative, let `W - h M W + h W CᵀC = Y₀ + g` (the backward Euler step from `Y₀`),
`A₁ - h M A₁ + h A₁ CᵀC = A₀ + g + δ` (the reference) and `V - h M V + h V CᵀC = A₀ - T₀ A₀` (the
backward Euler step of the part of the reference outside the range of `T₀`). Then for every
orthogonal projector `T₁`

  `‖T₁ W - T₁ A₁‖ ≤ ‖Y₀ - T₀ A₀‖ + ‖T₁ V‖ + ‖δ‖`.

Nothing is assumed on `T₀`. -/
theorem norm_proj_mul_sub_proj_mul_le_add_norm_proj_mul {T₀ T₁ : Matrix m m ℝ}
    (hT₁ : IsOrthProjMat T₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    {Y₀ A₀ A₁ W V g δ : Matrix m n ℝ}
    (hW : W - h • (M * W) + h • (W * (Cᵀ * C)) = Y₀ + g)
    (hA : A₁ - h • (M * A₁) + h • (A₁ * (Cᵀ * C)) = A₀ + g + δ)
    (hV : V - h • (M * V) + h • (V * (Cᵀ * C)) = A₀ - T₀ * A₀) :
    ‖T₁ * W - T₁ * A₁‖ ≤ ‖Y₀ - T₀ * A₀‖ + ‖T₁ * V‖ + ‖δ‖ := by
  have hD := backwardEuler_sub hW hA
  have hS : W - A₁ + V - h • (M * (W - A₁ + V)) + h • ((W - A₁ + V) * (Cᵀ * C)) =
      Y₀ - T₀ * A₀ - δ := by
    have e : Y₀ - T₀ * A₀ - δ = Y₀ + g - (A₀ + g + δ) + (A₀ - T₀ * A₀) := by abel
    rw [e, ← hD, ← hV]
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  have n1 : ‖W - A₁ + V‖ ≤ ‖Y₀ - T₀ * A₀‖ + ‖δ‖ :=
    (norm_le_of_backwardEuler hdiss hh hS).trans (norm_sub_le _ _)
  have e : T₁ * W - T₁ * A₁ = T₁ * (W - A₁ + V) - T₁ * V := by
    rw [← Matrix.mul_sub, ← Matrix.mul_sub]
    congr 1
    abel
  have n3 : ‖T₁ * (W - A₁ + V)‖ ≤ ‖W - A₁ + V‖ := norm_proj_mul_le hT₁.idem hT₁.symm _
  have n6 := norm_sub_le (T₁ * (W - A₁ + V)) (T₁ * V)
  rw [e]
  linarith

/-- **One backward Euler step, seen inside the new range.** Let `M` be dissipative and bounded
by `μ`, let `W - h M W + h W CᵀC = Y₀ + g` (the backward Euler step from `Y₀`) and
`A₁ - h M A₁ + h A₁ CᵀC = A₀ + g + δ` (the reference), and let `T₀`, `T₁` be orthogonal
projectors with `‖T₁ (1 - T₀)‖₂ ≤ γ`. Then

  `‖T₁ W - T₁ A₁‖ ≤ ‖Y₀ - T₀ A₀‖ + (h μ + γ) ‖A₀ - T₀ A₀‖ + ‖δ‖`.

The part `A₀ - T₀ A₀` of the reference outside the old range enters the new range only through
the commutator with `M` and through the rotation of the range. -/
theorem norm_proj_mul_sub_proj_mul_le_of_backwardEuler {T₀ T₁ : Matrix m m ℝ}
    (hT₀ : IsOrthProjMat T₀) (hT₁ : IsOrthProjMat T₁)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    {Y₀ A₀ A₁ W g δ : Matrix m n ℝ} {γ : ℝ}
    (hW : W - h • (M * W) + h • (W * (Cᵀ * C)) = Y₀ + g)
    (hA : A₁ - h • (M * A₁) + h • (A₁ * (Cᵀ * C)) = A₀ + g + δ)
    (hγ : specNorm (T₁ * (1 - T₀)) ≤ γ) :
    ‖T₁ * W - T₁ * A₁‖ ≤ ‖Y₀ - T₀ * A₀‖ + (h * μ + γ) * ‖A₀ - T₀ * A₀‖ + ‖δ‖ := by
  obtain ⟨V, hV⟩ := exists_backwardEuler (C := C) hdiss hh (A₀ - T₀ * A₀)
  have hTN : T₀ * (A₀ - T₀ * A₀) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT₀.idem, sub_self]
  have h1 := norm_proj_mul_sub_proj_mul_le_add_norm_proj_mul hT₁ hdiss hh hW hA hV
  have h2 := norm_proj_mul_le_of_backwardEuler_of_specNorm_le hT₀ hT₁ hdiss hμ0 hμ hh hV hTN hγ
  linarith

/-- **The projection of the reference satisfies the projected backward Euler scheme up to the
weighted outside part.** Let `W - h M W + h W CᵀC = T₀ A₀ + g` be the backward Euler step from the
projection `T₀ A₀` of the reference and `A₁ - h M A₁ + h A₁ CᵀC = A₀ + g + δ`. Then

  `‖T₁ W - T₁ A₁‖ ≤ (h μ + γ) ‖A₀ - T₀ A₀‖ + ‖δ‖`,   `‖T₁ (1 - T₀)‖₂ ≤ γ`.

For the projectors onto the dominant left singular subspaces of `A₀`, `A₁` this is the defect of
the best approximations `T₀ A₀`, `T₁ A₁` in the scheme `Y₁ = T₁ W`: the best approximation error
`‖A₀ - T₀ A₀‖` times `h μ` plus the rotation of the dominant subspace, whatever `C` is. -/
theorem norm_proj_mul_backwardEuler_proj_mul_sub_le {T₀ T₁ : Matrix m m ℝ}
    (hT₀ : IsOrthProjMat T₀) (hT₁ : IsOrthProjMat T₁)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    {A₀ A₁ W g δ : Matrix m n ℝ} {γ : ℝ}
    (hW : W - h • (M * W) + h • (W * (Cᵀ * C)) = T₀ * A₀ + g)
    (hA : A₁ - h • (M * A₁) + h • (A₁ * (Cᵀ * C)) = A₀ + g + δ)
    (hγ : specNorm (T₁ * (1 - T₀)) ≤ γ) :
    ‖T₁ * W - T₁ * A₁‖ ≤ (h * μ + γ) * ‖A₀ - T₀ * A₀‖ + ‖δ‖ := by
  have h1 := norm_proj_mul_sub_proj_mul_le_of_backwardEuler hT₀ hT₁ hdiss hμ0 hμ hh hW hA hγ
  rwa [sub_self, norm_zero, zero_add] at h1

end Step

/-! ### Runs of any sequence -/

section Run

variable {N : ℕ} {Y W V A g δ : ℕ → Matrix m n ℝ} {T : ℕ → Matrix m m ℝ} {γ : ℕ → ℝ}

/-- **Run bound for the error inside the range, for any sequence: the exact coupling.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative, `𝒫 Z = Z - h M Z + h Z CᵀC`, let `A` be a reference with
`𝒫 A_{j+1} = A_j + g_j + δ_j`, let `Y_j` be any sequence, `𝒫 W_j = Y_j + g_j` the backward Euler
steps of the full problem from `Y_j`, let `T_j` be orthogonal projectors and
`𝒫 V_j = A_j - T_j A_j` the backward Euler steps of the parts of the reference outside the ranges.
Then

  `‖Y_N - T_N A_N‖ ≤ ‖Y₀ - T₀ A₀‖`
  `    + ∑_{j<N} (‖T_{j+1} V_j‖ + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖)`.

No bound of `M` enters. -/
theorem norm_sub_proj_mul_le_add_sum_norm_proj_mul_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hV : ∀ j < N, V j - h • (M * V j) + h • (V j * (Cᵀ * C)) = A j - T j * A j) :
    ‖Y N - T N * A N‖ ≤ ‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      (‖T (j + 1) * V j‖ + ‖δ j‖ + ‖Y (j + 1) - T (j + 1) * W j‖) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hT j (Nat.le_succ_of_le hj))
      (fun j hj => hW j (Nat.lt_succ_of_lt hj)) (fun j hj => hA j (Nat.lt_succ_of_lt hj))
      fun j hj => hV j (Nat.lt_succ_of_lt hj)
    have hn := Nat.lt_succ_self n
    have h1 := norm_proj_mul_sub_proj_mul_le_add_norm_proj_mul (hT (n + 1) le_rfl) hdiss hh
      (hW n hn) (hA n hn) (hV n hn)
    have e : Y (n + 1) - T (n + 1) * A (n + 1) =
        Y (n + 1) - T (n + 1) * W n + (T (n + 1) * W n - T (n + 1) * A (n + 1)) := by abel
    have h2 := norm_add_le (Y (n + 1) - T (n + 1) * W n)
      (T (n + 1) * W n - T (n + 1) * A (n + 1))
    rw [← e] at h2
    rw [Finset.sum_range_succ]
    linarith

variable [DecidableEq m]

/-- **Run bound for the error inside the range, for any sequence.** Let `F(Z) = M Z - Z CᵀC` with
`M` dissipative and bounded by `μ`, `𝒫 Z = Z - h M Z + h Z CᵀC`, let `A` be a reference with
`𝒫 A_{j+1} = A_j + g_j + δ_j`, let `Y_j` be any sequence, `𝒫 W_j = Y_j + g_j` the backward Euler
steps of the full problem from `Y_j`, and let `T_j` be orthogonal projectors with
`‖T_{j+1} (1 - T_j)‖₂ ≤ γ_j`. Then

  `‖Y_N - T_N A_N‖ ≤ ‖Y₀ - T₀ A₀‖`
  `    + ∑_{j<N} ((h μ + γ_j) ‖A_j - T_j A_j‖ + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖)`.

If `Y_{j+1} = T_{j+1} Ŷ_{j+1}` the last term is at most `‖Ŷ_{j+1} - W_j‖`: what is cut off by
`T_{j+1}` does not enter, whatever its size. -/
theorem norm_sub_proj_mul_le_add_sum_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) :
    ‖Y N - T N * A N‖ ≤ ‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖A j - T j * A j‖ + ‖δ j‖ + ‖Y (j + 1) - T (j + 1) * W j‖) := by
  choose V hV using fun j => exists_backwardEuler (C := C) hdiss hh (A j - T j * A j)
  refine (norm_sub_proj_mul_le_add_sum_norm_proj_mul_of_backwardEuler hdiss hh hT hW hA
    fun j _ => hV j).trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
  have hjN : j < N := Finset.mem_range.1 hj
  have hT0 := hT j hjN.le
  have hTN : T j * (A j - T j * A j) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT0.idem, sub_self]
  have h2 := norm_proj_mul_le_of_backwardEuler_of_specNorm_le hT0 (hT (j + 1) hjN) hdiss hμ0 hμ
    hh (hV j) hTN (hγ j hjN)
  linarith

/-- **Run bound for the error inside the range with a Lipschitz forcing.** In the setting of
`norm_sub_proj_mul_le_add_sum_of_backwardEuler` let the forcing of the sequence and the forcing
of the reference differ, `𝒫 W_j = Y_j + g_j` and `𝒫 A_{j+1} = A_j + gA_j + δ_j` with
`‖g_j - gA_j‖ ≤ h L ‖Y_j - A_j‖` (a non-stiff part `G` with Lipschitz constant `L`, evaluated
explicitly: `g_j = h G(Y_j)`, `gA_j = h G(A_j)`). Then

  `‖Y_N - T_N A_N‖ ≤ (1 + h L)^N (‖Y₀ - T₀ A₀‖`
  `    + ∑_{j<N} ((h (μ + L) + γ_j) ‖A_j - T_j A_j‖ + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖))`.

The stiffness does not enter, and the part of the reference outside the ranges enters with the
weights `h (μ + L) + γ_j`. -/
theorem norm_sub_proj_mul_le_pow_mul_of_backwardEuler_of_lipschitz {gA : ℕ → Matrix m n ℝ}
    {L : ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + gA j + δ j)
    (hg : ∀ j < N, ‖g j - gA j‖ ≤ h * L * ‖Y j - A j‖)
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) :
    ‖Y N - T N * A N‖ ≤ (1 + h * L) ^ N * (‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      ((h * (μ + L) + γ j) * ‖A j - T j * A j‖ + ‖δ j‖ + ‖Y (j + 1) - T (j + 1) * W j‖)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hT j (Nat.le_succ_of_le hj))
      (fun j hj => hW j (Nat.lt_succ_of_lt hj)) (fun j hj => hA j (Nat.lt_succ_of_lt hj))
      (fun j hj => hg j (Nat.lt_succ_of_lt hj)) fun j hj => hγ j (Nat.lt_succ_of_lt hj)
    have hn := Nat.lt_succ_self n
    have hA' : A (n + 1) - h • (M * A (n + 1)) + h • (A (n + 1) * (Cᵀ * C)) =
        A n + g n + (gA n - g n + δ n) := by
      rw [hA n hn]; abel
    have h1 := norm_proj_mul_sub_proj_mul_le_of_backwardEuler (hT n hn.le) (hT (n + 1) le_rfl)
      hdiss hμ0 hμ hh (hW n hn) hA' (hγ n hn)
    have h3 : ‖gA n - g n + δ n‖ ≤ h * L * ‖Y n - A n‖ + ‖δ n‖ :=
      (norm_add_le _ _).trans (add_le_add (by rw [norm_sub_rev]; exact hg n hn) le_rfl)
    have h4 : ‖Y n - A n‖ ≤ ‖Y n - T n * A n‖ + ‖A n - T n * A n‖ := by
      have e : Y n - A n = Y n - T n * A n - (A n - T n * A n) := by abel
      rw [e]; exact norm_sub_le _ _
    have hhL : 0 ≤ h * L := mul_nonneg hh hL
    have h5 := mul_le_mul_of_nonneg_left h4 hhL
    have e : Y (n + 1) - T (n + 1) * A (n + 1) =
        Y (n + 1) - T (n + 1) * W n + (T (n + 1) * W n - T (n + 1) * A (n + 1)) := by abel
    have h2 := norm_add_le (Y (n + 1) - T (n + 1) * W n)
      (T (n + 1) * W n - T (n + 1) * A (n + 1))
    rw [← e] at h2
    have hγ0 : 0 ≤ γ n := (specNorm_nonneg _).trans (hγ n hn)
    have hs0 : 0 ≤ (h * (μ + L) + γ n) * ‖A n - T n * A n‖ + ‖δ n‖ +
        ‖Y (n + 1) - T (n + 1) * W n‖ := by
      have := mul_nonneg hh hμ0
      positivity
    have hG1 : 1 ≤ 1 + h * L := by linarith
    have hGn : 1 ≤ (1 + h * L) ^ (n + 1) := one_le_pow₀ hG1
    have key : ‖Y (n + 1) - T (n + 1) * A (n + 1)‖ ≤ (1 + h * L) * ‖Y n - T n * A n‖ +
        ((h * (μ + L) + γ n) * ‖A n - T n * A n‖ + ‖δ n‖ + ‖Y (n + 1) - T (n + 1) * W n‖) := by
      linarith
    rw [Finset.sum_range_succ]
    calc ‖Y (n + 1) - T (n + 1) * A (n + 1)‖
        ≤ (1 + h * L) * ‖Y n - T n * A n‖ +
          ((h * (μ + L) + γ n) * ‖A n - T n * A n‖ + ‖δ n‖ +
            ‖Y (n + 1) - T (n + 1) * W n‖) := key
      _ ≤ (1 + h * L) * ((1 + h * L) ^ n * (‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range n,
            ((h * (μ + L) + γ j) * ‖A j - T j * A j‖ + ‖δ j‖ +
              ‖Y (j + 1) - T (j + 1) * W j‖))) +
          (1 + h * L) ^ (n + 1) * ((h * (μ + L) + γ n) * ‖A n - T n * A n‖ + ‖δ n‖ +
            ‖Y (n + 1) - T (n + 1) * W n‖) :=
        add_le_add (mul_le_mul_of_nonneg_left ih' (by linarith))
          (le_mul_of_one_le_left hs0 hGn)
      _ = _ := by ring

/-- **Run bound for the error of any sequence with its columns in the ranges `T_j`.** In the
setting of `norm_sub_proj_mul_le_add_sum_of_backwardEuler`, if `T_N Y_N = Y_N`, then

  `‖Y_N - A_N‖ ≤ √(B² + ‖A_N - T_N A_N‖²)`,
  `B = ‖Y₀ - T₀ A₀‖ + ∑_{j<N} ((h μ + γ_j) ‖A_j - T_j A_j‖ + ‖δ_j‖ + ‖Y_{j+1} - T_{j+1} W_j‖)`.

The part of the reference outside the last range enters once, with the factor one. -/
theorem norm_sub_le_sqrt_add_of_backwardEuler
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 ≤ h)
    (hT : ∀ j ≤ N, IsOrthProjMat (T j)) (hYN : T N * Y N = Y N)
    (hW : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j)
    (hA : ∀ j < N,
      A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) = A j + g j + δ j)
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) :
    ‖Y N - A N‖ ≤ √((‖Y 0 - T 0 * A 0‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖A j - T j * A j‖ + ‖δ j‖ + ‖Y (j + 1) - T (j + 1) * W j‖)) ^ 2 +
        ‖A N - T N * A N‖ ^ 2) := by
  have h1 := norm_sub_proj_mul_le_add_sum_of_backwardEuler hdiss hμ0 hμ hh hT hW hA hγ
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_norm_sub_eq_sq_norm_sub_proj_mul_add (hT N le_rfl) hYN]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) le_rfl

end Run

end ImplicitBUGStiffColumnSpace

open ImplicitBUGStiffColumnSpace

/-! ### Runs of the integrator with truncation -/

section Integrator

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
  {N : ℕ} {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ} {ϑ γ : ℕ → ℝ}
  {T : ℕ → Matrix m m ℝ} {Y Yh X δ : ℕ → Matrix m n ℝ}

/-- **Run bound with truncation in which the truncation errors do not add up.** Let
`F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ`, and let `X_j` be a reference with
`X_{j+1} - h M X_{j+1} + h X_{j+1} CᵀC = X_j + δ_j`. Let step `j` of the integrator with backward
Euler substeps start from `Y_j` (of any rank), with exact capture by bases of any size, result
`Ŷ_{j+1} = U₁ S₁ V₁ᵀ` and truncated value `Y_{j+1} = T_{j+1} Ŷ_{j+1}` with orthogonal projectors
`T_j`, `‖T_{j+1} (1 - T_j)‖₂ ≤ γ_j`. Then for every sequence of comparison matrices `Z_j`

  `‖Y_N - T_N X_N‖ ≤ ‖Y₀ - T₀ X₀‖ + ∑_{j<N} ((h μ + γ_j) ‖X_j - T_j X_j‖ + ‖δ_j‖`
  `    + (27/4 + 2 h μ) h μ λ_j)`,
  `λ_j = min(‖Y_j‖, √h ‖(Y_j - Z_j) Cᵀ‖ / 2 + h ‖Z_j CᵀC‖)`.

The size of the truncated parts does not enter; the part `X_j - T_j X_j` of the reference outside
the range of `T_j` enters with the weight `h μ + γ_j`. -/
theorem norm_implicitBUG_truncated_run_sub_proj_mul_le_of_sylvester
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (hT : ∀ j ≤ N, IsOrthProjMat (T j))
    (htrunc : ∀ j < N, Y (j + 1) = T (j + 1) * Yh (j + 1))
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (Z : ℕ → Matrix m n ℝ) :
    ‖Y N - T N * X N‖ ≤ ‖Y 0 - T 0 * X 0‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖X j - T j * X j‖ + ‖δ j‖ + (27 / 4 + 2 * (h * μ)) * (h * μ) *
        min ‖Y j‖ (√h * ‖(Y j - Z j) * Cᵀ‖ / 2 + h * ‖Z j * (Cᵀ * C)‖)) := by
  choose W hW using fun j => exists_backwardEuler (C := C) hdiss hh.le (Y j)
  have hW' : ∀ j < N, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + (0 : Matrix m n ℝ) :=
    fun j _ => (hW j).trans (add_zero _).symm
  have hX' : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) =
      X j + (0 : Matrix m n ℝ) + δ j := fun j hj => by
    rw [add_zero]; exact hX j hj
  have key := norm_sub_proj_mul_le_add_sum_of_backwardEuler (g := fun _ => 0) hdiss hμ0
    hμ hh.le hT hW' hX' hγ
  refine key.trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
  have hjN : j < N := Finset.mem_range.1 hj
  obtain ⟨r, k₁, k₂, U₀, S₀, V₀, K₁, L₁, U₁, V₁, S₁, ε, t, hY, hYh, hs⟩ := hstep j hjN
  have h1 := hs.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester hdiss hμ0 hμ hh
    (Yt := W j) (by rw [← hY]; exact hW j) (Z j)
  rw [← hY, ← hYh] at h1
  have h2 : ‖Yh (j + 1) - W j‖ ≤
      √(‖Yh (j + 1) - W j‖ ^ 2 + 2 * (h * ‖(Yh (j + 1) - W j) * Cᵀ‖ ^ 2)) :=
    Real.le_sqrt_of_sq_le (by
      have : 0 ≤ 2 * (h * ‖(Yh (j + 1) - W j) * Cᵀ‖ ^ 2) := by positivity
      linarith)
  have hT1 := hT (j + 1) hjN
  have h3 : ‖Y (j + 1) - T (j + 1) * W j‖ ≤ ‖Yh (j + 1) - W j‖ := by
    rw [htrunc j hjN, ← Matrix.mul_sub]
    exact norm_proj_mul_le hT1.idem hT1.symm _
  linarith

/-- **Run bound with truncation for the whole error.** In the setting of
`norm_implicitBUG_truncated_run_sub_proj_mul_le_of_sylvester`, if `T₀ Y₀ = Y₀`, then

  `‖Y_N - X_N‖ ≤ √(B² + ‖X_N - T_N X_N‖²)`,
  `B = ‖Y₀ - T₀ X₀‖ + ∑_{j<N} ((h μ + γ_j) ‖X_j - T_j X_j‖ + ‖δ_j‖ + (27/4 + 2 h μ) h μ λ_j)`.

Compared with the bound `‖Y₀ - X₀‖ + ∑ (‖δ_j‖ + ϑ_j + (27/4 + 2 h μ) h μ λ_j)` with the truncation
errors `ϑ_j = ‖Y_{j+1} - Ŷ_{j+1}‖`, the sum of the truncation errors is replaced by the part of
the reference outside the ranges, once with the factor one and in the sum with the weights
`h μ + γ_j`. -/
theorem norm_implicitBUG_truncated_run_sub_le_sqrt_of_sylvester
    (hstep : ∀ j < N, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
      (V₀ : Matrix n (Fin r) ℝ) (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ)
      (U₁ : Matrix m (Fin k₁) ℝ) (V₁ : Matrix n (Fin k₂) ℝ) (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ)
      (ε t : ℝ), Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
        IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0
          (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (Y (j + 1)))
    (hT : ∀ j ≤ N, IsOrthProjMat (T j)) (hY₀ : T 0 * Y 0 = Y 0)
    (htrunc : ∀ j < N, Y (j + 1) = T (j + 1) * Yh (j + 1))
    (hγ : ∀ j < N, specNorm (T (j + 1) * (1 - T j)) ≤ γ j)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hX : ∀ j < N, X (j + 1) - h • (M * X (j + 1)) + h • (X (j + 1) * (Cᵀ * C)) = X j + δ j)
    (Z : ℕ → Matrix m n ℝ) :
    ‖Y N - X N‖ ≤ √((‖Y 0 - T 0 * X 0‖ + ∑ j ∈ range N,
      ((h * μ + γ j) * ‖X j - T j * X j‖ + ‖δ j‖ + (27 / 4 + 2 * (h * μ)) * (h * μ) *
        min ‖Y j‖ (√h * ‖(Y j - Z j) * Cᵀ‖ / 2 + h * ‖Z j * (Cᵀ * C)‖))) ^ 2 +
        ‖X N - T N * X N‖ ^ 2) := by
  have h1 := norm_implicitBUG_truncated_run_sub_proj_mul_le_of_sylvester hstep hT htrunc hγ hdiss
    hμ0 hμ hh hX Z
  have hYN : T N * Y N = Y N := by
    cases N with
    | zero => exact hY₀
    | succ n =>
      have hTn := hT (n + 1) le_rfl
      rw [htrunc n (Nat.lt_succ_self n), ← Matrix.mul_assoc, hTn.idem]
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_norm_sub_eq_sq_norm_sub_proj_mul_add (hT N le_rfl) hYN]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) le_rfl

end Integrator

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffColumnSpaceExample

open ImplicitBUGStiffLemmasExample ImplicitBUGStiffLocalExample

local notation "Dᶜ" => (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Hᶜ" => (!![1 / 2, 1 / 2; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Mᶜ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cᶜ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

local notation "Bᶜ" => (!![9 / 25, 12 / 25; 12 / 25, 16 / 25] : Matrix (Fin 2) (Fin 2) ℝ)

/-- `diag(1, 0)` is an orthogonal projector. -/
theorem isOrthProjMat_diag : IsOrthProjMat Dᶜ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The projector onto the span of `(1, 1)` is an orthogonal projector. -/
theorem isOrthProjMat_half : IsOrthProjMat Hᶜ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num

/-- The projector onto the span of `(3/5, 4/5)` is an orthogonal projector. -/
theorem isOrthProjMat_start : IsOrthProjMat Bᶜ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num

/-- The part of the identity outside the range of `diag(1, 0)` is not zero. -/
theorem one_sub_diag_mul_one_ne_zero : (1 : Matrix (Fin 2) (Fin 2) ℝ) - Dᶜ * 1 ≠ 0 := by
  intro hc
  have := congrFun (congrFun hc 1) 1
  simp at this

/-- The projector onto the span of `(1, 1)` does not vanish outside the range of `diag(1, 0)`. -/
theorem half_mul_one_sub_diag_ne_zero : Hᶜ * (1 - Dᶜ) ≠ 0 := by
  intro hc
  have := congrFun (congrFun hc 0) 1
  simp [Matrix.mul_apply] at this

/-- The part of the identity outside the range of the projector onto `(3/5, 4/5)` is not zero. -/
theorem one_sub_start_mul_one_ne_zero : (1 : Matrix (Fin 2) (Fin 2) ℝ) - Bᶜ * 1 ≠ 0 := by
  intro hc
  have := congrFun (congrFun hc 0) 1
  simp at this

/-- The hypotheses of the run bounds for any sequence hold for every `M`, `C` and `h` with a
reference that has a part outside the first range and with a range that rotates in the step:
`T₀ = diag(1, 0)`, `T₁` the projector onto the span of `(1, 1)`, `A_j = 1`, `Y_j = T_j`. -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) (h : ℝ) :
    ∃ (Y W A g δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (γ : ℕ → ℝ),
      (∀ j ≤ 1, IsOrthProjMat (T j)) ∧ T 1 * Y 1 = Y 1 ∧
      (∀ j < 1, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j) ∧
      (∀ j < 1, A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) =
        A j + g j + δ j) ∧
      (∀ j < 1, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) ∧
      A 0 - T 0 * A 0 ≠ 0 ∧ T 1 * (1 - T 0) ≠ 0 := by
  refine ⟨fun j => if j = 0 then Dᶜ else Hᶜ, fun j => if j = 0 then Dᶜ else Hᶜ, fun _ => 1,
    fun _ => Dᶜ - h • (M * Dᶜ) + h • (Dᶜ * (Cᵀ * C)) - Dᶜ,
    fun _ => 1 - h • (M * 1) + h • (1 * (Cᵀ * C)) -
      (1 + (Dᶜ - h • (M * Dᶜ) + h • (Dᶜ * (Cᵀ * C)) - Dᶜ)),
    fun j => if j = 0 then Dᶜ else Hᶜ, fun _ => specNorm (Hᶜ * (1 - Dᶜ)), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro j _
    by_cases hj : j = 0
    · simp only [hj, ite_true]; exact isOrthProjMat_diag
    · simp only [hj, ite_false]; exact isOrthProjMat_half
  · simp only [one_ne_zero, ite_false]
    exact isOrthProjMat_half.idem
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [ite_true]
    abel
  · intro j hj
    exact (add_sub_cancel _ _).symm
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact le_rfl
  · simp only [ite_true]
    exact one_sub_diag_mul_one_ne_zero
  · simp only [one_ne_zero, ite_false, ite_true]
    exact half_mul_one_sub_diag_ne_zero

/-- The hypotheses of the run bound with a Lipschitz forcing hold for every `M`, `C`, `h > 0` and
`L > 0` with forcings of the sequence and of the reference that differ by exactly
`h L ‖Y₀ - A₀‖ ≠ 0`: `T₀ = Y₀ = diag(1, 0)`, `A_j = 1`. -/
example (M : Matrix (Fin 2) (Fin 2) ℝ) (C : Matrix (Fin 1) (Fin 2) ℝ) {h L : ℝ} (hh : 0 < h)
    (hL : 0 < L) :
    ∃ (Y W A g gA δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (γ : ℕ → ℝ),
      (∀ j ≤ 1, IsOrthProjMat (T j)) ∧
      (∀ j < 1, W j - h • (M * W j) + h • (W j * (Cᵀ * C)) = Y j + g j) ∧
      (∀ j < 1, A (j + 1) - h • (M * A (j + 1)) + h • (A (j + 1) * (Cᵀ * C)) =
        A j + gA j + δ j) ∧
      (∀ j < 1, ‖g j - gA j‖ ≤ h * L * ‖Y j - A j‖) ∧
      (∀ j < 1, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) ∧ g 0 - gA 0 ≠ 0 := by
  have hne : Dᶜ - (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
    intro hc
    have := congrFun (congrFun hc 1) 1
    simp at this
  refine ⟨fun _ => Dᶜ, fun _ => Dᶜ, fun _ => 1,
    fun _ => Dᶜ - h • (M * Dᶜ) + h • (Dᶜ * (Cᵀ * C)) - Dᶜ,
    fun _ => Dᶜ - h • (M * Dᶜ) + h • (Dᶜ * (Cᵀ * C)) - Dᶜ - (h * L) • (Dᶜ - 1),
    fun _ => 1 - h • (M * 1) + h • (1 * (Cᵀ * C)) -
      (1 + (Dᶜ - h • (M * Dᶜ) + h • (Dᶜ * (Cᵀ * C)) - Dᶜ - (h * L) • (Dᶜ - 1))),
    fun j => if j = 0 then Dᶜ else Hᶜ, fun _ => specNorm (Hᶜ * (1 - Dᶜ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    by_cases hj : j = 0
    · simp only [hj, ite_true]; exact isOrthProjMat_diag
    · simp only [hj, ite_false]; exact isOrthProjMat_half
  · intro j hj
    exact (add_sub_cancel _ _).symm
  · intro j hj
    exact (add_sub_cancel _ _).symm
  · intro j hj
    rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg (mul_pos hh hL).le]
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact le_rfl
  · rw [sub_sub_cancel]
    exact smul_ne_zero (mul_pos hh hL).ne' hne

/-- The hypotheses of the run bounds with truncation hold with `N = 1`, for every stiffness
`lam > 0` and every `h > 0`: `M = diag(0, -1)`, `C = (0, √lam)`, a step from
`(3/5, 4/5)ᵀ (3/5, 4/5)`, `T₀` the projector onto the span of `(3/5, 4/5)`, `T₁ = 1`, and the
reference `X₀ = 1`, which has a part outside the range of `T₀`. -/
example {h lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) :
    ∃ (ϑ γ : ℕ → ℝ) (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (Y Yh X δ : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      (∀ j < 1, ∃ (r k₁ k₂ : ℕ) (U₀ : Matrix (Fin 2) (Fin r) ℝ)
        (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix (Fin 2) (Fin r) ℝ)
        (K₁ : Matrix (Fin 2) (Fin r) ℝ) (L₁ : Matrix (Fin 2) (Fin r) ℝ)
        (U₁ : Matrix (Fin 2) (Fin k₁) ℝ) (V₁ : Matrix (Fin 2) (Fin k₂) ℝ)
        (S₁ : Matrix (Fin k₁) (Fin k₂) ℝ) (ε t : ℝ),
        Y j = U₀ * S₀ * V₀ᵀ ∧ Yh (j + 1) = U₁ * S₁ * V₁ᵀ ∧
          IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
            Mᶜ * Z - Z * ((Cᶜ lam)ᵀ * (Cᶜ lam))) ε 0 (ϑ j) t h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁
            (Y (j + 1))) ∧
      (∀ j ≤ 1, IsOrthProjMat (T j)) ∧ T 0 * Y 0 = Y 0 ∧
      (∀ j < 1, Y (j + 1) = T (j + 1) * Yh (j + 1)) ∧
      (∀ j < 1, specNorm (T (j + 1) * (1 - T j)) ≤ γ j) ∧
      (∀ j < 1, X (j + 1) - h • (Mᶜ * X (j + 1)) +
        h • (X (j + 1) * ((Cᶜ lam)ᵀ * (Cᶜ lam))) = X j + δ j) ∧
      X 0 - T 0 * X 0 ≠ 0 ∧ T 1 * (1 - T 0) ≠ 0 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    ImplicitBUGStiffLocalExample.exists_isMatrixImplicitBUGStep hh hlam.le
  obtain ⟨X₁, hX₁⟩ := exists_backwardEuler (C := Cᶜ lam) dotProduct_mulVec_nonpos hh.le
    (1 : Matrix (Fin 2) (Fin 2) ℝ)
  refine ⟨fun _ => 0, fun _ => specNorm ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 - Bᶜ)),
    fun j => if j = 0 then Bᶜ else 1,
    fun j => if j = 0 then (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ
      else U₁ * S₁ * V₁ᵀ,
    fun _ => U₁ * S₁ * V₁ᵀ, fun j => if j = 0 then 1 else X₁, fun _ => 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨1, 1, 1, !![3 / 5; 4 / 5], 1, !![3 / 5; 4 / 5], K₁, L₁, U₁, V₁, S₁, ε, 0, rfl, rfl,
      ⟨hs.orthU₀, hs.orthV₀, hs.kstep, hs.lstep, hs.orthU₁, hs.orthV₁, hs.kcap, hs.lcap,
        hs.knormal, hs.lnormal, hs.sstep, by simp⟩⟩
  · intro j _
    by_cases hj : j = 0
    · simp only [hj, ite_true]; exact isOrthProjMat_start
    · simp only [hj, ite_false]
      exact ⟨Matrix.transpose_one, Matrix.one_mul 1⟩
  · simp only [ite_true]
    rw [start_eq]
    exact isOrthProjMat_start.idem
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp
  · intro j hj
    obtain rfl : j = 0 := by omega
    simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact le_rfl
  · intro j hj
    obtain rfl : j = 0 := by omega
    simpa using hX₁
  · simp only [ite_true]
    exact one_sub_start_mul_one_ne_zero
  · simp only [one_ne_zero, ite_false, ite_true, Matrix.one_mul]
    intro hc
    have := congrFun (congrFun hc 0) 1
    simp at this

end ImplicitBUGStiffColumnSpaceExample

end LeanDLRA
