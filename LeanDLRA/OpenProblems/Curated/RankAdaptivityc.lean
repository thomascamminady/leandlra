import LeanDLRA.DLRA.QuasiOptimality

/-!
# Quasi-optimality of dynamical low-rank approximation for matrices: the recorded form

The quasi-optimality bound for matrices is `dlra_norm_sub_truncation_le_integral` in
`LeanDLRA/DLRA/QuasiOptimality.lean`. This module keeps the statement
`dlra_quasiOptimal_matrix` in its recorded form, which has two more hypotheses and one more
instance argument, and proves it from that theorem.

## Main results

* `dlra_quasiOptimal_matrix`: the bound of `dlra_norm_sub_truncation_le_integral` under the
  additional hypotheses that the derivative of `X` is continuous and that
  `‖Y s - X s‖ ≤ ρ / 16` for all `s ∈ [0, t]`.

## References

* O. Koch, Ch. Lubich, Dynamical low-rank approximation, SIAM J. Matrix Anal. Appl. 29 (2007).
-/

open Set Finset Matrix

namespace LeanDLRA

section QuasiOptimal

open scoped LeanDLRA.Frobenius
open EckartYoung

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

set_option linter.unusedDecidableInType false in
/-- **Quasi-optimality of matrix DLRA** (source: Koch–Lubich, SIAM J. Matrix Anal. Appl. 29
(2007), Theorem 5.1). Let `X(t) = T_r(A(t))` be a `C¹` best rank-`r` approximation with
`σ_r(X(t)) ≥ ρ` and `‖X(t) - A(t)‖_F ≤ ρ/16`, `‖Ȧ‖_F ≤ μ`, and let `Y = U S Vᵀ` solve the DLRA
equation `Ẏ = P(Y) Ȧ` with `Y(0) = X(0)`. While `‖Y - X‖_F ≤ ρ/16`,
`‖Y(t) - X(t)‖_F ≤ 2 β e^{β t} ∫₀ᵗ ‖X(s) - A(s)‖_F ds`, `β = 8 μ / ρ`.
This is the recorded form of the statement, with the redundant hypotheses that the derivative of
`X` is continuous and that `‖Y s - X s‖ ≤ ρ / 16` on `[0, t]`, and with the instance
`DecidableEq m`, which its type does not use; `dlra_norm_sub_truncation_le_integral` is the same
statement without them. -/
theorem dlra_quasiOptimal_matrix {r : ℕ} (hr : 0 < r) {A A' X X' Y : ℝ → Matrix m n ℝ}
    {T μ ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ t ∈ Icc 0 T, HasDerivAt A (A' t) t)
    (hμ : ∀ t ∈ Icc 0 T, ‖A' t‖ ≤ μ) (hXbest : ∀ t ∈ Icc 0 T, X t = truncation (A t) r)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (X' t) t) (hX'c : ContinuousOn X' (Icc 0 T))
    (hσ : ∀ t ∈ Icc 0 T, ρ ≤ (toEuclideanLin (A t)).singularValues (r - 1))
    (hd : ∀ t ∈ Icc 0 T, ‖X t - A t‖ ≤ ρ / 16)
    {U : ℝ → Matrix m (Fin r) ℝ} {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {V : ℝ → Matrix n (Fin r) ℝ}
    (hUV : ∀ t ∈ Icc 0 T, (U t)ᵀ * U t = 1 ∧ (V t)ᵀ * V t = 1 ∧ Y t = U t * S t * (V t)ᵀ)
    (hY : ODESolution (fun t _ => tangentProj (U t) (V t) (A' t)) Y 0 T) (hY₀ : Y 0 = X 0) :
    ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, ‖Y s - X s‖ ≤ ρ / 16) →
      ‖Y t - X t‖ ≤
        2 * (8 * μ / ρ) * Real.exp (8 * μ / ρ * t) * ∫ s in (0 : ℝ)..t, ‖X s - A s‖ := by
  have _ := hX'c
  let _ : DecidableEq m := inferInstance
  exact fun t ht _ =>
    dlra_norm_sub_truncation_le_integral hr hρ hA hμ hXbest hX hσ hd hUV hY hY₀ t ht

end QuasiOptimal

end LeanDLRA
