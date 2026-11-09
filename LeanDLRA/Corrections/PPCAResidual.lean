import LeanDLRA.Literature.Applications.P2407_03373a

/-!
# Correction: arXiv 2407.03373, Proposition 8 (residual of the PPCA projection)

Bonnabel, Lambert, Bach, arXiv 2407.03373v1, Appendix B, Proposition 8, states that in the PPCA
case `‖H - P_{U,R,s}(H)‖² = Tr((I - UUᵀ)[H - δs I]ᵀ[H - δs I])`, with `P_{U,R,s}` the PPCA
projection of Proposition 2 (`ppcaProj`) and `δs = (Tr H - Tr(Uᵀ H U))/(d - p)` (`ppcaShift`).
The norm is the Frobenius norm.

* `prop8_printed_false`: the printed formula is false. For `d = 2`, `p = 1`, `U = e₁` and the
  symmetric `H = [0 1; 1 0]` one has `δs = 0` and `P(H) = H`, so the left side is `0`, while the
  printed right side is `1`.
* `prop8_corrected`: with `Q = I - UUᵀ` and `M = H - δs I`, the residual is `H - P(H) = Q M Q`,
  so `‖H - P(H)‖² = Tr(Q Mᵀ Q M)`. The middle factor `Q` is the one the printed formula drops; the
  same expression appears in the paper's own proof of Proposition 2, (19).
* `prop8_printed_eq`: the printed right side equals `‖H - P(H)‖² + ‖UUᵀ H (I - UUᵀ)‖²`, so it is
  an upper bound, with equality iff `UUᵀ H (I - UUᵀ) = 0` (`prop8_printed_iff`), that is, iff the
  range of `U` is invariant under `H`.

No hypothesis on `H` is needed (the paper takes `H` symmetric; the counterexample is symmetric).
Core definitions used: the Frobenius norm and inner product (`LeanDLRA.Frobenius`); the PPCA
objects `ppcaProj`, `ppcaShift`, `ppcaRes` and the projector lemmas are those of
`LeanDLRA.Literature.P2407_03373`.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.Corrections.P2407_03373

open LeanDLRA.Literature.P2407_03373

variable {d p : Type*} [Fintype d] [Fintype p] [DecidableEq d] [DecidableEq p]

section Generic

/-- For an idempotent `Q`, `Q H Q - c Q = Q (H - c I) Q`. -/
lemma sandwich_sub_smul {Q : Matrix d d ℝ} (hQQ : Q * Q = Q) (H : Matrix d d ℝ) (c : ℝ) :
    Q * H * Q - c • Q = Q * (H - c • (1 : Matrix d d ℝ)) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQQ]

/-- If `P Q = 0`, then `P (H - c I) Q = P H Q`. -/
lemma mul_sub_smul_mul {P Q : Matrix d d ℝ} (hPQ : P * Q = 0) (H : Matrix d d ℝ) (c : ℝ) :
    P * (H - c • (1 : Matrix d d ℝ)) * Q = P * H * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ,
    smul_zero, sub_zero]

omit [DecidableEq d] in
/-- `‖Q M Q‖² = Tr(Q Mᵀ Q M)` for a symmetric idempotent `Q` (Frobenius norm). -/
lemma norm_sq_sandwich {Q : Matrix d d ℝ} (hQQ : Q * Q = Q) (hQs : Qᵀ = Q) (M : Matrix d d ℝ) :
    ‖Q * M * Q‖ ^ 2 = Matrix.trace (Q * Mᵀ * Q * M) := by
  rw [← real_inner_self_eq_norm_sq, LeanDLRA.Frobenius.inner_eq_trace, Matrix.transpose_mul,
    Matrix.transpose_mul, hQs]
  calc Matrix.trace (Q * (Mᵀ * Q) * (Q * M * Q))
      = Matrix.trace (Q * Mᵀ * (Q * Q) * M * Q) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q * (Q * Mᵀ * Q * M)) := by
        rw [hQQ]; exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q * Mᵀ * Q * M) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ]

omit [DecidableEq d] in
/-- `Tr(Q Mᵀ M) = ‖M Q‖²` for a symmetric idempotent `Q` (Frobenius norm). -/
lemma trace_mul_transpose_mul {Q : Matrix d d ℝ} (hQQ : Q * Q = Q) (hQs : Qᵀ = Q)
    (M : Matrix d d ℝ) : Matrix.trace (Q * Mᵀ * M) = ‖M * Q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, LeanDLRA.Frobenius.inner_eq_trace, Matrix.transpose_mul, hQs]
  calc Matrix.trace (Q * Mᵀ * M) = Matrix.trace (Q * (Q * Mᵀ * M)) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ]
    _ = Matrix.trace (Q * Mᵀ * M * Q) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q * Mᵀ * (M * Q)) := by rw [Matrix.mul_assoc (Q * Mᵀ) M Q]

/-- If `Q + P = I` and `Qᵀ P = 0`, then `‖M Q‖² = ‖Q M Q‖² + ‖P M Q‖²`. -/
lemma norm_sq_split {P Q : Matrix d d ℝ} (hPQ : Q + P = 1) (hQP : Qᵀ * P = 0)
    (M : Matrix d d ℝ) : ‖M * Q‖ ^ 2 = ‖Q * M * Q‖ ^ 2 + ‖P * M * Q‖ ^ 2 := by
  have hsplit : M * Q = Q * M * Q + P * M * Q := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, hPQ, Matrix.one_mul]
  have horth : ⟪Q * M * Q, P * M * Q⟫ = 0 := by
    rw [LeanDLRA.Frobenius.inner_eq_trace]
    have e : (Q * M * Q)ᵀ * (P * M * Q) = Qᵀ * Mᵀ * (Qᵀ * P) * M * Q := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hQP, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  rw [hsplit, norm_add_sq_real, horth]
  ring

end Generic

variable {U : Matrix d p ℝ}

/-- The residual of the PPCA projection is `Q (H - δs I) Q` with `Q = I - UUᵀ`. -/
lemma ppcaRes_eq_sandwich (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    ppcaRes U H = (1 - U * Uᵀ) * (H - ppcaShift U H • (1 : Matrix d d ℝ)) * (1 - U * Uᵀ) :=
  sandwich_sub_smul (Q_mul_Q hU) H (ppcaShift U H)

/-- **Proposition 8 of arXiv 2407.03373, corrected.** In the PPCA case, with `Q = I - UUᵀ` and
`M = H - δs I`, `‖H - P_{U,R,s}(H)‖² = Tr(Q Mᵀ Q M)`. The printed formula `Tr(Q Mᵀ M)` lacks the
middle `Q` (`prop8_printed_false`). -/
theorem prop8_corrected (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    ‖H - ppcaProj U H‖ ^ 2
      = Matrix.trace ((1 - U * Uᵀ) * (H - ppcaShift U H • (1 : Matrix d d ℝ))ᵀ * (1 - U * Uᵀ)
          * (H - ppcaShift U H • (1 : Matrix d d ℝ))) := by
  rw [H_sub_ppcaProj, ppcaRes_eq_sandwich hU, norm_sq_sandwich (Q_mul_Q hU) Q_symm]

/-- **Proposition 8 of arXiv 2407.03373: the printed right side overestimates.** It equals
`‖H - P_{U,R,s}(H)‖² + ‖UUᵀ H (I - UUᵀ)‖²`. -/
theorem prop8_printed_eq (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    Matrix.trace ((1 - U * Uᵀ) * (H - ppcaShift U H • (1 : Matrix d d ℝ))ᵀ
        * (H - ppcaShift U H • (1 : Matrix d d ℝ)))
      = ‖H - ppcaProj U H‖ ^ 2 + ‖U * Uᵀ * H * (1 - U * Uᵀ)‖ ^ 2 := by
  have hQP : (1 - U * Uᵀ)ᵀ * (U * Uᵀ) = 0 := by
    rw [Q_symm, ← Matrix.mul_assoc, Q_mul_U hU, Matrix.zero_mul]
  have hPQ : U * Uᵀ * (1 - U * Uᵀ) = 0 := by
    rw [Matrix.mul_assoc, transpose_mul_Q hU, Matrix.mul_zero]
  rw [trace_mul_transpose_mul (Q_mul_Q hU) Q_symm,
    norm_sq_split (P := U * Uᵀ) (sub_add_cancel 1 (U * Uᵀ)) hQP,
    H_sub_ppcaProj, ppcaRes_eq_sandwich hU, mul_sub_smul_mul hPQ]

/-- Proposition 8 of arXiv 2407.03373 holds for given `U`, `H` iff `UUᵀ H (I - UUᵀ) = 0`, that is,
iff the range of `U` is invariant under `H`. -/
theorem prop8_printed_iff (hU : Uᵀ * U = 1) (H : Matrix d d ℝ) :
    ‖H - ppcaProj U H‖ ^ 2
        = Matrix.trace ((1 - U * Uᵀ) * (H - ppcaShift U H • (1 : Matrix d d ℝ))ᵀ
          * (H - ppcaShift U H • (1 : Matrix d d ℝ)))
      ↔ U * Uᵀ * H * (1 - U * Uᵀ) = 0 := by
  rw [prop8_printed_eq hU]
  constructor
  · intro h
    have h0 : ‖U * Uᵀ * H * (1 - U * Uᵀ)‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  · intro h
    rw [h, norm_zero]
    ring

/-- **Proposition 8 of arXiv 2407.03373 is false as printed.** For `d = 2`, `p = 1`, `U = e₁` and
the symmetric `H = [0 1; 1 0]`, the printed formula differs from `‖H - P_{U,R,s}(H)‖²`, because
`UUᵀ H (I - UUᵀ) ≠ 0` (`prop8_printed_iff`). Here `δs = 0` and `P_{U,R,s}(H) = H`, so the left side
is `0`, while the printed right side is `1` (`prop8_printed_eq`). -/
theorem prop8_printed_false :
    ∃ (U : Matrix (Fin 2) (Fin 1) ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ), Uᵀ * U = 1 ∧ Hᵀ = H ∧
      ‖H - ppcaProj U H‖ ^ 2 ≠
        Matrix.trace ((1 - U * Uᵀ) * (H - ppcaShift U H • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ
          * (H - ppcaShift U H • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hU : (Matrix.of fun (i : Fin 2) (_ : Fin 1) => if i = 0 then (1 : ℝ) else 0)ᵀ
      * (Matrix.of fun (i : Fin 2) (_ : Fin 1) => if i = 0 then (1 : ℝ) else 0) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply]
  have hH : (Matrix.of fun (i j : Fin 2) => if i = j then (0 : ℝ) else 1)ᵀ
      = (Matrix.of fun (i j : Fin 2) => if i = j then (0 : ℝ) else 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨_, _, hU, hH, fun h => ?_⟩
  have h0 := (prop8_printed_iff hU _).mp h
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h0
  have h01 := congrFun (congrFun h0 0) 1
  simp [Matrix.mul_apply] at h01

end LeanDLRA.Corrections.P2407_03373
