import LeanDLRA.Integrators.Matrix.BUG

/-!
# Results of arXiv 1705.10175: low-rank split-step integrator for differential Lyapunov equations

Matrix-level results of Mena, Ostermann, Pfurtscheller and Piazzola (arXiv 1705.10175) for
`Ẋ = A X + X Aᵀ + Q`, with `A` the stiff linear part and `Q` the non-stiff constant part. All
matrices are real; the rank-`r` factors satisfy `r ≤ d`.

* `eq7_factorization` (eq. (7)): the exact stiff flow of a rank-`r` matrix,
  `e^{τA} U S Vᵀ e^{τAᵀ}`, equals `Ũ (R S Pᵀ) Ṽᵀ`, where `Ũ`, `Ṽ` have orthonormal columns and
  `e^{τA} U = Ũ R`, `e^{τA} V = Ṽ P`. The QR factors come from `LeanDLRA.MatrixBUG.exists_qr`.
* `eq7_rank`: `rank (e^{τA} M e^{τAᵀ}) = rank M` for every square `M`, since `e^{τA}` is
  invertible. The rank of the stiff flow is therefore preserved.
* `IsAlg1Step` (Algorithm 1, steps 3–5): one step of the first-order low-rank split-step
  integrator. Step 3 is the QR step for `e^{τA} U`, step 4 sets `S^A = R S Rᵀ`, and step 5 applies
  the three substeps. Each substep is linear with constant coefficients on the step interval, so
  it is written with its exact solution: `K(t₁) = U S^A + τ Q U`, `S̃ = Ŝ - τ U₁ᵀ Q U`,
  `L(t₁) = S̃ Uᵀ + τ U₁ᵀ Q`. The flows are not solved numerically. `isAlg1Step_exists` shows
  that a step always exists.
* `lemma_1` (Lemma 1): if `S` and `Q` are symmetric positive semidefinite and `τ ≥ 0`, then the
  new factor `S₁` of one step is symmetric positive semidefinite.
* `algorithm_1_psd` (Algorithm 1): for any sequence of steps starting from a positive
  semidefinite `S₀`, every iterate `U_n S_n U_nᵀ` is symmetric positive semidefinite.

Core definitions used: `LeanDLRA.MatrixBUG.exists_qr`. Local definitions added: `IsAlg1Step`,
which writes the algorithm's steps out for this DLE. The general `IsKSLStep` is not used, since
the substeps here have explicit constant-coefficient flows.

Not formalized: Section 2 (eqs. (2)–(6)) only defines the variation-of-constants formula and the
Lie and Strang splittings and quotes their orders, so there is no claim to prove there. Section 3
states without proof that the exact solution of the DLE is symmetric positive semidefinite. That
needs the variation-of-constants integral and is left out. The paper's convergence and numerical
results are not formalized.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P1705_10175

variable {d r : ℕ}

/-- The matrix exponential `e^{τA}` has a unit determinant. -/
lemma isUnit_det_exp (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) :
    IsUnit (NormedSpace.exp (τ • A)).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)

/-- `e^{τAᵀ} = (e^{τA})ᵀ`. -/
lemma exp_smul_transpose (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) :
    NormedSpace.exp (τ • Aᵀ) = (NormedSpace.exp (τ • A))ᵀ := by
  rw [← Matrix.transpose_smul, Matrix.exp_transpose]

/-- **Eq. (7), factorization (arXiv 1705.10175, eq. (7)).** For any `U`, `V ∈ ℝ^{d×r}` and
`S ∈ ℝ^{r×r}` (the paper takes `U`, `V` orthonormal; this is not needed), the stiff flow
`e^{τA} U S Vᵀ e^{τAᵀ}` equals `Ũ (R S Pᵀ) Ṽᵀ`, where `Ũ`, `Ṽ` have orthonormal columns and
`e^{τA} U = Ũ R`, `e^{τA} V = Ṽ P`. -/
theorem eq7_factorization (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hr : r ≤ d)
    (U V : Matrix (Fin d) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    ∃ (Ut Vt : Matrix (Fin d) (Fin r) ℝ) (R P : Matrix (Fin r) (Fin r) ℝ),
      Utᵀ * Ut = 1 ∧ Vtᵀ * Vt = 1 ∧
      NormedSpace.exp (τ • A) * U = Ut * R ∧ NormedSpace.exp (τ • A) * V = Vt * P ∧
      NormedSpace.exp (τ • A) * (U * S * Vᵀ) * NormedSpace.exp (τ • Aᵀ)
        = Ut * (R * S * Pᵀ) * Vtᵀ := by
  have hr' : r ≤ Fintype.card (Fin d) := by simpa using hr
  obtain ⟨Ut, hUt, hcapU⟩ := LeanDLRA.MatrixBUG.exists_qr hr' (NormedSpace.exp (τ • A) * U)
  obtain ⟨Vt, hVt, hcapV⟩ := LeanDLRA.MatrixBUG.exists_qr hr' (NormedSpace.exp (τ • A) * V)
  have hEU : NormedSpace.exp (τ • A) * U = Ut * (Utᵀ * (NormedSpace.exp (τ • A) * U)) := by
    rw [← Matrix.mul_assoc]; exact hcapU.symm
  have hEV : NormedSpace.exp (τ • A) * V = Vt * (Vtᵀ * (NormedSpace.exp (τ • A) * V)) := by
    rw [← Matrix.mul_assoc]; exact hcapV.symm
  refine ⟨Ut, Vt, Utᵀ * (NormedSpace.exp (τ • A) * U), Vtᵀ * (NormedSpace.exp (τ • A) * V),
    hUt, hVt, hEU, hEV, ?_⟩
  rw [exp_smul_transpose]
  have hYt : (NormedSpace.exp (τ • A) * V)ᵀ * (Vt * Vtᵀ) = (NormedSpace.exp (τ • A) * V)ᵀ := by
    have := congrArg Matrix.transpose hcapV
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  calc NormedSpace.exp (τ • A) * (U * S * Vᵀ) * (NormedSpace.exp (τ • A))ᵀ
      = (NormedSpace.exp (τ • A) * U) * S * (NormedSpace.exp (τ • A) * V)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Ut * Utᵀ * (NormedSpace.exp (τ • A) * U)) * S
          * ((NormedSpace.exp (τ • A) * V)ᵀ * (Vt * Vtᵀ)) := by
        rw [hcapU, hYt]
    _ = Ut * (Utᵀ * (NormedSpace.exp (τ • A) * U) * S
          * (Vtᵀ * (NormedSpace.exp (τ • A) * V))ᵀ) * Vtᵀ := by
        rw [Matrix.transpose_mul Vtᵀ, Matrix.transpose_transpose]
        simp only [Matrix.mul_assoc]

/-- **Eq. (7), rank (arXiv 1705.10175, eq. (7) and the remark that the rank is kept).** The
stiff flow `M ↦ e^{τA} M e^{τAᵀ}` preserves the rank of every square matrix `M`. -/
theorem eq7_rank (A : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (NormedSpace.exp (τ • A) * M * NormedSpace.exp (τ • Aᵀ)).rank = M.rank := by
  have hd : IsUnit (NormedSpace.exp (τ • A)).det := isUnit_det_exp A τ
  have hdT : IsUnit (NormedSpace.exp (τ • A))ᵀ.det := by rw [Matrix.det_transpose]; exact hd
  rw [exp_smul_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdT,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hd]

/-- One step of Algorithm 1 (arXiv 1705.10175), steps 3–5, for `Ṁ = A M + M Aᵀ + Q` with step
`τ`. `U`, `S` is the current factorization `U S Uᵀ` and `U'`, `S'` the next one. The existential
variables are the intermediate quantities of the algorithm: `UA` and `R` from the QR step
`e^{τA} U = UA R`, `SA = R S Rᵀ`, `Sh` from the QR step `U' Sh = UA SA + τ Q UA` of step 5a, `Sb`
the solution of step 5b and `Lt` that of step 5c, with `S' = Lt U'`. -/
def IsAlg1Step (A Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (U U' : Matrix (Fin d) (Fin r) ℝ)
    (S S' : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∃ (UA : Matrix (Fin d) (Fin r) ℝ) (R SA Sh Sb : Matrix (Fin r) (Fin r) ℝ)
    (Lt : Matrix (Fin r) (Fin d) ℝ),
    NormedSpace.exp (τ • A) * U = UA * R ∧ UAᵀ * UA = 1 ∧ SA = R * S * Rᵀ ∧
    U' * Sh = UA * SA + τ • (Q * UA) ∧ U'ᵀ * U' = 1 ∧
    Sb = Sh - τ • (U'ᵀ * Q * UA) ∧ Lt = Sb * UAᵀ + τ • (U'ᵀ * Q) ∧ S' = Lt * U'

/-- **Lemma 1 (arXiv 1705.10175, Lemma 1).** If `S₀` and `Q` are symmetric positive semidefinite
and `τ ≥ 0`, then the factor `S₁` of one step of Algorithm 1 is symmetric positive semidefinite.
Here `S` stands for `S₀` and `S'` for `S₁`; the paper states the lemma without these hypotheses,
which hold in its setting (Section 3). -/
theorem lemma_1 {A Q : Matrix (Fin d) (Fin d) ℝ} {τ : ℝ}
    {U U' : Matrix (Fin d) (Fin r) ℝ} {S S' : Matrix (Fin r) (Fin r) ℝ}
    (hS : S.PosSemidef) (hQ : Q.PosSemidef) (hτ : 0 ≤ τ) (h : IsAlg1Step A Q τ U U' S S') :
    S'.PosSemidef := by
  obtain ⟨UA, R, SA, Sh, Sb, Lt, _, _, hSA, hSh, hU', hSb, hLt, hS'⟩ := h
  have hSAp : SA.PosSemidef := by
    have := hS.mul_mul_conjTranspose_same R
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [hSA]; exact this
  have hSh' : Sh = U'ᵀ * (UA * SA + τ • (Q * UA)) := by
    rw [← hSh, ← Matrix.mul_assoc, hU', Matrix.one_mul]
  have hSb' : Sb = U'ᵀ * UA * SA := by
    rw [hSb, hSh', Matrix.mul_add, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc]
    abel
  have hform : S' = U'ᵀ * UA * SA * (UAᵀ * U') + τ • (U'ᵀ * Q * U') := by
    rw [hS', hLt, hSb', Matrix.add_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have h1 : (U'ᵀ * UA * SA * (UAᵀ * U')).PosSemidef := by
    have := hSAp.mul_mul_conjTranspose_same (U'ᵀ * UA)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose] at this
  have h2 : (U'ᵀ * Q * U').PosSemidef := by
    have := hQ.conjTranspose_mul_mul_same U'
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [hform]
  exact h1.add (h2.smul hτ)

/-- **Algorithm 1 (arXiv 1705.10175).** Starting from a symmetric positive semidefinite `S₀`,
along any sequence of steps of Algorithm 1 with `Q` symmetric positive semidefinite and `τ ≥ 0`,
every factor `S_n` is symmetric positive semidefinite and every iterate `N_n = U_n S_n U_nᵀ` is
symmetric positive semidefinite. -/
theorem algorithm_1_psd {A Q : Matrix (Fin d) (Fin d) ℝ} {τ : ℝ}
    (hQ : Q.PosSemidef) (hτ : 0 ≤ τ) (U : ℕ → Matrix (Fin d) (Fin r) ℝ)
    (S : ℕ → Matrix (Fin r) (Fin r) ℝ)
    (hstep : ∀ n, IsAlg1Step A Q τ (U n) (U (n + 1)) (S n) (S (n + 1)))
    (hS0 : (S 0).PosSemidef) :
    ∀ n, (S n).PosSemidef ∧ (U n * S n * (U n)ᵀ).PosSemidef := by
  have hS : ∀ n, (S n).PosSemidef := by
    intro n
    induction n with
    | zero => exact hS0
    | succ n ih => exact lemma_1 ih hQ hτ (hstep n)
  intro n
  refine ⟨hS n, ?_⟩
  have := (hS n).mul_mul_conjTranspose_same (U n)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Existence of a step (non-vacuity of `IsAlg1Step`).** For every `U`, `S`, `A`, `Q`, `τ` with
`r ≤ d`, one step of Algorithm 1 exists, with the QR factors from `LeanDLRA.MatrixBUG.exists_qr`. -/
theorem isAlg1Step_exists (A Q : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (hr : r ≤ d)
    (U : Matrix (Fin d) (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) :
    ∃ U' : Matrix (Fin d) (Fin r) ℝ, ∃ S' : Matrix (Fin r) (Fin r) ℝ,
      IsAlg1Step A Q τ U U' S S' := by
  have hr' : r ≤ Fintype.card (Fin d) := by simpa using hr
  obtain ⟨UA, hUA, hcap⟩ := LeanDLRA.MatrixBUG.exists_qr hr' (NormedSpace.exp (τ • A) * U)
  set R := UAᵀ * (NormedSpace.exp (τ • A) * U) with hRdef
  have hER : NormedSpace.exp (τ • A) * U = UA * R := by
    rw [hRdef, ← Matrix.mul_assoc]; exact hcap.symm
  set SA := R * S * Rᵀ with hSAdef
  set K := UA * SA + τ • (Q * UA) with hKdef
  obtain ⟨U', hU', hcap'⟩ := LeanDLRA.MatrixBUG.exists_qr hr' K
  set Sh := U'ᵀ * K with hShdef
  have hSh : U' * Sh = K := by rw [hShdef, ← Matrix.mul_assoc]; exact hcap'
  set Sb := Sh - τ • (U'ᵀ * Q * UA) with hSbdef
  set Lt := Sb * UAᵀ + τ • (U'ᵀ * Q) with hLtdef
  exact ⟨U', Lt * U', UA, R, SA, Sh, Sb, Lt, hER, hUA, rfl, hSh, hU', rfl, rfl, rfl⟩

end LeanDLRA.Literature.P1705_10175
