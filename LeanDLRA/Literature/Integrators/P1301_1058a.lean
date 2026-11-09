import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.GaugeODE
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 1301.1058: Projector-splitting (KSL) integrator

Lubich–Oseledets, *A projector-splitting integrator for dynamical low-rank approximation*, BIT 2014.
The module proves two groups of results for real `m × n` matrices with the Frobenius norm.  First,
**Theorem 4.2** (`ksl_overapproximation`): for `A = A' + ε A''` with `rank A' = q`, the integrator
of §3.2 with `r` and with `q` columns agree up to `C (ε + h)`, with `C` independent of `ε`, `h`, `n`
and of the small singular values.  The proof is not the paper's: it stays in the projector
framework, and compares both runs with `A'` through the curvature estimate
`norm_normal_increment_le` and discrete Grönwall (`ksl_run_error`).  Second, **Sections 3.3–3.4**:
the symmetrized scheme (12) (`IsStrangStep`) is of second order for `Ẏ = P(Y) Ȧ`
(`strang_local_error`, `strang_global_error`), and the explicit predictor-corrector method of §3.4
(`IsExplicitStep`) is of second order for `Ẏ = P(Y) F(Y)` (`explicit_local_error`,
`explicit_global_error`).  The paper proves neither claim and states no regularity.  Here `Ȧ`
(resp. `t ↦ F(Y(t))`) is `C^{1,1}`, and the constants depend on a bound `κ` for `‖S⁻¹‖`.  Both are
derived from one estimate for a step of (12) from a perturbed start with perturbed data
(`strang_step_estimate`).  The exact solution is given through the factors of the gauge-fixed
system (5) (`IsFactorSolution`), as in the library's `factorODE_solution_isDLRA`.  The remarks of
the paper that the symmetric composition is implicit for `Ȧ = F(A)`, and that further compositions
give higher order, are not formalized.  Non-vacuity: `exists_ksl_run`, `exists_strang_run`,
`exists_explicit_run` give runs of all three methods for `r ≤ m, n`, and `isFactorSolution_exp`,
`isC11_exp` a concrete exact solution.

Theorem 4.1 (exactness) is not restated here: the library proves it in
`Integrators/Exactness.lean` (`ksl_exact_of_factors`) under the invertibility of `V(t₁)ᵀ V(t₀)`
that the paper's proof assumes; see the docstrings there for the singular case.  Lemma 3.1 (the
exact solution of the three sub-flows) is not formalized; `ksl_increment_eq` is the closed form
of one step of §3.2.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P1301_1058

open LeanDLRA.Exactness (IsKSLIncrementStep)

variable {m n q r l : Type*} [Fintype m] [Fintype n] [Fintype q] [Fintype r] [Fintype l]
  [DecidableEq m] [DecidableEq n] [DecidableEq q] [DecidableEq r]

/-! ### Contractions -/

section Contraction

/-- `I - U Uᵀ` does not increase the Frobenius norm. -/
private theorem norm_compl_mul_le {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) (X : Matrix m l ℝ) :
    ‖(1 - U * Uᵀ) * X‖ ≤ ‖X‖ := by
  have h := (isOrthProj_leftProj (n := l) hU).norm_sub_le X
  rw [leftProj_apply] at h
  rwa [Matrix.sub_mul, Matrix.one_mul]

/-- `I - V Vᵀ` does not increase the Frobenius norm. -/
private theorem norm_mul_compl_le {V : Matrix n r ℝ} (hV : Vᵀ * V = 1) (X : Matrix l n ℝ) :
    ‖X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  have h := (isOrthProj_rightProj (m := l) hV).norm_sub_le X
  rw [rightProj_apply'] at h
  rwa [Matrix.mul_sub, Matrix.mul_one]

omit [DecidableEq m] in
/-- `U Uᵀ` does not increase the Frobenius norm. -/
private theorem norm_proj_mul_le {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) (X : Matrix m l ℝ) :
    ‖U * Uᵀ * X‖ ≤ ‖X‖ := by
  simpa using (isOrthProj_leftProj (n := l) hU).norm_le X

omit [DecidableEq n] in
/-- `V Vᵀ` does not increase the Frobenius norm. -/
private theorem norm_mul_proj_le {V : Matrix n r ℝ} (hV : Vᵀ * V = 1) (X : Matrix l n ℝ) :
    ‖X * (V * Vᵀ)‖ ≤ ‖X‖ := by
  have h := (isOrthProj_rightProj (m := l) hV).norm_le X
  rwa [rightProj_apply'] at h

end Contraction

/-! ### Projector form of one KSL step -/

omit [DecidableEq m] in
/-- **Projector form of one KSL step** (arXiv 1301.1058, §3.2, and the computation in the proof of
Theorem 4.1): `Y₁ = Y₀ + ΔA Q₀ + P₁ ΔA (I - Q₀)` with `Q₀ = V₀ V₀ᵀ`, `P₁ = U₁ U₁ᵀ`.  No
orthonormality is used. -/
theorem ksl_increment_eq {A₀ A₁ : Matrix m n ℝ} {U₀ U₁ : Matrix m r ℝ} {S₀ Ŝ₁ S₁ : Matrix r r ℝ}
    {V₀ V₁ : Matrix n r ℝ} (hs : IsKSLIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ Ŝ₁ S₁ V₁) :
    U₁ * S₁ * V₁ᵀ =
      U₀ * S₀ * V₀ᵀ + (A₁ - A₀) * (V₀ * V₀ᵀ) + U₁ * U₁ᵀ * (A₁ - A₀) * (1 - V₀ * V₀ᵀ) := by
  have hL : S₁ * V₁ᵀ = (Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀) * V₀ᵀ + U₁ᵀ * (A₁ - A₀) := by
    have h := congrArg Matrix.transpose hs.qrL
    simpa only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose] using h
  have hK : U₁ * (Ŝ₁ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ + (A₁ - A₀) * (V₀ * V₀ᵀ) := by
    rw [← Matrix.mul_assoc, hs.qrK, Matrix.add_mul, Matrix.mul_assoc (A₁ - A₀)]
  rw [Matrix.mul_assoc, hL]
  simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, hK]
  simp only [Matrix.mul_assoc]
  abel

/-! ### The curvature estimate -/

/-- `X` has a factorization `X = U S Vᵀ` with `q` orthonormal columns and an invertible `q × q` core
whose inverse has Frobenius norm at most `κ`: the factorization `A'(t) = U'(t) S'(t) V'(t)ᵀ` of
arXiv 1301.1058, §4, at one time.  Since `‖S⁻¹‖ ≥ 1 / σ_q(X)`, a bound `κ` that does not depend on
`ε` says that the `q` singular values of the rank-`q` part stay away from zero. -/
def HasRankFactorization (q : Type*) [Fintype q] [DecidableEq q] (κ : ℝ) (X : Matrix m n ℝ) :
    Prop :=
  ∃ (U : Matrix m q ℝ) (S G : Matrix q q ℝ) (V : Matrix n q ℝ),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ G * S = 1 ∧ ‖G‖ ≤ κ ∧ X = U * S * Vᵀ

/-- **Curvature estimate for the increment of a rank-`q` curve** (the rank argument in the proof of
Theorem 4.2 of arXiv 1301.1058 given here; not stated in the paper).  If `B₀`, `B₁` have rank-`q`
factorizations with core inverses bounded by `κ`, then for any projectors `W Wᵀ`, `Z Zᵀ`

    ‖(I - W Wᵀ) (B₁ - B₀) (I - Z Zᵀ)‖ ≤ κ ‖B₁ - B₀‖ (‖B₁ - B₀‖ + ‖(I - W Wᵀ) B₀‖ + ‖B₀ (I - Z Zᵀ)‖).

This is the only place where the rank of `A'` enters the proof of `ksl_overapproximation`.  No
smoothness of a factorization is needed. -/
theorem norm_normal_increment_le {κ : ℝ} {B₀ B₁ : Matrix m n ℝ}
    (h₀ : HasRankFactorization q κ B₀) (h₁ : HasRankFactorization q κ B₁)
    {W : Matrix m r ℝ} {Z : Matrix n r ℝ} (hW : Wᵀ * W = 1) (hZ : Zᵀ * Z = 1) :
    ‖(1 - W * Wᵀ) * (B₁ - B₀) * (1 - Z * Zᵀ)‖ ≤
      κ * ‖B₁ - B₀‖ * (‖B₁ - B₀‖ + ‖(1 - W * Wᵀ) * B₀‖ + ‖B₀ * (1 - Z * Zᵀ)‖) := by
  obtain ⟨U, S, G, V, hU, hV, hGS, hκ, hB₀⟩ := h₀
  obtain ⟨U', S', G', V', hU', hV', hGS', hκ', hB₁⟩ := h₁
  have hSG : S * G = 1 := mul_eq_one_comm.mp hGS
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans hκ
  set D := B₁ - B₀ with hD
  set Pc : Matrix m m ℝ := 1 - W * Wᵀ with hPc
  set Qc : Matrix n n ℝ := 1 - Z * Zᵀ with hQc
  -- the factors of `B₀` in terms of `B₀`
  have e₁ : U = B₀ * V * G := by
    rw [hB₀, Matrix.mul_assoc (U * S), hV, Matrix.mul_one, Matrix.mul_assoc, hSG, Matrix.mul_one]
  have e₂ : Vᵀ = G * Uᵀ * B₀ := by
    calc Vᵀ = G * S * Vᵀ := by rw [hGS, Matrix.one_mul]
      _ = G * (Uᵀ * U) * S * Vᵀ := by rw [hU, Matrix.mul_one]
      _ = G * Uᵀ * B₀ := by rw [hB₀]; simp only [Matrix.mul_assoc]
  have e₃ : (1 - U * Uᵀ) * B₀ = 0 := by
    have h : U * Uᵀ * B₀ = B₀ := by
      calc U * Uᵀ * B₀ = U * (Uᵀ * U) * (S * Vᵀ) := by rw [hB₀]; simp only [Matrix.mul_assoc]
        _ = B₀ := by rw [hU, Matrix.mul_one, hB₀, Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  have e₄ : B₀ * (1 - V * Vᵀ) = 0 := by
    have h : B₀ * (V * Vᵀ) = B₀ := by
      calc B₀ * (V * Vᵀ) = U * S * (Vᵀ * V) * Vᵀ := by rw [hB₀]; simp only [Matrix.mul_assoc]
        _ = B₀ := by rw [hV, Matrix.mul_one, hB₀]
    rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  have e₅ : (1 - U * Uᵀ) * B₁ = (1 - U * Uᵀ) * D := by
    rw [hD, Matrix.mul_sub, e₃, sub_zero]
  have e₆ : B₁ * (1 - V * Vᵀ) = D * (1 - V * Vᵀ) := by
    rw [hD, Matrix.sub_mul, e₄, sub_zero]
  -- the factors of `B₁`
  have e₇ : U' * S' = B₁ * V' := by
    rw [hB₁, Matrix.mul_assoc (U' * S'), hV', Matrix.mul_one]
  have e₈ : S' * V'ᵀ = U'ᵀ * B₁ := by
    calc S' * V'ᵀ = (U'ᵀ * U') * S' * V'ᵀ := by rw [hU', Matrix.one_mul]
      _ = U'ᵀ * B₁ := by rw [hB₁]; simp only [Matrix.mul_assoc]
  -- the third term is second order in `D`
  have hc : ‖(1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ)‖ ≤ κ * ‖D‖ * ‖D‖ := by
    have : (1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ) =
        ((1 - U * Uᵀ) * D * V') * G' * (U'ᵀ * (D * (1 - V * Vᵀ))) := by
      rw [← e₆, ← e₅, Matrix.mul_assoc _ B₁ V', ← e₇, ← Matrix.mul_assoc U'ᵀ, ← e₈]
      calc (1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ)
          = (1 - U * Uᵀ) * (U' * (S' * (G' * S')) * V'ᵀ) * (1 - V * Vᵀ) := by
            rw [hGS', Matrix.mul_one, hB₁]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [this]
    calc _ ≤ ‖(1 - U * Uᵀ) * D * V'‖ * ‖G'‖ * ‖U'ᵀ * (D * (1 - V * Vᵀ))‖ := by
          refine (Frobenius.norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (Frobenius.norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖D‖ * κ * ‖D‖ := by
          have h1 : ‖(1 - U * Uᵀ) * D * V'‖ ≤ ‖D‖ :=
            (norm_mul_le_of_orthonormal hV' _).trans (norm_compl_mul_le hU _)
          have h2 : ‖U'ᵀ * (D * (1 - V * Vᵀ))‖ ≤ ‖D‖ :=
            (norm_transpose_mul_le hU' _).trans (norm_mul_compl_le hV _)
          gcongr
      _ = κ * ‖D‖ * ‖D‖ := by ring
  have key : Pc * D * Qc = (Pc * U) * (Uᵀ * D * Qc) + (Pc * ((1 - U * Uᵀ) * D * V)) * (Vᵀ * Qc)
      + Pc * ((1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ)) * Qc := by
    rw [e₅]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [key]
  have ha : ‖(Pc * U) * (Uᵀ * D * Qc)‖ ≤ κ * ‖D‖ * ‖Pc * B₀‖ := by
    calc _ ≤ ‖Pc * U‖ * ‖Uᵀ * D * Qc‖ := Frobenius.norm_mul_le _ _
      _ ≤ (‖Pc * B₀‖ * κ) * ‖D‖ := by
          have h1 : ‖Pc * U‖ ≤ ‖Pc * B₀‖ * κ := by
            have : Pc * U = Pc * B₀ * V * G := by
              conv_lhs => rw [e₁]
              simp only [Matrix.mul_assoc]
            rw [this]
            refine (Frobenius.norm_mul_le _ _).trans ?_
            exact mul_le_mul (norm_mul_le_of_orthonormal hV _) hκ (norm_nonneg _) (norm_nonneg _)
          have h2 : ‖Uᵀ * D * Qc‖ ≤ ‖D‖ :=
            (norm_mul_compl_le hZ _).trans (norm_transpose_mul_le hU _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) hκ0)
      _ = _ := by ring
  have hb : ‖(Pc * ((1 - U * Uᵀ) * D * V)) * (Vᵀ * Qc)‖ ≤ κ * ‖D‖ * ‖B₀ * Qc‖ := by
    calc _ ≤ ‖Pc * ((1 - U * Uᵀ) * D * V)‖ * ‖Vᵀ * Qc‖ := Frobenius.norm_mul_le _ _
      _ ≤ ‖D‖ * (κ * ‖B₀ * Qc‖) := by
          have h1 : ‖Pc * ((1 - U * Uᵀ) * D * V)‖ ≤ ‖D‖ :=
            (norm_compl_mul_le hW _).trans
              ((norm_mul_le_of_orthonormal hV _).trans (norm_compl_mul_le hU _))
          have h2 : ‖Vᵀ * Qc‖ ≤ κ * ‖B₀ * Qc‖ := by
            have : Vᵀ * Qc = G * (Uᵀ * (B₀ * Qc)) := by
              conv_lhs => rw [e₂]
              simp only [Matrix.mul_assoc]
            rw [this]
            refine (Frobenius.norm_mul_le _ _).trans ?_
            exact mul_le_mul hκ (norm_transpose_mul_le hU _) (norm_nonneg _) hκ0
          exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hc' : ‖Pc * ((1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ)) * Qc‖ ≤ κ * ‖D‖ * ‖D‖ :=
    ((norm_mul_compl_le hZ _).trans (norm_compl_mul_le hW _)).trans hc
  calc _ ≤ ‖(Pc * U) * (Uᵀ * D * Qc)‖ + ‖(Pc * ((1 - U * Uᵀ) * D * V)) * (Vᵀ * Qc)‖
        + ‖Pc * ((1 - U * Uᵀ) * B₁ * (1 - V * Vᵀ)) * Qc‖ := norm_add₃_le
    _ ≤ κ * ‖D‖ * ‖Pc * B₀‖ + κ * ‖D‖ * ‖B₀ * Qc‖ + κ * ‖D‖ * ‖D‖ := by gcongr
    _ = _ := by ring

/-! ### Theorem 4.2: robustness under over-approximation -/

omit [DecidableEq m] [DecidableEq n] in
/-- One step of the recursion behind `ksl_overapproximation` (Theorem 4.2 of arXiv 1301.1058).  Let
`B₀, B₁` be the values of the rank-`q` part at two times and `C₀, C₁` those of the perturbation.
One KSL step for `A = B + ε C` from `Y₀` satisfies

    ‖Y₁ - B₁‖ ≤ (1 + 2 κ b h) ‖Y₀ - B₀‖ + 2 ε c h + κ b (2 b + ε c) h².

The number of columns of the KSL factors plays no role. -/
theorem ksl_step_error {κ b c ε h : ℝ} {B₀ B₁ C₀ C₁ : Matrix m n ℝ}
    {U₀ U₁ : Matrix m r ℝ} {S₀ Ŝ₁ S₁ : Matrix r r ℝ} {V₀ V₁ : Matrix n r ℝ}
    (hκ : 0 ≤ κ) (hb : 0 ≤ b) (hε : 0 ≤ ε) (hh : 0 ≤ h)
    (h₀ : HasRankFactorization q κ B₀) (h₁ : HasRankFactorization q κ B₁)
    (hB : ‖B₁ - B₀‖ ≤ b * h) (hC : ‖C₁ - C₀‖ ≤ c * h) (hV₀ : V₀ᵀ * V₀ = 1)
    (hs : IsKSLIncrementStep (B₀ + ε • C₀) (B₁ + ε • C₁) U₀ S₀ V₀ U₁ Ŝ₁ S₁ V₁) :
    ‖U₁ * S₁ * V₁ᵀ - B₁‖ ≤ (1 + 2 * κ * b * h) * ‖U₀ * S₀ * V₀ᵀ - B₀‖ + 2 * ε * c * h
      + κ * b * (2 * b + ε * c) * h ^ 2 := by
  classical
  have hU₁ := hs.orthU
  have hY₁ := ksl_increment_eq hs
  have hK := hs.qrK
  set Y₀ := U₀ * S₀ * V₀ᵀ with hY₀
  set ΔA := (B₁ + ε • C₁) - (B₀ + ε • C₀) with hΔA
  have hΔA' : ΔA = (B₁ - B₀) + ε • (C₁ - C₀) := by
    rw [hΔA, smul_sub]; abel
  have hA : ‖ΔA‖ ≤ b * h + ε * (c * h) := by
    rw [hΔA']
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε]
    gcongr
  have hY₀Q : Y₀ * (1 - V₀ * V₀ᵀ) = 0 := by
    have : Y₀ * (V₀ * V₀ᵀ) = Y₀ := by
      calc Y₀ * (V₀ * V₀ᵀ) = U₀ * S₀ * (V₀ᵀ * V₀) * V₀ᵀ := by
            rw [hY₀]; simp only [Matrix.mul_assoc]
        _ = Y₀ := by rw [hV₀, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  have hPcU : (1 - U₁ * U₁ᵀ) * U₁ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU₁, Matrix.mul_one, sub_self]
  have hcap : (1 - U₁ * U₁ᵀ) * (Y₀ + ΔA * (V₀ * V₀ᵀ)) = 0 := by
    have : Y₀ + ΔA * (V₀ * V₀ᵀ) = U₁ * (Ŝ₁ * V₀ᵀ) := by
      rw [← Matrix.mul_assoc U₁, hK, Matrix.add_mul, Matrix.mul_assoc ΔA]
    rw [this, ← Matrix.mul_assoc, hPcU, Matrix.zero_mul]
  -- the two normal defects of `B₀`
  set e := ‖Y₀ - B₀‖ with he
  have hPB : ‖(1 - U₁ * U₁ᵀ) * B₀‖ ≤ e + ‖ΔA‖ := by
    have : (1 - U₁ * U₁ᵀ) * B₀ = -((1 - U₁ * U₁ᵀ) * ((Y₀ - B₀) + ΔA * (V₀ * V₀ᵀ))) := by
      have h2 : (Y₀ - B₀) + ΔA * (V₀ * V₀ᵀ) = (Y₀ + ΔA * (V₀ * V₀ᵀ)) - B₀ := by abel
      rw [h2, Matrix.mul_sub, hcap]; simp
    rw [this, norm_neg]
    refine (norm_compl_mul_le hU₁ _).trans ((norm_add_le _ _).trans ?_)
    have := norm_mul_proj_le (l := m) hV₀ ΔA
    gcongr
  have hBQ : ‖B₀ * (1 - V₀ * V₀ᵀ)‖ ≤ e := by
    have : B₀ * (1 - V₀ * V₀ᵀ) = -((Y₀ - B₀) * (1 - V₀ * V₀ᵀ)) := by
      rw [Matrix.sub_mul, hY₀Q]; simp
    rw [this, norm_neg]
    exact norm_mul_compl_le hV₀ _
  have hnorm := norm_normal_increment_le h₀ h₁ hU₁ hV₀
  have he0 : 0 ≤ e := norm_nonneg _
  have hN : ‖(1 - U₁ * U₁ᵀ) * (B₁ - B₀) * (1 - V₀ * V₀ᵀ)‖ ≤
      κ * (b * h) * (b * h + (e + (b * h + ε * (c * h))) + e) := by
    refine hnorm.trans ?_
    have h1 : ‖B₁ - B₀‖ + ‖(1 - U₁ * U₁ᵀ) * B₀‖ + ‖B₀ * (1 - V₀ * V₀ᵀ)‖ ≤
        b * h + (e + (b * h + ε * (c * h))) + e := by
      have := hPB.trans (add_le_add_right hA e)
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB hκ) h1 (by positivity) (by positivity)
  have hN' : ‖(1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ)‖ ≤ c * h :=
    (norm_mul_compl_le hV₀ _).trans ((norm_compl_mul_le hU₁ _).trans hC)
  have herr : U₁ * S₁ * V₁ᵀ - B₁ = (Y₀ - B₀) + ε • (C₁ - C₀)
      - (1 - U₁ * U₁ᵀ) * (B₁ - B₀) * (1 - V₀ * V₀ᵀ)
      - ε • ((1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ)) := by
    have h3 : (1 - U₁ * U₁ᵀ) * ΔA * (1 - V₀ * V₀ᵀ) =
        (1 - U₁ * U₁ᵀ) * (B₁ - B₀) * (1 - V₀ * V₀ᵀ)
          + ε • ((1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ)) := by
      rw [hΔA', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have h4 : U₁ * S₁ * V₁ᵀ = Y₀ + ΔA - (1 - U₁ * U₁ᵀ) * ΔA * (1 - V₀ * V₀ᵀ) := by
      rw [hY₁]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [h4, h3, hΔA']
    abel
  rw [herr]
  have hsm : ‖ε • (C₁ - C₀)‖ ≤ ε * (c * h) := by
    rw [norm_smul, Real.norm_of_nonneg hε]; gcongr
  have hsm' : ‖ε • ((1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ))‖ ≤ ε * (c * h) := by
    rw [norm_smul, Real.norm_of_nonneg hε]; gcongr
  calc _ ≤ ‖(Y₀ - B₀) + ε • (C₁ - C₀) - (1 - U₁ * U₁ᵀ) * (B₁ - B₀) * (1 - V₀ * V₀ᵀ)‖
        + ‖ε • ((1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ))‖ := norm_sub_le _ _
    _ ≤ ‖(Y₀ - B₀) + ε • (C₁ - C₀)‖ + ‖(1 - U₁ * U₁ᵀ) * (B₁ - B₀) * (1 - V₀ * V₀ᵀ)‖
        + ‖ε • ((1 - U₁ * U₁ᵀ) * (C₁ - C₀) * (1 - V₀ * V₀ᵀ))‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ e + ε * (c * h) + κ * (b * h) * (b * h + (e + (b * h + ε * (c * h))) + e)
        + ε * (c * h) := by
        have := norm_add_le (Y₀ - B₀) (ε • (C₁ - C₀))
        linarith
    _ = _ := by ring

/-- `n` steps of the splitting integrator of arXiv 1301.1058, §3.2, for a given `A`, with step
size `h` on the grid `t₀ + k h`: factors `U k`, `S k`, `V k` (`Y k = U k * S k * (V k)ᵀ`) and the
intermediate cores `Ŝ (k + 1)`.  The QR factorizations are free, as in the paper. -/
structure IsKSLRun (A : ℝ → Matrix m n ℝ) (t₀ h : ℝ) (N : ℕ) (U : ℕ → Matrix m r ℝ)
    (Ŝ S : ℕ → Matrix r r ℝ) (V : ℕ → Matrix n r ℝ) : Prop where
  orthV : ∀ k ≤ N, (V k)ᵀ * V k = 1
  step : ∀ k < N, IsKSLIncrementStep (A (t₀ + k * h)) (A (t₀ + (k + 1) * h)) (U k) (S k) (V k)
    (U (k + 1)) (Ŝ (k + 1)) (S (k + 1)) (V (k + 1))

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- The grid points of a run stay in `[t₀, T]`. -/
private theorem grid_mem {t₀ T h : ℝ} {N k : ℕ} (hh : 0 ≤ h) (hT : t₀ + N * h ≤ T) (hk : k ≤ N) :
    t₀ + k * h ∈ Icc t₀ T := by
  have h1 : (k : ℝ) * h ≤ N * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh
  exact ⟨by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh], by linarith⟩

omit [DecidableEq m] [DecidableEq n] in
/-- **The KSL iterates stay `O(ε + h)` close to the rank-`q` part** (the estimate that gives
Theorem 4.2 of arXiv 1301.1058).  Under the assumptions of `ksl_overapproximation`, for the run of
one of the two integrators and `τ = T - t₀`,

    ‖Yₙ - A'(tₙ)‖ ≤ e^{2 κ b τ} ((a + 2 c τ + κ b c τ²) ε + 2 κ b² τ h).

This run may have any number of columns.  Proof: `ksl_step_error` and discrete Grönwall. -/
theorem ksl_run_error {κ b c ε h t₀ T a : ℝ} {N : ℕ} {A' A'' : ℝ → Matrix m n ℝ}
    {A₀'' : Matrix m n ℝ} {U : ℕ → Matrix m r ℝ} {Ŝ S : ℕ → Matrix r r ℝ}
    {V : ℕ → Matrix n r ℝ} (hκ : 0 ≤ κ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hh : 0 ≤ h)
    (hT : t₀ + N * h ≤ T) (hfac : ∀ t ∈ Icc t₀ T, HasRankFactorization q κ (A' t))
    (hA' : ∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A' t - A' s‖ ≤ b * |t - s|)
    (hA'' : ∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A'' t - A'' s‖ ≤ c * |t - s|)
    (hrun : IsKSLRun (fun t => A' t + ε • A'' t) t₀ h N U Ŝ S V)
    (hY₀ : U 0 * S 0 * (V 0)ᵀ = A' t₀ + ε • A₀'') (ha : ‖A₀''‖ ≤ a) :
    ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - A' (t₀ + n * h)‖ ≤ Real.exp (2 * κ * b * (T - t₀)) *
      ((a + 2 * c * (T - t₀) + κ * b * c * (T - t₀) ^ 2) * ε + 2 * κ * b ^ 2 * (T - t₀) * h) := by
  set τ := T - t₀ with hτ
  have hN0 : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hL : 0 ≤ 2 * κ * b := by positivity
  set g := 2 * ε * c * h + κ * b * (2 * b + ε * c) * h ^ 2 with hg
  have hg0 : 0 ≤ g := by positivity
  set e : ℕ → ℝ := fun k => ‖U k * S k * (V k)ᵀ - A' (t₀ + k * h)‖ with he
  have hrec : ∀ k < N, e (k + 1) ≤ Real.exp (2 * κ * b * h) * e k + g := by
    intro k hk
    have hk1 : t₀ + (k : ℝ) * h ∈ Icc t₀ T := grid_mem hh hT hk.le
    have hk2 : t₀ + (k + 1 : ℝ) * h ∈ Icc t₀ T := by
      have := grid_mem (k := k + 1) hh hT hk
      simpa only [Nat.cast_add, Nat.cast_one] using this
    have hdist : |t₀ + (k + 1 : ℝ) * h - (t₀ + k * h)| = h := by
      have : t₀ + (k + 1 : ℝ) * h - (t₀ + k * h) = h := by ring
      rw [this, abs_of_nonneg hh]
    have hB := hA' _ hk1 _ hk2
    have hC := hA'' _ hk1 _ hk2
    rw [hdist] at hB hC
    have h1 := ksl_step_error hκ hb hε hh (hfac _ hk1) (hfac _ hk2) hB hC
      (hrun.orthV k hk.le) (hrun.step k hk)
    have h2 : 1 + 2 * κ * b * h ≤ Real.exp (2 * κ * b * h) := by
      linarith [Real.add_one_le_exp (2 * κ * b * h)]
    have he0 : 0 ≤ e k := norm_nonneg _
    have h3 : e (k + 1) = ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - A' (t₀ + (k + 1 : ℝ) * h)‖ := by
      simp only [he, Nat.cast_add, Nat.cast_one]
    rw [h3]
    calc _ ≤ (1 + 2 * κ * b * h) * e k + g := by rw [hg]; linarith
      _ ≤ _ := by gcongr
  intro n hn
  have hg' := LeanDLRA.discrete_gronwall_exp_le hL hh hg0 hrec n hn
  set x := (n : ℝ) * h with hx
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hh
  have hxτ : x ≤ τ := by
    have := (grid_mem hh hT hn).2
    rw [hτ]; linarith
  have hxh : x * h ≤ τ ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [hx, Nat.cast_zero, zero_mul]; positivity
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      have h2 : h ≤ x := by rw [hx]; nlinarith
      have h3 : h ≤ τ := h2.trans hxτ
      calc x * h ≤ τ * τ := mul_le_mul hxτ h3 hh hτ0
        _ = τ ^ 2 := by ring
  have he0 : e 0 ≤ ε * a := by
    have : e 0 = ‖ε • A₀''‖ := by
      simp only [he, Nat.cast_zero, zero_mul, add_zero, hY₀, add_sub_cancel_left]
    rw [this, norm_smul, Real.norm_of_nonneg hε]
    gcongr
  have hsum : e 0 + n * g ≤ (a + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h := by
    have h1 : (n : ℝ) * g = 2 * ε * c * x + 2 * κ * b ^ 2 * x * h + κ * b * c * ε * (x * h) := by
      rw [hg, hx]; ring
    have h2 : 2 * ε * c * x ≤ 2 * ε * c * τ := by gcongr
    have h3 : 2 * κ * b ^ 2 * x * h ≤ 2 * κ * b ^ 2 * τ * h := by gcongr
    have h4 : κ * b * c * ε * (x * h) ≤ κ * b * c * ε * τ ^ 2 := by gcongr
    rw [h1]
    nlinarith
  have hsum0 : 0 ≤ (a + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h := by
    have : 0 ≤ a := (norm_nonneg _).trans ha
    positivity
  calc e n ≤ Real.exp (2 * κ * b * x) * (e 0 + n * g) := hg'
    _ ≤ Real.exp (2 * κ * b * τ) * ((a + 2 * c * τ + κ * b * c * τ ^ 2) * ε
          + 2 * κ * b ^ 2 * τ * h) := by
        refine mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxτ hL)) hsum ?_
          (Real.exp_pos _).le
        exact add_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hg0)

omit [DecidableEq m] [DecidableEq n] in
/-- **Theorem 4.2 of arXiv 1301.1058 (robustness under over-approximation).**  Let
`A(t) = A'(t) + ε A''(t)`, where `A'(t) = U'(t) S'(t) V'(t)ᵀ` has rank `q`, with `q` orthonormal
columns and `‖S'(t)⁻¹‖ ≤ κ` (`HasRankFactorization`).  Let `Yₙ`, `Ȳₙ` be the results of `n` steps of
the splitting integrator of §3.2 with step size `h`, applied to `A` with `r` and with `q` columns,
from `Y₀ = A'(t₀) + ε A₀''` and `Ȳ₀ = A'(t₀) + ε Ā₀''`, with `‖A₀''‖ ≤ a`, `‖Ā₀''‖ ≤ ā`.  Then, as
long as `t₀ + n h ≤ T`,

    ‖Yₙ - Ȳₙ‖ ≤ C (ε + h),

where `C` is independent of `n`, `h` and `ε`, and of the small singular values: the quantifiers
choose `C` before `ε`, `h`, `A'`, `A''`, the starting values and the runs.  It depends only on the
bounds and on `T - t₀`:
`C = e^{2 κ b (T-t₀)} (a + ā + 4 c (T-t₀) + 2 κ b c (T-t₀)² + 4 κ b² (T-t₀))`.

Differences from the paper:

* The paper's "`A'`, `A''` and their derivatives are bounded independently of `ε`" enters only as
  the Lipschitz bounds `b`, `c` on `[t₀, T]`, which follow from the derivative bounds by the mean
  value inequality.  Bounds on `A'`, `A''` themselves and differentiability are not needed.
* `κ` is the bound `(S')⁻¹ = O(1)` that the paper uses in its proof without stating it, in the
  Frobenius norm.
* `q < r`, `rank Y₀ = r`, `rank Ȳ₀ = q`, a smooth choice of the factors of `A'` (a factorization at
  each `t` is enough) and smallness of `ε`, `h` are not assumed.  That runs exist for `r ≤ m, n` is
  `exists_ksl_run`.  The theorem is stronger than the paper's in these respects.
* The proof is not the paper's comparison of gauge-fixed block factor ODEs.  Both runs are compared
  with `A'` (`ksl_run_error`): the projector form of a step gives
  `Y₁ - A'₁ = (Y₀ - A'₀) + ε ΔA'' - (I - P₁) ΔA (I - Q₀)`, and the rank of `A'` gives
  `‖(I - P₁) ΔA' (I - Q₀)‖ ≤ κ b h (2 ‖Y₀ - A'₀‖ + (2 b + ε c) h)` (`norm_normal_increment_le`), so
  that the error recursion closes by discrete Grönwall. -/
theorem ksl_overapproximation (q r : Type*) [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    {κ b c a ā t₀ T : ℝ} (hκ : 0 ≤ κ) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : 0 ≤ a) (hā : 0 ≤ ā)
    (hT : t₀ ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε h : ℝ) (A' A'' : ℝ → Matrix m n ℝ) (A₀'' Ā₀'' : Matrix m n ℝ) (N : ℕ)
      (U : ℕ → Matrix m r ℝ) (Ŝ S : ℕ → Matrix r r ℝ) (V : ℕ → Matrix n r ℝ)
      (Uq : ℕ → Matrix m q ℝ) (Ŝq Sq : ℕ → Matrix q q ℝ) (Vq : ℕ → Matrix n q ℝ),
      0 ≤ ε → 0 ≤ h → t₀ + N * h ≤ T →
      (∀ t ∈ Icc t₀ T, HasRankFactorization q κ (A' t)) →
      (∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A' t - A' s‖ ≤ b * |t - s|) →
      (∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A'' t - A'' s‖ ≤ c * |t - s|) →
      ‖A₀''‖ ≤ a → ‖Ā₀''‖ ≤ ā →
      IsKSLRun (fun t => A' t + ε • A'' t) t₀ h N U Ŝ S V →
      IsKSLRun (fun t => A' t + ε • A'' t) t₀ h N Uq Ŝq Sq Vq →
      U 0 * S 0 * (V 0)ᵀ = A' t₀ + ε • A₀'' →
      Uq 0 * Sq 0 * (Vq 0)ᵀ = A' t₀ + ε • Ā₀'' →
      ∀ n ≤ N, ‖U n * S n * (V n)ᵀ - Uq n * Sq n * (Vq n)ᵀ‖ ≤ C * (ε + h) := by
  classical
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = T - t₀ := ⟨_, rfl⟩
  have hτ : 0 ≤ τ := by rw [hτdef]; linarith
  refine ⟨Real.exp (2 * κ * b * τ) * (a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2
    + 4 * κ * b ^ 2 * τ), by positivity, ?_⟩
  intro ε h A' A'' A₀'' Ā₀'' N U Ŝ S V Uq Ŝq Sq Vq hε hh hN hfac hA' hA'' hA₀ hĀ₀ hrun hrun' hY₀
    hYq₀ n hn
  have h1 := ksl_run_error hκ hb hc hε hh hN hfac hA' hA'' hrun hY₀ hA₀ n hn
  have h2 := ksl_run_error hκ hb hc hε hh hN hfac hA' hA'' hrun' hYq₀ hĀ₀ n hn
  rw [← hτdef] at h1 h2
  have h3 : 0 ≤ κ * b ^ 2 * τ * ε := by positivity
  have h4 : 0 ≤ (a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2) * h := by positivity
  have key : (a + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h
      + ((ā + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h)
      ≤ (a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2 + 4 * κ * b ^ 2 * τ) * (ε + h) := by
    have : (a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2 + 4 * κ * b ^ 2 * τ) * (ε + h)
        - ((a + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h
          + ((ā + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h))
        = (a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2) * h + 4 * (κ * b ^ 2 * τ * ε) := by ring
    linarith
  have hsum := norm_sub_le_norm_sub_add_norm_sub (U n * S n * (V n)ᵀ) (A' (t₀ + n * h))
    (Uq n * Sq n * (Vq n)ᵀ)
  have hsum' : ‖U n * S n * (V n)ᵀ - Uq n * Sq n * (Vq n)ᵀ‖ ≤
      ‖U n * S n * (V n)ᵀ - A' (t₀ + n * h)‖ + ‖Uq n * Sq n * (Vq n)ᵀ - A' (t₀ + n * h)‖ := by
    rwa [norm_sub_rev (A' (t₀ + n * h))] at hsum
  calc _ ≤ _ := hsum'
    _ ≤ _ := add_le_add h1 h2
    _ = Real.exp (2 * κ * b * τ) * ((a + 2 * c * τ + κ * b * c * τ ^ 2) * ε
          + 2 * κ * b ^ 2 * τ * h
          + ((ā + 2 * c * τ + κ * b * c * τ ^ 2) * ε + 2 * κ * b ^ 2 * τ * h)) := by ring
    _ ≤ Real.exp (2 * κ * b * τ) * ((a + ā + 4 * c * τ + 2 * κ * b * c * τ ^ 2
          + 4 * κ * b ^ 2 * τ) * (ε + h)) := mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = _ := by ring

/-! ### Non-vacuity of Theorem 4.2 -/

section NonVacuity

omit [DecidableEq m] [DecidableEq n] in
/-- `HasRankFactorization` (arXiv 1301.1058, §4) says in particular that `X` has rank exactly
`q`. -/
theorem HasRankFactorization.rank_eq {κ : ℝ} {X : Matrix m n ℝ}
    (hX : HasRankFactorization q κ X) : X.rank = Fintype.card q := by
  obtain ⟨U, S, G, V, hU, hV, hGS, -, rfl⟩ := hX
  have hS : S = Uᵀ * (U * S * Vᵀ) * V := by
    calc S = (Uᵀ * U) * S * (Vᵀ * V) := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hunit : IsUnit S.det := by
    have h1 : IsUnit S := IsUnit.of_mul_eq_one G (mul_eq_one_comm.mp hGS)
    exact (Matrix.isUnit_iff_isUnit_det S).mp h1
  apply le_antisymm
  · calc (U * S * Vᵀ).rank ≤ Vᵀ.rank := Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card q := by simpa using Vᵀ.rank_le_card_height
  · calc Fintype.card q = S.rank := (Matrix.rank_of_isUnit S
        ((Matrix.isUnit_iff_isUnit_det S).mpr hunit)).symm
      _ = (Uᵀ * (U * S * Vᵀ) * V).rank := by rw [← hS]
      _ ≤ (Uᵀ * (U * S * Vᵀ)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (U * S * Vᵀ).rank := Matrix.rank_mul_le_right _ _

omit [DecidableEq m] [DecidableEq n] in
/-- One step of the splitting integrator exists for `r ≤ m, n`, also for rank-deficient `K₁`, `L₁`
(arXiv 1301.1058, §3.2: the factorizations are computed "using QR or SVD"). -/
theorem exists_ksl_step {r : ℕ} (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (A₀ A₁ : Matrix m n ℝ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix n (Fin r) ℝ) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (Ŝ₁ S₁ : Matrix (Fin r) (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ),
      IsKSLIncrementStep A₀ A₁ U₀ S₀ V₀ U₁ Ŝ₁ S₁ V₁ ∧ V₁ᵀ * V₁ = 1 := by
  obtain ⟨U₁, Ŝ₁, hU₁, hK⟩ := MatrixKSL.exists_qr (U₀ * S₀ + (A₁ - A₀) * V₀) hm
  obtain ⟨V₁, R, hV₁, hL⟩ :=
    MatrixKSL.exists_qr (V₀ * (Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀)ᵀ + (A₁ - A₀)ᵀ * U₁) hn
  exact ⟨U₁, Ŝ₁, Rᵀ, V₁,
    ⟨hU₁, hK.symm, by rw [Matrix.transpose_transpose]; exact hL.symm⟩, hV₁⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Runs of the splitting integrator of arXiv 1301.1058, §3.2, exist from every starting
factorization with orthonormal `V₀`, for `r ≤ m, n`; the run hypotheses of `ksl_overapproximation`
can therefore always be met. -/
theorem exists_ksl_run {r : ℕ} (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (A : ℝ → Matrix m n ℝ) (t₀ h : ℝ) (N : ℕ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (U : ℕ → Matrix m (Fin r) ℝ) (Ŝ S : ℕ → Matrix (Fin r) (Fin r) ℝ)
      (V : ℕ → Matrix n (Fin r) ℝ),
      U 0 = U₀ ∧ S 0 = S₀ ∧ V 0 = V₀ ∧ IsKSLRun A t₀ h N U Ŝ S V := by
  let St := {p : Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ ×
    Matrix n (Fin r) ℝ // p.2.2.2ᵀ * p.2.2.2 = 1}
  have hstep : ∀ (k : ℕ) (x : St), ∃ y : St,
      IsKSLIncrementStep (A (t₀ + k * h)) (A (t₀ + (k + 1) * h)) x.1.1 x.1.2.2.1 x.1.2.2.2
        y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2 := by
    intro k x
    obtain ⟨U₁, Ŝ₁, S₁, V₁, hs, hV₁⟩ :=
      exists_ksl_step hm hn (A (t₀ + k * h)) (A (t₀ + (k + 1) * h)) x.1.1 x.1.2.2.1 x.1.2.2.2
    exact ⟨⟨(U₁, Ŝ₁, S₁, V₁), hV₁⟩, hs⟩
  choose f hf using hstep
  let s : ℕ → St := fun k => Nat.rec ⟨(U₀, 0, S₀, V₀), hV₀⟩ (fun k x => f k x) k
  exact ⟨fun k => (s k).1.1, fun k => (s k).1.2.1, fun k => (s k).1.2.2.1,
    fun k => (s k).1.2.2.2, rfl, rfl, rfl, ⟨fun k _ => (s k).2, fun k _ => hf k (s k)⟩⟩

/-- The rank-`1` part of the instance below: `e₁ e₁ᵀ` on `ℝ^{2×2}`, with `κ = 1`. -/
private theorem hasRankFactorization_e₁ : HasRankFactorization (Fin 1) 1
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨!![1; 0], 1, 1, !![1; 0], ?_, ?_, by simp, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Frobenius.norm_def]; simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- All hypotheses of `ksl_overapproximation` (Theorem 4.2 of arXiv 1301.1058) can hold at once, for
every `ε`, `h`, `N`: on `ℝ^{2×2}` take `q = 1`, `r = 2`, `A' = e₁ e₁ᵀ`, `A''(t) = t e₂ e₂ᵀ`, with
`Y₀ = e₁ e₁ᵀ + ε e₂ e₂ᵀ`, of rank `2` for `ε ≠ 0` and nearly singular for small `ε`, and
`Ȳ₀ = e₁ e₁ᵀ`.  The runs are those of `exists_ksl_run`. -/
example (t₀ T ε h : ℝ) (N : ℕ) :
    ∃ (A' A'' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A₀'' Ā₀'' : Matrix (Fin 2) (Fin 2) ℝ)
      (U : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (Ŝ S : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
      (V : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (Uq : ℕ → Matrix (Fin 2) (Fin 1) ℝ)
      (Ŝq Sq : ℕ → Matrix (Fin 1) (Fin 1) ℝ) (Vq : ℕ → Matrix (Fin 2) (Fin 1) ℝ),
      (∀ t ∈ Icc t₀ T, HasRankFactorization (Fin 1) 1 (A' t)) ∧
      (∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A' t - A' s‖ ≤ 0 * |t - s|) ∧
      (∀ s ∈ Icc t₀ T, ∀ t ∈ Icc t₀ T, ‖A'' t - A'' s‖ ≤ ‖A₀''‖ * |t - s|) ∧
      IsKSLRun (fun t => A' t + ε • A'' t) t₀ h N U Ŝ S V ∧
      IsKSLRun (fun t => A' t + ε • A'' t) t₀ h N Uq Ŝq Sq Vq ∧
      U 0 * S 0 * (V 0)ᵀ = A' t₀ + ε • A₀'' ∧
      Uq 0 * Sq 0 * (Vq 0)ᵀ = A' t₀ + ε • Ā₀'' := by
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 2) (Fin 2) ℝ, E = !![1, 0; 0, 0] := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin 2) (Fin 2) ℝ, F = !![0, 0; 0, 1] := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e = !![1; 0] := ⟨_, rfl⟩
  have hee : eᵀ * e = 1 := by
    rw [he]; ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hE' : e * (1 : Matrix (Fin 1) (Fin 1) ℝ) * eᵀ = E := by
    rw [he, hE]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  obtain ⟨U, Ŝ, S, V, hU0, hS0, hV0, hrun⟩ := exists_ksl_run (m := Fin 2) (n := Fin 2) (r := 2)
    (by simp) (by simp) (fun t => E + ε • (t • F)) t₀ h N 1 (E + ε • F) 1 (by simp)
  obtain ⟨Uq, Ŝq, Sq, Vq, hUq0, hSq0, hVq0, hrunq⟩ := exists_ksl_run (m := Fin 2) (n := Fin 2)
    (r := 1) (by simp) (by simp) (fun t => E + ε • (t • F)) t₀ h N e 1 e hee
  refine ⟨fun _ => E, fun t => t • F, F, 0, U, Ŝ, S, V, Uq, Ŝq, Sq, Vq, ?_, ?_, ?_, hrun, hrunq,
    ?_, ?_⟩
  · intro t _
    rw [hE]; exact hasRankFactorization_e₁
  · intro s _ t _
    simp
  · intro s _ t _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]
  · rw [hU0, hS0, hV0]; simp
  · rw [hUq0, hSq0, hVq0, hE']; simp

end NonVacuity

/-! ### Calculus: `C^{1,1}` curves -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve on `[a, b]` with right derivative `f'` bounded by `p₁` and Lipschitz with constant
`p₂`.  This is the regularity used for `A` and for the projectors of the exact solution in the
second-order results for arXiv 1301.1058, §3.3–3.4. -/
structure IsC11 (f f' : ℝ → E) (a b p₁ p₂ : ℝ) : Prop where
  cont : ContinuousOn f (Icc a b)
  deriv : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t
  bound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ p₁
  lip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖f' t - f' s‖ ≤ p₂ * |t - s|
  nn₁ : 0 ≤ p₁
  nn₂ : 0 ≤ p₂

/-- A curve with bounded right derivative is Lipschitz. -/
private theorem norm_sub_le_of_right_deriv {f f' : ℝ → E} {a b B : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hB : ∀ t ∈ Ico a b, ‖f' t‖ ≤ B) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ≤ B * |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · have := this ht hs (le_of_not_ge hst)
    rwa [norm_sub_rev, abs_sub_comm] at this
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f) (f' := f') (C := B)
    (a := s) (b := t) (hc.mono (Icc_subset_Icc hs.1 ht.2))
    (fun x hx => hd x ⟨hs.1.trans hx.1, hx.2.trans_le ht.2⟩)
    (fun x hx => hB x ⟨hs.1.trans hx.1, hx.2.trans_le ht.2⟩) t ⟨hst, le_rfl⟩
  rwa [abs_of_nonneg (sub_nonneg.2 hst)]

namespace IsC11

variable {f f' : ℝ → E} {a b p₁ p₂ : ℝ}

/-- Mean value bound for a `C^{1,1}` curve. -/
private theorem norm_sub_le (hf : IsC11 f f' a b p₁ p₂) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ≤ p₁ * |t - s| :=
  norm_sub_le_of_right_deriv hf.cont hf.deriv (fun t ht' => hf.bound t ⟨ht'.1, ht'.2.le⟩) hs ht

/-- Restriction of a `C^{1,1}` curve to a subinterval. -/
private theorem mono (hf : IsC11 f f' a b p₁ p₂) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    IsC11 f f' a' b' p₁ p₂ where
  cont := hf.cont.mono (Icc_subset_Icc ha hb)
  deriv t ht := hf.deriv t ⟨ha.trans ht.1, ht.2.trans_le hb⟩
  bound t ht := hf.bound t ⟨ha.trans ht.1, ht.2.trans hb⟩
  lip s hs t ht := hf.lip s ⟨ha.trans hs.1, hs.2.trans hb⟩ t ⟨ha.trans ht.1, ht.2.trans hb⟩
  nn₁ := hf.nn₁
  nn₂ := hf.nn₂

/-- Mean value bound for the first-order Taylor remainder. -/
private theorem norm_sub_sub_smul_le (hf : IsC11 f f' a b p₁ p₂) {s u c w : ℝ} (hs : s ∈ Icc a b)
    (hu : u ∈ Icc a b) (hsu : s ≤ u) (hw : ∀ x ∈ Icc s u, ‖f' x - f' c‖ ≤ w) :
    ‖f u - f s - (u - s) • f' c‖ ≤ w * (u - s) := by
  have hder : ∀ x ∈ Ico s u,
      HasDerivWithinAt (fun x => f x - (x - s) • f' c) (f' x - f' c) (Ici x) x := by
    intro x hx
    have h1 := hf.deriv x ⟨hs.1.trans hx.1, hx.2.trans_le hu.2⟩
    have h2 : HasDerivWithinAt (fun x : ℝ => (x - s) • f' c) ((1 : ℝ) • f' c) (Ici x) x :=
      ((hasDerivWithinAt_id x _).sub_const s).smul_const (f' c)
    have h3 := h1.fun_sub h2
    rwa [one_smul] at h3
  have hc : ContinuousOn (fun x => f x - (x - s) • f' c) (Icc s u) :=
    (hf.cont.mono (Icc_subset_Icc hs.1 hu.2)).sub (by fun_prop)
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hc hder
    (fun x hx => hw x ⟨hx.1, hx.2.le⟩) u ⟨hsu, le_rfl⟩
  have h2 : f u - f s - (u - s) • f' c = (f u - (u - s) • f' c) - (f s - (s - s) • f' c) := by
    rw [sub_self, zero_smul]; abel
  rwa [h2]

/-- First-order Taylor expansion of a `C^{1,1}` curve around an arbitrary point of the interval. -/
private theorem taylor (hf : IsC11 f f' a b p₁ p₂) {c t : ℝ} (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f c - (t - c) • f' c‖ ≤ p₂ * (t - c) ^ 2 := by
  have hp := hf.nn₂
  rcases le_total c t with h | h
  · have := hf.norm_sub_sub_smul_le (c := c) (w := p₂ * (t - c)) hc ht h (fun x hx => by
      refine (hf.lip c hc x ⟨hc.1.trans hx.1, hx.2.trans ht.2⟩).trans ?_
      rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) hp)
    calc _ ≤ _ := this
      _ = _ := by ring
  · have := hf.norm_sub_sub_smul_le (c := c) (w := p₂ * (c - t)) ht hc h (fun x hx => by
      refine (hf.lip c hc x ⟨ht.1.trans hx.1, hx.2.trans hc.2⟩).trans ?_
      rw [abs_of_nonpos (sub_nonpos.2 hx.2)]
      exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) hp)
    have h2 : f t - f c - (t - c) • f' c = -(f c - f t - (c - t) • f' c) := by
      rw [show t - c = -(c - t) by ring, neg_smul]; abel
    rw [h2, norm_neg]
    calc _ ≤ _ := this
      _ = _ := by ring

end IsC11

end Calculus

/-! ### Equal-rank projectors -/

section ProjectorGap

/-- Two orthogonal projectors of the same rank: the gap is controlled by one of the two "sines",
`‖U Uᵀ - W Wᵀ‖ ≤ 2 ‖(I - W Wᵀ) U Uᵀ‖` in the Frobenius norm. -/
private theorem norm_proj_sub_le {U W : Matrix m r ℝ} (hU : Uᵀ * U = 1) (hW : Wᵀ * W = 1) :
    ‖U * Uᵀ - W * Wᵀ‖ ≤ 2 * ‖(1 - W * Wᵀ) * (U * Uᵀ)‖ := by
  set P := U * Uᵀ with hP
  set R := W * Wᵀ with hR
  have hPs : Pᵀ = P := by rw [hP, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hRs : Rᵀ = R := by rw [hR, Matrix.transpose_mul, Matrix.transpose_transpose]
  -- `‖P‖ = ‖R‖`
  have hsq : ∀ {Z : Matrix m r ℝ}, Zᵀ * Z = 1 → ‖Z * Zᵀ‖ ^ 2 = Matrix.trace (1 : Matrix r r ℝ) := by
    intro Z hZ
    rw [Frobenius.norm_mul_transpose_of_orthonormal hZ, ← real_inner_self_eq_norm_sq,
      Frobenius.inner_eq_trace, hZ]
  have h1 := (isOrthProj_leftProj (n := m) hW).norm_sq_add P
  have h2 := (isOrthProj_leftProj (n := m) hU).norm_sq_add R
  simp only [leftProj_apply] at h1 h2
  rw [← hP] at h2
  rw [← hR] at h1
  have h3 : ‖R * P‖ = ‖P * R‖ := by
    rw [← Frobenius.norm_transpose (R * P), Matrix.transpose_mul, hPs, hRs]
  have h4 : ‖P‖ ^ 2 = ‖R‖ ^ 2 := by rw [hP, hR, hsq hU, hsq hW]
  have h5 : ‖R - P * R‖ = ‖P - R * P‖ := by
    have : ‖R - P * R‖ ^ 2 = ‖P - R * P‖ ^ 2 := by rw [h3] at h1; linarith
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have h6 : (1 - R) * P = P - R * P := by rw [Matrix.sub_mul, Matrix.one_mul]
  have h7 : P - R = (P - R * P) - (R - P * R)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul P R, hPs, hRs]; abel
  rw [h6, h7]
  calc _ ≤ ‖P - R * P‖ + ‖(R - P * R)ᵀ‖ := norm_sub_le _ _
    _ = _ := by rw [Frobenius.norm_transpose, h5]; ring

omit [DecidableEq m] [DecidableEq n] in
/-- If `R` almost captures a matrix with invertible core, it almost captures its left basis. -/
private theorem norm_compl_proj_le {κ : ℝ} {U : Matrix m r ℝ} {S G : Matrix r r ℝ}
    {V : Matrix n r ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hSG : S * G = 1) (hκ : ‖G‖ ≤ κ) (R : Matrix m m ℝ) :
    ‖R * (U * Uᵀ)‖ ≤ κ * ‖R * (U * S * Vᵀ)‖ := by
  have h : U = (U * S * Vᵀ) * V * G := by
    calc U = U * (S * G) := by rw [hSG, Matrix.mul_one]
      _ = U * S * (Vᵀ * V) * G := by rw [hV, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have h2 : R * (U * Uᵀ) = (R * U) * Uᵀ := by rw [Matrix.mul_assoc]
  rw [h2, Frobenius.norm_mul_transpose_of_orthonormal hU]
  have h3 : R * U = R * (U * S * Vᵀ) * V * G := by
    conv_lhs => rw [h]
    simp only [Matrix.mul_assoc]
  rw [h3, mul_comm]
  refine (Frobenius.norm_mul_le _ _).trans ?_
  exact mul_le_mul (norm_mul_le_of_orthonormal hV _) hκ (norm_nonneg _) (norm_nonneg _)

omit [DecidableEq n] in
/-- Bootstrap, right version: if `X R = X` and `R` is `1/2`-close to `Z Zᵀ`, then `X` is controlled
by `X Z Zᵀ`. -/
private theorem norm_le_two_mul_of_right {X : Matrix l n ℝ} {R : Matrix n n ℝ} {Z : Matrix n r ℝ}
    (hZ : Zᵀ * Z = 1) (hX : X * R = X) (hR : ‖R - Z * Zᵀ‖ ≤ 1 / 2) :
    ‖X‖ ≤ 2 * ‖X * (Z * Zᵀ)‖ := by
  classical
  have hZZ : (Z * Zᵀ) * (1 - Z * Zᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, hZ,
      Matrix.one_mul, sub_self]
  have h1 : X * (1 - Z * Zᵀ) = X * (R - Z * Zᵀ) * (1 - Z * Zᵀ) := by
    have h : X * (R - Z * Zᵀ) * (1 - Z * Zᵀ) =
        (X * R) * (1 - Z * Zᵀ) - X * ((Z * Zᵀ) * (1 - Z * Zᵀ)) := by
      rw [Matrix.mul_sub X, Matrix.sub_mul, Matrix.mul_assoc X (Z * Zᵀ)]
    rw [h, hZZ, Matrix.mul_zero, sub_zero, hX]
  have h2 : ‖X * (1 - Z * Zᵀ)‖ ≤ ‖X‖ * (1 / 2) := by
    rw [h1]
    refine (norm_mul_compl_le hZ _).trans ((Frobenius.norm_mul_le _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  have h3 : X = X * (Z * Zᵀ) + X * (1 - Z * Zᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  have h4 : ‖X‖ ≤ ‖X * (Z * Zᵀ)‖ + ‖X * (1 - Z * Zᵀ)‖ := by
    conv_lhs => rw [h3]
    exact norm_add_le _ _
  linarith

omit [DecidableEq m] in
/-- Bootstrap, left version: if `R X = X` and `R` is `1/2`-close to `Z Zᵀ`, then `X` is controlled
by `Z Zᵀ X`. -/
private theorem norm_le_two_mul_of_left {X : Matrix m l ℝ} {R : Matrix m m ℝ} {Z : Matrix m r ℝ}
    (hZ : Zᵀ * Z = 1) (hX : R * X = X) (hR : ‖R - Z * Zᵀ‖ ≤ 1 / 2) :
    ‖X‖ ≤ 2 * ‖Z * Zᵀ * X‖ := by
  have hs : (Z * Zᵀ)ᵀ = Z * Zᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h := norm_le_two_mul_of_right (X := Xᵀ) (R := Rᵀ) hZ
    (by rw [← Matrix.transpose_mul, hX])
    (by
      have : Rᵀ - Z * Zᵀ = (R - Z * Zᵀ)ᵀ := by rw [Matrix.transpose_sub, hs]
      rw [this, Frobenius.norm_transpose]
      exact hR)
  have h2 : Xᵀ * (Z * Zᵀ) = (Z * Zᵀ * X)ᵀ := by rw [Matrix.transpose_mul, hs]
  rwa [h2, Frobenius.norm_transpose, Frobenius.norm_transpose] at h

end ProjectorGap

/-! ### The exact solution of the DLRA equation -/

section Exact

/-- The right-hand side `(I - U Uᵀ) Ȧ V S⁻¹` of the first equation of (5) of arXiv 1301.1058. -/
noncomputable def factorRhs (dA : ℝ → Matrix m n ℝ) (U : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ)
    (V : ℝ → Matrix n r ℝ) (t : ℝ) : Matrix m r ℝ :=
  (1 - U t * (U t)ᵀ) * dA t * V t * (S t)⁻¹

/-- The derivative `U̇ Uᵀ + U U̇ᵀ` of the projector `U Uᵀ` along a solution of (5) of
arXiv 1301.1058. -/
noncomputable def projRhs (dA : ℝ → Matrix m n ℝ) (U : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ)
    (V : ℝ → Matrix n r ℝ) (t : ℝ) : Matrix m m ℝ :=
  factorRhs dA U S V t * (U t)ᵀ + U t * (factorRhs dA U S V t)ᵀ

/-- The solution `Y(t) = U(t) S(t) V(t)ᵀ ∈ M_r` of the dynamical low-rank equation (6)
`Ẏ = P(Y) Ȧ` of arXiv 1301.1058 on `[a, b]`, written through the gauge-fixed factors, i.e. the
solution of the system (5), with `‖S(t)⁻¹‖ ≤ κ`.  That `Y` then solves (6) is
`factorODE_solution_isDLRA`, and `IsFactorSolution.hasDerivWithinAt_Y` below.  The derivatives are
right derivatives, as in `ODESolution`.  The constant `κ` is the (curvature) constant on which the
constants of the second-order results depend: these results cover the case of a well-conditioned
`S`, while the paper's §3.3–3.4 state second order without any condition. -/
structure IsFactorSolution (dA : ℝ → Matrix m n ℝ) (κ a b : ℝ) (U : ℝ → Matrix m r ℝ)
    (S : ℝ → Matrix r r ℝ) (V : ℝ → Matrix n r ℝ) : Prop where
  solU : ODESolution (fun t X => (1 - X * Xᵀ) * dA t * V t * (S t)⁻¹) U a b
  solS : ODESolution (fun t _ => (U t)ᵀ * dA t * V t) S a b
  solV : ODESolution (fun t X => (1 - X * Xᵀ) * (dA t)ᵀ * U t * ((S t)⁻¹)ᵀ) V a b
  orthU : ∀ t ∈ Icc a b, (U t)ᵀ * U t = 1
  orthV : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1
  det : ∀ t ∈ Icc a b, IsUnit (S t).det
  core : ∀ t ∈ Icc a b, ‖(S t)⁻¹‖ ≤ κ

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- Transposition preserves `IsC11`. -/
private theorem IsC11.transpose {A dA : ℝ → Matrix m n ℝ} {a b a₁ a₂ : ℝ}
    (hA : IsC11 A dA a b a₁ a₂) :
    IsC11 (fun t => (A t)ᵀ) (fun t => (dA t)ᵀ) a b a₁ a₂ where
  cont := GaugeODE.continuousOn_transpose hA.cont
  deriv t ht := Frobenius.hasDerivWithinAt_transpose (hA.deriv t ht)
  bound t ht := by rw [Frobenius.norm_transpose]; exact hA.bound t ht
  lip s hs t ht := by
    rw [← Matrix.transpose_sub, Frobenius.norm_transpose]; exact hA.lip s hs t ht
  nn₁ := hA.nn₁
  nn₂ := hA.nn₂

namespace IsFactorSolution

variable {dA A : ℝ → Matrix m n ℝ} {κ a b a₁ a₂ : ℝ} {U : ℝ → Matrix m r ℝ}
  {S : ℝ → Matrix r r ℝ} {V : ℝ → Matrix n r ℝ}

/-- Restriction of a solution of (5) to a subinterval. -/
private theorem mono (h : IsFactorSolution dA κ a b U S V) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    IsFactorSolution dA κ a' b' U S V where
  solU := h.solU.mono ha hb
  solS := h.solS.mono ha hb
  solV := h.solV.mono ha hb
  orthU t ht := h.orthU t ⟨ha.trans ht.1, ht.2.trans hb⟩
  orthV t ht := h.orthV t ⟨ha.trans ht.1, ht.2.trans hb⟩
  det t ht := h.det t ⟨ha.trans ht.1, ht.2.trans hb⟩
  core t ht := h.core t ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- The system (5) is invariant under transposition (`A ↦ Aᵀ`, `U ↔ V`, `S ↦ Sᵀ`). -/
private theorem transpose (h : IsFactorSolution dA κ a b U S V) :
    IsFactorSolution (fun t => (dA t)ᵀ) κ a b V (fun t => (S t)ᵀ) U where
  solU := ⟨h.solV.cont, fun t ht => by
    simpa only [Matrix.transpose_nonsing_inv] using h.solV.deriv t ht⟩
  solS := ⟨GaugeODE.continuousOn_transpose h.solS.cont, fun t ht => by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using
      Frobenius.hasDerivWithinAt_transpose (h.solS.deriv t ht)⟩
  solV := ⟨h.solU.cont, fun t ht => by
    simpa only [Matrix.transpose_transpose, Matrix.transpose_nonsing_inv] using
      h.solU.deriv t ht⟩
  orthU := h.orthV
  orthV := h.orthU
  det t ht := by rw [Matrix.det_transpose]; exact h.det t ht
  core t ht := by
    rw [← Matrix.transpose_nonsing_inv, Frobenius.norm_transpose]; exact h.core t ht

/-- Bound of the right-hand side of the first equation of (5). -/
private theorem norm_factorRhs_le (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂)
    {t : ℝ} (ht : t ∈ Icc a b) : ‖factorRhs dA U S V t‖ ≤ a₁ * κ := by
  have h1 : ‖(1 - U t * (U t)ᵀ) * dA t * V t‖ ≤ a₁ :=
    (norm_mul_le_of_orthonormal (h.orthV t ht) _).trans
      ((norm_compl_mul_le (h.orthU t ht) _).trans (hA.bound t ht))
  exact (Frobenius.norm_mul_le _ _).trans
    (mul_le_mul h1 (h.core t ht) (norm_nonneg _) hA.nn₁)

/-- The factor `U` of a solution of (5) is Lipschitz. -/
private theorem lip_U (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : ‖U t - U s‖ ≤ a₁ * κ * |t - s| :=
  norm_sub_le_of_right_deriv h.solU.cont h.solU.deriv
    (fun _ hx => h.norm_factorRhs_le hA ⟨hx.1, hx.2.le⟩) hs ht

/-- The factor `V` of a solution of (5) is Lipschitz. -/
private theorem lip_V (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : ‖V t - V s‖ ≤ a₁ * κ * |t - s| :=
  h.transpose.lip_U hA.transpose hs ht

/-- The inverse of the core `S` of a solution of (5) is Lipschitz. -/
private theorem lip_inv (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂)
    (hκ : 0 ≤ κ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖(S t)⁻¹ - (S s)⁻¹‖ ≤ κ ^ 2 * a₁ * |t - s| := by
  have hS : ‖S t - S s‖ ≤ a₁ * |t - s| :=
    norm_sub_le_of_right_deriv h.solS.cont h.solS.deriv (fun x hx => by
      have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
      exact (norm_mul_le_of_orthonormal (h.orthV x hx') _).trans
        ((norm_transpose_mul_le (h.orthU x hx') _).trans (hA.bound x hx'))) hs ht
  have key : (S t)⁻¹ - (S s)⁻¹ = (S t)⁻¹ * (S s - S t) * (S s)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ (h.det t ht), Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (h.det s hs), Matrix.mul_one]
  rw [key]
  have h2 : ‖S s - S t‖ ≤ a₁ * |t - s| := by rwa [norm_sub_rev]
  have hd : 0 ≤ a₁ * |t - s| := mul_nonneg hA.nn₁ (abs_nonneg _)
  calc _ ≤ ‖(S t)⁻¹ * (S s - S t)‖ * ‖(S s)⁻¹‖ := Frobenius.norm_mul_le _ _
    _ ≤ (‖(S t)⁻¹‖ * ‖S s - S t‖) * ‖(S s)⁻¹‖ := by
        gcongr; exact Frobenius.norm_mul_le _ _
    _ ≤ (κ * (a₁ * |t - s|)) * κ := by
        have h3 := h.core t ht
        have h4 := h.core s hs
        gcongr
    _ = _ := by ring

/-- The projector `U Uᵀ` of a solution of (5) is Lipschitz. -/
private theorem lip_proj (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖U t * (U t)ᵀ - U s * (U s)ᵀ‖ ≤ 2 * a₁ * κ * |t - s| := by
  have key : U t * (U t)ᵀ - U s * (U s)ᵀ = U t * (U t - U s)ᵀ + (U t - U s) * (U s)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [key]
  have h1 := h.lip_U hA hs ht
  calc _ ≤ ‖U t * (U t - U s)ᵀ‖ + ‖(U t - U s) * (U s)ᵀ‖ := norm_add_le _ _
    _ = ‖U t - U s‖ + ‖U t - U s‖ := by
        rw [Frobenius.norm_mul_of_orthonormal (h.orthU t ht), Frobenius.norm_transpose,
          Frobenius.norm_mul_transpose_of_orthonormal (h.orthU s hs)]
    _ ≤ _ := by linarith

/-- The right-hand side of the first equation of (5) is Lipschitz along a solution. -/
private theorem lip_factorRhs (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂)
    (hκ : 0 ≤ κ) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖factorRhs dA U S V t - factorRhs dA U S V s‖ ≤ (a₂ * κ + 4 * a₁ ^ 2 * κ ^ 2) * |t - s| := by
  have hd := abs_nonneg (t - s)
  have ha₁ := hA.nn₁
  have ha₂ := hA.nn₂
  have hVt := h.orthV t ht
  have hVs := h.orthV s hs
  have hGt := h.core t ht
  have hGs := h.core s hs
  set G := fun x => (S x)⁻¹ with hG
  have e : ∀ x, factorRhs dA U S V x = (1 - U x * (U x)ᵀ) * (dA x * V x * G x) := by
    intro x; simp only [factorRhs, hG, Matrix.mul_assoc]
  have hΦ : ‖dA t * V t * G t - dA s * V s * G s‖ ≤ (a₂ * κ + 2 * a₁ ^ 2 * κ ^ 2) * |t - s| := by
    have key : dA t * V t * G t - dA s * V s * G s = (dA t - dA s) * V t * G t
        + dA s * (V t - V s) * G t + dA s * V s * (G t - G s) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [key]
    have h1 : ‖(dA t - dA s) * V t * G t‖ ≤ a₂ * |t - s| * κ :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le_of_orthonormal hVt _).trans (hA.lip s hs t ht)) hGt (norm_nonneg _)
        (mul_nonneg ha₂ hd))
    have h2 : ‖dA s * (V t - V s) * G t‖ ≤ a₁ * (a₁ * κ * |t - s|) * κ :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul
        ((Frobenius.norm_mul_le _ _).trans (mul_le_mul (hA.bound s hs) (h.lip_V hA hs ht)
          (norm_nonneg _) ha₁)) hGt (norm_nonneg _) (by positivity))
    have h3 : ‖dA s * V s * (G t - G s)‖ ≤ a₁ * (κ ^ 2 * a₁ * |t - s|) :=
      (Frobenius.norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le_of_orthonormal hVs _).trans (hA.bound s hs)) (h.lip_inv hA hκ hs ht)
        (norm_nonneg _) ha₁)
    calc _ ≤ ‖(dA t - dA s) * V t * G t‖ + ‖dA s * (V t - V s) * G t‖
          + ‖dA s * V s * (G t - G s)‖ := norm_add₃_le
      _ ≤ _ := by nlinarith
  have key : factorRhs dA U S V t - factorRhs dA U S V s =
      (1 - U t * (U t)ᵀ) * (dA t * V t * G t - dA s * V s * G s)
        + (U s * (U s)ᵀ - U t * (U t)ᵀ) * (dA s * V s * G s) := by
    rw [e, e]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
    abel
  rw [key]
  have h1 := norm_compl_mul_le (h.orthU t ht) (dA t * V t * G t - dA s * V s * G s)
  have h2 : ‖(U s * (U s)ᵀ - U t * (U t)ᵀ) * (dA s * V s * G s)‖ ≤
      (2 * a₁ * κ * |t - s|) * (a₁ * κ) := by
    refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
    · rw [norm_sub_rev]; exact h.lip_proj hA hs ht
    · exact (Frobenius.norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le_of_orthonormal hVs _).trans (hA.bound s hs)) hGs (norm_nonneg _) ha₁)
  calc _ ≤ ‖(1 - U t * (U t)ᵀ) * (dA t * V t * G t - dA s * V s * G s)‖
        + ‖(U s * (U s)ᵀ - U t * (U t)ᵀ) * (dA s * V s * G s)‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- The derivative of the projector `U Uᵀ` is Lipschitz along a solution of (5). -/
private theorem lip_projRhs (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂)
    (hκ : 0 ≤ κ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖projRhs dA U S V t - projRhs dA U S V s‖ ≤ (2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2) * |t - s| := by
  have hUt := h.orthU t ht
  have hUs := h.orthU s hs
  have h1 := h.lip_factorRhs hA hκ hs ht
  have h2 := h.lip_U hA hs ht
  have hbt := h.norm_factorRhs_le hA ht
  have hbs := h.norm_factorRhs_le hA hs
  have hκ1 : 0 ≤ a₁ * κ := mul_nonneg hA.nn₁ hκ
  have hd := abs_nonneg (t - s)
  have key : projRhs dA U S V t - projRhs dA U S V s =
      (factorRhs dA U S V t - factorRhs dA U S V s) * (U t)ᵀ
        + factorRhs dA U S V s * (U t - U s)ᵀ + (U t - U s) * (factorRhs dA U S V t)ᵀ
        + U s * (factorRhs dA U S V t - factorRhs dA U S V s)ᵀ := by
    simp only [projRhs, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [key]
  generalize factorRhs dA U S V t = Ut at *
  generalize factorRhs dA U S V s = Us at *
  have h2' : ‖(U t - U s)ᵀ‖ ≤ a₁ * κ * |t - s| := by rw [Frobenius.norm_transpose]; exact h2
  have hbt' : ‖Utᵀ‖ ≤ a₁ * κ := by rw [Frobenius.norm_transpose]; exact hbt
  have h3 : ‖Us * (U t - U s)ᵀ‖ ≤ (a₁ * κ) * (a₁ * κ * |t - s|) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hbs h2' (norm_nonneg _) hκ1)
  have h4 : ‖(U t - U s) * Utᵀ‖ ≤ (a₁ * κ * |t - s|) * (a₁ * κ) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul h2 hbt' (norm_nonneg _) (mul_nonneg hκ1 hd))
  have h5 : ‖(Ut - Us) * (U t)ᵀ‖ = ‖Ut - Us‖ :=
    Frobenius.norm_mul_transpose_of_orthonormal hUt _
  have h6 : ‖U s * (Ut - Us)ᵀ‖ = ‖Ut - Us‖ := by
    rw [Frobenius.norm_mul_of_orthonormal hUs, Frobenius.norm_transpose]
  calc _ ≤ ‖(Ut - Us) * (U t)ᵀ‖ + ‖Us * (U t - U s)ᵀ‖ + ‖(U t - U s) * Utᵀ‖
        + ‖U s * (Ut - Us)ᵀ‖ := norm_add₄_le
    _ ≤ (a₂ * κ + 4 * a₁ ^ 2 * κ ^ 2) * |t - s| + (a₁ * κ) * (a₁ * κ * |t - s|)
        + (a₁ * κ * |t - s|) * (a₁ * κ) + (a₂ * κ + 4 * a₁ ^ 2 * κ ^ 2) * |t - s| := by
        rw [h5, h6]
        gcongr
    _ = _ := by ring

/-- **The projector `U Uᵀ` of the solution of (5) of arXiv 1301.1058 is a `C^{1,1}` curve**, with
constants depending only on the bounds `a₁`, `a₂` of `Ȧ` and on `κ`. -/
theorem isC11_proj (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂) (hκ : 0 ≤ κ) :
    IsC11 (fun t => U t * (U t)ᵀ) (projRhs dA U S V) a b (2 * a₁ * κ)
      (2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2) where
  cont := GaugeODE.continuousOn_mul h.solU.cont (GaugeODE.continuousOn_transpose h.solU.cont)
  deriv t ht := Frobenius.hasDerivWithinAt_mul (h.solU.deriv t ht)
    (Frobenius.hasDerivWithinAt_transpose (h.solU.deriv t ht))
  bound t ht := by
    have hU := h.orthU t ht
    have h1 := h.norm_factorRhs_le hA ht
    calc _ ≤ ‖factorRhs dA U S V t * (U t)ᵀ‖ + ‖U t * (factorRhs dA U S V t)ᵀ‖ := norm_add_le _ _
      _ = ‖factorRhs dA U S V t‖ + ‖factorRhs dA U S V t‖ := by
          rw [Frobenius.norm_mul_transpose_of_orthonormal hU,
            Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_transpose]
      _ ≤ _ := by linarith
  lip s hs t ht := h.lip_projRhs hA hκ hs ht
  nn₁ := by have := hA.nn₁; positivity
  nn₂ := by have := hA.nn₁; have := hA.nn₂; positivity

/-- `isC11_proj` for the right projector `V Vᵀ` of the solution of (5) of arXiv 1301.1058. -/
theorem isC11_proj_right (h : IsFactorSolution dA κ a b U S V) (hA : IsC11 A dA a b a₁ a₂)
    (hκ : 0 ≤ κ) :
    IsC11 (fun t => V t * (V t)ᵀ) (projRhs (fun t => (dA t)ᵀ) V (fun t => (S t)ᵀ) U) a b
      (2 * a₁ * κ) (2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2) :=
  h.transpose.isC11_proj hA.transpose hκ

/-- `Y = U S Vᵀ` solves the DLRA equation (6) of arXiv 1301.1058, with the projector (7). -/
theorem hasDerivWithinAt_Y (h : IsFactorSolution dA κ a b U S V)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * dA t + dA t * (V t * (V t)ᵀ) - U t * (U t)ᵀ * dA t * (V t * (V t)ᵀ))
      (Ici t) t := by
  have h1 : HasDerivWithinAt (fun t => U t * S t * (V t)ᵀ)
      (U t * (U t)ᵀ * dA t + dA t * V t * (V t)ᵀ - U t * (U t)ᵀ * dA t * V t * (V t)ᵀ)
      (Ici t) t := hasDerivWithinAt_factorProduct_of_factorODE (h.det t ⟨ht.1, ht.2.le⟩)
    (h.solU.deriv t ht) (h.solS.deriv t ht) (h.solV.deriv t ht)
  simpa only [Matrix.mul_assoc] using h1

/-- A solution of (5) gives a continuous curve `Y`. -/
private theorem continuousOn_Y (h : IsFactorSolution dA κ a b U S V) :
    ContinuousOn (fun t => U t * S t * (V t)ᵀ) (Icc a b) :=
  GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul h.solU.cont h.solS.cont)
    (GaugeODE.continuousOn_transpose h.solV.cont)

end IsFactorSolution

end Exact

/-! ### The symmetrized scheme (12) -/

section Strang

/-- One step of the **symmetrized splitting scheme (12) of arXiv 1301.1058, §3.3**, for the values
`A₀ = A(t₀)`, `Am = A(t₀ + h/2)`, `A₁ = A(t₀ + h)`:

    K_{1/2} = U₀ S₀ + (A_{1/2} - A₀) V₀,          (U_{1/2}, Ŝ_{1/2}) = QR(K_{1/2}),
    S̃₀ = Ŝ_{1/2} - U_{1/2}ᵀ (A_{1/2} - A₀) V₀,
    L₁ = V₀ S̃₀ᵀ + (A₁ - A₀)ᵀ U_{1/2},             (V₁, Ŝ₁ᵀ) = QR(L₁),
    S̃_{1/2} = Ŝ₁ - U_{1/2}ᵀ (A₁ - A_{1/2}) V₁,
    K₁ = U_{1/2} S̃_{1/2} + (A₁ - A_{1/2}) V₁,     (U₁, S₁) = QR(K₁),

with result `Y₁ = U₁ S₁ V₁ᵀ`.  The factorizations are only required to have orthonormal first
factors.  (`Um`, `Ŝm` stand for `U_{1/2}`, `Ŝ_{1/2}`.) -/
structure IsStrangStep (A₀ Am A₁ : Matrix m n ℝ) (U₀ : Matrix m r ℝ) (S₀ : Matrix r r ℝ)
    (V₀ : Matrix n r ℝ) (Um : Matrix m r ℝ) (Ŝm : Matrix r r ℝ) (V₁ : Matrix n r ℝ)
    (Ŝ₁ : Matrix r r ℝ) (U₁ : Matrix m r ℝ) (S₁ : Matrix r r ℝ) : Prop where
  orthUm : Umᵀ * Um = 1
  qrKm : Um * Ŝm = U₀ * S₀ + (Am - A₀) * V₀
  orthV₁ : V₁ᵀ * V₁ = 1
  qrL : V₁ * Ŝ₁ᵀ = V₀ * (Ŝm - Umᵀ * (Am - A₀) * V₀)ᵀ + (A₁ - A₀)ᵀ * Um
  orthU₁ : U₁ᵀ * U₁ = 1
  qrK : U₁ * S₁ = Um * (Ŝ₁ - Umᵀ * (A₁ - Am) * V₁) + (A₁ - Am) * V₁

namespace IsStrangStep

variable {A₀ Am A₁ : Matrix m n ℝ} {U₀ Um U₁ : Matrix m r ℝ} {S₀ Ŝm Ŝ₁ S₁ : Matrix r r ℝ}
  {V₀ V₁ : Matrix n r ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- The K-substep of (12) in factored form. -/
private theorem left_eq (hs : IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁) :
    Um * (Ŝm * V₀ᵀ) = U₀ * S₀ * V₀ᵀ + (Am - A₀) * (V₀ * V₀ᵀ) := by
  rw [← Matrix.mul_assoc Um, hs.qrKm, Matrix.add_mul, Matrix.mul_assoc (Am - A₀)]

omit [DecidableEq m] [DecidableEq n] in
/-- The result of the L-substep of the scheme (12) of arXiv 1301.1058:
`Ŝ₁ V₁ᵀ = U_{1/2}ᵀ (Y₀ + A₁ - A₀)`. -/
private theorem core_eq (hs : IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁) :
    Ŝ₁ * V₁ᵀ = Umᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) := by
  have hL : Ŝ₁ * V₁ᵀ = (Ŝm - Umᵀ * (Am - A₀) * V₀) * V₀ᵀ + Umᵀ * (A₁ - A₀) := by
    have h := congrArg Matrix.transpose hs.qrL
    simpa only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose] using h
  have h1 : Ŝm * V₀ᵀ = Umᵀ * (U₀ * S₀ * V₀ᵀ + (Am - A₀) * (V₀ * V₀ᵀ)) := by
    rw [← hs.left_eq, ← Matrix.mul_assoc Umᵀ, hs.orthUm, Matrix.one_mul]
  rw [hL, Matrix.sub_mul, h1, Matrix.mul_add Umᵀ (U₀ * S₀ * V₀ᵀ),
    Matrix.mul_add Umᵀ (U₀ * S₀ * V₀ᵀ)]
  simp only [Matrix.mul_assoc]
  abel

omit [DecidableEq m] [DecidableEq n] in
/-- **Closed form of the scheme (12) of arXiv 1301.1058**: with `Pm = U_{1/2} U_{1/2}ᵀ`,
`Q₀ = V₀ V₀ᵀ`, `Q₁ = V₁ V₁ᵀ`,
`Y₁ = Y₀ + (I - Pm) (A_{1/2} - A₀) Q₀ + Pm (A₁ - A₀) + (I - Pm) (A₁ - A_{1/2}) Q₁`. -/
theorem eq_closed [DecidableEq m] (hs : IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁) :
    U₁ * S₁ * V₁ᵀ = U₀ * S₀ * V₀ᵀ + (1 - Um * Umᵀ) * (Am - A₀) * (V₀ * V₀ᵀ)
      + Um * Umᵀ * (A₁ - A₀) + (1 - Um * Umᵀ) * (A₁ - Am) * (V₁ * V₁ᵀ) := by
  have h1 : Um * (Ŝ₁ * V₁ᵀ) = U₀ * S₀ * V₀ᵀ + (1 - Um * Umᵀ) * (Am - A₀) * (V₀ * V₀ᵀ)
      + Um * Umᵀ * (A₁ - A₀) := by
    have hL : Ŝ₁ * V₁ᵀ = (Ŝm - Umᵀ * (Am - A₀) * V₀) * V₀ᵀ + Umᵀ * (A₁ - A₀) := by
      have h := congrArg Matrix.transpose hs.qrL
      simpa only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose] using h
    rw [hL, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, hs.left_eq]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hs.qrK, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc Um Ŝ₁, h1]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  abel

omit [DecidableEq n] in
/-- The first basis captures the K-substep: `(I - Pm) (Y₀ + (A_{1/2} - A₀) Q₀) = 0`. -/
private theorem capture_left (hs : IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁) :
    (1 - Um * Umᵀ) * (U₀ * S₀ * V₀ᵀ + (Am - A₀) * (V₀ * V₀ᵀ)) = 0 := by
  have h : (1 - Um * Umᵀ) * Um = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hs.orthUm, Matrix.mul_one, sub_self]
  rw [← hs.left_eq, ← Matrix.mul_assoc, h, Matrix.zero_mul]

omit [DecidableEq m] in
/-- The new right basis captures the L-substep: `Pm (Y₀ + A₁ - A₀) (I - Q₁) = 0`. -/
private theorem capture_right (hs : IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁) :
    Um * Umᵀ * (U₀ * S₀ * V₀ᵀ + (A₁ - A₀)) * (1 - V₁ * V₁ᵀ) = 0 := by
  have h : V₁ᵀ * (1 - V₁ * V₁ᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hs.orthV₁, Matrix.one_mul, sub_self]
  rw [Matrix.mul_assoc Um, ← hs.core_eq, Matrix.mul_assoc Um, Matrix.mul_assoc Ŝ₁, h,
    Matrix.mul_zero, Matrix.mul_zero]

end IsStrangStep

/-- Pointwise algebra behind `half_estimate`: the derivative of the comparison function is
`O(ρ² + β)`. -/
private theorem half_pointwise {Dt Ds : Matrix m n ℝ} {Pt Ps Pds Pm : Matrix m m ℝ}
    {Qt Qs Qds Qk : Matrix n n ℝ} {a₁ a₂ p₁ p₂ ρ β w τ : ℝ}
    (hPm : ∀ X : Matrix m n ℝ, ‖(1 - Pm) * X‖ ≤ ‖X‖)
    (hQt : ∀ X : Matrix m n ℝ, ‖X * (1 - Qt)‖ ≤ ‖X‖)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hβ0 : 0 ≤ β)
    (hτ : |τ| ≤ ρ) (hD : ‖Dt - Ds‖ ≤ a₂ * ρ) (hDt : ‖Dt‖ ≤ a₁) (hDs : ‖Ds‖ ≤ a₁)
    (hQ1 : ‖Qt - Qs‖ ≤ p₁ * ρ) (hQ2 : ‖Qt - Qs - τ • Qds‖ ≤ p₂ * ρ ^ 2)
    (hP2 : ‖Pt - Ps - τ • Pds‖ ≤ p₂ * ρ ^ 2) (hPd : ‖Pds‖ ≤ p₁) (hβ : ‖Ps - Pm‖ ≤ β)
    (hw : ‖Qk - Qs‖ ≤ w) :
    ‖(1 - Pm) * Dt * Qk + Pm * Dt - (Pt * Dt + Dt * Qt - Pt * Dt * Qt)
        - (1 - Pm) * Ds * (Qk - Qs) + τ • ((1 - Pm) * Ds * Qds + Pds * Ds * (1 - Qs))‖
      ≤ a₂ * ρ * w + a₁ * β + (2 * a₂ * p₁ + 2 * a₁ * p₂ + a₁ * p₁ ^ 2) * ρ ^ 2 := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hτ
  have key : (1 - Pm) * Dt * Qk + Pm * Dt - (Pt * Dt + Dt * Qt - Pt * Dt * Qt)
        - (1 - Pm) * Ds * (Qk - Qs) + τ • ((1 - Pm) * Ds * Qds + Pds * Ds * (1 - Qs))
      = (1 - Pm) * ((Dt - Ds) * (Qk - Qs))
        - (1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds))
        - (Pt - Ps - τ • Pds) * (Dt * (1 - Qt)) - (Ps - Pm) * (Dt * (1 - Qt))
        - τ • (Pds * ((Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs))) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, Matrix.mul_assoc]
    abel
  rw [key]
  have hτD : |τ| * ‖Pds‖ ≤ ρ * p₁ :=
    mul_le_mul hτ hPd (norm_nonneg _) hρ
  have h1 : ‖(1 - Pm) * ((Dt - Ds) * (Qk - Qs))‖ ≤ a₂ * ρ * w :=
    (hPm _).trans ((Frobenius.norm_mul_le _ _).trans
      (mul_le_mul hD hw (norm_nonneg _) (by positivity)))
  have h2a : ‖(Dt - Ds) * (Qt - Qs)‖ ≤ a₂ * ρ * (p₁ * ρ) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hD hQ1 (norm_nonneg _) (by positivity))
  have h2b : ‖Ds * (Qt - Qs - τ • Qds)‖ ≤ a₁ * (p₂ * ρ ^ 2) :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hDs hQ2 (norm_nonneg _) ha₁)
  have h2 : ‖(1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds))‖
      ≤ a₂ * ρ * (p₁ * ρ) + a₁ * (p₂ * ρ ^ 2) :=
    (hPm _).trans ((norm_add_le _ _).trans (add_le_add h2a h2b))
  have hDQ : ‖Dt * (1 - Qt)‖ ≤ a₁ := (hQt _).trans hDt
  have h3 : ‖(Pt - Ps - τ • Pds) * (Dt * (1 - Qt))‖ ≤ p₂ * ρ ^ 2 * a₁ :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hP2 hDQ (norm_nonneg _) (by positivity))
  have h4 : ‖(Ps - Pm) * (Dt * (1 - Qt))‖ ≤ β * a₁ :=
    (Frobenius.norm_mul_le _ _).trans (mul_le_mul hβ hDQ (norm_nonneg _) hβ0)
  have h5a : ‖(Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs)‖ ≤ a₂ * ρ + a₁ * (p₁ * ρ) :=
    (norm_sub_le _ _).trans (add_le_add ((hQt _).trans hD)
      ((Frobenius.norm_mul_le _ _).trans (mul_le_mul hDs hQ1 (norm_nonneg _) ha₁)))
  have h5 : ‖τ • (Pds * ((Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs)))‖
      ≤ ρ * p₁ * (a₂ * ρ + a₁ * (p₁ * ρ)) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ |τ| * (‖Pds‖ * ‖(Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs)‖) := by
          gcongr; exact Frobenius.norm_mul_le _ _
      _ = (|τ| * ‖Pds‖) * ‖(Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs)‖ := by ring
      _ ≤ _ := mul_le_mul hτD h5a (norm_nonneg _) (by positivity)
  have hsum := norm_sub_le ((1 - Pm) * ((Dt - Ds) * (Qk - Qs))
      - (1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds))
      - (Pt - Ps - τ • Pds) * (Dt * (1 - Qt)) - (Ps - Pm) * (Dt * (1 - Qt)))
    (τ • (Pds * ((Dt - Ds) * (1 - Qt) - Ds * (Qt - Qs))))
  have hsum2 := norm_sub_le ((1 - Pm) * ((Dt - Ds) * (Qk - Qs))
      - (1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds))
      - (Pt - Ps - τ • Pds) * (Dt * (1 - Qt))) ((Ps - Pm) * (Dt * (1 - Qt)))
  have hsum3 := norm_sub_le ((1 - Pm) * ((Dt - Ds) * (Qk - Qs))
      - (1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds)))
    ((Pt - Ps - τ • Pds) * (Dt * (1 - Qt)))
  have hsum4 := norm_sub_le ((1 - Pm) * ((Dt - Ds) * (Qk - Qs)))
    ((1 - Pm) * ((Dt - Ds) * (Qt - Qs) + Ds * (Qt - Qs - τ • Qds)))
  have hfin : a₂ * ρ * w + (a₂ * ρ * (p₁ * ρ) + a₁ * (p₂ * ρ ^ 2)) + p₂ * ρ ^ 2 * a₁ + β * a₁
      + ρ * p₁ * (a₂ * ρ + a₁ * (p₁ * ρ))
      = a₂ * ρ * w + a₁ * β + (2 * a₂ * p₁ + 2 * a₁ * p₂ + a₁ * p₁ ^ 2) * ρ ^ 2 := by ring
  linarith

variable {A dA Y : ℝ → Matrix m n ℝ} {P Pd : ℝ → Matrix m m ℝ} {V : ℝ → Matrix n r ℝ}
  {Qd : ℝ → Matrix n n ℝ} {a b a₁ a₂ p₁ p₂ : ℝ}

/-- One half of the quadrature estimate of the scheme (12): on a subinterval `[c, d]` around the
point `ts`, for a fixed right projector `Qk` and a left projector `Pm`, compare the increment of
`(I - Pm) A Qk + Pm A` with that of the exact solution `Y`.  The error is the explicit
polynomial in `ts`-centred time plus `O((ρ² + β) (d - c))`. -/
private theorem half_estimate (hA : IsC11 A dA a b a₁ a₂) (hP : IsC11 P Pd a b p₁ p₂)
    (hQ : IsC11 (fun t => V t * (V t)ᵀ) Qd a b p₁ p₂) (hV : ∀ t ∈ Icc a b, (V t)ᵀ * V t = 1)
    (hYc : ContinuousOn Y (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y
      (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ)) (Ici t) t)
    {Um : Matrix m r ℝ} (hUm : Umᵀ * Um = 1) {c d ts ρ β w : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hts : ts ∈ Icc a b) (hρ : ∀ t ∈ Icc c d, |t - ts| ≤ ρ) (hβ0 : 0 ≤ β)
    (hβ : ‖P ts - Um * Umᵀ‖ ≤ β) {Qk : Matrix n n ℝ} (hw : ‖Qk - V ts * (V ts)ᵀ‖ ≤ w) :
    ‖(1 - Um * Umᵀ) * (A d - A c) * Qk + Um * Umᵀ * (A d - A c) - (Y d - Y c)
        - (d - c) • ((1 - Um * Umᵀ) * dA ts * (Qk - V ts * (V ts)ᵀ))
        + (((d - ts) ^ 2 - (c - ts) ^ 2) / 2) •
          ((1 - Um * Umᵀ) * dA ts * Qd ts + Pd ts * dA ts * (1 - V ts * (V ts)ᵀ))‖
      ≤ (a₂ * ρ * w + a₁ * β + (2 * a₂ * p₁ + 2 * a₁ * p₂ + a₁ * p₁ ^ 2) * ρ ^ 2) * (d - c) := by
  set Pm := Um * Umᵀ with hPm
  set W := (1 - Pm) * dA ts * (Qk - V ts * (V ts)ᵀ) with hW
  set X := (1 - Pm) * dA ts * Qd ts + Pd ts * dA ts * (1 - V ts * (V ts)ᵀ) with hX
  set M := a₂ * ρ * w + a₁ * β + (2 * a₂ * p₁ + 2 * a₁ * p₂ + a₁ * p₁ ^ 2) * ρ ^ 2 with hM
  have hsub : ∀ {t : ℝ}, t ∈ Ico c d → t ∈ Ico a b := fun ht =>
    ⟨hac.trans ht.1, ht.2.trans_le hdb⟩
  have hder : ∀ t ∈ Ico c d, HasDerivWithinAt
      (fun t => (1 - Pm) * A t * Qk + Pm * A t - Y t - (t - ts) • W + ((t - ts) ^ 2 / 2) • X)
      ((1 - Pm) * dA t * Qk + Pm * dA t
        - (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ))
        - W + (t - ts) • X) (Ici t) t := by
    intro t ht
    have h1 := hA.deriv t (hsub ht)
    have h2 := Frobenius.hasDerivWithinAt_mul_const Qk
      (Frobenius.hasDerivWithinAt_const_mul (1 - Pm) h1)
    have h3 := Frobenius.hasDerivWithinAt_const_mul Pm h1
    have h4 : HasDerivWithinAt (fun t : ℝ => (t - ts) • W) ((1 : ℝ) • W) (Ici t) t :=
      ((hasDerivWithinAt_id t _).sub_const ts).smul_const W
    have h5 : HasDerivWithinAt (fun t : ℝ => (t - ts) ^ 2 / 2) (t - ts) (Ici t) t := by
      have h6 : HasDerivAt (fun t : ℝ => (t - ts) ^ 2 / 2) (t - ts) t := by
        have h7 : HasDerivAt (fun t : ℝ => (t - ts) ^ 2) (2 * (t - ts)) t := by
          simpa using ((hasDerivAt_id' t).sub_const ts).fun_pow 2
        convert h7.div_const 2 using 1
        ring
      exact h6.hasDerivWithinAt
    have h8 := h5.smul_const X
    have h9 := (((h2.fun_add h3).fun_sub (hY t (hsub ht))).fun_sub h4).fun_add h8
    rwa [one_smul] at h9
  have hcont : ContinuousOn
      (fun t => (1 - Pm) * A t * Qk + Pm * A t - Y t - (t - ts) • W + ((t - ts) ^ 2 / 2) • X)
      (Icc c d) := by
    have hAc := hA.cont.mono (Icc_subset_Icc hac hdb)
    have hYc' := hYc.mono (Icc_subset_Icc hac hdb)
    have h1 : ContinuousOn (fun t => (1 - Pm) * A t * Qk) (Icc c d) :=
      GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul continuousOn_const hAc)
        continuousOn_const
    have h2 : ContinuousOn (fun t => Pm * A t) (Icc c d) :=
      GaugeODE.continuousOn_mul continuousOn_const hAc
    have h3 : ContinuousOn (fun t : ℝ => (t - ts) • W) (Icc c d) := by fun_prop
    have h4 : ContinuousOn (fun t : ℝ => ((t - ts) ^ 2 / 2) • X) (Icc c d) := by fun_prop
    exact ((h1.add h2).sub hYc').sub h3 |>.add h4
  have hbd : ∀ t ∈ Ico c d, ‖(1 - Pm) * dA t * Qk + Pm * dA t
        - (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ))
        - W + (t - ts) • X‖ ≤ M := by
    intro t ht
    have ht' : t ∈ Icc a b := ⟨hac.trans ht.1, ht.2.le.trans hdb⟩
    have hτ : |t - ts| ≤ ρ := hρ t ⟨ht.1, ht.2.le⟩
    have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans hτ
    have hsq : (t - ts) ^ 2 ≤ ρ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hτ 2
    exact half_pointwise (norm_compl_mul_le hUm) (norm_mul_compl_le (hV t ht')) hA.nn₁ hA.nn₂
      hQ.nn₁ hQ.nn₂ hβ0 hτ
      ((hA.lip ts hts t ht').trans (mul_le_mul_of_nonneg_left hτ hA.nn₂))
      (hA.bound t ht') (hA.bound ts hts)
      ((hQ.norm_sub_le hts ht').trans (mul_le_mul_of_nonneg_left hτ hQ.nn₁))
      ((hQ.taylor hts ht').trans (mul_le_mul_of_nonneg_left hsq hQ.nn₂))
      ((hP.taylor hts ht').trans (mul_le_mul_of_nonneg_left hsq hP.nn₂))
      (hP.bound ts hts) hβ hw
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd d ⟨hcd, le_rfl⟩
  have heq : (1 - Pm) * (A d - A c) * Qk + Pm * (A d - A c) - (Y d - Y c) - (d - c) • W
        + (((d - ts) ^ 2 - (c - ts) ^ 2) / 2) • X
      = ((1 - Pm) * A d * Qk + Pm * A d - Y d - (d - ts) • W + ((d - ts) ^ 2 / 2) • X)
        - ((1 - Pm) * A c * Qk + Pm * A c - Y c - (c - ts) • W + ((c - ts) ^ 2 / 2) • X) := by
    have h1 : (d - c) • W = (d - ts) • W - (c - ts) • W := by
      rw [← sub_smul]; congr 1; ring
    have h2 : (((d - ts) ^ 2 - (c - ts) ^ 2) / 2) • X
        = ((d - ts) ^ 2 / 2) • X - ((c - ts) ^ 2 / 2) • X := by
      rw [← sub_smul]; congr 1; ring
    rw [h1, h2]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [heq]
  exact hmv

omit [DecidableEq n] in
/-- **Second-order quadrature estimate for the scheme (12) of arXiv 1301.1058.**  Let
`t₁ = t₀ + h`, `tm = t₀ + h/2`,
and let `Pm`, `Q₀`, `Q₁` agree up to `β` with the exact projectors `P(tm)`, `Q(t₀)`, `Q(t₁)`.  Then

    ‖(I - Pm) (A(tm) - A(t₀)) Q₀ + Pm (A(t₁) - A(t₀)) + (I - Pm) (A(t₁) - A(tm)) Q₁
        - (Y(t₁) - Y(t₀))‖ ≤ h β (2 a₁ + a₂ h / 2) + h³ (3 a₂ p₁ + 3 a₁ p₂ + a₁ p₁²) / 4.

The `h²` terms of the two half steps cancel; this is the symmetry of the composition. -/
theorem strang_defect {t₀ tm t₁ h β : ℝ} (hh : 0 ≤ h) (htm : tm = t₀ + h / 2) (ht₁ : t₁ = t₀ + h)
    (hA : IsC11 A dA t₀ t₁ a₁ a₂) (hP : IsC11 P Pd t₀ t₁ p₁ p₂)
    (hQ : IsC11 (fun t => V t * (V t)ᵀ) Qd t₀ t₁ p₁ p₂)
    (hV : ∀ t ∈ Icc t₀ t₁, (V t)ᵀ * V t = 1) (hYc : ContinuousOn Y (Icc t₀ t₁))
    (hY : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt Y
      (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ)) (Ici t) t)
    {Um : Matrix m r ℝ} (hUm : Umᵀ * Um = 1) {Q₀ Q₁ : Matrix n n ℝ} (hβ0 : 0 ≤ β)
    (hβ : ‖P tm - Um * Umᵀ‖ ≤ β) (hQ₀ : ‖Q₀ - V t₀ * (V t₀)ᵀ‖ ≤ β)
    (hQ₁ : ‖Q₁ - V t₁ * (V t₁)ᵀ‖ ≤ β) :
    ‖(1 - Um * Umᵀ) * (A tm - A t₀) * Q₀ + Um * Umᵀ * (A t₁ - A t₀)
        + (1 - Um * Umᵀ) * (A t₁ - A tm) * Q₁ - (Y t₁ - Y t₀)‖
      ≤ h * β * (2 * a₁ + a₂ * h / 2) + h ^ 3 * (3 * a₂ * p₁ + 3 * a₁ * p₂ + a₁ * p₁ ^ 2) / 4 := by
  classical
  have ha₁ := hA.nn₁
  have ha₂ := hA.nn₂
  have hp₁ := hQ.nn₁
  have hp₂ := hQ.nn₂
  have h0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, by rw [ht₁]; linarith⟩
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨by rw [ht₁]; linarith, le_rfl⟩
  have hm : tm ∈ Icc t₀ t₁ := ⟨by rw [htm]; linarith, by rw [htm, ht₁]; linarith⟩
  have hd1 : tm - t₀ = h / 2 := by rw [htm]; ring
  have hd2 : t₁ - tm = h / 2 := by rw [htm, ht₁]; ring
  have hd3 : t₀ - tm = -(h / 2) := by rw [htm]; ring
  have habs : |t₀ - tm| = h / 2 := by rw [hd3, abs_neg, abs_of_nonneg (by positivity)]
  have habs' : |t₁ - tm| = h / 2 := by rw [hd2, abs_of_nonneg (by positivity)]
  have hρ₁ : ∀ t ∈ Icc t₀ tm, |t - tm| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hρ₂ : ∀ t ∈ Icc tm t₁, |t - tm| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hw₀ : ‖Q₀ - V tm * (V tm)ᵀ‖ ≤ β + p₁ * (h / 2) := by
    have h2 := hQ.norm_sub_le hm h0
    rw [habs] at h2
    have h3 : Q₀ - V tm * (V tm)ᵀ = (Q₀ - V t₀ * (V t₀)ᵀ) + (V t₀ * (V t₀)ᵀ - V tm * (V tm)ᵀ) := by
      abel
    rw [h3]
    exact (norm_add_le _ _).trans (add_le_add hQ₀ h2)
  have hw₁ : ‖Q₁ - V tm * (V tm)ᵀ‖ ≤ β + p₁ * (h / 2) := by
    have h2 := hQ.norm_sub_le hm h1
    rw [habs'] at h2
    have h3 : Q₁ - V tm * (V tm)ᵀ = (Q₁ - V t₁ * (V t₁)ᵀ) + (V t₁ * (V t₁)ᵀ - V tm * (V tm)ᵀ) := by
      abel
    rw [h3]
    exact (norm_add_le _ _).trans (add_le_add hQ₁ h2)
  have hI₁ := half_estimate hA hP hQ hV hYc hY hUm h0.1 hm.1 hm.2 hm hρ₁ hβ0 hβ hw₀
  have hI₂ := half_estimate hA hP hQ hV hYc hY hUm hm.1 hm.2 h1.2 hm hρ₂ hβ0 hβ hw₁
  rw [hd1, sub_self, hd3] at hI₁
  rw [hd2, sub_self] at hI₂
  obtain ⟨Pm, hPm⟩ : ∃ Pm, Pm = Um * Umᵀ := ⟨_, rfl⟩
  obtain ⟨Qs, hQs⟩ : ∃ Qs, Qs = V tm * (V tm)ᵀ := ⟨_, rfl⟩
  rw [← hPm] at hI₁ hI₂ ⊢
  rw [← hQs] at hI₁ hI₂
  obtain ⟨X, hX⟩ : ∃ X, X = (1 - Pm) * dA tm * Qd tm + Pd tm * dA tm * (1 - Qs) := ⟨_, rfl⟩
  rw [← hX] at hI₁ hI₂
  obtain ⟨M, hM⟩ : ∃ M, M = a₂ * (h / 2) * (β + p₁ * (h / 2)) + a₁ * β
      + (2 * a₂ * p₁ + 2 * a₁ * p₂ + a₁ * p₁ ^ 2) * (h / 2) ^ 2 := ⟨_, rfl⟩
  rw [← hM] at hI₁ hI₂
  -- second difference of `Q`
  have hsum : ‖Q₀ + Q₁ - (2 : ℝ) • Qs‖ ≤ 2 * β + 2 * p₂ * (h / 2) ^ 2 := by
    have ht₀' := hQ.taylor hm h0
    have ht₁' := hQ.taylor hm h1
    rw [hd3, ← hQs, neg_sq] at ht₀'
    rw [hd2, ← hQs] at ht₁'
    have key : Q₀ + Q₁ - (2 : ℝ) • Qs = (Q₀ - V t₀ * (V t₀)ᵀ) + (Q₁ - V t₁ * (V t₁)ᵀ)
        + (V t₀ * (V t₀)ᵀ - Qs - (-(h / 2)) • Qd tm)
        + (V t₁ * (V t₁)ᵀ - Qs - (h / 2) • Qd tm) := by
      rw [neg_smul, two_smul]; abel
    rw [key]
    calc _ ≤ ‖Q₀ - V t₀ * (V t₀)ᵀ‖ + ‖Q₁ - V t₁ * (V t₁)ᵀ‖
          + ‖V t₀ * (V t₀)ᵀ - Qs - (-(h / 2)) • Qd tm‖
          + ‖V t₁ * (V t₁)ᵀ - Qs - (h / 2) • Qd tm‖ := norm_add₄_le
      _ ≤ β + β + p₂ * (h / 2) ^ 2 + p₂ * (h / 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hW : ‖(1 - Pm) * (dA tm * (Q₀ + Q₁ - (2 : ℝ) • Qs))‖ ≤
      a₁ * (2 * β + 2 * p₂ * (h / 2) ^ 2) := by
    rw [hPm]
    exact (norm_compl_mul_le hUm _).trans ((Frobenius.norm_mul_le _ _).trans
      (mul_le_mul (hA.bound tm hm) hsum (norm_nonneg _) ha₁))
  obtain ⟨E₁, hE₁⟩ : ∃ E, E = (1 - Pm) * (A tm - A t₀) * Q₀ + Pm * (A tm - A t₀) - (Y tm - Y t₀)
      - (h / 2) • ((1 - Pm) * dA tm * (Q₀ - Qs)) + ((0 ^ 2 - (-(h / 2)) ^ 2) / 2) • X := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E, E = (1 - Pm) * (A t₁ - A tm) * Q₁ + Pm * (A t₁ - A tm) - (Y t₁ - Y tm)
      - (h / 2) • ((1 - Pm) * dA tm * (Q₁ - Qs)) + (((h / 2) ^ 2 - 0 ^ 2) / 2) • X := ⟨_, rfl⟩
  rw [← hE₁] at hI₁
  rw [← hE₂] at hI₂
  have key : (1 - Pm) * (A tm - A t₀) * Q₀ + Pm * (A t₁ - A t₀)
        + (1 - Pm) * (A t₁ - A tm) * Q₁ - (Y t₁ - Y t₀)
      = E₁ + E₂ + (h / 2) • ((1 - Pm) * (dA tm * (Q₀ + Q₁ - (2 : ℝ) • Qs))) := by
    have hA₃ : Pm * (A t₁ - A t₀) = Pm * (A tm - A t₀) + Pm * (A t₁ - A tm) := by
      rw [← Matrix.mul_add]; congr 1; abel
    have hW₃ : (1 - Pm) * (dA tm * (Q₀ + Q₁ - (2 : ℝ) • Qs))
        = (1 - Pm) * dA tm * (Q₀ - Qs) + (1 - Pm) * dA tm * (Q₁ - Qs) := by
      rw [two_smul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.mul_add]
      congr 2; abel
    rw [hW₃, hA₃, hE₁, hE₂]
    module
  rw [key]
  have hscal : ‖(h / 2) • ((1 - Pm) * (dA tm * (Q₀ + Q₁ - (2 : ℝ) • Qs)))‖ ≤
      h / 2 * (a₁ * (2 * β + 2 * p₂ * (h / 2) ^ 2)) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  calc _ ≤ ‖E₁‖ + ‖E₂‖ + ‖(h / 2) • ((1 - Pm) * (dA tm * (Q₀ + Q₁ - (2 : ℝ) • Qs)))‖ :=
        norm_add₃_le
    _ ≤ M * (h / 2) + M * (h / 2) + h / 2 * (a₁ * (2 * β + 2 * p₂ * (h / 2) ^ 2)) := by gcongr
    _ = _ := by rw [hM]; ring

/-! ### One step of the scheme (12) from a perturbed start with perturbed data -/

omit [DecidableEq m] [DecidableEq n] in
/-- Gap of two left projectors, one of them from a factorization with invertible core. -/
private theorem left_gap [DecidableEq m] {κ : ℝ} {U W : Matrix m r ℝ} {S G : Matrix r r ℝ}
    {V₁ : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : V₁ᵀ * V₁ = 1) (hSG : S * G = 1) (hκ : ‖G‖ ≤ κ)
    (hW : Wᵀ * W = 1) :
    ‖U * Uᵀ - W * Wᵀ‖ ≤ 2 * κ * ‖(1 - W * Wᵀ) * (U * S * V₁ᵀ)‖ := by
  have h := norm_compl_proj_le hU hV hSG hκ (1 - W * Wᵀ)
  have h2 := norm_proj_sub_le hU hW
  linarith

omit [DecidableEq m] [DecidableEq n] in
/-- Gap of two right projectors, one of them from a factorization with invertible core. -/
private theorem right_gap [DecidableEq n] {κ : ℝ} {U₁ : Matrix m r ℝ} {S G : Matrix r r ℝ}
    {Z : Matrix n r ℝ} {V₁ : Matrix n r ℝ} (hU : U₁ᵀ * U₁ = 1) (hV : V₁ᵀ * V₁ = 1)
    (hGS : G * S = 1) (hκ : ‖G‖ ≤ κ) (hZ : Zᵀ * Z = 1) :
    ‖V₁ * V₁ᵀ - Z * Zᵀ‖ ≤ 2 * κ * ‖(U₁ * S * V₁ᵀ) * (1 - Z * Zᵀ)‖ := by
  have hSG' : Sᵀ * Gᵀ = 1 := by rw [← Matrix.transpose_mul, hGS, Matrix.transpose_one]
  have hκ' : ‖Gᵀ‖ ≤ κ := by rw [Frobenius.norm_transpose]; exact hκ
  have h := left_gap (n := m) hV hU hSG' hκ' hZ
  have h2 : (1 - Z * Zᵀ) * (V₁ * Sᵀ * U₁ᵀ) = ((U₁ * S * V₁ᵀ) * (1 - Z * Zᵀ))ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rwa [h2, Frobenius.norm_transpose] at h

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- `U S Vᵀ` is fixed by `V Vᵀ` from the right. -/
private theorem mul_proj_eq {U₁ : Matrix m r ℝ} {S : Matrix r r ℝ} {V₁ : Matrix n r ℝ}
    (hV : V₁ᵀ * V₁ = 1) : U₁ * S * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S * V₁ᵀ := by
  calc U₁ * S * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S * (V₁ᵀ * V₁) * V₁ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `U S Vᵀ` is fixed by `U Uᵀ` from the left. -/
private theorem proj_mul_eq {U₁ : Matrix m r ℝ} {S : Matrix r r ℝ} {V₁ : Matrix n r ℝ}
    (hU : U₁ᵀ * U₁ = 1) : U₁ * U₁ᵀ * (U₁ * S * V₁ᵀ) = U₁ * S * V₁ᵀ := by
  calc U₁ * U₁ᵀ * (U₁ * S * V₁ᵀ) = U₁ * (U₁ᵀ * U₁) * S * V₁ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

omit [DecidableEq r] in
/-- Mean value bound for the increment of `Y - A`, whose derivative is the normal component
`-(I - P) Ȧ (I - Q)`, multiplied by constant matrices. -/
private theorem norm_increment_le {l' : Type*} [Fintype l'] (hA : IsC11 A dA a b a₁ a₂)
    (hYc : ContinuousOn Y (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y
      (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ)) (Ici t) t)
    {L : Matrix l m ℝ} {R : Matrix n l' ℝ} {c d w : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hw : ∀ t ∈ Ico c d, ‖L * ((1 - P t) * dA t * (1 - V t * (V t)ᵀ)) * R‖ ≤ w) :
    ‖L * ((Y d - A d) - (Y c - A c)) * R‖ ≤ w * (d - c) := by
  have hN : ∀ t, P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ) - dA t
      = -((1 - P t) * dA t * (1 - V t * (V t)ᵀ)) := by
    intro t
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have hder : ∀ t ∈ Ico c d, HasDerivWithinAt (fun t => L * (Y t - A t) * R)
      (L * (-((1 - P t) * dA t * (1 - V t * (V t)ᵀ))) * R) (Ici t) t := by
    intro t ht
    have ht' : t ∈ Ico a b := ⟨hac.trans ht.1, ht.2.trans_le hdb⟩
    have h1 := (hY t ht').fun_sub (hA.deriv t ht')
    rw [hN] at h1
    exact Frobenius.hasDerivWithinAt_mul_const R (Frobenius.hasDerivWithinAt_const_mul L h1)
  have hcont : ContinuousOn (fun t => L * (Y t - A t) * R) (Icc c d) :=
    GaugeODE.continuousOn_mul (GaugeODE.continuousOn_mul continuousOn_const
      ((hYc.mono (Icc_subset_Icc hac hdb)).sub (hA.cont.mono (Icc_subset_Icc hac hdb))))
      continuousOn_const
  have hbd : ∀ t ∈ Ico c d, ‖L * (-((1 - P t) * dA t * (1 - V t * (V t)ᵀ))) * R‖ ≤ w := by
    intro t ht
    rw [Matrix.mul_neg, Matrix.neg_mul, norm_neg]
    exact hw t ht
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd d ⟨hcd, le_rfl⟩
  have heq : L * ((Y d - A d) - (Y c - A c)) * R = L * (Y d - A d) * R - L * (Y c - A c) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [heq]

/-- **One step of the scheme (12) against the exact solution, with a perturbed start and perturbed
data** (the core of the second-order results for arXiv 1301.1058, §3.3–3.4).  Let `Y = U S Vᵀ` solve
(5) on `[t₀, t₁]`, `t₁ = t₀ + h`, `tm = t₀ + h/2`, and apply one step of (12) to values
`A₀', Am', A₁'` whose increments are `η`-close to those of `A`, from a factorized
`Y₀ = U₀ S₀ V₀ᵀ` that is `δ`-close to `Y(t₀)`.  If the smallness conditions `hsm₁`, `hsm₂` hold,
then

    ‖Y₁ - Y(t₁)‖ ≤ δ + 4 η + h β (2 a₁ + a₂ h / 2) + h³ (3 a₂ p₁ + 3 a₁ p₂ + a₁ p₁²) / 4,

where `β = 2 κ δ + bP + bQ` bounds the deviation of the projectors of the scheme from the exact
ones.  This is the estimate from which `strang_local_error`, `strang_global_error` and the results
for the explicit method are derived. -/
theorem strang_step_estimate {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {κ t₀ tm t₁ h δ η p₁ p₂
      bP bQ : ℝ} (hκ : 0 ≤ κ) (hh : 0 ≤ h) (htm : tm = t₀ + h / 2) (ht₁ : t₁ = t₀ + h)
    (hp₁ : p₁ = 2 * a₁ * κ) (hp₂ : p₂ = 2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2)
    (hfac : IsFactorSolution dA κ t₀ t₁ U S V) (hA : IsC11 A dA t₀ t₁ a₁ a₂)
    {A₀' Am' A₁' : Matrix m n ℝ} {U₀ Um U₁ : Matrix m r ℝ} {S₀ Ŝm Ŝ₁ S₁ : Matrix r r ℝ}
    {V₀ V₁ : Matrix n r ℝ} (hs : IsStrangStep A₀' Am' A₁' U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hδ : ‖U₀ * S₀ * V₀ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ δ)
    (hη₁ : ‖(Am' - A₀') - (A tm - A t₀)‖ ≤ η) (hη₂ : ‖(A₁' - Am') - (A t₁ - A tm)‖ ≤ η)
    (hbP : 4 * κ * (δ + η + h / 2 * (a₁ * (2 * κ * δ + p₁ * (h / 2)))) ≤ bP)
    (hbQ : 4 * κ * (δ + 2 * η + h * (a₁ * (bP + p₁ * (h / 2)))) ≤ bQ)
    (hsm₁ : 2 * κ * δ + p₁ * (h / 2) ≤ 1 / 2) (hsm₂ : bP + p₁ * (h / 2) ≤ 1 / 2) :
    ‖U₁ * S₁ * V₁ᵀ - U t₁ * S t₁ * (V t₁)ᵀ‖ ≤ δ + 4 * η
      + h * (2 * κ * δ + bP + bQ) * (2 * a₁ + a₂ * h / 2)
      + h ^ 3 * (3 * a₂ * p₁ + 3 * a₁ * p₂ + a₁ * p₁ ^ 2) / 4 := by
  have ha₁ := hA.nn₁
  have hUm := hs.orthUm
  have hV₁ := hs.orthV₁
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη₁
  have hp₁0 : 0 ≤ p₁ := by rw [hp₁]; positivity
  have h0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, by rw [ht₁]; linarith⟩
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨by rw [ht₁]; linarith, le_rfl⟩
  have hm : tm ∈ Icc t₀ t₁ := ⟨by rw [htm]; linarith, by rw [htm, ht₁]; linarith⟩
  have hP : IsC11 (fun t => U t * (U t)ᵀ) (projRhs dA U S V) t₀ t₁ p₁ p₂ := by
    rw [hp₁, hp₂]; exact hfac.isC11_proj hA hκ
  have hQ : IsC11 (fun t => V t * (V t)ᵀ) (projRhs (fun t => (dA t)ᵀ) V (fun t => (S t)ᵀ) U)
      t₀ t₁ p₁ p₂ := by
    rw [hp₁, hp₂]; exact hfac.isC11_proj_right hA hκ
  have hYc := hfac.continuousOn_Y
  have hY := fun t (ht : t ∈ Ico t₀ t₁) => hfac.hasDerivWithinAt_Y ht
  have hG : ∀ t ∈ Icc t₀ t₁, (S t)⁻¹ * S t = 1 := fun t ht =>
    Matrix.nonsing_inv_mul _ (hfac.det t ht)
  have hG' : ∀ t ∈ Icc t₀ t₁, S t * (S t)⁻¹ = 1 := fun t ht =>
    Matrix.mul_nonsing_inv _ (hfac.det t ht)
  have hUo := hfac.orthU
  have hVo := hfac.orthV
  have hcore := hfac.core
  have hclosed := hs.eq_closed
  have hcapL := hs.capture_left
  have hcapR := hs.capture_right
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = U₀ * S₀ * V₀ᵀ := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ Pm, Pm = Um * Umᵀ := ⟨_, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ = V₀ * V₀ᵀ := ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁, Q₁ = V₁ * V₁ᵀ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → Matrix m n ℝ, Y = fun t => U t * S t * (V t)ᵀ := ⟨_, rfl⟩
  have hYt : ∀ t, U t * S t * (V t)ᵀ = Y t := fun t => by rw [hYdef]
  rw [← hYdef] at hYc hY
  simp only [hYt] at hδ ⊢
  rw [← hY₀] at hδ hclosed hcapL hcapR
  rw [← hPm] at hclosed hcapR
  rw [← hPm, ← hQ₀] at hcapL
  rw [← hQ₀, ← hQ₁] at hclosed
  rw [← hQ₁] at hcapR
  have hδ' : ‖Y t₀ - Y₀‖ ≤ δ := by rwa [norm_sub_rev]
  have hY₀Q : Y₀ * Q₀ = Y₀ := by rw [hY₀, hQ₀]; exact mul_proj_eq hV₀
  have hQc : ∀ X : Matrix m n ℝ, ‖X * (1 - Q₀)‖ ≤ ‖X‖ := fun X => by
    rw [hQ₀]; exact norm_mul_compl_le hV₀ X
  have hQp : ∀ X : Matrix m n ℝ, ‖X * Q₀‖ ≤ ‖X‖ := fun X => by
    rw [hQ₀]; exact norm_mul_proj_le hV₀ X
  have hPc : ∀ X : Matrix m n ℝ, ‖(1 - Pm) * X‖ ≤ ‖X‖ := fun X => by
    rw [hPm]; exact norm_compl_mul_le hUm X
  have hY₀Qc : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  -- (A) the old right projector
  have hQ₀gap : ‖V t₀ * (V t₀)ᵀ - Q₀‖ ≤ 2 * κ * δ := by
    have h2 := right_gap (hUo t₀ h0) (hVo t₀ h0) (hG t₀ h0) (hcore t₀ h0) hV₀
    rw [hYt, ← hQ₀] at h2
    have h3 : Y t₀ * (1 - Q₀) = (Y t₀ - Y₀) * (1 - Q₀) := by
      rw [Matrix.sub_mul, hY₀Qc, sub_zero]
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left ((hQc _).trans hδ') (by positivity))
  have hdist : ∀ t ∈ Icc t₀ t₁, |tm - t| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hQw : ∀ t ∈ Icc t₀ tm, ‖V t * (V t)ᵀ - Q₀‖ ≤ 2 * κ * δ + p₁ * (h / 2) := by
    intro t ht
    have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1, ht.2.trans hm.2⟩
    have h2 := hQ.norm_sub_le h0 ht'
    have h3 : |t - t₀| ≤ h / 2 := by
      rw [abs_of_nonneg (sub_nonneg.2 ht.1)]; linarith [ht.2]
    have h4 : V t * (V t)ᵀ - Q₀ = (V t * (V t)ᵀ - V t₀ * (V t₀)ᵀ) + (V t₀ * (V t₀)ᵀ - Q₀) := by abel
    rw [h4]
    refine (norm_add_le _ _).trans ?_
    have h5 : p₁ * |t - t₀| ≤ p₁ * (h / 2) := mul_le_mul_of_nonneg_left h3 hp₁0
    linarith
  -- (B) the intermediate left projector
  have hQmle : ‖V tm * (V tm)ᵀ - V₀ * V₀ᵀ‖ ≤ 1 / 2 := by
    rw [← hQ₀]; exact (hQw tm ⟨hm.1, le_rfl⟩).trans hsm₁
  have hXR : (1 - Pm) * Y tm * (V tm * (V tm)ᵀ) = (1 - Pm) * Y tm := by
    rw [Matrix.mul_assoc, ← hYt tm, mul_proj_eq (hVo tm hm)]
  have hboot := norm_le_two_mul_of_right hV₀ hXR hQmle
  rw [← hQ₀] at hboot
  have hKey : (1 - Pm) * Y tm * Q₀ = (1 - Pm) * (((Y tm - A tm) - (Y t₀ - A t₀)) * Q₀
      + (Y t₀ - Y₀) * Q₀ + ((A tm - A t₀) - (Am' - A₀')) * Q₀) := by
    have e : ((Y tm - A tm) - (Y t₀ - A t₀)) * Q₀ + (Y t₀ - Y₀) * Q₀
        + ((A tm - A t₀) - (Am' - A₀')) * Q₀ = Y tm * Q₀ - (Y₀ + (Am' - A₀') * Q₀) := by
      simp only [Matrix.sub_mul, hY₀Q]
      abel
    rw [e, Matrix.mul_sub, hcapL, sub_zero, Matrix.mul_assoc]
  have hN1 := norm_increment_le (P := fun t => U t * (U t)ᵀ) (L := (1 : Matrix m m ℝ)) (R := Q₀)
    (w := a₁ * (2 * κ * δ + p₁ * (h / 2))) hA hYc hY h0.1 hm.1 hm.2 (fun t ht => by
      have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1, ht.2.le.trans hm.2⟩
      have hq : (1 - V t * (V t)ᵀ) * (V t * (V t)ᵀ) = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (V t)ᵀ,
          hVo t ht', Matrix.one_mul, sub_self]
      have h2 : (1 : Matrix m m ℝ) * ((1 - U t * (U t)ᵀ) * dA t * (1 - V t * (V t)ᵀ)) * Q₀ =
          (1 - U t * (U t)ᵀ) * dA t * ((1 - V t * (V t)ᵀ) * (Q₀ - V t * (V t)ᵀ)) := by
        rw [Matrix.mul_sub (1 - V t * (V t)ᵀ) Q₀, hq, sub_zero, Matrix.one_mul, Matrix.mul_assoc]
      simp only [h2]
      refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul
        ((norm_compl_mul_le (hUo t ht') _).trans (hA.bound t ht')) ?_ (norm_nonneg _) ha₁)
      refine (norm_compl_mul_le (hVo t ht') _).trans ?_
      rw [norm_sub_rev]
      exact hQw t ⟨ht.1, ht.2.le⟩)
  rw [Matrix.one_mul] at hN1
  have hd1 : tm - t₀ = h / 2 := by rw [htm]; ring
  rw [hd1] at hN1
  have hβ₁ : ‖(1 - Pm) * Y tm * Q₀‖ ≤ δ + η + h / 2 * (a₁ * (2 * κ * δ + p₁ * (h / 2))) := by
    rw [hKey]
    refine (hPc _).trans (norm_add₃_le.trans ?_)
    have h2 : ‖(Y t₀ - Y₀) * Q₀‖ ≤ δ := (hQp _).trans hδ'
    have h3 : ‖((A tm - A t₀) - (Am' - A₀')) * Q₀‖ ≤ η :=
      (hQp _).trans (by rw [norm_sub_rev]; exact hη₁)
    have h4 : a₁ * (2 * κ * δ + p₁ * (h / 2)) * (h / 2)
        = h / 2 * (a₁ * (2 * κ * δ + p₁ * (h / 2))) := by ring
    linarith
  have hPmgap : ‖U tm * (U tm)ᵀ - Pm‖ ≤ bP := by
    have h2 := left_gap (hUo tm hm) (hVo tm hm) (hG' tm hm) (hcore tm hm) hUm
    rw [hYt, ← hPm] at h2
    refine h2.trans (le_trans ?_ hbP)
    have h3 := hboot.trans (mul_le_mul_of_nonneg_left hβ₁ (by norm_num))
    calc 2 * κ * ‖(1 - Pm) * Y tm‖ ≤ 2 * κ * (2 * (δ + η + h / 2 * (a₁ * (2 * κ * δ
          + p₁ * (h / 2))))) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hPt : ∀ t ∈ Icc t₀ t₁, ‖Pm - U t * (U t)ᵀ‖ ≤ bP + p₁ * (h / 2) := by
    intro t ht
    have h2 := hP.norm_sub_le ht hm
    have h3 : p₁ * |tm - t| ≤ p₁ * (h / 2) := mul_le_mul_of_nonneg_left (hdist t ht) hp₁0
    have h4 : Pm - U t * (U t)ᵀ = -(U tm * (U tm)ᵀ - Pm) + (U tm * (U tm)ᵀ - U t * (U t)ᵀ) := by
      abel
    rw [h4]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith
  -- (C) the new right projector
  have hPmle : ‖U t₁ * (U t₁)ᵀ - Um * Umᵀ‖ ≤ 1 / 2 := by
    rw [← hPm, norm_sub_rev]; exact (hPt t₁ h1).trans hsm₂
  have hXL : U t₁ * (U t₁)ᵀ * (Y t₁ * (1 - Q₁)) = Y t₁ * (1 - Q₁) := by
    rw [← Matrix.mul_assoc, ← hYt t₁, proj_mul_eq (hUo t₁ h1)]
  have hboot2 := norm_le_two_mul_of_left hUm hXL hPmle
  rw [← hPm] at hboot2
  have hN2 := norm_increment_le (P := fun t => U t * (U t)ᵀ) (L := Pm) (R := (1 : Matrix n n ℝ))
    (w := a₁ * (bP + p₁ * (h / 2))) hA hYc hY h0.1 h1.1 h1.2 (fun t ht => by
      have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1, ht.2.le⟩
      have hq : U t * (U t)ᵀ * (1 - U t * (U t)ᵀ) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc (U t)ᵀ,
          hUo t ht', Matrix.one_mul, sub_self]
      have h2 : Pm * ((1 - U t * (U t)ᵀ) * dA t * (1 - V t * (V t)ᵀ)) * (1 : Matrix n n ℝ) =
          (Pm - U t * (U t)ᵀ) * ((1 - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ))) := by
        have h3 : (Pm - U t * (U t)ᵀ) * ((1 - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ)))
            = Pm * ((1 - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ)))
              - (U t * (U t)ᵀ * (1 - U t * (U t)ᵀ)) * (dA t * (1 - V t * (V t)ᵀ)) := by
          rw [Matrix.sub_mul, Matrix.mul_assoc (U t * (U t)ᵀ)]
        rw [h3, hq, Matrix.zero_mul, sub_zero, Matrix.mul_one, Matrix.mul_assoc (1 - U t * (U t)ᵀ)]
      simp only [h2]
      refine (Frobenius.norm_mul_le _ _).trans ?_
      rw [mul_comm]
      refine mul_le_mul ?_ (hPt t ht') (norm_nonneg _) ha₁
      exact (norm_compl_mul_le (hUo t ht') _).trans
        ((norm_mul_compl_le (hVo t ht') _).trans (hA.bound t ht')))
  rw [Matrix.mul_one] at hN2
  have hd2 : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hd2] at hN2
  have hη₃ : ‖(A t₁ - A t₀) - (A₁' - A₀')‖ ≤ 2 * η := by
    have h2 : (A t₁ - A t₀) - (A₁' - A₀') =
        -(((A₁' - Am') - (A t₁ - A tm)) + ((Am' - A₀') - (A tm - A t₀))) := by abel
    rw [h2, norm_neg]
    refine (norm_add_le _ _).trans ?_
    linarith
  have hβ₂ : ‖Pm * (Y t₁ * (1 - Q₁))‖ ≤ δ + 2 * η + h * (a₁ * (bP + p₁ * (h / 2))) := by
    have e : Pm * (Y t₁ * (1 - Q₁)) = Pm * (((Y t₁ - A t₁) - (Y t₀ - A t₀)) + (Y t₀ - Y₀)
        + ((A t₁ - A t₀) - (A₁' - A₀'))) * (1 - Q₁) := by
      have e2 : ((Y t₁ - A t₁) - (Y t₀ - A t₀)) + (Y t₀ - Y₀) + ((A t₁ - A t₀) - (A₁' - A₀'))
          = Y t₁ - (Y₀ + (A₁' - A₀')) := by abel
      rw [e2, Matrix.mul_sub Pm (Y t₁), Matrix.sub_mul, hcapR, sub_zero, Matrix.mul_assoc]
    rw [e, hQ₁]
    refine (norm_mul_compl_le hV₁ _).trans ?_
    rw [Matrix.mul_add, Matrix.mul_add]
    refine norm_add₃_le.trans ?_
    have h2 : ‖Pm * (Y t₀ - Y₀)‖ ≤ δ := by
      rw [hPm]; exact (norm_proj_mul_le hUm _).trans hδ'
    have h3 : ‖Pm * ((A t₁ - A t₀) - (A₁' - A₀'))‖ ≤ 2 * η := by
      rw [hPm]; exact (norm_proj_mul_le hUm _).trans hη₃
    have h4 : a₁ * (bP + p₁ * (h / 2)) * h = h * (a₁ * (bP + p₁ * (h / 2))) := by ring
    linarith
  have hQ₁gap : ‖V t₁ * (V t₁)ᵀ - Q₁‖ ≤ bQ := by
    have h2 := right_gap (hUo t₁ h1) (hVo t₁ h1) (hG t₁ h1) (hcore t₁ h1) hV₁
    rw [hYt, ← hQ₁] at h2
    refine h2.trans (le_trans ?_ hbQ)
    have h3 := hboot2.trans (mul_le_mul_of_nonneg_left hβ₂ (by norm_num))
    calc 2 * κ * ‖Y t₁ * (1 - Q₁)‖ ≤ 2 * κ * (2 * (δ + 2 * η + h * (a₁ * (bP
          + p₁ * (h / 2))))) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  -- (D) quadrature
  have hbP0 : 0 ≤ bP := le_trans (by positivity) hbP
  have hbQ0 : 0 ≤ bQ := le_trans (by positivity) hbQ
  have hκδ : 0 ≤ 2 * κ * δ := by positivity
  have hβ0 : 0 ≤ 2 * κ * δ + bP + bQ := by positivity
  have hdefect := strang_defect (β := 2 * κ * δ + bP + bQ) (Q₀ := Q₀) (Q₁ := Q₁) hh htm ht₁ hA hP hQ
    hVo hYc hY hUm hβ0 (by rw [← hPm]; linarith)
    (by rw [norm_sub_rev]; linarith) (by rw [norm_sub_rev]; linarith)
  rw [← hPm] at hdefect
  have hsplit : U₁ * S₁ * V₁ᵀ - Y t₁ = (Y₀ - Y t₀)
      + ((1 - Pm) * ((Am' - A₀') - (A tm - A t₀)) * Q₀
        + Pm * ((A₁' - A₀') - (A t₁ - A t₀))
        + (1 - Pm) * ((A₁' - Am') - (A t₁ - A tm)) * Q₁)
      + ((1 - Pm) * (A tm - A t₀) * Q₀ + Pm * (A t₁ - A t₀)
        + (1 - Pm) * (A t₁ - A tm) * Q₁ - (Y t₁ - Y t₀)) := by
    rw [hclosed]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hsplit]
  have hQc₁ : ∀ X : Matrix m n ℝ, ‖X * Q₁‖ ≤ ‖X‖ := fun X => by
    rw [hQ₁]; exact norm_mul_proj_le hV₁ X
  have hT : ‖(1 - Pm) * ((Am' - A₀') - (A tm - A t₀)) * Q₀ + Pm * ((A₁' - A₀') - (A t₁ - A t₀))
      + (1 - Pm) * ((A₁' - Am') - (A t₁ - A tm)) * Q₁‖ ≤ 4 * η := by
    refine norm_add₃_le.trans ?_
    have h2 : ‖(1 - Pm) * ((Am' - A₀') - (A tm - A t₀)) * Q₀‖ ≤ η :=
      (hQp _).trans ((hPc _).trans hη₁)
    have h3 : ‖Pm * ((A₁' - A₀') - (A t₁ - A t₀))‖ ≤ 2 * η := by
      rw [hPm]
      refine (norm_proj_mul_le hUm _).trans ?_
      rw [norm_sub_rev]; exact hη₃
    have h4 : ‖(1 - Pm) * ((A₁' - Am') - (A t₁ - A tm)) * Q₁‖ ≤ η :=
      (hQc₁ _).trans ((hPc _).trans hη₂)
    linarith
  have hsum := norm_add₃_le (a := Y₀ - Y t₀)
    (b := (1 - Pm) * ((Am' - A₀') - (A tm - A t₀)) * Q₀ + Pm * ((A₁' - A₀') - (A t₁ - A t₀))
      + (1 - Pm) * ((A₁' - Am') - (A t₁ - A tm)) * Q₁)
    (c := (1 - Pm) * (A tm - A t₀) * Q₀ + Pm * (A t₁ - A t₀)
      + (1 - Pm) * (A t₁ - A tm) * Q₁ - (Y t₁ - Y t₀))
  linarith

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the Lipschitz constant `2 a₁ κ` of the exact
projectors. -/
noncomputable def strP (a₁ κ : ℝ) : ℝ := 2 * a₁ * κ

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the Lipschitz constant
`2 a₂ κ + 10 a₁² κ²` of the derivative of the exact projectors. -/
noncomputable def strQ (a₁ a₂ κ : ℝ) : ℝ := 2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the constant in the bound of the
intermediate left projector. -/
noncomputable def strKP (a₁ κ : ℝ) : ℝ := 4 * κ * (1 + a₁ * κ + a₁ * strP a₁ κ / 4)

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the constant in the bound of the new right
projector. -/
noncomputable def strKQ (a₁ κ : ℝ) : ℝ := 4 * κ * (2 + a₁ * strKP a₁ κ + a₁ * strP a₁ κ / 2)

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the stability constant of the scheme
(12). -/
noncomputable def strK (a₁ a₂ κ : ℝ) : ℝ :=
  (2 * κ + strKP a₁ κ + strKQ a₁ κ) * (2 * a₁ + a₂ / 2)

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the constant of the `h³` term. -/
noncomputable def strC (a₁ a₂ κ : ℝ) : ℝ :=
  (3 * a₂ * strP a₁ κ + 3 * a₁ * strQ a₁ a₂ κ + a₁ * strP a₁ κ ^ 2) / 4

/-- Second-order results for arXiv 1301.1058, §3.3–3.4: the smallness threshold for step size,
perturbation of the start and of the data. -/
noncomputable def strS (a₁ κ : ℝ) : ℝ := 1 / (8 * (1 + 2 * κ + strKP a₁ κ + strP a₁ κ))

/-- `strang_step_estimate` (scheme (12) of arXiv 1301.1058) with explicit constants: if `h`, `δ`,
`η` are at most `strS a₁ κ`, then

    ‖Y₁ - Y(t₁)‖ ≤ (1 + K h) δ + (4 + K h) η + (K + C) h³

with `K = strK a₁ a₂ κ`, `C = strC a₁ a₂ κ`. -/
theorem strang_step_bound {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {κ t₀ tm t₁ h δ η : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (htm : tm = t₀ + h / 2) (ht₁ : t₁ = t₀ + h)
    (hfac : IsFactorSolution dA κ t₀ t₁ U S V) (hA : IsC11 A dA t₀ t₁ a₁ a₂)
    {A₀' Am' A₁' : Matrix m n ℝ} {U₀ Um U₁ : Matrix m r ℝ} {S₀ Ŝm Ŝ₁ S₁ : Matrix r r ℝ}
    {V₀ V₁ : Matrix n r ℝ} (hs : IsStrangStep A₀' Am' A₁' U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hδ : ‖U₀ * S₀ * V₀ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ δ)
    (hη₁ : ‖(Am' - A₀') - (A tm - A t₀)‖ ≤ η) (hη₂ : ‖(A₁' - Am') - (A t₁ - A tm)‖ ≤ η)
    (hhs : h ≤ strS a₁ κ) (hδs : δ ≤ strS a₁ κ) (hηs : η ≤ strS a₁ κ) :
    ‖U₁ * S₁ * V₁ᵀ - U t₁ * S t₁ * (V t₁)ᵀ‖ ≤ (1 + strK a₁ a₂ κ * h) * δ
      + (4 + strK a₁ a₂ κ * h) * η + (strK a₁ a₂ κ + strC a₁ a₂ κ) * h ^ 3 := by
  have ha₁ := hA.nn₁
  have ha₂ := hA.nn₂
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη₁
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = strP a₁ κ := ⟨_, rfl⟩
  have hp₁' : p₁ = 2 * a₁ * κ := by rw [hp₁, strP]
  have hp₁0 : 0 ≤ p₁ := by rw [hp₁']; positivity
  obtain ⟨KP, hKP⟩ : ∃ KP, KP = strKP a₁ κ := ⟨_, rfl⟩
  have hKP' : KP = 4 * κ * (1 + a₁ * κ + a₁ * p₁ / 4) := by rw [hKP, strKP, hp₁]
  have hKP0 : 0 ≤ KP := by rw [hKP']; positivity
  obtain ⟨KQ, hKQ⟩ : ∃ KQ, KQ = strKQ a₁ κ := ⟨_, rfl⟩
  have hKQ' : KQ = 4 * κ * (2 + a₁ * KP + a₁ * p₁ / 2) := by rw [hKQ, strKQ, hKP, hp₁]
  have hKQ0 : 0 ≤ KQ := by rw [hKQ']; positivity
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 1 + 2 * κ + KP + p₁ := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; linarith
  have hZ0 : 0 < Z := by linarith
  obtain ⟨s, hs'⟩ : ∃ s, s = strS a₁ κ := ⟨_, rfl⟩
  have hsZ : s * Z = 1 / 8 := by
    rw [hs', strS, ← hKP, ← hp₁, ← hZ]; field_simp
  rw [← hs'] at hhs hδs hηs
  have hs0 : 0 ≤ s := by linarith
  have hs18 : s ≤ 1 / 8 := by
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * Z := mul_le_mul_of_nonneg_left hZ1 hs0
      _ = 1 / 8 := hsZ
  have hh1 : h ≤ 1 := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = δ + η + h ^ 2 := ⟨_, rfl⟩
  have hhsq : h ^ 2 ≤ h := pow_le_of_le_one hh hh1 two_ne_zero
  have hsq0 : 0 ≤ h ^ 2 := by positivity
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hδx : δ ≤ x := by rw [hx]; linarith
  have hsqx : h ^ 2 ≤ x := by rw [hx]; linarith
  have hx3 : x ≤ 3 * s := by rw [hx]; linarith
  have hbP : 4 * κ * (δ + η + h / 2 * (a₁ * (2 * κ * δ + p₁ * (h / 2)))) ≤ KP * x := by
    have hKPx : KP * x = 4 * κ * ((1 + a₁ * κ + a₁ * p₁ / 4) * x) := by rw [hKP']; ring
    rw [hKPx]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : h * (a₁ * κ * δ) ≤ a₁ * κ * δ := by
      have h0 : 0 ≤ a₁ * κ * δ := by positivity
      calc _ ≤ 1 * (a₁ * κ * δ) := mul_le_mul_of_nonneg_right hh1 h0
        _ = _ := one_mul _
    have h2 : a₁ * κ * δ ≤ a₁ * κ * x := mul_le_mul_of_nonneg_left hδx (by positivity)
    have h3 : a₁ * p₁ / 4 * h ^ 2 ≤ a₁ * p₁ / 4 * x :=
      mul_le_mul_of_nonneg_left hsqx (by positivity)
    have h4 : δ + η ≤ x := by rw [hx]; linarith
    have h5 : δ + η + h / 2 * (a₁ * (2 * κ * δ + p₁ * (h / 2)))
        = δ + η + h * (a₁ * κ * δ) + a₁ * p₁ / 4 * h ^ 2 := by ring
    have h6 : (1 + a₁ * κ + a₁ * p₁ / 4) * x = x + a₁ * κ * x + a₁ * p₁ / 4 * x := by ring
    rw [h5, h6]
    linarith
  have hbQ : 4 * κ * (δ + 2 * η + h * (a₁ * (KP * x + p₁ * (h / 2)))) ≤ KQ * x := by
    have hKQx : KQ * x = 4 * κ * ((2 + a₁ * KP + a₁ * p₁ / 2) * x) := by rw [hKQ']; ring
    rw [hKQx]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : h * (a₁ * KP * x) ≤ a₁ * KP * x := by
      have h0 : 0 ≤ a₁ * KP * x := by positivity
      calc _ ≤ 1 * (a₁ * KP * x) := mul_le_mul_of_nonneg_right hh1 h0
        _ = _ := one_mul _
    have h3 : a₁ * p₁ / 2 * h ^ 2 ≤ a₁ * p₁ / 2 * x :=
      mul_le_mul_of_nonneg_left hsqx (by positivity)
    have h4 : δ + 2 * η ≤ 2 * x := by rw [hx]; linarith
    have h5 : δ + 2 * η + h * (a₁ * (KP * x + p₁ * (h / 2)))
        = δ + 2 * η + h * (a₁ * KP * x) + a₁ * p₁ / 2 * h ^ 2 := by ring
    have h6 : (2 + a₁ * KP + a₁ * p₁ / 2) * x = 2 * x + a₁ * KP * x + a₁ * p₁ / 2 * x := by ring
    rw [h5, h6]
    linarith
  have hsZ1 : 2 * κ * s ≤ 1 / 8 := by
    rw [← hsZ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hs0
  have hsZ2 : p₁ * s ≤ 1 / 8 := by
    rw [← hsZ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hs0
  have hsZ3 : KP * s ≤ 1 / 8 := by
    rw [← hsZ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hs0
  have hsm₁ : 2 * κ * δ + p₁ * (h / 2) ≤ 1 / 2 := by
    have h1 : 2 * κ * δ ≤ 2 * κ * s := mul_le_mul_of_nonneg_left hδs (by positivity)
    have h2 : p₁ * (h / 2) ≤ p₁ * s :=
      mul_le_mul_of_nonneg_left (by linarith) hp₁0
    linarith
  have hsm₂ : KP * x + p₁ * (h / 2) ≤ 1 / 2 := by
    have h1 : KP * x ≤ KP * (3 * s) := mul_le_mul_of_nonneg_left hx3 hKP0
    have h2 : p₁ * (h / 2) ≤ p₁ * s :=
      mul_le_mul_of_nonneg_left (by linarith) hp₁0
    have h3 : KP * (3 * s) = 3 * (KP * s) := by ring
    linarith
  obtain ⟨p₂, hp₂⟩ : ∃ p₂, p₂ = strQ a₁ a₂ κ := ⟨_, rfl⟩
  have hp₂' : p₂ = 2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2 := by rw [hp₂, strQ]
  have hest := strang_step_estimate (p₂ := p₂) (bP := KP * x) (bQ := KQ * x) hκ hh htm ht₁ hp₁' hp₂'
    hfac hA hs hV₀ hδ hη₁ hη₂ hbP hbQ hsm₁ hsm₂
  have hK : strK a₁ a₂ κ = (2 * κ + KP + KQ) * (2 * a₁ + a₂ / 2) := by rw [strK, hKP, hKQ]
  have hC : strC a₁ a₂ κ = (3 * a₂ * p₁ + 3 * a₁ * p₂ + a₁ * p₁ ^ 2) / 4 := by
    rw [strC, hp₁, hp₂]
  rw [hK, hC]
  have h1 : 2 * κ * δ + KP * x + KQ * x ≤ (2 * κ + KP + KQ) * x := by
    have h0 : 2 * κ * δ ≤ 2 * κ * x := mul_le_mul_of_nonneg_left hδx (by positivity)
    have h00 : (2 * κ + KP + KQ) * x = 2 * κ * x + KP * x + KQ * x := by ring
    linarith
  have h2 : 2 * a₁ + a₂ * h / 2 ≤ 2 * a₁ + a₂ / 2 := by
    have h0 : a₂ * h ≤ a₂ * 1 := mul_le_mul_of_nonneg_left hh1 ha₂
    linarith
  have h3 : h * (2 * κ * δ + KP * x + KQ * x) * (2 * a₁ + a₂ * h / 2)
      ≤ h * ((2 * κ + KP + KQ) * x) * (2 * a₁ + a₂ / 2) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hh) h2 (by positivity) (by positivity)
  have h4 : δ + 4 * η + h * ((2 * κ + KP + KQ) * x) * (2 * a₁ + a₂ / 2)
      + h ^ 3 * (3 * a₂ * p₁ + 3 * a₁ * p₂ + a₁ * p₁ ^ 2) / 4
      = (1 + (2 * κ + KP + KQ) * (2 * a₁ + a₂ / 2) * h) * δ
        + (4 + (2 * κ + KP + KQ) * (2 * a₁ + a₂ / 2) * h) * η
        + ((2 * κ + KP + KQ) * (2 * a₁ + a₂ / 2)
          + (3 * a₂ * p₁ + 3 * a₁ * p₂ + a₁ * p₁ ^ 2) / 4) * h ^ 3 := by
    rw [hx]; ring
  linarith

/-- `strK` is nonnegative. -/
private theorem strK_nonneg {a₁ a₂ κ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ) :
    0 ≤ strK a₁ a₂ κ := by
  simp only [strK, strKP, strKQ, strP]; positivity

/-- `strC` is nonnegative. -/
private theorem strC_nonneg {a₁ a₂ κ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ) :
    0 ≤ strC a₁ a₂ κ := by
  simp only [strC, strQ, strP]; positivity

/-- `strS` is positive. -/
private theorem strS_pos {a₁ κ : ℝ} (ha₁ : 0 ≤ a₁) (hκ : 0 ≤ κ) : 0 < strS a₁ κ := by
  simp only [strS, strKP, strP]; positivity

/-- **The scheme (12) has local error `O(h³)`: "this symmetrized splitting is a second-order
scheme for (6)"** (arXiv 1301.1058, §3.3).  Let `A`
have a derivative bounded by `a₁` and Lipschitz with constant `a₂`, let `Y = U S Vᵀ` be the
solution (5) of the DLRA equation (6) on `[t₀, t₀ + h]` with `‖S(t)⁻¹‖ ≤ κ`, and let one step of
(12), with step size `0 ≤ h ≤ strS a₁ κ`, start at any
factorization `Y(t₀) = U₀ S₀ V₀ᵀ` with `V₀ᵀ V₀ = I`.  Then

    ‖Y₁ - Y(t₀ + h)‖ ≤ (strK a₁ a₂ κ + strC a₁ a₂ κ) h³.

Order `2` is read as in the theory of one-step methods: local error `O(h³)`; for the global error
see `strang_global_error`.  The paper gives no proof (order is claimed from composition theory) and
states no regularity; here `A` is `C^{1,1}`.  The constants are explicit polynomials in `a₁`, `a₂`,
`κ`.  They depend on `κ`, the bound for `‖S⁻¹‖`, so that this result, unlike Theorem 4.2, does not
hold uniformly under over-approximation. -/
theorem strang_local_error {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {κ t₀ h : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hhs : h ≤ strS a₁ κ)
    (hfac : IsFactorSolution dA κ t₀ (t₀ + h) U S V) (hA : IsC11 A dA t₀ (t₀ + h) a₁ a₂)
    {U₀ Um U₁ : Matrix m r ℝ} {S₀ Ŝm Ŝ₁ S₁ : Matrix r r ℝ} {V₀ V₁ : Matrix n r ℝ}
    (hs : IsStrangStep (A t₀) (A (t₀ + h / 2)) (A (t₀ + h)) U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁)
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = U t₀ * S t₀ * (V t₀)ᵀ) :
    ‖U₁ * S₁ * V₁ᵀ - U (t₀ + h) * S (t₀ + h) * (V (t₀ + h))ᵀ‖ ≤
      (strK a₁ a₂ κ + strC a₁ a₂ κ) * h ^ 3 := by
  have hs0 := strS_pos hA.nn₁ hκ
  have h1 := strang_step_bound (δ := 0) (η := 0) hκ hh rfl rfl hfac hA hs hV₀
    (by rw [hY₀, sub_self, norm_zero]) (by simp) (by simp) hhs hs0.le hs0.le
  simpa using h1

/-- Discrete Grönwall inequality with a bootstrap: the recursion only has to hold while `e k ≤ s`,
and the Grönwall bound stays below `s`. -/
private theorem gronwall_bootstrap {e : ℕ → ℝ} {L h g s : ℝ} {N : ℕ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hg : 0 ≤ g)
    (he0 : 0 ≤ e 0) (hrec : ∀ k < N, e k ≤ s → e (k + 1) ≤ Real.exp (L * h) * e k + g)
    (hsmall : Real.exp (L * (N * h)) * (e 0 + N * g) ≤ s) :
    ∀ n ≤ N, e n ≤ Real.exp (L * (n * h)) * (e 0 + n * g) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < N := hk
    have h1 := ih hk'.le
    have hmono : Real.exp (L * (k * h)) * (e 0 + k * g)
        ≤ Real.exp (L * (N * h)) * (e 0 + N * g) := by
      have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk'.le
      refine mul_le_mul (Real.exp_le_exp.2 ?_) ?_ (by positivity) (Real.exp_pos _).le
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkN hh) hL
      · have := mul_le_mul_of_nonneg_right hkN hg
        linarith
    have h2 := hrec k hk' (h1.trans (hmono.trans hsmall))
    have h3 : Real.exp (L * h) * Real.exp (L * (k * h)) = Real.exp (L * ((k + 1 : ℕ) * h)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have h4 : 1 ≤ Real.exp (L * ((k + 1 : ℕ) * h)) := Real.one_le_exp (by positivity)
    have h5 : g ≤ Real.exp (L * ((k + 1 : ℕ) * h)) * g := le_mul_of_one_le_left hg h4
    calc e (k + 1) ≤ Real.exp (L * h) * e k + g := h2
      _ ≤ Real.exp (L * h) * (Real.exp (L * (k * h)) * (e 0 + k * g)) + g := by gcongr
      _ = Real.exp (L * ((k + 1 : ℕ) * h)) * (e 0 + k * g) + g := by rw [← mul_assoc, h3]
      _ ≤ Real.exp (L * ((k + 1 : ℕ) * h)) * (e 0 + k * g)
          + Real.exp (L * ((k + 1 : ℕ) * h)) * g := by linarith
      _ = _ := by push_cast; ring

/-- `strS` is at most one. -/
private theorem strS_le_one {a₁ κ : ℝ} (ha₁ : 0 ≤ a₁) (hκ : 0 ≤ κ) : strS a₁ κ ≤ 1 := by
  have h1 : 0 ≤ strKP a₁ κ := by simp only [strKP, strP]; positivity
  have h2 : 0 ≤ strP a₁ κ := by simp only [strP]; positivity
  rw [strS, div_le_one (by positivity)]
  linarith

/-- The threshold `strS` makes the terms of the smallness conditions at most `1/8`. -/
private theorem strS_mul_le {a₁ κ : ℝ} (ha₁ : 0 ≤ a₁) (hκ : 0 ≤ κ) :
    2 * κ * strS a₁ κ ≤ 1 / 8 ∧ strP a₁ κ * strS a₁ κ ≤ 1 / 8 := by
  have h1 : 0 ≤ strKP a₁ κ := by simp only [strKP, strP]; positivity
  have h2 : 0 ≤ strP a₁ κ := by simp only [strP]; positivity
  have hZ : 0 < 1 + 2 * κ + strKP a₁ κ + strP a₁ κ := by positivity
  have hsZ : strS a₁ κ * (1 + 2 * κ + strKP a₁ κ + strP a₁ κ) = 1 / 8 := by
    rw [strS]; field_simp
  have hs0 := (strS_pos ha₁ hκ).le
  constructor
  · rw [← hsZ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0
  · rw [← hsZ, mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0

/-- The constant of the global error bounds is at least one. -/
private theorem one_le_globalConst {K c τ : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hτ : 0 ≤ τ) :
    1 ≤ Real.exp (K * τ) * (1 + τ * c) := by
  have h1 : 1 ≤ Real.exp (K * τ) := Real.one_le_exp (by positivity)
  have h2 : 1 ≤ 1 + τ * c := by linarith [mul_nonneg hτ hc]
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ _ := mul_le_mul h1 h2 zero_le_one (by linarith)

/-- From a one-step recursion `e⁺ ≤ (1 + K h) e + c h³`, valid while `e ≤ s`, to the global bound
`e n ≤ C (e 0 + h²)` with `C = e^{K τ} (1 + τ c)`, for `h`, `e 0 ≤ s / C`. -/
private theorem global_of_recursion {e : ℕ → ℝ} {K c s τ h : ℝ} {N : ℕ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hτ : 0 ≤ τ) (hs : 0 < s) (hs1 : s ≤ 1) (hh : 0 ≤ h)
    (hhs : h ≤ s / (Real.exp (K * τ) * (1 + τ * c)))
    (he₀s : e 0 ≤ s / (Real.exp (K * τ) * (1 + τ * c))) (hnn : ∀ k, 0 ≤ e k)
    (hgrid : ∀ n ≤ N, (n : ℝ) * h ≤ τ)
    (hrec : ∀ k < N, e k ≤ s → e (k + 1) ≤ (1 + K * h) * e k + c * h ^ 3) :
    ∀ n ≤ N, e n ≤ Real.exp (K * τ) * (1 + τ * c) * (e 0 + h ^ 2) := by
  have he0 := hnn 0
  obtain ⟨C, hC⟩ : ∃ C, C = Real.exp (K * τ) * (1 + τ * c) := ⟨_, rfl⟩
  rw [← hC] at hhs he₀s ⊢
  have hC1 : 1 ≤ C := by rw [hC]; exact one_le_globalConst hK hc hτ
  have hC0 : 0 < C := by linarith
  have hsC : s / C ≤ s := div_le_self hs.le hC1
  have hh1 : h ≤ 1 := hhs.trans (hsC.trans hs1)
  have hsq : h ^ 2 ≤ h := pow_le_of_le_one hh hh1 two_ne_zero
  have hg0 : 0 ≤ c * h ^ 3 := by positivity
  have hgN : ∀ {n : ℕ}, n ≤ N → (n : ℝ) * (c * h ^ 3) ≤ τ * c * h ^ 2 := by
    intro n hn
    calc (n : ℝ) * (c * h ^ 3) = (n * h) * (c * h ^ 2) := by ring
      _ ≤ τ * (c * h ^ 2) := mul_le_mul_of_nonneg_right (hgrid n hn) (by positivity)
      _ = _ := by ring
  have hexpn : ∀ {n : ℕ}, n ≤ N → Real.exp (K * (n * h)) ≤ Real.exp (K * τ) := fun hn =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hgrid _ hn) hK)
  have hsmall : Real.exp (K * (N * h)) * (e 0 + N * (c * h ^ 3)) ≤ s := by
    have h2 : e 0 + N * (c * h ^ 3) ≤ (1 + τ * c) * (s / C) := by
      have h3 := hgN (le_refl N)
      have h4 : τ * c * h ^ 2 ≤ τ * c * (s / C) :=
        mul_le_mul_of_nonneg_left (hsq.trans hhs) (by positivity)
      have h5 : (1 + τ * c) * (s / C) = s / C + τ * c * (s / C) := by ring
      linarith
    calc _ ≤ Real.exp (K * τ) * ((1 + τ * c) * (s / C)) :=
          mul_le_mul (hexpn le_rfl) h2 (by positivity) (Real.exp_pos _).le
      _ = C * (s / C) := by rw [hC]; ring
      _ = s := by field_simp
  have hrec' : ∀ k < N, e k ≤ s → e (k + 1) ≤ Real.exp (K * h) * e k + c * h ^ 3 := by
    intro k hk hek
    have h1 := hrec k hk hek
    have h2 : 1 + K * h ≤ Real.exp (K * h) := by linarith [Real.add_one_le_exp (K * h)]
    have h3 := mul_le_mul_of_nonneg_right h2 (hnn k)
    linarith
  intro n hn
  have hmain := gronwall_bootstrap hK hh hg0 he0 hrec' hsmall n hn
  have hbound : e 0 + n * (c * h ^ 3) ≤ (1 + τ * c) * (e 0 + h ^ 2) := by
    have h3 := hgN hn
    have h4 : 0 ≤ τ * c * e 0 := by positivity
    have h5 : 0 ≤ h ^ 2 := by positivity
    have h6 : (1 + τ * c) * (e 0 + h ^ 2) = e 0 + h ^ 2 + τ * c * e 0 + τ * c * h ^ 2 := by ring
    linarith
  calc e n ≤ _ := hmain
    _ ≤ Real.exp (K * τ) * ((1 + τ * c) * (e 0 + h ^ 2)) :=
        mul_le_mul (hexpn hn) hbound
          (add_nonneg he0 (mul_nonneg (Nat.cast_nonneg _) hg0)) (Real.exp_pos _).le
    _ = _ := by rw [hC]; ring

/-- `N` steps of the scheme (12) of arXiv 1301.1058 with step size `h` on the grid `t₀ + k h`. -/
structure IsStrangRun (A : ℝ → Matrix m n ℝ) (t₀ h : ℝ) (N : ℕ) (U Um : ℕ → Matrix m r ℝ)
    (S Ŝm Ŝ : ℕ → Matrix r r ℝ) (W : ℕ → Matrix n r ℝ) : Prop where
  orthV₀ : (W 0)ᵀ * W 0 = 1
  step : ∀ k < N, IsStrangStep (A (t₀ + k * h)) (A (t₀ + k * h + h / 2)) (A (t₀ + k * h + h))
    (U k) (S k) (W k) (Um k) (Ŝm k) (W (k + 1)) (Ŝ k) (U (k + 1)) (S (k + 1))

omit [DecidableEq m] [DecidableEq n] in
/-- A run has orthonormal right factors. -/
private theorem IsStrangRun.orthV {A : ℝ → Matrix m n ℝ} {t₀ h : ℝ} {N : ℕ}
    {U Um : ℕ → Matrix m r ℝ}
    {S Ŝm Ŝ : ℕ → Matrix r r ℝ} {W : ℕ → Matrix n r ℝ}
    (hrun : IsStrangRun A t₀ h N U Um S Ŝm Ŝ W) : ∀ k ≤ N, (W k)ᵀ * W k = 1 := by
  intro k hk
  cases k with
  | zero => exact hrun.orthV₀
  | succ k => exact (hrun.step k hk).orthV₁

/-- **The scheme (12) converges with order two** (arXiv 1301.1058, §3.3: "a second-order
scheme").
On `[t₀, T]`, let `Y = U S Vᵀ` solve (5) with `‖S(t)⁻¹‖ ≤ κ`, for `A` with `‖Ȧ‖ ≤ a₁` and `Ȧ`
Lipschitz with constant `a₂`.  Then there are `C` and `s > 0`, depending only on `a₁`, `a₂`, `κ` and
`T - t₀` (not on `A`, `Y`, `h`, `N`), such that every run of (12) with step size `0 ≤ h ≤ s`,
`t₀ + N h ≤ T`, and with starting value within `s` of `Y(t₀)` satisfies

    ‖Yₙ - Y(tₙ)‖ ≤ C (‖Y₀ - Y(t₀)‖ + h²)        (n ≤ N).

Here `C = e^{K τ} (1 + τ c)`, `τ = T - t₀`, `K = strK a₁ a₂ κ`, `c = K + strC a₁ a₂ κ`.  The
numerical starting value only has to be factorized with orthonormal `V₀`.  The proof is the
recursion `e⁺ ≤ (1 + K h) e + c h³` of `strang_step_bound` with a bootstrap (the numerical solution
has to stay within `strS a₁ κ` of the exact one); the paper appeals to standard theory.  As in
`strang_local_error`, `C` depends on `κ`. -/
theorem strang_global_error {κ t₀ T : ℝ} (hκ : 0 ≤ κ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hT : t₀ ≤ T) :
    ∃ C s : ℝ, 0 ≤ C ∧ 0 < s ∧ ∀ (A dA : ℝ → Matrix m n ℝ) (U : ℝ → Matrix m r ℝ)
      (S : ℝ → Matrix r r ℝ) (V : ℝ → Matrix n r ℝ) (h : ℝ) (N : ℕ) (Ur Um : ℕ → Matrix m r ℝ)
      (Sr Ŝm Ŝ : ℕ → Matrix r r ℝ) (Vr : ℕ → Matrix n r ℝ),
      0 ≤ h → h ≤ s → t₀ + N * h ≤ T → IsC11 A dA t₀ T a₁ a₂ →
      IsFactorSolution dA κ t₀ T U S V → IsStrangRun A t₀ h N Ur Um Sr Ŝm Ŝ Vr →
      ‖Ur 0 * Sr 0 * (Vr 0)ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ s →
      ∀ n ≤ N, ‖Ur n * Sr n * (Vr n)ᵀ - U (t₀ + n * h) * S (t₀ + n * h) * (V (t₀ + n * h))ᵀ‖ ≤
        C * (‖Ur 0 * Sr 0 * (Vr 0)ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ + h ^ 2) := by
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = T - t₀ := ⟨_, rfl⟩
  have hτ : 0 ≤ τ := by rw [hτdef]; linarith
  have hK0 := strK_nonneg ha₁ ha₂ hκ
  have hC0 := strC_nonneg ha₁ ha₂ hκ
  have hs0 := strS_pos ha₁ hκ
  obtain ⟨K, hK⟩ : ∃ K, K = strK a₁ a₂ κ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = strK a₁ a₂ κ + strC a₁ a₂ κ := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = strS a₁ κ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact add_nonneg hK0 hC0
  rw [← hK] at hK0
  rw [← hs₀] at hs0
  have hs₀1 : s₀ ≤ 1 := by rw [hs₀]; exact strS_le_one ha₁ hκ
  obtain ⟨C, hC⟩ : ∃ C, C = Real.exp (K * τ) * (1 + τ * c) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; exact one_le_globalConst hK0 hc0 hτ
  refine ⟨C, s₀ / C, by linarith, div_pos hs0 (by linarith), ?_⟩
  intro A dA U S V h N Ur Um Sr Ŝm Ŝ Vr hh hhs hN hA hfac hrun hstart
  have hsC : s₀ / C ≤ s₀ := div_le_self hs0.le hC1
  have hgrid : ∀ {k : ℕ}, k ≤ N → t₀ + k * h ∈ Icc t₀ T := fun hk => grid_mem hh hN hk
  have hmain := global_of_recursion (s := s₀) (τ := τ) (N := N) (h := h)
    (e := fun k => ‖Ur k * Sr k * (Vr k)ᵀ - U (t₀ + k * h) * S (t₀ + k * h)
      * (V (t₀ + k * h))ᵀ‖) hK0 hc0 hτ hs0 hs₀1 hh (by rw [← hC]; exact hhs)
    (by simpa [hC] using hstart) (fun _ => norm_nonneg _)
    (fun n hn => by
      have := (hgrid hn).2
      rw [hτdef]; linarith)
    (fun k hk hek => by
      have hk1 := hgrid hk.le
      have hk2 := hgrid (k := k + 1) hk
      have hk2' : t₀ + (k : ℝ) * h + h = t₀ + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      have h1 := strang_step_bound (t₀ := t₀ + k * h) (tm := t₀ + k * h + h / 2)
        (t₁ := t₀ + k * h + h) (δ := ‖Ur k * Sr k * (Vr k)ᵀ - U (t₀ + k * h) * S (t₀ + k * h)
          * (V (t₀ + k * h))ᵀ‖) (η := 0) hκ hh rfl rfl
        (hfac.mono hk1.1 (by rw [hk2']; exact hk2.2)) (hA.mono hk1.1 (by rw [hk2']; exact hk2.2))
        (hrun.step k hk) (hrun.orthV k hk.le) le_rfl (by simp) (by simp)
        (by rw [← hs₀]; linarith) (by rw [← hs₀]; exact hek) (by rw [← hs₀]; exact hs0.le)
      rw [← hc, ← hK, mul_zero, add_zero, hk2'] at h1
      exact h1)
  intro n hn
  have h2 := hmain n hn
  simp only [Nat.cast_zero, zero_mul, add_zero] at h2
  rw [hC]
  exact h2

end Strang

/-! ### The explicit method of §3.4 for `Ȧ = F(A)` -/

section ExplicitMethod

/-- A continuous curve on `[a, b]` has an antiderivative. -/
private theorem exists_antiderivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {g : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    ∃ A : ℝ → E, ContinuousOn A (Icc a b) ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt A (g t) (Ici t) t := by
  obtain ⟨g', hg', hgg'⟩ : ∃ g' : ℝ → E, Continuous g' ∧ ∀ t ∈ Icc a b, g' t = g t := by
    refine ⟨fun t => g (projIcc a b hab t), ?_, fun t ht => ?_⟩
    · exact hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun t => (projIcc a b hab t).2)
    · simp only [projIcc_of_mem hab ht]
  have hder : ∀ t, HasDerivAt (fun t => ∫ s in a..t, g' s) (g' t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg'.intervalIntegrable _ _)
      (hg'.stronglyMeasurableAtFilter _ _) hg'.continuousAt
  refine ⟨fun t => ∫ s in a..t, g' s, fun t _ => (hder t).continuousAt.continuousWithinAt,
    fun t ht => ?_⟩
  rw [← hgg' t ⟨ht.1, ht.2.le⟩]
  exact (hder t).hasDerivWithinAt

variable {A dA Y : ℝ → Matrix m n ℝ} {P Pd : ℝ → Matrix m m ℝ} {V : ℝ → Matrix n r ℝ}
  {a b a₁ a₂ M : ℝ}

omit [DecidableEq r] in
/-- Mean value bound for `Y - A` against a fixed normal direction `Nc`. -/
private theorem norm_increment_normal_le (hA : IsC11 A dA a b a₁ a₂)
    (hYc : ContinuousOn Y (Icc a b))
    (hY : ∀ t ∈ Ico a b, HasDerivWithinAt Y
      (P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ)) (Ici t) t)
    {Nc : Matrix m n ℝ} {c d w : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hw : ∀ t ∈ Ico c d, ‖(1 - P t) * dA t * (1 - V t * (V t)ᵀ) - Nc‖ ≤ w) :
    ‖(Y d - A d) - (Y c - A c) + (d - c) • Nc‖ ≤ w * (d - c) := by
  have hN : ∀ t, P t * dA t + dA t * (V t * (V t)ᵀ) - P t * dA t * (V t * (V t)ᵀ) - dA t
      = -((1 - P t) * dA t * (1 - V t * (V t)ᵀ)) := by
    intro t
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have hder : ∀ t ∈ Ico c d, HasDerivWithinAt (fun t => (Y t - A t) + (t - c) • Nc)
      (-((1 - P t) * dA t * (1 - V t * (V t)ᵀ)) + Nc) (Ici t) t := by
    intro t ht
    have ht' : t ∈ Ico a b := ⟨hac.trans ht.1, ht.2.trans_le hdb⟩
    have h1 := (hY t ht').fun_sub (hA.deriv t ht')
    rw [hN] at h1
    have h2 : HasDerivWithinAt (fun t : ℝ => (t - c) • Nc) ((1 : ℝ) • Nc) (Ici t) t :=
      ((hasDerivWithinAt_id t _).sub_const c).smul_const Nc
    have h3 := h1.fun_add h2
    rwa [one_smul] at h3
  have hcont : ContinuousOn (fun t => (Y t - A t) + (t - c) • Nc) (Icc c d) :=
    ((hYc.mono (Icc_subset_Icc hac hdb)).sub (hA.cont.mono (Icc_subset_Icc hac hdb))).add
      (by fun_prop)
  have hbd : ∀ t ∈ Ico c d, ‖-((1 - P t) * dA t * (1 - V t * (V t)ᵀ)) + Nc‖ ≤ w := by
    intro t ht
    rw [neg_add_eq_sub, norm_sub_rev]
    exact hw t ht
  have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd d ⟨hcd, le_rfl⟩
  have heq : (Y d - A d) - (Y c - A c) + (d - c) • Nc
      = ((Y d - A d) + (d - c) • Nc) - ((Y c - A c) + (c - c) • Nc) := by
    rw [sub_self, zero_smul]; abel
  rwa [heq]

/-- **Estimate of the predictor** of the explicit method of arXiv 1301.1058, §3.4 (one step of the
basic integrator with `ΔA = h F₀`): if `Y₀` is `δ`-close to `Y(t₀)` and `F₀` is `f`-close to
`Ȧ(t₀)`, then `Ỹ₁` is `O(δ + f h + h²)`-close to
`Y(t₀ + h)`. -/
theorem predictor_estimate {U : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ} {κ t₀ t₁ h δ f p₁ : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (ht₁ : t₁ = t₀ + h) (hp₁ : p₁ = 2 * a₁ * κ)
    (hfac : IsFactorSolution dA κ t₀ t₁ U S V) (hA : IsC11 A dA t₀ t₁ a₁ a₂)
    {F₀ : Matrix m n ℝ} {U₀ Up : Matrix m r ℝ} {S₀ Ŝp Sp : Matrix r r ℝ} {V₀ Vp : Matrix n r ℝ}
    (hs : IsKSLIncrementStep 0 (h • F₀) U₀ S₀ V₀ Up Ŝp Sp Vp) (hV₀ : V₀ᵀ * V₀ = 1)
    (hδ : ‖U₀ * S₀ * V₀ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ δ) (hf : ‖F₀ - dA t₀‖ ≤ f)
    (hsm : 2 * κ * δ + p₁ * h ≤ 1 / 2) :
    ‖Up * Sp * Vpᵀ - U t₁ * S t₁ * (V t₁)ᵀ‖ ≤ δ + h * f + a₂ * h ^ 2
      + h * ((4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * f) + p₁ * h) * a₁ + (a₂ * h + f)
        + (a₁ + f) * (2 * κ * δ + p₁ * h)) := by
  have ha₁ := hA.nn₁
  have ha₂ := hA.nn₂
  have hUp := hs.orthU
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hf0 : 0 ≤ f := (norm_nonneg _).trans hf
  have hp₁0 : 0 ≤ p₁ := by rw [hp₁]; positivity
  have h0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, by rw [ht₁]; linarith⟩
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨by rw [ht₁]; linarith, le_rfl⟩
  have hd : t₁ - t₀ = h := by rw [ht₁]; ring
  have hP : IsC11 (fun t => U t * (U t)ᵀ) (projRhs dA U S V) t₀ t₁ p₁
      (2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2) := by
    rw [hp₁]; exact hfac.isC11_proj hA hκ
  have hQ : IsC11 (fun t => V t * (V t)ᵀ) (projRhs (fun t => (dA t)ᵀ) V (fun t => (S t)ᵀ) U)
      t₀ t₁ p₁ (2 * a₂ * κ + 10 * a₁ ^ 2 * κ ^ 2) := by
    rw [hp₁]; exact hfac.isC11_proj_right hA hκ
  have hYc := hfac.continuousOn_Y
  have hY := fun t (ht : t ∈ Ico t₀ t₁) => hfac.hasDerivWithinAt_Y ht
  have hG : ∀ t ∈ Icc t₀ t₁, (S t)⁻¹ * S t = 1 := fun t ht =>
    Matrix.nonsing_inv_mul _ (hfac.det t ht)
  have hG' : ∀ t ∈ Icc t₀ t₁, S t * (S t)⁻¹ = 1 := fun t ht =>
    Matrix.mul_nonsing_inv _ (hfac.det t ht)
  have hUo := hfac.orthU
  have hVo := hfac.orthV
  have hcore := hfac.core
  have hclosed := ksl_increment_eq hs
  have hK := hs.qrK
  rw [sub_zero] at hclosed hK
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = U₀ * S₀ * V₀ᵀ := ⟨_, rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ Pp, Pp = Up * Upᵀ := ⟨_, rfl⟩
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ = V₀ * V₀ᵀ := ⟨_, rfl⟩
  obtain ⟨Yt, hYdef⟩ : ∃ Yt : ℝ → Matrix m n ℝ, Yt = fun t => U t * S t * (V t)ᵀ := ⟨_, rfl⟩
  have hYt : ∀ t, U t * S t * (V t)ᵀ = Yt t := fun t => by rw [hYdef]
  rw [← hYdef] at hYc hY
  simp only [hYt] at hδ ⊢
  rw [← hY₀] at hδ hclosed
  rw [← hPp, ← hQ₀] at hclosed
  have hδ' : ‖Yt t₀ - Y₀‖ ≤ δ := by rwa [norm_sub_rev]
  have hY₀Q : Y₀ * Q₀ = Y₀ := by rw [hY₀, hQ₀]; exact mul_proj_eq hV₀
  have hQc : ∀ X : Matrix m n ℝ, ‖X * (1 - Q₀)‖ ≤ ‖X‖ := fun X => by
    rw [hQ₀]; exact norm_mul_compl_le hV₀ X
  have hQp : ∀ X : Matrix m n ℝ, ‖X * Q₀‖ ≤ ‖X‖ := fun X => by
    rw [hQ₀]; exact norm_mul_proj_le hV₀ X
  have hPc : ∀ X : Matrix m n ℝ, ‖(1 - Pp) * X‖ ≤ ‖X‖ := fun X => by
    rw [hPp]; exact norm_compl_mul_le hUp X
  have hY₀Qc : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  have hcap : (1 - Pp) * (Y₀ + (h • F₀) * Q₀) = 0 := by
    have hPU : (1 - Pp) * Up = 0 := by
      rw [hPp, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hUp, Matrix.mul_one, sub_self]
    have h2 : Y₀ + (h • F₀) * Q₀ = Up * (Ŝp * V₀ᵀ) := by
      rw [← Matrix.mul_assoc Up, hK, Matrix.add_mul, hY₀, hQ₀, Matrix.mul_assoc (h • F₀)]
    rw [h2, ← Matrix.mul_assoc, hPU, Matrix.zero_mul]
  -- the old right projector
  have hQ₀gap : ‖V t₀ * (V t₀)ᵀ - Q₀‖ ≤ 2 * κ * δ := by
    have h2 := right_gap (hUo t₀ h0) (hVo t₀ h0) (hG t₀ h0) (hcore t₀ h0) hV₀
    rw [hYt, ← hQ₀] at h2
    have h3 : Yt t₀ * (1 - Q₀) = (Yt t₀ - Y₀) * (1 - Q₀) := by
      rw [Matrix.sub_mul, hY₀Qc, sub_zero]
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left ((hQc _).trans hδ') (by positivity))
  have hdist : ∀ t ∈ Icc t₀ t₁, |t - t₀| ≤ h := fun t ht => by
    rw [abs_of_nonneg (sub_nonneg.2 ht.1)]; linarith [ht.2]
  have hdist' : ∀ t ∈ Icc t₀ t₁, |t₁ - t| ≤ h := fun t ht => by
    rw [abs_of_nonneg (sub_nonneg.2 ht.2)]; linarith [ht.1]
  have hQw : ∀ t ∈ Icc t₀ t₁, ‖V t * (V t)ᵀ - Q₀‖ ≤ 2 * κ * δ + p₁ * h := by
    intro t ht
    have h2 := hQ.norm_sub_le h0 ht
    have h5 : p₁ * |t - t₀| ≤ p₁ * h := mul_le_mul_of_nonneg_left (hdist t ht) hp₁0
    have h4 : V t * (V t)ᵀ - Q₀ = (V t * (V t)ᵀ - V t₀ * (V t₀)ᵀ) + (V t₀ * (V t₀)ᵀ - Q₀) := by abel
    rw [h4]
    refine (norm_add_le _ _).trans ?_
    linarith
  -- the new left projector
  have hN₁ := norm_increment_le (P := fun t => U t * (U t)ᵀ) (L := (1 : Matrix m m ℝ))
    (R := (1 : Matrix n n ℝ)) (w := a₁) hA hYc hY h0.1 h1.1 h1.2 (fun t ht => by
      have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1, ht.2.le⟩
      simp only [Matrix.one_mul, Matrix.mul_one]
      exact (norm_mul_compl_le (hVo t ht') _).trans
        ((norm_compl_mul_le (hUo t ht') _).trans (hA.bound t ht')))
  rw [Matrix.one_mul, Matrix.mul_one, hd] at hN₁
  have hΔ : ‖(A t₁ - A t₀) - h • dA t₀‖ ≤ a₂ * h ^ 2 := by
    have h2 := IsC11.norm_sub_sub_smul_le hA (c := t₀) (w := a₂ * h) h0 h1 h1.1 (fun x hx => by
      refine (hA.lip t₀ h0 x hx).trans (mul_le_mul_of_nonneg_left (hdist x hx) ha₂))
    rw [hd] at h2
    calc _ ≤ _ := h2
      _ = _ := by ring
  have hΔ' : ‖h • F₀ - (A t₁ - A t₀)‖ ≤ h * f + a₂ * h ^ 2 := by
    have h2 : h • F₀ - (A t₁ - A t₀) = h • (F₀ - dA t₀) - ((A t₁ - A t₀) - h • dA t₀) := by
      rw [smul_sub]; abel
    rw [h2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh]
    gcongr
  have hβp : ‖Yt t₁ - Y₀ - h • F₀‖ ≤ δ + a₁ * h + a₂ * h ^ 2 + h * f := by
    have h2 : Yt t₁ - Y₀ - h • F₀ = ((Yt t₁ - A t₁) - (Yt t₀ - A t₀)) + (Yt t₀ - Y₀)
        - (h • F₀ - (A t₁ - A t₀)) := by abel
    rw [h2]
    refine (norm_sub_le _ _).trans ?_
    have h3 := norm_add_le ((Yt t₁ - A t₁) - (Yt t₀ - A t₀)) (Yt t₀ - Y₀)
    linarith
  have hQmle : ‖V t₁ * (V t₁)ᵀ - V₀ * V₀ᵀ‖ ≤ 1 / 2 := by
    rw [← hQ₀]; exact (hQw t₁ h1).trans hsm
  have hXR : (1 - Pp) * Yt t₁ * (V t₁ * (V t₁)ᵀ) = (1 - Pp) * Yt t₁ := by
    rw [Matrix.mul_assoc, ← hYt t₁, mul_proj_eq (hVo t₁ h1)]
  have hboot := norm_le_two_mul_of_right hV₀ hXR hQmle
  rw [← hQ₀] at hboot
  have hKey : (1 - Pp) * Yt t₁ * Q₀ = (1 - Pp) * ((Yt t₁ - Y₀ - h • F₀) * Q₀) := by
    have e : (Yt t₁ - Y₀ - h • F₀) * Q₀ = Yt t₁ * Q₀ - (Y₀ + (h • F₀) * Q₀) := by
      simp only [Matrix.sub_mul, hY₀Q]
      abel
    rw [e, Matrix.mul_sub, hcap, sub_zero, Matrix.mul_assoc]
  have hβp' : ‖(1 - Pp) * Yt t₁ * Q₀‖ ≤ δ + a₁ * h + a₂ * h ^ 2 + h * f := by
    rw [hKey]
    exact (hPc _).trans ((hQp _).trans hβp)
  have hPpgap : ‖U t₁ * (U t₁)ᵀ - Pp‖ ≤ 4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * f) := by
    have h2 := left_gap (hUo t₁ h1) (hVo t₁ h1) (hG' t₁ h1) (hcore t₁ h1) hUp
    rw [hYt, ← hPp] at h2
    refine h2.trans ?_
    have h3 := hboot.trans (mul_le_mul_of_nonneg_left hβp' (by norm_num))
    calc 2 * κ * ‖(1 - Pp) * Yt t₁‖ ≤ 2 * κ * (2 * (δ + a₁ * h + a₂ * h ^ 2 + h * f)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hPt : ∀ t ∈ Icc t₀ t₁, ‖Pp - U t * (U t)ᵀ‖ ≤
      4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * f) + p₁ * h := by
    intro t ht
    have h2 := hP.norm_sub_le ht h1
    have h3 : p₁ * |t₁ - t| ≤ p₁ * h := mul_le_mul_of_nonneg_left (hdist' t ht) hp₁0
    have h4 : Pp - U t * (U t)ᵀ = -(U t₁ * (U t₁)ᵀ - Pp) + (U t₁ * (U t₁)ᵀ - U t * (U t)ᵀ) := by
      abel
    rw [h4]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith
  -- the normal component
  have hF₀ : ‖F₀‖ ≤ a₁ + f := by
    have h2 : F₀ = (F₀ - dA t₀) + dA t₀ := by abel
    rw [h2]
    exact (norm_add_le _ _).trans (by linarith [hA.bound t₀ h0])
  obtain ⟨w, hw⟩ : ∃ w, w = (4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * f) + p₁ * h) * a₁
      + (a₂ * h + f) + (a₁ + f) * (2 * κ * δ + p₁ * h) := ⟨_, rfl⟩
  have hNc := norm_increment_normal_le (P := fun t => U t * (U t)ᵀ)
    (Nc := (1 - Pp) * F₀ * (1 - Q₀)) (w := w) hA hYc hY h0.1 h1.1 h1.2 (fun t ht => by
      have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1, ht.2.le⟩
      have hg1 : ‖dA t * (1 - V t * (V t)ᵀ)‖ ≤ a₁ :=
        (norm_mul_compl_le (hVo t ht') _).trans (hA.bound t ht')
      have hg2 : ‖dA t - F₀‖ ≤ a₂ * h + f := by
        have h2 : dA t - F₀ = (dA t - dA t₀) - (F₀ - dA t₀) := by abel
        rw [h2]
        refine (norm_sub_le _ _).trans ?_
        have h3 := (hA.lip t₀ h0 t ht').trans (mul_le_mul_of_nonneg_left (hdist t ht') ha₂)
        linarith
      have hdecomp : (1 - U t * (U t)ᵀ) * dA t * (1 - V t * (V t)ᵀ) - (1 - Pp) * F₀ * (1 - Q₀)
          = (Pp - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ))
            + (1 - Pp) * ((dA t - F₀) * (1 - V t * (V t)ᵀ))
            + (1 - Pp) * (F₀ * (Q₀ - V t * (V t)ᵀ)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
          Matrix.mul_assoc]
        abel
      simp only [hdecomp]
      have h2 : ‖(Pp - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ))‖ ≤
          (4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * f) + p₁ * h) * a₁ :=
        (Frobenius.norm_mul_le _ _).trans (mul_le_mul (hPt t ht') hg1 (norm_nonneg _)
          (by positivity))
      have h3 : ‖(1 - Pp) * ((dA t - F₀) * (1 - V t * (V t)ᵀ))‖ ≤ a₂ * h + f :=
        (hPc _).trans ((norm_mul_compl_le (hVo t ht') _).trans hg2)
      have h4 : ‖(1 - Pp) * (F₀ * (Q₀ - V t * (V t)ᵀ))‖ ≤ (a₁ + f) * (2 * κ * δ + p₁ * h) := by
        refine (hPc _).trans ((Frobenius.norm_mul_le _ _).trans (mul_le_mul hF₀ ?_ (norm_nonneg _)
          (by positivity)))
        rw [norm_sub_rev]; exact hQw t ht'
      have h5 := norm_add₃_le (a := (Pp - U t * (U t)ᵀ) * (dA t * (1 - V t * (V t)ᵀ)))
        (b := (1 - Pp) * ((dA t - F₀) * (1 - V t * (V t)ᵀ)))
        (c := (1 - Pp) * (F₀ * (Q₀ - V t * (V t)ᵀ)))
      rw [hw]
      linarith)
  rw [hd] at hNc
  have hsplit : Up * Sp * Vpᵀ - Yt t₁ = (Y₀ - Yt t₀) + (h • F₀ - (A t₁ - A t₀))
      - ((Yt t₁ - A t₁) - (Yt t₀ - A t₀) + h • ((1 - Pp) * F₀ * (1 - Q₀))) := by
    have h3 : Pp * (h • F₀) * (1 - Q₀)
        = h • F₀ - (h • F₀) * Q₀ - h • ((1 - Pp) * F₀ * (1 - Q₀)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_sub]
      abel
    rw [hclosed, h3]
    abel
  rw [hsplit]
  have hfin := norm_sub_le ((Y₀ - Yt t₀) + (h • F₀ - (A t₁ - A t₀)))
    ((Yt t₁ - A t₁) - (Yt t₀ - A t₀) + h • ((1 - Pp) * F₀ * (1 - Q₀)))
  have hfin2 := norm_add_le (Y₀ - Yt t₀) (h • F₀ - (A t₁ - A t₀))
  rw [← hw]
  have h8 : w * h = h * w := mul_comm _ _
  linarith

/-- The quadratic surrogate of arXiv 1301.1058, §3.4:
`A(t₀ + θ h) ≈ Y₀ + (h/2) θ (2 - θ) F(Y₀) + (h/2) θ² F(Ỹ₁)`, the primitive of the linear function
`B(t₀ + θ h) = (1 - θ) F(Y₀) + θ F(Ỹ₁)`. -/
noncomputable def surrogate (Y₀ F₀ F₁ : Matrix m n ℝ) (h θ : ℝ) : Matrix m n ℝ :=
  Y₀ + (h / 2 * (θ * (2 - θ))) • F₀ + (h / 2 * θ ^ 2) • F₁

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The first increment of the surrogate. -/
private theorem surrogate_half_sub (Y₀ F₀ F₁ : Matrix m n ℝ) (h : ℝ) :
    surrogate Y₀ F₀ F₁ h (1 / 2) - surrogate Y₀ F₀ F₁ h 0 = (3 * h / 8) • F₀ + (h / 8) • F₁ := by
  simp only [surrogate]
  module

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The second increment of the surrogate. -/
private theorem surrogate_one_sub (Y₀ F₀ F₁ : Matrix m n ℝ) (h : ℝ) :
    surrogate Y₀ F₀ F₁ h 1 - surrogate Y₀ F₀ F₁ h (1 / 2) = (h / 8) • F₀ + (3 * h / 8) • F₁ := by
  simp only [surrogate]
  module

/-- One step of the **explicit method of arXiv 1301.1058, §3.4** for `Ȧ = F(A)`:

* predictor: one step of the basic integrator with `ΔA = h F(Y₀)`, with result
  `Ỹ₁ = Up Sp Vpᵀ`;
* corrector: one step of the second-order scheme (12) with `A` replaced by the quadratic
  `surrogate Y₀ F(Y₀) F(Ỹ₁) h` at `θ = 0, 1/2, 1`. -/
structure IsExplicitStep (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (Up : Matrix m r ℝ) (Ŝp Sp : Matrix r r ℝ)
    (Vp : Matrix n r ℝ) (Um : Matrix m r ℝ) (Ŝm : Matrix r r ℝ) (V₁ : Matrix n r ℝ)
    (Ŝ₁ : Matrix r r ℝ) (U₁ : Matrix m r ℝ) (S₁ : Matrix r r ℝ) : Prop where
  predictor : IsKSLIncrementStep 0 (h • F (U₀ * S₀ * V₀ᵀ)) U₀ S₀ V₀ Up Ŝp Sp Vp
  corrector : IsStrangStep
    (surrogate (U₀ * S₀ * V₀ᵀ) (F (U₀ * S₀ * V₀ᵀ)) (F (Up * Sp * Vpᵀ)) h 0)
    (surrogate (U₀ * S₀ * V₀ᵀ) (F (U₀ * S₀ * V₀ᵀ)) (F (Up * Sp * Vpᵀ)) h (1 / 2))
    (surrogate (U₀ * S₀ * V₀ᵀ) (F (U₀ * S₀ * V₀ᵀ)) (F (Up * Sp * Vpᵀ)) h 1)
    U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁

/-- The surrogate of arXiv 1301.1058, §3.4, is third-order accurate: the increments of a primitive
`A` of `g ∈ C^{1,1}` agree up to `O(h³)` with those of the primitive of the linear interpolant of
`g(t₀)`, `g(t₁)`. -/
theorem increments_estimate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A g dg : ℝ → E}
    {t₀ tm t₁ h a₁ a₂ M : ℝ} (hh : 0 ≤ h) (htm : tm = t₀ + h / 2) (ht₁ : t₁ = t₀ + h)
    (hA : IsC11 A g t₀ t₁ a₁ a₂) (hg : IsC11 g dg t₀ t₁ a₂ M) :
    ‖(A tm - A t₀) - ((3 * h / 8) • g t₀ + (h / 8) • g t₁)‖ ≤ M * h ^ 3 ∧
      ‖(A t₁ - A tm) - ((h / 8) • g t₀ + (3 * h / 8) • g t₁)‖ ≤ 2 * M * h ^ 3 := by
  have hM := hg.nn₂
  have h0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, by rw [ht₁]; linarith⟩
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨by rw [ht₁]; linarith, le_rfl⟩
  have hm : tm ∈ Icc t₀ t₁ := ⟨by rw [htm]; linarith, by rw [htm, ht₁]; linarith⟩
  have hd : t₁ - t₀ = h := by rw [ht₁]; ring
  have hdm : tm - t₀ = h / 2 := by rw [htm]; ring
  have hT : ∀ t ∈ Icc t₀ t₁, ‖A t - A t₀ - (t - t₀) • g t₀ - ((t - t₀) ^ 2 / 2) • dg t₀‖ ≤
      M * h ^ 2 * (t - t₀) := by
    intro t ht
    have hder : ∀ x ∈ Ico t₀ t, HasDerivWithinAt
        (fun x => A x - A t₀ - (x - t₀) • g t₀ - ((x - t₀) ^ 2 / 2) • dg t₀)
        (g x - g t₀ - (x - t₀) • dg t₀) (Ici x) x := by
      intro x hx
      have hx' : x ∈ Ico t₀ t₁ := ⟨hx.1, hx.2.trans_le ht.2⟩
      have h2 : HasDerivWithinAt (fun x : ℝ => (x - t₀) • g t₀) ((1 : ℝ) • g t₀) (Ici x) x :=
        ((hasDerivWithinAt_id x _).sub_const t₀).smul_const (g t₀)
      have h3 : HasDerivWithinAt (fun x : ℝ => (x - t₀) ^ 2 / 2) (x - t₀) (Ici x) x := by
        have h6 : HasDerivAt (fun x : ℝ => (x - t₀) ^ 2 / 2) (x - t₀) x := by
          have h7 : HasDerivAt (fun x : ℝ => (x - t₀) ^ 2) (2 * (x - t₀)) x := by
            simpa using ((hasDerivAt_id' x).sub_const t₀).fun_pow 2
          convert h7.div_const 2 using 1
          ring
        exact h6.hasDerivWithinAt
      have h4 := (((hA.deriv x hx').sub_const (A t₀)).fun_sub h2).fun_sub (h3.smul_const (dg t₀))
      rwa [one_smul] at h4
    have hcont : ContinuousOn
        (fun x => A x - A t₀ - (x - t₀) • g t₀ - ((x - t₀) ^ 2 / 2) • dg t₀) (Icc t₀ t) :=
      ((((hA.cont.mono (Icc_subset_Icc le_rfl ht.2))).sub continuousOn_const).sub
        (by fun_prop)).sub (by fun_prop)
    have hbd : ∀ x ∈ Ico t₀ t, ‖g x - g t₀ - (x - t₀) • dg t₀‖ ≤ M * h ^ 2 := by
      intro x hx
      have hx' : x ∈ Icc t₀ t₁ := ⟨hx.1, hx.2.le.trans ht.2⟩
      refine (hg.taylor h0 hx').trans (mul_le_mul_of_nonneg_left ?_ hM)
      have h5 : x - t₀ ≤ h := by linarith [hx'.2]
      exact pow_le_pow_left₀ (sub_nonneg.2 hx.1) h5 2
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd t ⟨ht.1, le_rfl⟩
    simpa using this
  have hR : ‖g t₁ - g t₀ - h • dg t₀‖ ≤ M * h ^ 2 := by
    have := hg.taylor h0 h1
    rwa [hd] at this
  have hTm := hT tm hm
  have hT₁ := hT t₁ h1
  rw [hdm] at hTm
  rw [hd] at hT₁
  obtain ⟨Tm, hTmd⟩ : ∃ Tm, Tm = A tm - A t₀ - (h / 2) • g t₀ - ((h / 2) ^ 2 / 2) • dg t₀ :=
    ⟨_, rfl⟩
  obtain ⟨T₁, hT₁d⟩ : ∃ T₁, T₁ = A t₁ - A t₀ - h • g t₀ - (h ^ 2 / 2) • dg t₀ := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = g t₁ - g t₀ - h • dg t₀ := ⟨_, rfl⟩
  rw [← hTmd] at hTm
  rw [← hT₁d] at hT₁
  rw [← hRd] at hR
  have hscale : ∀ {c : ℝ}, 0 ≤ c → ‖c • R‖ ≤ c * (M * h ^ 2) := fun hc => by
    rw [norm_smul, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hR hc
  have hg₁ : g t₁ = g t₀ + h • dg t₀ + R := by rw [hRd]; abel
  constructor
  · have e : (A tm - A t₀) - ((3 * h / 8) • g t₀ + (h / 8) • g t₁) = Tm - (h / 8) • R := by
      rw [hg₁, hTmd]; module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h3 := hscale (c := h / 8) (by positivity)
    have h4 : 0 ≤ M * h ^ 3 := by positivity
    nlinarith
  · have e : (A t₁ - A tm) - ((h / 8) • g t₀ + (3 * h / 8) • g t₁) = T₁ - Tm - (3 * h / 8) • R := by
      rw [hg₁, hTmd, hT₁d]; module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h3 := hscale (c := 3 * h / 8) (by positivity)
    have h4 := norm_sub_le T₁ Tm
    have h5 : 0 ≤ M * h ^ 3 := by positivity
    nlinarith

/-- Real arithmetic behind the predictor bound in `explicit_step_estimate`. -/
private theorem predictor_arith {a₁ a₂ κ L p₁ h δ Cw : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ)
    (hL : 0 ≤ L) (hp₁0 : 0 ≤ p₁) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hCw : Cw = 4 * κ * (1 + L + a₁ + a₂) * a₁ + p₁ * a₁ + a₂ + L + (a₁ + L) * (2 * κ + p₁)) :
    δ + h * (L * δ) + a₂ * h ^ 2
        + h * ((4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * (L * δ)) + p₁ * h) * a₁
          + (a₂ * h + L * δ) + (a₁ + L * δ) * (2 * κ * δ + p₁ * h))
      ≤ (1 + (L + Cw)) * δ + (a₂ + Cw) * h ^ 2 := by
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  have hsq : h ^ 2 ≤ h := pow_le_of_le_one hh hh1 two_ne_zero
  obtain ⟨x, hx⟩ : ∃ x, x = δ + h := ⟨_, rfl⟩
  have hδx : δ ≤ x := by rw [hx]; linarith
  have hhx : h ≤ x := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hT1 : δ + a₁ * h + a₂ * h ^ 2 + h * (L * δ) ≤ (1 + L + a₁ + a₂) * x := by
    have e1 : a₁ * h ≤ a₁ * x := mul_le_mul_of_nonneg_left hhx ha₁
    have e2 : a₂ * h ^ 2 ≤ a₂ * x := mul_le_mul_of_nonneg_left (hsq.trans hhx) ha₂
    have e3 : h * (L * δ) ≤ L * x := by
      have e4 : h * (L * δ) ≤ 1 * (L * δ) :=
        mul_le_mul_of_nonneg_right hh1 (by positivity)
      have e5 : L * δ ≤ L * x := mul_le_mul_of_nonneg_left hδx hL
      linarith
    have e6 : (1 + L + a₁ + a₂) * x = x + L * x + a₁ * x + a₂ * x := by ring
    linarith
  have hW : (4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * (L * δ)) + p₁ * h) * a₁ + (a₂ * h + L * δ)
      + (a₁ + L * δ) * (2 * κ * δ + p₁ * h) ≤ Cw * x := by
    have e1 : 4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * (L * δ)) ≤ 4 * κ * ((1 + L + a₁ + a₂) * x) :=
      mul_le_mul_of_nonneg_left hT1 (by positivity)
    have e2 : p₁ * h ≤ p₁ * x := mul_le_mul_of_nonneg_left hhx hp₁0
    have e3 : (4 * κ * (δ + a₁ * h + a₂ * h ^ 2 + h * (L * δ)) + p₁ * h) * a₁
        ≤ (4 * κ * ((1 + L + a₁ + a₂) * x) + p₁ * x) * a₁ :=
      mul_le_mul_of_nonneg_right (by linarith) ha₁
    have e4 : a₂ * h + L * δ ≤ (a₂ + L) * x := by
      have e5 : a₂ * h ≤ a₂ * x := mul_le_mul_of_nonneg_left hhx ha₂
      have e6 : L * δ ≤ L * x := mul_le_mul_of_nonneg_left hδx hL
      have e7 : (a₂ + L) * x = a₂ * x + L * x := by ring
      linarith
    have e5 : (a₁ + L * δ) * (2 * κ * δ + p₁ * h) ≤ (a₁ + L) * ((2 * κ + p₁) * x) := by
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · have e6 : L * δ ≤ L * 1 := mul_le_mul_of_nonneg_left hδ1 hL
        linarith
      · have e6 : 2 * κ * δ ≤ 2 * κ * x := mul_le_mul_of_nonneg_left hδx (by positivity)
        have e8 : p₁ * h ≤ p₁ * x := mul_le_mul_of_nonneg_left hhx hp₁0
        have e7 : (2 * κ + p₁) * x = 2 * κ * x + p₁ * x := by ring
        linarith
    have e6 : Cw * x = (4 * κ * ((1 + L + a₁ + a₂) * x) + p₁ * x) * a₁ + (a₂ + L) * x
        + (a₁ + L) * ((2 * κ + p₁) * x) := by rw [hCw]; ring
    linarith
  have e1 := mul_le_mul_of_nonneg_left hW hh
  have e2 : h * (Cw * x) = h * Cw * δ + Cw * h ^ 2 := by rw [hx]; ring
  have hC : 0 ≤ L + Cw := by positivity
  have e3 : h * (L + Cw) * δ ≤ 1 * (L + Cw) * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh1 hC) hδ0
  have e4 : h * (L * δ) + h * Cw * δ = h * (L + Cw) * δ := by ring
  have e5 : a₂ * h ^ 2 + Cw * h ^ 2 = (a₂ + Cw) * h ^ 2 := by ring
  have e6 : (1 + (L + Cw)) * δ = δ + 1 * (L + Cw) * δ := by ring
  linarith

/-- One step of the explicit method of arXiv 1301.1058, §3.4, against the exact solution of
`Ẏ = P(Y) F(Y)`, with `g` the exact right-hand side, `g(t) = F(Y(t))`, from a start that is
`δ`-close to `Y(t₀)`: the recursion `e⁺ ≤ (1 + K h) e + c h³`. -/
theorem explicit_step_estimate {a₁ a₂ κ L M : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ K c s : ℝ, 0 ≤ K ∧ 0 ≤ c ∧ 0 < s ∧ s ≤ 1 ∧ ∀ (F : Matrix m n ℝ → Matrix m n ℝ)
      (g dg : ℝ → Matrix m n ℝ) (U : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ)
      (V : ℝ → Matrix n r ℝ) (t₀ t₁ h δ : ℝ) (U₀ Up Um U₁ : Matrix m r ℝ)
      (S₀ Ŝp Sp Ŝm Ŝ₁ S₁ : Matrix r r ℝ) (V₀ Vp V₁ : Matrix n r ℝ),
      (∀ X Y, ‖F X - F Y‖ ≤ L * ‖X - Y‖) → (∀ t, g t = F (U t * S t * (V t)ᵀ)) →
      0 ≤ h → h ≤ s → t₁ = t₀ + h → δ ≤ s →
      IsFactorSolution g κ t₀ t₁ U S V → (∀ t ∈ Icc t₀ t₁, ‖g t‖ ≤ a₁) → IsC11 g dg t₀ t₁ a₂ M →
      IsExplicitStep F h U₀ S₀ V₀ Up Ŝp Sp Vp Um Ŝm V₁ Ŝ₁ U₁ S₁ → V₀ᵀ * V₀ = 1 →
      ‖U₀ * S₀ * V₀ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ δ →
      ‖U₁ * S₁ * V₁ᵀ - U t₁ * S t₁ * (V t₁)ᵀ‖ ≤ (1 + K * h) * δ + c * h ^ 3 := by
  have hK₀ := strK_nonneg ha₁ ha₂ hκ
  have hC₀ := strC_nonneg ha₁ ha₂ hκ
  have hs₀p := strS_pos ha₁ hκ
  have hs₀1 := strS_le_one ha₁ hκ
  obtain ⟨hs₀a, hs₀b⟩ := strS_mul_le ha₁ hκ
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = strP a₁ κ := ⟨_, rfl⟩
  have hp₁' : p₁ = 2 * a₁ * κ := by rw [hp₁, strP]
  have hp₁0 : 0 ≤ p₁ := by rw [hp₁']; positivity
  rw [← hp₁] at hs₀b
  obtain ⟨K₀, hK₀d⟩ : ∃ K₀, K₀ = strK a₁ a₂ κ := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀d⟩ : ∃ c₀, c₀ = strK a₁ a₂ κ + strC a₁ a₂ κ := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀d]; positivity
  rw [← hK₀d] at hK₀
  obtain ⟨s₀, hs₀d⟩ : ∃ s₀, s₀ = strS a₁ κ := ⟨_, rfl⟩
  rw [← hs₀d] at hs₀p hs₀1 hs₀a hs₀b
  obtain ⟨Cw, hCw⟩ : ∃ Cw, Cw = 4 * κ * (1 + L + a₁ + a₂) * a₁ + p₁ * a₁ + a₂ + L
      + (a₁ + L) * (2 * κ + p₁) := ⟨_, rfl⟩
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = L + Cw := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = a₂ + Cw := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  obtain ⟨C₃, hC₃⟩ : ∃ C₃, C₃ = L * (1 + C₁) / 2 := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄⟩ : ∃ C₄, C₄ = 2 * M + L * C₂ / 2 := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; positivity
  have hdenom : 1 ≤ 1 + C₃ + C₄ := by linarith
  have hdp : 0 < 1 + C₃ + C₄ := by linarith
  refine ⟨K₀ + (4 + K₀) * C₃, (4 + K₀) * C₄ + c₀, s₀ / (1 + C₃ + C₄), by positivity,
    by positivity, by positivity, (div_le_self hs₀p.le hdenom).trans hs₀1, ?_⟩
  intro F g dg U S V t₀ t₁ h δ U₀ Up Um U₁ S₀ Ŝp Sp Ŝm Ŝ₁ S₁ V₀ Vp V₁ hF hgF hh hhs ht₁ hδs hfac hgb
    hg hstep hV₀ hδ
  obtain ⟨s, hsd⟩ : ∃ s, s = s₀ / (1 + C₃ + C₄) := ⟨_, rfl⟩
  rw [← hsd] at hhs hδs
  have hss₀ : s ≤ s₀ := by rw [hsd]; exact div_le_self hs₀p.le hdenom
  have hsmul : s * (1 + C₃ + C₄) = s₀ := by rw [hsd]; field_simp
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hs0 : 0 ≤ s := hδ0.trans hδs
  have hh1 : h ≤ 1 := hhs.trans (hss₀.trans hs₀1)
  have hδ1 : δ ≤ 1 := hδs.trans (hss₀.trans hs₀1)
  have ht₀₁ : t₀ ≤ t₁ := by rw [ht₁]; linarith
  have hsq : h ^ 2 ≤ h := pow_le_of_le_one hh hh1 two_ne_zero
  have hsq0 : 0 ≤ h ^ 2 := by positivity
  obtain ⟨A, hAc, hAd⟩ := exists_antiderivative ht₀₁ hg.cont
  have hA : IsC11 A g t₀ t₁ a₁ a₂ :=
    ⟨hAc, hAd, hgb, fun _ hs' _ ht' => hg.norm_sub_le hs' ht', ha₁, ha₂⟩
  have h0 : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht₀₁⟩
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht₀₁, le_rfl⟩
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = U₀ * S₀ * V₀ᵀ := ⟨_, rfl⟩
  have hpred := hstep.predictor
  have hcorr := hstep.corrector
  rw [← hY₀] at hpred hcorr hδ
  obtain ⟨F₀, hF₀⟩ : ∃ F₀, F₀ = F Y₀ := ⟨_, rfl⟩
  rw [← hF₀] at hpred hcorr
  obtain ⟨Ypr, hYpr⟩ : ∃ Ypr, Ypr = Up * Sp * Vpᵀ := ⟨_, rfl⟩
  rw [← hYpr] at hcorr
  obtain ⟨F₁, hF₁⟩ : ∃ F₁, F₁ = F Ypr := ⟨_, rfl⟩
  rw [← hF₁] at hcorr
  have hf₀ : ‖F₀ - g t₀‖ ≤ L * δ := by
    rw [hF₀, hgF]
    exact (hF _ _).trans (mul_le_mul_of_nonneg_left hδ hL)
  have hsm : 2 * κ * δ + p₁ * h ≤ 1 / 2 := by
    have h2 : 2 * κ * δ ≤ 2 * κ * s₀ := mul_le_mul_of_nonneg_left (hδs.trans hss₀) (by positivity)
    have h3 : p₁ * h ≤ p₁ * s₀ := mul_le_mul_of_nonneg_left (hhs.trans hss₀) hp₁0
    linarith
  have hp := predictor_estimate hκ hh ht₁ hp₁' hfac hA hpred hV₀ (by rw [← hY₀]; exact hδ) hf₀ hsm
  rw [← hYpr] at hp
  obtain ⟨D, hD⟩ : ∃ D, D = (1 + C₁) * δ + C₂ * h ^ 2 := ⟨_, rfl⟩
  have hδD : δ ≤ D := by
    rw [hD]
    have e1 : 0 ≤ C₁ * δ := by positivity
    have e2 : 0 ≤ C₂ * h ^ 2 := by positivity
    have e3 : (1 + C₁) * δ = δ + C₁ * δ := by ring
    linarith only [e1, e2, e3]
  have hep : ‖Ypr - U t₁ * S t₁ * (V t₁)ᵀ‖ ≤ D := by
    refine hp.trans ?_
    rw [hD, hC₁, hC₂]
    exact predictor_arith ha₁ ha₂ hκ hL hp₁0 hh hh1 hδ0 hδ1 hCw
  -- the data of the corrector
  have hfp : ‖F₁ - g t₁‖ ≤ L * D := by
    rw [hF₁, hgF]
    exact (hF _ _).trans (mul_le_mul_of_nonneg_left hep hL)
  have hf₀D : ‖F₀ - g t₀‖ ≤ L * D := hf₀.trans (mul_le_mul_of_nonneg_left hδD hL)
  obtain ⟨hinc₁, hinc₂⟩ := increments_estimate hh rfl ht₁ hA hg
  obtain ⟨η, hη⟩ : ∃ η, η = h / 2 * (L * D) + 2 * M * h ^ 3 := ⟨_, rfl⟩
  have hbase : ∀ {α β : ℝ} {Δ : Matrix m n ℝ} {w : ℝ}, 0 ≤ α → 0 ≤ β → α + β = h / 2 →
      ‖Δ - (α • g t₀ + β • g t₁)‖ ≤ w → w ≤ 2 * M * h ^ 3 →
      ‖(α • F₀ + β • F₁) - Δ‖ ≤ η := by
    intro α β Δ w hα hβ hαβ h2 h3
    have e : (α • F₀ + β • F₁) - Δ = α • (F₀ - g t₀) + β • (F₁ - g t₁)
        - (Δ - (α • g t₀ + β • g t₁)) := by
      rw [smul_sub, smul_sub]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖α • (F₀ - g t₀)‖ ≤ α * (L * D) := by
      rw [norm_smul, Real.norm_of_nonneg hα]; exact mul_le_mul_of_nonneg_left hf₀D hα
    have e2 : ‖β • (F₁ - g t₁)‖ ≤ β * (L * D) := by
      rw [norm_smul, Real.norm_of_nonneg hβ]; exact mul_le_mul_of_nonneg_left hfp hβ
    have e3 := norm_add_le (α • (F₀ - g t₀)) (β • (F₁ - g t₁))
    have e4 : α * (L * D) + β * (L * D) = h / 2 * (L * D) := by rw [← hαβ]; ring
    rw [hη]
    linarith
  have hM3 : 0 ≤ M * h ^ 3 := by positivity
  have hη₁ : ‖(surrogate Y₀ F₀ F₁ h (1 / 2) - surrogate Y₀ F₀ F₁ h 0)
      - (A (t₀ + h / 2) - A t₀)‖ ≤ η := by
    rw [surrogate_half_sub]
    exact hbase (by positivity) (by positivity) (by ring) hinc₁ (by linarith)
  have hη₂ : ‖(surrogate Y₀ F₀ F₁ h 1 - surrogate Y₀ F₀ F₁ h (1 / 2))
      - (A t₁ - A (t₀ + h / 2))‖ ≤ η := by
    rw [surrogate_one_sub]
    exact hbase (by positivity) (by positivity) (by ring) hinc₂ le_rfl
  have hηform : η = h * C₃ * δ + C₄ * h ^ 3 := by
    rw [hη, hD, hC₃, hC₄]; ring
  have hη0 : 0 ≤ η := by rw [hηform]; positivity
  have hηs : η ≤ s₀ := by
    have e1 : h * C₃ * δ ≤ s * C₃ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hhs hC₃0) hδ1 hδ0 (by positivity)
    have e2 : C₄ * h ^ 3 ≤ C₄ * s := by
      refine mul_le_mul_of_nonneg_left ?_ hC₄0
      exact (pow_le_of_le_one hh hh1 (by norm_num)).trans hhs
    have e3 : s * (1 + C₃ + C₄) = s + s * C₃ + s * C₄ := by ring
    have e4 : s * C₃ * 1 = s * C₃ := by ring
    have e5 : C₄ * s = s * C₄ := by ring
    rw [hηform]
    linarith only [e1, e2, e3, e4, e5, hsmul, hs0]
  have hbound := strang_step_bound (δ := δ) (η := η) (tm := t₀ + h / 2) hκ hh rfl ht₁ hfac hA hcorr
    hV₀ (by rw [← hY₀]; exact hδ) hη₁ hη₂ (by rw [← hs₀d]; linarith)
    (by rw [← hs₀d]; linarith) (by rw [← hs₀d]; exact hηs)
  rw [← hc₀d, ← hK₀d] at hbound
  refine hbound.trans ?_
  have e1 : (4 + K₀ * h) * η ≤ (4 + K₀) * η := by
    refine mul_le_mul_of_nonneg_right ?_ hη0
    have : K₀ * h ≤ K₀ * 1 := mul_le_mul_of_nonneg_left hh1 hK₀
    linarith
  have e2 : (1 + (K₀ + (4 + K₀) * C₃) * h) * δ + ((4 + K₀) * C₄ + c₀) * h ^ 3
      = (1 + K₀ * h) * δ + (4 + K₀) * (h * C₃ * δ + C₄ * h ^ 3) + c₀ * h ^ 3 := by ring
  rw [e2, ← hηform]
  linarith

/-- **The explicit method has local error `O(h³)`** (arXiv 1301.1058, §3.4: "an explicit method
of order 2").  Let `F` be Lipschitz with
constant `L`, and let `Y = U S Vᵀ` solve `Ẏ = P(Y) F(Y)` on `[t₀, t₀ + h]`, i.e. the system (5)
with `Ȧ(t) = F(Y(t))`, with `‖S(t)⁻¹‖ ≤ κ`, `‖F(Y(t))‖ ≤ a₁`, and such that `g = F ∘ Y` is
`C^{1,1}`: `‖ġ‖ ≤ a₂`, `ġ` Lipschitz with constant `M`.  Then there are
`c` and `s > 0`, depending only on `a₁`, `a₂`, `κ`, `L`, `M`, such that one step of the method
(`IsExplicitStep`) with `0 ≤ h ≤ s`, from any factorization `U₀ S₀ V₀ᵀ = Y(t₀)` with `V₀ᵀ V₀ = I`,
satisfies `‖Y₁ - Y(t₀ + h)‖ ≤ c h³`.

The paper states no regularity assumption and no proof.  Here the regularity is imposed on the
exact solution through `g`, which holds for `F ∈ C^{1,1}`.  The primitive `A` of `g` is the matrix
to which (12) would have to be applied.  The proof compares the surrogate with `A`
(`increments_estimate`), and uses `strang_step_bound` for perturbed data. -/
theorem explicit_local_error {a₁ a₂ κ L M : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ c s : ℝ, 0 ≤ c ∧ 0 < s ∧ ∀ (F : Matrix m n ℝ → Matrix m n ℝ) (dg : ℝ → Matrix m n ℝ)
      (U : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ) (V : ℝ → Matrix n r ℝ) (t₀ h : ℝ)
      (U₀ Up Um U₁ : Matrix m r ℝ) (S₀ Ŝp Sp Ŝm Ŝ₁ S₁ : Matrix r r ℝ) (V₀ Vp V₁ : Matrix n r ℝ),
      (∀ X Y, ‖F X - F Y‖ ≤ L * ‖X - Y‖) → 0 ≤ h → h ≤ s →
      IsFactorSolution (fun t => F (U t * S t * (V t)ᵀ)) κ t₀ (t₀ + h) U S V →
      (∀ t ∈ Icc t₀ (t₀ + h), ‖F (U t * S t * (V t)ᵀ)‖ ≤ a₁) →
      IsC11 (fun t => F (U t * S t * (V t)ᵀ)) dg t₀ (t₀ + h) a₂ M →
      IsExplicitStep F h U₀ S₀ V₀ Up Ŝp Sp Vp Um Ŝm V₁ Ŝ₁ U₁ S₁ → V₀ᵀ * V₀ = 1 →
      U₀ * S₀ * V₀ᵀ = U t₀ * S t₀ * (V t₀)ᵀ →
      ‖U₁ * S₁ * V₁ᵀ - U (t₀ + h) * S (t₀ + h) * (V (t₀ + h))ᵀ‖ ≤ c * h ^ 3 := by
  obtain ⟨K, c, s, -, hc, hs, -, hstep⟩ :=
    explicit_step_estimate (m := m) (n := n) (r := r) ha₁ ha₂ hκ hL hM
  refine ⟨c, s, hc, hs, ?_⟩
  intro F dg U S V t₀ h U₀ Up Um U₁ S₀ Ŝp Sp Ŝm Ŝ₁ S₁ V₀ Vp V₁ hF hh hhs hfac hgb hg hexp hV₀ hY₀
  have h1 := hstep F _ dg U S V t₀ (t₀ + h) h 0 U₀ Up Um U₁ S₀ Ŝp Sp Ŝm Ŝ₁ S₁ V₀ Vp V₁ hF
    (fun _ => rfl) hh hhs rfl hs.le hfac hgb hg hexp hV₀ (by rw [hY₀, sub_self, norm_zero])
  simpa using h1

/-- `N` steps of the explicit method of arXiv 1301.1058, §3.4, with step size `h`. -/
structure IsExplicitRun (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (N : ℕ)
    (U Up Um : ℕ → Matrix m r ℝ) (S Ŝp Sp Ŝm Ŝ : ℕ → Matrix r r ℝ)
    (W Vp : ℕ → Matrix n r ℝ) : Prop where
  orthV₀ : (W 0)ᵀ * W 0 = 1
  step : ∀ k < N, IsExplicitStep F h (U k) (S k) (W k) (Up k) (Ŝp k) (Sp k) (Vp k) (Um k) (Ŝm k)
    (W (k + 1)) (Ŝ k) (U (k + 1)) (S (k + 1))

omit [DecidableEq m] [DecidableEq n] in
/-- A run of the explicit method has orthonormal right factors. -/
private theorem IsExplicitRun.orthV {F : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ} {N : ℕ}
    {U Up Um : ℕ → Matrix m r ℝ} {S Ŝp Sp Ŝm Ŝ : ℕ → Matrix r r ℝ} {W Vp : ℕ → Matrix n r ℝ}
    (hrun : IsExplicitRun F h N U Up Um S Ŝp Sp Ŝm Ŝ W Vp) : ∀ k ≤ N, (W k)ᵀ * W k = 1 := by
  intro k hk
  cases k with
  | zero => exact hrun.orthV₀
  | succ k => exact (hrun.step k hk).corrector.orthV₁

/-- **The explicit method converges with order two** (arXiv 1301.1058, §3.4).  Under the
assumptions of `explicit_local_error` on `[t₀, T]`,
there are `C` and `s > 0`, depending only on `a₁`, `a₂`, `κ`, `L`, `M` and `T - t₀`, such that
every run with step size `0 ≤ h ≤ s`, `t₀ + N h ≤ T`, from a starting value within `s` of `Y(t₀)`,
satisfies

    ‖Yₙ - Y(tₙ)‖ ≤ C (‖Y₀ - Y(t₀)‖ + h²)        (n ≤ N).

The paper states only "an explicit method of order 2"; assumptions as in `explicit_local_error`. -/
theorem explicit_global_error {a₁ a₂ κ L M t₀ T : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hκ : 0 ≤ κ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hT : t₀ ≤ T) :
    ∃ C s : ℝ, 0 ≤ C ∧ 0 < s ∧ ∀ (F : Matrix m n ℝ → Matrix m n ℝ) (dg : ℝ → Matrix m n ℝ)
      (U : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ) (V : ℝ → Matrix n r ℝ) (h : ℝ) (N : ℕ)
      (Ur Up Um : ℕ → Matrix m r ℝ) (Sr Ŝp Sp Ŝm Ŝ : ℕ → Matrix r r ℝ)
      (Vr Vp : ℕ → Matrix n r ℝ),
      (∀ X Y, ‖F X - F Y‖ ≤ L * ‖X - Y‖) → 0 ≤ h → h ≤ s → t₀ + N * h ≤ T →
      IsFactorSolution (fun t => F (U t * S t * (V t)ᵀ)) κ t₀ T U S V →
      (∀ t ∈ Icc t₀ T, ‖F (U t * S t * (V t)ᵀ)‖ ≤ a₁) →
      IsC11 (fun t => F (U t * S t * (V t)ᵀ)) dg t₀ T a₂ M →
      IsExplicitRun F h N Ur Up Um Sr Ŝp Sp Ŝm Ŝ Vr Vp →
      ‖Ur 0 * Sr 0 * (Vr 0)ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ ≤ s →
      ∀ n ≤ N, ‖Ur n * Sr n * (Vr n)ᵀ - U (t₀ + n * h) * S (t₀ + n * h) * (V (t₀ + n * h))ᵀ‖ ≤
        C * (‖Ur 0 * Sr 0 * (Vr 0)ᵀ - U t₀ * S t₀ * (V t₀)ᵀ‖ + h ^ 2) := by
  obtain ⟨K, c, s₀, hK0, hc0, hs0, hs₀1, hstep⟩ :=
    explicit_step_estimate (m := m) (n := n) (r := r) ha₁ ha₂ hκ hL hM
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = T - t₀ := ⟨_, rfl⟩
  have hτ : 0 ≤ τ := by rw [hτdef]; linarith
  obtain ⟨C, hC⟩ : ∃ C, C = Real.exp (K * τ) * (1 + τ * c) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; exact one_le_globalConst hK0 hc0 hτ
  refine ⟨C, s₀ / C, by linarith, div_pos hs0 (by linarith), ?_⟩
  intro F dg U S V h N Ur Up Um Sr Ŝp Sp Ŝm Ŝ Vr Vp hF hh hhs hN hfac hgb hg hrun hstart
  have hsC : s₀ / C ≤ s₀ := div_le_self hs0.le hC1
  have hgrid : ∀ {k : ℕ}, k ≤ N → t₀ + k * h ∈ Icc t₀ T := fun hk => grid_mem hh hN hk
  have hmain := global_of_recursion (s := s₀) (τ := τ) (N := N) (h := h)
    (e := fun k => ‖Ur k * Sr k * (Vr k)ᵀ - U (t₀ + k * h) * S (t₀ + k * h)
      * (V (t₀ + k * h))ᵀ‖) hK0 hc0 hτ hs0 hs₀1 hh (by rw [← hC]; exact hhs)
    (by simpa [hC] using hstart) (fun _ => norm_nonneg _)
    (fun n hn => by
      have := (hgrid hn).2
      rw [hτdef]; linarith)
    (fun k hk hek => by
      have hk1 := hgrid hk.le
      have hk2 := hgrid (k := k + 1) hk
      have hk2' : t₀ + (k : ℝ) * h + h = t₀ + ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
      have hle : t₀ + (k : ℝ) * h + h ≤ T := by rw [hk2']; exact hk2.2
      have h1 := hstep F _ dg U S V (t₀ + k * h) (t₀ + k * h + h) h _ (Ur k) (Up k) (Um k)
        (Ur (k + 1)) (Sr k) (Ŝp k) (Sp k) (Ŝm k) (Ŝ k) (Sr (k + 1)) (Vr k) (Vp k) (Vr (k + 1)) hF
        (fun _ => rfl) hh (by linarith) rfl hek (hfac.mono hk1.1 hle)
        (fun t ht => hgb t ⟨hk1.1.trans ht.1, ht.2.trans hle⟩) (hg.mono hk1.1 hle)
        (hrun.step k hk) (hrun.orthV k hk.le) le_rfl
      rw [hk2'] at h1
      exact h1)
  intro n hn
  have h2 := hmain n hn
  simp only [Nat.cast_zero, zero_mul, add_zero] at h2
  rw [hC]
  exact h2

end ExplicitMethod

/-! ### Non-vacuity of the second-order results -/

section NonVacuitySecondOrder

omit [DecidableEq m] [DecidableEq n] in
/-- One step of the scheme (12) of arXiv 1301.1058 exists for `r ≤ m, n`, also for rank-deficient
`K`, `L`. -/
theorem exists_strang_step {r : ℕ} (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (A₀ Am A₁ : Matrix m n ℝ) (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (V₀ : Matrix n (Fin r) ℝ) :
    ∃ (Um : Matrix m (Fin r) ℝ) (Ŝm : Matrix (Fin r) (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ)
      (Ŝ₁ : Matrix (Fin r) (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsStrangStep A₀ Am A₁ U₀ S₀ V₀ Um Ŝm V₁ Ŝ₁ U₁ S₁ := by
  obtain ⟨Um, Ŝm, hUm, hKm⟩ := MatrixKSL.exists_qr (U₀ * S₀ + (Am - A₀) * V₀) hm
  obtain ⟨V₁, R, hV₁, hL⟩ :=
    MatrixKSL.exists_qr (V₀ * (Ŝm - Umᵀ * (Am - A₀) * V₀)ᵀ + (A₁ - A₀)ᵀ * Um) hn
  obtain ⟨U₁, S₁, hU₁, hK⟩ :=
    MatrixKSL.exists_qr (Um * (Rᵀ - Umᵀ * (A₁ - Am) * V₁) + (A₁ - Am) * V₁) hm
  exact ⟨Um, Ŝm, V₁, Rᵀ, U₁, S₁, hUm, hKm.symm, hV₁,
    by rw [Matrix.transpose_transpose]; exact hL.symm, hU₁, hK.symm⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Runs of the scheme (12) of arXiv 1301.1058 exist from every starting factorization with
orthonormal `V₀`, for `r ≤ m, n`. -/
theorem exists_strang_run {r : ℕ} (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (A : ℝ → Matrix m n ℝ) (t₀ h : ℝ) (N : ℕ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (U Um : ℕ → Matrix m (Fin r) ℝ) (S Ŝm Ŝ : ℕ → Matrix (Fin r) (Fin r) ℝ)
      (W : ℕ → Matrix n (Fin r) ℝ),
      U 0 = U₀ ∧ S 0 = S₀ ∧ W 0 = V₀ ∧ IsStrangRun A t₀ h N U Um S Ŝm Ŝ W := by
  let St := Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ
  let Aux := Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ
  have hstep : ∀ (k : ℕ) (x : St), ∃ (y : St) (z : Aux),
      IsStrangStep (A (t₀ + k * h)) (A (t₀ + k * h + h / 2)) (A (t₀ + k * h + h)) x.1 x.2.1 x.2.2
        z.1 z.2.1 y.2.2 z.2.2 y.1 y.2.1 := by
    intro k x
    obtain ⟨Um, Ŝm, V₁, Ŝ₁, U₁, S₁, hs⟩ := exists_strang_step hm hn (A (t₀ + k * h))
      (A (t₀ + k * h + h / 2)) (A (t₀ + k * h + h)) x.1 x.2.1 x.2.2
    exact ⟨(U₁, S₁, V₁), (Um, Ŝm, Ŝ₁), hs⟩
  choose f g hfg using hstep
  let s : ℕ → St := fun k => Nat.rec (U₀, S₀, V₀) (fun k x => f k x) k
  exact ⟨fun k => (s k).1, fun k => (g k (s k)).1, fun k => (s k).2.1,
    fun k => (g k (s k)).2.1, fun k => (g k (s k)).2.2, fun k => (s k).2.2, rfl, rfl, rfl,
    ⟨hV₀, fun k _ => hfg k (s k)⟩⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Runs of the explicit method of arXiv 1301.1058, §3.4, exist from every starting factorization
with orthonormal `V₀`, for `r ≤ m, n`. -/
theorem exists_explicit_run {r : ℕ} (hm : r ≤ Fintype.card m) (hn : r ≤ Fintype.card n)
    (F : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ) (N : ℕ) (U₀ : Matrix m (Fin r) ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ) (hV₀ : V₀ᵀ * V₀ = 1) :
    ∃ (U Up Um : ℕ → Matrix m (Fin r) ℝ) (S Ŝp Sp Ŝm Ŝ : ℕ → Matrix (Fin r) (Fin r) ℝ)
      (W Vp : ℕ → Matrix n (Fin r) ℝ),
      U 0 = U₀ ∧ S 0 = S₀ ∧ W 0 = V₀ ∧ IsExplicitRun F h N U Up Um S Ŝp Sp Ŝm Ŝ W Vp := by
  let St := Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix n (Fin r) ℝ
  let Aux := Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ ×
    Matrix n (Fin r) ℝ × Matrix m (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ ×
    Matrix (Fin r) (Fin r) ℝ
  have hstep : ∀ (x : St), ∃ (y : St) (z : Aux), IsExplicitStep F h x.1 x.2.1 x.2.2 z.1 z.2.1
      z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 y.2.2 z.2.2.2.2.2.2 y.1 y.2.1 := by
    intro x
    obtain ⟨Up, Ŝp, Sp, Vp, hp, -⟩ :=
      exists_ksl_step hm hn 0 (h • F (x.1 * x.2.1 * x.2.2ᵀ)) x.1 x.2.1 x.2.2
    obtain ⟨Um, Ŝm, V₁, Ŝ₁, U₁, S₁, hs⟩ := exists_strang_step hm hn
      (surrogate (x.1 * x.2.1 * x.2.2ᵀ) (F (x.1 * x.2.1 * x.2.2ᵀ)) (F (Up * Sp * Vpᵀ)) h 0)
      (surrogate (x.1 * x.2.1 * x.2.2ᵀ) (F (x.1 * x.2.1 * x.2.2ᵀ)) (F (Up * Sp * Vpᵀ)) h (1 / 2))
      (surrogate (x.1 * x.2.1 * x.2.2ᵀ) (F (x.1 * x.2.1 * x.2.2ᵀ)) (F (Up * Sp * Vpᵀ)) h 1)
      x.1 x.2.1 x.2.2
    exact ⟨(U₁, S₁, V₁), (Up, Ŝp, Sp, Vp, Um, Ŝm, Ŝ₁), ⟨hp, hs⟩⟩
  choose f g hfg using hstep
  let s : ℕ → St := fun k => Nat.rec (U₀, S₀, V₀) (fun _ x => f x) k
  exact ⟨fun k => (s k).1, fun k => (g (s k)).1, fun k => (g (s k)).2.2.2.2.1, fun k => (s k).2.1,
    fun k => (g (s k)).2.1, fun k => (g (s k)).2.2.1, fun k => (g (s k)).2.2.2.2.2.1,
    fun k => (g (s k)).2.2.2.2.2.2, fun k => (s k).2.2, fun k => (g (s k)).2.2.2.1, rfl, rfl, rfl,
    ⟨hV₀, fun k _ => hfg (s k)⟩⟩

omit [DecidableEq m] [DecidableEq n] in
/-- The inverse of a positive multiple of the identity. -/
private theorem exp_inv_smul (t : ℝ) :
    (Real.exp t • (1 : Matrix r r ℝ))⁻¹ = (Real.exp t)⁻¹ • (1 : Matrix r r ℝ) := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm, mul_inv_cancel₀ (Real.exp_ne_zero t), Matrix.one_mul, one_smul]

/-- A concrete solution of (5) of arXiv 1301.1058: for orthonormal `U₀`, `V₀`, the curve
`A(t) = eᵗ U₀ V₀ᵀ` of rank `r`
has the factors `U₀`, `eᵗ I`, `V₀`.  Since `A` is its own derivative and `Y = A`, this solves both
`Ẏ = P(Y) Ȧ` and `Ẏ = P(Y) F(Y)` with `F = id`. -/
theorem isFactorSolution_exp {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (b : ℝ) :
    IsFactorSolution (fun t => Real.exp t • (U₀ * V₀ᵀ)) ‖(1 : Matrix r r ℝ)‖ 0 b (fun _ => U₀)
      (fun t => Real.exp t • (1 : Matrix r r ℝ)) (fun _ => V₀) where
  solU := by
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    have h : (1 - U₀ * U₀ᵀ) * U₀ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU₀, Matrix.mul_one, sub_self]
    have h2 : (1 - U₀ * U₀ᵀ) * (Real.exp t • (U₀ * V₀ᵀ)) * V₀
        * (Real.exp t • (1 : Matrix r r ℝ))⁻¹ = 0 := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, Matrix.zero_mul, smul_zero, Matrix.zero_mul,
        Matrix.zero_mul]
    simp only [h2]
    exact hasDerivWithinAt_const _ _ _
  solS := by
    refine ⟨Continuous.continuousOn (by fun_prop), fun t _ => ?_⟩
    have h2 : U₀ᵀ * (Real.exp t • (U₀ * V₀ᵀ)) * V₀ = Real.exp t • 1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hU₀, Matrix.one_mul, hV₀]
    simp only [h2]
    exact ((Real.hasDerivAt_exp t).smul_const (1 : Matrix r r ℝ)).hasDerivWithinAt
  solV := by
    refine ⟨continuousOn_const, fun t _ => ?_⟩
    have h : (1 - V₀ * V₀ᵀ) * V₀ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV₀, Matrix.mul_one, sub_self]
    have h2 : (1 - V₀ * V₀ᵀ) * (Real.exp t • (U₀ * V₀ᵀ))ᵀ * U₀
        * ((Real.exp t • (1 : Matrix r r ℝ))⁻¹)ᵀ = 0 := by
      rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
        ← Matrix.mul_assoc, h, Matrix.zero_mul, smul_zero, Matrix.zero_mul, Matrix.zero_mul]
    simp only [h2]
    exact hasDerivWithinAt_const _ _ _
  orthU _ _ := hU₀
  orthV _ _ := hV₀
  det t _ := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.2 (Real.exp_ne_zero t)).pow _
  core t ht := by
    rw [exp_inv_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Real.exp_pos t).le)]
    have h1 : (Real.exp t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_exp ht.1)
    exact mul_le_of_le_one_left (norm_nonneg _) h1

omit [DecidableEq m] [DecidableEq n] in
/-- The curve `eᵗ E` of `isFactorSolution_exp` (arXiv 1301.1058, non-vacuity) is `C^{1,1}` on
`[0, b]`. -/
theorem isC11_exp (E : Matrix m n ℝ) (b : ℝ) :
    IsC11 (fun t => Real.exp t • E) (fun t => Real.exp t • E) 0 b (Real.exp b * ‖E‖)
      (Real.exp b * ‖E‖) where
  cont := Continuous.continuousOn (by fun_prop)
  deriv t _ := ((Real.hasDerivAt_exp t).smul_const E).hasDerivWithinAt
  bound t ht := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos t).le]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht.2) (norm_nonneg _)
  lip s hs t ht := by
    have h1 : |Real.exp t - Real.exp s| ≤ Real.exp b * |t - s| := by
      have h2 := norm_sub_le_of_right_deriv (f := Real.exp) (f' := Real.exp) (a := 0) (b := b)
        (B := Real.exp b) Real.continuous_exp.continuousOn
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
        (fun x hx => by
          rw [Real.norm_of_nonneg (Real.exp_pos x).le]
          exact Real.exp_le_exp.2 hx.2.le) hs ht
      simpa only [Real.norm_eq_abs] using h2
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    calc _ ≤ Real.exp b * |t - s| * ‖E‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := by ring
  nn₁ := by positivity
  nn₂ := by positivity

/-- The hypotheses of `strang_local_error` and `strang_global_error` are satisfiable, and the local
bound applies to steps that exist by `exists_strang_step`: for `A(t) = eᵗ E` with `E = e₁ e₁ᵀ`, all
assumptions on the exact solution hold on `[0, 1]`, with a nonzero derivative and a nonzero
Lipschitz constant. -/
example : ∃ (E : Matrix (Fin 2) (Fin 2) ℝ) (U₀ V₀ : Matrix (Fin 2) (Fin 1) ℝ), E ≠ 0 ∧
    IsFactorSolution (fun t => Real.exp t • E) ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ 0 1
      (fun _ => U₀) (fun t => Real.exp t • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => V₀) ∧
    IsC11 (fun t => Real.exp t • E) (fun t => Real.exp t • E) 0 1 (Real.exp 1 * ‖E‖)
      (Real.exp 1 * ‖E‖) := by
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin 2) (Fin 1) ℝ, e = !![1; 0] := ⟨_, rfl⟩
  have hU : eᵀ * e = 1 := by
    rw [he]; ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨e * eᵀ, e, e, ?_, isFactorSolution_exp hU hU 1, isC11_exp _ 1⟩
  intro h0
  have := congrFun (congrFun h0 0) 0
  rw [he] at this
  simp [Matrix.mul_apply] at this

/-- The hypotheses of `explicit_local_error` and `explicit_global_error` are satisfiable: for
`F = id`, which is `1`-Lipschitz, and `Y(t) = eᵗ U₀ V₀ᵀ`, the curve `t ↦ F(Y(t))` solves (5) and is
`C^{1,1}`.  Steps and runs of the method exist by `exists_explicit_run`. -/
example {U₀ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (T : ℝ) :
    (∀ X Y : Matrix m n ℝ, ‖id X - id Y‖ ≤ 1 * ‖X - Y‖) ∧
    IsFactorSolution (fun t => id (U₀ * (Real.exp t • (1 : Matrix r r ℝ)) * V₀ᵀ))
      ‖(1 : Matrix r r ℝ)‖ 0 T (fun _ => U₀) (fun t => Real.exp t • (1 : Matrix r r ℝ))
      (fun _ => V₀) ∧
    IsC11 (fun t => id (U₀ * (Real.exp t • (1 : Matrix r r ℝ)) * V₀ᵀ))
      (fun t => Real.exp t • (U₀ * V₀ᵀ)) 0 T (Real.exp T * ‖U₀ * V₀ᵀ‖)
      (Real.exp T * ‖U₀ * V₀ᵀ‖) := by
  have h : (fun t => id (U₀ * (Real.exp t • (1 : Matrix r r ℝ)) * V₀ᵀ))
      = fun t => Real.exp t • (U₀ * V₀ᵀ) := by
    funext t
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [h]
  exact ⟨fun X Y => by simp, isFactorSolution_exp hU₀ hV₀ T, isC11_exp _ T⟩

end NonVacuitySecondOrder

end LeanDLRA.Literature.P1301_1058
