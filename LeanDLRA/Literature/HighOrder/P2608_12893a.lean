import Mathlib
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Existence
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.OpenProblems.Curated.HighOrderDefs

/-!
# The counterexample family of arXiv 2608.12893 (Strang projector splitting)

Zhang, *A counterexample to robust second-order convergence of the Strang projector-splitting
integrator*. The paper's family on `3 × 3` matrices is defined here exactly: `Fj j η t X =
M_η(X) + R_j(t)` with `M_η(X) = q_η(X) (Ω X - X Ω)`, `q_η(X) = (1 + η tanh x₃₁)/√(1 + ‖X‖_F²)`,
`Ω = E₃₁ - E₁₃`, the forcing `R_j(t) = h_j³ ϑ_j'(t) W'(ϑ_j(t))` with `W = ν νᵀ`,
`ν(θ) = (0, cos(πθ/4), sin(πθ/4))`, `h_j = 2^(-j²)`, the phase `ϑ_j` (`th`) switched off on
`[4 j h_j, 4 (j+1) h_j]` by `ψ(x) = x + 15x⁴ - 39x⁵ + 34x⁶ - 10x⁷`, and `Y⁰_j = E₁₁ + h_j³ E₂₂`.

## Main results

* Prop. 3.2 in full: `prop_3_2` (`B_F = 5`, `L_F = 12`, `‖M_η‖ ≤ 4`, tangency of `M_η` at every
  factored `Y = U S Vᵀ`, `‖R_j‖ ≤ ε_j = β √2 (π/4) h_j²`) and `prop_3_2_kappa`
  (`F_{j,η}(t, ·) ∈ C²`, `‖D²_X F‖ ≤ 123`, `∂_t F` independent of `X`, `‖∂_t F‖, ‖∂_t² F‖ ≤ 123`),
  with
  `β = ψ'(3/7) = max_{[0,1]} ψ'` (`dpsi_le_beta`, `dpsi_three_sevenths`), `ϑ_j' = dth`,
  `R_j = d/dt (h_j³ W(ϑ_j))` (`hasDerivAt_th`, `hasDerivAt_hW`); the singular values `1`, `h_j³`
  of `Y⁰_j` (`Y0_svd`), as stated in Thm 3.1.
* Lemma 4.3 (`lemma_4_3`: `‖Φ₊(4h_j) - Φ₋(4h_j) - 8 h_j² H‖ ≤ 10⁵ h_j³` for `j ≥ 3`; the flows
  exist by `exists_solution`) and the facts (3.4) = (4.18) at `E₁₁`: `M_±(E₁₁) = H/√2` (`Mη_E11`),
  `D(M₊ - M₋)(E₁₁)[Z] = √2 z₃₁ H` (`fderiv_Mη_sub_E11`, quantitative: `Mη_sub_taylor`).
* Eq. (5.16): `first_order_sum`, and `first_order_sum_Mη` for `M_η` at `Ȳ = U Vᵀ`.
* Lemma A.1 for the core factor fields `MatrixKSL.kField`, `lField`, `sField` with `F = M_η`:
  `det (Kᵀ K)`, `det (Lᵀ L)` and `det S` are constant, so K, L keep rank two and S stays
  nonsingular (`lemma_A_1_K`, `lemma_A_1_L`, `lemma_A_1_S`). With `R_j = 0` after the switch-off
  (`Rj_eq_zero`, `Fj_eq_of_ge`) this is the last step of Prop. 5.2
  (`prop_5_2_after_switchoff_KL`, `prop_5_2_after_switchoff_S`).
* Appendix A.2: the identities (A.2) (`nu_dot`, `W_mul_W`), `W(θ + 4) = W(θ)` (`W_add_four`) and
  the leading factor cycle (A.26) (`leading_cycle`): for the forcing alone, `R_h(t) = h² W'(t/h)`,
  an exact-subflow Strang step (the core `IsStrangKSLStep`) with the `h⁰` projectors
  `E₁₁ + W(ℓ)`, `E₁₁ + W(ℓ+½)`, `E₁₁ + W(ℓ+1)` of Lemma 4.1 maps `B(ℓ) Σ_h(1) B(ℓ)ᵀ` through
  `B(ℓ+½) Σ_h(cos(π/8)) B(ℓ)ᵀ` and `B(ℓ+½) Σ_h(cos(π/8)) B(ℓ+1)ᵀ` to `B(ℓ+1) Σ_h(1) B(ℓ+1)ᵀ`
  (`exists_leading_step` shows that the step exists).
* The mechanism of §5, for any Lipschitz field: `norm_flow_sub_sub_le` ((5.27)) and
  `norm_globalErr_sub_sum_le` (the global error is the sum of the block errors up to a factor
  `e^{L T} - 1`, (5.26)–(5.27)).

## Conditional results

* `prop_4_4_of_lemma_4_2`: Prop. 4.4, `‖τ_{0,+} - τ_{0,-} - (√2/16) h_j² E₁₂‖ ≤ (C + 10⁵) h_j³`,
  conditional on Lemma 4.2 (a hypothesis with constant `C`); Lemma 4.3 enters proved.
* `errSum_ge_of_blockErr`, `lower_bound_of_prop_5_1`, `not_robust_of_prop_5_1`: the lower bound
  (3.20) `max_η ‖Y^{4j}_{j,η} - A_{j,η}(4 j h_j)‖ ≥ (√2/64) j h_j²` for large `j`, and the failure
  of (2.11), conditional on (5.3)–(5.4) of Prop. 5.1, which are hypotheses on arbitrary block
  data `Y`, `Φ`. The hypotheses are consistent (`exists_blockData`, `prop_5_1_hyps_satisfiable`,
  with data that are not Strang iterates).

## Not proved

Lemma 4.1, Lemma 4.2, Prop. 4.4 and Prop. 5.1 for the Strang iterates of `F_{j,η}`, Prop. 5.2 on
the first `j + 1` blocks, and Lemmas A.2–A.3; hence the lower bound of Thm 3.1 holds here only
conditionally. These need second-order expansions of the nonlinear substep flows, whose projectors
are fixed by components of size `h_j³`; the paper controls them through the desingularized
coordinates of Appendix A with uniform `C³` bounds, which are not formalized. The conclusion of
Thm 3.1, that exact-subflow Strang splitting is not robustly second order, is proved in
`LeanDLRA.Corrections.strangKSL_not_robust_second_order_rankTwo` for a different, explicitly
solvable family, not for `F_{j,η}`.

## Core definitions

`ODESolution`, `IsBoundedField`, `IsLipschitzField`, `ODESolution.norm_sub_le_exp`,
`exists_ODESolution_of_continuousOn` (Foundations), the Frobenius norm and inner product
(`LeanDLRA.Frobenius`), `MatrixKSL.kField`, `sField`, `lField` (Integrators/Matrix),
`leftProj`, `rightProj`, `IsOrthProj` (Matrix/Projectors, Foundations/Projector) and
`IsStrangKSLStep` (OpenProblems/Curated/HighOrderDefs). The local definitions are the paper's
concrete objects (`Om`, `Hm`, `qη`, `Mη`, `nu`, `W`, `psi`, `th`, `Rj`, `Fj`, `Y0`, `Bm`, `Sig`,
`Rh`, ...); none duplicates a core concept. `norm_flow_sub_sub_le` and
`norm_globalErr_sub_sum_le` are general and belong in `Foundations/Gronwall`.

## Differences from the paper

`η` ranges over `|η| ≤ 1` (the paper: `η = ±1`) wherever the sign plays no role; the bounds hold
for every `t`, not only `t ∈ [0, 1]`, with `ϑ_j(t) = t / h_j` for `t < 0`, where the paper does
not define `ϑ_j`; Prop. 3.2 is proved for `j ≥ 1` (the paper: `j ≥ 3`). The paper's `‖DM_η‖ ≤ 10`
is `Mη_lipschitz`, its `‖D²M_η‖ ≤ 34` is proved with `27` (`norm_iteratedFDeriv_Mη_le`, via
`DM_lipschitz`); its bounds `|ψ''| ≤ 15`, `|ψ'''| ≤ 1110` are used as stated (the true maxima are
about `5.03` and `26.6`). The `O(h³)` of Lemma 4.3 is made explicit. `δ_j = 0` holds by
construction, the exact solution starting at `Y⁰_j`. Lemma A.1 is proved for full column rank
two (the paper: column rank in general, via `K(t) = e^{σΩ} K(t₀) e^{-σ Vᵀ Ω V}`). The cycle (A.26)
is stated for the matrices `U S Vᵀ`, not the factors. No claim of the paper was found to be
false.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2608_12893

open LeanDLRA

local notation "M₃" => Matrix (Fin 3) (Fin 3) ℝ

/-! ### Eq. (5.16) -/

/-- **Eq. (5.16)** (arXiv 2608.12893): the first-order sum of the five Strang substeps,
`½ M P₀ - ½ Q M P₀ + Q M - ½ Q M P₁ + ½ M P₁`, equals `M` whenever `(1 - Q) M` is fixed by `P₀`
and by `P₁`. Stated for rectangular real matrices; no projector property is needed. -/
theorem first_order_sum {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℝ) (Q : Matrix m m ℝ) (P₀ P₁ : Matrix n n ℝ)
    (h₀ : (1 - Q) * M * P₀ = (1 - Q) * M) (h₁ : (1 - Q) * M * P₁ = (1 - Q) * M) :
    (1 / 2 : ℝ) • (M * P₀) - (1 / 2 : ℝ) • (Q * M * P₀) + Q * M - (1 / 2 : ℝ) • (Q * M * P₁) +
      (1 / 2 : ℝ) • (M * P₁) = M := by
  have e₀ : M * P₀ - Q * M * P₀ = M - Q * M := by
    simpa [Matrix.sub_mul, Matrix.one_mul] using h₀
  have e₁ : M * P₁ - Q * M * P₁ = M - Q * M := by
    simpa [Matrix.sub_mul, Matrix.one_mul] using h₁
  linear_combination (norm := module) (1 / 2 : ℝ) • e₀ + (1 / 2 : ℝ) • e₁

/-! ### The family of §3 -/

/-- `Ω = E₃₁ - E₁₃` (arXiv 2608.12893, §3). -/
def Om : M₃ := !![0, 0, -1; 0, 0, 0; 1, 0, 0]

/-- `H = Ω E₁₁ - E₁₁ Ω = E₃₁ + E₁₃` (arXiv 2608.12893, (4.2)). -/
def Hm : M₃ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]

/-- `E₁₁`. -/
def E11 : M₃ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- `E₂₂`. -/
def E22 : M₃ := !![0, 0, 0; 0, 1, 0; 0, 0, 0]

/-- The commutator `X ↦ Ω X - X Ω`. -/
def comm (X : M₃) : M₃ := Om * X - X * Om

/-- `q_η(X) = (1 + η tanh x₃₁) / √(1 + ‖X‖_F²)`. -/
noncomputable def qη (η : ℝ) (X : M₃) : ℝ := (1 + η * Real.tanh (X 2 0)) / √(1 + ‖X‖ ^ 2)

/-- `M_η(X) = q_η(X) (Ω X - X Ω)`. -/
noncomputable def Mη (η : ℝ) (X : M₃) : M₃ := qη η X • comm X

/-- `ν(θ) = (0, cos(π θ / 4), sin(π θ / 4))ᵀ`. -/
noncomputable def nu (θ : ℝ) : Fin 3 → ℝ :=
  ![0, Real.cos (Real.pi * θ / 4), Real.sin (Real.pi * θ / 4)]

/-- `W(θ) = ν(θ) ν(θ)ᵀ`. -/
noncomputable def W (θ : ℝ) : M₃ := Matrix.vecMulVec (nu θ) (nu θ)

/-- The derivative `W'(θ)`, see `hasDerivAt_W`. -/
noncomputable def Wd (θ : ℝ) : M₃ :=
  (Real.pi / 4) • !![0, 0, 0; 0, -Real.sin (Real.pi * θ / 2), Real.cos (Real.pi * θ / 2);
    0, Real.cos (Real.pi * θ / 2), Real.sin (Real.pi * θ / 2)]

/-- The smoothing polynomial `ψ(x) = x + 15x⁴ - 39x⁵ + 34x⁶ - 10x⁷`. -/
def psi (x : ℝ) : ℝ := x + 15 * x ^ 4 - 39 * x ^ 5 + 34 * x ^ 6 - 10 * x ^ 7

/-- `ψ'`. -/
def dpsi (x : ℝ) : ℝ := 1 + 60 * x ^ 3 - 195 * x ^ 4 + 204 * x ^ 5 - 70 * x ^ 6

/-- `β = max_{[0,1]} |ψ'| = 27904/16807`. -/
noncomputable def beta : ℝ := 27904 / 16807

/-- The step size `h_j = 2^(-j²)`. -/
noncomputable def hj (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j ^ 2)

/-- The phase `ϑ_j`: `t / h_j` up to `4 j h_j`, then `4j + 4ψ((t - 4 j h_j)/(4 h_j))` up to
`4 (j+1) h_j`, then `4 (j+1)`. For `t < 0` the first formula is used. -/
noncomputable def th (j : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 4 * j * hj j then t / hj j
  else if t ≤ 4 * (j + 1) * hj j then 4 * j + 4 * psi ((t - 4 * j * hj j) / (4 * hj j))
  else 4 * (j + 1)

/-- `ϑ_j'`, see `hasDerivAt_th`. -/
noncomputable def dth (j : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 4 * j * hj j then 1 / hj j
  else if t ≤ 4 * (j + 1) * hj j then dpsi ((t - 4 * j * hj j) / (4 * hj j)) / hj j
  else 0

/-- The forcing `R_j(t) = h_j³ ϑ_j'(t) W'(ϑ_j(t))`. -/
noncomputable def Rj (j : ℕ) (t : ℝ) : M₃ := (hj j ^ 3 * dth j t) • Wd (th j t)

/-- The right-hand side `F_{j,η}(t, X) = M_η(X) + R_j(t)`. -/
noncomputable def Fj (j : ℕ) (η : ℝ) (t : ℝ) (X : M₃) : M₃ := Mη η X + Rj j t

/-- The initial value `Y⁰_j = E₁₁ + h_j³ E₂₂`. -/
noncomputable def Y0 (j : ℕ) : M₃ := E11 + hj j ^ 3 • E22

/-- `ε_j = β √2 (π/4) h_j²`. -/
noncomputable def εj (j : ℕ) : ℝ := beta * √2 * (Real.pi / 4) * hj j ^ 2

/-- **Eq. (5.16) for `M_η`** (arXiv 2608.12893): if `Ȳ = U Vᵀ` (in the paper `u vᵀ`, the rank-one
limit (5.13)) with `Q U = U`, `P₀ V = V`, `P₁ V = V` and `P₀, P₁` symmetric, then the first-order
sum of the five Strang substeps at `Ȳ` is `M_η(Ȳ)`: the paper's verification of the hypotheses
of `first_order_sum` from `(I - Q) Ȳ = 0` and `Ȳ P₀ = Ȳ P₁ = Ȳ`. -/
theorem first_order_sum_Mη {k : Type*} [Fintype k] (η : ℝ) (U V : Matrix (Fin 3) k ℝ)
    (Q P₀ P₁ : M₃) (hQ : Q * U = U) (hP₀ : P₀ᵀ = P₀) (hP₀V : P₀ * V = V) (hP₁ : P₁ᵀ = P₁)
    (hP₁V : P₁ * V = V) :
    (1 / 2 : ℝ) • (Mη η (U * Vᵀ) * P₀) - (1 / 2 : ℝ) • (Q * Mη η (U * Vᵀ) * P₀) +
      Q * Mη η (U * Vᵀ) - (1 / 2 : ℝ) • (Q * Mη η (U * Vᵀ) * P₁) +
      (1 / 2 : ℝ) • (Mη η (U * Vᵀ) * P₁) = Mη η (U * Vᵀ) := by
  have hU0 : ∀ X : Matrix k (Fin 3) ℝ, (1 - Q) * (U * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQ, sub_self, Matrix.zero_mul]
  have hfix : ∀ P : M₃, Pᵀ = P → P * V = V →
      (1 - Q) * Mη η (U * Vᵀ) * P = (1 - Q) * Mη η (U * Vᵀ) := by
    intro P hP hPV
    have hVP : Vᵀ * P = Vᵀ := by
      conv_lhs => rw [← hP]
      rw [← Matrix.transpose_mul, hPV]
    simp only [Mη, comm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, hU0, hVP, Matrix.zero_mul]
  exact first_order_sum _ Q P₀ P₁ (hfix P₀ hP₀ hP₀V) (hfix P₁ hP₁ hP₁V)

/-! ### Elementary bounds -/

private theorem norm_Om_mul_le (X : M₃) : ‖Om * X‖ ≤ ‖X‖ := by
  have h : ‖Om * X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    simp [Om, Matrix.mul_apply, Fin.sum_univ_three]
    nlinarith [sq_nonneg (X 1 0), sq_nonneg (X 1 1), sq_nonneg (X 1 2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

private theorem norm_mul_Om_le (X : M₃) : ‖X * Om‖ ≤ ‖X‖ := by
  have h : ‖X * Om‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    simp [Om, Matrix.mul_apply, Fin.sum_univ_three]
    nlinarith [sq_nonneg (X 0 1), sq_nonneg (X 1 1), sq_nonneg (X 2 1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

private theorem norm_comm_le (X : M₃) : ‖comm X‖ ≤ 2 * ‖X‖ := by
  unfold comm
  linarith [norm_sub_le (Om * X) (X * Om), norm_Om_mul_le X, norm_mul_Om_le X]

private theorem comm_sub (X Z : M₃) : comm X - comm Z = comm (X - Z) := by
  simp only [comm, Matrix.mul_sub, Matrix.sub_mul]
  abel

private theorem comm_smul (a : ℝ) (X : M₃) : comm (a • X) = a • comm X := by
  simp only [comm, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-! ### `tanh` and the normalization `X / √(1 + ‖X‖²)` -/

private theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : Real.sinh / Real.cosh = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  have e2 : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
    nlinarith [Real.cosh_sq x]
  rwa [e, e2] at h

private theorem abs_tanh_sub_le (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.tanh)
    (f' := fun x => 1 / Real.cosh x ^ 2) (s := univ) (C := 1)
    (fun x _ => (hasDerivAt_tanh x).hasDerivWithinAt) (fun x _ => ?_) convex_univ
    (mem_univ y) (mem_univ x)
  · simpa [Real.norm_eq_abs] using h
  · have hc := Real.one_le_cosh x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith

private theorem abs_tanh_le (x : ℝ) : |Real.tanh x| ≤ |x| := by
  simpa using abs_tanh_sub_le x 0

/-- `|tanh x - x| ≤ |x|³`. -/
private theorem abs_tanh_sub_self_le (x : ℝ) : |Real.tanh x - x| ≤ |x| ^ 3 := by
  have hd : ∀ y, HasDerivAt (fun y => Real.tanh y - y) (1 / Real.cosh y ^ 2 - 1) y :=
    fun y => (hasDerivAt_tanh y).sub (hasDerivAt_id y)
  have h := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => Real.tanh y - y) (f' := fun y => 1 / Real.cosh y ^ 2 - 1) (C := x ^ 2)
    (fun y _ => (hd y).hasDerivWithinAt) (fun y hy => ?_)
    (show (0 : ℝ) ∈ Icc (-|x|) |x| by simp) (show x ∈ Icc (-|x|) |x| from
      ⟨neg_abs_le x, le_abs_self x⟩)
  · simp only [Real.tanh_zero, sub_zero, Real.norm_eq_abs] at h
    calc |Real.tanh x - x| ≤ x ^ 2 * |x| := h
      _ = |x| ^ 3 := by rw [← sq_abs]; ring
  · have hc := Real.cosh_pos y
    have e : 1 / Real.cosh y ^ 2 - 1 = -Real.tanh y ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_pow]
      field_simp
      nlinarith [Real.cosh_sq y]
    rw [e, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_tanh_le y
    have h2 : |y| ≤ |x| := abs_le.2 hy
    rw [← sq_abs, ← sq_abs x]
    have := abs_nonneg (Real.tanh y)
    nlinarith

private theorem one_le_sqrt_one_add_sq (a : ℝ) : 1 ≤ √(1 + a ^ 2) := by
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg a]

private theorem abs_le_sqrt_one_add_sq (a : ℝ) : |a| ≤ √(1 + a ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- For `a, b ≥ 0`: `|1/√(1+a²) - 1/√(1+b²)| b ≤ |a - b|`. -/
private theorem abs_inv_sqrt_sub_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |1 / √(1 + a ^ 2) - 1 / √(1 + b ^ 2)| * b ≤ |a - b| := by
  set sa := √(1 + a ^ 2) with hsa
  set sb := √(1 + b ^ 2) with hsb
  have sa1 : 1 ≤ sa := one_le_sqrt_one_add_sq a
  have sb1 : 1 ≤ sb := one_le_sqrt_one_add_sq b
  have saa : a ≤ sa := by simpa [abs_of_nonneg ha] using abs_le_sqrt_one_add_sq a
  have sbb : b ≤ sb := by simpa [abs_of_nonneg hb] using abs_le_sqrt_one_add_sq b
  have sa2 : sa ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have sb2 : sb ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have e : 1 / sa - 1 / sb = (sb - sa) / (sa * sb) := by field_simp
  have key : |sb - sa| * (sa + sb) = |a - b| * (a + b) := by
    have : (sb - sa) * (sa + sb) = (b - a) * (a + b) := by nlinarith
    have h1 : |sb - sa| * (sa + sb) = |(sb - sa) * (sa + sb)| := by
      rw [abs_mul, abs_of_pos (show 0 < sa + sb by linarith)]
    rw [h1, this, abs_mul, abs_of_nonneg (show 0 ≤ a + b by linarith), abs_sub_comm]
  rw [e, abs_div, abs_of_pos (show 0 < sa * sb by positivity), div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)]
  have hpos : 0 < sa + sb := by linarith
  have hd := abs_nonneg (sb - sa)
  have he := abs_nonneg (a - b)
  refine le_of_mul_le_mul_right ?_ hpos
  calc |sb - sa| * b * (sa + sb) = |a - b| * (a + b) * b := by rw [mul_right_comm, key]
    _ ≤ |a - b| * (sa + sb) * (sa * sb) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) he) (by nlinarith) hb
        positivity
    _ = |a - b| * (sa * sb) * (sa + sb) := by ring

/-- The normalization `X / √(1 + ‖X‖²)`. -/
noncomputable def nrm (X : M₃) : M₃ := (1 / √(1 + ‖X‖ ^ 2)) • X

private theorem norm_nrm_sub_le (X Z : M₃) : ‖nrm X - nrm Z‖ ≤ 2 * ‖X - Z‖ := by
  have e : nrm X - nrm Z = (1 / √(1 + ‖X‖ ^ 2)) • (X - Z) +
      (1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Z‖ ^ 2)) • Z := by
    simp only [nrm, smul_sub, sub_smul]
    abel
  have h1 : ‖(1 / √(1 + ‖X‖ ^ 2)) • (X - Z)‖ ≤ ‖X - Z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have := one_le_sqrt_one_add_sq ‖X‖
    have h0 : 1 / √(1 + ‖X‖ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; exact this
    nlinarith [norm_nonneg (X - Z)]
  have h2 : ‖(1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Z‖ ^ 2)) • Z‖ ≤ ‖X - Z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (abs_inv_sqrt_sub_mul_le (norm_nonneg X) (norm_nonneg Z)).trans
      (abs_norm_sub_norm_le X Z)
  rw [e]
  linarith [norm_add_le ((1 / √(1 + ‖X‖ ^ 2)) • (X - Z))
    ((1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Z‖ ^ 2)) • Z)]

private theorem inv_sqrt_mul_norm_le (X : M₃) : 1 / √(1 + ‖X‖ ^ 2) * ‖X‖ ≤ 1 := by
  have h := abs_le_sqrt_one_add_sq ‖X‖
  rw [abs_of_nonneg (norm_nonneg X)] at h
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  exact h

/-! ### Prop. 3.2: the bounds on `M_η` -/

/-- `‖M_η(X)‖_F ≤ 4` for every `X` (arXiv 2608.12893, Prop. 3.2, where it is stated for
rank-two `X`); here `|η| ≤ 1`. -/
theorem norm_Mη_le {η : ℝ} (hη : |η| ≤ 1) (X : M₃) : ‖Mη η X‖ ≤ 4 := by
  have ht := Real.abs_tanh_lt_one (X 2 0)
  have hq : |1 + η * Real.tanh (X 2 0)| ≤ 2 := by
    calc |1 + η * Real.tanh (X 2 0)| ≤ |1| + |η| * |Real.tanh (X 2 0)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; nlinarith [abs_nonneg η, abs_nonneg (Real.tanh (X 2 0))]
  have hs0 : 0 < √(1 + ‖X‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Mη, qη, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hs0,
    div_mul_eq_mul_div, div_le_iff₀ hs0]
  have hc := norm_comm_le X
  have hs := abs_le_sqrt_one_add_sq ‖X‖
  rw [abs_of_nonneg (norm_nonneg X)] at hs
  have := norm_nonneg (comm X)
  have := abs_nonneg (1 + η * Real.tanh (X 2 0))
  nlinarith

/-- `M_η` is `10`-Lipschitz in the Frobenius norm, i.e. `‖DM_η‖ ≤ 10` (arXiv 2608.12893,
proof of Prop. 3.2); here `|η| ≤ 1`. -/
theorem Mη_lipschitz {η : ℝ} (hη : |η| ≤ 1) (X Z : M₃) :
    ‖Mη η X - Mη η Z‖ ≤ 10 * ‖X - Z‖ := by
  set a := X 2 0
  set b := Z 2 0
  have e : Mη η X - Mη η Z = (1 + η * Real.tanh a) • comm (nrm X - nrm Z) +
      (η * (Real.tanh a - Real.tanh b) * (1 / √(1 + ‖Z‖ ^ 2))) • comm Z := by
    rw [← comm_sub]
    simp only [nrm, comm_smul, Mη, qη]
    module
  have hq : |1 + η * Real.tanh a| ≤ 2 := by
    have ht := Real.abs_tanh_lt_one a
    calc |1 + η * Real.tanh a| ≤ |1| + |η| * |Real.tanh a| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; nlinarith [abs_nonneg η, abs_nonneg (Real.tanh a)]
  have h1 : ‖(1 + η * Real.tanh a) • comm (nrm X - nrm Z)‖ ≤ 8 * ‖X - Z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have := (norm_comm_le (nrm X - nrm Z)).trans
      (mul_le_mul_of_nonneg_left (norm_nrm_sub_le X Z) zero_le_two)
    have := norm_nonneg (comm (nrm X - nrm Z))
    nlinarith [abs_nonneg (1 + η * Real.tanh a)]
  have hab : |a - b| ≤ ‖X - Z‖ := Frobenius.abs_apply_le_norm (X - Z) 2 0
  have h2 : ‖(η * (Real.tanh a - Real.tanh b) * (1 / √(1 + ‖Z‖ ^ 2))) • comm Z‖ ≤
      2 * ‖X - Z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) <
      1 / √(1 + ‖Z‖ ^ 2))]
    have ht := (abs_tanh_sub_le a b).trans hab
    have hc := norm_comm_le Z
    have hz := inv_sqrt_mul_norm_le Z
    have h3 : 1 / √(1 + ‖Z‖ ^ 2) * ‖comm Z‖ ≤ 2 := by
      have : (0 : ℝ) ≤ 1 / √(1 + ‖Z‖ ^ 2) := by positivity
      nlinarith
    have : |η| * |Real.tanh a - Real.tanh b| ≤ ‖X - Z‖ := by
      have := abs_nonneg (Real.tanh a - Real.tanh b)
      nlinarith [abs_nonneg η]
    calc |η| * |Real.tanh a - Real.tanh b| * (1 / √(1 + ‖Z‖ ^ 2)) * ‖comm Z‖
        = |η| * |Real.tanh a - Real.tanh b| * (1 / √(1 + ‖Z‖ ^ 2) * ‖comm Z‖) := by ring
      _ ≤ ‖X - Z‖ * 2 := mul_le_mul this h3 (by positivity) (norm_nonneg _)
      _ = 2 * ‖X - Z‖ := by ring
  rw [e]
  linarith [norm_add_le ((1 + η * Real.tanh a) • comm (nrm X - nrm Z))
    ((η * (Real.tanh a - Real.tanh b) * (1 / √(1 + ‖Z‖ ^ 2))) • comm Z)]

/-- `M_η(Y)` is tangent to the rank-`r` manifold at `Y = U S Vᵀ`: its doubly normal part
`(1 - U Uᵀ) M_η(Y) (1 - V Vᵀ)` vanishes (arXiv 2608.12893, Prop. 3.2). Here `U, V` are any
`3 × k` matrices with orthonormal columns and `S` any `k × k` matrix, so this covers every
rank-two `Y` through its SVD. -/
theorem Mη_tangent {k : Type*} [Fintype k] [DecidableEq k] (η : ℝ) (U V : Matrix (Fin 3) k ℝ)
    (S : Matrix k k ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    (1 - U * Uᵀ) * Mη η (U * S * Vᵀ) * (1 - V * Vᵀ) = 0 := by
  set Y := U * S * Vᵀ
  have h1 : (1 - U * Uᵀ) * Y = 0 := by
    have : U * Uᵀ * Y = Y := by
      simp only [Y, ← Matrix.mul_assoc]
      rw [Matrix.mul_assoc U Uᵀ U, hU, Matrix.mul_one]
    rw [Matrix.sub_mul, Matrix.one_mul, this, sub_self]
  have h2 : Y * (1 - V * Vᵀ) = 0 := by
    have : Y * (V * Vᵀ) = Y := by
      simp only [Y, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V Vᵀ, hV, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  have : (1 - U * Uᵀ) * comm Y * (1 - V * Vᵀ) =
      (1 - U * Uᵀ) * Om * (Y * (1 - V * Vᵀ)) - ((1 - U * Uᵀ) * Y) * (Om * (1 - V * Vᵀ)) := by
    simp only [comm]
    noncomm_ring
  rw [Mη, Matrix.mul_smul, Matrix.smul_mul, this, h1, h2]
  simp

/-! ### `W`, `ψ`, `ϑ_j` and `R_j` -/

/-- `diag(0, 1, 1)`. -/
def D23 : M₃ := !![0, 0, 0; 0, 1, 0; 0, 0, 1]
/-- `diag(0, 1, -1)`. -/
def A23 : M₃ := !![0, 0, 0; 0, 1, 0; 0, 0, -1]
/-- `E₂₃ + E₃₂`. -/
def B23 : M₃ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]

private theorem W_eq (θ : ℝ) : W θ = (1 / 2 : ℝ) • D23 + (Real.cos (Real.pi * θ / 2) / 2) • A23 +
    (Real.sin (Real.pi * θ / 2) / 2) • B23 := by
  have e : Real.pi * θ / 2 = 2 * (Real.pi * θ / 4) := by ring
  rw [e, Real.cos_two_mul, Real.sin_two_mul]
  have hs := Real.sin_sq_add_cos_sq (Real.pi * θ / 4)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, nu, Matrix.vecMulVec_apply, D23, A23, B23] <;> nlinarith

private theorem Wd_eq (θ : ℝ) : Wd θ = (-(Real.sin (Real.pi * θ / 2) * (Real.pi / 2)) / 2) • A23 +
    (Real.cos (Real.pi * θ / 2) * (Real.pi / 2) / 2) • B23 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wd, A23, B23] <;> ring

/-- `W' = Wd` (arXiv 2608.12893, §3, the derivative in `R_j = h_j³ ϑ_j' W'(ϑ_j)`). -/
theorem hasDerivAt_W (θ : ℝ) : HasDerivAt W (Wd θ) θ := by
  have hu : HasDerivAt (fun θ : ℝ => Real.pi * θ / 2) (Real.pi / 2) θ := by
    simpa using ((hasDerivAt_id θ).const_mul Real.pi).div_const 2
  have hc := ((Real.hasDerivAt_cos _).comp θ hu).div_const 2
  have hs := ((Real.hasDerivAt_sin _).comp θ hu).div_const 2
  have h := ((hasDerivAt_const θ ((1 / 2 : ℝ) • D23)).add (hc.smul_const A23)).add
    (hs.smul_const B23)
  have h' := h.congr_of_eventuallyEq (Eventually.of_forall fun θ => W_eq θ)
  convert h' using 1
  rw [Wd_eq]
  module

private theorem norm_Wd (θ : ℝ) : ‖Wd θ‖ = √2 * (Real.pi / 4) := by
  set A : M₃ := !![0, 0, 0; 0, -Real.sin (Real.pi * θ / 2), Real.cos (Real.pi * θ / 2);
    0, Real.cos (Real.pi * θ / 2), Real.sin (Real.pi * θ / 2)]
  have hA : ‖A‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [A, Fin.sum_univ_three]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ / 2)]
  have hA' : ‖A‖ = √2 := by
    rw [← hA, Real.sqrt_sq (norm_nonneg _)]
  rw [Wd, norm_smul, hA', Real.norm_eq_abs, abs_of_pos (by positivity)]
  ring

private theorem hasDerivAt_psi (x : ℝ) : HasDerivAt psi (dpsi x) x := by
  have h := ((((hasDerivAt_id x).add ((hasDerivAt_pow 4 x).const_mul 15)).sub
    ((hasDerivAt_pow 5 x).const_mul 39)).add ((hasDerivAt_pow 6 x).const_mul 34)).sub
    ((hasDerivAt_pow 7 x).const_mul 10)
  convert h using 1
  · funext y
    simp [psi]
  · simp only [dpsi]
    push_cast
    ring

private theorem dpsi_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ dpsi x := by
  have e : dpsi x = (1 - x) ^ 3 * (70 * x ^ 3 + 6 * x ^ 2 + 3 * x + 1) := by
    unfold dpsi; ring
  rw [e]
  exact mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)

/-- `ψ' ≤ β` on `[0, 1]` (arXiv 2608.12893, Prop. 3.2, `β = max_{[0,1]} |ψ'|`; with
`ψ' ≥ 0` there and `dpsi_three_sevenths`, `β` is the maximum). -/
theorem dpsi_le_beta {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : dpsi x ≤ beta := by
  have e : beta - dpsi x = (7 * x - 3) ^ 2 *
      (24010 * x ^ 4 - 49392 * x ^ 3 + 20139 * x ^ 2 + 5754 * x + 1233) / 16807 := by
    unfold beta dpsi; ring
  have hq : 0 ≤ 24010 * x ^ 4 - 49392 * x ^ 3 + 20139 * x ^ 2 + 5754 * x + 1233 := by
    nlinarith [sq_nonneg (x ^ 2 - 36 / 35 * x), mul_nonneg h0 (sub_nonneg.2 h1)]
  have : 0 ≤ beta - dpsi x := by
    rw [e]; positivity
  linarith

/-- `ψ'(3/7) = β = 27904/16807` (arXiv 2608.12893, Prop. 3.2: the maximum is attained at
`3/7`). -/
theorem dpsi_three_sevenths : dpsi (3 / 7) = beta := by
  norm_num [dpsi, beta]

private theorem hj_pos (j : ℕ) : 0 < hj j := by
  unfold hj; positivity

private theorem hj_le_half {j : ℕ} (hj1 : 1 ≤ j) : hj j ≤ 1 / 2 := by
  unfold hj
  exact pow_le_of_le_one (by norm_num) (by norm_num) (by positivity)

private theorem hj_le {j : ℕ} (hj3 : 3 ≤ j) : hj j ≤ 1 / 512 := by
  unfold hj
  have h9 : 9 ≤ j ^ 2 := by nlinarith
  calc (1 / 2 : ℝ) ^ (j ^ 2) ≤ (1 / 2) ^ 9 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h9
    _ = 1 / 512 := by norm_num

private theorem abs_dth_le (j : ℕ) (t : ℝ) : |dth j t| ≤ beta / hj j := by
  have hh := hj_pos j
  have hb : (1 : ℝ) ≤ beta := by norm_num [beta]
  unfold dth
  split_ifs with h1 h2
  · rw [abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_right hb hh.le
  · have hx0 : 0 ≤ (t - 4 * j * hj j) / (4 * hj j) := div_nonneg (by linarith) (by positivity)
    have hx1 : (t - 4 * j * hj j) / (4 * hj j) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [abs_div, abs_of_pos hh, abs_of_nonneg (dpsi_nonneg hx0 hx1)]
    exact div_le_div_of_nonneg_right (dpsi_le_beta hx0 hx1) hh.le
  · simp only [abs_zero]
    exact div_nonneg (by norm_num [beta]) hh.le

/-- `‖R_j(t)‖_F ≤ ε_j = β √2 (π/4) h_j²` for every `t` (arXiv 2608.12893, Prop. 3.2). -/
theorem norm_Rj_le (j : ℕ) (t : ℝ) : ‖Rj j t‖ ≤ εj j := by
  have hh := hj_pos j
  rw [Rj, norm_smul, norm_Wd, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < hj j ^ 3)]
  have h := abs_dth_le j t
  calc hj j ^ 3 * |dth j t| * (√2 * (Real.pi / 4)) ≤ hj j ^ 3 * (beta / hj j) *
      (√2 * (Real.pi / 4)) := by gcongr
    _ = εj j := by unfold εj; field_simp

private theorem εj_le {j : ℕ} (hj1 : 1 ≤ j) : εj j ≤ 1 / 2 := by
  have h := hj_le_half hj1
  have hh := hj_pos j
  have hs : √2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp := Real.pi_lt_d2
  have hb : beta ≤ 1.661 := by norm_num [beta]
  have hb0 : 0 ≤ beta := by norm_num [beta]
  have hs0 := Real.sqrt_nonneg 2
  unfold εj
  have h2 : hj j ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 : beta * √2 * (Real.pi / 4) ≤ 2 := by
    calc beta * √2 * (Real.pi / 4) ≤ 1.661 * 1.415 * (3.15 / 4) := by gcongr
      _ ≤ 2 := by norm_num
  have h4 : 0 ≤ beta * √2 * (Real.pi / 4) := by positivity
  calc beta * √2 * (Real.pi / 4) * hj j ^ 2 ≤ 2 * (1 / 4) := by gcongr
    _ = 1 / 2 := by norm_num

/-- **Prop. 3.2** (arXiv 2608.12893), the bounds `B_F = 5`, `L_F = 12`, the splitting
`F = M_η + R_j` with `M_η` tangent at every factored `Y = U S Vᵀ` and `‖M_η‖ ≤ 4`, the normal size
`‖R_j‖ ≤ ε_j = β √2 (π/4) h_j²`, for `j ≥ 1` (the paper: `j ≥ 3`) and `η = ±1` (here `|η| ≤ 1`).
The bounds hold for all `t`, not only `t ∈ [0, 1]`. The smoothness constant `κ = 123` is
`prop_3_2_kappa`. `δ_j = 0` holds by construction, the exact solution starting at `Y⁰_j`. -/
theorem prop_3_2 {j : ℕ} (hj1 : 1 ≤ j) {η : ℝ} (hη : |η| ≤ 1) :
    IsBoundedField (Fj j η) 5 ∧ IsLipschitzField (Fj j η) 12 ∧
    (∀ X, ‖Mη η X‖ ≤ 4) ∧ (∀ t, ‖Rj j t‖ ≤ εj j) ∧
    (∀ (U V : Matrix (Fin 3) (Fin 2) ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → (1 - U * Uᵀ) * Mη η (U * S * Vᵀ) * (1 - V * Vᵀ) = 0) ∧
    (∀ t X, Fj j η t X = Mη η X + Rj j t) := by
  refine ⟨fun t X => ?_, fun t X Z => ?_, norm_Mη_le hη, norm_Rj_le j,
    fun U V S hU hV => Mη_tangent η U V S hU hV, fun _ _ => rfl⟩
  · change ‖Mη η X + Rj j t‖ ≤ 5
    have := norm_add_le (Mη η X) (Rj j t)
    linarith [norm_Mη_le hη X, norm_Rj_le j t, εj_le hj1]
  · have e : Fj j η t X - Fj j η t Z = Mη η X - Mη η Z := by simp [Fj]
    rw [e]
    linarith [Mη_lipschitz hη X Z, norm_nonneg (X - Z)]

/-! ### The phase `ϑ_j` is differentiable with derivative `dth` -/

private theorem hasDerivAt_ite {f g : ℝ → ℝ} {f' g' : ℝ → ℝ} (a : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (h0 : f a = g a) (h1 : f' a = g' a) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ a then f s else g s) (if t ≤ a then f' t else g' t) t := by
  rcases lt_trichotomy t a with h | rfl | h
  · rw [ite_eq_left h.le]
    apply (hf t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    rw [ite_eq_left (le_of_lt hs)]
  · rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Iic t) t :=
      (hf t).hasDerivWithinAt.congr (fun s hs => ite_eq_left hs) (ite_eq_left le_rfl)
    have hr : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Ici t) t := by
      rw [h1]
      refine (hg t).hasDerivWithinAt.congr (fun s hs => ?_) ?_
      · by_cases hst : s ≤ t
        · have : s = t := le_antisymm hst hs
          subst this
          rw [ite_eq_left le_rfl, h0]
        · rw [ite_eq_right hst]
      · rw [ite_eq_left le_rfl, h0]
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [ite_eq_right (not_le.2 h)]
    apply (hg t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with s hs
    rw [ite_eq_right (not_le.2 hs)]

/-- `ϑ_j' = dth j` everywhere (arXiv 2608.12893, §3): the three pieces of `ϑ_j` join with
matching derivatives, since `ψ(0) = 0`, `ψ(1) = 1`, `ψ'(0) = 1`, `ψ'(1) = 0`. -/
theorem hasDerivAt_th (j : ℕ) (t : ℝ) : HasDerivAt (th j) (dth j t) t := by
  have hh := hj_pos j
  set h := hj j
  have hx : ∀ t, HasDerivAt (fun t => (t - 4 * j * h) / (4 * h)) (1 / (4 * h)) t := fun t => by
    simpa using ((hasDerivAt_id t).sub_const (4 * j * h)).div_const (4 * h)
  have hp : ∀ t, HasDerivAt (fun t => 4 * j + 4 * psi ((t - 4 * j * h) / (4 * h)))
      (dpsi ((t - 4 * j * h) / (4 * h)) / h) t := fun t => by
    have := (((hasDerivAt_psi _).comp t (hx t)).const_mul 4).const_add (4 * (j : ℝ))
    refine this.congr_deriv ?_
    field_simp
  have hin : ∀ t, HasDerivAt (fun s => if s ≤ 4 * (j + 1) * h then
      4 * j + 4 * psi ((s - 4 * j * h) / (4 * h)) else 4 * (j + 1))
      (if t ≤ 4 * (j + 1) * h then dpsi ((t - 4 * j * h) / (4 * h)) / h else 0) t :=
    hasDerivAt_ite (4 * (j + 1) * h) hp (fun t => hasDerivAt_const t _)
      (by
        have : (4 * (j + 1) * h - 4 * j * h) / (4 * h) = 1 := by field_simp; ring
        rw [this]; norm_num [psi]; ring)
      (by
        have : (4 * (j + 1) * h - 4 * j * h) / (4 * h) = 1 := by field_simp; ring
        rw [this]; norm_num [dpsi])
  have hl : ∀ t, HasDerivAt (fun t => t / h) (1 / h) t := fun t => by
    simpa using (hasDerivAt_id t).div_const h
  have hjh : 4 * (j : ℝ) * h ≤ 4 * (j + 1) * h := by nlinarith
  exact hasDerivAt_ite (4 * j * h) hl hin
    (by rw [ite_eq_left hjh, sub_self, zero_div]; field_simp; norm_num [psi])
    (by rw [ite_eq_left hjh, sub_self, zero_div]; norm_num [dpsi]) t

/-- `R_j(t) = d/dt (h_j³ W(ϑ_j(t)))` (arXiv 2608.12893, §3, definition of `R_j`). -/
theorem hasDerivAt_hW (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t => hj j ^ 3 • W (th j t)) (Rj j t) t := by
  have := ((hasDerivAt_W (th j t)).scomp t (hasDerivAt_th j t)).const_smul (hj j ^ 3)
  rw [Rj, mul_smul]
  exact this

/-! ### Lemma 4.3 and the derivative of `M₊ - M₋` at `E₁₁` -/

/-- `E₃₁`. -/
def E31 : M₃ := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

private theorem norm_E11 : ‖E11‖ = 1 := by
  have h : ‖E11‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [E11, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg E11), h, Real.sqrt_one]

private theorem norm_E22 : ‖E22‖ = 1 := by
  have h : ‖E22‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [E22, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg E22), h, Real.sqrt_one]

private theorem norm_Hm : ‖Hm‖ = √2 := by
  have h : ‖Hm‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [Hm, Fin.sum_univ_three]; norm_num
  rw [← Real.sqrt_sq (norm_nonneg Hm), h]

private theorem comm_E11 : comm E11 = Hm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comm, Om, E11, Hm]

/-- `M_±(E₁₁) = H / √2` (arXiv 2608.12893, proof of Lemma 4.2). -/
theorem Mη_E11 (η : ℝ) : Mη η E11 = (1 / √2) • Hm := by
  rw [Mη, qη, comm_E11, norm_E11]
  norm_num [E11]

private theorem nrm_E11 : comm (nrm E11) = (1 / √2) • Hm := by
  rw [nrm, comm_smul, comm_E11, norm_E11]
  norm_num

private theorem norm_nrm_le (X : M₃) : ‖nrm X‖ ≤ 1 := by
  rw [nrm, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact inv_sqrt_mul_norm_le X

private theorem Mη_sub_eq (X : M₃) :
    Mη 1 X - Mη (-1) X = (2 * Real.tanh (X 2 0)) • comm (nrm X) := by
  simp only [Mη, qη, nrm, comm_smul, smul_smul, ← sub_smul]
  congr 1
  ring

private theorem norm_Mη_sub_le (X : M₃) : ‖Mη 1 X - Mη (-1) X‖ ≤ 4 * |X 2 0| := by
  rw [Mη_sub_eq, norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
  have h1 := abs_tanh_le (X 2 0)
  have h2 := (norm_comm_le (nrm X)).trans
    (mul_le_mul_of_nonneg_left (norm_nrm_le X) zero_le_two)
  have := abs_nonneg (Real.tanh (X 2 0))
  have := norm_nonneg (comm (nrm X))
  nlinarith

private theorem abs_entry_le (X : M₃) : |X 2 0| ≤ ‖X - E11‖ := by
  have := Frobenius.abs_apply_le_norm (X - E11) 2 0
  simpa [E11] using this

/-- **The derivative of `M₊ - M₋` at `E₁₁`** (arXiv 2608.12893, proof of Lemma 4.2):
`D(M₊ - M₋)(E₁₁)[Z] = √2 z₃₁ H`, in the quantitative form
`‖(M₊ - M₋)(X) - √2 x₃₁ H‖ ≤ 12 ‖X - E₁₁‖²` for `‖X - E₁₁‖ ≤ 1` (note `(M₊ - M₋)(E₁₁) = 0`). -/
theorem Mη_sub_taylor (X : M₃) (hX : ‖X - E11‖ ≤ 1) :
    ‖Mη 1 X - Mη (-1) X - (√2 * X 2 0) • Hm‖ ≤ 12 * ‖X - E11‖ ^ 2 := by
  set x := X 2 0
  set ρ := ‖X - E11‖
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have e2 : Mη 1 X - Mη (-1) X - (√2 * x) • Hm =
      (2 * (Real.tanh x - x)) • comm (nrm X) + (2 * x) • comm (nrm X - nrm E11) := by
    rw [Mη_sub_eq, ← comm_sub, nrm_E11, smul_sub, smul_smul]
    have : 2 * x * (1 / √2) = √2 * x := by
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [this]
    module
  have hx : |x| ≤ ρ := abs_entry_le X
  have h1 : ‖(2 * (Real.tanh x - x)) • comm (nrm X)‖ ≤ 4 * ρ ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have ht := abs_tanh_sub_self_le x
    have hc := (norm_comm_le (nrm X)).trans
      (mul_le_mul_of_nonneg_left (norm_nrm_le X) zero_le_two)
    have hx3 : |x| ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
    have := abs_nonneg (Real.tanh x - x)
    have := norm_nonneg (comm (nrm X))
    nlinarith
  have h2 : ‖(2 * x) • comm (nrm X - nrm E11)‖ ≤ 8 * ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have hc := (norm_comm_le (nrm X - nrm E11)).trans
      (mul_le_mul_of_nonneg_left (norm_nrm_sub_le X E11) zero_le_two)
    have := abs_nonneg x
    have := norm_nonneg (comm (nrm X - nrm E11))
    have : 0 ≤ ρ := norm_nonneg _
    nlinarith
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have h3 : ρ ^ 3 ≤ ρ ^ 2 := by nlinarith
  rw [e2]
  linarith [norm_add_le ((2 * (Real.tanh x - x)) • comm (nrm X))
    ((2 * x) • comm (nrm X - nrm E11))]

private theorem inner_E31 (X : M₃) : ⟪E31, X⟫ = X 2 0 := by
  rw [Frobenius.inner_def]; simp [E31, Fin.sum_univ_three]

private theorem hasDerivWithinAt_entry {A : ℝ → M₃} {A' : M₃} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt A A' s t) : HasDerivWithinAt (fun t => A t 2 0) (A' 2 0) s t := by
  have := (innerSL ℝ E31).hasFDerivAt.comp_hasDerivWithinAt t h
  simpa [Function.comp_def, inner_E31] using this

private theorem continuousOn_entry {A : ℝ → M₃} {s : Set ℝ} (h : ContinuousOn A s) :
    ContinuousOn (fun t => A t 2 0) s := by
  have := (innerSL ℝ E31).continuous.comp_continuousOn h
  simpa [Function.comp_def, inner_E31] using this

private theorem Rj_entry (j : ℕ) (t : ℝ) : Rj j t 2 0 = 0 := by
  simp [Rj, Wd]

/-- **Lemma 4.3** (arXiv 2608.12893): for the exact flows of `F_{j,+}` and `F_{j,-}` from
`Y⁰_j`, `Φ_{j,+}(4h_j) - Φ_{j,-}(4h_j) = 8 h_j² H + O(h_j³)`, with the explicit constant
`10⁵` in the `O`, uniform in `j ≥ 3`. Any solutions in the sense of `ODESolution` qualify; they
exist by `exists_solution`. -/
theorem lemma_4_3 {j : ℕ} (hj3 : 3 ≤ j) {Ap Am : ℝ → M₃}
    (hp : ODESolution (Fj j 1) Ap 0 (4 * hj j)) (hp0 : Ap 0 = Y0 j)
    (hm : ODESolution (Fj j (-1)) Am 0 (4 * hj j)) (hm0 : Am 0 = Y0 j) :
    ‖Ap (4 * hj j) - Am (4 * hj j) - (8 * hj j ^ 2) • Hm‖ ≤ 100000 * hj j ^ 3 := by
  have hh : 0 < hj j := hj_pos j
  have hh1 : hj j ≤ 1 / 512 := hj_le hj3
  have hj1 : 1 ≤ j := by omega
  set h := hj j with hdef
  have hbm : IsBoundedField (Fj j (-1)) 5 := (prop_3_2 hj1 (by norm_num)).1
  have hs2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hY0 : ‖Y0 j - E11‖ = h ^ 3 := by
    rw [Y0, add_sub_cancel_left, norm_smul, norm_E22, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one]
  have hρ : ∀ t ∈ Icc 0 (4 * h), ‖Am t - E11‖ ≤ 21 * h := by
    intro t ht
    have h1 := hm.norm_sub_le_of_bounded hbm t ht
    rw [hm0, sub_zero] at h1
    have h3 : h ^ 3 ≤ h := pow_le_of_le_one hh.le (by linarith) (by norm_num)
    calc ‖Am t - E11‖ = ‖(Am t - Y0 j) + (Y0 j - E11)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Am t - Y0 j‖ + ‖Y0 j - E11‖ := norm_add_le _ _
      _ ≤ 5 * t + h ^ 3 := by rw [hY0]; linarith
      _ ≤ 21 * h := by linarith [ht.2]
  have hentry : ∀ t ∈ Icc 0 (4 * h), |Am t 2 0| ≤ 21 * h := fun t ht =>
    (abs_entry_le (Am t)).trans (hρ t ht)
  -- the difference `G = A₊ - A₋`
  have hGd : ∀ t ∈ Ico 0 (4 * h), HasDerivWithinAt (fun t => Ap t - Am t)
      (Mη 1 (Ap t) - Mη (-1) (Am t)) (Ici t) t := by
    intro t ht
    have := (hp.deriv t ht).sub (hm.deriv t ht)
    convert this using 1
    simp [Fj]
  have hGc : ContinuousOn (fun t => Ap t - Am t) (Icc 0 (4 * h)) := hp.cont.sub hm.cont
  have hG0 : Ap 0 - Am 0 = 0 := by rw [hp0, hm0, sub_self]
  have hA : ∀ t ∈ Icc 0 (4 * h), ‖Ap t - Am t‖ ≤ 8 * t := by
    have H := norm_image_sub_le_of_norm_deriv_right_le_segment hGc hGd (C := 8) (fun t _ => by
      have := norm_sub_le (Mη 1 (Ap t)) (Mη (-1) (Am t))
      linarith [norm_Mη_le (η := 1) (by norm_num) (Ap t),
        norm_Mη_le (η := -1) (by norm_num) (Am t)])
    intro t ht
    have h1 : ‖(Ap t - Am t) - (Ap 0 - Am 0)‖ ≤ 8 * (t - 0) := H t ht
    rwa [hG0, sub_zero, sub_zero] at h1
  have hsplit : ∀ t, ‖Mη 1 (Ap t) - Mη (-1) (Am t)‖ ≤
      10 * ‖Ap t - Am t‖ + 4 * |Am t 2 0| := by
    intro t
    have e : Mη 1 (Ap t) - Mη (-1) (Am t) =
        (Mη 1 (Ap t) - Mη 1 (Am t)) + (Mη 1 (Am t) - Mη (-1) (Am t)) := by abel
    rw [e]
    linarith [norm_add_le (Mη 1 (Ap t) - Mη 1 (Am t)) (Mη 1 (Am t) - Mη (-1) (Am t)),
      Mη_lipschitz (η := 1) (by norm_num) (Ap t) (Am t), norm_Mη_sub_le (Am t)]
  have hB : ∀ t ∈ Icc 0 (4 * h), ‖Ap t - Am t‖ ≤ 404 * h * t := by
    have H := norm_image_sub_le_of_norm_deriv_right_le_segment hGc hGd (C := 404 * h)
      (fun t ht => by
        have htI : t ∈ Icc 0 (4 * h) := Ico_subset_Icc_self ht
        have h1 := hA t htI
        have h2 := hentry t htI
        have h3 := hsplit t
        have : t ≤ 4 * h := htI.2
        nlinarith)
    intro t ht
    have h1 : ‖(Ap t - Am t) - (Ap 0 - Am 0)‖ ≤ 404 * h * (t - 0) := H t ht
    rwa [hG0, sub_zero, sub_zero] at h1
  -- the entry `x₃₁` of `A₋`
  have hφd : ∀ t ∈ Ico 0 (4 * h), HasDerivWithinAt (fun t => √2 * Am t 2 0 - t)
      (√2 * (Fj j (-1) t (Am t)) 2 0 - 1) (Ici t) t := fun t ht =>
    ((hasDerivWithinAt_entry (hm.deriv t ht)).const_mul √2).sub (hasDerivWithinAt_id t _)
  have hφc : ContinuousOn (fun t => √2 * Am t 2 0 - t) (Icc 0 (4 * h)) :=
    (continuousOn_const.mul (continuousOn_entry hm.cont)).sub continuousOn_id
  have hφ0 : √2 * Am 0 2 0 - 0 = 0 := by
    rw [hm0]; simp [Y0, E11, E22]
  have hC : ∀ t ∈ Icc 0 (4 * h), |√2 * Am t 2 0 - t| ≤ 315 * h * t := by
    have H := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd (C := 315 * h)
      (fun t ht => by
        have htI : t ∈ Icc 0 (4 * h) := Ico_subset_Icc_self ht
        have e1 : (Fj j (-1) t (Am t)) 2 0 = (Mη (-1) (Am t)) 2 0 := by
          simp [Fj, Rj_entry]
        have e2 : (Mη (-1) E11) 2 0 = 1 / √2 := by
          rw [Mη_E11]; simp [Hm]
        have e3 : √2 * (Fj j (-1) t (Am t)) 2 0 - 1 =
            √2 * (Mη (-1) (Am t) - Mη (-1) E11) 2 0 := by
          rw [e1, Matrix.sub_apply, e2, mul_sub]
          field_simp
        rw [Real.norm_eq_abs, e3, abs_mul, abs_of_pos hs0]
        have h1 := (Frobenius.abs_apply_le_norm (Mη (-1) (Am t) - Mη (-1) E11) 2 0).trans
          (Mη_lipschitz (η := -1) (by norm_num) (Am t) E11)
        have h2 := hρ t htI
        have := abs_nonneg ((Mη (-1) (Am t) - Mη (-1) E11) 2 0)
        nlinarith)
    intro t ht
    have h1 : ‖(√2 * Am t 2 0 - t) - (√2 * Am 0 2 0 - 0)‖ ≤ 315 * h * (t - 0) := H t ht
    rwa [hφ0, sub_zero, sub_zero, Real.norm_eq_abs] at h1
  -- the main estimate
  have hfd : ∀ t ∈ Ico 0 (4 * h), HasDerivWithinAt (fun t => Ap t - Am t - (t ^ 2 / 2) • Hm)
      (Mη 1 (Ap t) - Mη (-1) (Am t) - t • Hm) (Ici t) t := by
    intro t ht
    have hq : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) • Hm) (t • Hm) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const Hm
      convert this using 2
      push_cast
      ring
    exact (hGd t ht).sub hq.hasDerivWithinAt
  have hfc : ContinuousOn (fun t => Ap t - Am t - (t ^ 2 / 2) • Hm) (Icc 0 (4 * h)) :=
    hGc.sub ((continuousOn_id.pow 2).div_const 2 |>.smul continuousOn_const)
  have H := norm_image_sub_le_of_norm_deriv_right_le_segment hfc hfd (C := 23342 * h ^ 2)
    (fun t ht => by
      have htI : t ∈ Icc 0 (4 * h) := Ico_subset_Icc_self ht
      have e : Mη 1 (Ap t) - Mη (-1) (Am t) - t • Hm = (Mη 1 (Ap t) - Mη 1 (Am t)) +
          (Mη 1 (Am t) - Mη (-1) (Am t) - (√2 * Am t 2 0) • Hm) +
          (√2 * Am t 2 0 - t) • Hm := by
        rw [sub_smul]; abel
      have hρ1 : ‖Am t - E11‖ ≤ 1 := (hρ t htI).trans (by linarith)
      have k1 := (Mη_lipschitz (η := 1) (by norm_num) (Ap t) (Am t)).trans
        (mul_le_mul_of_nonneg_left (hB t htI) (by norm_num))
      have k2 := Mη_sub_taylor (Am t) hρ1
      have k3 : ‖(√2 * Am t 2 0 - t) • Hm‖ ≤ 315 * h * t * (3 / 2) := by
        rw [norm_smul, norm_Hm, Real.norm_eq_abs]
        exact mul_le_mul (hC t htI) hs2 hs0.le (mul_nonneg (by positivity) htI.1)
      have k4 : ‖Am t - E11‖ ^ 2 ≤ (21 * h) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hρ t htI) 2
      have ht4 : t ≤ 4 * h := htI.2
      have ht0 : 0 ≤ t := htI.1
      rw [e]
      have n1 := norm_add_le ((Mη 1 (Ap t) - Mη 1 (Am t)) +
          (Mη 1 (Am t) - Mη (-1) (Am t) - (√2 * Am t 2 0) • Hm)) ((√2 * Am t 2 0 - t) • Hm)
      have n2 := norm_add_le (Mη 1 (Ap t) - Mη 1 (Am t))
          (Mη 1 (Am t) - Mη (-1) (Am t) - (√2 * Am t 2 0) • Hm)
      have : h * t ≤ 4 * h ^ 2 := by nlinarith
      nlinarith)
  have hend : (4 * h) ∈ Icc 0 (4 * h) := ⟨by positivity, le_rfl⟩
  have h1 : ‖(Ap (4 * h) - Am (4 * h) - ((4 * h) ^ 2 / 2) • Hm) -
      (Ap 0 - Am 0 - ((0 : ℝ) ^ 2 / 2) • Hm)‖ ≤ 23342 * h ^ 2 * (4 * h - 0) := H _ hend
  have e4 : (4 * h) ^ 2 / 2 = 8 * h ^ 2 := by ring
  rw [hG0, e4] at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_smul,
    sub_zero] at h1
  nlinarith

/-- The hypotheses of `lemma_4_3` can be met (arXiv 2608.12893, Lemma 4.3): the exact flows of
`F_{j,η}` from `Y⁰_j` exist on `[0, 4 h_j]` (Picard–Lindelöf; `F_{j,η}` is bounded, Lipschitz,
and continuous in `t` there). -/
theorem exists_solution {j : ℕ} (hj1 : 1 ≤ j) {η : ℝ} (hη : |η| ≤ 1) :
    ∃ A : ℝ → M₃, ODESolution (Fj j η) A 0 (4 * hj j) ∧ A 0 = Y0 j := by
  have hh := hj_pos j
  obtain ⟨hB, hL, -⟩ := prop_3_2 hj1 hη
  refine exists_ODESolution_of_continuousOn hL hB (fun X => ?_) (by positivity) (Y0 j)
  have hWc : Continuous Wd := by
    rw [show Wd = fun θ => (-(Real.sin (Real.pi * θ / 2) * (Real.pi / 2)) / 2) • A23 +
      (Real.cos (Real.pi * θ / 2) * (Real.pi / 2) / 2) • B23 from funext Wd_eq]
    fun_prop
  have hg : Continuous fun t => Mη η X + (hj j ^ 3 * (1 / hj j)) • Wd (t / hj j) := by
    fun_prop
  refine hg.continuousOn.congr fun t ht => ?_
  have hjt : t ≤ 4 * j * hj j := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith [ht.2]
  simp only [Fj, Rj, th, dth, ite_eq_left hjt]

/-! ### Prop. 3.2: the time derivatives of `F_{j,η}` -/

/-- `ψ''`. -/
def ddpsi (x : ℝ) : ℝ := 180 * x ^ 2 - 780 * x ^ 3 + 1020 * x ^ 4 - 420 * x ^ 5

/-- `ψ'''`. -/
def dddpsi (x : ℝ) : ℝ := 360 * x - 2340 * x ^ 2 + 4080 * x ^ 3 - 2100 * x ^ 4

private theorem hasDerivAt_dpsi (x : ℝ) : HasDerivAt dpsi (ddpsi x) x := by
  have h := (((((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_pow 3 x).const_mul 60)).sub
    ((hasDerivAt_pow 4 x).const_mul 195)).add ((hasDerivAt_pow 5 x).const_mul 204)).sub
    ((hasDerivAt_pow 6 x).const_mul 70))
  convert h using 1
  · funext y; simp [dpsi]
  · simp only [ddpsi]; push_cast; ring

private theorem hasDerivAt_ddpsi (x : ℝ) : HasDerivAt ddpsi (dddpsi x) x := by
  have h := ((((hasDerivAt_pow 2 x).const_mul 180).sub ((hasDerivAt_pow 3 x).const_mul 780)).add
    ((hasDerivAt_pow 4 x).const_mul 1020)).sub ((hasDerivAt_pow 5 x).const_mul 420)
  convert h using 1
  · funext y; simp [ddpsi]
  · simp only [dddpsi]; push_cast; ring

/-- `|ψ''| ≤ 15` on `[0, 1]`, as in the paper (the true maximum is about `5.03`). -/
private theorem abs_ddpsi_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |ddpsi x| ≤ 15 := by
  have e : ddpsi x = -(60 * (x * (1 - x)) ^ 2 * (7 * x - 3)) := by unfold ddpsi; ring
  have hx : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hx0 : 0 ≤ x * (1 - x) := mul_nonneg h0 (by linarith)
  have h7 : |7 * x - 3| ≤ 4 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 60 * (x * (1 - x)) ^ 2)]
  have : (x * (1 - x)) ^ 2 ≤ 1 / 16 := by nlinarith
  have := abs_nonneg (7 * x - 3)
  nlinarith

/-- `|ψ'''| ≤ 1110` on `[0, 1]`, as in the paper (the true maximum is about `26.6`). -/
private theorem abs_dddpsi_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |dddpsi x| ≤ 1110 := by
  have e : dddpsi x = 60 * (x * (1 - x)) * (35 * x ^ 2 - 33 * x + 6) := by unfold dddpsi; ring
  have hx : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hx0 : 0 ≤ x * (1 - x) := mul_nonneg h0 (by linarith)
  have h7 : |35 * x ^ 2 - 33 * x + 6| ≤ 74 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 60 * (x * (1 - x)))]
  have := abs_nonneg (35 * x ^ 2 - 33 * x + 6)
  nlinarith

/-- `ϑ_j''`. -/
noncomputable def ddth (j : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 4 * j * hj j then 0
  else if t ≤ 4 * (j + 1) * hj j then ddpsi ((t - 4 * j * hj j) / (4 * hj j)) / (4 * hj j ^ 2)
  else 0

/-- `ϑ_j'''`. -/
noncomputable def dddth (j : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 4 * j * hj j then 0
  else if t ≤ 4 * (j + 1) * hj j then dddpsi ((t - 4 * j * hj j) / (4 * hj j)) / (16 * hj j ^ 3)
  else 0

private theorem hasDerivAt_dth (j : ℕ) (t : ℝ) : HasDerivAt (dth j) (ddth j t) t := by
  have hh := hj_pos j
  set h := hj j
  have hx : ∀ t, HasDerivAt (fun t => (t - 4 * j * h) / (4 * h)) (1 / (4 * h)) t := fun t => by
    simpa using ((hasDerivAt_id t).sub_const (4 * j * h)).div_const (4 * h)
  have hp : ∀ t, HasDerivAt (fun t => dpsi ((t - 4 * j * h) / (4 * h)) / h)
      (ddpsi ((t - 4 * j * h) / (4 * h)) / (4 * h ^ 2)) t := fun t => by
    have := ((hasDerivAt_dpsi _).comp t (hx t)).div_const h
    refine this.congr_deriv ?_
    field_simp
  have e1 : (4 * (j + 1) * h - 4 * j * h) / (4 * h) = 1 := by field_simp; ring
  have hin : ∀ t, HasDerivAt (fun s => if s ≤ 4 * (j + 1) * h then
      dpsi ((s - 4 * j * h) / (4 * h)) / h else 0)
      (if t ≤ 4 * (j + 1) * h then ddpsi ((t - 4 * j * h) / (4 * h)) / (4 * h ^ 2) else 0) t :=
    hasDerivAt_ite (4 * (j + 1) * h) hp (fun t => hasDerivAt_const t _)
      (by rw [e1]; norm_num [dpsi]) (by rw [e1]; norm_num [ddpsi])
  have hjh : 4 * (j : ℝ) * h ≤ 4 * (j + 1) * h := by nlinarith
  exact hasDerivAt_ite (4 * j * h) (fun t => hasDerivAt_const t (1 / h)) hin
    (by rw [ite_eq_left hjh, sub_self, zero_div]; norm_num [dpsi])
    (by rw [ite_eq_left hjh, sub_self, zero_div]; norm_num [ddpsi]) t

private theorem hasDerivAt_ddth (j : ℕ) (t : ℝ) : HasDerivAt (ddth j) (dddth j t) t := by
  have hh := hj_pos j
  set h := hj j
  have hx : ∀ t, HasDerivAt (fun t => (t - 4 * j * h) / (4 * h)) (1 / (4 * h)) t := fun t => by
    simpa using ((hasDerivAt_id t).sub_const (4 * j * h)).div_const (4 * h)
  have hp : ∀ t, HasDerivAt (fun t => ddpsi ((t - 4 * j * h) / (4 * h)) / (4 * h ^ 2))
      (dddpsi ((t - 4 * j * h) / (4 * h)) / (16 * h ^ 3)) t := fun t => by
    have := ((hasDerivAt_ddpsi _).comp t (hx t)).div_const (4 * h ^ 2)
    refine this.congr_deriv ?_
    field_simp
    ring
  have e1 : (4 * (j + 1) * h - 4 * j * h) / (4 * h) = 1 := by field_simp; ring
  have hin : ∀ t, HasDerivAt (fun s => if s ≤ 4 * (j + 1) * h then
      ddpsi ((s - 4 * j * h) / (4 * h)) / (4 * h ^ 2) else 0)
      (if t ≤ 4 * (j + 1) * h then dddpsi ((t - 4 * j * h) / (4 * h)) / (16 * h ^ 3) else 0) t :=
    hasDerivAt_ite (4 * (j + 1) * h) hp (fun t => hasDerivAt_const t _)
      (by rw [e1]; norm_num [ddpsi]) (by rw [e1]; norm_num [dddpsi])
  have hjh : 4 * (j : ℝ) * h ≤ 4 * (j + 1) * h := by nlinarith
  exact hasDerivAt_ite (4 * j * h) (fun t => hasDerivAt_const t (0 : ℝ)) hin
    (by rw [ite_eq_left hjh, sub_self, zero_div]; norm_num [ddpsi])
    (by rw [ite_eq_left hjh, sub_self, zero_div]; norm_num [dddpsi]) t

/-- `W''`. -/
noncomputable def Wdd (θ : ℝ) : M₃ :=
  (-(Real.cos (Real.pi * θ / 2) * (Real.pi / 2) ^ 2) / 2) • A23 +
    (-(Real.sin (Real.pi * θ / 2) * (Real.pi / 2) ^ 2) / 2) • B23

/-- `W'''`. -/
noncomputable def Wddd (θ : ℝ) : M₃ := (Real.sin (Real.pi * θ / 2) * (Real.pi / 2) ^ 3 / 2) • A23 +
    (-(Real.cos (Real.pi * θ / 2) * (Real.pi / 2) ^ 3) / 2) • B23

private theorem hasDerivAt_Wd (θ : ℝ) : HasDerivAt Wd (Wdd θ) θ := by
  have hu : HasDerivAt (fun θ : ℝ => Real.pi * θ / 2) (Real.pi / 2) θ := by
    simpa using ((hasDerivAt_id θ).const_mul Real.pi).div_const 2
  have hs := (((Real.hasDerivAt_sin _).comp θ hu).mul_const (Real.pi / 2)).neg.div_const 2
  have hc := (((Real.hasDerivAt_cos _).comp θ hu).mul_const (Real.pi / 2)).div_const 2
  have h := (hs.smul_const A23).add (hc.smul_const B23)
  have e : Wd = fun θ => (-(Real.sin (Real.pi * θ / 2) * (Real.pi / 2)) / 2) • A23 +
      (Real.cos (Real.pi * θ / 2) * (Real.pi / 2) / 2) • B23 := funext Wd_eq
  rw [e]
  refine h.congr_deriv ?_
  simp only [Wdd]
  module

private theorem hasDerivAt_Wdd (θ : ℝ) : HasDerivAt Wdd (Wddd θ) θ := by
  have hu : HasDerivAt (fun θ : ℝ => Real.pi * θ / 2) (Real.pi / 2) θ := by
    simpa using ((hasDerivAt_id θ).const_mul Real.pi).div_const 2
  have hc := (((Real.hasDerivAt_cos _).comp θ hu).mul_const ((Real.pi / 2) ^ 2)).neg.div_const 2
  have hs := (((Real.hasDerivAt_sin _).comp θ hu).mul_const ((Real.pi / 2) ^ 2)).neg.div_const 2
  have h := (hc.smul_const A23).add (hs.smul_const B23)
  refine h.congr_deriv ?_
  simp only [Wddd]
  module

private theorem norm_AB (α β' : ℝ) : ‖α • A23 + β' • B23‖ = √2 * √(α ^ 2 + β' ^ 2) := by
  have h : ‖α • A23 + β' • B23‖ ^ 2 = 2 * (α ^ 2 + β' ^ 2) := by
    rw [Frobenius.norm_sq_eq_sum]; simp [A23, B23, Fin.sum_univ_three]; ring
  rw [← Real.sqrt_mul (by norm_num), ← h, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_Wdd (θ : ℝ) : ‖Wdd θ‖ = √2 * (Real.pi ^ 2 / 8) := by
  rw [Wdd, norm_AB]
  congr 1
  rw [show (-(Real.cos (Real.pi * θ / 2) * (Real.pi / 2) ^ 2) / 2) ^ 2 +
      (-(Real.sin (Real.pi * θ / 2) * (Real.pi / 2) ^ 2) / 2) ^ 2 = (Real.pi ^ 2 / 8) ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ / 2)]]
  exact Real.sqrt_sq (by positivity)

private theorem norm_Wddd (θ : ℝ) : ‖Wddd θ‖ = √2 * (Real.pi ^ 3 / 16) := by
  rw [Wddd, norm_AB]
  congr 1
  rw [show (Real.sin (Real.pi * θ / 2) * (Real.pi / 2) ^ 3 / 2) ^ 2 +
      (-(Real.cos (Real.pi * θ / 2) * (Real.pi / 2) ^ 3) / 2) ^ 2 = (Real.pi ^ 3 / 16) ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ / 2)]]
  exact Real.sqrt_sq (by positivity)

/-- `∂_t R_j`. -/
noncomputable def Rd (j : ℕ) (t : ℝ) : M₃ :=
  hj j ^ 3 • (ddth j t • Wd (th j t) + dth j t ^ 2 • Wdd (th j t))

/-- `∂_t² R_j`. -/
noncomputable def Rdd (j : ℕ) (t : ℝ) : M₃ :=
  hj j ^ 3 • (dddth j t • Wd (th j t) + (3 * dth j t * ddth j t) • Wdd (th j t) +
    dth j t ^ 3 • Wddd (th j t))

/-- `∂_t F_{j,η} = ∂_t R_j = Rd j` (arXiv 2608.12893, Prop. 3.2, the bound `κ`). -/
theorem hasDerivAt_Rj (j : ℕ) (t : ℝ) : HasDerivAt (Rj j) (Rd j t) t := by
  have hc := (hasDerivAt_dth j t).const_mul (hj j ^ 3)
  have hf := (hasDerivAt_Wd (th j t)).scomp t (hasDerivAt_th j t)
  have h := hc.smul hf
  refine h.congr_deriv ?_
  simp only [Rd, Function.comp_apply]
  module

/-- `∂_t² R_j = Rdd j` (arXiv 2608.12893, Prop. 3.2, the bound `κ`). -/
theorem hasDerivAt_Rd (j : ℕ) (t : ℝ) : HasDerivAt (Rd j) (Rdd j t) t := by
  have hsq : HasDerivAt (fun s => dth j s ^ 2) (2 * dth j t * ddth j t) t :=
    ((hasDerivAt_dth j t).pow 2).congr_deriv (by norm_num)
  have h1 := (hasDerivAt_ddth j t).smul ((hasDerivAt_Wd (th j t)).scomp t (hasDerivAt_th j t))
  have h2 := hsq.smul ((hasDerivAt_Wdd (th j t)).scomp t (hasDerivAt_th j t))
  have h := (h1.add h2).const_smul (hj j ^ 3)
  refine h.congr_deriv ?_
  simp only [Rdd, Function.comp_apply]
  module

private theorem pi_bounds : Real.pi ≤ 3.1416 ∧ 0 < Real.pi := ⟨Real.pi_lt_d4.le, Real.pi_pos⟩

private theorem sqrt_two_le : √2 ≤ 1.41422 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- `‖∂_t R_j‖ ≤ 123` (arXiv 2608.12893, Prop. 3.2, `κ = 123`). -/
theorem norm_Rd_le {j : ℕ} (hj1 : 1 ≤ j) (t : ℝ) : ‖Rd j t‖ ≤ 123 := by
  have hh := hj_pos j
  have hh1 := hj_le_half hj1
  obtain ⟨hp, hp0⟩ := pi_bounds
  have hs := sqrt_two_le
  have hs0 := Real.sqrt_nonneg 2
  have hWd : ‖Wd (th j t)‖ ≤ 2 := by
    rw [norm_Wd]; nlinarith
  have hWdd : ‖Wdd (th j t)‖ ≤ 3 := by
    rw [norm_Wdd]
    have : Real.pi ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ hp0.le hp 2
    nlinarith
  have hb : beta ≤ 2 := by norm_num [beta]
  rw [Rd, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold ddth dth
  split_ifs with h1 h2
  · rw [zero_smul, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have e : hj j ^ 3 * ((1 / hj j) ^ 2 * ‖Wdd (th j t)‖) = hj j * ‖Wdd (th j t)‖ := by
      field_simp
    rw [e]; nlinarith [norm_nonneg (Wdd (th j t))]
  · set x := (t - 4 * j * hj j) / (4 * hj j)
    have hx0 : 0 ≤ x := div_nonneg (by linarith) (by positivity)
    have hx1 : x ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have k1 := abs_ddpsi_le hx0 hx1
    have k2 := dpsi_nonneg hx0 hx1
    have k3 := dpsi_le_beta hx0 hx1
    have n := norm_add_le ((ddpsi x / (4 * hj j ^ 2)) • Wd (th j t))
      ((dpsi x / hj j) ^ 2 • Wdd (th j t))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * hj j ^ 2),
      abs_of_nonneg (sq_nonneg (dpsi x / hj j))] at n
    have e : hj j ^ 3 * (|ddpsi x| / (4 * hj j ^ 2) * ‖Wd (th j t)‖ +
        (dpsi x / hj j) ^ 2 * ‖Wdd (th j t)‖) =
        hj j * (|ddpsi x| / 4 * ‖Wd (th j t)‖ + dpsi x ^ 2 * ‖Wdd (th j t)‖) := by
      field_simp
    have hd2 : dpsi x ^ 2 ≤ 4 := by nlinarith
    have hin : |ddpsi x| / 4 * ‖Wd (th j t)‖ + dpsi x ^ 2 * ‖Wdd (th j t)‖ ≤
        15 / 4 * 2 + 4 * 3 := by
      have := norm_nonneg (Wd (th j t))
      have := norm_nonneg (Wdd (th j t))
      have := abs_nonneg (ddpsi x)
      gcongr
    have hin0 : 0 ≤ |ddpsi x| / 4 * ‖Wd (th j t)‖ + dpsi x ^ 2 * ‖Wdd (th j t)‖ := by positivity
    calc hj j ^ 3 * ‖(ddpsi x / (4 * hj j ^ 2)) • Wd (th j t) + (dpsi x / hj j) ^ 2 • Wdd (th j t)‖
        ≤ hj j ^ 3 * (|ddpsi x| / (4 * hj j ^ 2) * ‖Wd (th j t)‖ +
          (dpsi x / hj j) ^ 2 * ‖Wdd (th j t)‖) := by gcongr
      _ = _ := e
      _ ≤ 1 * (15 / 4 * 2 + 4 * 3) := by gcongr; linarith
      _ ≤ 123 := by norm_num
  · simp

/-- `‖∂_t² R_j‖ ≤ 123` (arXiv 2608.12893, Prop. 3.2, `κ = 123`; the constant is that of the
paper's proof, with `|ψ''| ≤ 15`, `|ψ'''| ≤ 1110`). -/
theorem norm_Rdd_le (j : ℕ) (t : ℝ) : ‖Rdd j t‖ ≤ 123 := by
  have hh := hj_pos j
  obtain ⟨hp, hp0⟩ := pi_bounds
  have hs := sqrt_two_le
  have hs0 := Real.sqrt_nonneg 2
  have hp2 : Real.pi ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ hp0.le hp 2
  have hp3 : Real.pi ^ 3 ≤ 3.1416 ^ 3 := pow_le_pow_left₀ hp0.le hp 3
  rw [Rdd, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  unfold dddth ddth dth
  split_ifs with h1 h2
  · simp only [zero_smul, zero_add, mul_zero, norm_smul, Real.norm_eq_abs, norm_Wddd]
    rw [abs_of_pos (by positivity)]
    have e : hj j ^ 3 * ((1 / hj j) ^ 3 * (√2 * (Real.pi ^ 3 / 16))) =
        √2 * (Real.pi ^ 3 / 16) := by field_simp
    rw [e]
    nlinarith
  · set x := (t - 4 * j * hj j) / (4 * hj j)
    have hx0 : 0 ≤ x := div_nonneg (by linarith) (by positivity)
    have hx1 : x ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have k1 := abs_ddpsi_le hx0 hx1
    have k1' := abs_dddpsi_le hx0 hx1
    have k2 := dpsi_nonneg hx0 hx1
    have k3 := dpsi_le_beta hx0 hx1
    have n : ‖(dddpsi x / (16 * hj j ^ 3)) • Wd (th j t) +
        (3 * (dpsi x / hj j) * (ddpsi x / (4 * hj j ^ 2))) • Wdd (th j t) +
        (dpsi x / hj j) ^ 3 • Wddd (th j t)‖ ≤ ‖(dddpsi x / (16 * hj j ^ 3)) • Wd (th j t)‖ +
        ‖(3 * (dpsi x / hj j) * (ddpsi x / (4 * hj j ^ 2))) • Wdd (th j t)‖ +
        ‖(dpsi x / hj j) ^ 3 • Wddd (th j t)‖ := norm_add₃_le
    simp only [norm_smul, Real.norm_eq_abs, norm_Wd, norm_Wdd, norm_Wddd] at n
    have e1 : hj j ^ 3 * |dddpsi x / (16 * hj j ^ 3)| = |dddpsi x| / 16 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 * hj j ^ 3)]; field_simp
    have e2 : hj j ^ 3 * |3 * (dpsi x / hj j) * (ddpsi x / (4 * hj j ^ 2))| =
        3 / 4 * dpsi x * |ddpsi x| := by
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hh, abs_of_nonneg k2,
        abs_of_pos (by positivity : (0 : ℝ) < 4 * hj j ^ 2), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      field_simp
    have e3 : hj j ^ 3 * |(dpsi x / hj j) ^ 3| = dpsi x ^ 3 := by
      rw [abs_of_nonneg (by positivity)]; field_simp
    have hb : beta ≤ 1.6603 := by norm_num [beta]
    have hd3 : dpsi x ^ 3 ≤ 1.6603 ^ 3 := pow_le_pow_left₀ k2 (k3.trans hb) 3
    have hdd : dpsi x * |ddpsi x| ≤ 1.6603 * 15 :=
      mul_le_mul (k3.trans hb) k1 (abs_nonneg _) (by norm_num)
    have hA : 0 ≤ √2 * (Real.pi / 4) := by positivity
    have hB : 0 ≤ √2 * (Real.pi ^ 2 / 8) := by positivity
    have hC : 0 ≤ √2 * (Real.pi ^ 3 / 16) := by positivity
    calc hj j ^ 3 * ‖(dddpsi x / (16 * hj j ^ 3)) • Wd (th j t) +
          (3 * (dpsi x / hj j) * (ddpsi x / (4 * hj j ^ 2))) • Wdd (th j t) +
          (dpsi x / hj j) ^ 3 • Wddd (th j t)‖
        ≤ hj j ^ 3 * (|dddpsi x / (16 * hj j ^ 3)| * (√2 * (Real.pi / 4)) +
          |3 * (dpsi x / hj j) * (ddpsi x / (4 * hj j ^ 2))| * (√2 * (Real.pi ^ 2 / 8)) +
          |(dpsi x / hj j) ^ 3| * (√2 * (Real.pi ^ 3 / 16))) := by gcongr
      _ = |dddpsi x| / 16 * (√2 * (Real.pi / 4)) +
          3 / 4 * (dpsi x * |ddpsi x|) * (√2 * (Real.pi ^ 2 / 8)) +
          dpsi x ^ 3 * (√2 * (Real.pi ^ 3 / 16)) := by
        linear_combination (√2 * (Real.pi / 4)) * e1 + (√2 * (Real.pi ^ 2 / 8)) * e2 +
          (√2 * (Real.pi ^ 3 / 16)) * e3
      _ ≤ 1110 / 16 * (√2 * (Real.pi / 4)) + 3 / 4 * (1.6603 * 15) * (√2 * (Real.pi ^ 2 / 8)) +
          1.6603 ^ 3 * (√2 * (Real.pi ^ 3 / 16)) := by gcongr
      _ = √2 * (1110 / 64 * Real.pi + 45 * 1.6603 / 32 * Real.pi ^ 2 +
          1.6603 ^ 3 / 16 * Real.pi ^ 3) := by ring
      _ ≤ 1.41422 * (1110 / 64 * 3.1416 + 45 * 1.6603 / 32 * 3.1416 ^ 2 +
          1.6603 ^ 3 / 16 * 3.1416 ^ 3) := by gcongr
      _ ≤ 123 := by norm_num
  · simp

/-! ### Prop. 3.2: the second derivative of `M_η` -/

/-- `X ↦ Ω X - X Ω` as a continuous linear map. -/
noncomputable def commL : M₃ →L[ℝ] M₃ := Frobenius.leftMulCLM Om - Frobenius.rightMulCLM Om

private theorem commL_apply (X : M₃) : commL X = comm X := by
  simp [commL, comm]

/-- `X ↦ x₃₁` as a continuous linear map. -/
noncomputable def e31 : M₃ →L[ℝ] ℝ := innerSL ℝ E31

private theorem e31_apply (X : M₃) : e31 X = X 2 0 := by
  simp [e31, innerSL_apply_apply, inner_E31]

/-- `Dq_η(X)[Z] = η sech²(x₃₁) z₃₁ / s - (1 + η tanh x₃₁) ⟪X, Z⟫ / s³`, `s = √(1 + ‖X‖²)`. -/
noncomputable def dq (η : ℝ) (X : M₃) : M₃ →L[ℝ] ℝ :=
  (η * (1 / Real.cosh (X 2 0) ^ 2) / √(1 + ‖X‖ ^ 2)) • e31 -
    ((1 + η * Real.tanh (X 2 0)) / √(1 + ‖X‖ ^ 2) ^ 3) • innerSL ℝ X

/-- `DM_η(X)[Z] = q_η(X) (Ω Z - Z Ω) + Dq_η(X)[Z] (Ω X - X Ω)`. -/
noncomputable def DM (η : ℝ) (X : M₃) : M₃ →L[ℝ] M₃ :=
  qη η X • commL + (dq η X).smulRight (comm X)

private theorem hasFDerivAt_qη (η : ℝ) (X : M₃) : HasFDerivAt (qη η) (dq η X) X := by
  have hs0 : 0 < √(1 + ‖X‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hn : HasFDerivAt (fun X : M₃ => 1 + ‖X‖ ^ 2) (2 • (innerSL ℝ X).comp
      (ContinuousLinearMap.id ℝ M₃)) X := ((hasFDerivAt_id X).norm_sq).const_add 1
  have hs := hn.sqrt (by positivity)
  have hi := (hasDerivAt_inv hs0.ne').comp_hasFDerivAt X hs
  have ht := (((hasDerivAt_tanh (e31 X)).comp_hasFDerivAt X e31.hasFDerivAt).const_mul η).const_add
    (1 : ℝ)
  have h := ht.mul hi
  have hfun : qη η = (fun y => 1 + η * (Real.tanh ∘ e31) y) *
      ((fun y => y⁻¹) ∘ fun y : M₃ => √(1 + ‖y‖ ^ 2)) := by
    funext y
    simp [qη, e31_apply, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv ?_
  ext1 Z
  simp [dq, e31_apply]
  field_simp
  ring

/-- `DM_η` is the Fréchet derivative of `M_η` (arXiv 2608.12893, proof of Prop. 3.2). -/
theorem hasFDerivAt_Mη (η : ℝ) (X : M₃) : HasFDerivAt (Mη η) (DM η X) X := by
  have hc : HasFDerivAt comm commL X := by
    have h := commL.hasFDerivAt (x := X)
    rwa [show (⇑commL : M₃ → M₃) = comm from funext commL_apply] at h
  exact (hasFDerivAt_qη η X).smul hc

/-- The map `X ↦ X / (1 + ‖X‖²)`. -/
noncomputable def mX (X : M₃) : M₃ := (1 / (1 + ‖X‖ ^ 2)) • X

private theorem DM_apply (η : ℝ) (X Z : M₃) : DM η X Z = qη η X • comm Z +
    ((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
    (⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) := by
  have hs0 : 0 < √(1 + ‖X‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : √(1 + ‖X‖ ^ 2) ^ 2 = 1 + ‖X‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hs3 : √(1 + ‖X‖ ^ 2) ^ 3 = (1 + ‖X‖ ^ 2) * √(1 + ‖X‖ ^ 2) := by
    rw [pow_succ, hs2]
  have e1 : DM η X Z = qη η X • comm Z + (dq η X Z) • comm X := by
    simp [DM, commL_apply]
  have e2 : dq η X Z = η * (1 / Real.cosh (X 2 0) ^ 2) / √(1 + ‖X‖ ^ 2) * Z 2 0 -
      (1 + η * Real.tanh (X 2 0)) / √(1 + ‖X‖ ^ 2) ^ 3 * ⟪X, Z⟫ := by
    simp [dq, e31_apply]
  rw [e1, e2, hs3, nrm, mX, comm_smul, real_inner_smul_left]
  generalize 1 + ‖X‖ ^ 2 = u
  module

private theorem abs_inv_sqrt_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |1 / √(1 + a ^ 2) - 1 / √(1 + b ^ 2)| ≤ |a - b| := by
  set sa := √(1 + a ^ 2)
  set sb := √(1 + b ^ 2)
  have sa1 : 1 ≤ sa := one_le_sqrt_one_add_sq a
  have sb1 : 1 ≤ sb := one_le_sqrt_one_add_sq b
  have saa : a ≤ sa := by simpa [abs_of_nonneg ha] using abs_le_sqrt_one_add_sq a
  have sbb : b ≤ sb := by simpa [abs_of_nonneg hb] using abs_le_sqrt_one_add_sq b
  have sa2 : sa ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have sb2 : sb ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have e : 1 / sa - 1 / sb = (sb - sa) / (sa * sb) := by field_simp
  have key : |sb - sa| * (sa + sb) = |a - b| * (a + b) := by
    have : (sb - sa) * (sa + sb) = (b - a) * (a + b) := by nlinarith
    have h1 : |sb - sa| * (sa + sb) = |(sb - sa) * (sa + sb)| := by
      rw [abs_mul, abs_of_pos (show 0 < sa + sb by linarith)]
    rw [h1, this, abs_mul, abs_of_nonneg (show 0 ≤ a + b by linarith), abs_sub_comm]
  have hd : |sb - sa| ≤ |a - b| := by
    have hpos : 0 < sa + sb := by linarith
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hp : 0 < sa * sb := mul_pos (by linarith) (by linarith)
  have h1 : 1 ≤ sa * sb := one_le_mul_of_one_le_of_one_le sa1 sb1
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have := abs_nonneg (a - b)
  nlinarith

private theorem abs_qη_sub_le {η : ℝ} (hη : |η| ≤ 1) (X Y : M₃) :
    |qη η X - qη η Y| ≤ 3 * ‖X - Y‖ := by
  have e : qη η X - qη η Y = η * (Real.tanh (X 2 0) - Real.tanh (Y 2 0)) * (1 / √(1 + ‖X‖ ^ 2)) +
      (1 + η * Real.tanh (Y 2 0)) * (1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Y‖ ^ 2)) := by
    simp only [qη]; ring
  have h1 : |Real.tanh (X 2 0) - Real.tanh (Y 2 0)| ≤ ‖X - Y‖ :=
    (abs_tanh_sub_le _ _).trans (Frobenius.abs_apply_le_norm (X - Y) 2 0)
  have h2 : |1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Y‖ ^ 2)| ≤ ‖X - Y‖ :=
    (abs_inv_sqrt_sub_le (norm_nonneg X) (norm_nonneg Y)).trans (abs_norm_sub_norm_le X Y)
  have h3 : |1 + η * Real.tanh (Y 2 0)| ≤ 2 := by
    have ht := Real.abs_tanh_lt_one (Y 2 0)
    calc |1 + η * Real.tanh (Y 2 0)| ≤ |1| + |η| * |Real.tanh (Y 2 0)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; nlinarith [abs_nonneg η, abs_nonneg (Real.tanh (Y 2 0))]
  have h4 : 0 < 1 / √(1 + ‖X‖ ^ 2) := by positivity
  have h5 : 1 / √(1 + ‖X‖ ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_sqrt_one_add_sq _
  rw [e]
  calc _ ≤ |η * (Real.tanh (X 2 0) - Real.tanh (Y 2 0)) * (1 / √(1 + ‖X‖ ^ 2))| +
        |(1 + η * Real.tanh (Y 2 0)) * (1 / √(1 + ‖X‖ ^ 2) - 1 / √(1 + ‖Y‖ ^ 2))| :=
        abs_add_le _ _
    _ ≤ 1 * ‖X - Y‖ * 1 + 2 * ‖X - Y‖ := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos h4]
        gcongr
    _ = 3 * ‖X - Y‖ := by ring

private theorem abs_sech_sq_sub_le (x y : ℝ) :
    |1 / Real.cosh x ^ 2 - 1 / Real.cosh y ^ 2| ≤ 2 * |x - y| := by
  have e : ∀ z, 1 / Real.cosh z ^ 2 = 1 - Real.tanh z ^ 2 := fun z => by
    have hc := Real.cosh_pos z
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp
    nlinarith [Real.cosh_sq z]
  rw [e, e, show 1 - Real.tanh x ^ 2 - (1 - Real.tanh y ^ 2) =
    (Real.tanh y - Real.tanh x) * (Real.tanh y + Real.tanh x) by ring, abs_mul]
  have h1 := abs_tanh_sub_le y x
  have h2 : |Real.tanh y + Real.tanh x| ≤ 2 := by
    have := Real.abs_tanh_lt_one x
    have := Real.abs_tanh_lt_one y
    calc |Real.tanh y + Real.tanh x| ≤ |Real.tanh y| + |Real.tanh x| := abs_add_le _ _
      _ ≤ 2 := by linarith
  rw [abs_sub_comm y x] at h1
  have := abs_nonneg (Real.tanh y - Real.tanh x)
  nlinarith [abs_nonneg (x - y)]

private theorem sech_sq_mem (x : ℝ) : 0 < 1 / Real.cosh x ^ 2 ∧ 1 / Real.cosh x ^ 2 ≤ 1 := by
  have hc := Real.one_le_cosh x
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

private theorem norm_mX_le (X : M₃) : ‖mX X‖ ≤ 1 / 2 := by
  rw [mX, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_eq_mul_div, one_mul,
    div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖X‖ - 1)]

private theorem norm_mX_sub_le (X Y : M₃) : ‖mX X - mX Y‖ ≤ 2 * ‖X - Y‖ := by
  set a := ‖X‖
  set b := ‖Y‖
  have ha : 0 ≤ a := norm_nonneg X
  have hb : 0 ≤ b := norm_nonneg Y
  have e : mX X - mX Y = (1 / (1 + a ^ 2)) • (X - Y) + (1 / (1 + a ^ 2) - 1 / (1 + b ^ 2)) • Y := by
    simp only [mX, smul_sub, sub_smul, a, b]; abel
  have h1 : ‖(1 / (1 + a ^ 2)) • (X - Y)‖ ≤ ‖X - Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : 1 / (1 + a ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    nlinarith [norm_nonneg (X - Y)]
  have h2 : ‖(1 / (1 + a ^ 2) - 1 / (1 + b ^ 2)) • Y‖ ≤ ‖X - Y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hab : |a - b| ≤ ‖X - Y‖ := abs_norm_sub_norm_le X Y
    have e2 : 1 / (1 + a ^ 2) - 1 / (1 + b ^ 2) =
        (b - a) * (a + b) / ((1 + a ^ 2) * (1 + b ^ 2)) := by
      field_simp; ring
    rw [e2, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 + a ^ 2) * (1 + b ^ 2)),
      abs_of_nonneg (by linarith : 0 ≤ a + b), abs_sub_comm, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    have key : (a + b) * b ≤ (1 + a ^ 2) * (1 + b ^ 2) := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg a, mul_nonneg ha hb]
    have := abs_nonneg (a - b)
    calc |a - b| * (a + b) * b = |a - b| * ((a + b) * b) := by ring
      _ ≤ |a - b| * ((1 + a ^ 2) * (1 + b ^ 2)) := mul_le_mul_of_nonneg_left key this
      _ ≤ ‖X - Y‖ * ((1 + a ^ 2) * (1 + b ^ 2)) := mul_le_mul_of_nonneg_right hab (by positivity)
  rw [e]
  linarith [norm_add_le ((1 / (1 + a ^ 2)) • (X - Y)) ((1 / (1 + a ^ 2) - 1 / (1 + b ^ 2)) • Y)]

private theorem norm_comm_nrm_le (X : M₃) : ‖comm (nrm X)‖ ≤ 2 :=
  (norm_comm_le _).trans (by linarith [norm_nrm_le X])

private theorem norm_comm_nrm_sub_le (X Y : M₃) : ‖comm (nrm X) - comm (nrm Y)‖ ≤ 4 * ‖X - Y‖ := by
  rw [comm_sub]
  exact (norm_comm_le _).trans (by linarith [norm_nrm_sub_le X Y])

/-- `DM_η` is `27`-Lipschitz in operator norm, i.e. `‖D²M_η‖ ≤ 27` (arXiv 2608.12893,
Prop. 3.2: `‖D²M_η‖ ≤ 34`). -/
theorem DM_lipschitz {η : ℝ} (hη : |η| ≤ 1) (X Y : M₃) :
    ‖DM η X - DM η Y‖ ≤ 27 * ‖X - Y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Z => ?_
  have hsub : (DM η X - DM η Y) Z = DM η X Z - DM η Y Z := rfl
  rw [hsub, DM_apply, DM_apply]
  have hz : |Z 2 0| ≤ ‖Z‖ := Frobenius.abs_apply_le_norm Z 2 0
  have hΔ : |X 2 0 - Y 2 0| ≤ ‖X - Y‖ := by
    simpa using Frobenius.abs_apply_le_norm (X - Y) 2 0
  have hΔ0 := norm_nonneg (X - Y)
  have hZ0 := norm_nonneg Z
  have hηz : |η * Z 2 0| ≤ ‖Z‖ := by
    rw [abs_mul]
    calc |η| * |Z 2 0| ≤ 1 * ‖Z‖ := mul_le_mul hη hz (abs_nonneg _) zero_le_one
      _ = ‖Z‖ := one_mul _
  have hbound : ∀ W : M₃, |1 + η * Real.tanh (W 2 0)| ≤ 2 := fun W => by
    have ht := Real.abs_tanh_lt_one (W 2 0)
    calc |1 + η * Real.tanh (W 2 0)| ≤ |1| + |η| * |Real.tanh (W 2 0)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 := by rw [abs_one]; nlinarith [abs_nonneg η, abs_nonneg (Real.tanh (W 2 0))]
  -- first piece
  have p1 : ‖qη η X • comm Z - qη η Y • comm Z‖ ≤ 6 * ‖X - Y‖ * ‖Z‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    calc |qη η X - qη η Y| * ‖comm Z‖ ≤ (3 * ‖X - Y‖) * (2 * ‖Z‖) :=
          mul_le_mul (abs_qη_sub_le hη X Y) (norm_comm_le Z) (norm_nonneg _) (by positivity)
      _ = 6 * ‖X - Y‖ * ‖Z‖ := by ring
  -- second piece
  have p2 : ‖((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
      ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y)‖ ≤ 8 * ‖X - Y‖ * ‖Z‖ := by
    have e : ((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
        ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y) =
        (η * Z 2 0) • ((1 / Real.cosh (X 2 0) ^ 2 - 1 / Real.cosh (Y 2 0) ^ 2) • comm (nrm X) +
          (1 / Real.cosh (Y 2 0) ^ 2) • (comm (nrm X) - comm (nrm Y))) := by
      module
    have b1 : ‖(1 / Real.cosh (X 2 0) ^ 2 - 1 / Real.cosh (Y 2 0) ^ 2) • comm (nrm X)‖ ≤
        (2 * ‖X - Y‖) * 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ((abs_sech_sq_sub_le _ _).trans (by linarith)) (norm_comm_nrm_le X)
        (norm_nonneg _) (by positivity)
    have b2 : ‖(1 / Real.cosh (Y 2 0) ^ 2) • (comm (nrm X) - comm (nrm Y))‖ ≤
        1 * (4 * ‖X - Y‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sech_sq_mem _).1]
      exact mul_le_mul (sech_sq_mem _).2 (norm_comm_nrm_sub_le X Y) (norm_nonneg _) zero_le_one
    have b3 := norm_add_le ((1 / Real.cosh (X 2 0) ^ 2 - 1 / Real.cosh (Y 2 0) ^ 2) •
      comm (nrm X)) ((1 / Real.cosh (Y 2 0) ^ 2) • (comm (nrm X) - comm (nrm Y)))
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |η * Z 2 0| * ‖(1 / Real.cosh (X 2 0) ^ 2 - 1 / Real.cosh (Y 2 0) ^ 2) •
          comm (nrm X) + (1 / Real.cosh (Y 2 0) ^ 2) • (comm (nrm X) - comm (nrm Y))‖ ≤
          ‖Z‖ * (8 * ‖X - Y‖) := mul_le_mul hηz (by linarith) (norm_nonneg _) hZ0
      _ = 8 * ‖X - Y‖ * ‖Z‖ := by ring
  -- third piece
  have p3 : ‖(⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) -
      (⟪mX Y, Z⟫ * (1 + η * Real.tanh (Y 2 0))) • comm (nrm Y)‖ ≤ 13 * ‖X - Y‖ * ‖Z‖ := by
    have e : (⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) -
        (⟪mX Y, Z⟫ * (1 + η * Real.tanh (Y 2 0))) • comm (nrm Y) =
        ⟪mX X - mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X)) +
        ⟪mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X) -
          (1 + η * Real.tanh (Y 2 0)) • comm (nrm Y)) := by
      rw [inner_sub_left]
      module
    have hA : ‖(1 + η * Real.tanh (X 2 0)) • comm (nrm X)‖ ≤ 4 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |1 + η * Real.tanh (X 2 0)| * ‖comm (nrm X)‖ ≤ 2 * 2 :=
            mul_le_mul (hbound X) (norm_comm_nrm_le X) (norm_nonneg _) zero_le_two
        _ = 4 := by norm_num
    have hAB : ‖(1 + η * Real.tanh (X 2 0)) • comm (nrm X) -
        (1 + η * Real.tanh (Y 2 0)) • comm (nrm Y)‖ ≤ 10 * ‖X - Y‖ := by
      have e2 : (1 + η * Real.tanh (X 2 0)) • comm (nrm X) -
          (1 + η * Real.tanh (Y 2 0)) • comm (nrm Y) =
          (η * (Real.tanh (X 2 0) - Real.tanh (Y 2 0))) • comm (nrm X) +
          (1 + η * Real.tanh (Y 2 0)) • (comm (nrm X) - comm (nrm Y)) := by
        module
      have c1 : ‖(η * (Real.tanh (X 2 0) - Real.tanh (Y 2 0))) • comm (nrm X)‖ ≤
          ‖X - Y‖ * 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        have : |η| * |Real.tanh (X 2 0) - Real.tanh (Y 2 0)| ≤ ‖X - Y‖ := by
          calc |η| * |Real.tanh (X 2 0) - Real.tanh (Y 2 0)| ≤ 1 * ‖X - Y‖ :=
                mul_le_mul hη ((abs_tanh_sub_le _ _).trans hΔ) (abs_nonneg _) zero_le_one
            _ = ‖X - Y‖ := one_mul _
        exact mul_le_mul this (norm_comm_nrm_le X) (norm_nonneg _) hΔ0
      have c2 : ‖(1 + η * Real.tanh (Y 2 0)) • (comm (nrm X) - comm (nrm Y))‖ ≤
          2 * (4 * ‖X - Y‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hbound Y) (norm_comm_nrm_sub_le X Y) (norm_nonneg _) zero_le_two
      rw [e2]
      linarith [norm_add_le ((η * (Real.tanh (X 2 0) - Real.tanh (Y 2 0))) • comm (nrm X))
        ((1 + η * Real.tanh (Y 2 0)) • (comm (nrm X) - comm (nrm Y)))]
    have i1 : |⟪mX X - mX Y, Z⟫| ≤ 2 * ‖X - Y‖ * ‖Z‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mX_sub_le X Y) hZ0)
    have i2 : |⟪mX Y, Z⟫| ≤ 1 / 2 * ‖Z‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_mX_le Y) hZ0)
    have d1 : ‖⟪mX X - mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X))‖ ≤
        (2 * ‖X - Y‖ * ‖Z‖) * 4 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul i1 hA (norm_nonneg _) (by positivity)
    have d2 : ‖⟪mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X) -
        (1 + η * Real.tanh (Y 2 0)) • comm (nrm Y))‖ ≤ (1 / 2 * ‖Z‖) * (10 * ‖X - Y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul i2 hAB (norm_nonneg _) (by positivity)
    rw [e]
    have := norm_add_le (⟪mX X - mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X)))
      (⟪mX Y, Z⟫ • ((1 + η * Real.tanh (X 2 0)) • comm (nrm X) -
        (1 + η * Real.tanh (Y 2 0)) • comm (nrm Y)))
    nlinarith
  have e : qη η X • comm Z + ((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
      (⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) -
      (qη η Y • comm Z + ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y) -
      (⟪mX Y, Z⟫ * (1 + η * Real.tanh (Y 2 0))) • comm (nrm Y)) =
      (qη η X • comm Z - qη η Y • comm Z) +
      (((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
        ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y)) -
      ((⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) -
        (⟪mX Y, Z⟫ * (1 + η * Real.tanh (Y 2 0))) • comm (nrm Y)) := by
    abel
  rw [e]
  have n1 := norm_sub_le ((qη η X • comm Z - qη η Y • comm Z) +
      (((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
        ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y)))
      ((⟪mX X, Z⟫ * (1 + η * Real.tanh (X 2 0))) • comm (nrm X) -
        (⟪mX Y, Z⟫ * (1 + η * Real.tanh (Y 2 0))) • comm (nrm Y))
  have n2 := norm_add_le (qη η X • comm Z - qη η Y • comm Z)
      (((η * Z 2 0) * (1 / Real.cosh (X 2 0) ^ 2)) • comm (nrm X) -
        ((η * Z 2 0) * (1 / Real.cosh (Y 2 0) ^ 2)) • comm (nrm Y))
  nlinarith

/-- `M_η` is `C^n` for every `n` (arXiv 2608.12893, Prop. 3.2, smoothness of `F_{j,η}` in
`X`). -/
theorem contDiff_Mη (η : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (Mη η) := by
  have ht : ContDiff ℝ n Real.tanh := by
    have : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
      funext fun x => Real.tanh_eq_sinh_div_cosh x
    rw [this]
    exact Real.contDiff_sinh.div Real.contDiff_cosh fun x => (Real.cosh_pos x).ne'
  have hfun : Mη η = fun y => ((1 + η * Real.tanh (e31 y)) / √(1 + ‖y‖ ^ 2)) • commL y := by
    funext y
    simp [Mη, qη, e31_apply, commL_apply]
  have h1 : ContDiff ℝ n fun y : M₃ => (1 + η * Real.tanh (e31 y)) / √(1 + ‖y‖ ^ 2) := by
    refine ContDiff.div ?_ ?_ fun y => (Real.sqrt_pos.2 (by positivity)).ne'
    · exact contDiff_const.add (contDiff_const.mul (ht.comp e31.contDiff))
    · exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun y => by positivity
  rw [hfun]
  exact h1.smul commL.contDiff

/-- **`‖D²_X F_{j,η}‖ ≤ 27`** (arXiv 2608.12893, Prop. 3.2, part of `κ = 123`; the paper bounds
it by `34`): the second derivative of `M_η`, as a bilinear map in Frobenius norms. -/
theorem norm_iteratedFDeriv_Mη_le {η : ℝ} (hη : |η| ≤ 1) (X : M₃) :
    ‖iteratedFDeriv ℝ 2 (Mη η) X‖ ≤ 27 := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  have hf : fderiv ℝ (Mη η) = DM η := funext fun X => (hasFDerivAt_Mη η X).fderiv
  rw [hf]
  have hL : LipschitzWith 27 (DM η) := LipschitzWith.of_dist_le_mul fun X Y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact_mod_cast DM_lipschitz hη X Y
  exact_mod_cast norm_fderiv_le_of_lipschitz ℝ hL

/-- **`D(M₊ - M₋)(E₁₁)[Z] = √2 z₃₁ H`** (arXiv 2608.12893, proof of Lemma 4.2), with the true
Fréchet derivatives; `Mη_sub_taylor` is the quantitative form. -/
theorem fderiv_Mη_sub_E11 (Z : M₃) :
    fderiv ℝ (Mη 1) E11 Z - fderiv ℝ (Mη (-1)) E11 Z = (√2 * Z 2 0) • Hm := by
  rw [(hasFDerivAt_Mη 1 E11).fderiv, (hasFDerivAt_Mη (-1) E11).fderiv, DM_apply, DM_apply]
  have h0 : E11 2 0 = 0 := by simp [E11]
  have hq : qη 1 E11 = qη (-1) E11 := by simp [qη, h0]
  rw [h0, Real.tanh_zero, Real.cosh_zero, nrm_E11, hq]
  have key : 2 * Z 2 0 * (1 / √2) = √2 * Z 2 0 := by
    have : (2 : ℝ) / √2 = √2 := Real.div_sqrt
    calc 2 * Z 2 0 * (1 / √2) = (2 / √2) * Z 2 0 := by ring
      _ = √2 * Z 2 0 := by rw [this]
  rw [← key]
  module

/-- `D²_X F_{j,η}(t, ·) = D²M_η`, since `R_j` does not depend on `X` (arXiv 2608.12893,
Prop. 3.2). -/
theorem iteratedFDeriv_Fj (j : ℕ) (η t : ℝ) (X : M₃) :
    iteratedFDeriv ℝ 2 (Fj j η t) X = iteratedFDeriv ℝ 2 (Mη η) X := by
  have e : Fj j η t = Mη η + fun _ => Rj j t := by
    funext Y; simp [Fj]
  rw [e, iteratedFDeriv_add_apply (contDiff_Mη η).contDiffAt contDiff_const.contDiffAt,
    iteratedFDeriv_const_of_ne two_ne_zero]
  simp

/-- **Prop. 3.2, the constant `κ = 123`** (arXiv 2608.12893, (2.5)): `F_{j,η}(t, ·)` is `C²` with
`‖D²_X F_{j,η}‖ ≤ 123` (in fact `≤ 27`); `∂_t F_{j,η}(t, X) = Rd j t` does not depend on `X`, so
`D_X ∂_t F_{j,η} = 0`; and `‖∂_t F_{j,η}‖ ≤ 123`, `‖∂_t² F_{j,η}‖ ≤ 123`. For `j ≥ 1` (the paper:
`j ≥ 3`), `|η| ≤ 1` (the paper: `η = ±1`) and every `t` (the paper: `t ∈ [0, 1]`). -/
theorem prop_3_2_kappa {j : ℕ} (hj1 : 1 ≤ j) {η : ℝ} (hη : |η| ≤ 1) :
    (∀ t, ContDiff ℝ 2 (Fj j η t)) ∧ (∀ t X, ‖iteratedFDeriv ℝ 2 (Fj j η t) X‖ ≤ 123) ∧
    (∀ t X, HasDerivAt (fun s => Fj j η s X) (Rd j t) t) ∧
    (∀ t, HasDerivAt (Rd j) (Rdd j t) t) ∧ (∀ t, ‖Rd j t‖ ≤ 123) ∧ (∀ t, ‖Rdd j t‖ ≤ 123) := by
  refine ⟨fun t => ?_, fun t X => ?_, fun t X => ?_, hasDerivAt_Rd j, norm_Rd_le hj1,
    norm_Rdd_le j⟩
  · have e : Fj j η t = fun X => Mη η X + Rj j t := rfl
    rw [e]
    exact (contDiff_Mη η).add contDiff_const
  · rw [iteratedFDeriv_Fj]
    linarith [norm_iteratedFDeriv_Mη_le hη X]
  · exact (hasDerivAt_Rj j t).const_add (Mη η X)


/-! ### The initial value: retained singular values `1` and `h_j³` -/

/-- `B(0) = [e₁, e₂]` (arXiv 2608.12893, (A.1), (A.3)). -/
def B0 : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- A `2 × 2` matrix has rank two iff its determinant is nonzero. -/
private theorem rank_eq_two_iff_det_ne_zero (G : Matrix (Fin 2) (Fin 2) ℝ) :
    G.rank = 2 ↔ G.det ≠ 0 := by
  constructor
  · intro h
    have hs : Function.Surjective G.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.2 (by simpa using h)
    exact ((Matrix.isUnit_iff_isUnit_det G).1 (Matrix.mulVec_surjective_iff_isUnit.1 hs)).ne_zero
  · intro h
    rw [Matrix.rank_of_isUnit G ((Matrix.isUnit_iff_isUnit_det G).2 h.isUnit)]
    simp

/-- **The retained singular values of `Y⁰_j`** (arXiv 2608.12893, Thm 3.1 and (A.3)):
`Y⁰_j = B(0) diag(1, h_j³) B(0)ᵀ` with `B(0) = [e₁, e₂]` orthonormal, so the singular values of
`Y⁰_j` are `1`, `h_j³` and `0`, and `Y⁰_j` has rank two. -/
theorem Y0_svd (j : ℕ) : B0ᵀ * B0 = 1 ∧ Y0 j = B0 * Matrix.diagonal ![1, hj j ^ 3] * B0ᵀ ∧
    (Y0 j).rank = 2 := by
  have hB : B0ᵀ * B0 = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [B0, Matrix.mul_apply, Fin.sum_univ_three]
  have hY : Y0 j = B0 * Matrix.diagonal ![1, hj j ^ 3] * B0ᵀ := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Y0, E11, E22, B0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal]
  refine ⟨hB, hY, le_antisymm ?_ ?_⟩
  · rw [hY]
    calc (B0 * Matrix.diagonal ![1, hj j ^ 3] * B0ᵀ).rank ≤ B0ᵀ.rank :=
          Matrix.rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_card_height _
      _ = 2 := by simp
  · have hD : B0ᵀ * Y0 j * B0 = Matrix.diagonal ![1, hj j ^ 3] := by
      rw [hY]
      calc B0ᵀ * (B0 * Matrix.diagonal ![1, hj j ^ 3] * B0ᵀ) * B0
          = (B0ᵀ * B0) * Matrix.diagonal ![1, hj j ^ 3] * (B0ᵀ * B0) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, Matrix.one_mul, Matrix.mul_one]
    have hr : (Matrix.diagonal ![(1 : ℝ), hj j ^ 3]).rank = 2 := by
      rw [rank_eq_two_iff_det_ne_zero, Matrix.det_diagonal]
      simp [Fin.prod_univ_two, (hj_pos j).ne']
    calc 2 = (B0ᵀ * Y0 j * B0).rank := by rw [hD, hr]
      _ ≤ (B0ᵀ * Y0 j).rank := Matrix.rank_mul_le_left _ _
      _ ≤ _ := Matrix.rank_mul_le_right _ _

/-! ### Prop. 4.4 from Lemma 4.2 -/

/-- `E₁₂`. -/
def E12 : M₃ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

private theorem inner_E12 (X : M₃) : ⟪X, E12⟫ = X 0 1 := by
  rw [Frobenius.inner_def]; simp [E12, Fin.sum_univ_three]

private theorem norm_E12 : ‖E12‖ = 1 := by
  have h : ‖E12‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]; simp [E12, Fin.sum_univ_three]
  rw [← Real.sqrt_sq (norm_nonneg E12), h, Real.sqrt_one]

/-- **Prop. 4.4, conditional on Lemma 4.2** (arXiv 2608.12893). If two matrices `Ψ_±` (in the
paper the four-step Strang results `Ψ^{[4]}_{h_j,±}(Y⁰_j)` of (3.12)) satisfy the conclusion of
Lemma 4.2 with an explicit constant, `‖Ψ₊ - Ψ₋ - h_j² (8 H + (√2/16) E₁₂)‖ ≤ C h_j³`, then the
four-step local errors `τ_{0,±} = Ψ_± - Φ_±(4 h_j)` of (3.15) satisfy
`‖τ_{0,+} - τ_{0,-} - (√2/16) h_j² E₁₂‖ ≤ (C + 10⁵) h_j³`, for `j ≥ 3`. This is the paper's
proof of Prop. 4.4 ((4.5) and (4.23) in (4.1)), with Lemma 4.3 proved (`lemma_4_3`).
Conditional: Lemma 4.2 is a hypothesis; it is not proved in this module. -/
theorem prop_4_4_of_lemma_4_2 {j : ℕ} (hj3 : 3 ≤ j) {Ψp Ψm : M₃} {C : ℝ}
    (h42 : ‖Ψp - Ψm - hj j ^ 2 • ((8 : ℝ) • Hm + (√2 / 16) • E12)‖ ≤ C * hj j ^ 3)
    {Ap Am : ℝ → M₃}
    (hp : ODESolution (Fj j 1) Ap 0 (4 * hj j)) (hp0 : Ap 0 = Y0 j)
    (hm : ODESolution (Fj j (-1)) Am 0 (4 * hj j)) (hm0 : Am 0 = Y0 j) :
    ‖(Ψp - Ap (4 * hj j)) - (Ψm - Am (4 * hj j)) - ((√2 / 16) * hj j ^ 2) • E12‖ ≤
      (C + 100000) * hj j ^ 3 := by
  have h43 := lemma_4_3 hj3 hp hp0 hm hm0
  have e : (Ψp - Ap (4 * hj j)) - (Ψm - Am (4 * hj j)) - ((√2 / 16) * hj j ^ 2) • E12 =
      (Ψp - Ψm - hj j ^ 2 • ((8 : ℝ) • Hm + (√2 / 16) • E12)) -
        (Ap (4 * hj j) - Am (4 * hj j) - (8 * hj j ^ 2) • Hm) := by
    module
  rw [e]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ C * hj j ^ 3 + 100000 * hj j ^ 3 := add_le_add h42 h43
    _ = (C + 100000) * hj j ^ 3 := by ring

/-! ### Section 5: from the block errors to the global error -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The flow derivative is close to the identity** (arXiv 2608.12893, (5.27); a general fact).
Two solutions `y, z` of an `L`-Lipschitz field on `[a, b]` satisfy
`‖(y t - z t) - (y a - z a)‖ ≤ (exp (L (t - a)) - 1) ‖y a - z a‖`. -/
theorem norm_flow_sub_sub_le {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    {y z : ℝ → E} {a b : ℝ} (hy : ODESolution F y a b) (hz : ODESolution F z a b) :
    ∀ t ∈ Icc a b, ‖(y t - z t) - (y a - z a)‖ ≤ (Real.exp (L * (t - a)) - 1) * ‖y a - z a‖ := by
  set δ := ‖y a - z a‖
  have hstab := hy.norm_sub_le_exp hF hL hz
  have hf : ContinuousOn (fun t => (y t - z t) - (y a - z a)) (Icc a b) :=
    (hy.cont.sub hz.cont).sub continuousOn_const
  have hf' : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => (y t - z t) - (y a - z a))
      (F t (y t) - F t (z t)) (Ici t) t := fun t ht =>
    ((hy.deriv t ht).sub (hz.deriv t ht)).sub_const _
  have hB : ∀ t, HasDerivAt (fun t => (Real.exp (L * (t - a)) - 1) * δ)
      (Real.exp (L * (t - a)) * L * δ) t := by
    intro t
    have h1 : HasDerivAt (fun t => L * (t - a)) L t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul L
    exact ((h1.exp).sub_const 1).mul_const δ
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary hf hf'
    (B := fun t => (Real.exp (L * (t - a)) - 1) * δ) (by simp) hB (fun t ht => ?_)
  have hti : t ∈ Icc a b := Ico_subset_Icc_self ht
  calc ‖F t (y t) - F t (z t)‖ ≤ L * ‖y t - z t‖ := hF t _ _
    _ ≤ L * (Real.exp (L * (t - a)) * δ) := mul_le_mul_of_nonneg_left (hstab t hti) hL
    _ = Real.exp (L * (t - a)) * L * δ := by ring

/-- **The global error is the sum of the transported local errors** (arXiv 2608.12893, (5.26)
and (5.27); a general fact). Let `F` be `L`-Lipschitz, `t₀ ≤ t₁ ≤ ⋯`, and for `k ≤ N` let `Φ k`
solve `y' = F(t, y)` on `[t_k, t_N]` with `Φ k (t_k) = Y k` (so `Φ 0` is the exact solution
through `Y 0`). With the local errors `τ_k = Y (k+1) - Φ k (t_{k+1})`,
`‖(Y N - Φ 0 (t_N)) - ∑_{k<N} τ_k‖ ≤ (exp (L (t_N - t₀)) - 1) ∑_{k<N} ‖τ_k‖`. -/
theorem norm_globalErr_sub_sum_le {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {N : ℕ} {t : ℕ → ℝ} (ht : Monotone t) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ k ≤ N, ODESolution F (Φ k) (t k) (t N)) (hΦ₀ : ∀ k ≤ N, Φ k (t k) = Y k) :
    ‖(Y N - Φ 0 (t N)) - ∑ k ∈ range N, (Y (k + 1) - Φ k (t (k + 1)))‖ ≤
      (Real.exp (L * (t N - t 0)) - 1) * ∑ k ∈ range N, ‖Y (k + 1) - Φ k (t (k + 1))‖ := by
  have htel : Y N - Φ 0 (t N) = ∑ k ∈ range N, (Φ (k + 1) (t N) - Φ k (t N)) := by
    have := Finset.sum_range_sub (fun k => Φ k (t N)) N
    rw [this, hΦ₀ N le_rfl]
  rw [htel, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk : k < N := Finset.mem_range.1 hk
  have h1 : t (k + 1) ≤ t N := ht hk
  have hp := hΦ (k + 1) hk
  have hq := (hΦ k hk.le).mono (ht (Nat.le_succ k)) le_rfl
  have key := norm_flow_sub_sub_le hF hL hp hq (t N) ⟨h1, le_rfl⟩
  rw [hΦ₀ (k + 1) hk] at key
  have he : Real.exp (L * (t N - t (k + 1))) - 1 ≤ Real.exp (L * (t N - t 0)) - 1 := by
    have : L * (t N - t (k + 1)) ≤ L * (t N - t 0) :=
      mul_le_mul_of_nonneg_left (by linarith [ht (Nat.zero_le (k + 1))]) hL
    linarith [Real.exp_le_exp.2 this]
  exact key.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))

end Transport

/-- **Thm 3.1 from Prop. 5.1, one `j`** (arXiv 2608.12893, (5.26)–(5.32)), conditional on the
block-error bounds of Prop. 5.1, which are hypotheses here. For `η = ±1` let `Y_η k` be any
matrices (in the paper the block starts `Y^{4k}_{j,η}` of the Strang run) and, for `k ≤ j`,
let `Φ_η k` solve `A' = F_{j,η}(t, A)` on `[4 k h_j, 4 j h_j]` from `Y_η k`; so `Φ_η 0` is the
exact solution through `Y_η 0`. With the block errors `τ_{k,η} = Y_η (k+1) - Φ_η k (4(k+1)h_j)`
of (3.14): if `‖τ_{k,±}‖ ≤ C h_j²` ((5.3)) and `⟪τ_{k,+} - τ_{k,-}, E₁₂⟫ ≥ c h_j²` (a lower
bound in (5.4)) for all `k < j`, then the two global errors at `t = 4 j h_j` satisfy
`‖e_{j,+}‖ + ‖e_{j,-}‖ ≥ j h_j² (c - 2 C (e^{48 j h_j} - 1))`. The factor `e^{48 j h_j}` is the
paper's `e^{4 L_F j h_j}` with `L_F = 12` (`prop_3_2`). -/
theorem errSum_ge_of_blockErr {j : ℕ} (hj1 : 1 ≤ j) {Yp Ym : ℕ → M₃} {Φp Φm : ℕ → ℝ → M₃}
    (hΦp : ∀ k ≤ j, ODESolution (Fj j 1) (Φp k) (4 * k * hj j) (4 * j * hj j))
    (hΦp0 : ∀ k ≤ j, Φp k (4 * k * hj j) = Yp k)
    (hΦm : ∀ k ≤ j, ODESolution (Fj j (-1)) (Φm k) (4 * k * hj j) (4 * j * hj j))
    (hΦm0 : ∀ k ≤ j, Φm k (4 * k * hj j) = Ym k) {C c : ℝ}
    (h53p : ∀ k < j, ‖Yp (k + 1) - Φp k (4 * (k + 1 : ℕ) * hj j)‖ ≤ C * hj j ^ 2)
    (h53m : ∀ k < j, ‖Ym (k + 1) - Φm k (4 * (k + 1 : ℕ) * hj j)‖ ≤ C * hj j ^ 2)
    (h54 : ∀ k < j, c * hj j ^ 2 ≤ ⟪(Yp (k + 1) - Φp k (4 * (k + 1 : ℕ) * hj j)) -
      (Ym (k + 1) - Φm k (4 * (k + 1 : ℕ) * hj j)), E12⟫) :
    j * hj j ^ 2 * (c - 2 * C * (Real.exp (48 * (j * hj j)) - 1)) ≤
      ‖Yp j - Φp 0 (4 * j * hj j)‖ + ‖Ym j - Φm 0 (4 * j * hj j)‖ := by
  set h := hj j with hh
  have hh0 : 0 < h := hj_pos j
  set t : ℕ → ℝ := fun k => 4 * (k : ℝ) * h with ht
  have htm : Monotone t := fun a b hab => by
    simp only [ht]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hLp : IsLipschitzField (Fj j 1) 12 := (prop_3_2 hj1 (by norm_num)).2.1
  have hLm : IsLipschitzField (Fj j (-1)) 12 := (prop_3_2 hj1 (by norm_num)).2.1
  have Tp := norm_globalErr_sub_sum_le hLp (by norm_num) (N := j) htm (Y := Yp) (Φ := Φp)
    hΦp hΦp0
  have Tm := norm_globalErr_sub_sum_le hLm (by norm_num) (N := j) htm (Y := Ym) (Φ := Φm)
    hΦm hΦm0
  have hT : 12 * (t j - t 0) = 48 * (j * h) := by simp only [ht]; push_cast; ring
  rw [hT] at Tp Tm
  set ρ := Real.exp (48 * (j * h)) - 1 with hρdef
  have hρ : 0 ≤ ρ := by
    have h1 := Real.add_one_le_exp (48 * (j * h))
    have h2 : 0 ≤ 48 * ((j : ℝ) * h) := by positivity
    linarith
  set Sp := ∑ k ∈ range j, (Yp (k + 1) - Φp k (t (k + 1))) with hSp
  set Sm := ∑ k ∈ range j, (Ym (k + 1) - Φm k (t (k + 1))) with hSm
  have hsp : ∑ k ∈ range j, ‖Yp (k + 1) - Φp k (t (k + 1))‖ ≤ j * (C * h ^ 2) := by
    calc _ ≤ ∑ k ∈ range j, C * h ^ 2 := Finset.sum_le_sum fun k hk => h53p k (mem_range.1 hk)
      _ = j * (C * h ^ 2) := by simp
  have hsm : ∑ k ∈ range j, ‖Ym (k + 1) - Φm k (t (k + 1))‖ ≤ j * (C * h ^ 2) := by
    calc _ ≤ ∑ k ∈ range j, C * h ^ 2 := Finset.sum_le_sum fun k hk => h53m k (mem_range.1 hk)
      _ = j * (C * h ^ 2) := by simp
  have hsum : (j : ℝ) * (c * h ^ 2) ≤ ⟪Sp - Sm, E12⟫ := by
    rw [hSp, hSm, ← Finset.sum_sub_distrib, sum_inner]
    calc (j : ℝ) * (c * h ^ 2) = ∑ k ∈ range j, c * h ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => h54 k (mem_range.1 hk)
  set ep := Yp j - Φp 0 (t j) with hep
  set em := Ym j - Φm 0 (t j) with hem
  have hd : ⟪ep - em, E12⟫ = ⟪Sp - Sm, E12⟫ + ⟪(ep - Sp) - (em - Sm), E12⟫ := by
    rw [← inner_add_left]
    congr 1
    abel
  have hb : -‖(ep - Sp) - (em - Sm)‖ ≤ ⟪(ep - Sp) - (em - Sm), E12⟫ := by
    have := abs_real_inner_le_norm ((ep - Sp) - (em - Sm)) E12
    rw [norm_E12, mul_one] at this
    exact neg_le_of_abs_le this
  have hb2 : ‖(ep - Sp) - (em - Sm)‖ ≤ ρ * (j * (C * h ^ 2)) + ρ * (j * (C * h ^ 2)) := by
    calc ‖(ep - Sp) - (em - Sm)‖ ≤ ‖ep - Sp‖ + ‖em - Sm‖ := norm_sub_le _ _
      _ ≤ ρ * (j * (C * h ^ 2)) + ρ * (j * (C * h ^ 2)) :=
        add_le_add (Tp.trans (mul_le_mul_of_nonneg_left hsp hρ))
          (Tm.trans (mul_le_mul_of_nonneg_left hsm hρ))
  have hup : ⟪ep - em, E12⟫ ≤ ‖ep‖ + ‖em‖ := by
    calc ⟪ep - em, E12⟫ ≤ ‖ep - em‖ * ‖E12‖ := real_inner_le_norm _ _
      _ = ‖ep - em‖ := by rw [norm_E12, mul_one]
      _ ≤ ‖ep‖ + ‖em‖ := norm_sub_le _ _
  have hfin : (j : ℝ) * h ^ 2 * (c - 2 * C * ρ) ≤ ‖ep‖ + ‖em‖ := by linarith
  exact hfin

/-- `j h_j → 0`. -/
private theorem tendsto_j_mul_hj : Tendsto (fun j : ℕ => (j : ℝ) * hj j) atTop (𝓝 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)
  refine squeeze_zero (fun j => by unfold hj; positivity) (fun j => ?_) h1
  unfold hj
  have : (1 / 2 : ℝ) ^ (j ^ 2) ≤ (1 / 2) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_self_pow two_ne_zero j)
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg j)

/-- **Thm 3.1, the lower bound (3.20), conditional on Prop. 5.1** (arXiv 2608.12893, the proof of
Thm 3.1 in §5). For each `j` and `η = ±1` let `Y j η k` be any matrices (in the paper the block
starts `Y^{4k}_{j,η}` of the exact-subflow Strang run, which exist for large `j` by Prop. 5.2)
and `Φ j η k` the solution of `A' = F_{j,η}(t, A)` on `[4 k h_j, 4 j h_j]` through `Y j η k`
at `4 k h_j`; so `Φ j η 0 = A_{j,η}` when `Y j η 0 = Y⁰_j`. Assume Prop. 5.1 for all large `j`:
(5.3) `‖τ_{k,j,η}‖ ≤ C h_j²` and (5.4) `|⟪τ_{k,j,+} - τ_{k,j,-}, E₁₂⟫ - (√2/16) h_j²| ≤ ρ_j h_j²`
with `ρ_j → 0`, uniformly in `k < j`. Then (3.20) holds for all large `j`:
`max_η ‖Y^{4j}_{j,η} - A_{j,η}(4 j h_j)‖ ≥ (√2/64) j h_j²`.
Conditional: (5.3) and (5.4), which the paper proves from Prop. 4.4 and Appendix A, are
hypotheses; the deduction ((5.26)–(5.32)) is proved, with `L_F = 12` from `prop_3_2`. -/
theorem lower_bound_of_prop_5_1 (Y : ℕ → ℝ → ℕ → M₃) (Φ : ℕ → ℝ → ℕ → ℝ → M₃) {C : ℝ}
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (hΦ : ∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k ≤ j,
      ODESolution (Fj j η) (Φ j η k) (4 * k * hj j) (4 * j * hj j) ∧
        Φ j η k (4 * k * hj j) = Y j η k)
    (h53 : ∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k < j,
      ‖Y j η (k + 1) - Φ j η k (4 * (k + 1 : ℕ) * hj j)‖ ≤ C * hj j ^ 2)
    (h54 : ∀ᶠ j in atTop, ∀ k < j,
      |⟪(Y j 1 (k + 1) - Φ j 1 k (4 * (k + 1 : ℕ) * hj j)) -
        (Y j (-1) (k + 1) - Φ j (-1) k (4 * (k + 1 : ℕ) * hj j)), E12⟫ - √2 / 16 * hj j ^ 2| ≤
        ρ j * hj j ^ 2) :
    ∀ᶠ j in atTop, √2 / 64 * j * hj j ^ 2 ≤
      max ‖Y j 1 j - Φ j 1 0 (4 * j * hj j)‖ ‖Y j (-1) j - Φ j (-1) 0 (4 * j * hj j)‖ := by
  have hρev : ∀ᶠ j in atTop, ρ j < √2 / 64 :=
    hρ.eventually (gt_mem_nhds (by positivity))
  have hexp : Tendsto (fun j : ℕ => 2 * C * (Real.exp (48 * ((j : ℝ) * hj j)) - 1)) atTop
      (𝓝 (2 * C * (Real.exp (48 * 0) - 1))) :=
    ((((tendsto_j_mul_hj.const_mul 48).rexp).sub_const 1).const_mul (2 * C))
  rw [mul_zero, Real.exp_zero, sub_self, mul_zero] at hexp
  have hexpev : ∀ᶠ j : ℕ in atTop, 2 * C * (Real.exp (48 * ((j : ℝ) * hj j)) - 1) < √2 / 64 :=
    hexp.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hΦ, h53, h54, hρev, hexpev, eventually_ge_atTop 1] with
    j hΦj h53j h54j hρj hexj hj1
  have hp1 : (1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
  have hm1 : (-1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
  have key := errSum_ge_of_blockErr (c := √2 / 16 - ρ j) hj1
    (fun k hk => (hΦj 1 hp1 k hk).1) (fun k hk => (hΦj 1 hp1 k hk).2)
    (fun k hk => (hΦj (-1) hm1 k hk).1) (fun k hk => (hΦj (-1) hm1 k hk).2)
    (h53j 1 hp1) (h53j (-1) hm1) (fun k hk => by
      have := h54j k hk
      rw [abs_le] at this
      nlinarith [this.1])
  have hj0 : (0 : ℝ) ≤ j * hj j ^ 2 := by have := hj_pos j; positivity
  have hcoef : √2 / 32 ≤ √2 / 16 - ρ j - 2 * C * (Real.exp (48 * (j * hj j)) - 1) := by
    linarith
  have h2 : √2 / 32 * (j * hj j ^ 2) ≤ ‖Y j 1 j - Φ j 1 0 (4 * j * hj j)‖ +
      ‖Y j (-1) j - Φ j (-1) 0 (4 * j * hj j)‖ := by
    calc √2 / 32 * (j * hj j ^ 2) ≤ j * hj j ^ 2 *
        (√2 / 16 - ρ j - 2 * C * (Real.exp (48 * (j * hj j)) - 1)) := by
          have := mul_le_mul_of_nonneg_left hcoef hj0
          linarith
      _ ≤ _ := key
  have hmax := add_le_add (le_max_left ‖Y j 1 j - Φ j 1 0 (4 * j * hj j)‖
    ‖Y j (-1) j - Φ j (-1) 0 (4 * j * hj j)‖) (le_max_right ‖Y j 1 j - Φ j 1 0 (4 * j * hj j)‖
    ‖Y j (-1) j - Φ j (-1) 0 (4 * j * hj j)‖)
  linarith

/-- **Thm 3.1, failure of (2.11), conditional on Prop. 5.1** (arXiv 2608.12893, end of the proof
of Thm 3.1). Under the hypotheses of `lower_bound_of_prop_5_1`, for every constant `K`, for all
large `j` the error at `t = 4 j h_j` exceeds `K (δ_j + ε_j + h_j²)`, where
`δ_j = ‖Y j η 0 - Φ j η 0 0‖ = 0` (the exact solution starts at the initial iterate, as in the
paper) and `ε_j = β √2 (π/4) h_j²` is the normal-component bound of Prop. 3.2. So no `C`, `h₀`
independent of the retained singular values make (2.11) hold for the family. Conditional on (5.3)
and (5.4), as `lower_bound_of_prop_5_1`. -/
theorem not_robust_of_prop_5_1 (Y : ℕ → ℝ → ℕ → M₃) (Φ : ℕ → ℝ → ℕ → ℝ → M₃) {C : ℝ}
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (hΦ : ∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k ≤ j,
      ODESolution (Fj j η) (Φ j η k) (4 * k * hj j) (4 * j * hj j) ∧
        Φ j η k (4 * k * hj j) = Y j η k)
    (h53 : ∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k < j,
      ‖Y j η (k + 1) - Φ j η k (4 * (k + 1 : ℕ) * hj j)‖ ≤ C * hj j ^ 2)
    (h54 : ∀ᶠ j in atTop, ∀ k < j,
      |⟪(Y j 1 (k + 1) - Φ j 1 k (4 * (k + 1 : ℕ) * hj j)) -
        (Y j (-1) (k + 1) - Φ j (-1) k (4 * (k + 1 : ℕ) * hj j)), E12⟫ - √2 / 16 * hj j ^ 2| ≤
        ρ j * hj j ^ 2) (K : ℝ) :
    ∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ),
      ‖Y j η 0 - Φ j η 0 0‖ = 0 ∧
      K * (‖Y j η 0 - Φ j η 0 0‖ + εj j + hj j ^ 2) <
        max ‖Y j 1 j - Φ j 1 0 (4 * j * hj j)‖ ‖Y j (-1) j - Φ j (-1) 0 (4 * j * hj j)‖ := by
  have hs0 : 0 < √2 := by positivity
  set D := beta * √2 * (Real.pi / 4) + 1 with hD
  have hb0 : 0 < beta := by norm_num [beta]
  have hD0 : 0 < D := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (64 * K * D / √2)
  filter_upwards [lower_bound_of_prop_5_1 Y Φ hρ hΦ h53 h54, hΦ, eventually_gt_atTop n] with
    j hlow hΦj hjn η hη
  have h0 : Φ j η 0 0 = Y j η 0 := by simpa using (hΦj η hη 0 (Nat.zero_le j)).2
  refine ⟨by simp [h0], ?_⟩
  rw [h0, sub_self, norm_zero, zero_add]
  have he : εj j + hj j ^ 2 = D * hj j ^ 2 := by simp only [εj, hD]; ring
  rw [he]
  have hh := hj_pos j
  have hjn' : 64 * K * D / √2 < j := by
    have : (n : ℝ) < j := by exact_mod_cast hjn
    linarith
  have hK : K * D < √2 / 64 * j := by
    rw [div_lt_iff₀ hs0] at hjn'
    nlinarith
  have hh2 : 0 < hj j ^ 2 := by positivity
  calc K * (D * hj j ^ 2) = (K * D) * hj j ^ 2 := by ring
    _ < √2 / 64 * j * hj j ^ 2 := mul_lt_mul_of_pos_right hK hh2
    _ ≤ _ := hlow

/-- Block data with prescribed block errors exist: for `j ≥ 1`, `|η| ≤ 1` and any `c` there are
matrices `Y k` with `Y 0 = Y⁰_j` and solutions `Φ k` of `F_{j,η}` on `[4 k h_j, 4 j h_j]` through
`Y k` whose block errors `Y (k+1) - Φ k (4 (k+1) h_j)` all equal `c h_j² E₁₂`. (Used to show
that the hypotheses of `lower_bound_of_prop_5_1` are consistent; these are not Strang
iterates.) -/
theorem exists_blockData {j : ℕ} (hj1 : 1 ≤ j) {η : ℝ} (hη : |η| ≤ 1) (c : ℝ) :
    ∃ (Y : ℕ → M₃) (Φ : ℕ → ℝ → M₃), Y 0 = Y0 j ∧
      (∀ k ≤ j, ODESolution (Fj j η) (Φ k) (4 * k * hj j) (4 * j * hj j) ∧
        Φ k (4 * k * hj j) = Y k) ∧
      ∀ k < j, Y (k + 1) - Φ k (4 * (k + 1 : ℕ) * hj j) = (c * hj j ^ 2) • E12 := by
  obtain ⟨hB, hL, -⟩ := prop_3_2 hj1 hη
  have hc : ∀ X, Continuous fun t => Fj j η t X := fun X =>
    (continuous_const.add
      (continuous_iff_continuousAt.2 fun t => (hasDerivAt_Rj j t).continuousAt) :
      Continuous fun t => Mη η X + Rj j t)
  have hex : ∀ (k : ℕ) (x : M₃), ∃ A : ℝ → M₃,
      (k ≤ j → ODESolution (Fj j η) A (4 * k * hj j) (4 * j * hj j)) ∧ A (4 * k * hj j) = x := by
    intro k x
    by_cases hk : k ≤ j
    · have hkj : 4 * (k : ℝ) * hj j ≤ 4 * j * hj j := by
        have : (k : ℝ) ≤ j := by exact_mod_cast hk
        have := hj_pos j
        nlinarith
      obtain ⟨A, hA, hA0⟩ :=
        exists_ODESolution_of_continuousOn hL hB (fun X => (hc X).continuousOn) hkj x
      exact ⟨A, fun _ => hA, hA0⟩
    · exact ⟨fun _ => x, fun h => absurd h hk, rfl⟩
  choose sol hsol using hex
  let Y : ℕ → M₃ := fun k => Nat.rec (Y0 j)
    (fun k y => sol k y (4 * (k + 1 : ℕ) * hj j) + (c * hj j ^ 2) • E12) k
  refine ⟨Y, fun k => sol k (Y k), rfl,
    fun k hk => ⟨(hsol k (Y k)).1 hk, (hsol k (Y k)).2⟩, fun k _ => ?_⟩
  change sol k (Y k) (4 * (k + 1 : ℕ) * hj j) + (c * hj j ^ 2) • E12 -
    sol k (Y k) (4 * (k + 1 : ℕ) * hj j) = _
  abel

/-- The hypotheses of `lower_bound_of_prop_5_1` and `not_robust_of_prop_5_1` are consistent: data
with block errors `±(√2/32) h_j² E₁₂` (from `exists_blockData`, not the Strang iterates) satisfy
them with `C = √2/32` and `ρ = 0`. -/
theorem prop_5_1_hyps_satisfiable : ∃ (Y : ℕ → ℝ → ℕ → M₃) (Φ : ℕ → ℝ → ℕ → ℝ → M₃),
    (∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k ≤ j,
      ODESolution (Fj j η) (Φ j η k) (4 * k * hj j) (4 * j * hj j) ∧
        Φ j η k (4 * k * hj j) = Y j η k) ∧
    (∀ᶠ j in atTop, ∀ η ∈ ({1, -1} : Set ℝ), ∀ k < j,
      ‖Y j η (k + 1) - Φ j η k (4 * (k + 1 : ℕ) * hj j)‖ ≤ √2 / 32 * hj j ^ 2) ∧
    (∀ᶠ j in atTop, ∀ k < j,
      |⟪(Y j 1 (k + 1) - Φ j 1 k (4 * (k + 1 : ℕ) * hj j)) -
        (Y j (-1) (k + 1) - Φ j (-1) k (4 * (k + 1 : ℕ) * hj j)), E12⟫ - √2 / 16 * hj j ^ 2| ≤
        (fun _ : ℕ => (0 : ℝ)) j * hj j ^ 2) := by
  have hex : ∀ (j : ℕ) (η : ℝ), ∃ (Y : ℕ → M₃) (Φ : ℕ → ℝ → M₃), 1 ≤ j → |η| ≤ 1 →
      Y 0 = Y0 j ∧ (∀ k ≤ j, ODESolution (Fj j η) (Φ k) (4 * k * hj j) (4 * j * hj j) ∧
        Φ k (4 * k * hj j) = Y k) ∧
      ∀ k < j, Y (k + 1) - Φ k (4 * (k + 1 : ℕ) * hj j) = (η * (√2 / 32) * hj j ^ 2) • E12 := by
    intro j η
    by_cases h : 1 ≤ j ∧ |η| ≤ 1
    · obtain ⟨Y, Φ, h1⟩ := exists_blockData h.1 h.2 (η * (√2 / 32))
      exact ⟨Y, Φ, fun _ _ => h1⟩
    · exact ⟨fun _ => 0, fun _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Y Φ hYΦ using hex
  have hmem : ∀ η ∈ ({1, -1} : Set ℝ), |η| ≤ 1 := by
    intro η hη
    rcases hη with rfl | rfl <;> norm_num
  have hs : 0 ≤ √2 := Real.sqrt_nonneg 2
  refine ⟨Y, Φ, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with j hj1 η hη
    exact (hYΦ j η hj1 (hmem η hη)).2.1
  · filter_upwards [eventually_ge_atTop 1] with j hj1 η hη k hk
    rw [(hYΦ j η hj1 (hmem η hη)).2.2 k hk, norm_smul, norm_E12, mul_one, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ √2 / 32),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ hj j ^ 2)]
    have := hmem η hη
    have h2 : 0 ≤ √2 / 32 * hj j ^ 2 := by positivity
    nlinarith [abs_nonneg η]
  · filter_upwards [eventually_ge_atTop 1] with j hj1 k hk
    have h01 : E12 0 1 = 1 := rfl
    have key : ⟪(Y j 1 (k + 1) - Φ j 1 k (4 * (k + 1 : ℕ) * hj j)) -
        (Y j (-1) (k + 1) - Φ j (-1) k (4 * (k + 1 : ℕ) * hj j)), E12⟫ = √2 / 16 * hj j ^ 2 := by
      rw [(hYΦ j 1 hj1 (by norm_num)).2.2 k hk, (hYΦ j (-1) hj1 (by norm_num)).2.2 k hk,
        inner_E12]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h01]
      ring
    rw [key, sub_self, abs_zero]
    simp

/-! ### Lemma A.1: the subflows of `M_η` preserve rank two -/

/-- The entry `X i k`, as a continuous linear functional (the Frobenius inner product with the
matrix unit `E_{ik}`). -/
private noncomputable def entry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (i : m) (k : n) : Matrix m n ℝ →L[ℝ] ℝ :=
  innerSL ℝ (Matrix.single i k 1)

private theorem entry_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (i : m) (k : n) (X : Matrix m n ℝ) : entry i k X = X i k := by
  simp [entry, innerSL_apply_apply, Frobenius.inner_def, Matrix.single_apply, ite_and]

/-- Derivative of the determinant of a `2 × 2` matrix curve. -/
private theorem hasDerivWithinAt_det_two {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {G' : Matrix (Fin 2) (Fin 2) ℝ} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt G G' s t) :
    HasDerivWithinAt (fun t => (G t).det)
      (G' 0 0 * G t 1 1 + G t 0 0 * G' 1 1 - (G' 0 1 * G t 1 0 + G t 0 1 * G' 1 0)) s t := by
  have e : ∀ a b, HasDerivWithinAt (fun t => G t a b) (G' a b) s t := fun a b => by
    simpa [Function.comp_def, entry_apply] using (entry a b).hasFDerivAt.comp_hasDerivWithinAt t h
  simp only [Matrix.det_fin_two]
  exact ((e 0 0).mul (e 1 1)).sub ((e 0 1).mul (e 1 0))

/-- A `2 × 2` curve with `G' = A G - G B` and `tr A = tr B` has constant determinant (Jacobi's
formula gives `(det G)' = (tr A - tr B) det G`). -/
private theorem det_eq_of_deriv {G A B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a b : ℝ}
    (hc : ContinuousOn G (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt G (A t * G t - G t * B t) (Ici t) t)
    (htr : ∀ t ∈ Ico a b, (A t).trace = (B t).trace) :
    ∀ t ∈ Icc a b, (G t).det = (G a).det := by
  have ec : ∀ i k, ContinuousOn (fun t => G t i k) (Icc a b) := fun i k => by
    simpa [Function.comp_def, entry_apply] using (entry i k).continuous.comp_continuousOn hc
  have hfc : ContinuousOn (fun t => (G t).det) (Icc a b) := by
    simp only [Matrix.det_fin_two]
    exact ((ec 0 0).mul (ec 1 1)).sub ((ec 0 1).mul (ec 1 0))
  have hfd : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => (G t).det) 0 (Ici t) t := by
    intro t ht
    have h := hasDerivWithinAt_det_two (hd t ht)
    have htr' := htr t ht
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at htr'
    convert h using 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(G t 0 0 * G t 1 1 - G t 0 1 * G t 1 0)) * htr'
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hfc hfd (C := 0)
    (fun _ _ => by simp) t ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  exact this

private theorem Om_transpose : Omᵀ = -Om := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [Om]

private theorem skew_conj (V : Matrix (Fin 3) (Fin 2) ℝ) : (Vᵀ * Om * V)ᵀ = -(Vᵀ * Om * V) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Om_transpose]
  simp [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

private theorem trace_eq_zero_of_skew {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : Bᵀ = -B) :
    B.trace = 0 := by
  have h := congrArg Matrix.trace hB
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith

/-- If `K' = c (Ω K - K B)` with `Bᵀ = -B`, then the Gram determinant `det (Kᵀ K)` is constant;
so `K` keeps column rank two, or keeps rank below two. -/
private theorem gram_det_eq {K : ℝ → Matrix (Fin 3) (Fin 2) ℝ} {c : ℝ → ℝ}
    {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : Bᵀ = -B) {a b : ℝ} (hc : ContinuousOn K (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt K (c t • (Om * K t - K t * B)) (Ici t) t) :
    ∀ t ∈ Icc a b, ((K t)ᵀ * K t).det = ((K a)ᵀ * K a).det ∧
      ((K t).rank = 2 ↔ (K a).rank = 2) := by
  have hG : ∀ t ∈ Icc a b, ((K t)ᵀ * K t).det = ((K a)ᵀ * K a).det := by
    refine det_eq_of_deriv (A := fun t => c t • B) (B := fun t => c t • B) ?_ (fun t ht => ?_)
      (fun _ _ => rfl)
    · have h1 : ContinuousOn (fun t => (K t)ᵀ) (Icc a b) :=
        (Frobenius.transposeCLM (m := Fin 3) (n := Fin 2)).continuous.comp_continuousOn hc
      have h2 : ContinuousOn (fun t => Frobenius.mulCLM (K t)ᵀ) (Icc a b) :=
        (Frobenius.mulCLM (m := Fin 2) (l := Fin 3) (n := Fin 2)).continuous.comp_continuousOn h1
      exact h2.clm_apply hc
    · have h := Frobenius.hasDerivWithinAt_mul (Frobenius.hasDerivWithinAt_transpose (hd t ht))
        (hd t ht)
      convert h using 1
      rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
        Om_transpose, hB]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
      module
  intro t ht
  refine ⟨hG t ht, ?_⟩
  rw [← Matrix.rank_transpose_mul_self (K t), ← Matrix.rank_transpose_mul_self (K a),
    rank_eq_two_iff_det_ne_zero, rank_eq_two_iff_det_ne_zero, hG t ht]

private theorem kField_Mη (η : ℝ) {V : Matrix (Fin 3) (Fin 2) ℝ} (hV : Vᵀ * V = 1) (t : ℝ)
    (K : Matrix (Fin 3) (Fin 2) ℝ) : MatrixKSL.kField V (fun _ => Mη η) t K =
      qη η (K * Vᵀ) • (Om * K - K * (Vᵀ * Om * V)) := by
  simp only [MatrixKSL.kField, Mη, comm, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc, hV,
    Matrix.mul_one]

private theorem lField_Mη (η : ℝ) {U : Matrix (Fin 3) (Fin 2) ℝ} (hU : Uᵀ * U = 1) (t : ℝ)
    (L : Matrix (Fin 3) (Fin 2) ℝ) : MatrixKSL.lField U (fun _ => Mη η) t L =
      qη η (U * Lᵀ) • (Om * L - L * (Uᵀ * Om * U)) := by
  simp only [MatrixKSL.lField, Mη, comm, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_transpose, Om_transpose, Matrix.smul_mul,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  module

private theorem sField_Mη (η : ℝ) {U V : Matrix (Fin 3) (Fin 2) ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (t : ℝ) (S : Matrix (Fin 2) (Fin 2) ℝ) :
    MatrixKSL.sField U V (fun _ => Mη η) t S =
      ((-qη η (U * S * Vᵀ)) • (Uᵀ * Om * U)) * S - S * ((-qη η (U * S * Vᵀ)) • (Vᵀ * Om * V)) := by
  simp only [MatrixKSL.sField, Mη, comm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  simp only [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  module

/-- **Lemma A.1, K substep** (arXiv 2608.12893). When the right-hand side is `M_η`, the exact K
subproblem `K' = M_η(K Vᵀ) V` (`MatrixKSL.kField V`, with `V` column-orthonormal) keeps the Gram
determinant `det (Kᵀ K)` constant, so `K(t)` has rank two iff `K(t₀)` has. The paper states
that the column rank is preserved and proves `K(t) = e^{σΩ} K(t₀) e^{-σ Vᵀ Ω V}`; here only
rank two (full column rank, the case used for rank admissibility) is treated. -/
theorem lemma_A_1_K (η : ℝ) {V : Matrix (Fin 3) (Fin 2) ℝ} (hV : Vᵀ * V = 1)
    {K : ℝ → Matrix (Fin 3) (Fin 2) ℝ} {t₀ t₁ : ℝ}
    (hK : ODESolution (MatrixKSL.kField V (fun _ => Mη η)) K t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ((K t)ᵀ * K t).det = ((K t₀)ᵀ * K t₀).det ∧
      ((K t).rank = 2 ↔ (K t₀).rank = 2) :=
  gram_det_eq (c := fun t => qη η (K t * Vᵀ)) (skew_conj V) hK.cont fun t ht => by
    have := hK.deriv t ht
    rwa [kField_Mη η hV] at this

/-- **Lemma A.1, L substep** (arXiv 2608.12893). When the right-hand side is `M_η`, the exact L
subproblem `L' = M_η(U Lᵀ)ᵀ U` (`MatrixKSL.lField U`, with `U` column-orthonormal) keeps
`det (Lᵀ L)` constant, so `L(t)` has rank two iff `L(t₀)` has (only rank two is treated, as in
`lemma_A_1_K`). -/
theorem lemma_A_1_L (η : ℝ) {U : Matrix (Fin 3) (Fin 2) ℝ} (hU : Uᵀ * U = 1)
    {L : ℝ → Matrix (Fin 3) (Fin 2) ℝ} {t₀ t₁ : ℝ}
    (hL : ODESolution (MatrixKSL.lField U (fun _ => Mη η)) L t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ((L t)ᵀ * L t).det = ((L t₀)ᵀ * L t₀).det ∧
      ((L t).rank = 2 ↔ (L t₀).rank = 2) :=
  gram_det_eq (c := fun t => qη η (U * (L t)ᵀ)) (skew_conj U) hL.cont fun t ht => by
    have := hL.deriv t ht
    rwa [lField_Mη η hU] at this

/-- **Lemma A.1, S substep** (arXiv 2608.12893). When the right-hand side is `M_η`, the exact S
subproblem `S' = -Uᵀ M_η(U S Vᵀ) V` (`MatrixKSL.sField U V`, with `U, V` column-orthonormal)
keeps `det S` constant, so it preserves nonsingularity. -/
theorem lemma_A_1_S (η : ℝ) {U V : Matrix (Fin 3) (Fin 2) ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {S : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {t₀ t₁ : ℝ}
    (hS : ODESolution (MatrixKSL.sField U V (fun _ => Mη η)) S t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, (S t).det = (S t₀).det := by
  refine det_eq_of_deriv (A := fun t => (-qη η (U * S t * Vᵀ)) • (Uᵀ * Om * U))
    (B := fun t => (-qη η (U * S t * Vᵀ)) • (Vᵀ * Om * V)) hS.cont
    (fun t ht => by have := hS.deriv t ht; rwa [sField_Mη η hU hV] at this) (fun t _ => ?_)
  simp only [Matrix.trace_smul, trace_eq_zero_of_skew (skew_conj U),
    trace_eq_zero_of_skew (skew_conj V), smul_zero]


/-! ### Prop. 5.2 after the switch-off -/

/-- `R_j(t) = 0` once the phase has stopped, `t ≥ 4 (j+1) h_j` (arXiv 2608.12893,
(3.8)–(3.10)). -/
theorem Rj_eq_zero {j : ℕ} {t : ℝ} (ht : 4 * (j + 1) * hj j ≤ t) : Rj j t = 0 := by
  have hh := hj_pos j
  have hd : dth j t = 0 := by
    unfold dth
    split_ifs with h1 h2
    · linarith
    · have he : t = 4 * (j + 1) * hj j := le_antisymm h2 ht
      have hx : (t - 4 * j * hj j) / (4 * hj j) = 1 := by
        rw [he, div_eq_one_iff_eq (by positivity)]
        ring
      rw [hx]
      norm_num [dpsi]
    · rfl
  simp [Rj, hd]

/-- After the switch-off `F_{j,η}(t, ·) = M_η`. -/
theorem Fj_eq_of_ge {j : ℕ} {η t : ℝ} (ht : 4 * (j + 1) * hj j ≤ t) : Fj j η t = Mη η := by
  funext X
  simp [Fj, Rj_eq_zero ht]

/-- **Prop. 5.2 after the switch-off, K and L substeps** (arXiv 2608.12893, last step of the proof
of Prop. 5.2): on `[t₀, t₁]` with `t₀ ≥ 4 (j+1) h_j`, an exact K subproblem
`K' = F_{j,η}(t, K Vᵀ) V` and an exact L subproblem `L' = F_{j,η}(t, U Lᵀ)ᵀ U` (`V`, `U`
column-orthonormal) have rank two at `t` iff they have it at `t₀`, by Lemma A.1 (`lemma_A_1_K`,
`lemma_A_1_L`), since `R_j = 0` there. The first `j + 1` blocks of Prop. 5.2 are not treated. -/
theorem prop_5_2_after_switchoff_KL {j : ℕ} {η : ℝ} {U V : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {K L : ℝ → Matrix (Fin 3) (Fin 2) ℝ} {t₀ t₁ : ℝ}
    (ht₀ : 4 * (j + 1) * hj j ≤ t₀)
    (hK : ODESolution (MatrixKSL.kField V (Fj j η)) K t₀ t₁)
    (hL : ODESolution (MatrixKSL.lField U (Fj j η)) L t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ((K t).rank = 2 ↔ (K t₀).rank = 2) ∧ ((L t).rank = 2 ↔ (L t₀).rank = 2) := by
  have hK' : ODESolution (MatrixKSL.kField V (fun _ => Mη η)) K t₀ t₁ :=
    ⟨hK.cont, fun t ht => by
      have := hK.deriv t ht
      rwa [show MatrixKSL.kField V (Fj j η) t (K t) =
        MatrixKSL.kField V (fun _ => Mη η) t (K t) by
          simp only [MatrixKSL.kField, Fj_eq_of_ge (ht₀.trans ht.1)]] at this⟩
  have hL' : ODESolution (MatrixKSL.lField U (fun _ => Mη η)) L t₀ t₁ :=
    ⟨hL.cont, fun t ht => by
      have := hL.deriv t ht
      rwa [show MatrixKSL.lField U (Fj j η) t (L t) =
        MatrixKSL.lField U (fun _ => Mη η) t (L t) by
          simp only [MatrixKSL.lField, Fj_eq_of_ge (ht₀.trans ht.1)]] at this⟩
  exact fun t ht => ⟨(lemma_A_1_K η hV hK' t ht).2, (lemma_A_1_L η hU hL' t ht).2⟩

/-- **Prop. 5.2 after the switch-off, S substeps** (arXiv 2608.12893, last step of the proof of
Prop. 5.2): on `[t₀, t₁]` with `t₀ ≥ 4 (j+1) h_j`, an exact S subproblem
`S' = -Uᵀ F_{j,η}(t, U S Vᵀ) V` keeps `det S` constant, by Lemma A.1 (`lemma_A_1_S`). -/
theorem prop_5_2_after_switchoff_S {j : ℕ} {η : ℝ} {U V : Matrix (Fin 3) (Fin 2) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {S : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {t₀ t₁ : ℝ}
    (ht₀ : 4 * (j + 1) * hj j ≤ t₀) (hS : ODESolution (MatrixKSL.sField U V (Fj j η)) S t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, (S t).det = (S t₀).det := by
  have hS' : ODESolution (MatrixKSL.sField U V (fun _ => Mη η)) S t₀ t₁ :=
    ⟨hS.cont, fun t ht => by
      have := hS.deriv t ht
      rwa [show MatrixKSL.sField U V (Fj j η) t (S t) =
        MatrixKSL.sField U V (fun _ => Mη η) t (S t) by
          simp only [MatrixKSL.sField, Fj_eq_of_ge (ht₀.trans ht.1)]] at this⟩
  exact lemma_A_1_S η hU hV hS'

/-! ### Appendix A.2: the leading factor cycle -/

/-- `B(θ) = [e₁, ν(θ)]` (arXiv 2608.12893, (A.1)). -/
noncomputable def Bm (θ : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, Real.cos (Real.pi * θ / 4); 0, Real.sin (Real.pi * θ / 4)]

/-- `Σ_h(ζ) = diag(1, h³ ζ)` (arXiv 2608.12893, (A.1)). -/
noncomputable def Sig (h ζ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, h ^ 3 * ζ]

/-- The forcing of one periodic block, `R_h(t) = h² W'(t/h)` (arXiv 2608.12893, Appendix A; it is
`R_j` on `[0, 4 j h_j]` for `h = h_j`, (3.10)). -/
noncomputable def Rh (h t : ℝ) : M₃ := h ^ 2 • Wd (t / h)

/-- `B(θ)` has orthonormal columns (arXiv 2608.12893, after (A.1)). -/
theorem Bm_orth (θ : ℝ) : (Bm θ)ᵀ * Bm θ = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Bm, Matrix.mul_apply, Fin.sum_univ_three, ← sq, Real.cos_sq_add_sin_sq]

/-- `B(θ) B(θ)ᵀ = E₁₁ + W(θ)`. -/
theorem Bm_mul_transpose (θ : ℝ) : Bm θ * (Bm θ)ᵀ = E11 + W θ := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Bm, E11, W, nu, Matrix.mul_apply, Fin.sum_univ_two]

/-- `ν(a)ᵀ ν(b) = cos(π (a - b)/4)` (arXiv 2608.12893, (A.2)). -/
theorem nu_dot (a b : ℝ) : nu a ⬝ᵥ nu b = Real.cos (Real.pi * (a - b) / 4) := by
  rw [show Real.pi * (a - b) / 4 = Real.pi * a / 4 - Real.pi * b / 4 by ring, Real.cos_sub]
  simp [nu, dotProduct, Fin.sum_univ_three]

/-- `W(a) W(b) = cos(π (a - b)/4) ν(a) ν(b)ᵀ`, equivalently `W(a) ν(b) = cos(π (a - b)/4) ν(a)`
(arXiv 2608.12893, (A.2)). -/
theorem W_mul_W (a b : ℝ) :
    W a * W b = Real.cos (Real.pi * (a - b) / 4) • Matrix.vecMulVec (nu a) (nu b) := by
  rw [← nu_dot]
  ext i k
  simp only [W, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    smul_eq_mul, Fin.sum_univ_three]
  ring

/-- `W(θ + 4) = W(θ)` (arXiv 2608.12893, after (3.5)). -/
theorem W_add_four (θ : ℝ) : W (θ + 4) = W θ := by
  have hc : Real.cos (Real.pi * (θ + 4) / 4) = -Real.cos (Real.pi * θ / 4) := by
    rw [show Real.pi * (θ + 4) / 4 = Real.pi * θ / 4 + Real.pi by ring, Real.cos_add_pi]
  have hs : Real.sin (Real.pi * (θ + 4) / 4) = -Real.sin (Real.pi * θ / 4) := by
    rw [show Real.pi * (θ + 4) / 4 = Real.pi * θ / 4 + Real.pi by ring, Real.sin_add_pi]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [W, nu, Matrix.vecMulVec_apply, hc, hs]

private theorem W_mul_self (a : ℝ) : W a * W a = W a := by
  rw [W_mul_W, sub_self, mul_zero, zero_div, Real.cos_zero, one_smul]
  rfl

private theorem E11_mul_W (a : ℝ) : E11 * W a = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [E11, W, nu, Matrix.mul_apply, Fin.sum_univ_three]

private theorem W_mul_E11 (a : ℝ) : W a * E11 = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [E11, W, nu, Matrix.mul_apply, Fin.sum_univ_three]

private theorem E11_mul_E11 : E11 * E11 = E11 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [E11, Matrix.mul_apply, Fin.sum_univ_three]

private theorem W_mul_W_mul (a : ℝ) (X : M₃) : W a * (W a * X) = W a * X := by
  rw [← Matrix.mul_assoc, W_mul_self]

private theorem E11_mul_W_mul (a : ℝ) (X : M₃) : E11 * (W a * X) = 0 := by
  rw [← Matrix.mul_assoc, E11_mul_W, Matrix.zero_mul]

private theorem W_mul_E11_mul (a : ℝ) (X : M₃) : W a * (E11 * X) = 0 := by
  rw [← Matrix.mul_assoc, W_mul_E11, Matrix.zero_mul]

private theorem E11_mul_E11_mul (X : M₃) : E11 * (E11 * X) = E11 * X := by
  rw [← Matrix.mul_assoc, E11_mul_E11]

private theorem rightProj_Bm (θ : ℝ) (X : M₃) : rightProj (Bm θ) X = X * (E11 + W θ) := by
  rw [rightProj_apply', Bm_mul_transpose]

private theorem leftProj_Bm (θ : ℝ) (X : M₃) : leftProj (Bm θ) X = (E11 + W θ) * X := by
  rw [leftProj_apply, Bm_mul_transpose]

/-- `B(a) Σ_h(cos(π(a - b)/4)) B(b)ᵀ = E₁₁ + h³ W(a) W(b)`. -/
theorem Bm_Sig_eq (a b h : ℝ) :
    Bm a * Sig h (Real.cos (Real.pi * (a - b) / 4)) * (Bm b)ᵀ = E11 + h ^ 3 • (W a * W b) := by
  rw [W_mul_W, smul_smul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Bm, Sig, E11, nu, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal] <;> ring

/-- `h³ W(t/h)` has derivative `R_h(t)`. -/
theorem hasDerivAt_hW_div {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => h ^ 3 • W (t / h)) (Rh h t) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / h) (1 / h) t := by
    simpa using (hasDerivAt_id t).div_const h
  have e : h ^ 3 • (1 / h) • Wd (t / h) = Rh h t := by
    simp only [Rh, smul_smul]
    congr 1
    field_simp
  exact (((hasDerivAt_W (t / h)).scomp t h1).const_smul (h ^ 3)).congr_deriv e

/-- A field `g(t)` that does not depend on the state has the solutions `c + G(t)`, `G' = g`. -/
private theorem odeSolution_add_antideriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g G : ℝ → E} (hG : ∀ t, HasDerivAt G (g t) t) (c : E) (a b : ℝ) :
    ODESolution (fun t _ => g t) (fun t => c + G t) a b :=
  ⟨(continuous_const.add (continuous_iff_continuousAt.2 fun t => (hG t).continuousAt)).continuousOn,
    fun t _ => ((hG t).const_add c).hasDerivWithinAt⟩

/-- Every solution of a state-independent field `g(t)` is `y(a) - G(a) + G(t)`, `G' = g`. -/
private theorem odeSolution_eq_add_antideriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g G : ℝ → E} (hG : ∀ t, HasDerivAt G (g t) t) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun t _ => g t) y a b) : ∀ t ∈ Icc a b, y t = (y a - G a) + G t := by
  have := hy.eqOn (odeSolution_add_antideriv hG (y a - G a) a b) (L := 0)
    (fun _ _ _ => by simp) le_rfl (by simp)
  exact fun t ht => this ht

section Cycle

variable {ℓ h : ℝ}

private theorem hasDerivAt_R {h : ℝ} (hh : h ≠ 0) (P : M₃ →L[ℝ] M₃) (t : ℝ) :
    HasDerivAt (fun t => P (h ^ 3 • W (t / h))) (P (Rh h t)) t :=
  P.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_hW_div hh t)

private theorem hasDerivAt_negR {h : ℝ} (hh : h ≠ 0) (P Q : M₃ →L[ℝ] M₃) (t : ℝ) :
    HasDerivAt (fun t => -P (Q (h ^ 3 • W (t / h)))) (-P (Q (Rh h t))) t :=
  ((P.comp Q).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_hW_div hh t)).neg

/-- The substep endpoints of the leading cycle, in terms of `W`. -/
private theorem cycle_values (hh : 0 < h) {YK₁ YS₁ YL YS₂ YK₂ : ℝ → M₃}
    (k₁Sol : ODESolution (fun t _ => rightProj (Bm ℓ) (Rh h t)) YK₁ (ℓ * h) (ℓ * h + h / 2))
    (k₁Start : YK₁ (ℓ * h) = E11 + h ^ 3 • W ℓ)
    (s₁Sol : ODESolution (fun t _ => -leftProj (Bm (ℓ + 1 / 2)) (rightProj (Bm ℓ) (Rh h t)))
      YS₁ (ℓ * h) (ℓ * h + h / 2))
    (s₁Start : YS₁ (ℓ * h) = YK₁ (ℓ * h + h / 2))
    (lSol : ODESolution (fun t _ => leftProj (Bm (ℓ + 1 / 2)) (Rh h t)) YL (ℓ * h) (ℓ * h + h))
    (lStart : YL (ℓ * h) = YS₁ (ℓ * h + h / 2))
    (s₂Sol : ODESolution
      (fun t _ => -leftProj (Bm (ℓ + 1 / 2)) (rightProj (Bm (ℓ + 1)) (Rh h t)))
      YS₂ (ℓ * h + h / 2) (ℓ * h + h))
    (s₂Start : YS₂ (ℓ * h + h / 2) = YL (ℓ * h + h))
    (k₂Sol : ODESolution (fun t _ => rightProj (Bm (ℓ + 1)) (Rh h t)) YK₂ (ℓ * h + h / 2)
      (ℓ * h + h))
    (k₂Start : YK₂ (ℓ * h + h / 2) = YS₂ (ℓ * h + h)) :
    YK₁ (ℓ * h + h / 2) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W ℓ) ∧
    YS₁ (ℓ * h + h / 2) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W ℓ) ∧
    YL (ℓ * h + h) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W (ℓ + 1)) ∧
    YS₂ (ℓ * h + h) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W (ℓ + 1)) ∧
    YK₂ (ℓ * h + h) = E11 + h ^ 3 • W (ℓ + 1) := by
  have hh0 : h ≠ 0 := hh.ne'
  have d0 : ℓ * h / h = ℓ := by field_simp
  have d1 : (ℓ * h + h / 2) / h = ℓ + 1 / 2 := by field_simp
  have d2 : (ℓ * h + h) / h = ℓ + 1 := by field_simp
  have k1 := odeSolution_eq_add_antideriv (hasDerivAt_R hh0 (rightProj (Bm ℓ))) k₁Sol
    (ℓ * h + h / 2) ⟨by linarith, le_rfl⟩
  have s1 := odeSolution_eq_add_antideriv
    (hasDerivAt_negR hh0 (leftProj (Bm (ℓ + 1 / 2))) (rightProj (Bm ℓ))) s₁Sol
    (ℓ * h + h / 2) ⟨by linarith, le_rfl⟩
  have l1 := odeSolution_eq_add_antideriv (hasDerivAt_R hh0 (leftProj (Bm (ℓ + 1 / 2)))) lSol
    (ℓ * h + h) ⟨by linarith, le_rfl⟩
  have s2 := odeSolution_eq_add_antideriv
    (hasDerivAt_negR hh0 (leftProj (Bm (ℓ + 1 / 2))) (rightProj (Bm (ℓ + 1)))) s₂Sol
    (ℓ * h + h) ⟨by linarith, le_rfl⟩
  have k2 := odeSolution_eq_add_antideriv (hasDerivAt_R hh0 (rightProj (Bm (ℓ + 1)))) k₂Sol
    (ℓ * h + h) ⟨by linarith, le_rfl⟩
  simp only [d0, d1, d2] at k1 s1 l1 s2 k2
  rw [k₁Start] at k1
  rw [s₁Start] at s1
  rw [lStart] at l1
  rw [s₂Start] at s2
  rw [k₂Start] at k2
  simp only [rightProj_Bm, leftProj_Bm, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, E11_mul_W, W_mul_E11, W_mul_self, W_mul_W_mul, E11_mul_W_mul, smul_zero,
    zero_add] at k1 s1 l1 s2 k2
  have hK1 : YK₁ (ℓ * h + h / 2) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W ℓ) := by
    rw [k1]; module
  have hS1 : YS₁ (ℓ * h + h / 2) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W ℓ) := by
    rw [s1, hK1]; module
  have hL : YL (ℓ * h + h) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W (ℓ + 1)) := by
    rw [l1, hS1]; module
  have hS2 : YS₂ (ℓ * h + h) = E11 + h ^ 3 • (W (ℓ + 1 / 2) * W (ℓ + 1)) := by
    rw [s2, hL]; module
  refine ⟨hK1, hS1, hL, hS2, ?_⟩
  rw [k2, hS2]
  module

private theorem Bm_Sig_one (a h : ℝ) : Bm a * Sig h 1 * (Bm a)ᵀ = E11 + h ^ 3 • W a := by
  have := Bm_Sig_eq a a h
  rwa [sub_self, mul_zero, zero_div, Real.cos_zero, W_mul_self] at this

private theorem Bm_Sig_half (ℓ h : ℝ) :
    Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm ℓ)ᵀ =
      E11 + h ^ 3 • (W (ℓ + 1 / 2) * W ℓ) := by
  rw [← Bm_Sig_eq]; congr 3; ring_nf

private theorem Bm_Sig_half' (ℓ h : ℝ) :
    Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm (ℓ + 1))ᵀ =
      E11 + h ^ 3 • (W (ℓ + 1 / 2) * W (ℓ + 1)) := by
  rw [← Bm_Sig_eq, ← Real.cos_neg]; congr 3; ring_nf

/-- **The leading factor cycle (A.26)** (arXiv 2608.12893, Appendix A.2). With `M_η` omitted,
i.e. for the forcing alone, `F(t, X) = R_h(t) = h² W'(t/h)`, every exact-subflow Strang step on
`[ℓ h, (ℓ+1) h]` (`IsStrangKSLStep`, table (2.7)) from `Y = B(ℓ) Σ_h(1) B(ℓ)ᵀ = E₁₁ + h³ W(ℓ)`
with the projectors `P₀ = B(ℓ)B(ℓ)ᵀ`, `Q = B(ℓ+½)B(ℓ+½)ᵀ`, `P₁ = B(ℓ+1)B(ℓ+1)ᵀ` passes through
`B(ℓ+½) Σ_h(γ) B(ℓ)ᵀ` (after K₁ and S₁) and `B(ℓ+½) Σ_h(γ) B(ℓ+1)ᵀ` (after L and S₂), and ends at
`B(ℓ+1) Σ_h(1) B(ℓ+1)ᵀ = E₁₁ + h³ W(ℓ+1)`, with `γ = cos(π/8)`. The step is exact for this
problem, whose solution is `E₁₁ + h³ W(t/h)`. The projectors are taken as given; that they are
the ones the QR steps of (2.9) produce (the column space of `B(ℓ+½) Σ_h(γ) B(ℓ)ᵀ` is the range of
`B(ℓ+½)` because `γ h³ ≠ 0`, and similarly for `L`) is the paper's remark and is not formalized.
The paper writes the cycle in factor form `(U, S, V)`; here the matrices `U S Vᵀ`, for any real
`ℓ`. The hypotheses can be met: `exists_leading_step`. -/
theorem leading_cycle (hh : 0 < h) {ε : ℝ} {YK₁ YS₁ YL YS₂ YK₂ : ℝ → M₃}
    (hs : IsStrangKSLStep (fun t _ => Rh h t) ε (rightProj (Bm ℓ)) (leftProj (Bm (ℓ + 1 / 2)))
      (rightProj (Bm (ℓ + 1))) (ℓ * h) h (Bm ℓ * Sig h 1 * (Bm ℓ)ᵀ) YK₁ YS₁ YL YS₂ YK₂) :
    YK₁ (ℓ * h + h / 2) = Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm ℓ)ᵀ ∧
    YS₁ (ℓ * h + h / 2) = Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm ℓ)ᵀ ∧
    YL (ℓ * h + h) = Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm (ℓ + 1))ᵀ ∧
    YS₂ (ℓ * h + h) = Bm (ℓ + 1 / 2) * Sig h (Real.cos (Real.pi / 8)) * (Bm (ℓ + 1))ᵀ ∧
    YK₂ (ℓ * h + h) = Bm (ℓ + 1) * Sig h 1 * (Bm (ℓ + 1))ᵀ ∧
    Bm (ℓ + 1) * Sig h 1 * (Bm (ℓ + 1))ᵀ = E11 + h ^ 3 • W (ℓ + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cycle_values hh hs.k₁Sol (hs.k₁Start.trans (Bm_Sig_one ℓ h))
    hs.s₁Sol hs.s₁Start hs.lSol hs.lStart hs.s₂Sol hs.s₂Start hs.k₂Sol hs.k₂Start
  exact ⟨h1.trans (Bm_Sig_half ℓ h).symm, h2.trans (Bm_Sig_half ℓ h).symm,
    h3.trans (Bm_Sig_half' ℓ h).symm, h4.trans (Bm_Sig_half' ℓ h).symm,
    h5.trans (Bm_Sig_one _ h).symm, Bm_Sig_one _ h⟩

/-- The hypotheses of `leading_cycle` can be met: the five substeps exist in closed form, the
projectors capture the K₁ and L results, and the normal components are bounded by
`ε = h² √2 (π/4) = ‖R_h‖`. -/
theorem exists_leading_step (hh : 0 < h) :
    ∃ YK₁ YS₁ YL YS₂ YK₂ : ℝ → M₃, IsStrangKSLStep (fun t _ => Rh h t)
      (h ^ 2 * (√2 * (Real.pi / 4))) (rightProj (Bm ℓ)) (leftProj (Bm (ℓ + 1 / 2)))
      (rightProj (Bm (ℓ + 1))) (ℓ * h) h (Bm ℓ * Sig h 1 * (Bm ℓ)ᵀ) YK₁ YS₁ YL YS₂ YK₂ := by
  have hh0 : h ≠ 0 := hh.ne'
  set P₀ : M₃ →L[ℝ] M₃ := rightProj (Bm ℓ) with hP₀def
  set Q : M₃ →L[ℝ] M₃ := leftProj (Bm (ℓ + 1 / 2)) with hQdef
  set P₁ : M₃ →L[ℝ] M₃ := rightProj (Bm (ℓ + 1)) with hP₁def
  set G₁ : ℝ → M₃ := fun t => P₀ (h ^ 3 • W (t / h))
  set G₂ : ℝ → M₃ := fun t => -Q (P₀ (h ^ 3 • W (t / h)))
  set G₃ : ℝ → M₃ := fun t => Q (h ^ 3 • W (t / h))
  set G₄ : ℝ → M₃ := fun t => -Q (P₁ (h ^ 3 • W (t / h)))
  set G₅ : ℝ → M₃ := fun t => P₁ (h ^ 3 • W (t / h))
  set t₀ := ℓ * h with ht₀
  set YK₁ : ℝ → M₃ := fun t => (E11 + h ^ 3 • W ℓ - G₁ t₀) + G₁ t
  set YS₁ : ℝ → M₃ := fun t => (YK₁ (t₀ + h / 2) - G₂ t₀) + G₂ t
  set YL : ℝ → M₃ := fun t => (YS₁ (t₀ + h / 2) - G₃ t₀) + G₃ t
  set YS₂ : ℝ → M₃ := fun t => (YL (t₀ + h) - G₄ (t₀ + h / 2)) + G₄ t
  set YK₂ : ℝ → M₃ := fun t => (YS₂ (t₀ + h) - G₅ (t₀ + h / 2)) + G₅ t
  have sK₁ : ODESolution (fun t _ => P₀ (Rh h t)) YK₁ t₀ (t₀ + h / 2) :=
    odeSolution_add_antideriv (hasDerivAt_R hh0 P₀) _ _ _
  have sS₁ : ODESolution (fun t _ => -Q (P₀ (Rh h t))) YS₁ t₀ (t₀ + h / 2) :=
    odeSolution_add_antideriv (hasDerivAt_negR hh0 Q P₀) _ _ _
  have sL : ODESolution (fun t _ => Q (Rh h t)) YL t₀ (t₀ + h) :=
    odeSolution_add_antideriv (hasDerivAt_R hh0 Q) _ _ _
  have sS₂ : ODESolution (fun t _ => -Q (P₁ (Rh h t))) YS₂ (t₀ + h / 2) (t₀ + h) :=
    odeSolution_add_antideriv (hasDerivAt_negR hh0 Q P₁) _ _ _
  have sK₂ : ODESolution (fun t _ => P₁ (Rh h t)) YK₂ (t₀ + h / 2) (t₀ + h) :=
    odeSolution_add_antideriv (hasDerivAt_R hh0 P₁) _ _ _
  have e₁ : YK₁ t₀ = E11 + h ^ 3 • W ℓ := by simp only [YK₁]; abel
  have e₂ : YS₁ t₀ = YK₁ (t₀ + h / 2) := by simp only [YS₁]; abel
  have e₃ : YL t₀ = YS₁ (t₀ + h / 2) := by simp only [YL]; abel
  have e₄ : YS₂ (t₀ + h / 2) = YL (t₀ + h) := by simp only [YS₂]; abel
  have e₅ : YK₂ (t₀ + h / 2) = YS₂ (t₀ + h) := by simp only [YK₂]; abel
  obtain ⟨v₁, -, v₃, -, -⟩ := cycle_values hh sK₁ e₁ sS₁ e₂ sL e₃ sS₂ e₄ sK₂ e₅
  have hP₀ : IsOrthProj P₀ := isOrthProj_rightProj (Bm_orth ℓ)
  have hQ : IsOrthProj Q := isOrthProj_leftProj (Bm_orth (ℓ + 1 / 2))
  have hP₁ : IsOrthProj P₁ := isOrthProj_rightProj (Bm_orth (ℓ + 1))
  have hR : ∀ t, ‖Rh h t‖ ≤ h ^ 2 * (√2 * (Real.pi / 4)) := fun t => by
    rw [Rh, norm_smul, norm_Wd, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine ⟨YK₁, YS₁, YL, YS₂, YK₂,
    { projQ₀ := hP₀, projP₁ := hQ, projQ₁ := hP₁, comm := fun x => leftProj_rightProj_comm _ _ x,
      k₁Sol := sK₁, k₁Start := (e₁.trans (Bm_Sig_one ℓ h).symm), k₁Cap := ?_,
      k₁Normal := fun t _ => (hQ.compl.norm_le _).trans ((hP₀.compl.norm_le _).trans (hR t)),
      s₁Sol := sS₁, s₁Start := e₂, lSol := sL, lStart := e₃, lCap := ?_,
      lNormal := fun t _ => (hP₁.compl.norm_le _).trans ((hQ.compl.norm_le _).trans (hR t)),
      s₂Sol := sS₂, s₂Start := e₄, k₂Sol := sK₂, k₂Start := e₅ }⟩
  · rw [v₁, hQdef, leftProj_Bm]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, E11_mul_E11,
      W_mul_E11, E11_mul_W_mul, W_mul_W_mul, add_zero, zero_add]
  · rw [v₃, hP₁def, rightProj_Bm]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, E11_mul_E11,
      E11_mul_W, W_mul_E11, W_mul_self, Matrix.mul_zero, smul_zero, add_zero, zero_add]

end Cycle

end LeanDLRA.Literature.P2608_12893
