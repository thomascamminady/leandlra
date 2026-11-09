import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Algebra.Polynomial
import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector
import LeanDLRA.Integrators.KStep
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stiff.ImplicitBUG

/-!
# Results of arXiv 2412.09400: high-order implicit low-rank SDC (SDC-mBUG)

Li–Jiang–Cheng, *High-order implicit low-rank method with spectral deferred correction for matrix
differential equations*.  This module formalizes the error analysis of the paper on an abstract
real inner product space `E`, for a field `F` that is Lipschitz in both variables
(`IsLipschitzTX`, the standing assumption of §3.2) and bounded; matrices with the Frobenius inner
product and the Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` are an instance
(`IsMatrixMBUGStep.isMBUGStep`, `matrix_correction_sstep_eq`).  An mBUG step (`IsMBUGStep`) is an
implicit Galerkin Euler step on the range of an orthogonal projector that fixes the start and the
truncated `F(t₀, Y₀)`, followed by a truncation; a low-rank correction sweep
(`IsCorrectionSweep`) is Steps C-1 to C-3 of §3.1.  Results: **Theorem 3.2**
(`sdc_mbug_local_error`; at all nodes and levels, eq. (14), `sdc_mbug_node_error`; with the
quadrature error derived from smoothness, `sdc_mbug_local_error_smooth`):
`‖X_{n+1} - X(t_{n+1})‖ ≤ C_{K+1} (δ^{(K+1)} + h^{min(K+2, P+2)})` with explicit constants
`sdcC` and the recursion `sdcDelta` (closed form `sdcDelta_closed_form`); **Remark 3.1**
(`sdc_mbug_local_error_order`): `O(h^{K+2})` for `P = K` and the stated tolerances;
**Theorem 2.1** (`sdc_local_error`): classical SDC with the Lagrange weights `sdcWeight` has local
error `C h^{min(K+2, P+2)}`, the quadrature error being derived from Taylor's theorem and the
exactness of the weights (`quadDefect_le`, `quad_exact_pow`), and the weights do not depend on the
step (`sdcWeight_affine`); **Lemma 3.1** for the factor-level mBUG step
(`IsMatrixMBUGStep.local_error`; the abstract form is the library's
`LeanDLRA.mergeBUG_local_error`, and `mbug_step_error` is the perturbed-start version used for
Stage 1); and the **§2.1 truncation operators**: `rank_hardThreshold_le`,
`rank_softThreshold_le`, `sq_norm_sub_hardThreshold`, `sq_norm_sub_softThreshold`
(`‖X - H_α(X)‖_F² = Δ^h(α)`, `‖X - S_α(X)‖_F² = Δ^s(α)`), `norm_sub_hardThreshold_le`,
`norm_sub_softThreshold_le` (error `≤ ε` for every admissible threshold),
`softThreshold_argmax_exists` and `softThreshold_nonexpansive`
(`‖S_α(X₁) - S_α(X₂)‖_F ≤ ‖X₁ - X₂‖_F`).  **A defect of §2.1**: the threshold of `T^h_ε`, defined as
`argmax {β > 0 | Δ^h(β) ≤ ε²}`, need not exist, and with the supremum the bound
`‖X - T^h_ε(X)‖_F ≤ ε` fails (`hardThreshold_argmax_counterexample`, `X = diag(2, 1)`,
`ε = 1/2`).

Differences from the paper:

* the truncations (`T^{sum}`, SVD truncation) enter only through their error bounds, and the
  implicit K- and L-steps of mBUG, which only enlarge the bases, are not recorded;
* `δ^{(k)}` is the paper's recursion with all `O`-constants equal to one; the constants `C_k`
  are explicit and also depend on a bound `Λ ≥ ∑_s |w_{m,s}|` of the weights and on the
  quadrature constant `C_A`, which the paper hides in its `O`; `L > 0` as in the paper;
* `sdc_mbug_node_error`, `sdc_mbug_local_error` and `sdc_mbug_local_error_order` are
  **conditional** on the quadrature defect `‖X(t_{m+1}) - X(t_m) - I_m^{m+1} F(X)‖ ≤ C_A h^{P+2}`
  of the exact solution, the bound on the term (A) that the paper's proof asserts; it does not
  follow from the assumptions (12) alone.  `quadDefect_le` proves it with
  `C_A = (1 + Λ) M / P!` when `t ↦ F(t, X t)` is `C^{P+1}` with `(P+1)`-st derivative `≤ M`, and
  `sdc_mbug_local_error_smooth` is the unconditional form under that smoothness assumption (the
  paper assumes `F` "sufficiently smooth" in §2.3);
* the paper's proof of Theorem 3.2 uses `Û Ûᵀ F(X^{(k+1)}_{m+1}) V̂ V̂ᵀ = F(X^{(k+1)}_{m+1})`,
  which does not follow from its choice (10) of the bases (they contain the range of the
  truncated `F^{(k)}_{m+1}` only); the proof here does not need it;
* the product in the weight formula (5) is printed with upper limit `m`; the text ("the `P`-th
  degree interpolating polynomial on the `P + 1` points") fixes it as `P`, which is used here;
* Theorem 2.1 ("smooth `F` and solution") is stated with the Lipschitz and boundedness
  assumptions of §3.2 and the derivative bound `M`;
* §2.1: `H_α`, `S_α` are defined from a given factorization `X = U diag(σ) Vᵀ` with orthonormal
  columns (independence of the chosen SVD is not shown); `T^h_ε` is `H_α` for any admissible `α`;
  of the statement that soft thresholding is the proximal map of `α ‖·‖_*`, hence non-expansive,
  only the consequence (non-expansiveness) is proved, through the first-order optimality
  relation `X - S_α(X) = α G`, `‖G‖₂ ≤ 1`, and the duality inequality `inner_svdMat_le`; the
  minimization property itself is not stated, for lack of a nuclear-norm API.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2412_09400

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The standing assumption and the algorithm -/

/-- The standing assumption of arXiv 2412.09400, §3.2: `F` is Lipschitz in both variables with
the same constant, `‖F(s, Y) - F(t, Z)‖ ≤ L ‖Y - Z‖ + L |s - t|` (the paper writes `F(Y, s)`). -/
def IsLipschitzTX (F : ℝ → E → E) (L : ℝ) : Prop :=
  ∀ (s t : ℝ) (Y Z : E), ‖F s Y - F t Z‖ ≤ L * ‖Y - Z‖ + L * |s - t|

namespace IsLipschitzTX

variable {F : ℝ → E → E} {L : ℝ}

omit [InnerProductSpace ℝ E] in
/-- The standing assumption of arXiv 2412.09400 gives Lipschitz continuity in the state. -/
lemma isLipschitzField (hF : IsLipschitzTX F L) : IsLipschitzField F L := fun t x y => by
  simpa using hF t t x y

omit [InnerProductSpace ℝ E] in
/-- The standing assumption of arXiv 2412.09400 gives Lipschitz continuity in time. -/
lemma time (hF : IsLipschitzTX F L) : ∀ s t x, ‖F s x - F t x‖ ≤ L * |s - t| :=
  fun s t x => by simpa using hF s t x x

end IsLipschitzTX

/-- One **mBUG step** (merge-BUG, arXiv 2412.09400, Algorithm 2, in the abstract projector form
of the library) from `(t₀, Y₀)` to `(t₁, Y₁)`: there are an orthogonal projector `Π` (the
Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` onto the merged bases `Û = qr [U₀, U_F, K₁]`,
`V̂ = qr [V₀, V_F, L₁]`), the truncated right-hand side `F_c = T_{ε_f}(F(t₀, Y₀))` and the S-step
value `X̂ = Û Ŝ₁ V̂ᵀ` such that `Π` fixes `Y₀` and `F_c`, `X̂ = Π (Y₀ + Δt F(t₁, X̂))` (implicit
Euler S-step) and `‖Y₁ - X̂‖ ≤ ε_s` (final truncation). -/
def IsMBUGStep (F : ℝ → E → E) (εf εs t₀ t₁ : ℝ) (Y₀ Y₁ : E) : Prop :=
  ∃ (Pr : E →L[ℝ] E) (Fc Xh : E), IsOrthProj Pr ∧ ‖Fc - F t₀ Y₀‖ ≤ εf ∧ Pr Y₀ = Y₀ ∧ Pr Fc = Fc ∧
    Xh = Pr (Y₀ + (t₁ - t₀) • F t₁ Xh) ∧ ‖Y₁ - Xh‖ ≤ εs

/-- The quadrature sum `∑_{s=0}^{P} w_{m,s} G_s`; the quadrature of the paper is
`I_m^{m+1} G = Δt_{n,m} ∑_s w_{m,s} G_s`. -/
noncomputable def quadSum (w : ℕ → ℕ → ℝ) (P m : ℕ) (G : ℕ → E) : E :=
  ∑ s ∈ range (P + 1), w m s • G s

/-- One **low-rank correction sweep** of SDC-mBUG (arXiv 2412.09400, §3.1, Steps C-1 to C-3) from
the level-`k` iterates `Yk` to the level-`k+1` iterates `Y`, with tolerances `ε_f^{(k)}`,
`ε_r^{(k)}`, `ε_s^{(k+1)}`: there are truncations `F_s^{(k)}` of `F(t_s, Yk_s)` (Step C-1) and,
for every substep `m`, a truncated residual
`R_m ≈ Δt_m (∑_s w_{m,s} F_s^{(k)} - F_{m+1}^{(k)})` (Step C-2), a Galerkin projector `Π_m`
onto the merged bases `qr [U^{(k+1)}_m, U^{(k)}_{F,m+1}, U^{(k)}_{R,m}]` (fixing `Y m`,
`F^{(k)}_{m+1}` and `R_m`), the S-step value `X̂ = Π_m (Y m + Δt_m F(t_{m+1}, X̂) + R_m)`
(eq. (11)) and the final truncation `‖Y (m+1) - X̂‖ ≤ ε_s^{(k+1)}`. -/
def IsCorrectionSweep (F : ℝ → E → E) (t : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (P : ℕ) (εf εr εs : ℝ)
    (Yk Y : ℕ → E) : Prop :=
  ∃ Fk : ℕ → E, (∀ s ≤ P, ‖Fk s - F (t s) (Yk s)‖ ≤ εf) ∧
    ∀ m < P, ∃ (Pr : E →L[ℝ] E) (R Xh : E), IsOrthProj Pr ∧
      ‖R - (t (m + 1) - t m) • (quadSum w P m Fk - Fk (m + 1))‖ ≤ εr ∧
      Pr (Y m) = Y m ∧ Pr (Fk (m + 1)) = Fk (m + 1) ∧ Pr R = R ∧
      Xh = Pr (Y m + (t (m + 1) - t m) • F (t (m + 1)) Xh + R) ∧ ‖Y (m + 1) - Xh‖ ≤ εs

/-! ### One-step estimates -/

/-- **Error of one perturbed mBUG step** (the building block of Stage 1 of SDC-mBUG; with
`Y₀ = X t₀` it is Lemma 3.1 of arXiv 2412.09400, proved in the library as
`LeanDLRA.mergeBUG_local_error`).  Here the start `Y₀` may differ from the exact value. -/
theorem mbug_step_error {F : ℝ → E → E} {L B γ h Δ εf εs a b : ℝ} (hF : IsLipschitzTX F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hγ : γ < 1) (hb : b = a + Δ) (hΔ0 : 0 ≤ Δ)
    (hΔh : Δ ≤ h) (hhL : h * L ≤ γ) {X : ℝ → E} (hX : ODESolution F X a b) {Y Y' : E}
    (hstep : IsMBUGStep F εf εs a b Y Y') :
    ‖X b - Y'‖ ≤ ((1 + γ) * ‖X a - Y‖ + 2 * L * (B + 1) * h ^ 2 + h * εf) / (1 - γ) + εs := by
  obtain ⟨Pr, Fc, Xh, hPr, hFc, hfixY, hfixF, hXh, hY'⟩ := hstep
  have hba : b - a = Δ := by rw [hb]; ring
  rw [hba] at hXh
  have hd := hX.implicitEuler_defect_le hF.isLipschitzField hL hF.time hL hB hb hΔ0
  have hXh' : Xh = Y + Δ • Pr (F b Xh) := by
    conv_lhs => rw [hXh]
    rw [map_add, map_smul, hfixY]
  set e := ‖X a - Y‖ with he
  set d := ‖X b - Xh‖ with hdd
  have hdec : X b - Xh = (X a - Y) + (X b - X a - Δ • F b (X b)) +
      Δ • ((1 - Pr) (F b (X b))) + Δ • Pr (F b (X b) - F b Xh) := by
    conv_lhs => rw [hXh']
    simp only [sub_apply, one_apply_eq_self, map_sub, smul_sub]
    abel
  have hεf : 0 ≤ εf := (norm_nonneg _).trans hFc
  have hXba : ‖X b - X a‖ ≤ B * Δ := hX.norm_sub_start_le hB hb b ⟨by linarith, le_rfl⟩
  have h1 : ‖(1 - Pr) (F b (X b))‖ ≤ L * (B * Δ + e) + L * Δ + εf := by
    refine (norm_compl_le_of_fixed hPr hfixF le_rfl).trans ?_
    have h2 : ‖F b (X b) - F a Y‖ ≤ L * ‖X b - Y‖ + L * |b - a| := hF b a _ _
    have h3 : ‖X b - Y‖ ≤ B * Δ + e := by
      calc ‖X b - Y‖ ≤ ‖X b - X a‖ + ‖X a - Y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by linarith
    rw [hba, abs_of_nonneg hΔ0] at h2
    calc ‖F b (X b) - Fc‖ ≤ ‖F b (X b) - F a Y‖ + ‖F a Y - Fc‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * ‖X b - Y‖ + L * Δ + εf := by rw [norm_sub_rev (F a Y)]; linarith
      _ ≤ _ := by nlinarith
  have h2 : ‖Pr (F b (X b) - F b Xh)‖ ≤ L * d :=
    (hPr.norm_le _).trans (hF.isLipschitzField b _ _)
  have hDd : d = ‖(X a - Y) + (X b - X a - Δ • F b (X b)) +
      Δ • ((1 - Pr) (F b (X b))) + Δ • Pr (F b (X b) - F b Xh)‖ := by rw [hdd, hdec]
  have htri : d ≤ e + (L * B + L) * Δ ^ 2 + Δ * (L * (B * Δ + e) + L * Δ + εf) + Δ * (L * d) := by
    nth_rewrite 1 [hDd]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hd)) ?_)) ?_)
    · rw [norm_smul, Real.norm_of_nonneg hΔ0]; exact mul_le_mul_of_nonneg_left h1 hΔ0
    · rw [norm_smul, Real.norm_of_nonneg hΔ0]; exact mul_le_mul_of_nonneg_left h2 hΔ0
  have hpos : 0 < 1 - γ := by linarith
  have hΔL : Δ * L ≤ γ := (mul_le_mul_of_nonneg_right hΔh hL).trans hhL
  have he0 : 0 ≤ e := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hB0 : 0 ≤ B := hB.nonneg
  have hΔ2 : Δ ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hΔ0 hΔh 2
  have hkey : (1 - γ) * d ≤ (1 + γ) * e + 2 * L * (B + 1) * h ^ 2 + h * εf := by
    have i1 : Δ * L * d ≤ γ * d := mul_le_mul_of_nonneg_right hΔL hd0
    have i2 : Δ * L * e ≤ γ * e := mul_le_mul_of_nonneg_right hΔL he0
    have i3 : L * (B + 1) * Δ ^ 2 ≤ L * (B + 1) * h ^ 2 :=
      mul_le_mul_of_nonneg_left hΔ2 (by positivity)
    have i4 : Δ * εf ≤ h * εf := mul_le_mul_of_nonneg_right hΔh hεf
    nlinarith
  have hD : d ≤ ((1 + γ) * e + 2 * L * (B + 1) * h ^ 2 + h * εf) / (1 - γ) := by
    rw [le_div_iff₀ hpos]; linarith
  calc ‖X b - Y'‖ ≤ ‖X b - Xh‖ + ‖Xh - Y'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by rw [norm_sub_rev Xh]; linarith

/-- **Error of one corrected S-step of SDC-mBUG** (arXiv 2412.09400, proof of Theorem 3.2).  Let
`x s = X(t_s)` be the exact values at the nodes, with the quadrature defect
`‖x_{m+1} - x_m - Δ ∑_s w_s F(t_s, x_s)‖ ≤ q`, let the level-`k` iterates satisfy
`‖x_s - Yk_s‖ ≤ E_k` at all nodes, and let `Y'` be computed from `Y` by the corrected S-step
with tolerances `ε_f, ε_r, ε_s`.  Then for `0 ≤ Δ ≤ h`, `h L ≤ γ < 1`,
`‖x_{m+1} - Y'‖ ≤ (‖x_m - Y‖ + q + ε_r + h (Λ + 1) (L E_k + ε_f)) / (1 - γ) + ε_s`, where
`Λ ≥ ∑_s |w_s|`.  The paper's proof uses
`Û Ûᵀ F(X^{(k+1)}_{m+1}) V̂ V̂ᵀ = F(X^{(k+1)}_{m+1})`, which does not follow from its choice (10)
of the bases; this proof does not need it: the projector only has to fix `Y`, `R` and
`F^{(k)}_{m+1}`. -/
theorem correction_step_error {F : ℝ → E → E} {L γ h Λ q Ek εf εr εs Δ : ℝ} {P m : ℕ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hγ : γ < 1) (hΔ0 : 0 ≤ Δ) (hΔh : Δ ≤ h)
    (hhL : h * L ≤ γ) {Pr : E →L[ℝ] E} (hPr : IsOrthProj Pr) {w : ℕ → ℝ}
    (hw : ∑ s ∈ range (P + 1), |w s| ≤ Λ) {tn : ℕ → ℝ} {x Yk Fk : ℕ → E} (hm : m < P)
    {Y Y' R Xh : E}
    (hq : ‖x (m + 1) - x m - Δ • ∑ s ∈ range (P + 1), w s • F (tn s) (x s)‖ ≤ q)
    (hE : ∀ s ≤ P, ‖x s - Yk s‖ ≤ Ek) (hFk : ∀ s ≤ P, ‖Fk s - F (tn s) (Yk s)‖ ≤ εf)
    (hR : ‖R - Δ • (∑ s ∈ range (P + 1), w s • Fk s - Fk (m + 1))‖ ≤ εr)
    (hfixY : Pr Y = Y) (hfixF : Pr (Fk (m + 1)) = Fk (m + 1)) (hfixR : Pr R = R)
    (hXh : Xh = Pr (Y + Δ • F (tn (m + 1)) Xh + R)) (hY' : ‖Y' - Xh‖ ≤ εs) :
    ‖x (m + 1) - Y'‖ ≤ (‖x m - Y‖ + q + εr + h * (Λ + 1) * (L * Ek + εf)) / (1 - γ) + εs := by
  have hXh' : Xh = Y + R + Δ • Pr (F (tn (m + 1)) Xh) := by
    conv_lhs => rw [hXh]
    rw [map_add, map_add, map_smul, hfixY, hfixR]
    abel
  set Q := ∑ s ∈ range (P + 1), w s • F (tn s) (x s) with hQ
  set Qk := ∑ s ∈ range (P + 1), w s • Fk s with hQk
  set e := ‖x m - Y‖ with he
  set d := ‖x (m + 1) - Xh‖ with hdd
  have hdec : x (m + 1) - Xh = (x m - Y) + (x (m + 1) - x m - Δ • Q) + Δ • (Q - Qk) -
      (R - Δ • (Qk - Fk (m + 1))) + Δ • Pr (Fk (m + 1) - F (tn (m + 1)) Xh) := by
    conv_lhs => rw [hXh']
    rw [map_sub, hfixF]
    simp only [smul_sub]
    abel
  have hEk : 0 ≤ Ek := (norm_nonneg _).trans (hE 0 (Nat.zero_le _))
  have hεf : 0 ≤ εf := (norm_nonneg _).trans (hFk 0 (Nat.zero_le _))
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg fun s _ => abs_nonneg (w s)).trans hw
  have hc0 : 0 ≤ L * Ek + εf := by positivity
  have hterm : ∀ s ≤ P, ‖F (tn s) (x s) - Fk s‖ ≤ L * Ek + εf := by
    intro s hs
    calc ‖F (tn s) (x s) - Fk s‖ ≤ ‖F (tn s) (x s) - F (tn s) (Yk s)‖ +
          ‖F (tn s) (Yk s) - Fk s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * ‖x s - Yk s‖ + εf := by
          rw [norm_sub_rev (F (tn s) (Yk s))]; exact add_le_add (hF _ _ _) (hFk s hs)
      _ ≤ _ := by nlinarith [hE s hs]
  have h1 : ‖Q - Qk‖ ≤ Λ * (L * Ek + εf) := by
    have hsub : Q - Qk = ∑ s ∈ range (P + 1), w s • (F (tn s) (x s) - Fk s) := by
      rw [hQ, hQk, ← Finset.sum_sub_distrib]
      simp only [smul_sub]
    rw [hsub]
    calc ‖∑ s ∈ range (P + 1), w s • (F (tn s) (x s) - Fk s)‖
        ≤ ∑ s ∈ range (P + 1), ‖w s • (F (tn s) (x s) - Fk s)‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ range (P + 1), |w s| * (L * Ek + εf) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hterm s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))
            (abs_nonneg _)
      _ = (∑ s ∈ range (P + 1), |w s|) * (L * Ek + εf) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hc0
  have h2 : ‖Pr (Fk (m + 1) - F (tn (m + 1)) Xh)‖ ≤ εf + L * (Ek + d) := by
    refine (hPr.norm_le _).trans ?_
    have h3 : ‖Yk (m + 1) - Xh‖ ≤ Ek + d := by
      calc ‖Yk (m + 1) - Xh‖ ≤ ‖Yk (m + 1) - x (m + 1)‖ + ‖x (m + 1) - Xh‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by rw [norm_sub_rev]; linarith [hE (m + 1) hm]
    calc ‖Fk (m + 1) - F (tn (m + 1)) Xh‖ ≤ ‖Fk (m + 1) - F (tn (m + 1)) (Yk (m + 1))‖ +
          ‖F (tn (m + 1)) (Yk (m + 1)) - F (tn (m + 1)) Xh‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ εf + L * ‖Yk (m + 1) - Xh‖ := add_le_add (hFk (m + 1) hm) (hF _ _ _)
      _ ≤ _ := by nlinarith
  have hDd : d = ‖(x m - Y) + (x (m + 1) - x m - Δ • Q) + Δ • (Q - Qk) -
      (R - Δ • (Qk - Fk (m + 1))) + Δ • Pr (Fk (m + 1) - F (tn (m + 1)) Xh)‖ := by rw [hdd, hdec]
  have htri : d ≤ e + q + Δ * (Λ * (L * Ek + εf)) + εr + Δ * (εf + L * (Ek + d)) := by
    nth_rewrite 1 [hDd]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl hq)) ?_))
      hR)) ?_)
    · rw [norm_smul, Real.norm_of_nonneg hΔ0]; exact mul_le_mul_of_nonneg_left h1 hΔ0
    · rw [norm_smul, Real.norm_of_nonneg hΔ0]; exact mul_le_mul_of_nonneg_left h2 hΔ0
  have hpos : 0 < 1 - γ := by linarith
  have hΔL : Δ * L ≤ γ := (mul_le_mul_of_nonneg_right hΔh hL).trans hhL
  have hd0 : 0 ≤ d := norm_nonneg _
  have hkey : (1 - γ) * d ≤ e + q + εr + h * (Λ + 1) * (L * Ek + εf) := by
    have i1 : Δ * L * d ≤ γ * d := mul_le_mul_of_nonneg_right hΔL hd0
    have i2 : Δ * ((Λ + 1) * (L * Ek + εf)) ≤ h * ((Λ + 1) * (L * Ek + εf)) :=
      mul_le_mul_of_nonneg_right hΔh (by positivity)
    nlinarith
  have hD : d ≤ (e + q + εr + h * (Λ + 1) * (L * Ek + εf)) / (1 - γ) := by
    rw [le_div_iff₀ hpos]; linarith
  calc ‖x (m + 1) - Y'‖ ≤ ‖x (m + 1) - Xh‖ + ‖Xh - Y'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by rw [norm_sub_rev Xh]; linarith

/-- A linear recursion `e_{m+1} ≤ a e_m + b` from `e_0 ≤ 0` gives `e_m ≤ (∑_{i<P} aⁱ) b` for all
`m ≤ P` (`a, b ≥ 0`). -/
lemma le_geom_of_rec {e : ℕ → ℝ} {a b : ℝ} {P : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : e 0 ≤ 0)
    (hrec : ∀ m < P, e (m + 1) ≤ a * e m + b) :
    ∀ m ≤ P, e m ≤ (∑ i ∈ range P, a ^ i) * b := by
  have key : ∀ m ≤ P, e m ≤ (∑ i ∈ range m, a ^ i) * b := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
      intro hm
      have h1 := hrec m hm
      have h2 := ih (Nat.le_of_succ_le hm)
      have h3 : ∑ i ∈ range m, a ^ (i + 1) = a * ∑ i ∈ range m, a ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_range_succ', pow_zero, h3]
      nlinarith [mul_le_mul_of_nonneg_left h2 ha]
  intro m hm
  refine (key m hm).trans (mul_le_mul_of_nonneg_right ?_ hb)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    fun i _ _ => pow_nonneg ha i

/-! ### The two sweeps -/

/-- Nodes `t_0 ≤ ⋯ ≤ t_P` give substeps `0 ≤ Δt_m ≤ h = t_P - t_0`. -/
lemma substep_bounds {t : ℕ → ℝ} {P m : ℕ} (ht : MonotoneOn t (Set.Iic P)) (hm : m < P) :
    t 0 ≤ t m ∧ t m ≤ t (m + 1) ∧ t (m + 1) ≤ t P := by
  refine ⟨ht (by simp) (by simp; omega) (Nat.zero_le _), ht (by simp; omega) (by simp; omega)
    (Nat.le_succ _), ht (by simp; omega) (by simp) hm⟩

/-- **Stage 1 of SDC-mBUG** (arXiv 2412.09400, §3.1, Stage 1; the case `k = 1` of eq. (14)):
`P` mBUG substeps from the exact value `Y_0 = X(t_n)` stay within
`(∑_{i<P} aⁱ) ((2 L (B + 1) h² + h ε_f)/(1 - γ) + ε_s)` of the exact solution at every node,
`a = (1 + γ)/(1 - γ)`. -/
theorem stage1_error {F : ℝ → E → E} {L B γ εf εs : ℝ} {P : ℕ} {t : ℕ → ℝ} {X : ℝ → E}
    {Y : ℕ → E} (hF : IsLipschitzTX F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : MonotoneOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ) (hX : ODESolution F X (t 0) (t P))
    (hεf : 0 ≤ εf) (hεs : 0 ≤ εs) (h0 : Y 0 = X (t 0))
    (hstep : ∀ m < P, IsMBUGStep F εf εs (t m) (t (m + 1)) (Y m) (Y (m + 1))) :
    ∀ m ≤ P, ‖X (t m) - Y m‖ ≤ (∑ i ∈ range P, ((1 + γ) / (1 - γ)) ^ i) *
      ((2 * L * (B + 1) * (t P - t 0) ^ 2 + (t P - t 0) * εf) / (1 - γ) + εs) := by
  set h := t P - t 0 with hh
  have hpos : 0 < 1 - γ := by linarith
  have hP0 : t 0 ≤ t P := ht (by simp) (by simp) (Nat.zero_le _)
  have hh0 : 0 ≤ h := by rw [hh]; linarith
  have hγ0 : 0 ≤ γ := (mul_nonneg hh0 hL).trans hhL
  have hB0 : 0 ≤ B := hB.nonneg
  refine le_geom_of_rec (e := fun m => ‖X (t m) - Y m‖) (div_nonneg (by linarith) hpos.le)
    (add_nonneg (div_nonneg (by positivity) hpos.le) hεs) (by simp [h0]) fun m hm => ?_
  obtain ⟨h1, h2, h3⟩ := substep_bounds ht hm
  have hXm : ODESolution F X (t m) (t (m + 1)) := hX.mono h1 h3
  have := mbug_step_error hF hL hB hγ (show t (m + 1) = t m + (t (m + 1) - t m) by ring)
    (by linarith) (by rw [hh]; linarith) hhL hXm (hstep m hm)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **One correction sweep of SDC-mBUG** (arXiv 2412.09400, proof of Theorem 3.2, induction step
of eq. (14)): if the level-`k` iterates are within `E_k` of the exact solution at all nodes, the
level-`k+1` iterates are within
`(∑_{i<P} (1/(1 - γ))ⁱ) ((C_A h^{P+2} + ε_r + h (Λ + 1) (L E_k + ε_f))/(1 - γ) + ε_s)`,
where `C_A h^{P+2}` bounds the quadrature defect of the exact solution. -/
theorem correction_sweep_error {F : ℝ → E → E} {L γ Λ CA Ek εf εr εs : ℝ} {P : ℕ}
    {t : ℕ → ℝ} {w : ℕ → ℕ → ℝ} {X : ℝ → E} {Yk Y : ℕ → E} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hγ : γ < 1) (ht : MonotoneOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ)
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |w m s| ≤ Λ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hquad : ∀ m < P, ‖X (t (m + 1)) - X (t m) -
      (t (m + 1) - t m) • quadSum w P m (fun s => F (t s) (X (t s)))‖ ≤ CA * (t P - t 0) ^ (P + 2))
    (hEk : ∀ s ≤ P, ‖X (t s) - Yk s‖ ≤ Ek) (hεf : 0 ≤ εf) (hεr : 0 ≤ εr) (hεs : 0 ≤ εs)
    (h0 : Y 0 = X (t 0)) (hsweep : IsCorrectionSweep F t w P εf εr εs Yk Y) :
    ∀ m ≤ P, ‖X (t m) - Y m‖ ≤ (∑ i ∈ range P, (1 / (1 - γ)) ^ i) *
      ((CA * (t P - t 0) ^ (P + 2) + εr + (t P - t 0) * (Λ + 1) * (L * Ek + εf)) / (1 - γ) +
        εs) := by
  set h := t P - t 0 with hh
  have hpos : 0 < 1 - γ := by linarith
  have hP0 : t 0 ≤ t P := ht (by simp) (by simp) (Nat.zero_le _)
  have hh0 : 0 ≤ h := by rw [hh]; linarith
  have hE0 : 0 ≤ Ek := (norm_nonneg _).trans (hEk 0 (Nat.zero_le _))
  obtain ⟨Fk, hFk, hstep⟩ := hsweep
  refine le_geom_of_rec (e := fun m => ‖X (t m) - Y m‖) (div_nonneg zero_le_one hpos.le)
    (add_nonneg (div_nonneg (by positivity) hpos.le) hεs) (by simp [h0]) fun m hm => ?_
  obtain ⟨h1, h2, h3⟩ := substep_bounds ht hm
  obtain ⟨Pr, R, Xh, hPr, hR, hfY, hfF, hfR, hXh, hY'⟩ := hstep m hm
  have := correction_step_error (x := fun s => X (t s)) (Yk := Yk) (tn := t) (Fk := Fk)
    (hF) hL hγ (by linarith) (by rw [hh]; linarith) hhL hPr (hw m hm) hm (hquad m hm) hEk hFk hR
    hfY hfF hfR hXh hY'
  calc _ ≤ _ := this
    _ = _ := by ring

/-! ### Theorem 3.2: local error of SDC-mBUG -/

/-- The error recursion `δ^{(k)}` of arXiv 2412.09400, Theorem 3.2, with all `O`-constants equal
to one: `δ^{(1)} = ε_s + h ε_f`, `δ^{(k+1)} = h δ^{(k)} + ε_s^{(k+1)} + h ε_f^{(k)} + ε_r^{(k)}`
(the value at `0` is not used). -/
noncomputable def sdcDelta (h εs εf : ℝ) (εsk εfk εrk : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => εs + h * εf
  | k + 2 => h * sdcDelta h εs εf εsk εfk εrk (k + 1) + εsk (k + 2) + h * εfk (k + 1) +
      εrk (k + 1)

/-- The constants `C_k` of arXiv 2412.09400, Theorem 3.2, explicitly: they depend only on `L`,
`B`, `γ`, the weight bound `Λ`, the quadrature constant `C_A`, `P` and `k` (the value at `0` is
not used). -/
noncomputable def sdcC (L B γ Λ CA : ℝ) (P : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => (∑ i ∈ range P, ((1 + γ) / (1 - γ)) ^ i) * (max (2 * L * (B + 1)) 1 / (1 - γ))
  | k + 2 => (∑ i ∈ range P, (1 / (1 - γ)) ^ i) *
      ((Λ + 1) * (1 + L * sdcC L B γ Λ CA P (k + 1)) / (1 - γ) +
        (CA * (γ / L) ^ (P + 2 - min (k + 3) (P + 2)) +
          (Λ + 1) * sdcC L B γ Λ CA P (k + 1) * (L + γ)) / (1 - γ))

/-- `δ^{(k)} ≥ 0` for nonnegative tolerances (arXiv 2412.09400, Theorem 3.2). -/
lemma sdcDelta_nonneg {h εs εf : ℝ} {εsk εfk εrk : ℕ → ℝ} (hh : 0 ≤ h) (hεs : 0 ≤ εs)
    (hεf : 0 ≤ εf) (hεsk : ∀ k, 0 ≤ εsk k) (hεfk : ∀ k, 0 ≤ εfk k) (hεrk : ∀ k, 0 ≤ εrk k) :
    ∀ k, 0 ≤ sdcDelta h εs εf εsk εfk εrk k
  | 0 => le_rfl
  | 1 => by simp only [sdcDelta]; positivity
  | k + 2 => by
      have := sdcDelta_nonneg hh hεs hεf hεsk hεfk hεrk (k + 1)
      have := hεsk (k + 2); have := hεfk (k + 1); have := hεrk (k + 1)
      simp only [sdcDelta]; positivity

/-- The constants `C_k` of arXiv 2412.09400, Theorem 3.2, are nonnegative. -/
lemma sdcC_nonneg {L B γ Λ CA : ℝ} {P : ℕ} (hL : 0 < L) (hγ0 : 0 ≤ γ) (hγ : γ < 1)
    (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA) : ∀ k, 0 ≤ sdcC L B γ Λ CA P k := by
  have hpos : 0 < 1 - γ := by linarith
  have hL0 : 0 ≤ L := hL.le
  have hγL : 0 ≤ γ / L := div_nonneg hγ0 hL0
  have key : ∀ k, 0 ≤ sdcC L B γ Λ CA P (k + 1) := by
    intro k
    induction k with
    | zero =>
      simp only [sdcC]
      exact mul_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (div_nonneg (by linarith)
        hpos.le) i) (div_nonneg ((le_max_right _ _).trans' zero_le_one) hpos.le)
    | succ k ih =>
      simp only [sdcC]
      exact mul_nonneg (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
  intro k
  cases k with
  | zero => exact le_rfl
  | succ k => exact key k

/-- The base case of eq. (14): the Stage-1 bound is `≤ C_1 (δ^{(1)} + h²)`. -/
lemma stage1_bound_le {L B γ εf εs h : ℝ} {P : ℕ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hh : 0 ≤ h)
    (hεf : 0 ≤ εf) (hεs : 0 ≤ εs) :
    (∑ i ∈ range P, ((1 + γ) / (1 - γ)) ^ i) *
      ((2 * L * (B + 1) * h ^ 2 + h * εf) / (1 - γ) + εs) ≤
    (∑ i ∈ range P, ((1 + γ) / (1 - γ)) ^ i) * (max (2 * L * (B + 1)) 1 / (1 - γ)) *
      ((εs + h * εf) + h ^ 2) := by
  have hpos : 0 < 1 - γ := by linarith
  have hG : 0 ≤ ∑ i ∈ range P, ((1 + γ) / (1 - γ)) ^ i :=
    Finset.sum_nonneg fun i _ => by positivity
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hG) (mul_assoc _ _ _).symm
  set M := max (2 * L * (B + 1)) 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM2 : 2 * L * (B + 1) ≤ M := le_max_left _ _
  have hMu : 1 ≤ M / (1 - γ) := by rw [le_div_iff₀ hpos]; linarith
  have e1 : (2 * L * (B + 1) * h ^ 2 + h * εf) / (1 - γ) ≤ M / (1 - γ) * (h ^ 2 + h * εf) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    nlinarith [mul_le_mul_of_nonneg_right hM2 (sq_nonneg h),
      mul_le_mul_of_nonneg_right hM1 (mul_nonneg hh hεf)]
  have e2 : εs ≤ M / (1 - γ) * εs := le_mul_of_one_le_left hεs hMu
  nlinarith

/-- The induction step of eq. (14): the correction-sweep bound with
`E_k = C_k (δ^{(k)} + h^{min(k+1, P+2)})` is `≤ C_{k+1} (δ^{(k+1)} + h^{min(k+2, P+2)})`. -/
lemma correction_bound_le {L γ Λ CA C δ h εf εr εs Ek : ℝ} {P k : ℕ} (hL : 0 < L)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hh : 0 ≤ h) (hhL : h * L ≤ γ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hεf : 0 ≤ εf) (hεr : 0 ≤ εr) (hεs : 0 ≤ εs)
    (hE : Ek ≤ C * (δ + h ^ min (k + 1) (P + 2))) :
    (∑ i ∈ range P, (1 / (1 - γ)) ^ i) *
      ((CA * h ^ (P + 2) + εr + h * (Λ + 1) * (L * Ek + εf)) / (1 - γ) + εs) ≤
    (∑ i ∈ range P, (1 / (1 - γ)) ^ i) *
      ((Λ + 1) * (1 + L * C) / (1 - γ) +
        (CA * (γ / L) ^ (P + 2 - min (k + 2) (P + 2)) + (Λ + 1) * C * (L + γ)) / (1 - γ)) *
      ((h * δ + εs + h * εf + εr) + h ^ min (k + 2) (P + 2)) := by
  have hpos : 0 < 1 - γ := by linarith
  have hG : 0 ≤ ∑ i ∈ range P, (1 / (1 - γ)) ^ i := Finset.sum_nonneg fun i _ => by positivity
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hG) (mul_assoc _ _ _).symm
  set p := min (k + 2) (P + 2) with hp
  set H := h ^ p with hH
  set g := (γ / L) ^ (P + 2 - p) with hg
  set u := 1 / (1 - γ) with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hpos]; linarith
  have hu0 : 0 ≤ u := by linarith
  have hH0 : 0 ≤ H := by positivity
  have hg0 : 0 ≤ g := by positivity
  -- `h^{P+2} ≤ g H`, using `h ≤ γ / L`
  have hhγ : h ≤ γ / L := by rw [le_div_iff₀ hL]; exact hhL
  have ha : h ^ (P + 2) ≤ g * H := by
    have hsplit : h ^ (P + 2) = h ^ (P + 2 - p) * H := by
      rw [hH, ← pow_add]; congr 1; omega
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hhγ _) hH0
  -- `L h h^{min(k+1, P+2)} ≤ (L + γ) H`
  have hb : L * (h * h ^ min (k + 1) (P + 2)) ≤ (L + γ) * H := by
    by_cases hk : k + 1 ≤ P + 1
    · have e1 : min (k + 1) (P + 2) = k + 1 := by omega
      have e2 : p = k + 2 := by omega
      rw [e1, hH, e2, ← pow_succ']
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · have e1 : min (k + 1) (P + 2) = P + 2 := by omega
      have e2 : p = P + 2 := by omega
      rw [e1, hH, e2, ← mul_assoc, mul_comm L h]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hK1 : 1 ≤ (Λ + 1) * (1 + L * C) := by nlinarith [mul_nonneg hL.le hC]
  have hcd : (Λ + 1) * (1 + L * C) / (1 - γ) = (Λ + 1) * (1 + L * C) * u := by
    rw [hu]; ring
  have hch : (CA * g + (Λ + 1) * C * (L + γ)) / (1 - γ) = (CA * g + (Λ + 1) * C * (L + γ)) * u := by
    rw [hu]; ring
  have hlhs : (CA * h ^ (P + 2) + εr + h * (Λ + 1) * (L * Ek + εf)) / (1 - γ) + εs =
      (CA * h ^ (P + 2) + εr + h * (Λ + 1) * (L * Ek + εf)) * u + εs := by rw [hu]; ring
  rw [hcd, hch, hlhs]
  -- bound of the bracket
  have hEk : h * Ek ≤ C * (h * δ) + C * (h * h ^ min (k + 1) (P + 2)) := by
    have := mul_le_mul_of_nonneg_left hE hh
    linarith
  have i1 : CA * h ^ (P + 2) ≤ CA * (g * H) := mul_le_mul_of_nonneg_left ha hCA
  have i2 : (Λ + 1) * L * (h * Ek) ≤
      (Λ + 1) * L * (C * (h * δ) + C * (h * h ^ min (k + 1) (P + 2))) :=
    mul_le_mul_of_nonneg_left hEk (by positivity)
  have i3 : (Λ + 1) * C * (L * (h * h ^ min (k + 1) (P + 2))) ≤ (Λ + 1) * C * ((L + γ) * H) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hbr : CA * h ^ (P + 2) + εr + h * (Λ + 1) * (L * Ek + εf) ≤
      (CA * g + (Λ + 1) * C * (L + γ)) * H + εr + (Λ + 1) * (h * εf) +
        (Λ + 1) * L * C * (h * δ) := by
    linarith
  have hbr' := mul_le_mul_of_nonneg_right hbr hu0
  have j1 : 0 ≤ (Λ + 1) * u * (h * δ) := by positivity
  have j2 : 0 ≤ (Λ + 1) * L * C * u * (h * εf) := by positivity
  have j3 : 0 ≤ (Λ + Λ * L * C + L * C) * u * εr := by positivity
  have j4 : 0 ≤ (Λ + Λ * L * C + L * C) * u * εs := by positivity
  have j4' : 0 ≤ (u - 1) * εs := mul_nonneg (by linarith) hεs
  have j5 : 0 ≤ (Λ + 1) * (1 + L * C) * u * H := by positivity
  have j6 : 0 ≤ (CA * g + (Λ + 1) * C * (L + γ)) * u * (h * δ + εs + h * εf + εr) := by
    positivity
  linarith

/-- **Theorem 3.2 of arXiv 2412.09400 at all nodes and levels** (eq. (14) of its proof),
conditional on the quadrature-defect bound `hquad` (the bound on the term (A) of the proof).  Let
`F` be Lipschitz in both variables with `L > 0` and bounded by `B`, `X` the exact solution on
`[t_n, t_{n+1}] = [t_0, t_P]`, `h = t_P - t_0`, `h L ≤ γ < 1`, let the quadrature weights satisfy
`∑_s |w_{m,s}| ≤ Λ`, and let the exact solution have quadrature defect
`‖X(t_{m+1}) - X(t_m) - I_m^{m+1} F(X)‖ ≤ C_A h^{P+2}` (Theorem 2.1 setting, proved from
smoothness in `quadDefect_le` below).  If `Y 1` is computed by `P` mBUG substeps and `Y (k+1)`
from `Y k` by a low-rank correction sweep (`k = 1, …, K`), all from `Y k 0 = X(t_n)`, then for
`1 ≤ k ≤ K + 1` and all nodes `m ≤ P`

  `‖X(t_m) - Y k m‖ ≤ C_k (δ^{(k)} + h^{min(k+1, P+2)})`

with the explicit constants `C_k = sdcC L B γ Λ C_A P k`.  Differences from the paper: the
statement is on an abstract real inner product space (matrices with the Frobenius inner product
and `Pr Z = Û Ûᵀ Z V̂ V̂ᵀ` are an instance); the truncations are only used through their error
bounds; the constants also depend on `Λ` and `C_A`, which the paper hides in its `O`. -/
theorem sdc_mbug_node_error {F : ℝ → E → E} {L B γ Λ CA εs εf : ℝ} {P K : ℕ} {t : ℕ → ℝ}
    {w : ℕ → ℕ → ℝ} {X : ℝ → E} {Y : ℕ → ℕ → E} {εsk εfk εrk : ℕ → ℝ}
    (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : MonotoneOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ) (hX : ODESolution F X (t 0) (t P))
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |w m s| ≤ Λ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hquad : ∀ m < P, ‖X (t (m + 1)) - X (t m) -
      (t (m + 1) - t m) • quadSum w P m (fun s => F (t s) (X (t s)))‖ ≤ CA * (t P - t 0) ^ (P + 2))
    (hεs : 0 ≤ εs) (hεf : 0 ≤ εf) (hεsk : ∀ k, 0 ≤ εsk k) (hεfk : ∀ k, 0 ≤ εfk k)
    (hεrk : ∀ k, 0 ≤ εrk k) (hinit : ∀ k, Y k 0 = X (t 0))
    (h1 : ∀ m < P, IsMBUGStep F εf εs (t m) (t (m + 1)) (Y 1 m) (Y 1 (m + 1)))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K →
      IsCorrectionSweep F t w P (εfk k) (εrk k) (εsk (k + 1)) (Y k) (Y (k + 1))) :
    ∀ k, 1 ≤ k → k ≤ K + 1 → ∀ m ≤ P, ‖X (t m) - Y k m‖ ≤
      sdcC L B γ Λ CA P k * (sdcDelta (t P - t 0) εs εf εsk εfk εrk k +
        (t P - t 0) ^ min (k + 1) (P + 2)) := by
  set h := t P - t 0 with hh
  have hP0 : t 0 ≤ t P := ht (by simp) (by simp) (Nat.zero_le _)
  have hh0 : 0 ≤ h := by rw [hh]; linarith
  have hγ0 : 0 ≤ γ := (mul_nonneg hh0 hL.le).trans hhL
  have hB0 : 0 ≤ B := hB.nonneg
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _ m hm
    have := stage1_error hF hL.le hB hγ ht hhL hX hεf hεs (hinit 1) h1 m hm
    refine this.trans ?_
    have e : min (1 + 1) (P + 2) = 2 := by omega
    rw [e]
    simpa only [sdcC, sdcDelta] using stage1_bound_le (P := P) (L := L) (B := B) hγ0 hγ hh0 hεf hεs
  | succ k hk ih =>
    intro hkK m hm
    have ih' := ih (by omega)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hC := sdcC_nonneg (P := P) (CA := CA) (Λ := Λ) (B := B) hL hγ0 hγ hΛ hCA (j + 1)
    have hδ := sdcDelta_nonneg hh0 hεs hεf hεsk hεfk hεrk (j + 1) (εsk := εsk) (εfk := εfk)
      (εrk := εrk)
    set Ek := sdcC L B γ Λ CA P (j + 1) *
      (sdcDelta h εs εf εsk εfk εrk (j + 1) + h ^ min (j + 1 + 1) (P + 2)) with hEk
    have hE0 : 0 ≤ Ek := by positivity
    have := correction_sweep_error hF.isLipschitzField hL.le hγ ht hhL hw hΛ hCA hquad ih'
      (hεfk (j + 1)) (hεrk (j + 1)) (hεsk (j + 1 + 1)) (hinit (j + 1 + 1))
      (hcorr (j + 1) (by omega) (by omega)) m hm
    refine this.trans ?_
    have := correction_bound_le (P := P) (k := j + 1) hL hγ0 hγ hh0 hhL hΛ hCA hC hδ
      (hεfk (j + 1)) (hεrk (j + 1)) (hεsk (j + 1 + 1)) le_rfl
    refine this.trans (le_of_eq ?_)
    simp only [sdcC, sdcDelta]

/-- **Theorem 3.2 of arXiv 2412.09400 (local error of SDC-mBUG)**, conditional on the
quadrature-defect bound `hquad` (unconditional under smoothness: `sdc_mbug_local_error_smooth`):
under the hypotheses of
`sdc_mbug_node_error`, the SDC-mBUG approximation `X_{n+1} = Y (K+1) P` after `K` correction
sweeps satisfies

  `‖X_{n+1} - X(t_{n+1})‖ ≤ C_{K+1} (δ^{(K+1)} + h^{min(K+2, P+2)})`,

with `C_{K+1} = sdcC L B γ Λ C_A P (K+1)`, depending only on `L, B, γ, P, K` and the quadrature
data `Λ, C_A`. -/
theorem sdc_mbug_local_error {F : ℝ → E → E} {L B γ Λ CA εs εf : ℝ} {P K : ℕ} {t : ℕ → ℝ}
    {w : ℕ → ℕ → ℝ} {X : ℝ → E} {Y : ℕ → ℕ → E} {εsk εfk εrk : ℕ → ℝ}
    (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : MonotoneOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ) (hX : ODESolution F X (t 0) (t P))
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |w m s| ≤ Λ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hquad : ∀ m < P, ‖X (t (m + 1)) - X (t m) -
      (t (m + 1) - t m) • quadSum w P m (fun s => F (t s) (X (t s)))‖ ≤ CA * (t P - t 0) ^ (P + 2))
    (hεs : 0 ≤ εs) (hεf : 0 ≤ εf) (hεsk : ∀ k, 0 ≤ εsk k) (hεfk : ∀ k, 0 ≤ εfk k)
    (hεrk : ∀ k, 0 ≤ εrk k) (hinit : ∀ k, Y k 0 = X (t 0))
    (h1 : ∀ m < P, IsMBUGStep F εf εs (t m) (t (m + 1)) (Y 1 m) (Y 1 (m + 1)))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K →
      IsCorrectionSweep F t w P (εfk k) (εrk k) (εsk (k + 1)) (Y k) (Y (k + 1))) :
    ‖Y (K + 1) P - X (t P)‖ ≤ sdcC L B γ Λ CA P (K + 1) *
      (sdcDelta (t P - t 0) εs εf εsk εfk εrk (K + 1) + (t P - t 0) ^ min (K + 2) (P + 2)) := by
  rw [norm_sub_rev]
  exact sdc_mbug_node_error hF hL hB hγ ht hhL hX hw hΛ hCA hquad hεs hεf hεsk hεfk hεrk hinit h1
    hcorr (K + 1) (by omega) le_rfl P le_rfl

/-- The closed form of `δ^{(k+1)}` displayed in the proof of Theorem 3.2 of arXiv 2412.09400:
`δ^{(k+1)} = h^k ε_s + h^{k+1} ε_f + ∑_{i=1}^{k} h^{k-i} (ε_s^{(i+1)} + h ε_f^{(i)} + ε_r^{(i)})`
(here an identity, since all `O`-constants are one). -/
theorem sdcDelta_closed_form (h εs εf : ℝ) (εsk εfk εrk : ℕ → ℝ) (k : ℕ) :
    sdcDelta h εs εf εsk εfk εrk (k + 1) = h ^ k * εs + h ^ (k + 1) * εf +
      ∑ i ∈ Icc 1 k, h ^ (k - i) * (εsk (i + 1) + h * εfk i + εrk i) := by
  induction k with
  | zero => simp [sdcDelta]
  | succ k ih =>
    have hs : h * ∑ i ∈ Icc 1 k, h ^ (k - i) * (εsk (i + 1) + h * εfk i + εrk i) =
        ∑ i ∈ Icc 1 k, h ^ (k + 1 - i) * (εsk (i + 1) + h * εfk i + εrk i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : k + 1 - i = (k - i) + 1 := by have := (Finset.mem_Icc.mp hi).2; omega
      rw [hik, pow_succ]; ring
    rw [sdcDelta, ih, Finset.sum_Icc_succ_top (by omega), mul_add, mul_add, hs, Nat.sub_self,
      pow_zero, one_mul]
    ring

/-- With the tolerances of Remark 3.1 the error recursion is `δ^{(k)} ≤ 3 k c h^{k+1}`. -/
lemma sdcDelta_le_of_tol {h εs εf c : ℝ} {εsk εfk εrk : ℕ → ℝ} {K : ℕ} (hh : 0 ≤ h)
    (hc : 0 ≤ c) (h1 : εs ≤ c * h ^ 2) (h2 : εf ≤ c * h)
    (h3 : ∀ k, 1 ≤ k → k ≤ K → εsk (k + 1) ≤ c * h ^ (k + 2))
    (h4 : ∀ k, 1 ≤ k → k ≤ K → εfk k ≤ c * h ^ (k + 1))
    (h5 : ∀ k, 1 ≤ k → k ≤ K → εrk k ≤ c * h ^ (k + 2)) :
    ∀ k, 1 ≤ k → k ≤ K + 1 → sdcDelta h εs εf εsk εfk εrk k ≤ 3 * k * c * h ^ (k + 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    simp only [sdcDelta]
    have : h * εf ≤ h * (c * h) := mul_le_mul_of_nonneg_left h2 hh
    rw [show (3 : ℝ) * ((1 : ℕ) : ℝ) * c * h ^ (1 + 1) = 3 * (c * h ^ 2) by push_cast; ring]
    have e : h * (c * h) = c * h ^ 2 := by ring
    have : 0 ≤ c * h ^ 2 := by positivity
    linarith
  | succ k hk ih =>
    intro hkK
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have ih' := ih (by omega)
    simp only [sdcDelta]
    have e1 : h * sdcDelta h εs εf εsk εfk εrk (j + 1) ≤ 3 * ((j : ℝ) + 1) * (c * h ^ (j + 3)) := by
      have := mul_le_mul_of_nonneg_left ih' hh
      calc _ ≤ _ := this
        _ = _ := by push_cast; ring
    have e2 : εsk (j + 2) ≤ c * h ^ (j + 3) := h3 (j + 1) (by omega) (by omega)
    have e3 : h * εfk (j + 1) ≤ c * h ^ (j + 3) := by
      have := mul_le_mul_of_nonneg_left (h4 (j + 1) (by omega) (by omega)) hh
      calc _ ≤ _ := this
        _ = _ := by ring
    have e4 : εrk (j + 1) ≤ c * h ^ (j + 3) := h5 (j + 1) (by omega) (by omega)
    rw [show (3 : ℝ) * ((j + 1 + 1 : ℕ) : ℝ) * c * h ^ (j + 1 + 1 + 1) =
      3 * ((j : ℝ) + 2) * (c * h ^ (j + 3)) by push_cast; ring]
    linarith

/-- **Remark 3.1 of arXiv 2412.09400 (order `K + 1`)**, conditional on the quadrature-defect
bound `hquad` as `sdc_mbug_local_error`: with `P = K` and the tolerances
`ε_s ≤ c h²`, `ε_f ≤ c h`, `ε_s^{(k+1)}, ε_r^{(k)} ≤ c h^{k+2}`, `ε_f^{(k)} ≤ c h^{k+1}`, the
local error of SDC-mBUG is `O(h^{K+2})`:
`‖X_{n+1} - X(t_{n+1})‖ ≤ C_{K+1} (3 (K + 1) c + 1) h^{K+2}`. -/
theorem sdc_mbug_local_error_order {F : ℝ → E → E} {L B γ Λ CA εs εf c : ℝ} {K : ℕ}
    {t : ℕ → ℝ} {w : ℕ → ℕ → ℝ} {X : ℝ → E} {Y : ℕ → ℕ → E} {εsk εfk εrk : ℕ → ℝ}
    (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : MonotoneOn t (Set.Iic K)) (hhL : (t K - t 0) * L ≤ γ) (hX : ODESolution F X (t 0) (t K))
    (hw : ∀ m < K, ∑ s ∈ range (K + 1), |w m s| ≤ Λ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hquad : ∀ m < K, ‖X (t (m + 1)) - X (t m) -
      (t (m + 1) - t m) • quadSum w K m (fun s => F (t s) (X (t s)))‖ ≤ CA * (t K - t 0) ^ (K + 2))
    (hεs : 0 ≤ εs) (hεf : 0 ≤ εf) (hεsk : ∀ k, 0 ≤ εsk k) (hεfk : ∀ k, 0 ≤ εfk k)
    (hεrk : ∀ k, 0 ≤ εrk k) (hc : 0 ≤ c) (h1c : εs ≤ c * (t K - t 0) ^ 2)
    (h2c : εf ≤ c * (t K - t 0))
    (h3c : ∀ k, 1 ≤ k → k ≤ K → εsk (k + 1) ≤ c * (t K - t 0) ^ (k + 2))
    (h4c : ∀ k, 1 ≤ k → k ≤ K → εfk k ≤ c * (t K - t 0) ^ (k + 1))
    (h5c : ∀ k, 1 ≤ k → k ≤ K → εrk k ≤ c * (t K - t 0) ^ (k + 2))
    (hinit : ∀ k, Y k 0 = X (t 0))
    (h1 : ∀ m < K, IsMBUGStep F εf εs (t m) (t (m + 1)) (Y 1 m) (Y 1 (m + 1)))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K →
      IsCorrectionSweep F t w K (εfk k) (εrk k) (εsk (k + 1)) (Y k) (Y (k + 1))) :
    ‖Y (K + 1) K - X (t K)‖ ≤
      sdcC L B γ Λ CA K (K + 1) * (3 * (K + 1) * c + 1) * (t K - t 0) ^ (K + 2) := by
  have hP0 : t 0 ≤ t K := ht (by simp) (by simp) (Nat.zero_le _)
  have hh0 : 0 ≤ t K - t 0 := by linarith
  have hγ0 : 0 ≤ γ := (mul_nonneg hh0 hL.le).trans hhL
  have hmain := sdc_mbug_local_error hF hL hB hγ ht hhL hX hw hΛ hCA hquad hεs hεf hεsk hεfk
    hεrk hinit h1 hcorr
  have hδ := sdcDelta_le_of_tol hh0 hc h1c h2c h3c h4c h5c (K + 1) (by omega) le_rfl
  have hC := sdcC_nonneg (P := K) (CA := CA) (Λ := Λ) (B := B) hL hγ0 hγ hΛ hCA (K + 1)
  rw [min_self] at hmain
  refine hmain.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hC) (mul_assoc _ _ _).symm)
  rw [show K + 1 + 1 = K + 2 from rfl] at hδ
  push_cast at hδ
  linarith

/-! ### Theorem 2.1: classical (full-rank) SDC -/

/-- The implicit Euler prediction of classical SDC (arXiv 2412.09400, §2.3):
`Y_{m+1} = Y_m + Δt_m F(t_{m+1}, Y_{m+1})`. -/
def IsImplicitEulerSweep (F : ℝ → E → E) (t : ℕ → ℝ) (P : ℕ) (Y : ℕ → E) : Prop :=
  ∀ m < P, Y (m + 1) = Y m + (t (m + 1) - t m) • F (t (m + 1)) (Y (m + 1))

/-- One correction sweep of classical SDC (arXiv 2412.09400, eq. (6)):
`Y_{m+1} = Y_m + Δt_m (F(t_{m+1}, Y_{m+1}) - F(t_{m+1}, Yk_{m+1})) + I_m^{m+1} F(Yk)`. -/
def IsSDCSweep (F : ℝ → E → E) (t : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (P : ℕ) (Yk Y : ℕ → E) : Prop :=
  ∀ m < P, Y (m + 1) = Y m + (t (m + 1) - t m) • (F (t (m + 1)) (Y (m + 1)) -
    F (t (m + 1)) (Yk (m + 1))) + (t (m + 1) - t m) • quadSum w P m (fun s => F (t s) (Yk s))

/-- Implicit Euler is the mBUG step with `Pr = 1` and zero tolerances. -/
lemma IsImplicitEulerSweep.isMBUGStep {F : ℝ → E → E} {t : ℕ → ℝ} {P : ℕ} {Y : ℕ → E}
    (hY : IsImplicitEulerSweep F t P Y) {m : ℕ} (hm : m < P) :
    IsMBUGStep F 0 0 (t m) (t (m + 1)) (Y m) (Y (m + 1)) :=
  ⟨1, F (t m) (Y m), Y (m + 1), IsOrthProj.one, by simp, rfl, rfl,
    by simpa using hY m hm, by simp⟩

/-- The classical SDC correction is the low-rank correction with `Pr = 1` and zero tolerances. -/
lemma IsSDCSweep.isCorrectionSweep {F : ℝ → E → E} {t : ℕ → ℝ} {w : ℕ → ℕ → ℝ} {P : ℕ}
    {Yk Y : ℕ → E} (hY : IsSDCSweep F t w P Yk Y) : IsCorrectionSweep F t w P 0 0 0 Yk Y := by
  refine ⟨fun s => F (t s) (Yk s), fun s _ => by simp, fun m hm => ?_⟩
  refine ⟨1, (t (m + 1) - t m) • (quadSum w P m (fun s => F (t s) (Yk s)) -
    F (t (m + 1)) (Yk (m + 1))), Y (m + 1), IsOrthProj.one, by simp, rfl, rfl, rfl, ?_, by simp⟩
  rw [one_apply_eq_self]
  conv_lhs => rw [hY m hm]
  simp only [smul_sub]
  abel

/-- With all tolerances zero (classical SDC, arXiv 2412.09400, Theorem 2.1), `δ^{(k)} = 0`. -/
lemma sdcDelta_zero (h : ℝ) : ∀ k, sdcDelta h 0 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) k = 0
  | 0 => rfl
  | 1 => by simp [sdcDelta]
  | k + 2 => by simp only [sdcDelta, sdcDelta_zero h (k + 1)]; ring

/-- **Theorem 2.1 of arXiv 2412.09400 (Dutt–Greengard–Rokhlin), given the quadrature error**:
implicit-Euler-based SDC with `P + 1` nodes and `K` correction sweeps has local error
`‖Y_{K+1, P} - X(t_{n+1})‖ ≤ C h^{min(K+2, P+2)}`, `C = sdcC L B γ Λ C_A P (K+1)`, when the
quadrature defect of the exact solution is `≤ C_A h^{P+2}`.  This is the case `Pr = 1`, all
tolerances `0`, of `sdc_mbug_local_error`; `sdc_local_error` derives the quadrature bound from
smoothness. -/
theorem sdc_local_error_of_quad {F : ℝ → E → E} {L B γ Λ CA : ℝ} {P K : ℕ} {t : ℕ → ℝ}
    {w : ℕ → ℕ → ℝ} {X : ℝ → E} {Y : ℕ → ℕ → E}
    (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : MonotoneOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ) (hX : ODESolution F X (t 0) (t P))
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |w m s| ≤ Λ) (hΛ : 0 ≤ Λ) (hCA : 0 ≤ CA)
    (hquad : ∀ m < P, ‖X (t (m + 1)) - X (t m) -
      (t (m + 1) - t m) • quadSum w P m (fun s => F (t s) (X (t s)))‖ ≤ CA * (t P - t 0) ^ (P + 2))
    (hinit : ∀ k, Y k 0 = X (t 0)) (h1 : IsImplicitEulerSweep F t P (Y 1))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K → IsSDCSweep F t w P (Y k) (Y (k + 1))) :
    ‖Y (K + 1) P - X (t P)‖ ≤ sdcC L B γ Λ CA P (K + 1) * (t P - t 0) ^ min (K + 2) (P + 2) := by
  have := sdc_mbug_local_error (εs := 0) (εf := 0) (εsk := fun _ => 0) (εfk := fun _ => 0)
    (εrk := fun _ => 0) hF hL hB hγ ht hhL hX hw hΛ hCA hquad le_rfl le_rfl (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) hinit (fun m hm => h1.isMBUGStep hm)
    (fun k hk hkK => (hcorr k hk hkK).isCorrectionSweep)
  rwa [sdcDelta_zero, zero_add] at this

/-! ### The SDC quadrature and its error -/

/-- The Lagrange basis polynomial `ℓ_s` on the nodes `t_0, …, t_P`. -/
noncomputable def lagBasis (t : ℕ → ℝ) (P s : ℕ) : Polynomial ℝ :=
  Lagrange.basis (range (P + 1)) t s

/-- The SDC quadrature weights of arXiv 2412.09400, §2.3:
`w_{m,s} = (1/Δt_m) ∫_{t_m}^{t_{m+1}} ℓ_s(τ) dτ`, `ℓ_s` the Lagrange basis on all `P + 1`
nodes (eq. (5) prints the products up to `m`; the text says `P + 1` points). -/
noncomputable def sdcWeight (t : ℕ → ℝ) (P m s : ℕ) : ℝ :=
  (∫ τ in t m..t (m + 1), (lagBasis t P s).eval τ) / (t (m + 1) - t m)

/-- Lagrange interpolation reproduces `(u - a)^j` for `j ≤ P`. -/
lemma sum_pow_mul_eval_lagBasis {t : ℕ → ℝ} {P j : ℕ}
    (hinj : Set.InjOn t (range (P + 1) : Finset ℕ)) (hj : j ≤ P) (a u : ℝ) :
    ∑ s ∈ range (P + 1), (t s - a) ^ j * (lagBasis t P s).eval u = (u - a) ^ j := by
  set f : Polynomial ℝ := (Polynomial.X - Polynomial.C a) ^ j with hf
  have hdeg : f.degree < ((range (P + 1)).card : WithBot ℕ) := by
    rw [card_range, hf, Polynomial.degree_pow, Polynomial.degree_X_sub_C, nsmul_one]
    exact_mod_cast Nat.lt_succ_of_le hj
  have h := congrArg (Polynomial.eval u) (Lagrange.eq_interpolate hinj hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at h
  simp only [hf, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X] at h
  exact h.symm

/-- **Exactness of the SDC quadrature for polynomials of degree `≤ P`**:
`Δt_m ∑_s w_{m,s} (t_s - a)^j = ∫_{t_m}^{t_{m+1}} (τ - a)^j dτ`. -/
lemma quad_exact_pow {t : ℕ → ℝ} {P m j : ℕ} (hinj : Set.InjOn t (range (P + 1) : Finset ℕ))
    (hne : t m ≠ t (m + 1)) (hj : j ≤ P) (a : ℝ) :
    (t (m + 1) - t m) * ∑ s ∈ range (P + 1), sdcWeight t P m s * (t s - a) ^ j =
      ((t (m + 1) - a) ^ (j + 1) - (t m - a) ^ (j + 1)) / (j + 1) := by
  have hΔ : t (m + 1) - t m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h1 : (t (m + 1) - t m) * ∑ s ∈ range (P + 1), sdcWeight t P m s * (t s - a) ^ j =
      ∑ s ∈ range (P + 1), ∫ τ in t m..t (m + 1), (t s - a) ^ j * (lagBasis t P s).eval τ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [intervalIntegral.integral_const_mul, sdcWeight]
    field_simp
  have hsum := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := t m)
    (b := t (m + 1)) (s := range (P + 1))
    (f := fun s τ => (t s - a) ^ j * (lagBasis t P s).eval τ)
    (fun s _ => (continuous_const.mul (lagBasis t P s).continuous).intervalIntegrable _ _)
  rw [h1, ← hsum]
  simp_rw [sum_pow_mul_eval_lagBasis hinj hj a]
  have h2 := intervalIntegral.integral_comp_sub_right (a := t m) (b := t (m + 1))
    (fun x : ℝ => x ^ j) a
  rw [h2, integral_pow]

/-- Exactness for `E`-valued polynomials: for `p(τ) = ∑_{j ≤ P} (τ - a)^j c_j` and its
antiderivative `Q(τ) = ∑_{j ≤ P} (τ - a)^{j+1}/(j+1) c_j`,
`Q(t_{m+1}) - Q(t_m) = Δt_m ∑_s w_{m,s} p(t_s)`. -/
lemma quad_exact_poly {t : ℕ → ℝ} {P m : ℕ} (hinj : Set.InjOn t (range (P + 1) : Finset ℕ))
    (hne : t m ≠ t (m + 1)) (a : ℝ) (c : ℕ → E) :
    (∑ j ∈ range (P + 1), ((t (m + 1) - a) ^ (j + 1) / (j + 1)) • c j) -
      ∑ j ∈ range (P + 1), ((t m - a) ^ (j + 1) / (j + 1)) • c j =
    (t (m + 1) - t m) • quadSum (sdcWeight t P) P m
      (fun s => ∑ j ∈ range (P + 1), (t s - a) ^ j • c j) := by
  rw [← Finset.sum_sub_distrib]
  unfold quadSum
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← sub_smul, ← Finset.sum_smul]
  congr 1
  have hj' : j ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have := quad_exact_pow hinj hne hj' a
  rw [Finset.mul_sum] at this
  rw [← sub_div, ← this]

/-- The antiderivative of an `E`-valued polynomial. -/
lemma hasDerivAt_antideriv (a : ℝ) (c : ℕ → E) (P : ℕ) (τ : ℝ) :
    HasDerivAt (fun τ => ∑ j ∈ range (P + 1), ((τ - a) ^ (j + 1) / (j + 1)) • c j)
      (∑ j ∈ range (P + 1), (τ - a) ^ j • c j) τ := by
  refine HasDerivAt.fun_sum fun j _ => ?_
  have h1 : HasDerivAt (fun τ : ℝ => (τ - a) ^ (j + 1) / (j + 1)) ((τ - a) ^ j) τ := by
    have := (((hasDerivAt_id τ).sub_const a).pow (j + 1)).div_const ((j : ℝ) + 1)
    convert this using 1
    · rfl
    · simp only [id, Nat.add_sub_cancel]
      push_cast
      field_simp
  exact h1.smul_const (c j)

/-- **Quadrature defect of the exact solution, polynomial form** (the quadrature error behind
Theorem 2.1 of arXiv 2412.09400): if the exact velocity `g(τ) = F(τ, X τ)` is within `η` of an
`E`-valued polynomial of degree `≤ P` on `[t_0, t_P]` and `∑_s |w_{m,s}| ≤ Λ`, then
`‖X(t_{m+1}) - X(t_m) - Δt_m ∑_s w_{m,s} g(t_s)‖ ≤ (1 + Λ) Δt_m η`. -/
theorem quadDefect_le_of_poly {F : ℝ → E → E} {X : ℝ → E} {t : ℕ → ℝ} {P m : ℕ} {Λ η : ℝ}
    (ht : StrictMonoOn t (Set.Iic P)) (hX : ODESolution F X (t 0) (t P)) (hm : m < P)
    (hw : ∑ s ∈ range (P + 1), |sdcWeight t P m s| ≤ Λ) (c : ℕ → E)
    (hη : ∀ τ ∈ Icc (t 0) (t P), ‖F τ (X τ) - ∑ j ∈ range (P + 1), (τ - t 0) ^ j • c j‖ ≤ η) :
    ‖X (t (m + 1)) - X (t m) - (t (m + 1) - t m) •
      quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s)))‖ ≤
      (1 + Λ) * (t (m + 1) - t m) * η := by
  set a := t 0 with ha
  set p : ℝ → E := fun τ => ∑ j ∈ range (P + 1), (τ - a) ^ j • c j with hp
  set Q : ℝ → E := fun τ => ∑ j ∈ range (P + 1), ((τ - a) ^ (j + 1) / (j + 1)) • c j with hQ
  have hmono := ht.monotoneOn
  obtain ⟨h1, h2, h3⟩ := substep_bounds hmono hm
  have hlt : t m < t (m + 1) := ht (by simp; omega) (by simp; omega) (Nat.lt_succ_self m)
  have hinj : Set.InjOn t (range (P + 1) : Finset ℕ) := by
    refine ht.injOn.mono fun s hs => ?_
    simp only [Finset.coe_range, Set.mem_Iio] at hs
    simp only [Set.mem_Iic]; omega
  have hnode : ∀ s ≤ P, t s ∈ Icc (t 0) (t P) := fun s hs =>
    ⟨hmono (by simp) (by simp; omega) (Nat.zero_le _), hmono (by simp; omega) (by simp) hs⟩
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη (t 0) (hnode 0 (Nat.zero_le _)))
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg fun s _ => abs_nonneg _).trans hw
  have hexact := quad_exact_poly hinj hlt.ne a c
  set Δ := t (m + 1) - t m with hΔ
  have hΔ0 : 0 ≤ Δ := by rw [hΔ]; linarith
  -- decomposition
  have hdec : X (t (m + 1)) - X (t m) - Δ • quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s)))
      = ((X (t (m + 1)) - Q (t (m + 1))) - (X (t m) - Q (t m))) -
        Δ • (quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s))) -
          quadSum (sdcWeight t P) P m (fun s => p (t s))) := by
    have : Q (t (m + 1)) - Q (t m) = Δ • quadSum (sdcWeight t P) P m (fun s => p (t s)) := hexact
    rw [smul_sub, ← this]
    abel
  rw [hdec]
  -- the mean value inequality for `X - Q`
  have hmvt : ‖(X (t (m + 1)) - Q (t (m + 1))) - (X (t m) - Q (t m))‖ ≤ η * Δ := by
    have hc : ContinuousOn (fun τ => X τ - Q τ) (Icc (t m) (t (m + 1))) :=
      (hX.mono h1 h3).cont.sub fun τ _ =>
        (hasDerivAt_antideriv a c P τ).continuousAt.continuousWithinAt
    have hd : ∀ τ ∈ Ico (t m) (t (m + 1)),
        HasDerivWithinAt (fun τ => X τ - Q τ) (F τ (X τ) - p τ) (Ici τ) τ := fun τ hτ =>
      ((hX.mono h1 h3).deriv τ hτ).sub (hasDerivAt_antideriv a c P τ).hasDerivWithinAt
    have hb : ∀ τ ∈ Ico (t m) (t (m + 1)), ‖F τ (X τ) - p τ‖ ≤ η := fun τ hτ =>
      hη τ ⟨h1.trans hτ.1, hτ.2.le.trans h3⟩
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hb (t (m + 1))
      ⟨hlt.le, le_rfl⟩
  have hq : ‖quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s))) -
      quadSum (sdcWeight t P) P m (fun s => p (t s))‖ ≤ Λ * η := by
    unfold quadSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    calc ‖∑ s ∈ range (P + 1), sdcWeight t P m s • (F (t s) (X (t s)) - p (t s))‖
        ≤ ∑ s ∈ range (P + 1), ‖sdcWeight t P m s • (F (t s) (X (t s)) - p (t s))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s ∈ range (P + 1), |sdcWeight t P m s| * η := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (hη (t s) (hnode s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))) (abs_nonneg _)
      _ = (∑ s ∈ range (P + 1), |sdcWeight t P m s|) * η := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hη0
  calc _ ≤ ‖(X (t (m + 1)) - Q (t (m + 1))) - (X (t m) - Q (t m))‖ +
        ‖Δ • (quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s))) -
          quadSum (sdcWeight t P) P m (fun s => p (t s)))‖ := norm_sub_le _ _
    _ ≤ η * Δ + Δ * (Λ * η) := by
        rw [norm_smul, Real.norm_of_nonneg hΔ0]
        exact add_le_add hmvt (mul_le_mul_of_nonneg_left hq hΔ0)
    _ = _ := by ring

/-- **Quadrature defect of the exact solution from smoothness**: if `g(τ) = F(τ, X τ)` is
`C^{P+1}` on `[t_0, t_P]` with `‖g^{(P+1)}‖ ≤ M`, the SDC quadrature applied to the exact solution
has defect `‖X(t_{m+1}) - X(t_m) - I_m^{m+1} F(X)‖ ≤ (1 + Λ) M / P! · h^{P+2}`, `h = t_P - t_0`
(Taylor expansion of `g` at `t_0`, exactness of the quadrature on its Taylor polynomial). -/
theorem quadDefect_le {F : ℝ → E → E} {X : ℝ → E} {t : ℕ → ℝ} {P m : ℕ} {Λ M : ℝ}
    (ht : StrictMonoOn t (Set.Iic P)) (hX : ODESolution F X (t 0) (t P)) (hm : m < P)
    (hw : ∑ s ∈ range (P + 1), |sdcWeight t P m s| ≤ Λ)
    (hg : ContDiffOn ℝ (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)))
    (hM : ∀ τ ∈ Icc (t 0) (t P),
      ‖iteratedDerivWithin (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)) τ‖ ≤ M) :
    ‖X (t (m + 1)) - X (t m) - (t (m + 1) - t m) •
      quadSum (sdcWeight t P) P m (fun s => F (t s) (X (t s)))‖ ≤
      (1 + Λ) * M / (P.factorial : ℝ) * (t P - t 0) ^ (P + 2) := by
  set g : ℝ → E := fun τ => F τ (X τ) with hgdef
  have hmono := ht.monotoneOn
  obtain ⟨h1, h2, h3⟩ := substep_bounds hmono hm
  have hab : t 0 ≤ t P := h1.trans (h2.trans h3)
  have hΛ : 0 ≤ Λ := (Finset.sum_nonneg fun s _ => abs_nonneg _).trans hw
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (t 0) ⟨le_rfl, hab⟩)
  set c : ℕ → E := fun j => ((j.factorial : ℝ)⁻¹) • iteratedDerivWithin j g (Icc (t 0) (t P)) (t 0)
  have hη : ∀ τ ∈ Icc (t 0) (t P), ‖F τ (X τ) - ∑ j ∈ range (P + 1), (τ - t 0) ^ j • c j‖ ≤
      M * (t P - t 0) ^ (P + 1) / (P.factorial : ℝ) := by
    intro τ hτ
    have htay : ∑ j ∈ range (P + 1), (τ - t 0) ^ j • c j =
        taylorWithinEval g P (Icc (t 0) (t P)) (t 0) τ := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c, smul_smul]
      rw [mul_comm]
    rw [htay]
    refine (taylor_mean_remainder_bound hab hg hτ hM).trans ?_
    have : (τ - t 0) ^ (P + 1) ≤ (t P - t 0) ^ (P + 1) :=
      pow_le_pow_left₀ (by linarith [hτ.1]) (by linarith [hτ.2]) _
    gcongr
  refine (quadDefect_le_of_poly ht hX hm hw c hη).trans ?_
  have hΔ : t (m + 1) - t m ≤ t P - t 0 := by linarith
  have hfac : (0 : ℝ) < (P.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos P
  have hh0 : 0 ≤ t P - t 0 := by linarith
  calc (1 + Λ) * (t (m + 1) - t m) * (M * (t P - t 0) ^ (P + 1) / (P.factorial : ℝ))
      ≤ (1 + Λ) * (t P - t 0) * (M * (t P - t 0) ^ (P + 1) / (P.factorial : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- **Theorem 2.1 of arXiv 2412.09400 (Dutt–Greengard–Rokhlin; local error of SDC)**:
implicit-Euler-based SDC with `P + 1` nodes `t_0 < ⋯ < t_P` (`h = t_P - t_0`), the quadrature
weights `w_{m,s} = (1/Δt_m) ∫_{t_m}^{t_{m+1}} ℓ_s` and `K` correction sweeps satisfies

  `‖Y_{K+1, P} - X(t_{n+1})‖ ≤ C h^{min(K+2, P+2)}`,  `C = sdcC L B γ Λ ((1 + Λ) M / P!) P (K+1)`,

when `F` is Lipschitz in both variables with `L > 0` and bounded by `B`, `h L ≤ γ < 1`, the exact
velocity `τ ↦ F(τ, X τ)` is `C^{P+1}` with `‖(d/dτ)^{P+1} F(τ, X τ)‖ ≤ M`, and
`∑_s |w_{m,s}| ≤ Λ`.  For nodes `t_s = t_n + c_s h` with fixed `c_s` (e.g. Gauss–Lobatto),
`w_{m,s}` and hence `Λ` do not depend on `h` (`sdcWeight_affine`), so this is
`O(h^{min(K+2, P+2)})`.  The paper assumes "smooth `F` and solution"; the Lipschitz and bound
hypotheses are those of its §3.2. -/
theorem sdc_local_error {F : ℝ → E → E} {L B γ Λ M : ℝ} {P K : ℕ} {t : ℕ → ℝ} {X : ℝ → E}
    {Y : ℕ → ℕ → E} (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B)
    (hγ : γ < 1) (ht : StrictMonoOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ)
    (hX : ODESolution F X (t 0) (t P))
    (hg : ContDiffOn ℝ (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)))
    (hM : ∀ τ ∈ Icc (t 0) (t P),
      ‖iteratedDerivWithin (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)) τ‖ ≤ M)
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |sdcWeight t P m s| ≤ Λ) (hΛ : 0 ≤ Λ)
    (hinit : ∀ k, Y k 0 = X (t 0)) (h1 : IsImplicitEulerSweep F t P (Y 1))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K → IsSDCSweep F t (sdcWeight t P) P (Y k) (Y (k + 1))) :
    ‖Y (K + 1) P - X (t P)‖ ≤
      sdcC L B γ Λ ((1 + Λ) * M / (P.factorial : ℝ)) P (K + 1) *
        (t P - t 0) ^ min (K + 2) (P + 2) := by
  have hab : t 0 ≤ t P := ht.monotoneOn (by simp) (by simp) (Nat.zero_le _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (t 0) ⟨le_rfl, hab⟩)
  have hCA : 0 ≤ (1 + Λ) * M / (P.factorial : ℝ) := by positivity
  exact sdc_local_error_of_quad hF hL hB hγ ht.monotoneOn hhL hX hw hΛ hCA
    (fun m hm => quadDefect_le ht hX hm (hw m hm) hg hM) hinit h1 hcorr

/-- **Theorem 3.2 of arXiv 2412.09400 with the SDC quadrature** (`sdc_mbug_local_error` with the
quadrature defect proved by `quadDefect_le`): for nodes `t_0 < ⋯ < t_P`, the Lagrange weights
`sdcWeight` with `∑_s |w_{m,s}| ≤ Λ`, and an exact velocity `τ ↦ F(τ, X τ)` of class `C^{P+1}`
with `‖(d/dτ)^{P+1} F(τ, X τ)‖ ≤ M`, SDC-mBUG satisfies
`‖X_{n+1} - X(t_{n+1})‖ ≤ C_{K+1} (δ^{(K+1)} + h^{min(K+2, P+2)})`,
`C_{K+1} = sdcC L B γ Λ ((1 + Λ) M / P!) P (K+1)`. -/
theorem sdc_mbug_local_error_smooth {F : ℝ → E → E} {L B γ Λ M εs εf : ℝ} {P K : ℕ}
    {t : ℕ → ℝ} {X : ℝ → E} {Y : ℕ → ℕ → E} {εsk εfk εrk : ℕ → ℝ}
    (hF : IsLipschitzTX F L) (hL : 0 < L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (ht : StrictMonoOn t (Set.Iic P)) (hhL : (t P - t 0) * L ≤ γ)
    (hX : ODESolution F X (t 0) (t P))
    (hg : ContDiffOn ℝ (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)))
    (hM : ∀ τ ∈ Icc (t 0) (t P),
      ‖iteratedDerivWithin (P + 1) (fun τ => F τ (X τ)) (Icc (t 0) (t P)) τ‖ ≤ M)
    (hw : ∀ m < P, ∑ s ∈ range (P + 1), |sdcWeight t P m s| ≤ Λ) (hΛ : 0 ≤ Λ)
    (hεs : 0 ≤ εs) (hεf : 0 ≤ εf) (hεsk : ∀ k, 0 ≤ εsk k) (hεfk : ∀ k, 0 ≤ εfk k)
    (hεrk : ∀ k, 0 ≤ εrk k) (hinit : ∀ k, Y k 0 = X (t 0))
    (h1 : ∀ m < P, IsMBUGStep F εf εs (t m) (t (m + 1)) (Y 1 m) (Y 1 (m + 1)))
    (hcorr : ∀ k, 1 ≤ k → k ≤ K →
      IsCorrectionSweep F t (sdcWeight t P) P (εfk k) (εrk k) (εsk (k + 1)) (Y k) (Y (k + 1))) :
    ‖Y (K + 1) P - X (t P)‖ ≤ sdcC L B γ Λ ((1 + Λ) * M / (P.factorial : ℝ)) P (K + 1) *
      (sdcDelta (t P - t 0) εs εf εsk εfk εrk (K + 1) + (t P - t 0) ^ min (K + 2) (P + 2)) := by
  have hab : t 0 ≤ t P := ht.monotoneOn (by simp) (by simp) (Nat.zero_le _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (t 0) ⟨le_rfl, hab⟩)
  have hCA : 0 ≤ (1 + Λ) * M / (P.factorial : ℝ) := by positivity
  exact sdc_mbug_local_error hF hL hB hγ ht.monotoneOn hhL hX hw hΛ hCA
    (fun m hm => quadDefect_le ht hX hm (hw m hm) hg hM) hεs hεf hεsk hεfk hεrk hinit h1 hcorr

/-- The Lagrange basis is invariant under affine maps of the nodes. -/
lemma eval_lagBasis_affine {c : ℕ → ℝ} {P s : ℕ} {a h : ℝ} (hh : h ≠ 0) (u : ℝ) :
    (lagBasis (fun j => a + h * c j) P s).eval (a + h * u) = (lagBasis c P s).eval u := by
  simp only [lagBasis, Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : a + h * c s - (a + h * c j) = h * (c s - c j) := by ring
  have e2 : a + h * u - (a + h * c j) = h * (u - c j) := by ring
  rw [e1, e2, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hh, one_mul]

/-- **The SDC weights do not depend on the step**: for nodes `t_s = a + h c_s` (`h ≠ 0`), the
weights `w_{m,s}` are those of the reference nodes `c_s`. -/
theorem sdcWeight_affine {c : ℕ → ℝ} {P m s : ℕ} {a h : ℝ} (hh : h ≠ 0) :
    sdcWeight (fun j => a + h * c j) P m s = sdcWeight c P m s := by
  have h1 := intervalIntegral.integral_comp_mul_add (a := c m) (b := c (m + 1))
    (fun τ => (lagBasis (fun j => a + h * c j) P s).eval τ) hh a
  have h2 : ∀ x, (lagBasis (fun j => a + h * c j) P s).eval (h * x + a) =
      (lagBasis c P s).eval x := fun x => by rw [add_comm, eval_lagBasis_affine hh]
  simp only [h2, smul_eq_mul] at h1
  rw [add_comm (h * c m) a, add_comm (h * c (m + 1)) a] at h1
  have h3 : (∫ τ in a + h * c m..a + h * c (m + 1),
      (lagBasis (fun j => a + h * c j) P s).eval τ) =
      h * ∫ x in c m..c (m + 1), (lagBasis c P s).eval x := by
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
  unfold sdcWeight
  rw [h3]
  have : a + h * c (m + 1) - (a + h * c m) = h * (c (m + 1) - c m) := by ring
  rw [this, mul_div_mul_left _ _ hh]

/-! ### Matrices: the factor-level mBUG step -/

section MatrixStep

open scoped LeanDLRA.Frobenius

variable {m n p q r r' f f' : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [Fintype r] [Fintype r'] [Fintype f] [Fintype f'] [DecidableEq p] [DecidableEq q]

omit [DecidableEq p] [DecidableEq q] in
/-- The Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` fixes `U₀ S₀ V₀ᵀ` when `Û Ûᵀ U₀ = U₀` and
`V̂ V̂ᵀ V₀ = V₀`. -/
lemma galerkinProj_fix {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ} {U₀ : Matrix m r ℝ}
    {S₀ : Matrix r r' ℝ} {V₀ : Matrix n r' ℝ} (hU : Uh * Uhᵀ * U₀ = U₀)
    (hV : Vh * Vhᵀ * V₀ = V₀) :
    (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (U₀ * S₀ * V₀ᵀ) =
      U₀ * S₀ * V₀ᵀ := by
  rw [mul_apply_eq_comp, leftProj_apply, rightProj_apply]
  have hV' : V₀ᵀ * Vh * Vhᵀ = V₀ᵀ := by
    conv_rhs => rw [← hV]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  calc Uh * Uhᵀ * (U₀ * S₀ * V₀ᵀ * Vh * Vhᵀ)
      = (Uh * Uhᵀ * U₀) * S₀ * (V₀ᵀ * Vh * Vhᵀ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, hV']

omit [DecidableEq p] [DecidableEq q] in
/-- The S-step `Ŝ = Ûᵀ Z V̂ + Δ Ûᵀ F(t₁, Û Ŝ V̂ᵀ) V̂` in factor form is the abstract Galerkin step
`X̂ = Π (Z + Δ F(t₁, X̂))` for `X̂ = Û Ŝ V̂ᵀ` and `Π = leftProj Û * rightProj V̂`. -/
lemma matrix_sstep_eq {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Uh : Matrix m p ℝ}
    {Vh : Matrix n q ℝ} {Sh : Matrix p q ℝ} {Z : Matrix m n ℝ} {Δ t₁ : ℝ}
    (hS : Sh = Uhᵀ * Z * Vh + Δ • (Uhᵀ * F t₁ (Uh * Sh * Vhᵀ) * Vh)) :
    Uh * Sh * Vhᵀ = (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
      (Z + Δ • F t₁ (Uh * Sh * Vhᵀ)) := by
  rw [mul_apply_eq_comp, leftProj_rightProj_apply]
  congr 2
  conv_lhs => rw [hS]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- **The factor-level mBUG step** (arXiv 2412.09400, Algorithm 2) from `Y₀ = U₀ S₀ V₀ᵀ`:
`U_F S_F V_Fᵀ` is the truncation of `F(t₀, Y₀)` with `‖U_F S_F V_Fᵀ - F(t₀, Y₀)‖ ≤ ε_f`; the merged
bases `Û`, `V̂` have orthonormal columns and contain the columns of `U₀, U_F` (resp. `V₀, V_F`),
as `Û = qr [U₀, U_F, K₁]` does; the S-step is
`Ŝ = (Ûᵀ U₀) S₀ (V̂ᵀ V₀)ᵀ + Δt Ûᵀ F(t₁, Û Ŝ V̂ᵀ) V̂`; and the result `Y₁` is a truncation of
`Û Ŝ V̂ᵀ` with `‖Y₁ - Û Ŝ V̂ᵀ‖ ≤ ε_s`.  The implicit K- and L-steps (`K₁`, `L₁`) only enlarge the
bases and are not needed for the error bound, so they are not recorded. -/
structure IsMatrixMBUGStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (εf εs t₀ t₁ : ℝ)
    (U₀ : Matrix m r ℝ) (S₀ : Matrix r r' ℝ) (V₀ : Matrix n r' ℝ) (UF : Matrix m f ℝ)
    (SF : Matrix f f' ℝ) (VF : Matrix n f' ℝ) (Uh : Matrix m p ℝ) (Vh : Matrix n q ℝ)
    (Sh : Matrix p q ℝ) (Y₁ : Matrix m n ℝ) : Prop where
  truncF : ‖UF * SF * VFᵀ - F t₀ (U₀ * S₀ * V₀ᵀ)‖ ≤ εf
  orthU : Uhᵀ * Uh = 1
  orthV : Vhᵀ * Vh = 1
  spanU₀ : Uh * Uhᵀ * U₀ = U₀
  spanV₀ : Vh * Vhᵀ * V₀ = V₀
  spanUF : Uh * Uhᵀ * UF = UF
  spanVF : Vh * Vhᵀ * VF = VF
  sstep : Sh = (Uhᵀ * U₀) * S₀ * (Vhᵀ * V₀)ᵀ + (t₁ - t₀) • (Uhᵀ * F t₁ (Uh * Sh * Vhᵀ) * Vh)
  trunc : ‖Y₁ - Uh * Sh * Vhᵀ‖ ≤ εs

/-- The factor-level mBUG step is an abstract mBUG step on `ℝ^{m×n}` with the Frobenius inner
product, with `Π = leftProj Û * rightProj V̂`. -/
theorem IsMatrixMBUGStep.isMBUGStep {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {εf εs t₀ t₁ : ℝ}
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r' ℝ} {V₀ : Matrix n r' ℝ} {UF : Matrix m f ℝ}
    {SF : Matrix f f' ℝ} {VF : Matrix n f' ℝ} {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ}
    {Sh : Matrix p q ℝ} {Y₁ : Matrix m n ℝ}
    (hs : IsMatrixMBUGStep F εf εs t₀ t₁ U₀ S₀ V₀ UF SF VF Uh Vh Sh Y₁) :
    IsMBUGStep F εf εs t₀ t₁ (U₀ * S₀ * V₀ᵀ) Y₁ := by
  refine ⟨leftProj Uh * rightProj Vh, UF * SF * VFᵀ, Uh * Sh * Vhᵀ,
    isOrthProj_leftProj_mul_rightProj hs.orthU hs.orthV, hs.truncF,
    galerkinProj_fix hs.spanU₀ hs.spanV₀, galerkinProj_fix hs.spanUF hs.spanVF, ?_, hs.trunc⟩
  refine matrix_sstep_eq ?_
  conv_lhs => rw [hs.sstep]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Lemma 3.1 of arXiv 2412.09400 for the factor-level mBUG step** (Appelö–Cheng's first-order
merge-BUG, cited there; the abstract version is the library's `LeanDLRA.mergeBUG_local_error`):
starting from the exact value `X(t₀) = U₀ S₀ V₀ᵀ`, with `h = t₁ - t₀`, `h L ≤ γ < 1`,

  `‖Y₁ - X(t₁)‖ ≤ C (h² + h ε_f + ε_s)`,  `C = max (2 L (B + 1)) 1 / (1 - γ)`,

a constant depending only on `L`, `B` and `γ`. -/
theorem IsMatrixMBUGStep.local_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B γ εf εs t₀ t₁ : ℝ}
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r' ℝ} {V₀ : Matrix n r' ℝ} {UF : Matrix m f ℝ}
    {SF : Matrix f f' ℝ} {VF : Matrix n f' ℝ} {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ}
    {Sh : Matrix p q ℝ} {Y₁ : Matrix m n ℝ}
    (hs : IsMatrixMBUGStep F εf εs t₀ t₁ U₀ S₀ V₀ UF SF VF Uh Vh Sh Y₁)
    (hF : IsLipschitzTX F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hγ : γ < 1)
    (h01 : t₀ ≤ t₁) (hhL : (t₁ - t₀) * L ≤ γ) {X : ℝ → Matrix m n ℝ}
    (hX : ODESolution F X t₀ t₁) (hX0 : X t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖Y₁ - X t₁‖ ≤ max (2 * L * (B + 1)) 1 / (1 - γ) *
      ((t₁ - t₀) ^ 2 + (t₁ - t₀) * εf + εs) := by
  have hstep := hs.isMBUGStep
  rw [← hX0] at hstep
  have hεf : 0 ≤ εf := (norm_nonneg _).trans hs.truncF
  have hεs : 0 ≤ εs := (norm_nonneg _).trans hs.trunc
  have hh : 0 ≤ t₁ - t₀ := by linarith
  have hγ0 : 0 ≤ γ := (mul_nonneg hh hL).trans hhL
  have h1 := mbug_step_error (h := t₁ - t₀) hF hL hB hγ (by ring) hh le_rfl hhL hX hstep
  rw [sub_self, norm_zero, mul_zero, zero_add] at h1
  have h2 := stage1_bound_le (P := 1) (L := L) (B := B) hγ0 hγ hh hεf hεs
  simp only [Finset.sum_range_one, pow_zero, one_mul] at h2
  rw [norm_sub_rev]
  calc ‖X t₁ - Y₁‖ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := by ring

omit [DecidableEq p] [DecidableEq q] in
/-- The corrected S-step (eq. (11) of arXiv 2412.09400),
`Ŝ = Ûᵀ Y V̂ + Δ Ûᵀ F(t₁, Û Ŝ V̂ᵀ) V̂ + Ûᵀ R V̂`, is the abstract step
`X̂ = Π (Y + Δ F(t₁, X̂) + R)` of `IsCorrectionSweep` for `X̂ = Û Ŝ V̂ᵀ` and
`Π = leftProj Û * rightProj V̂` (an orthogonal projector by `isOrthProj_leftProj_mul_rightProj`,
fixing `Y`, `R`, `F^{(k)}_{m+1}` in factored form by `galerkinProj_fix`). -/
lemma matrix_correction_sstep_eq {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Uh : Matrix m p ℝ}
    {Vh : Matrix n q ℝ} {Sh : Matrix p q ℝ} {Y R : Matrix m n ℝ} {Δ t₁ : ℝ}
    (hS : Sh = Uhᵀ * Y * Vh + Δ • (Uhᵀ * F t₁ (Uh * Sh * Vhᵀ) * Vh) + Uhᵀ * R * Vh) :
    Uh * Sh * Vhᵀ = (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
      (Y + Δ • F t₁ (Uh * Sh * Vhᵀ) + R) := by
  have h := matrix_sstep_eq (F := F) (Z := Y + R) (Δ := Δ) (t₁ := t₁) (Uh := Uh) (Vh := Vh)
    (Sh := Sh) (by rw [Matrix.mul_add, Matrix.add_mul]; exact hS.trans (by abel))
  exact h.trans (congrArg _ (by abel))

end MatrixStep

/-! ### §2.1: hard and soft thresholding -/

section Truncation

open scoped LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- Hard thresholding `H_α` of a real number (arXiv 2412.09400, §2.1):
`x` if `|x| > α`, `0` if `-α ≤ x ≤ α`. -/
noncomputable def hardThr (α x : ℝ) : ℝ := if α < x then x else if x < -α then x else 0

/-- Soft thresholding `S_α(x) = sgn(x) max(|x| - α, 0)` (arXiv 2412.09400, §2.1). -/
noncomputable def softThr (α x : ℝ) : ℝ := if α < x then x - α else if x < -α then x + α else 0

/-- The matrix `U diag(d) Vᵀ`. -/
noncomputable def svdMat (U : Matrix m r ℝ) (d : r → ℝ) (V : Matrix n r ℝ) : Matrix m n ℝ :=
  U * Matrix.diagonal d * Vᵀ

/-- Hard thresholding of `X = U diag(σ) Vᵀ`: `H_α(X) = U diag(H_α(σ_j)) Vᵀ`. -/
noncomputable def hardThreshold (U : Matrix m r ℝ) (σ : r → ℝ) (V : Matrix n r ℝ) (α : ℝ) :
    Matrix m n ℝ :=
  svdMat U (fun j => hardThr α (σ j)) V

/-- Soft thresholding of `X = U diag(σ) Vᵀ`: `S_α(X) = U diag(S_α(σ_j)) Vᵀ`. -/
noncomputable def softThreshold (U : Matrix m r ℝ) (σ : r → ℝ) (V : Matrix n r ℝ) (α : ℝ) :
    Matrix m n ℝ :=
  svdMat U (fun j => softThr α (σ j)) V

/-- `Δ^h(β) = ∑_{σ_j ≤ β} σ_j²` (for singular values `σ_j ≥ 0`; `|σ_j|` in general). -/
noncomputable def hardLoss (σ : r → ℝ) (β : ℝ) : ℝ := ∑ j, if |σ j| ≤ β then σ j ^ 2 else 0

/-- `Δ^s(β) = ∑_{σ_j ≤ β} σ_j² + ∑_{σ_j > β} β²`. -/
noncomputable def softLoss (σ : r → ℝ) (β : ℝ) : ℝ := ∑ j, if |σ j| ≤ β then σ j ^ 2 else β ^ 2

/-- `‖U diag(d) Vᵀ‖_F² = ∑_j d_j²` for orthonormal columns (arXiv 2412.09400, §2.1). -/
lemma sq_norm_svdMat {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (d : r → ℝ) : ‖svdMat U d V‖ ^ 2 = ∑ j, d j ^ 2 := by
  rw [svdMat, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hU, Frobenius.norm_sq_eq_sum]
  simp [Matrix.diagonal_apply, ite_pow]

omit [Fintype m] [Fintype n] in
/-- `U diag(d) Vᵀ - U diag(d') Vᵀ = U diag(d - d') Vᵀ`. -/
lemma svdMat_sub (U : Matrix m r ℝ) (d d' : r → ℝ) (V : Matrix n r ℝ) :
    svdMat U d V - svdMat U d' V = svdMat U (d - d') V := by
  rw [svdMat, svdMat, svdMat, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

/-- `(x - H_α(x))² = x²` if `|x| ≤ α`, else `0` (arXiv 2412.09400, §2.1). -/
lemma sub_hardThr_sq (α x : ℝ) : (x - hardThr α x) ^ 2 = if |x| ≤ α then x ^ 2 else 0 := by
  unfold hardThr
  by_cases h1 : α < x
  · have : ¬ |x| ≤ α := fun h => by linarith [le_abs_self x]
    simp [h1, this]
  · by_cases h2 : x < -α
    · have : ¬ |x| ≤ α := fun h => by linarith [neg_abs_le x]
      simp [h1, h2, this]
    · have : |x| ≤ α := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [h1, h2, this]

/-- `(x - S_α(x))² = min(|x|, α)²` (arXiv 2412.09400, §2.1). -/
lemma sub_softThr_sq (α x : ℝ) : (x - softThr α x) ^ 2 = if |x| ≤ α then x ^ 2 else α ^ 2 := by
  unfold softThr
  by_cases h1 : α < x
  · have : ¬ |x| ≤ α := fun h => by linarith [le_abs_self x]
    simp [h1, this]
  · by_cases h2 : x < -α
    · have : ¬ |x| ≤ α := fun h => by linarith [neg_abs_le x]
      simp [h1, h2, this]
    · have : |x| ≤ α := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [h1, h2, this]

/-- **Error of hard thresholding** (arXiv 2412.09400, §2.1): `‖X - H_α(X)‖_F² = Δ^h(α)`. -/
theorem sq_norm_sub_hardThreshold {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (σ : r → ℝ) (α : ℝ) :
    ‖svdMat U σ V - hardThreshold U σ V α‖ ^ 2 = hardLoss σ α := by
  rw [hardThreshold, svdMat_sub, sq_norm_svdMat hU hV]
  simp only [Pi.sub_apply, sub_hardThr_sq, hardLoss]

/-- **Error of soft thresholding** (arXiv 2412.09400, §2.1): `‖X - S_α(X)‖_F² = Δ^s(α)`. -/
theorem sq_norm_sub_softThreshold {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (σ : r → ℝ) (α : ℝ) :
    ‖svdMat U σ V - softThreshold U σ V α‖ ^ 2 = softLoss σ α := by
  rw [softThreshold, svdMat_sub, sq_norm_svdMat hU hV]
  simp only [Pi.sub_apply, sub_softThr_sq, softLoss]

omit [Fintype m] in
/-- Thresholding the diagonal by a map fixing `0` does not increase the rank:
`U diag(f(σ_j)) Vᵀ = X (V diag(f(σ_j)/σ_j) Vᵀ)`. -/
lemma rank_svdMat_comp_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hV : Vᵀ * V = 1) (σ : r → ℝ)
    {g : ℝ → ℝ} (hg : g 0 = 0) : (svdMat U (fun j => g (σ j)) V).rank ≤ (svdMat U σ V).rank := by
  set c : r → ℝ := fun j => if σ j = 0 then 0 else g (σ j) / σ j with hc
  have hfac : svdMat U (fun j => g (σ j)) V = svdMat U σ V * (V * Matrix.diagonal c * Vᵀ) := by
    have e : svdMat U σ V * (V * Matrix.diagonal c * Vᵀ) =
        U * (Matrix.diagonal σ * (Vᵀ * V) * Matrix.diagonal c) * Vᵀ := by
      simp only [svdMat, Matrix.mul_assoc]
    rw [e, hV, Matrix.mul_one, Matrix.diagonal_mul_diagonal, svdMat]
    congr 2
    congr 1
    funext j
    by_cases h : σ j = 0
    · simp [hc, h, hg]
    · simp only [hc, h, ↓reduceIte]
      field_simp
  rw [hfac]
  exact Matrix.rank_mul_le_left _ _

omit [Fintype m] in
/-- **Rank of hard thresholding** (arXiv 2412.09400, §2.1): `rank H_α(X) ≤ rank X`. -/
theorem rank_hardThreshold_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hV : Vᵀ * V = 1)
    (σ : r → ℝ) (α : ℝ) : (hardThreshold U σ V α).rank ≤ (svdMat U σ V).rank :=
  rank_svdMat_comp_le hV σ (g := hardThr α) (by simp [hardThr])

omit [Fintype m] in
/-- **Rank of soft thresholding** (arXiv 2412.09400, §2.1): `rank S_α(X) ≤ rank X` for `α ≥ 0`. -/
theorem rank_softThreshold_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hV : Vᵀ * V = 1)
    (σ : r → ℝ) {α : ℝ} (hα : 0 ≤ α) : (softThreshold U σ V α).rank ≤ (svdMat U σ V).rank :=
  rank_svdMat_comp_le hV σ (g := softThr α) (by
    have h1 : ¬ α < 0 := not_lt.mpr hα
    have h2 : ¬ (0 : ℝ) < -α := by linarith
    simp [softThr, h1, h2])

/-- **The truncation `T^h_ε`** (arXiv 2412.09400, §2.1): for every admissible threshold, i.e.
`α` with `Δ^h(α) ≤ ε²`, `‖X - H_α(X)‖_F ≤ ε` (and `rank H_α(X) ≤ rank X` by
`rank_hardThreshold_le`). -/
theorem norm_sub_hardThreshold_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (σ : r → ℝ) {α ε : ℝ} (hε : 0 ≤ ε) (hα : hardLoss σ α ≤ ε ^ 2) :
    ‖svdMat U σ V - hardThreshold U σ V α‖ ≤ ε := by
  rw [← sq_norm_sub_hardThreshold hU hV] at hα
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).mp hα

/-- **The truncation `T^s_ε`** (arXiv 2412.09400, §2.1): for every admissible threshold, i.e.
`α` with `Δ^s(α) ≤ ε²`, `‖X - S_α(X)‖_F ≤ ε` (and `rank S_α(X) ≤ rank X` for `α ≥ 0` by
`rank_softThreshold_le`). -/
theorem norm_sub_softThreshold_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (σ : r → ℝ) {α ε : ℝ} (hε : 0 ≤ ε) (hα : softLoss σ α ≤ ε ^ 2) :
    ‖svdMat U σ V - softThreshold U σ V α‖ ≤ ε := by
  rw [← sq_norm_sub_softThreshold hU hV] at hα
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).mp hα

/-- **The hard-threshold "argmax" of arXiv 2412.09400, §2.1 need not exist, and its supremum
violates the tolerance.**  For `X = diag(2, 1)` (`U = V = 1`, `σ = (2, 1)`) and `ε = 1/2`, the
admissible set `{β > 0 | Δ^h(β) ≤ ε²}` is `(0, 1)`: it has no greatest element, its supremum is
`α = 1`, and `‖X - H_1(X)‖_F = 1 > ε`.  So `T^h_ε` must be read as `H_α` for some admissible `α`
(`norm_sub_hardThreshold_le`), e.g. any `α` in `[σ_{r+1}, σ_r)`. -/
theorem hardThreshold_argmax_counterexample :
    (¬ ∃ α, IsGreatest {β : ℝ | 0 < β ∧ hardLoss ![(2 : ℝ), 1] β ≤ (1 / 2) ^ 2} α) ∧
    sSup {β : ℝ | 0 < β ∧ hardLoss ![(2 : ℝ), 1] β ≤ (1 / 2) ^ 2} = 1 ∧
    (1 / 2 : ℝ) < ‖svdMat (1 : Matrix (Fin 2) (Fin 2) ℝ) ![2, 1] 1 -
      hardThreshold (1 : Matrix (Fin 2) (Fin 2) ℝ) ![2, 1] (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (sSup {β : ℝ | 0 < β ∧ hardLoss ![(2 : ℝ), 1] β ≤ (1 / 2) ^ 2})‖ := by
  have hloss : ∀ β : ℝ, hardLoss ![(2 : ℝ), 1] β =
      (if 2 ≤ β then 4 else 0) + (if 1 ≤ β then 1 else 0) := by
    intro β
    simp only [hardLoss, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hS : {β : ℝ | 0 < β ∧ hardLoss ![(2 : ℝ), 1] β ≤ (1 / 2) ^ 2} = Set.Ioo 0 1 := by
    ext β
    constructor
    · rintro ⟨h0, h1⟩
      rw [hloss] at h1
      refine ⟨h0, lt_of_not_ge fun hb => ?_⟩
      have : (2 : ℝ) ≤ β ∨ ¬ (2 : ℝ) ≤ β := em _
      rcases this with h2 | h2 <;> simp [h2, hb] at h1 <;> norm_num at h1
    · rintro ⟨h0, h1⟩
      have h2 : ¬ (2 : ℝ) ≤ β := by linarith
      have h3 : ¬ (1 : ℝ) ≤ β := by linarith
      refine ⟨h0, ?_⟩
      rw [hloss]
      simp [h2, h3]
  rw [hS, csSup_Ioo zero_lt_one]
  refine ⟨?_, rfl, ?_⟩
  · rintro ⟨α, hα, hmax⟩
    have hmid : (α + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
    have := hmax hmid
    linarith [hα.2]
  · have h := sq_norm_sub_hardThreshold (U := (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (V := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) (by simp) ![2, 1] 1
    have hv : hardLoss ![(2 : ℝ), 1] 1 = 1 := by rw [hloss]; norm_num
    rw [hv] at h
    have h1 : ‖svdMat (1 : Matrix (Fin 2) (Fin 2) ℝ) ![2, 1] (1 : Matrix (Fin 2) (Fin 2) ℝ) -
        hardThreshold (1 : Matrix (Fin 2) (Fin 2) ℝ) ![2, 1] (1 : Matrix (Fin 2) (Fin 2) ℝ) 1‖
          = 1 :=
      (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (h.trans (one_pow 2).symm)
    rw [h1]; norm_num

omit [DecidableEq r] in
/-- `Δ^s(β) = ∑_j min(|σ_j|, β)²`. -/
lemma softLoss_eq (σ : r → ℝ) (β : ℝ) : softLoss σ β = ∑ j, (min |σ j| β) ^ 2 := by
  unfold softLoss
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [min_eq_left h, sq_abs]
  · rw [min_eq_right (le_of_lt (not_le.mp h))]

omit [DecidableEq r] in
/-- **The soft-threshold argmax of arXiv 2412.09400, §2.1 exists** when `0 < ε` and
`ε² < ∑_j σ_j² = ‖X‖_F²`: the admissible set `{β > 0 | Δ^s(β) ≤ ε²}` has a greatest element
(`Δ^s` is continuous), so `T^s_ε` is well defined; by `norm_sub_softThreshold_le` and
`rank_softThreshold_le` it satisfies `‖X - T^s_ε(X)‖_F ≤ ε` and `rank T^s_ε(X) ≤ rank X`.
(For `‖X‖_F ≤ ε` the admissible set is unbounded and the natural value is `T^s_ε(X) = 0`.) -/
theorem softThreshold_argmax_exists (σ : r → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hX : ε ^ 2 < ∑ j, σ j ^ 2) :
    ∃ α, IsGreatest {β : ℝ | 0 < β ∧ softLoss σ β ≤ ε ^ 2} α := by
  set S := {β : ℝ | 0 < β ∧ softLoss σ β ≤ ε ^ 2} with hSdef
  set f : ℝ → ℝ := fun β => ∑ j, (min |σ j| β) ^ 2 with hfdef
  have hf : Continuous f := by
    rw [hfdef]
    fun_prop
  have hSf : ∀ β, softLoss σ β = f β := fun β => softLoss_eq σ β
  set B0 := ∑ j, |σ j| with hB0def
  have hB0 : ∀ β ∈ S, β ≤ B0 := by
    rintro β ⟨_, hle⟩
    by_contra hlt'
    have hlt : B0 < β := lt_of_not_ge hlt'
    have : f β = ∑ j, σ j ^ 2 := Finset.sum_congr rfl fun j _ => by
      rw [min_eq_left ((Finset.single_le_sum (fun i _ => abs_nonneg (σ i))
        (Finset.mem_univ j)).trans hlt.le), sq_abs]
    rw [hSf, this] at hle
    linarith
  set c : ℝ := (Fintype.card r : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  set β₀ := ε / (c + 1) with hβ₀def
  have hβ₀ : 0 < β₀ := by positivity
  have hβ₀S : β₀ ∈ S := by
    refine ⟨hβ₀, ?_⟩
    rw [hSf]
    have h1 : (c + 1) * β₀ = ε := by rw [hβ₀def]; field_simp
    calc f β₀ ≤ ∑ _j : r, β₀ ^ 2 := Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (le_min (abs_nonneg _) hβ₀.le) (min_le_right _ _) 2
      _ = c * β₀ ^ 2 := by simp [hc]
      _ ≤ ε ^ 2 := by
        rw [← h1]
        nlinarith [sq_nonneg β₀, mul_nonneg hc0 (sq_nonneg β₀),
          mul_nonneg (mul_nonneg hc0 hc0) (sq_nonneg β₀)]
  have hbdd : BddAbove S := ⟨B0, hB0⟩
  have hne : S.Nonempty := ⟨β₀, hβ₀S⟩
  refine ⟨sSup S, ⟨hβ₀.trans_le (le_csSup hbdd hβ₀S), ?_⟩, fun β hβ => le_csSup hbdd hβ⟩
  rw [hSf]
  have hcl : IsClosed {β : ℝ | f β ≤ ε ^ 2} := isClosed_le hf continuous_const
  have hsub : S ⊆ {β : ℝ | f β ≤ ε ^ 2} := fun β hβ => by
    have := hβ.2
    rw [hSf] at this
    exact this
  exact hcl.closure_subset_iff.mpr hsub (csSup_mem_closure hne hbdd)

/-! #### Soft thresholding is non-expansive -/

omit [Fintype m] [Fintype n] in
/-- `⟪W, U diag(d) Vᵀ⟫_F = ∑_j d_j (Uᵀ W V)_{jj}`. -/
lemma inner_svdMat (W : Matrix m n ℝ) (U : Matrix m r ℝ) (d : r → ℝ) (V : Matrix n r ℝ)
    [Fintype m] [Fintype n] : ⟪W, svdMat U d V⟫ = ∑ j, d j * (Uᵀ * W * V) j j := by
  rw [Frobenius.inner_eq_trace, svdMat]
  have h1 : Wᵀ * (U * Matrix.diagonal d * Vᵀ) = (Wᵀ * U * Matrix.diagonal d) * Vᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Vᵀ * (Wᵀ * U * Matrix.diagonal d) = (Uᵀ * W * V)ᵀ * Matrix.diagonal d := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h2, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.transpose_apply, mul_comm]

omit [Fintype m] [DecidableEq r] in
/-- Multiplication by a diagonal matrix with entries in `[-1, 1]` does not increase the
Frobenius norm. -/
lemma norm_diagonal_mul_le {k : Type*} [Fintype k] [DecidableEq r] {g : r → ℝ}
    (hg : ∀ j, |g j| ≤ 1) (M : Matrix r k ℝ) : ‖Matrix.diagonal g * M‖ ≤ ‖M‖ := by
  have h : ‖Matrix.diagonal g * M‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => ?_
    rw [Matrix.diagonal_mul, mul_pow]
    have : g i ^ 2 ≤ 1 := by
      have := hg i
      nlinarith [abs_nonneg (g i), sq_abs (g i)]
    nlinarith [sq_nonneg (M i l)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit [Fintype m] in
/-- The unit column `e_j` as an `r × 1` matrix. -/
lemma norm_unitCol (j : r) :
    ‖(Matrix.of fun i (_ : Fin 1) => if i = j then (1 : ℝ) else 0)‖ = 1 := by
  have h : ‖(Matrix.of fun i (_ : Fin 1) => if i = j then (1 : ℝ) else 0)‖ ^ 2 = 1 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [ite_pow]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (h.trans (one_pow 2).symm)

omit [Fintype r] in
/-- For `G = U₁ diag(g) V₁ᵀ` with `|g_i| ≤ 1` and `U, V` with orthonormal columns,
`|(Uᵀ G V)_{jj}| ≤ 1`. -/
lemma abs_diag_le_one [Finite r] {r₁ : Type*} [Fintype r₁] [DecidableEq r₁] {U₁ : Matrix m r₁ ℝ}
    {V₁ : Matrix n r₁ ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) {g : r₁ → ℝ}
    (hg : ∀ j, |g j| ≤ 1) {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (j : r) : |(Uᵀ * svdMat U₁ g V₁ * V) j j| ≤ 1 := by
  have := Fintype.ofFinite r
  set e : Matrix r (Fin 1) ℝ := Matrix.of fun i (_ : Fin 1) => if i = j then (1 : ℝ) else 0
    with he
  have hentry : (Uᵀ * svdMat U₁ g V₁ * V) j j = ⟪U * e, svdMat U₁ g V₁ * (V * e)⟫ := by
    rw [Frobenius.inner_eq_trace, Matrix.trace, Fin.sum_univ_one, Matrix.diag_apply]
    have : (U * e)ᵀ * (svdMat U₁ g V₁ * (V * e)) = eᵀ * (Uᵀ * svdMat U₁ g V₁ * V) * e := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this]
    simp [he, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hentry]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 : ‖U * e‖ = 1 := by rw [Frobenius.norm_mul_of_orthonormal hU, he, norm_unitCol]
  have h2 : ‖svdMat U₁ g V₁ * (V * e)‖ ≤ 1 := by
    have e1 : svdMat U₁ g V₁ * (V * e) = U₁ * (Matrix.diagonal g * (V₁ᵀ * (V * e))) := by
      simp only [svdMat, Matrix.mul_assoc]
    rw [e1, Frobenius.norm_mul_of_orthonormal hU₁]
    refine (norm_diagonal_mul_le hg _).trans ((norm_transpose_mul_le hV₁ _).trans ?_)
    rw [Frobenius.norm_mul_of_orthonormal hV, he, norm_unitCol]
  rw [h1, one_mul]
  exact h2

/-- `⟪U₁ diag(g) V₁ᵀ, U₂ diag(s) V₂ᵀ⟫ ≤ ∑_j s_j` for `|g| ≤ 1`, `s ≥ 0` (the dual pairing of the
spectral and the nuclear norm). -/
lemma inner_svdMat_le {r₁ : Type*} [Fintype r₁] [DecidableEq r₁] {U₁ : Matrix m r₁ ℝ}
    {V₁ : Matrix n r₁ ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1) {g : r₁ → ℝ}
    (hg : ∀ j, |g j| ≤ 1) {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {s : r → ℝ} (hs : ∀ j, 0 ≤ s j) :
    ⟪svdMat U₁ g V₁, svdMat U s V⟫ ≤ ∑ j, s j := by
  rw [inner_svdMat]
  refine Finset.sum_le_sum fun j _ => ?_
  have := abs_diag_le_one hU₁ hV₁ hg hU hV j
  calc s j * (Uᵀ * svdMat U₁ g V₁ * V) j j ≤ s j * 1 :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans this) (hs j)
    _ = s j := mul_one _

/-- The dual coefficient `min(1, x/α)` of soft thresholding: `x - S_α(x) = α · softDual α x`
for `x ≥ 0`. -/
noncomputable def softDual (α x : ℝ) : ℝ := if α < x then 1 else x / α

/-- For `x ≥ 0`, `S_α(x) = max(x - α, 0)`. -/
lemma softThr_of_nonneg {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    softThr α x = if α < x then x - α else 0 := by
  have : ¬ x < -α := by linarith
  simp [softThr, this]

/-- `|min(1, x/α)| ≤ 1` for `x ≥ 0`, `α > 0`. -/
lemma abs_softDual_le {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) : |softDual α x| ≤ 1 := by
  unfold softDual
  split_ifs with h
  · simp
  · rw [abs_of_nonneg (div_nonneg hx hα.le), div_le_one hα]; linarith

/-- `S_α(x) ≥ 0` for `x ≥ 0`, `α > 0`. -/
lemma softThr_nonneg {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) : 0 ≤ softThr α x := by
  rw [softThr_of_nonneg hα hx]
  split_ifs with h <;> linarith

/-- `x - S_α(x) = α min(1, x/α)` for `x ≥ 0` (optimality relation of the prox). -/
lemma sub_softThr_eq {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    x - softThr α x = α * softDual α x := by
  rw [softThr_of_nonneg hα hx]
  unfold softDual
  split_ifs with h
  · ring
  · field_simp
    ring

/-- `min(1, x/α) S_α(x) = S_α(x)` for `x ≥ 0`. -/
lemma softDual_mul_softThr {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    softDual α x * softThr α x = softThr α x := by
  rw [softThr_of_nonneg hα hx]
  unfold softDual
  split_ifs with h <;> simp

omit [Fintype m] [Fintype n] in
/-- `X - S_α(X) = α U diag(softDual α σ) Vᵀ` for `σ ≥ 0`. -/
lemma svdMat_sub_softThreshold {U : Matrix m r ℝ} {V : Matrix n r ℝ} {σ : r → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) {α : ℝ} (hα : 0 < α) :
    svdMat U σ V - softThreshold U σ V α = α • svdMat U (fun j => softDual α (σ j)) V := by
  have hd : Matrix.diagonal (σ - fun j => softThr α (σ j)) =
      α • Matrix.diagonal (fun j => softDual α (σ j)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact sub_softThr_eq hα (hσ j)
  rw [softThreshold, svdMat_sub, svdMat, svdMat, hd, Matrix.mul_smul, Matrix.smul_mul]

/-- `⟪U diag(softDual α σ) Vᵀ, S_α(X)⟫ = ∑_j S_α(σ_j)` for `σ ≥ 0`. -/
lemma inner_softDual_softThreshold {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {σ : r → ℝ} (hσ : ∀ j, 0 ≤ σ j) {α : ℝ} (hα : 0 < α) :
    ⟪svdMat U (fun j => softDual α (σ j)) V, softThreshold U σ V α⟫ =
      ∑ j, softThr α (σ j) := by
  rw [softThreshold, inner_svdMat]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdiag : Uᵀ * svdMat U (fun j => softDual α (σ j)) V * V =
      Matrix.diagonal fun j => softDual α (σ j) := by
    simp only [svdMat, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, hV, Matrix.mul_one]
  rw [hdiag, Matrix.diagonal_apply_eq, mul_comm, softDual_mul_softThr hα (hσ j)]

/-- **Soft thresholding is non-expansive** (arXiv 2412.09400, §2.1, where it is the proximal map
of `α ‖·‖_*`): for `α > 0` and singular value decompositions `X₁ = U₁ diag(σ₁) V₁ᵀ`,
`X₂ = U₂ diag(σ₂) V₂ᵀ` (`σ ≥ 0`, orthonormal columns),
`‖S_α(X₁) - S_α(X₂)‖_F ≤ ‖X₁ - X₂‖_F`.  The proof is the firm non-expansiveness of a proximal
map: `X_i - S_α(X_i) = α G_i` with `G_i = U_i diag(min(1, σ_i/α)) V_iᵀ`, and
`⟪G_i, S_α(X_k)⟫ ≤ ⟪G_k, S_α(X_k)⟫` (`inner_svdMat_le`). -/
theorem softThreshold_nonexpansive {r₁ : Type*} [Fintype r₁] [DecidableEq r₁]
    {U₁ : Matrix m r₁ ℝ} {V₁ : Matrix n r₁ ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₁ : V₁ᵀ * V₁ = 1)
    {σ₁ : r₁ → ℝ} (hσ₁ : ∀ j, 0 ≤ σ₁ j) {U₂ : Matrix m r ℝ} {V₂ : Matrix n r ℝ}
    (hU₂ : U₂ᵀ * U₂ = 1) (hV₂ : V₂ᵀ * V₂ = 1) {σ₂ : r → ℝ} (hσ₂ : ∀ j, 0 ≤ σ₂ j) {α : ℝ}
    (hα : 0 < α) :
    ‖softThreshold U₁ σ₁ V₁ α - softThreshold U₂ σ₂ V₂ α‖ ≤
      ‖svdMat U₁ σ₁ V₁ - svdMat U₂ σ₂ V₂‖ := by
  set Z₁ := softThreshold U₁ σ₁ V₁ α with hZ₁
  set Z₂ := softThreshold U₂ σ₂ V₂ α with hZ₂
  set G₁ := svdMat U₁ (fun j => softDual α (σ₁ j)) V₁ with hG₁
  set G₂ := svdMat U₂ (fun j => softDual α (σ₂ j)) V₂ with hG₂
  have h11 : ⟪G₁, Z₁⟫ = ∑ j, softThr α (σ₁ j) := inner_softDual_softThreshold hU₁ hV₁ hσ₁ hα
  have h22 : ⟪G₂, Z₂⟫ = ∑ j, softThr α (σ₂ j) := inner_softDual_softThreshold hU₂ hV₂ hσ₂ hα
  have h12 : ⟪G₁, Z₂⟫ ≤ ∑ j, softThr α (σ₂ j) :=
    inner_svdMat_le hU₁ hV₁ (fun j => abs_softDual_le hα (hσ₁ j)) hU₂ hV₂
      (fun j => softThr_nonneg hα (hσ₂ j))
  have h21 : ⟪G₂, Z₁⟫ ≤ ∑ j, softThr α (σ₁ j) :=
    inner_svdMat_le hU₂ hV₂ (fun j => abs_softDual_le hα (hσ₂ j)) hU₁ hV₁
      (fun j => softThr_nonneg hα (hσ₁ j))
  set D := Z₁ - Z₂ with hD
  set Δ := svdMat U₁ σ₁ V₁ - svdMat U₂ σ₂ V₂ with hΔ
  have hΔD : Δ - D = α • (G₁ - G₂) := by
    rw [smul_sub, hG₁, hG₂, ← svdMat_sub_softThreshold hσ₁ hα, ← svdMat_sub_softThreshold hσ₂ hα,
      hΔ, hD, hZ₁, hZ₂]
    abel
  have hmono : 0 ≤ ⟪Δ - D, D⟫ := by
    rw [hΔD, real_inner_smul_left, hD, inner_sub_left, inner_sub_right, inner_sub_right]
    have : 0 ≤ ⟪G₁, Z₁⟫ - ⟪G₁, Z₂⟫ - (⟪G₂, Z₁⟫ - ⟪G₂, Z₂⟫) := by
      rw [h11, h22]; linarith
    exact mul_nonneg hα.le this
  have hDD : ‖D‖ ^ 2 ≤ ‖Δ‖ * ‖D‖ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hmono
    linarith [real_inner_le_norm Δ D]
  rcases (norm_nonneg D).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Truncation

/-! ### The hypotheses are satisfiable -/

/-- Non-vacuity of `sdc_mbug_local_error`: for `F = 0` on `ℝ`, nodes `t_s = s/2` (`P = K = 1`),
zero weights and zero iterates, every hypothesis holds, with `L = 1`, `B = 0`, `γ = 1/2`,
`Λ = C_A = 0` and `Π = 1`. -/
example : let F : ℝ → ℝ → ℝ := fun _ _ => 0
    let t : ℕ → ℝ := fun s => s / 2
    IsLipschitzTX F 1 ∧ IsBoundedField F 0 ∧ MonotoneOn t (Set.Iic 1) ∧
      (t 1 - t 0) * 1 ≤ 1 / 2 ∧ ODESolution F (fun _ => 0) (t 0) (t 1) ∧
      (∀ m < 1, ‖(0 : ℝ) - 0 - (t (m + 1) - t m) •
        quadSum (fun _ _ => 0) 1 m (fun s => F (t s) 0)‖ ≤ 0 * (t 1 - t 0) ^ (1 + 2)) ∧
      (∀ m < 1, IsMBUGStep F 0 0 (t m) (t (m + 1)) 0 0) ∧
      IsCorrectionSweep F t (fun _ _ => 0) 1 0 0 0 (fun _ => 0) (fun _ => 0) := by
  intro F t
  refine ⟨fun s t' Y Z => by simp only [F, sub_self, norm_zero]; positivity,
    fun _ _ => by simp [F], ?_, by norm_num [t], ?_, fun m _ => by simp [F, quadSum],
    fun m _ => ⟨1, 0, 0, IsOrthProj.one, by simp [F], rfl, rfl, by simp [F], by simp⟩,
    ⟨fun _ => 0, fun _ _ => by simp [F],
      fun m _ => ⟨1, 0, 0, IsOrthProj.one, by simp [quadSum], rfl, rfl, rfl, by simp [F],
        by simp⟩⟩⟩
  · intro a _ b _ hab
    simp only [t]
    gcongr
  · exact { cont := continuousOn_const, deriv := fun τ _ => hasDerivWithinAt_const τ _ 0 }

end LeanDLRA.Literature.P2412_09400
