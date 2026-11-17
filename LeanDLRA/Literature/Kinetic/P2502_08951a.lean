import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2502.08951: Asymptotic-preserving DLR for the stiff nonlinear Boltzmann equation

This module formalizes the integrators and the two theorems of Einkemmer, Hu and Zhang.  It proves
the exactness of the XL integrator on matrices (Theorem 2.2) and shows that it is false as printed;
the reduction of explicit-Euler XL to the sXL integrator for separable fields; the identities and
the contraction estimate behind the asymptotic-preserving property of the penalized splitting (4.3);
and Theorem 5.1 for the concrete low-rank scheme of Section 5: real velocity integrals, the real
Maxwellian (5.2), Hermite functions, and all of Steps 1–6 with their QR decompositions and the SVD.

## Main results

* `theorem_2_2`: exactness of XL for `F(t, Y) = Ȧ(t)`, including the truncation step.
* `Counterexample.theorem_2_2_false_for_state_dependent_field`: **Theorem 2.2 is false as
  printed**, for the general equation (2.1): an affine field `F(t, Y)`, an exact rank-one solution,
  an XL step whose result is not `A(1)`.
* `euler_lstep`, `sxl_step`, `sxl_capture_iff`: Section 2, (2.6)–(2.11).  The robust error bounds of
  sXL are `sxl_local_error`, `sxl_global_error` in `Integrators/EulerBUG`.
* `PenalizedSetting.IsPenalizedBGKStep.mom_eq`, `.mom_update`, `.eq_4_6`, `.eq_4_8`, `.abs_dev_le`,
  `PenalizedSetting.tendsto_collision`, `.abs_dev_le_pow`, `.exists_first_order`:
  (4.4)–(4.12); `bgk_condition_iff`, `bgk_step`, `bgk_moment_update`: the BGK case and (4.14).
* `hermite_recurrence`, `vIP_hermiteP`: the Hermite basis, (5.13).
* `theorem_5_1`, `theorem_5_1_rate`: Theorem 5.1.  The steps of its proof are
  `StepData.IsLowRankBGKStep.ctr_Ks_eq` ((5.15)–(5.26), as an exact identity),
  `StepData.IsKSStep.L₂_mem`, `.L_star_mem`, `.exists_Ss` (the proper QR decomposition),
  `StepData.IsLowRankBGKStep.max_mem` ((5.28), (5.30)), `.ctr_Lh`, `.fhat_sub_max`, `.moment_hat`
  ((5.29)–(5.32), for every `ε ≥ 0`), `.sigma_eq_zero`, `.isEq_next` ((5.33)).
* `exists_stationary_run`: non-vacuity.

## Differences from the paper

* Theorem 2.2 is stated for `(2.1)`, but the proof, like [6, Lemma 1], treats `F(t, Y) = Ȧ(t)`. Here
  this is the hypothesis `IsDerivRHS F A t₀ t₁`, and the counterexample shows that it cannot be
  dropped. Only the end points of `A` enter; `X(t₁)`, `V(t₁)` need not be orthonormal.
* `X̂` has `r + t` columns, `t` arbitrary (`t = r` in Sections 2 and 5, `t = r̃` in (2.9)).
* Section 4 is abstract: `𝒬`, the moments and the transport term are data of `PenalizedSetting`,
  with the conservation properties (1.4), (1.7) as fields of the structure; the Boltzmann operator
  is not defined, and `bgkSetting` is an instance.  The `O(1)` assumption on the brackets of (4.6)
  is the hypothesis `|b| ≤ B`, and `O(Δt)` becomes the explicit `(ε/λ + α Δt) B/(1 - α)`, for every
  `ε ≥ 0`.  (4.7) divides by `f* - ℳ*`, which has zeros since `f*` and `ℳ*` have the same moments;
  `𝒟*` is taken to be any multiplier with `𝒬(f*, f*) = (𝒟* - λ)(f* - ℳ*)` (`IsMultiplier`), and
  (4.9) is `|𝒟*| ≤ α λ`.  So (4.9) contains that `𝒬(f*, f*)` vanishes at these zeros.  (4.12) needs
  a bound of the flux functional, which stands for the formal `∇ₓ O(Δt) = O(Δt)`.
* In Section 5 the velocity variable is concrete: velocity functions are `p(v) e^{-v²/2}`, `p` a
  polynomial (`gaussFn`), the class in which the paper's proof takes place, and `⟨·⟩ᵥ` are Lebesgue
  integrals over `ℝ`.  The `x`-functions form an abstract real inner product space `Ex`, with a
  linear operator `D` for `∂ₓ` and an injective evaluation `ev` on a set `Ω` of points, for
  instance a spatial grid.  The paper does not specify boundary conditions or the regularity of
  `x`-functions.  `ρ* (u*)²` is the field `qs` of `Ex`, characterized pointwise.
* "As `ε → 0`" is read as in the paper's proof, which sets `ε = 0` in (5.8), (5.10): `theorem_5_1`
  is about the limit scheme.  For `ε > 0` the equations are multiplied by `ε Δt`, and one step gives
  `f̂ⁿ⁺¹ - M* = ε/(ε + Δt) (f* - M*)` (`IsLowRankBGKStep.fhat_sub_max`).  A multi-step statement for
  `ε > 0` is not claimed by the paper and is not proved: at `ε > 0` the iterates leave the
  Maxwellians, and the rank `r` does not control the basis in the following steps.
* The paper's "proper QR decomposition" is made explicit: `V*` contains `V₁, V₂, V₃`, and `Vⁿ`
  contains `V₁, …, V₆`.  These are the fields `proper_Vs`, `proper_V`, the latter implies `r ≥ 6`
  (`IsLowRankBGKStep.six_le`), and it holds for the paper's Hermite basis when `r ≥ 6`
  (`hermite_proper`).  An arbitrary QR decomposition is not covered, by the paper either: `M*` then
  need not lie in the span of `V*`.  A run may refactorize `f` at the start of each step (`IsRun`),
  as the paper does.
* (5.7) divides by `ρ*`, so non-vanishing of the density is a hypothesis of each step.  Explicit
  Euler does not preserve it in general.
* `O(Δt)` in (5.12) is an exact formula for the remainder, `theorem_5_1`, and a bound in terms of
  `‖D‖` and the moments of `Mⁿ`, `theorem_5_1_rate`.  The paper's proof gives no constant.

Existence of the QR factors and of an SVD with the required basis of `Vⁿ⁺¹` is standard linear
algebra, and it is not proved here in general.  `IsKSStep.exists_Ss` proves the non-trivial part,
that `L*` lies in the span of `Vⁿ`, and `exists_stationary_run` exhibits a complete run.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2502_08951

/-! ### SVD truncation -/

section Truncation

open Matrix

/-- If `A = U diag(σ) Wᵀ` (`U`, `W` orthogonal, `σ` nonnegative and sorted) and `rank A ≤ k`, then
`σⱼ = 0` for `j ≥ k`. -/
lemma sv_eq_zero_of_rank_le {N : ℕ} {A U W : Matrix (Fin N) (Fin N) ℝ} {σ : Fin N → ℝ}
    (hU : Uᵀ * U = 1) (hW : Wᵀ * W = 1) (hA : A = U * diagonal σ * Wᵀ) (hσ : Antitone σ)
    (hσ0 : ∀ i, 0 ≤ σ i) {k : ℕ} (hk : A.rank ≤ k) (j : Fin N) (hj : k ≤ j) : σ j = 0 := by
  have hW' : W * Wᵀ = 1 := mul_eq_one_comm.mp hW
  have hdiag : diagonal σ = Uᵀ * A * W := by
    rw [hA]
    calc diagonal σ = (Uᵀ * U) * diagonal σ * (Wᵀ * W) := by rw [hU, hW]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hrank : (diagonal σ).rank ≤ k := by
    rw [hdiag]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hk
  rw [Matrix.rank_diagonal] at hrank
  by_contra hne
  have hpos : ∀ i : Fin N, i ≤ j → σ i ≠ 0 := fun i hi =>
    ((lt_of_le_of_ne (hσ0 j) (Ne.symm hne)).trans_le (hσ hi)).ne'
  have hcard : (Finset.Iic j).card ≤ Fintype.card {i // σ i ≠ 0} := by
    rw [Fintype.card_subtype]
    exact Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpos i (Finset.mem_Iic.mp hi)
  rw [Fin.card_Iic] at hcard
  omega

end Truncation

/-! ### The XL integrator (Section 2) -/

section XL

open Matrix
open scoped LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] {r t : ℕ}

/-- One step of the **XL integrator** (arXiv 2502.08951, (2.2)–(2.5) and the truncation step). -/
structure IsXLStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (X₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (K : ℝ → Matrix m (Fin r) ℝ) (Xh : Matrix m (Fin (r + t)) ℝ)
    (Lh : ℝ → Matrix n (Fin (r + t)) ℝ) (Vh : Matrix n (Fin (r + t)) ℝ)
    (Sh Us Ws : Matrix (Fin (r + t)) (Fin (r + t)) ℝ) (σ : Fin (r + t) → ℝ) : Prop where
  /-- (2.2): the X-step. -/
  kstep : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁
  kstep₀ : K t₀ = X₀ * S₀
  /-- (2.3): `X̂ = orth[Xⁿ, K(tⁿ⁺¹)] = [Xⁿ, …]`. -/
  orth_Xh : Xhᵀ * Xh = 1
  Xh_left : ∀ i j, Xh i (Fin.castAdd t j) = X₀ i j
  capture : Xh * Xhᵀ * K t₁ = K t₁
  /-- (2.4): the L-step. -/
  lstep : ODESolution (fun t L => (F t (Xh * Lᵀ))ᵀ * Xh) Lh t₀ t₁
  lstep₀_left : ∀ i j, Lh t₀ i (Fin.castAdd t j) = (V₀ * S₀ᵀ) i j
  lstep₀_right : ∀ i j, Lh t₀ i (Fin.natAdd r j) = 0
  /-- (2.5): `[V̂, Ŝ] = QR(L̂(tⁿ⁺¹))`, i.e. `L̂(tⁿ⁺¹) = V̂ Ŝᵀ`. -/
  orth_Vh : Vhᵀ * Vh = 1
  qr : Lh t₁ = Vh * Shᵀ
  /-- Truncation step: the SVD of `Ŝ`. -/
  orth_Us : Usᵀ * Us = 1
  orth_Ws : Wsᵀ * Ws = 1
  svd : Sh = Us * Matrix.diagonal σ * Wsᵀ
  sorted : Antitone σ
  nonneg : ∀ i, 0 ≤ σ i

/-- The result of the truncation step that retains the first `k` singular values. -/
noncomputable def truncate (Xh : Matrix m (Fin (r + t)) ℝ) (Vh : Matrix n (Fin (r + t)) ℝ)
    (Us Ws : Matrix (Fin (r + t)) (Fin (r + t)) ℝ) (σ : Fin (r + t) → ℝ) (k : ℕ) : Matrix m n ℝ :=
  Xh * Us * Matrix.diagonal (fun j : Fin (r + t) => if (j : ℕ) < k then σ j else 0) * Wsᵀ * Vhᵀ

/-- The embedding of the first `r` columns. -/
def leftEmb (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) ℝ :=
  Matrix.of fun i j => if i = Fin.castAdd t j then 1 else 0

lemma mul_leftEmb {p : Type*} (A : Matrix p (Fin (r + t)) ℝ) :
    A * leftEmb r t = Matrix.of fun i j => A i (Fin.castAdd t j) := by
  ext i j
  simp [Matrix.mul_apply, leftEmb]

/-- `X̂ X̂ᵀ X₀ = X₀` when `X₀` is the block of the first `r` columns of `X̂`. -/
lemma capture_left {X₀ : Matrix m (Fin r) ℝ} {Xh : Matrix m (Fin (r + t)) ℝ}
    (hXh : Xhᵀ * Xh = 1) (hl : ∀ i j, Xh i (Fin.castAdd t j) = X₀ i j) :
    Xh * Xhᵀ * X₀ = X₀ := by
  have h0 : X₀ = Xh * leftEmb r t := by
    rw [mul_leftEmb]
    ext i j
    simp [hl]
  rw [h0, ← Matrix.mul_assoc, Matrix.mul_assoc Xh, hXh, Matrix.mul_one]

/-- **Exactness of the XL integrator** (arXiv 2502.08951, Theorem 2.2), for the right-hand side
`F(t, Y) = Ȧ(t)` that does not depend on `Y`: this is the setting of [6, Lemma 1], on which the
paper's proof rests. The field may *not* depend on `Y`, see
`Counterexample.theorem_2_2_false_for_state_dependent_field`. Only `A(tⁿ) = Xⁿ Sⁿ Vⁿᵀ` and a
factorization `A(tⁿ⁺¹) = X S Vᵀ` with `r` columns and `Vᵀ Vⁿ` invertible are used, not the rank of
`A(t)` between the end points; `X` and `V` need not be orthonormal, and `S` may be singular.
`X̂` has `r + t` columns (`t = r` in the paper); if `k ≥ r` singular values are retained, the result
is `A(tⁿ⁺¹)`. -/
theorem theorem_2_2 {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {X₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : X₀ * S₀ * V₀ᵀ = A t₀)
    {X₁ : Matrix m (Fin r) ℝ} {S₁ : Matrix (Fin r) (Fin r) ℝ} {V₁ : Matrix n (Fin r) ℝ}
    (hA₁ : A t₁ = X₁ * S₁ * V₁ᵀ) (hV : IsUnit (V₁ᵀ * V₀))
    {K : ℝ → Matrix m (Fin r) ℝ} {Xh : Matrix m (Fin (r + t)) ℝ}
    {Lh : ℝ → Matrix n (Fin (r + t)) ℝ} {Vh : Matrix n (Fin (r + t)) ℝ}
    {Sh Us Ws : Matrix (Fin (r + t)) (Fin (r + t)) ℝ} {σ : Fin (r + t) → ℝ}
    (hs : IsXLStep F t₀ t₁ X₀ S₀ V₀ K Xh Lh Vh Sh Us Ws σ) {k : ℕ} (hk : r ≤ k) :
    truncate Xh Vh Us Ws σ k = A t₁ := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eK := Exactness.kStepODE_eq_add hA hs.kstep t₁ h1
  rw [hs.kstep₀] at eK
  have hcapK : Xh * Xhᵀ * (X₀ * S₀ + (A t₁ - A t₀) * V₀) = X₀ * S₀ + (A t₁ - A t₀) * V₀ := by
    rw [← eK]; exact hs.capture
  have hP₁ : Xh * Xhᵀ * A t₁ = A t₁ := Exactness.left_capture hV₀ hY₀ hA₁ hV hcapK
  have hP₀ : Xh * Xhᵀ * A t₀ = A t₀ := by
    rw [← hY₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, capture_left hs.orth_Xh hs.Xh_left]
  have eL := Exactness.lStepODE_eq_add hA hs.lstep t₁ h1
  have hL0 : Lh t₀ = (V₀ * S₀ᵀ) * (leftEmb r t)ᵀ := by
    ext i j
    induction j using Fin.addCases with
    | left j => simp [Matrix.mul_apply, leftEmb, hs.lstep₀_left, Fin.castAdd_inj]
    | right j =>
      have hne : ∀ a : Fin r, Fin.natAdd r j ≠ Fin.castAdd t a := fun a h => by
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [Matrix.mul_apply, leftEmb, hs.lstep₀_right, hne]
  have hY0 : Xh * (Lh t₀)ᵀ = A t₀ := by
    rw [hL0, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, mul_leftEmb,
      Matrix.transpose_mul, Matrix.transpose_transpose, ← hY₀, ← Matrix.mul_assoc]
    congr 2
    ext i j
    simp [hs.Xh_left]
  have hYh : Xh * (Lh t₁)ᵀ = A t₁ := by
    rw [eL, Matrix.transpose_add, Matrix.mul_add, hY0, Matrix.transpose_mul,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_sub, hP₁, hP₀]
    abel
  have hSh : Xh * Sh * Vhᵀ = A t₁ := by
    rw [← hYh, hs.qr, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hShA : Sh = Xhᵀ * A t₁ * Vh := by
    rw [← hSh]
    calc Sh = (Xhᵀ * Xh) * Sh * (Vhᵀ * Vh) := by rw [hs.orth_Xh, hs.orth_Vh]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hrA : (A t₁).rank ≤ r := by
    rw [hA₁]
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    simpa using Matrix.rank_le_card_height V₁ᵀ
  have hrS : Sh.rank ≤ r := by
    rw [hShA]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrA
  have hzero := sv_eq_zero_of_rank_le hs.orth_Us hs.orth_Ws hs.svd hs.sorted hs.nonneg hrS
  have hdiag : (fun j : Fin (r + t) => if (j : ℕ) < k then σ j else 0) = σ := by
    funext j
    split_ifs with h
    · rfl
    · exact (hzero j (by omega)).symm
  rw [truncate, hdiag, ← hSh, hs.svd]
  simp only [Matrix.mul_assoc]


/-! ### Theorem 2.2 is false for a state-dependent field -/

namespace Counterexample

/-- `F(t, Y)`: affine in `Y`, smooth in `t`, and genuinely dependent on `Y`. -/
noncomputable def F (t : ℝ) (Y : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, 1; Y 0 1, 3 / 2 * Y 2 1; 1, 2 * t]

/-- The exact rank-one solution `A(t) = (1, t²/2, t)ᵀ (1, t)`. -/
noncomputable def A (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, t; t ^ 2 / 2, t ^ 3 / 2; t, t ^ 2]

/-- `X⁰ = e₁`. -/
def X₀ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- `S⁰ = 1`. -/
def S₀ : Matrix (Fin 1) (Fin 1) ℝ := 1

/-- `V⁰ = e₁`. -/
def V₀ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The K-step solution `K(t) = (1, 0, t)ᵀ`. -/
noncomputable def K (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; t]

/-- `X̂ = [e₁, e₃]`. -/
def Xh : Matrix (Fin 3) (Fin (1 + 1)) ℝ := !![1, 0; 0, 0; 0, 1]

/-- The L-step solution. -/
noncomputable def Lh (t : ℝ) : Matrix (Fin 2) (Fin (1 + 1)) ℝ := !![1, t; t, t ^ 2]

/-- `√2 / 2`. -/
noncomputable def c : ℝ := √2 / 2

lemma c_sq : c * c = 1 / 2 := by
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [c]
  nlinarith

/-- `V̂`. -/
noncomputable def Vh : Matrix (Fin 2) (Fin (1 + 1)) ℝ := !![c, c; c, -c]

/-- `Ŝ`. -/
noncomputable def Sh : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ := !![2 * c, 0; 2 * c, 0]

/-- The singular values of `Ŝ`. -/
def σ : Fin (1 + 1) → ℝ := ![2, 0]

lemma hasDerivAt_A (t : ℝ) : HasDerivAt A (F t (A t)) t := by
  have h1 := (hasDerivAt_id t).smul_const (!![0, 1; 0, 0; 1, 0] : Matrix (Fin 3) (Fin 2) ℝ)
  have h2 := (hasDerivAt_pow 2 t).smul_const (!![0, 0; 1 / 2, 0; 0, 1] :
    Matrix (Fin 3) (Fin 2) ℝ)
  have h3 := (hasDerivAt_pow 3 t).smul_const (!![0, 0; 0, 1 / 2; 0, 0] :
    Matrix (Fin 3) (Fin 2) ℝ)
  have h := ((h1.const_add (!![1, 0; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)).add h2).add h3
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [F, A] <;> ring

/-- `A` solves `Ȧ = F(t, A)` (equation (2.1)). -/
lemma odeSolution_A : ODESolution F A 0 1 :=
  ⟨fun t _ => (hasDerivAt_A t).continuousAt.continuousWithinAt,
    fun t _ => (hasDerivAt_A t).hasDerivWithinAt⟩

lemma odeSolution_K :
    ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K 0 1 := by
  have hK : K = fun t : ℝ => (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℝ) + t • !![0; 0; 1] := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K]
  rw [hK]
  refine Exactness.odeSolution_add_smul_of_const (fun t x => ?_) _ 0 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [F, V₀, Matrix.mul_apply, Fin.sum_univ_succ]

lemma odeSolution_Lh :
    ODESolution (fun t L => (F t (Xh * Lᵀ))ᵀ * Xh) Lh 0 1 := by
  have hd : ∀ t : ℝ, HasDerivAt Lh ((F t (Xh * (Lh t)ᵀ))ᵀ * Xh) t := by
    intro t
    have h1 := (hasDerivAt_id t).smul_const (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin (1 + 1)) ℝ)
    have h2 := (hasDerivAt_pow 2 t).smul_const (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin (1 + 1)) ℝ)
    have h := (h1.const_add (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin (1 + 1)) ℝ)).add h2
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Lh]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [F, Xh, Matrix.mul_apply, Fin.sum_univ_succ]
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

/-- All data of an XL step for the field `F`: the step exists. -/
lemma isXLStep : IsXLStep (r := 1) (t := 1) F 0 1 X₀ S₀ V₀ K Xh Lh Vh Sh Vh 1 σ where
  kstep := odeSolution_K
  kstep₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K, X₀, S₀]
  orth_Xh := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xh, Matrix.mul_apply, Fin.sum_univ_succ]
  Xh_left := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Xh, X₀]
  capture := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Xh, K, Matrix.mul_apply, Fin.sum_univ_succ,
          Function.swap, Matrix.vecHead, Matrix.vecTail]
  lstep := odeSolution_Lh
  lstep₀_left := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Lh, V₀, S₀, Matrix.mul_apply]
  lstep₀_right := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Lh]
  orth_Vh := by
    have h := c_sq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vh, Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  qr := by
    have h := c_sq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lh, Vh, Sh, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      linarith
  orth_Us := by
    have h := c_sq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vh, Matrix.mul_apply, Fin.sum_univ_succ] <;> linarith
  orth_Ws := by simp
  svd := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Vh, Sh, σ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;> ring
  sorted := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [σ]
  nonneg := by
    intro i
    fin_cases i <;> simp [σ]

/-- **Theorem 2.2 of arXiv 2502.08951 fails for a state-dependent field.**  The paper states
exactness for the general equation (2.1), `Ȧ = F(t, A)`; its proof, like [6, Lemma 1], uses
`F(t, Y) = Ȧ(t)` for all `Y`, in the K-step and in the L-step.  Here `F` is affine in `Y`, `A(t)`
is an exact solution of rank one for all `t`, with `A(0) = X⁰ S⁰ V⁰ᵀ`, `A(1) = X₁ S₁ V₁ᵀ` and
`V₁ᵀ V⁰` invertible, and an XL step exists; its result differs from `A(1)` however many singular
values are retained.  The defect is not tied to the choice of `X̂`: for **every** `X̂ = [X⁰, …]`
that captures `K(1)` no matrix `X̂ Z` equals `A(1)`. -/
theorem theorem_2_2_false_for_state_dependent_field :
    ODESolution F A 0 1 ∧ (∀ t, (A t).rank = 1) ∧ X₀ * S₀ * V₀ᵀ = A 0 ∧
      A 1 = (!![1; 1 / 2; 1] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
        (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ ∧
      IsUnit ((!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * V₀) ∧
      IsXLStep (r := 1) (t := 1) F 0 1 X₀ S₀ V₀ K Xh Lh Vh Sh Vh 1 σ ∧
      (∀ k, truncate Xh Vh Vh 1 σ k ≠ A 1) ∧
      ∀ (X : Matrix (Fin 3) (Fin (1 + 1)) ℝ), (∀ i j, X i (Fin.castAdd 1 j) = X₀ i j) →
        X * Xᵀ * K 1 = K 1 → ∀ Z : Matrix (Fin (1 + 1)) (Fin 2) ℝ, X * Z ≠ A 1 := by
  have key : ∀ (X : Matrix (Fin 3) (Fin (1 + 1)) ℝ), (∀ i j, X i (Fin.castAdd 1 j) = X₀ i j) →
      X * Xᵀ * K 1 = K 1 → ∀ Z : Matrix (Fin (1 + 1)) (Fin 2) ℝ, X * Z ≠ A 1 := by
    intro X hX hcap Z hZ
    have h10 : X 1 0 = 0 := by simpa [X₀] using hX 1 0
    have h20 : X 2 0 = 0 := by simpa [X₀] using hX 2 0
    rw [Matrix.mul_assoc] at hcap
    set w := Xᵀ * K 1 with hw
    have e1 := congrFun (congrFun hcap 1) 0
    have e2 := congrFun (congrFun hcap 2) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
      Fin.succ_zero_eq_one, add_zero, h10, h20, zero_mul, zero_add] at e1 e2
    have e1' : X 1 1 * w 1 0 = 0 := by simpa [K] using e1
    have e2' : X 2 1 * w 1 0 = 1 := by simpa [K] using e2
    have hw1 : w 1 0 ≠ 0 := fun h => by simp [h] at e2'
    have hX11 : X 1 1 = 0 := by
      rcases mul_eq_zero.mp e1' with h | h
      · exact h
      · exact absurd h hw1
    have e3 := congrFun (congrFun hZ 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h10, hX11, A] at e3
  have hrank : ∀ t, (A t).rank = 1 := by
    intro t
    have hfac : A t = (!![1; t ^ 2 / 2; t] : Matrix (Fin 3) (Fin 1) ℝ) *
        (!![1, t] : Matrix (Fin 1) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply] <;> ring
    have hle : (A t).rank ≤ 1 := by
      rw [hfac]
      refine (Matrix.rank_mul_le_right _ _).trans ?_
      simpa using Matrix.rank_le_card_height (!![1, t] : Matrix (Fin 1) (Fin 2) ℝ)
    refine le_antisymm hle (Nat.one_le_iff_ne_zero.mpr fun h0 => ?_)
    have hbot : LinearMap.range (A t).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hzero := LinearMap.range_eq_bot.mp hbot
    have h1 := congrFun (congrArg (fun f => f ![1, 0]) hzero) 0
    simp [A, Matrix.mulVec, dotProduct] at h1
  refine ⟨odeSolution_A, hrank, ?_, ?_, ?_, isXLStep, ?_, key⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [X₀, S₀, V₀, A, Matrix.mul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply]
  · have h : (!![1; 1] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * V₀ = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [V₀, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [h]
    exact isUnit_one
  · intro k
    have h := key Xh isXLStep.Xh_left isXLStep.capture
      (Vh * Matrix.diagonal (fun j : Fin (1 + 1) => if (j : ℕ) < k then σ j else 0) * 1ᵀ * Vhᵀ)
    rw [truncate]
    simpa only [Matrix.mul_assoc] using h

end Counterexample

/-! ### The sXL integrator -/

section sXL

variable {rt : ℕ}

omit [Fintype n] in
/-- **Explicit-Euler XL step** (arXiv 2502.08951, Sec. 2, (2.10)).  Let `X̂ = [X, …]` have
orthonormal columns and start the L-step from `L̂ⁿ = [V Sᵀ, 0]`.  Then
`X̂ (L̂ⁿ + Δt F(X̂ L̂ⁿᵀ)ᵀ X̂)ᵀ = Y + Δt P̂ F(Y)` with `Y = X S Vᵀ` and `P̂ = X̂ X̂ᵀ`.  This needs no
separability. -/
theorem euler_lstep {F : Matrix m n ℝ → Matrix m n ℝ} {X : Matrix m (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} {Xh : Matrix m (Fin (r + rt)) ℝ}
    (hl : ∀ i j, Xh i (Fin.castAdd rt j) = X i j) {L : Matrix n (Fin (r + rt)) ℝ}
    (hL₁ : ∀ i j, L i (Fin.castAdd rt j) = (V * Sᵀ) i j) (hL₂ : ∀ i j, L i (Fin.natAdd r j) = 0)
    (Δt : ℝ) :
    Xh * (L + Δt • ((F (Xh * Lᵀ))ᵀ * Xh))ᵀ =
      X * S * Vᵀ + Δt • (Xh * Xhᵀ * F (X * S * Vᵀ)) := by
  have hL : L = (V * Sᵀ) * (leftEmb r rt)ᵀ := by
    ext i j
    induction j using Fin.addCases with
    | left j => simp [Matrix.mul_apply, leftEmb, hL₁, Fin.castAdd_inj]
    | right j =>
      have hne : ∀ a : Fin r, Fin.natAdd r j ≠ Fin.castAdd rt a := fun a h => by
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [Matrix.mul_apply, leftEmb, hL₂, hne]
  have hY : Xh * Lᵀ = X * S * Vᵀ := by
    rw [hL, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, mul_leftEmb,
      Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    congr 2
    ext i j
    simp [hl]
  rw [Matrix.transpose_add, Matrix.mul_add, hY, Matrix.transpose_smul, Matrix.mul_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]

/-- **The sXL integrator** (arXiv 2502.08951, Sec. 2, (2.6)–(2.11)).  Let `F` be separable,
`F(K Vᵀ) = 𝒦(K) 𝒱(V)ᵀ`, and let `X̂ = orth[X, 𝒦(X S)]`.  Then

* the capture is exact: the explicit Euler K-step `K₁ = X S + Δt F(X S Vᵀ) V` lies in the range of
  `X̂`, and so does `F(Y)`, for `Y = X S Vᵀ`;
* the explicit Euler L-step (2.10) from `[V Sᵀ, 0]` gives `Ŷ = Y + Δt P̂ F(Y) = Y + Δt F(Y)`, the
  full explicit Euler step, before truncation. -/
theorem sxl_step {F : Matrix m n ℝ → Matrix m n ℝ} {𝒦 : Matrix m (Fin r) ℝ → Matrix m (Fin rt) ℝ}
    {𝒱 : Matrix n (Fin r) ℝ → Matrix n (Fin rt) ℝ} (hsep : ∀ K V, F (K * Vᵀ) = 𝒦 K * (𝒱 V)ᵀ)
    {X : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {Xh : Matrix m (Fin (r + rt)) ℝ} (hXh : Xhᵀ * Xh = 1)
    (hl : ∀ i j, Xh i (Fin.castAdd rt j) = X i j) (hcap : Xh * Xhᵀ * 𝒦 (X * S) = 𝒦 (X * S))
    {L : Matrix n (Fin (r + rt)) ℝ} (hL₁ : ∀ i j, L i (Fin.castAdd rt j) = (V * Sᵀ) i j)
    (hL₂ : ∀ i j, L i (Fin.natAdd r j) = 0) (Δt : ℝ) :
    Xh * Xhᵀ * F (X * S * Vᵀ) = F (X * S * Vᵀ) ∧
      Xh * Xhᵀ * (X * S + Δt • (F (X * S * Vᵀ) * V)) = X * S + Δt • (F (X * S * Vᵀ) * V) ∧
      Xh * (L + Δt • ((F (Xh * Lᵀ))ᵀ * Xh))ᵀ = X * S * Vᵀ + Δt • F (X * S * Vᵀ) := by
  have hF : Xh * Xhᵀ * F (X * S * Vᵀ) = F (X * S * Vᵀ) := by
    rw [hsep, ← Matrix.mul_assoc, hcap]
  have hX : Xh * Xhᵀ * (X * S) = X * S := by
    rw [← Matrix.mul_assoc, capture_left hXh hl]
  refine ⟨hF, ?_, ?_⟩
  · rw [Matrix.mul_add, hX, Matrix.mul_smul, ← Matrix.mul_assoc, hF]
  · rw [euler_lstep hl hL₁ hL₂, hF]

/-- **sXL is explicit-Euler XL** (arXiv 2502.08951, Sec. 2, "the effect of this step, if a forward
Euler scheme is applied, is simply to add `𝒦(K(tⁿ))` to the basis"): if `𝒱(V)ᵀ V` has a right
inverse and `Δt ≠ 0`, a matrix `P` that fixes `X` fixes the Euler K-step `K₁` iff it fixes `𝒦(X S)`.
So the augmentations `[X, K₁]` of XL and `[X, 𝒦(X S)]` of sXL have the same range. -/
theorem sxl_capture_iff {F : Matrix m n ℝ → Matrix m n ℝ}
    {𝒦 : Matrix m (Fin r) ℝ → Matrix m (Fin rt) ℝ}
    {𝒱 : Matrix n (Fin r) ℝ → Matrix n (Fin rt) ℝ} (hsep : ∀ K V, F (K * Vᵀ) = 𝒦 K * (𝒱 V)ᵀ)
    {X : Matrix m (Fin r) ℝ} {S : Matrix (Fin r) (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    {G : Matrix (Fin r) (Fin rt) ℝ} (hG : (𝒱 V)ᵀ * V * G = 1) {Δt : ℝ} (hΔt : Δt ≠ 0)
    {P : Matrix m m ℝ} (hP : P * X = X) :
    P * (X * S + Δt • (F (X * S * Vᵀ) * V)) = X * S + Δt • (F (X * S * Vᵀ) * V) ↔
      P * 𝒦 (X * S) = 𝒦 (X * S) := by
  have hPXS : P * (X * S) = X * S := by rw [← Matrix.mul_assoc, hP]
  have hexp : F (X * S * Vᵀ) * V = 𝒦 (X * S) * ((𝒱 V)ᵀ * V) := by
    rw [hsep, Matrix.mul_assoc]
  rw [hexp, Matrix.mul_add, hPXS, Matrix.mul_smul, add_right_inj, ← Matrix.mul_assoc]
  constructor
  · intro h
    have h1 : (P * 𝒦 (X * S)) * ((𝒱 V)ᵀ * V) = 𝒦 (X * S) * ((𝒱 V)ᵀ * V) := by
      have h2 := congrArg (fun Z => Δt⁻¹ • Z) h
      simpa only [smul_smul, inv_mul_cancel₀ hΔt, one_smul] using h2
    have h3 := congrArg (fun Z => Z * G) h1
    simpa only [Matrix.mul_assoc, hG, Matrix.mul_one] using h3
  · intro h
    rw [h]

end sXL

end XL

/-! ### The penalized splitting (Section 4) -/

section Penalized

/-- The setting of the full-tensor penalized scheme (4.3) of arXiv 2502.08951.  `E` is a real vector
space of admissible distribution functions, with pointwise values on phase space `Ξ` (`Ξ` is the
set of pairs `(x, v)`) and moments in `G`. -/
structure PenalizedSetting (Ξ E G : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup G]
    [Module ℝ G] where
  /-- The value `f(x, v)` of `f`. -/
  val : E →ₗ[ℝ] Ξ → ℝ
  /-- The moments `𝒰[f] = ∫ f φ dv`. -/
  mom : E →ₗ[ℝ] G
  /-- The Maxwellian with given moments, (1.5). -/
  mx : G → E
  /-- The collision term `𝒬(f, f)`. -/
  coll : E → E
  /-- The transport term `v · ∇ₓ f`. -/
  adv : E →ₗ[ℝ] E
  /-- `f` and `ℳ[f]` share their moments, (1.7). -/
  mom_mx : ∀ U, mom (mx U) = U
  /-- Conservation, (1.4). -/
  mom_coll : ∀ f, mom (coll f) = 0

namespace PenalizedSetting

variable {Ξ E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  (S : PenalizedSetting Ξ E G)

/-- The Maxwellian `ℳ[f]`. -/
def maxw (f : E) : E := S.mx (S.mom f)

/-- One step of the scheme (4.3): `f* = fⁿ - Δt v·∇ₓfⁿ` and (4.3b) multiplied by `ε Δt`. The limit
`ε = 0` is included. -/
structure IsPenalizedBGKStep (ε lam Δt : ℝ) (f fs f' : E) : Prop where
  advect : fs = f - Δt • S.adv f
  collide : ε • (f' - fs) = Δt • (S.coll fs + lam • fs - lam • f')

variable {S}
variable {ε lam Δt : ℝ} {f fs f' : E}

/-- arXiv 2502.08951, (4.4): the collision step conserves the moments, for every `ε ≥ 0`. -/
theorem IsPenalizedBGKStep.mom_eq (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) : S.mom f' = S.mom fs := by
  have h1 := congrArg S.mom h.collide
  simp only [map_smul, map_sub, map_add, S.mom_coll, zero_add] at h1
  have h2 : (ε + lam * Δt) • (S.mom f' - S.mom fs) = 0 := by
    linear_combination (norm := module) h1
  have h3 : S.mom f' - S.mom fs = (ε + lam * Δt)⁻¹ • (ε + lam * Δt) • (S.mom f' - S.mom fs) := by
    rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
  rw [h2, smul_zero] at h3
  exact sub_eq_zero.mp h3

/-- arXiv 2502.08951, (4.4): hence `ℳⁿ⁺¹ = ℳ*`. -/
theorem IsPenalizedBGKStep.maxw_eq (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) : S.maxw f' = S.maxw fs := by
  rw [maxw, maxw, h.mom_eq hw]

/-- arXiv 2502.08951, (4.5): the moment update `𝒰ⁿ⁺¹ - 𝒰ⁿ = -Δt ∇ₓ·∫ fⁿ v φ dv`. -/
theorem IsPenalizedBGKStep.mom_update (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) : S.mom f' - S.mom f = -(Δt • S.mom (S.adv f)) := by
  rw [h.mom_eq hw, h.advect]
  simp only [map_sub, map_smul]
  abel

/-- `Ds` is a multiplier `𝒟*` of (4.7): `𝒬(f*, f*) = (𝒟* - λ)(f* - ℳ*)` pointwise. This is (4.7)
without the division by `f* - ℳ*`, which may vanish at points where `𝒬(f*, f*) = 0`. -/
def IsMultiplier (S : PenalizedSetting Ξ E G) (lam : ℝ) (fs : E) (Ds : Ξ → ℝ) : Prop :=
  ∀ ξ, S.val (S.coll fs) ξ = (Ds ξ - lam) * (S.val fs ξ - S.val (S.maxw fs) ξ)

/-- The two brackets of (4.6) after the identity `ℳ* = ℳⁿ⁺¹`: the quantity
`(f* - fⁿ)/Δt - (ℳ* - ℳⁿ)/Δt`. -/
noncomputable def bracket (S : PenalizedSetting Ξ E G) (Δt : ℝ) (f fs : E) (ξ : Ξ) : ℝ :=
  (S.val fs ξ - S.val f ξ) / Δt - (S.val (S.maxw fs) ξ - S.val (S.maxw f) ξ) / Δt

/-- The deviation from equilibrium `f - ℳ[f]`. -/
def dev (S : PenalizedSetting Ξ E G) (f : E) (ξ : Ξ) : ℝ := S.val f ξ - S.val (S.maxw f) ξ

/-- The pointwise algebra behind (4.6). -/
lemma IsPenalizedBGKStep.dev_star (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) {Ds : Ξ → ℝ} (hD : S.IsMultiplier lam fs Ds) (ξ : Ξ) :
    S.dev f' ξ = (ε + Ds ξ * Δt) / (ε + lam * Δt) * S.dev fs ξ := by
  have hc := congrFun (congrArg S.val h.collide) ξ
  simp only [map_smul, map_sub, map_add, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul,
    hD ξ] at hc
  rw [dev, dev, h.maxw_eq hw, div_mul_eq_mul_div, eq_div_iff hw]
  linear_combination hc

/-- arXiv 2502.08951, The compact form of (4.6): `fⁿ⁺¹ - ℳⁿ⁺¹ = (ε + 𝒟* Δt)/(ε + λ Δt) (fⁿ - ℳⁿ + Δt
b)`, with `b` the bracket. -/
theorem IsPenalizedBGKStep.dev_eq (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) (hΔt : Δt ≠ 0) {Ds : Ξ → ℝ} (hD : S.IsMultiplier lam fs Ds) (ξ : Ξ) :
    S.dev f' ξ = (ε + Ds ξ * Δt) / (ε + lam * Δt) * (S.dev f ξ + Δt * S.bracket Δt f fs ξ) := by
  rw [h.dev_star hw hD ξ]
  congr 1
  rw [dev, dev, bracket]
  field_simp
  ring

/-- **The identity (4.6)** of arXiv 2502.08951, literally, with `𝒟*` any multiplier in the sense of
`IsMultiplier`.  It holds for every `ε ≥ 0` with `ε + λ Δt ≠ 0`. -/
theorem IsPenalizedBGKStep.eq_4_6 (h : S.IsPenalizedBGKStep ε lam Δt f fs f')
    (hw : ε + lam * Δt ≠ 0) (hΔt : Δt ≠ 0) {Ds : Ξ → ℝ} (hD : S.IsMultiplier lam fs Ds) (ξ : Ξ) :
    S.val f' ξ - S.val (S.maxw f') ξ =
      (ε + Ds ξ * Δt) / (ε + lam * Δt) * (S.val f ξ - S.val (S.maxw f) ξ)
      - ε * Δt / (ε + lam * Δt) *
          (S.val (S.adv f) ξ + (S.val (S.maxw f') ξ - S.val (S.maxw f) ξ) / Δt)
      + Ds ξ * Δt ^ 2 / (ε + lam * Δt) *
          ((S.val fs ξ - S.val f ξ) / Δt - (S.val (S.maxw fs) ξ - S.val (S.maxw f) ξ) / Δt) := by
  have h1 := h.dev_eq hw hΔt hD ξ
  have hadv : S.val fs ξ = S.val f ξ - Δt * S.val (S.adv f) ξ := by
    rw [h.advect]
    simp
  rw [dev, dev, bracket] at h1
  rw [h1, h.maxw_eq hw, hadv]
  field_simp
  ring

/-- arXiv 2502.08951, **(4.8)**: in the limit `ε = 0`, exactly `fⁿ⁺¹ - ℳⁿ⁺¹ = (𝒟*/λ)(fⁿ - ℳⁿ) +
(𝒟*/λ) Δt b`, so the remainder is `O(Δt)` when the bracket `b` is `O(1)`. -/
theorem IsPenalizedBGKStep.eq_4_8 (h : S.IsPenalizedBGKStep 0 lam Δt f fs f') (hlam : lam ≠ 0)
    (hΔt : Δt ≠ 0) {Ds : Ξ → ℝ} (hD : S.IsMultiplier lam fs Ds) (ξ : Ξ) :
    S.dev f' ξ = Ds ξ / lam * S.dev f ξ + Ds ξ / lam * Δt * S.bracket Δt f fs ξ := by
  have hw : (0 : ℝ) + lam * Δt ≠ 0 := by simpa using ⟨hlam, hΔt⟩
  rw [h.dev_eq hw hΔt hD ξ]
  field_simp
  ring

/-- arXiv 2502.08951, **(4.8), the limit**: for fixed `f*`, the solutions of (4.3b) converge
pointwise to `ℳ* + (𝒟*/λ)(f* - ℳ*)` as `ε → 0⁺`. -/
theorem tendsto_collision (hlam : 0 < lam) (hΔt : 0 < Δt) {Ds : Ξ → ℝ}
    (hD : S.IsMultiplier lam fs Ds) {fε : ℝ → E}
    (h : ∀ ε > 0, S.IsPenalizedBGKStep ε lam Δt f fs (fε ε)) (ξ : Ξ) :
    Tendsto (fun ε => S.val (fε ε) ξ) (𝓝[>] 0)
      (𝓝 (S.val (S.maxw fs) ξ + Ds ξ / lam * S.dev fs ξ)) := by
  have hpos : (0 : ℝ) + lam * Δt ≠ 0 := by positivity
  have hc : ContinuousAt (fun ε : ℝ => S.val (S.maxw fs) ξ +
      (ε + Ds ξ * Δt) / (ε + lam * Δt) * S.dev fs ξ) 0 := by
    refine continuousAt_const.fun_add (ContinuousAt.fun_mul
      (ContinuousAt.div₀ (by fun_prop) (by fun_prop) hpos) continuousAt_const)
  have hval : S.val (S.maxw fs) ξ + (0 + Ds ξ * Δt) / (0 + lam * Δt) * S.dev fs ξ =
      S.val (S.maxw fs) ξ + Ds ξ / lam * S.dev fs ξ := by
    field_simp
    ring
  have ht := hc.tendsto
  simp only [hval] at ht
  refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hw : ε + lam * Δt ≠ 0 := by positivity
  have h1 := (h ε hε').dev_star hw hD ξ
  rw [dev, (h ε hε').maxw_eq hw] at h1
  linarith

section Contraction

variable {α B : ℝ}

/-- The contraction factor of one step: `α` for `ε = 0`, tending to `α` as `ε → 0`. -/
noncomputable def contr (ε lam Δt α : ℝ) : ℝ := (ε + α * lam * Δt) / (ε + lam * Δt)

lemma contr_nonneg (hε : 0 ≤ ε) (hlam : 0 < lam) (hΔt : 0 < Δt) (hα : 0 ≤ α) :
    0 ≤ contr ε lam Δt α := by
  rw [contr]
  positivity

lemma contr_lt_one (hε : 0 ≤ ε) (hlam : 0 < lam) (hΔt : 0 < Δt) (hα1 : α < 1) :
    contr ε lam Δt α < 1 := by
  have hw : 0 < ε + lam * Δt := by positivity
  rw [contr, div_lt_one hw]
  nlinarith [mul_pos hlam hΔt]

/-- arXiv 2502.08951, **(4.10)**, with `|𝒟*| ≤ α λ` (condition (4.9)) and bracket bounded by `B`:
`|fⁿ⁺¹ - ℳⁿ⁺¹| ≤ α_ε (|fⁿ - ℳⁿ| + Δt B)`, `α_ε = (ε + α λ Δt)/(ε + λ Δt)`, so `α₀ = α`. -/
theorem IsPenalizedBGKStep.abs_dev_le (h : S.IsPenalizedBGKStep ε lam Δt f fs f') (hε : 0 ≤ ε)
    (hlam : 0 < lam) (hΔt : 0 < Δt) {Ds : Ξ → ℝ} (hD : S.IsMultiplier lam fs Ds) {ξ : Ξ}
    (hDs : |Ds ξ| ≤ α * lam) (hB : |S.bracket Δt f fs ξ| ≤ B) :
    |S.dev f' ξ| ≤ contr ε lam Δt α * |S.dev f ξ| + contr ε lam Δt α * (Δt * B) := by
  have hw : 0 < ε + lam * Δt := by positivity
  have hα : 0 ≤ α * lam := (abs_nonneg _).trans hDs
  rw [h.dev_eq hw.ne' hΔt.ne' hD ξ, abs_mul, abs_div, abs_of_pos hw, ← mul_add]
  have h1 : |ε + Ds ξ * Δt| ≤ ε + α * lam * Δt := by
    calc |ε + Ds ξ * Δt| ≤ |ε| + |Ds ξ * Δt| := abs_add_le _ _
      _ = ε + |Ds ξ| * Δt := by rw [abs_of_nonneg hε, abs_mul, abs_of_pos hΔt]
      _ ≤ _ := by gcongr
  have h2 : |S.dev f ξ + Δt * S.bracket Δt f fs ξ| ≤ |S.dev f ξ| + Δt * B := by
    calc _ ≤ |S.dev f ξ| + |Δt * S.bracket Δt f fs ξ| := abs_add_le _ _
      _ = |S.dev f ξ| + Δt * |S.bracket Δt f fs ξ| := by rw [abs_mul, abs_of_pos hΔt]
      _ ≤ _ := by gcongr
  rw [contr]
  gcongr

/-- arXiv 2502.08951, **(4.11)**: under (4.9) and bounded brackets, `|fⁿ - ℳⁿ| ≤ α_εⁿ |f⁰ - ℳ⁰| +
(ε/λ + α Δt) B / (1 - α)`, for every `ε ≥ 0`. For `ε = 0` this is `αⁿ |f⁰ - ℳ⁰| + O(Δt)`. -/
theorem abs_dev_le_pow {f fs : ℕ → E} {Ds : ℕ → Ξ → ℝ} (hε : 0 ≤ ε) (hlam : 0 < lam)
    (hΔt : 0 < Δt) (hα : 0 ≤ α) (hα1 : α < 1) (hB0 : 0 ≤ B)
    (h : ∀ n, S.IsPenalizedBGKStep ε lam Δt (f n) (fs n) (f (n + 1)))
    (hD : ∀ n, S.IsMultiplier lam (fs n) (Ds n)) (hDs : ∀ n ξ, |Ds n ξ| ≤ α * lam)
    (hB : ∀ n ξ, |S.bracket Δt (f n) (fs n) ξ| ≤ B) (n : ℕ) (ξ : Ξ) :
    |S.dev (f n) ξ| ≤ contr ε lam Δt α ^ n * |S.dev (f 0) ξ|
      + (ε / lam + α * Δt) * B / (1 - α) := by
  set a := contr ε lam Δt α with ha
  have ha0 : 0 ≤ a := contr_nonneg hε hlam hΔt hα
  have ha1 : a < 1 := contr_lt_one hε hlam hΔt hα1
  have hrec : ∀ k < n, |S.dev (f (k + 1)) ξ| ≤ a * |S.dev (f k) ξ| + a * (Δt * B) := fun k _ =>
    (h k).abs_dev_le hε hlam hΔt (hD k) (hDs k ξ) (hB k ξ)
  have hg := discrete_gronwall_const_le (e := fun k => |S.dev (f k) ξ|) ha0 hrec n le_rfl
  have hsum : ∑ k ∈ Finset.range n, a ^ k ≤ 1 / (1 - a) := by
    have h1 := mul_neg_geom_sum a n
    have h2 : 0 < 1 - a := by linarith
    rw [le_div_iff₀ h2, mul_comm, h1]
    have := pow_nonneg ha0 n
    linarith
  have hb0 : 0 ≤ a * (Δt * B) := by positivity
  have htail : a * (Δt * B) * (1 / (1 - a)) = (ε / lam + α * Δt) * B / (1 - α) := by
    have hw : ε + lam * Δt ≠ 0 := by positivity
    have h1α : 1 - α ≠ 0 := by linarith
    have h1a : 1 - a = (1 - α) * lam * Δt / (ε + lam * Δt) := by
      rw [ha, contr]
      field_simp
      ring
    rw [h1a, ha, contr]
    field_simp
  calc |S.dev (f n) ξ| ≤ a ^ n * |S.dev (f 0) ξ| + a * (Δt * B) * ∑ k ∈ Finset.range n, a ^ k := hg
    _ ≤ a ^ n * |S.dev (f 0) ξ| + a * (Δt * B) * (1 / (1 - a)) := by gcongr
    _ = _ := by rw [htail]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] {S' : PenalizedSetting Ξ E G'}

/-- arXiv 2502.08951, **(4.12) with an explicit remainder.**  If the flux functional `g ↦ ∇ₓ·∫ g v φ
dv` is bounded by `C` with respect to the pointwise bound on `g` (this is where a discretization of
`∇ₓ` enters), then `‖(𝒰ⁿ⁺¹ - 𝒰ⁿ)/Δt + ∇ₓ·∫ ℳⁿ v φ dv‖ ≤ C (α_εⁿ E₀ + (ε/λ + α Δt) B / (1 - α))`. -/
theorem moment_defect_le {f fs : ℕ → E} {Ds : ℕ → Ξ → ℝ} {C E₀ : ℝ} (hε : 0 ≤ ε)
    (hlam : 0 < lam) (hΔt : 0 < Δt) (hα : 0 ≤ α) (hα1 : α < 1) (hB0 : 0 ≤ B)
    (h : ∀ n, S'.IsPenalizedBGKStep ε lam Δt (f n) (fs n) (f (n + 1)))
    (hD : ∀ n, S'.IsMultiplier lam (fs n) (Ds n)) (hDs : ∀ n ξ, |Ds n ξ| ≤ α * lam)
    (hB : ∀ n ξ, |S'.bracket Δt (f n) (fs n) ξ| ≤ B)
    (hadv : ∀ (g : E) (b : ℝ), (∀ ξ, |S'.val g ξ| ≤ b) → ‖S'.mom (S'.adv g)‖ ≤ C * b)
    (hE₀ : ∀ ξ, |S'.dev (f 0) ξ| ≤ E₀) (n : ℕ) :
    ‖Δt⁻¹ • (S'.mom (f (n + 1)) - S'.mom (f n)) + S'.mom (S'.adv (S'.maxw (f n)))‖ ≤
      C * (contr ε lam Δt α ^ n * E₀ + (ε / lam + α * Δt) * B / (1 - α)) := by
  have hw : ε + lam * Δt ≠ 0 := by positivity
  have h1 := (h n).mom_update hw
  have heq : Δt⁻¹ • (S'.mom (f (n + 1)) - S'.mom (f n)) + S'.mom (S'.adv (S'.maxw (f n))) =
      S'.mom (S'.adv (S'.maxw (f n) - f n)) := by
    rw [h1, smul_neg, smul_smul, inv_mul_cancel₀ hΔt.ne', one_smul, map_sub, map_sub]
    abel
  rw [heq]
  refine hadv _ _ fun ξ => ?_
  have h2 := abs_dev_le_pow hε hlam hΔt hα hα1 hB0 h hD hDs hB n ξ
  have h3 : S'.val (S'.maxw (f n) - f n) ξ = -S'.dev (f n) ξ := by
    simp [dev]
  rw [h3, abs_neg]
  have h4 : contr ε lam Δt α ^ n * |S'.dev (f 0) ξ| ≤ contr ε lam Δt α ^ n * E₀ := by
    have := pow_nonneg (contr_nonneg hε hlam hΔt hα) n
    exact mul_le_mul_of_nonneg_left (hE₀ ξ) this
  linarith

/-- **(4.12)** of arXiv 2502.08951: for `ε = 0` there is `N` such that for all `n ≥ N`
`(𝒰ⁿ⁺¹ - 𝒰ⁿ)/Δt + ∇ₓ·∫ ℳⁿ v φ dv = O(Δt)`, with the explicit constant `C (1 + α B / (1 - α))`. -/
theorem exists_first_order {f fs : ℕ → E} {Ds : ℕ → Ξ → ℝ} {C E₀ : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam) (hΔt : 0 < Δt) (hα : 0 ≤ α) (hα1 : α < 1) (hB0 : 0 ≤ B)
    (h : ∀ n, S'.IsPenalizedBGKStep 0 lam Δt (f n) (fs n) (f (n + 1)))
    (hD : ∀ n, S'.IsMultiplier lam (fs n) (Ds n)) (hDs : ∀ n ξ, |Ds n ξ| ≤ α * lam)
    (hB : ∀ n ξ, |S'.bracket Δt (f n) (fs n) ξ| ≤ B)
    (hadv : ∀ (g : E) (b : ℝ), (∀ ξ, |S'.val g ξ| ≤ b) → ‖S'.mom (S'.adv g)‖ ≤ C * b)
    (hE₀ : ∀ ξ, |S'.dev (f 0) ξ| ≤ E₀) :
    ∃ N, ∀ n ≥ N,
      ‖Δt⁻¹ • (S'.mom (f (n + 1)) - S'.mom (f n)) + S'.mom (S'.adv (S'.maxw (f n)))‖ ≤
        C * Δt * (1 + α * B / (1 - α)) := by
  have hcontr : contr 0 lam Δt α = α := by
    rw [contr]
    field_simp
    ring
  set E₁ := max E₀ 0 with hE₁
  have hE₁0 : 0 ≤ E₁ := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < Δt / (E₁ + 1) by positivity) hα1
  refine ⟨N, fun n hn => ?_⟩
  have h1 := moment_defect_le (E₀ := E₁) le_rfl hlam hΔt hα hα1 hB0 h hD hDs hB hadv
    (fun ξ => (hE₀ ξ).trans (le_max_left _ _)) n
  rw [hcontr] at h1
  refine h1.trans ?_
  have h2 : α ^ n ≤ α ^ N := pow_le_pow_of_le_one hα hα1.le hn
  have h3 : α ^ n * E₁ ≤ Δt := by
    calc α ^ n * E₁ ≤ Δt / (E₁ + 1) * E₁ := by gcongr; exact h2.trans hN.le
      _ ≤ Δt := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  have h4 : (0 / lam + α * Δt) * B / (1 - α) = Δt * (α * B / (1 - α)) := by
    rw [zero_div, zero_add]
    ring
  rw [h4, mul_assoc]
  gcongr
  linarith [mul_comm Δt (1 + α * B / (1 - α))]

end Contraction

section BGK

/-- arXiv 2502.08951, For the BGK operator `𝒬_BGK(f) = ℳ[f] - f`, the constant `𝒟* = λ - 1` is a
multiplier. -/
theorem bgk_isMultiplier (hcoll : ∀ f, S.coll f = S.maxw f - f) (lam : ℝ) (fs : E) :
    S.IsMultiplier lam fs fun _ => lam - 1 := by
  intro ξ
  rw [hcoll]
  simp only [map_sub, Pi.sub_apply]
  ring

/-- arXiv 2502.08951, For the BGK operator, condition (4.9) with `𝒟* = λ - 1` holds iff `λ > 1/2`.
-/
theorem bgk_condition_iff (hlam : 0 < lam) : |lam - 1| / lam < 1 ↔ 1 / 2 < lam := by
  rw [div_lt_one hlam, abs_lt]
  constructor
  · rintro ⟨h, -⟩
    linarith
  · intro h
    constructor <;> linarith

/-- arXiv 2502.08951, The stronger AP property for BGK with `λ = 1` and `ε = 0`: `fⁿ⁺¹ = ℳ* = ℳⁿ⁺¹`,
regardless of the initial condition, so that for `n ≥ 1`, (4.14) holds with no remainder. -/
theorem bgk_step (hcoll : ∀ f, S.coll f = S.maxw f - f) (hΔt : Δt ≠ 0)
    (h : S.IsPenalizedBGKStep 0 1 Δt f fs f') : f' = S.maxw fs ∧ f' = S.maxw f' := by
  have h1 := h.collide
  rw [zero_smul, hcoll] at h1
  have h2 := (smul_eq_zero_iff_right hΔt).mp h1.symm
  have h3 : f' = S.maxw fs := by
    have : S.maxw fs - fs + (1 : ℝ) • fs - (1 : ℝ) • f' = S.maxw fs - f' := by
      simp only [one_smul]
      abel
    rw [this] at h2
    exact (sub_eq_zero.mp h2).symm
  refine ⟨h3, ?_⟩
  rw [h.maxw_eq (by simpa using hΔt)]
  exact h3

/-- arXiv 2502.08951, **(4.14)**: for BGK with `λ = 1`, `ε = 0`, `(𝒰ⁿ⁺¹ - 𝒰ⁿ)/Δt + ∇ₓ·∫ ℳⁿ v φ dv =
0` for `n ≥ 1`. -/
theorem bgk_moment_update (hcoll : ∀ f, S.coll f = S.maxw f - f) (hΔt : Δt ≠ 0) {f : ℕ → E}
    {fs : ℕ → E} (h : ∀ n, S.IsPenalizedBGKStep 0 1 Δt (f n) (fs n) (f (n + 1))) {n : ℕ}
      (hn : 1 ≤ n) :
    Δt⁻¹ • (S.mom (f (n + 1)) - S.mom (f n)) + S.mom (S.adv (S.maxw (f n))) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (bgk_step hcoll hΔt (h k)).2
  rw [(h (k + 1)).mom_update (by simpa using hΔt), ← hk, smul_neg, smul_smul,
    inv_mul_cancel₀ hΔt, one_smul, neg_add_cancel]

end BGK

end PenalizedSetting

end Penalized

/-! ### Gaussian integrals -/

section Gaussian

open Polynomial MeasureTheory Real

/-- `∫ p(v) e^{-b v²} dv`. -/
noncomputable def gaussI (b : ℝ) (p : ℝ[X]) : ℝ := ∫ v : ℝ, p.eval v * rexp (-b * v ^ 2)

lemma integrable_gauss (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable fun v : ℝ => p.eval v * rexp (-b * v ^ 2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine (hp.add hq).congr (ae_of_all _ fun v => ?_)
    simp [add_mul]
  | monomial n a =>
    have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := n)
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simpa [Real.rpow_natCast, mul_assoc] using h.const_mul a

lemma gaussI_add {b : ℝ} (hb : 0 < b) (p q : ℝ[X]) :
    gaussI b (p + q) = gaussI b p + gaussI b q := by
  simp only [gaussI, eval_add, add_mul]
  exact integral_add (integrable_gauss p hb) (integrable_gauss q hb)

lemma gaussI_smul (b c : ℝ) (p : ℝ[X]) : gaussI b (c • p) = c * gaussI b p := by
  simp only [gaussI, eval_smul, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

/-- `gaussI b` as a linear functional. -/
noncomputable def gaussL (b : ℝ) (hb : 0 < b) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun := gaussI b
  map_add' := gaussI_add hb
  map_smul' := gaussI_smul b

/-- Stein's identity `∫ p' e^{-b v²} = 2 b ∫ v p e^{-b v²}`. -/
lemma gaussI_derivative {b : ℝ} (hb : 0 < b) (p : ℝ[X]) :
    gaussI b (derivative p) = 2 * b * gaussI b (X * p) := by
  have hd : ∀ v : ℝ, HasDerivAt (fun v => p.eval v * rexp (-b * v ^ 2))
      ((derivative p - C (2 * b) * (X * p)).eval v * rexp (-b * v ^ 2)) v := by
    intro v
    have h1 := p.hasDerivAt v
    have h3 : HasDerivAt (fun v : ℝ => -b * v ^ 2) (-b * (2 * v)) v := by
      simpa using (hasDerivAt_pow 2 v).const_mul (-b)
    have h2 := h3.exp
    convert h1.mul h2 using 1
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (integrable_gauss _ hb) (integrable_gauss p hb)
  have h1 : gaussI b (derivative p - C (2 * b) * (X * p)) = 0 := h0
  have h2 : derivative p - C (2 * b) * (X * p) = derivative p + (-(2 * b)) • (X * p) := by
    rw [smul_eq_C_mul, C_neg]
    ring
  rw [h2, gaussI_add hb, gaussI_smul] at h1
  linarith

lemma gaussI_one {b : ℝ} (_hb : 0 < b) : gaussI b 1 = √(π / b) := by
  simp only [gaussI, eval_one, one_mul]
  exact integral_gaussian b

/-- The recursion for the Gaussian moments. -/
lemma gaussI_X_pow_add_two {b : ℝ} (hb : 0 < b) (k : ℕ) :
    gaussI b (X ^ (k + 2)) = (k + 1) / (2 * b) * gaussI b (X ^ k) := by
  have h := gaussI_derivative hb (X ^ (k + 1))
  have h1 : derivative (X ^ (k + 1) : ℝ[X]) = ((k : ℝ) + 1) • X ^ k := by
    rw [derivative_X_pow, smul_eq_C_mul]
    simp
  rw [h1, gaussI_smul] at h
  have h2 : (X * X ^ (k + 1) : ℝ[X]) = X ^ (k + 2) := by ring
  rw [h2] at h
  field_simp
  linarith

lemma gaussI_X {b : ℝ} (hb : 0 < b) : gaussI b X = 0 := by
  have h := gaussI_derivative hb 1
  have h0 : gaussI b 0 = 0 := by simp [gaussI]
  rw [derivative_one, h0, mul_one] at h
  have hb' : 2 * b ≠ 0 := by positivity
  exact (mul_eq_zero.mp h.symm).resolve_left hb'

/-! ### The velocity space -/

/-- The velocity function `p(v) e^{-v²/2}`: Gaussian times polynomial, the class of all velocity
factors in Section 5 of arXiv 2502.08951. -/
noncomputable def gaussFn (p : ℝ[X]) (v : ℝ) : ℝ := p.eval v * rexp (-v ^ 2 / 2)

/-- `⟨a b⟩ᵥ = ∫ a b dv` for velocity functions. -/
noncomputable def vIP (p q : ℝ[X]) : ℝ := ∫ v : ℝ, gaussFn p v * gaussFn q v

/-- `⟨a⟩ᵥ = ∫ a dv` for velocity functions. -/
noncomputable def vMean (p : ℝ[X]) : ℝ := ∫ v : ℝ, gaussFn p v

lemma vMean_eq (p : ℝ[X]) : vMean p = gaussI (1 / 2) p := by
  simp only [vMean, gaussI, gaussFn]
  congr 1
  funext v
  congr 2
  ring

lemma vIP_eq (p q : ℝ[X]) : vIP p q = gaussI 1 (p * q) := by
  simp only [vIP, gaussI, gaussFn, eval_mul]
  congr 1
  funext v
  have : rexp (-1 * v ^ 2) = rexp (-v ^ 2 / 2) * rexp (-v ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [this]
  ring

/-- `⟨·⟩ᵥ` as a linear functional. -/
noncomputable def vMeanL : ℝ[X] →ₗ[ℝ] ℝ := gaussL (1 / 2) (by norm_num)

@[simp] lemma vMeanL_apply (p : ℝ[X]) : vMeanL p = vMean p := (vMean_eq p).symm

/-- `⟨· ·⟩ᵥ` as a bilinear form. -/
noncomputable def vIPL : ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ :=
  (LinearMap.mul ℝ ℝ[X]).compr₂ (gaussL 1 one_pos)

@[simp] lemma vIPL_apply (p q : ℝ[X]) : vIPL p q = vIP p q := (vIP_eq p q).symm

lemma vIP_comm (p q : ℝ[X]) : vIP p q = vIP q p := by
  rw [vIP_eq, vIP_eq, mul_comm]

lemma vIP_X_left (p q : ℝ[X]) : vIP (X * p) q = vIP p (X * q) := by
  rw [vIP_eq, vIP_eq]
  congr 1
  ring

/-- The `k`-th velocity moment `a ↦ ∫ vᵏ a dv` as a linear functional. -/
noncomputable def momL (k : ℕ) : ℝ[X] →ₗ[ℝ] ℝ := vMeanL ∘ₗ LinearMap.mulLeft ℝ (X ^ k)

@[simp] lemma momL_apply (k : ℕ) (p : ℝ[X]) : momL k p = vMean (X ^ k * p) := by
  simp [momL]

/-- The value at `v` of a velocity function, as a linear functional. -/
noncomputable def pointL (v : ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := gaussFn p v
  map_add' p q := by simp [gaussFn, add_mul]
  map_smul' c p := by simp [gaussFn, mul_assoc]

@[simp] lemma pointL_apply (v : ℝ) (p : ℝ[X]) : pointL v p = gaussFn p v := rfl

/-! ### The Maxwellian -/

/-- `κ = 1/√(2π)`. -/
noncomputable def κ : ℝ := (√(2 * π))⁻¹

lemma κ_pos : 0 < κ := by
  have : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  exact inv_pos.mpr this

/-- The velocity factors of the rank-3 Maxwellian (5.2). -/
noncomputable def g₀ : ℝ[X] := κ • 1

/-- See `g₀`. -/
noncomputable def g₁ : ℝ[X] := κ • X

/-- See `g₀`. -/
noncomputable def g₂ : ℝ[X] := (κ / 2) • (X ^ 2 - 1)

/-- The simplified Maxwellian (5.2) `ρ e^{-v²/2}/√(2π) (1 + v u + (v² - 1) u² / 2)`: the expansion
of the Maxwellian `ρ e^{-(v-u)²/2}/√(2π)` (the core `Kinetic.maxwellian 1 ρ 1` in one dimension) to
second order in `u`, not equal to it. -/
noncomputable def maxwellianExpansion (ρ u v : ℝ) : ℝ :=
  ρ * (rexp (-v ^ 2 / 2) / √(2 * π)) * (1 + v * u + 1 / 2 * (v ^ 2 - 1) * u ^ 2)

lemma maxwellianExpansion_eq (ρ u v : ℝ) :
    maxwellianExpansion ρ u v =
      ρ * gaussFn g₀ v + ρ * u * gaussFn g₁ v + ρ * u ^ 2 * gaussFn g₂ v := by
  simp only [maxwellianExpansion, gaussFn, g₀, g₁, g₂, κ, eval_smul, eval_one, eval_X, eval_sub,
    eval_pow, smul_eq_mul, div_eq_mul_inv]
  ring

lemma gauss_half_zero : gaussI (1 / 2) 1 = √(2 * π) := by
  rw [gaussI_one (by norm_num)]
  congr 1
  ring

lemma gauss_half_succ (k : ℕ) :
    gaussI (1 / 2) (X ^ (k + 2)) = (k + 1) * gaussI (1 / 2) (X ^ k) := by
  rw [gaussI_X_pow_add_two (by norm_num)]
  norm_num

/-- The even and odd moments of the standard Gaussian. -/
lemma gauss_half_table :
    κ * gaussI (1 / 2) (X ^ 0) = 1 ∧ κ * gaussI (1 / 2) (X ^ 1) = 0 ∧
      κ * gaussI (1 / 2) (X ^ 2) = 1 ∧ κ * gaussI (1 / 2) (X ^ 3) = 0 ∧
      κ * gaussI (1 / 2) (X ^ 4) = 3 ∧ κ * gaussI (1 / 2) (X ^ 5) = 0 ∧
      κ * gaussI (1 / 2) (X ^ 6) = 15 := by
  have h0 : κ * gaussI (1 / 2) (X ^ 0) = 1 := by
    rw [pow_zero, gauss_half_zero, κ]
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne'
  have h1 : κ * gaussI (1 / 2) (X ^ 1) = 0 := by
    rw [pow_one, gaussI_X (by norm_num), mul_zero]
  have h2 : κ * gaussI (1 / 2) (X ^ 2) = 1 := by
    have := gauss_half_succ 0
    simp only [zero_add] at this
    rw [this]
    linarith
  have h3 : κ * gaussI (1 / 2) (X ^ 3) = 0 := by
    have := gauss_half_succ 1
    simp only [Nat.cast_one] at this
    rw [show (1 + 2 : ℕ) = 3 from rfl] at this
    rw [this]
    linarith
  have h4 : κ * gaussI (1 / 2) (X ^ 4) = 3 := by
    have := gauss_half_succ 2
    rw [show (2 + 2 : ℕ) = 4 from rfl] at this
    rw [this]
    push_cast
    linarith
  have h5 : κ * gaussI (1 / 2) (X ^ 5) = 0 := by
    have := gauss_half_succ 3
    rw [show (3 + 2 : ℕ) = 5 from rfl] at this
    rw [this]
    push_cast
    linarith
  have h6 : κ * gaussI (1 / 2) (X ^ 6) = 15 := by
    have := gauss_half_succ 4
    rw [show (4 + 2 : ℕ) = 6 from rfl] at this
    rw [this]
    push_cast
    linarith
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- The moments of the velocity factors `g₀`, `g₁`, `g₂`. -/
lemma momL_g₀ (k : ℕ) : momL k g₀ = κ * gaussI (1 / 2) (X ^ k) := by
  rw [momL_apply, vMean_eq, g₀, mul_smul_comm, mul_one, gaussI_smul]

lemma momL_g₁ (k : ℕ) : momL k g₁ = κ * gaussI (1 / 2) (X ^ (k + 1)) := by
  rw [momL_apply, vMean_eq, g₁, mul_smul_comm, gaussI_smul, pow_succ]

lemma momL_g₂ (k : ℕ) : momL k g₂ =
    (κ * gaussI (1 / 2) (X ^ (k + 2)) - κ * gaussI (1 / 2) (X ^ k)) / 2 := by
  have h : (X ^ k * (X ^ 2 - 1) : ℝ[X]) = X ^ (k + 2) + (-1 : ℝ) • X ^ k := by
    rw [smul_eq_C_mul]
    simp only [map_neg, map_one]
    ring
  rw [momL_apply, vMean_eq, g₂, mul_smul_comm, gaussI_smul, h, gaussI_add (by norm_num),
    gaussI_smul]
  ring

/-- The moments of the Maxwellian: `⟨M⟩ = ρ`, `⟨v M⟩ = ρ u`, `⟨v² M⟩ = ρ + ρ u²`, `⟨v³ M⟩ = 3 ρ u`,
`⟨v⁴ M⟩ = 3 ρ + 6 ρ u²`, in terms of `m = ρ u`, `q = ρ u²`. -/
lemma momL_table :
    (momL 0 g₀ = 1 ∧ momL 0 g₁ = 0 ∧ momL 0 g₂ = 0) ∧
    (momL 1 g₀ = 0 ∧ momL 1 g₁ = 1 ∧ momL 1 g₂ = 0) ∧
    (momL 2 g₀ = 1 ∧ momL 2 g₁ = 0 ∧ momL 2 g₂ = 1) ∧
    (momL 3 g₀ = 0 ∧ momL 3 g₁ = 3 ∧ momL 3 g₂ = 0) ∧
    (momL 4 g₀ = 3 ∧ momL 4 g₁ = 0 ∧ momL 4 g₂ = 6) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := gauss_half_table
  simp only [momL_g₀, momL_g₁, momL_g₂, zero_add, h0, h1, h2, h3, h4, h5, h6,
    show (1 + 1 : ℕ) = 2 from rfl, show (1 + 2 : ℕ) = 3 from rfl, show (2 + 2 : ℕ) = 4 from rfl,
    show (3 + 2 : ℕ) = 5 from rfl, show (4 + 2 : ℕ) = 6 from rfl]
  norm_num

/-- The Gaussian moments with weight `e^{-v²}` used for the `L²(ℝ)` inner product. -/
lemma gauss_one_table :
    gaussI 1 (X ^ 0) = √π ∧ gaussI 1 (X ^ 1) = 0 ∧ gaussI 1 (X ^ 2) = √π / 2 ∧
      gaussI 1 (X ^ 3) = 0 ∧ gaussI 1 (X ^ 4) = 3 * √π / 4 := by
  have h0 : gaussI 1 (X ^ 0) = √π := by
    rw [pow_zero, gaussI_one one_pos, div_one]
  have h1 : gaussI 1 (X ^ 1) = 0 := by
    rw [pow_one, gaussI_X one_pos]
  have hr := fun k => gaussI_X_pow_add_two (b := 1) one_pos k
  have h2 : gaussI 1 (X ^ 2) = √π / 2 := by
    have := hr 0
    simp only [zero_add] at this
    rw [this, h0]
    push_cast
    ring
  have h3 : gaussI 1 (X ^ 3) = 0 := by
    have := hr 1
    rw [show (1 + 2 : ℕ) = 3 from rfl, h1, mul_zero] at this
    exact this
  have h4 : gaussI 1 (X ^ 4) = 3 * √π / 4 := by
    have := hr 2
    rw [show (2 + 2 : ℕ) = 4 from rfl, h2] at this
    rw [this]
    push_cast
    ring
  exact ⟨h0, h1, h2, h3, h4⟩

/-! ### Polynomial degrees -/

lemma X_pow_mem_degreeLT {k n : ℕ} (h : k < n) : (X ^ k : ℝ[X]) ∈ degreeLT ℝ n := by
  rw [mem_degreeLT, degree_X_pow]
  exact_mod_cast h

lemma X_mul_mem_degreeLT {k : ℕ} {a : ℝ[X]} (ha : a ∈ degreeLT ℝ k) :
    X * a ∈ degreeLT ℝ (k + 1) := by
  rw [mem_degreeLT] at ha ⊢
  rw [degree_lt_iff_coeff_zero] at ha ⊢
  intro m hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [coeff_X_mul]
  exact ha m' (by omega)

lemma degreeLT_mono {k l : ℕ} (h : k ≤ l) : degreeLT ℝ k ≤ degreeLT ℝ l := by
  intro a ha
  rw [mem_degreeLT] at ha ⊢
  exact ha.trans_le (by exact_mod_cast h)

lemma g₀_mem : g₀ ∈ degreeLT ℝ 3 := by
  have : g₀ = κ • X ^ 0 := by simp [g₀]
  rw [this]
  exact Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num))

lemma g₁_mem : g₁ ∈ degreeLT ℝ 3 := by
  have : g₁ = κ • X ^ 1 := by simp [g₁]
  rw [this]
  exact Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num))

lemma g₂_mem : g₂ ∈ degreeLT ℝ 3 := by
  have : g₂ = (κ / 2) • (X ^ 2 - X ^ 0) := by simp [g₂]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (X_pow_mem_degreeLT (by norm_num))
    (X_pow_mem_degreeLT (by norm_num)))

/-! ### A dual basis of `g₀`, `g₁`, `g₂` -/

/-- `τ = 1/(κ √π)`. -/
noncomputable def τ : ℝ := (κ * √π)⁻¹

/-- Polynomials dual to `g₀`, `g₁`, `g₂` for `⟨· ·⟩ᵥ`. -/
noncomputable def e₀ : ℝ[X] := τ • X ^ 2 + (τ / 2) • X ^ 0

/-- See `e₀`. -/
noncomputable def e₁ : ℝ[X] := (2 * τ) • X ^ 1

/-- See `e₀`. -/
noncomputable def e₂ : ℝ[X] := (4 * τ) • X ^ 2 + (-(2 * τ)) • X ^ 0

lemma e₀_mem : e₀ ∈ degreeLT ℝ 3 :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num)))
    (Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num)))

lemma e₁_mem : e₁ ∈ degreeLT ℝ 3 :=
  Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num))

lemma e₂_mem : e₂ ∈ degreeLT ℝ 3 :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num)))
    (Submodule.smul_mem _ _ (X_pow_mem_degreeLT (by norm_num)))

lemma vIP_X_pow (a b : ℕ) : vIP (X ^ a) (X ^ b) = gaussI 1 (X ^ (a + b)) := by
  rw [vIP_eq, pow_add]

lemma τ_mul : τ * κ * √π = 1 := by
  have h : κ * √π ≠ 0 := (mul_pos κ_pos (Real.sqrt_pos.mpr Real.pi_pos)).ne'
  rw [τ, mul_assoc]
  exact inv_mul_cancel₀ h

lemma g₀_eq : g₀ = κ • X ^ 0 := by simp [g₀]

lemma g₁_eq : g₁ = κ • X ^ 1 := by simp [g₁]

lemma g₂_eq : g₂ = (κ / 2) • X ^ 2 + (-(κ / 2)) • X ^ 0 := by
  simp [g₂, sub_eq_add_neg, smul_add, smul_neg]

/-- The polynomials `e₀`, `e₁`, `e₂` are dual to `g₀`, `g₁`, `g₂` for `⟨· ·⟩ᵥ`. -/
lemma dual_table :
    (vIP e₀ g₀ = 1 ∧ vIP e₀ g₁ = 0 ∧ vIP e₀ g₂ = 0) ∧
    (vIP e₁ g₀ = 0 ∧ vIP e₁ g₁ = 1 ∧ vIP e₁ g₂ = 0) ∧
    (vIP e₂ g₀ = 0 ∧ vIP e₂ g₁ = 0 ∧ vIP e₂ g₂ = 1) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := gauss_one_table
  have ht := τ_mul
  simp only [← vIPL_apply, e₀, e₁, e₂, g₀_eq, g₁_eq, g₂_eq, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  simp only [vIPL_apply, vIP_X_pow, show (2 + 0 : ℕ) = 2 from rfl, show (0 + 0 : ℕ) = 0 from rfl,
    show (2 + 1 : ℕ) = 3 from rfl, show (0 + 1 : ℕ) = 1 from rfl, show (2 + 2 : ℕ) = 4 from rfl,
    h0, h1, h2, h3, h4]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    first
      | ring1
      | linear_combination ht

/-! ### Hermite functions -/

/-- The physicists' Hermite polynomials `H₀ = 1`, `H₁ = 2 v`, `H₂ = 4 v² - 2`, `H₃ = 8 v³ - 12 v`,
…, as in the proof of Theorem 5.1. -/
noncomputable def physH : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (2 : ℝ) • (X * physH n) - derivative (physH n)

lemma physH_succ (n : ℕ) :
    physH (n + 1) = (2 : ℝ) • (X * physH n) - derivative (physH n) := rfl

lemma derivative_physH (n : ℕ) :
    derivative (physH (n + 1)) = (2 * ((n : ℝ) + 1)) • physH n := by
  induction n with
  | zero =>
    simp [physH]
  | succ n ih =>
    have h1 : derivative (physH (n + 1 + 1)) =
        (2 : ℝ) • (physH (n + 1) + X * derivative (physH (n + 1))) -
          derivative (derivative (physH (n + 1))) := by
      rw [physH_succ (n + 1)]
      simp [derivative_mul]
    rw [h1, ih, derivative_smul, mul_smul_comm, physH_succ n]
    push_cast
    module

/-- The three-term recurrence of the Hermite polynomials. -/
lemma physH_rec (n : ℕ) :
    physH (n + 2) = (2 : ℝ) • (X * physH (n + 1)) - (2 * ((n : ℝ) + 1)) • physH n := by
  rw [physH_succ (n + 1), derivative_physH]

/-- Integration by parts: `⟨p H_{n+1}⟩ = ⟨p' H_n⟩` for the weight `e^{-v²}`. -/
lemma vIP_physH_succ (p : ℝ[X]) (n : ℕ) :
    vIP p (physH (n + 1)) = vIP (derivative p) (physH n) := by
  have hS := gaussI_derivative one_pos (p * physH n)
  rw [derivative_mul, gaussI_add one_pos] at hS
  have h1 : p * physH (n + 1) =
      (2 : ℝ) • (X * (p * physH n)) + (-1 : ℝ) • (p * derivative (physH n)) := by
    rw [physH_succ, mul_sub, mul_smul_comm]
    have : p * (X * physH n) = X * (p * physH n) := by ring
    rw [this]
    module
  rw [vIP_eq, vIP_eq, h1, gaussI_add one_pos, gaussI_smul, gaussI_smul]
  linarith

lemma vIP_physH (p : ℝ[X]) (n : ℕ) : vIP p (physH n) = vIP (derivative^[n] p) 1 := by
  induction n generalizing p with
  | zero => simp [physH]
  | succ n ih =>
    rw [vIP_physH_succ, ih, Function.iterate_succ_apply]

lemma iterate_derivative_physH (n : ℕ) :
    derivative^[n] (physH n) = ((2 : ℝ) ^ n * (n.factorial : ℝ)) • 1 := by
  induction n with
  | zero => simp [physH]
  | succ n ih =>
    rw [Function.iterate_succ_apply, derivative_physH, iterate_derivative_smul, ih, smul_smul,
      Nat.factorial_succ]
    push_cast
    congr 1
    ring

lemma iterate_derivative_physH_of_lt {i j : ℕ} (h : i < j) : derivative^[j] (physH i) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = (k + 1) + i := ⟨j - i - 1, by omega⟩
  rw [Function.iterate_add_apply, iterate_derivative_physH, Function.iterate_succ_apply,
    derivative_smul, derivative_one, smul_zero, iterate_derivative_zero]

/-- The Hermite polynomials are orthogonal for the weight `e^{-v²}`. -/
lemma vIP_physH_physH (i j : ℕ) : vIP (physH i) (physH j) =
    if i = j then (2 : ℝ) ^ i * (i.factorial : ℝ) * √π else 0 := by
  split_ifs with hij
  · subst hij
    rw [vIP_physH, iterate_derivative_physH, vIP_eq, mul_one, gaussI_smul, gaussI_one one_pos,
      div_one]
  · rcases lt_or_gt_of_ne hij with h | h
    · rw [vIP_physH, iterate_derivative_physH_of_lt h]
      simp [vIP_eq, gaussI]
    · rw [vIP_comm, vIP_physH, iterate_derivative_physH_of_lt h]
      simp [vIP_eq, gaussI]

/-- The normalization `αₖ₊₁ = (2ᵏ k! √π)^{-1/2}` of Theorem 5.1. -/
noncomputable def hAlpha (k : ℕ) : ℝ := (√((2 : ℝ) ^ k * (k.factorial : ℝ) * √π))⁻¹

lemma hAlpha_pos (k : ℕ) : 0 < hAlpha k := by
  have h : 0 < (2 : ℝ) ^ k * (k.factorial : ℝ) * √π := by
    have := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  exact inv_pos.mpr (Real.sqrt_pos.mpr h)

/-- The Hermite functions `V_{k+1}(v) = α_{k+1} H_k(v) e^{-v²/2}` of the proof of Theorem 5.1 of
arXiv 2502.08951, represented by their polynomial factor. -/
noncomputable def hermiteP (k : ℕ) : ℝ[X] := hAlpha k • physH k

/-- The Hermite functions are orthonormal in `L²(ℝ, dv)`. -/
lemma vIP_hermiteP (i j : ℕ) : vIP (hermiteP i) (hermiteP j) = if i = j then 1 else 0 := by
  simp only [← vIPL_apply, hermiteP, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [vIPL_apply, vIP_physH_physH]
  split_ifs with h
  · subst h
    have hc : 0 < (2 : ℝ) ^ i * (i.factorial : ℝ) * √π := by
      have := Real.sqrt_pos.mpr Real.pi_pos
      positivity
    have h1 := Real.mul_self_sqrt hc.le
    have h2 : √((2 : ℝ) ^ i * (i.factorial : ℝ) * √π) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
    rw [hAlpha]
    field_simp
    nlinarith
  · simp

/-- The recurrence (5.13) of arXiv 2502.08951 for the Hermite functions, `j ≥ 2`:
`v V_j = C_{j+1} V_{j+1} + D_{j-1} V_{j-1}`, `C_{j+1} = α_j/(2 α_{j+1})`,
`D_{j-1} = α_j (j - 1)/α_{j-1}`, in the index `k = j - 2`. -/
theorem hermite_recurrence (k : ℕ) :
    X * hermiteP (k + 1) = (hAlpha (k + 1) / (2 * hAlpha (k + 2))) • hermiteP (k + 2) +
      (hAlpha (k + 1) * ((k : ℝ) + 1) / hAlpha k) • hermiteP k := by
  have h1 := (hAlpha_pos k).ne'
  have h2 := (hAlpha_pos (k + 2)).ne'
  simp only [hermiteP, smul_smul, physH_rec k, mul_smul_comm, smul_sub]
  have e1 : hAlpha (k + 1) / (2 * hAlpha (k + 2)) * (hAlpha (k + 2) * 2) = hAlpha (k + 1) := by
    field_simp
  have e2 : hAlpha (k + 1) * ((k : ℝ) + 1) / hAlpha k * hAlpha k =
      hAlpha (k + 1) * ((k : ℝ) + 1) := by
    field_simp
  have e3 : hAlpha (k + 1) / (2 * hAlpha (k + 2)) * (hAlpha (k + 2) * (2 * ((k : ℝ) + 1))) =
      hAlpha (k + 1) * ((k : ℝ) + 1) := by
    field_simp
  rw [e1, e2, e3]
  abel

/-- arXiv 2502.08951, `v V₁ = C₂ V₂`, the first case of (5.13). -/
theorem hermite_recurrence_zero :
    X * hermiteP 0 = (hAlpha 0 / (2 * hAlpha 1)) • hermiteP 1 := by
  have h2 := (hAlpha_pos 1).ne'
  simp only [hermiteP, smul_smul]
  have e1 : hAlpha 0 / (2 * hAlpha 1) * hAlpha 1 = hAlpha 0 / 2 := by
    field_simp
  rw [e1, physH_succ 0]
  simp only [physH, derivative_one, sub_zero, mul_smul_comm, smul_smul]
  congr 1
  ring

lemma coeff_physH (n : ℕ) : (physH n).coeff n = 2 ^ n ∧ ∀ m, n < m → (physH n).coeff m = 0 := by
  induction n with
  | zero =>
    refine ⟨by simp [physH], fun m hm => ?_⟩
    simp [physH, coeff_one, hm.ne']
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hc : ∀ m, (physH (n + 1)).coeff (m + 1) =
        2 * (physH n).coeff m - (physH n).coeff (m + 2) * ((m : ℝ) + 1 + 1) := by
      intro m
      rw [physH_succ]
      simp [coeff_X_mul, coeff_derivative]
    refine ⟨?_, fun m hm => ?_⟩
    · rw [hc n, h1, h2 _ (by omega)]
      ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hc m', h2 _ (by omega), h2 _ (by omega)]
      ring

/-- The polynomials of degree `< k` are the span of `H₀, …, H_{k-1}`. -/
lemma degreeLT_le_span_physH (k : ℕ) :
    degreeLT ℝ k ≤ Submodule.span ℝ (physH '' Set.Iio k) := by
  induction k with
  | zero =>
    intro a ha
    have : a = 0 := by
      rw [mem_degreeLT] at ha
      simpa using ha
    rw [this]
    exact Submodule.zero_mem _
  | succ k ih =>
    intro a ha
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    obtain ⟨h1, h2⟩ := coeff_physH k
    set c := a.coeff k / 2 ^ k with hc
    have hq : a - c • physH k ∈ degreeLT ℝ k := by
      rw [mem_degreeLT, degree_lt_iff_coeff_zero]
      intro m hm
      rw [mem_degreeLT, degree_lt_iff_coeff_zero] at ha
      rcases hm.eq_or_lt with rfl | hm'
      · simp [h1, hc, h2k]
      · simp [h2 m hm', ha m (by omega)]
    have hmono : Submodule.span ℝ (physH '' Set.Iio k) ≤
        Submodule.span ℝ (physH '' Set.Iio (k + 1)) :=
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
    have hk : physH k ∈ Submodule.span ℝ (physH '' Set.Iio (k + 1)) :=
      Submodule.subset_span ⟨k, by simp, rfl⟩
    have := Submodule.add_mem _ (hmono (ih hq)) (Submodule.smul_mem _ c hk)
    simpa using this

/-- The first `k` Hermite functions span the polynomials of degree `< k`. -/
lemma degreeLT_le_span_hermite {k r : ℕ} (hk : k ≤ r) :
    degreeLT ℝ k ≤ Submodule.span ℝ (Set.range fun j : Fin r => hermiteP j) := by
  refine (degreeLT_le_span_physH k).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < r := lt_of_lt_of_le hi hk
  have h : physH i = (hAlpha i)⁻¹ • hermiteP i := by
    rw [hermiteP, smul_smul, inv_mul_cancel₀ (hAlpha_pos i).ne', one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩)

end Gaussian

section Scheme

open Polynomial

variable {Ex Ω : Type*} [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] {r t : ℕ}

/-- Orthonormality of velocity functions in `L²(ℝ, dv)`. -/
def VOrthonormal {ι : Type*} [DecidableEq ι] (V : ι → ℝ[X]) : Prop :=
  ∀ i j, vIP (V i) (V j) = if i = j then 1 else 0

/-- The `x`-function `⟨vᵏ f⟩ᵥ = ∑ⱼ ⟨vᵏ Vⱼ⟩ᵥ Kⱼ` of `f = ∑ⱼ Kⱼ Vⱼ`. -/
noncomputable def moment {ι : Type*} [Fintype ι] (k : ℕ) (K : ι → Ex) (V : ι → ℝ[X]) : Ex :=
  ∑ j, vMean (X ^ k * V j) • K j

/-- The value `f(x, v) = ∑ⱼ Kⱼ(x) Vⱼ(v)`; `ev y x` is the value at `x` of the `x`-function `y`. -/
noncomputable def fval {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex) (V : ι → ℝ[X])
    (x : Ω) (v : ℝ) : ℝ :=
  ∑ j, ev (K j) x * gaussFn (V j) v

/-- The density `ρ(x) = ∫ f(x, v) dv`, (5.2). -/
noncomputable def density {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex)
    (V : ι → ℝ[X]) (x : Ω) : ℝ :=
  ∫ v : ℝ, fval ev K V x v

/-- The bulk velocity `u(x) = ρ(x)⁻¹ ∫ v f(x, v) dv`, (5.2). -/
noncomputable def meanVelocity {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex)
    (V : ι → ℝ[X]) (x : Ω) : ℝ :=
  (∫ v : ℝ, v * fval ev K V x v) / density ev K V x

/-- The two variants of Step 4. -/
inductive Variant
  | XL
  | sXL

/-- All intermediate quantities of one step of the low-rank scheme of Section 5: Steps 1–3
((4.16)–(4.18)) and Steps 4–6 ((5.6)–(5.10), truncation). -/
structure StepData (Ex : Type*) (r t : ℕ) where
  /-- `X*`. -/
  Xs : Fin r → Ex
  /-- `S⁽¹⁾`. -/
  S₁ : Matrix (Fin r) (Fin r) ℝ
  /-- `S⁽²⁾`. -/
  S₂ : Matrix (Fin r) (Fin r) ℝ
  /-- `S*`. -/
  Ss : Matrix (Fin r) (Fin r) ℝ
  /-- `V*`. -/
  Vs : Fin r → ℝ[X]
  /-- The `x`-function `ρ* (u*)²` of (5.7). -/
  qs : Ex
  /-- `K⁽⁴⁾` of (5.8), which only XL uses. -/
  K₄ : Fin r → Ex
  /-- `X̂ⁿ⁺¹`. -/
  Xh : Fin (r + t) → Ex
  /-- `L̂ⁿ⁺¹`. -/
  Lh : Fin (r + t) → ℝ[X]
  /-- `Ŝⁿ⁺¹`. -/
  Sh : Matrix (Fin (r + t)) (Fin (r + t)) ℝ
  /-- `V̂ⁿ⁺¹`. -/
  Vh : Fin (r + t) → ℝ[X]
  /-- `X_s`. -/
  Us : Matrix (Fin (r + t)) (Fin (r + t)) ℝ
  /-- `V_s`. -/
  Ws : Matrix (Fin (r + t)) (Fin (r + t)) ℝ
  /-- The diagonal of `Σ_s`. -/
  σ : Fin (r + t) → ℝ

namespace StepData

/-- `K*ⱼ = ∑ᵢ X*ᵢ S*ᵢⱼ`, (5.6). -/
noncomputable def Ks (d : StepData Ex r t) (j : Fin r) : Ex := ∑ i, d.Ss i j • d.Xs i

/-- `ρ* = ∑ⱼ K*ⱼ ⟨V*ⱼ⟩ᵥ`, (5.7). -/
noncomputable def ρs (d : StepData Ex r t) : Ex := moment 0 d.Ks d.Vs

/-- `ρ* u* = ∑ⱼ K*ⱼ ⟨v V*ⱼ⟩ᵥ`, (5.7). -/
noncomputable def ms (d : StepData Ex r t) : Ex := moment 1 d.Ks d.Vs

/-- `⟨M* a⟩ᵥ` for the velocity function `a`, with `M*` of (5.7). -/
noncomputable def MV (d : StepData Ex r t) (a : ℝ[X]) : Ex :=
  vIP g₀ a • d.ρs + vIP g₁ a • d.ms + vIP g₂ a • d.qs

/-- `⟨y M*⟩ₓ` for the `x`-function `y`, with `M*` of (5.7). -/
noncomputable def MX (d : StepData Ex r t) (y : Ex) : ℝ[X] :=
  ⟪y, d.ρs⟫ • g₀ + ⟪y, d.ms⟫ • g₁ + ⟪y, d.qs⟫ • g₂

/-- `L⁽²⁾ᵢ = ∑ⱼ S⁽²⁾ᵢⱼ Vⱼ`. -/
noncomputable def L₂ (d : StepData Ex r t) (V : Fin r → ℝ[X]) (i : Fin r) : ℝ[X] :=
  ∑ j, d.S₂ i j • V j

/-- The functions added to the basis `X*` in Step 4: `K⁽⁴⁾` for XL, (5.8); `⟨M* V*⟩ᵥ` for sXL,
(5.9). -/
noncomputable def aug (d : StepData Ex r t) : Variant → Fin r → Ex
  | .XL, j => d.K₄ j
  | .sXL, j => d.MV (d.Vs j)

/-- Steps 1 and 2 of the low-rank scheme of Section 5 of arXiv 2502.08951, from `f = ∑ⱼ Kⱼ Vⱼ`.
`D` is the operator `∂ₓ`. -/
structure IsKSStep (d : StepData Ex r t) (D : Ex →ₗ[ℝ] Ex) (Δt : ℝ) (K : Fin r → Ex)
    (V : Fin r → ℝ[X]) : Prop where
  /-- The velocity basis at the start of the step. -/
  orth_V : VOrthonormal V
  /-- The "proper" basis of the paper's proof: it contains `V₁, …, V₆`, which forces `r ≥ 6`. -/
  proper_V : degreeLT ℝ 6 ≤ Submodule.span ℝ (Set.range V)
  /-- Step 1, (4.16): the K-step and the QR decomposition `K⁽¹⁾ = X* S⁽¹⁾`. -/
  orth_Xs : Orthonormal ℝ d.Xs
  kstep : ∀ j, ∑ i, d.S₁ i j • d.Xs i = K j - Δt • ∑ l, vIP (X * V j) (V l) • D (K l)
  /-- Step 2, (4.17). -/
  sstep : ∀ i j, d.S₂ i j = d.S₁ i j +
    Δt * ∑ k, ∑ l, vIP (X * V j) (V l) * ⟪d.Xs i, D (d.Xs k)⟫ * d.S₁ k l

/-- One step of the low-rank scheme of Section 5 of arXiv 2502.08951 from `f = ∑ⱼ Kⱼ Vⱼ` to
`f' = ∑ⱼ K'ⱼ V'ⱼ`. `ev` evaluates `x`-functions at points, and `ε ≥ 0` (equations (5.8), (5.10) are
multiplied by `ε Δt`; `ε = 0` is the limit scheme). -/
structure IsLowRankBGKStep (d : StepData Ex r t) (ev : Ex →ₗ[ℝ] Ω → ℝ) (D : Ex →ₗ[ℝ] Ex) (ε Δt : ℝ)
    (sch : Variant) (K : Fin r → Ex) (V : Fin r → ℝ[X]) (K' : Fin r → Ex) (V' : Fin r → ℝ[X]) :
    Prop extends d.IsKSStep D Δt K V where
  /-- Step 3, (4.18), and the QR decomposition `L* = S* V*`. -/
  orth_Vs : VOrthonormal d.Vs
  lstep : ∀ i, ∑ j, d.Ss i j • d.Vs j =
    d.L₂ V i - Δt • ∑ k, ⟪d.Xs i, D (d.Xs k)⟫ • (X * d.L₂ V k)
  /-- The "proper QR decomposition": `V*` contains the velocity factors of the Maxwellian. The
  paper takes `V* = Vⁿ`. -/
  proper_Vs : degreeLT ℝ 3 ≤ Submodule.span ℝ (Set.range d.Vs)
  /-- Step 4, (5.7): the density does not vanish, so that `u* = (ρ* u*)/ρ*` is defined, and `qs` is
  the `x`-function `ρ* (u*)²`. -/
  rho_ne : ∀ x, ev d.ρs x ≠ 0
  qs_eq : ∀ x, ev d.qs x * ev d.ρs x = ev d.ms x ^ 2
  /-- (5.8). -/
  xstep : ∀ j, ε • (d.K₄ j - d.Ks j) = Δt • (d.MV (d.Vs j) - d.K₄ j)
  /-- (5.8) or (5.9): `X̂ = orth[X*, …]`. -/
  orth_Xh : Orthonormal ℝ d.Xh
  Xh_left : ∀ i, d.Xh (Fin.castAdd t i) = d.Xs i
  augment : ∀ j, d.aug sch j ∈ Submodule.span ℝ (Set.range d.Xh)
  /-- Step 5, (5.10), for `i ≤ r`, and for `i > r`. -/
  hlstep_left : ∀ i, ε • (d.Lh (Fin.castAdd t i) - ∑ j, d.Ss i j • d.Vs j) =
    Δt • (d.MX (d.Xh (Fin.castAdd t i)) - d.Lh (Fin.castAdd t i))
  hlstep_right : ∀ i, ε • d.Lh (Fin.natAdd r i) =
    Δt • (d.MX (d.Xh (Fin.natAdd r i)) - d.Lh (Fin.natAdd r i))
  /-- `L̂ⁿ⁺¹ = Ŝⁿ⁺¹ V̂ⁿ⁺¹`. -/
  orth_Vh : VOrthonormal d.Vh
  qr : ∀ i, d.Lh i = ∑ j, d.Sh i j • d.Vh j
  /-- Step 6: the SVD `Ŝⁿ⁺¹ = X_s Σ_s V_sᵀ` with sorted nonnegative singular values. -/
  orth_Us : d.Usᵀ * d.Us = 1
  orth_Ws : d.Wsᵀ * d.Ws = 1
  svd : d.Sh = d.Us * Matrix.diagonal d.σ * d.Wsᵀ
  sorted : Antitone d.σ
  nonneg : ∀ i, 0 ≤ d.σ i
  /-- The truncated factors: `Kⁿ⁺¹ⱼ = Xⁿ⁺¹ⱼ σⱼ` with `Xⁿ⁺¹ = X̂ X_s(:, 1:r)`, and
  `Vⁿ⁺¹ = V̂ V_s(:, 1:r)`. -/
  K_out : ∀ j, K' j = d.σ (Fin.castAdd t j) • ∑ i, d.Us i (Fin.castAdd t j) • d.Xh i
  V_out : ∀ j, V' j = ∑ i, d.Ws i (Fin.castAdd t j) • d.Vh i

end StepData

/-! ### Tensors as maps on functionals -/

/-- `⟨ℓ, f⟩ = ∑ⱼ ℓ(Vⱼ) Kⱼ`: the `x`-function obtained by applying the functional `ℓ` in the velocity
variable to `f = ∑ⱼ Kⱼ Vⱼ`.  The tensor `f` is determined by these. -/
noncomputable def ctr {ι : Type*} [Fintype ι] (K : ι → Ex) (V : ι → ℝ[X])
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) : Ex :=
  ∑ j, ℓ (V j) • K j

lemma moment_eq_ctr {ι : Type*} [Fintype ι] (k : ℕ) (K : ι → Ex) (V : ι → ℝ[X]) :
    moment k K V = ctr K V (momL k) := by
  simp [moment, ctr]

/-- `ℓ ∘ (v ·)`. -/
noncomputable def shift (ℓ : ℝ[X] →ₗ[ℝ] ℝ) : ℝ[X] →ₗ[ℝ] ℝ := ℓ ∘ₗ LinearMap.mulLeft ℝ X

@[simp] lemma shift_apply (ℓ : ℝ[X] →ₗ[ℝ] ℝ) (a : ℝ[X]) : shift ℓ a = ℓ (X * a) := by
  simp [shift]

lemma shift_momL (k : ℕ) : shift (momL k) = momL (k + 1) := by
  refine LinearMap.ext fun a => ?_
  simp only [shift_apply, momL_apply]
  congr 1
  ring

/-- `∑ⱼ ⟨Vⱼ a⟩ᵥ Vⱼ`, the orthogonal projection on the span of `V`. -/
noncomputable def vProj {ι : Type*} [Fintype ι] (V : ι → ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  ∑ j, (vIPL (V j)).smulRight (V j)

lemma vProj_apply {ι : Type*} [Fintype ι] (V : ι → ℝ[X]) (a : ℝ[X]) :
    vProj V a = ∑ j, vIP (V j) a • V j := by
  simp [vProj, LinearMap.sum_apply]

lemma vProj_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → ℝ[X]} (hV : VOrthonormal V)
    {a : ℝ[X]} (ha : a ∈ Submodule.span ℝ (Set.range V)) : vProj V a = a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp ha
  rw [vProj_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [← vIPL_apply, map_sum, map_smul, smul_eq_mul]
  simp [vIPL_apply, hV j]

/-- `∑ᵢ ⟪Yᵢ, y⟫ Yᵢ`, the orthogonal projection on the span of an orthonormal family. -/
noncomputable def Px {ι : Type*} [Fintype ι] (Y : ι → Ex) : Ex →ₗ[ℝ] Ex where
  toFun y := ∑ i, ⟪Y i, y⟫ • Y i
  map_add' x y := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [inner_smul_right, mul_smul, Finset.smul_sum]

lemma Px_apply {ι : Type*} [Fintype ι] (Y : ι → Ex) (y : Ex) :
    Px Y y = ∑ i, ⟪Y i, y⟫ • Y i := rfl

lemma Px_of_mem {ι : Type*} [Fintype ι] {Y : ι → Ex} (hY : Orthonormal ℝ Y) {y : Ex}
    (hy : y ∈ Submodule.span ℝ (Set.range Y)) : Px Y y = y := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  rw [Px_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hY.inner_right_fintype]

lemma norm_Px_le {ι : Type*} [Fintype ι] {Y : ι → Ex} (hY : Orthonormal ℝ Y) (y : Ex) :
    ‖Px Y y‖ ≤ ‖y‖ := by
  have h1 : ‖Px Y y‖ ^ 2 = ∑ i, ‖⟪Y i, y⟫‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Px_apply, hY.inner_sum]
    simp [sq]
  have h2 := hY.sum_inner_products_le (x := y) (s := Finset.univ)
  rw [← h1] at h2
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

lemma ctr_factor {ι κ' : Type*} [Fintype ι] [Fintype κ'] (S : Matrix ι κ' ℝ) (Y : ι → Ex)
    (W : κ' → ℝ[X]) (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr (fun j => ∑ i, S i j • Y i) W ℓ = ctr Y (fun i => ∑ j, S i j • W j) ℓ := by
  simp only [ctr, map_sum, map_smul, smul_eq_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- The K-step in terms of functionals. -/
lemma ctr_kstep {ι : Type*} [Fintype ι] {K K₁ : ι → Ex} {V : ι → ℝ[X]} {c : ℝ}
    (G : Ex →ₗ[ℝ] Ex) (hK : ∀ j, K₁ j = K j + c • ∑ l, vIP (X * V j) (V l) • G (K l))
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr K₁ V ℓ = ctr K V ℓ + c • G (ctr K V (shift (ℓ ∘ₗ vProj V))) := by
  have hℓ : ∀ l, shift (ℓ ∘ₗ vProj V) (V l) = ∑ j, vIP (V j) (X * V l) * ℓ (V j) := by
    intro l
    simp [vProj_apply, map_sum]
  have h2 : ∑ j, ℓ (V j) • (c • ∑ l, vIP (X * V j) (V l) • G (K l)) =
      c • G (ctr K V (shift (ℓ ∘ₗ vProj V))) := by
    simp only [ctr, map_sum, map_smul, hℓ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    rw [vIP_X_left]
    congr 1
    ring
  simp only [ctr] at h2 ⊢
  simp only [hK, smul_add, Finset.sum_add_distrib, h2]

/-- `T` depends on a functional only through its restriction to polynomials of degree `< k`: the
tensor lies in `Ex ⊗ span(V₁, …, V_k)`. -/
def Supp (T : (ℝ[X] →ₗ[ℝ] ℝ) → Ex) (k : ℕ) : Prop :=
  ∀ ℓ ℓ' : ℝ[X] →ₗ[ℝ] ℝ, (∀ a ∈ degreeLT ℝ k, ℓ a = ℓ' a) → T ℓ = T ℓ'

omit [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] in
lemma Supp.shift {T : (ℝ[X] →ₗ[ℝ] ℝ) → Ex} {k : ℕ} (h : Supp T k) {ℓ ℓ' : ℝ[X] →ₗ[ℝ] ℝ}
    (hℓ : ∀ a ∈ degreeLT ℝ (k + 1), ℓ a = ℓ' a) : T (shift ℓ) = T (shift ℓ') :=
  h _ _ fun a ha => by simpa using hℓ _ (X_mul_mem_degreeLT ha)

omit [NormedAddCommGroup Ex] [InnerProductSpace ℝ Ex] in
/-- If `Supp T k` and `span V` contains the polynomials of degree `≤ k`, the projection on `span V`
after the multiplication by `v` does nothing to `T`. -/
lemma Supp.vProj {ι : Type*} [Fintype ι] [DecidableEq ι] {T : (ℝ[X] →ₗ[ℝ] ℝ) → Ex} {k : ℕ}
    (h : Supp T k) {V : ι → ℝ[X]} (hV : VOrthonormal V)
    (hW : degreeLT ℝ (k + 1) ≤ Submodule.span ℝ (Set.range V)) (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    T (P2502_08951.shift (ℓ ∘ₗ P2502_08951.vProj V)) = T (P2502_08951.shift ℓ) :=
  h _ _ fun a ha => by
    simp only [shift_apply, LinearMap.comp_apply]
    rw [vProj_of_mem hV (hW (X_mul_mem_degreeLT ha))]


lemma supp_of_step {T T' : (ℝ[X] →ₗ[ℝ] ℝ) → Ex} {k : ℕ} {c : ℝ} (G : Ex →ₗ[ℝ] Ex)
    (hT : Supp T k) (h : ∀ ℓ, T' ℓ = T ℓ + c • G (T (shift ℓ))) : Supp T' (k + 1) := by
  intro ℓ ℓ' hℓ
  rw [h, h, hT ℓ ℓ' fun a ha => hℓ a (degreeLT_mono (Nat.le_succ k) ha), hT.shift hℓ]

namespace StepData

variable {d : StepData Ex r t} {ev : Ex →ₗ[ℝ] Ω → ℝ} {D : Ex →ₗ[ℝ] Ex} {ε Δt : ℝ} {sch : Variant}
  {K K' : Fin r → Ex} {V V' : Fin r → ℝ[X]}

/-- `K⁽¹⁾ⱼ = ∑ᵢ S⁽¹⁾ᵢⱼ X*ᵢ`. -/
noncomputable def K₁ (d : StepData Ex r t) (j : Fin r) : Ex := ∑ i, d.S₁ i j • d.Xs i

/-- `K⁽²⁾ⱼ = ∑ᵢ S⁽²⁾ᵢⱼ X*ᵢ`. -/
noncomputable def K₂ (d : StepData Ex r t) (j : Fin r) : Ex := ∑ i, d.S₂ i j • d.Xs i

/-- Step 1 on functionals: for a tensor in `Ex ⊗ span(V₁, V₂, V₃)` the K-step is the full advection
step `f⁽¹⁾ = fⁿ - Δt v ∂ₓ fⁿ`: the proof of (5.15). -/
lemma IsKSStep.ctr_K₁ (h : d.IsKSStep D Δt K V) (hT : Supp (ctr K V) 3)
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr d.K₁ V ℓ = ctr K V ℓ + (-Δt) • D (ctr K V (shift ℓ)) := by
  have hK : ∀ j, d.K₁ j = K j + (-Δt) • ∑ l, vIP (X * V j) (V l) • D (K l) := fun j => by
    rw [K₁, h.kstep j, neg_smul, sub_eq_add_neg]
  rw [ctr_kstep D hK ℓ, hT.vProj h.orth_V ((degreeLT_mono (by norm_num)).trans h.proper_V) ℓ]

/-- The S-step as a Galerkin step: `K⁽²⁾ⱼ = K⁽¹⁾ⱼ + Δt ∑ₗ ⟨v Vⱼ Vₗ⟩ P ∂ₓ K⁽¹⁾ₗ`. -/
lemma IsKSStep.K₂_eq (h : d.IsKSStep D Δt K V) (j : Fin r) :
    d.K₂ j = d.K₁ j + Δt • ∑ l, vIP (X * V j) (V l) • (Px d.Xs ∘ₗ D) (d.K₁ l) := by
  have key : ∀ l, (Px d.Xs ∘ₗ D) (d.K₁ l) =
      ∑ i, (∑ k, d.S₁ k l * ⟪d.Xs i, D (d.Xs k)⟫) • d.Xs i := by
    intro l
    simp only [K₁, LinearMap.comp_apply, Px_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  have hK₁ : d.K₁ j = ∑ i, d.S₁ i j • d.Xs i := rfl
  simp only [K₂, key, h.sstep, add_smul, Finset.sum_add_distrib, hK₁]
  congr 1
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- Step 2 on functionals. -/
lemma IsKSStep.ctr_K₂ (h : d.IsKSStep D Δt K V) (hT : Supp (ctr K V) 3)
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr d.K₂ V ℓ = ctr d.K₁ V ℓ + Δt • (Px d.Xs ∘ₗ D) (ctr d.K₁ V (shift ℓ)) := by
  have hs : Supp (ctr d.K₁ V) 4 := supp_of_step D hT (h.ctr_K₁ hT)
  rw [ctr_kstep (Px d.Xs ∘ₗ D) h.K₂_eq ℓ,
    hs.vProj h.orth_V ((degreeLT_mono (by norm_num)).trans h.proper_V) ℓ]

/-- Step 3 on functionals. -/
lemma IsLowRankBGKStep.ctr_Ks (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr d.Ks d.Vs ℓ = ctr d.K₂ V ℓ + (-Δt) • (Px d.Xs ∘ₗ D) (ctr d.K₂ V (shift ℓ)) := by
  have h1 : ctr d.Ks d.Vs ℓ = ctr d.Xs (fun i => ∑ j, d.Ss i j • d.Vs j) ℓ :=
    ctr_factor d.Ss d.Xs d.Vs ℓ
  have h2 : ∀ ℓ', ctr d.K₂ V ℓ' = ctr d.Xs (d.L₂ V) ℓ' := fun ℓ' => ctr_factor d.S₂ d.Xs V ℓ'
  have key : ∀ ℓ', (Px d.Xs ∘ₗ D) (ctr d.Xs (d.L₂ V) ℓ') =
      ∑ i, (∑ k, ⟪d.Xs i, D (d.Xs k)⟫ * ℓ' (d.L₂ V k)) • d.Xs i := by
    intro ℓ'
    simp only [ctr, LinearMap.comp_apply, Px_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h1, h2, h2, key]
  simp only [ctr, h.lstep, map_sub, map_smul, map_sum, smul_eq_mul, shift_apply, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← Finset.mul_sum]
  module

/-- arXiv 2502.08951, **The moment identity behind (5.15)–(5.25)**: for a tensor in `Ex ⊗ span(V₁,
V₂, V₃)`, Steps 1–3 give exactly `⟨ℓ, f*⟩ = ⟨ℓ, f⟩ - Δt ∂ₓ⟨v ℓ, f⟩ - Δt² P ∂ₓ P ∂ₓ (⟨v² ℓ, f⟩ - Δt
∂ₓ ⟨v³ ℓ, f⟩)`, where `P` is the orthogonal projection on `span X*`. -/
theorem IsLowRankBGKStep.ctr_Ks_eq (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V')
    (hT : Supp (ctr K V) 3) (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr d.Ks d.Vs ℓ = ctr K V ℓ - Δt • D (ctr K V (shift ℓ)) -
      Δt ^ 2 • Px d.Xs (D (Px d.Xs (D (ctr K V (shift (shift ℓ)) -
        Δt • D (ctr K V (shift (shift (shift ℓ)))))))) := by
  have h' := h.toIsKSStep
  rw [h.ctr_Ks, h'.ctr_K₂ hT, h'.ctr_K₂ hT, h'.ctr_K₁ hT, h'.ctr_K₁ hT, h'.ctr_K₁ hT]
  simp only [map_add, map_smul, map_sub, LinearMap.comp_apply]
  module

/-- arXiv 2502.08951, `L⁽²⁾ᵢ ∈ span(V₁, …, V₅)`, the consequence of (5.23) in the proof of Theorem
5.1. -/
theorem IsKSStep.L₂_mem (h : d.IsKSStep D Δt K V) (hT : Supp (ctr K V) 3) (i : Fin r) :
    d.L₂ V i ∈ degreeLT ℝ 5 := by
  by_contra hne
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hne
  have hs1 : Supp (ctr d.K₁ V) 4 := supp_of_step D hT (h.ctr_K₁ hT)
  have hs2 : Supp (ctr d.K₂ V) 5 := supp_of_step (Px d.Xs ∘ₗ D) hs1 (h.ctr_K₂ hT)
  have h0 := hs2 f 0 fun a ha => by simpa using LinearMap.mem_ker.mp (hker ha)
  have h1 : ctr d.K₂ V f = ctr d.Xs (d.L₂ V) f := ctr_factor d.S₂ d.Xs V f
  have h2 : ctr d.K₂ V 0 = 0 := by simp [ctr]
  have h3 : ⟪d.Xs i, ctr d.Xs (d.L₂ V) f⟫ = f (d.L₂ V i) := h.orth_Xs.inner_right_fintype _ _
  rw [← h1, h0, h2, inner_zero_right] at h3
  exact hf h3.symm

/-- arXiv 2502.08951, `L*ᵢ ∈ span(V₁, …, V₆) ⊆ span Vⁿ`: the paper's claim that `V* = Vⁿ` is a
possible (the "proper") QR decomposition of `L*` when `r ≥ 6`. -/
theorem IsKSStep.L_star_mem (h : d.IsKSStep D Δt K V) (hT : Supp (ctr K V) 3) (i : Fin r) :
    d.L₂ V i - Δt • ∑ k, ⟪d.Xs i, D (d.Xs k)⟫ • (X * d.L₂ V k) ∈ degreeLT ℝ 6 :=
  Submodule.sub_mem _ (degreeLT_mono (by norm_num) (h.L₂_mem hT i))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (X_mul_mem_degreeLT (h.L₂_mem hT k))))

/-- arXiv 2502.08951, The coefficients `S*` of the proper QR decomposition. -/
theorem IsKSStep.exists_Ss (h : d.IsKSStep D Δt K V) (hT : Supp (ctr K V) 3) :
    ∃ Ss : Matrix (Fin r) (Fin r) ℝ, ∀ i, ∑ j, Ss i j • V j =
      d.L₂ V i - Δt • ∑ k, ⟪d.Xs i, D (d.Xs k)⟫ • (X * d.L₂ V k) := by
  refine ⟨Matrix.of fun i j => vIP (V j)
    (d.L₂ V i - Δt • ∑ k, ⟪d.Xs i, D (d.Xs k)⟫ • (X * d.L₂ V k)), fun i => ?_⟩
  have := vProj_of_mem h.orth_V (h.proper_V (h.L_star_mem hT i))
  rw [vProj_apply] at this
  exact this

/-- `V*`-Parseval. -/
lemma parseval {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ι → ℝ[X]} (hW : VOrthonormal W)
    {a : ℝ[X]} (ha : a ∈ Submodule.span ℝ (Set.range W)) (b : ℝ[X]) :
    ∑ j, vIP (W j) a * vIP b (W j) = vIP b a := by
  conv_rhs => rw [← vProj_of_mem hW ha, vProj_apply]
  simp only [← vIPL_apply, map_sum, map_smul, smul_eq_mul]

/-- `Xs ⊂ X̂`. -/
lemma IsLowRankBGKStep.Xs_mem (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (i : Fin r) :
    d.Xs i ∈ Submodule.span ℝ (Set.range d.Xh) :=
  Submodule.subset_span ⟨Fin.castAdd t i, h.Xh_left i⟩

/-- `K*ⱼ` lies in the range of `X̂`: (5.29). -/
lemma IsLowRankBGKStep.Ks_mem (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (j : Fin r) :
    d.Ks j ∈ Submodule.span ℝ (Set.range d.Xh) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h.Xs_mem i)

/-- For XL as for sXL, `⟨M* V*ⱼ⟩ᵥ` lies in the range of `X̂`: for every `ε ≥ 0`, not only for the
`ε → 0` of (5.27), (5.28). -/
lemma IsLowRankBGKStep.MV_mem (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (hΔt : Δt ≠ 0)
    (j : Fin r) : d.MV (d.Vs j) ∈ Submodule.span ℝ (Set.range d.Xh) := by
  cases sch with
  | sXL => exact h.augment j
  | XL =>
    have h1 : d.K₄ j ∈ Submodule.span ℝ (Set.range d.Xh) := h.augment j
    have h2 : d.MV (d.Vs j) = Δt⁻¹ • ((ε + Δt) • d.K₄ j - ε • d.Ks j) := by
      have h3 := h.xstep j
      have h4 : Δt • d.MV (d.Vs j) = (ε + Δt) • d.K₄ j - ε • d.Ks j := by
        linear_combination (norm := module) -h3
      rw [← h4, smul_smul, inv_mul_cancel₀ hΔt, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ h1)
      (Submodule.smul_mem _ _ (h.Ks_mem j)))

/-- `M*` lies in the range of `X̂`, i.e. (5.30): the three `x`-factors of `M*` do. -/
lemma IsLowRankBGKStep.max_mem (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (hΔt : Δt ≠ 0) :
    d.ρs ∈ Submodule.span ℝ (Set.range d.Xh) ∧ d.ms ∈ Submodule.span ℝ (Set.range d.Xh) ∧
      d.qs ∈ Submodule.span ℝ (Set.range d.Xh) := by
  have key : ∀ a ∈ degreeLT ℝ 3, vIP g₀ a • d.ρs + vIP g₁ a • d.ms + vIP g₂ a • d.qs ∈
      Submodule.span ℝ (Set.range d.Xh) := by
    intro a ha
    have ha' := h.proper_Vs ha
    have h1 : ∑ j, vIP (d.Vs j) a • d.MV (d.Vs j) =
        vIP g₀ a • d.ρs + vIP g₁ a • d.ms + vIP g₂ a • d.qs := by
      simp only [MV, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, smul_smul,
        parseval h.orth_Vs ha']
    rw [← h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h.MV_mem hΔt j)
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := dual_table
  refine ⟨?_, ?_, ?_⟩
  · simpa [vIP_comm _ e₀, a1, a2, a3] using key e₀ e₀_mem
  · simpa [vIP_comm _ e₁, b1, b2, b3] using key e₁ e₁_mem
  · simpa [vIP_comm _ e₂, c1, c2, c3] using key e₂ e₂_mem

/-- arXiv 2502.08951, Step 5 on functionals: (5.29)–(5.31) for every `ε ≥ 0`: `(ε + Δt) ⟨ℓ, f̂ⁿ⁺¹⟩ =
ε ⟨ℓ, f*⟩ + Δt ⟨ℓ, M*⟩`. -/
theorem IsLowRankBGKStep.ctr_Lh (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (hΔt : Δt ≠ 0)
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) : (ε + Δt) • ctr d.Xh d.Lh ℓ =
      ε • ctr d.Ks d.Vs ℓ + Δt • (ℓ g₀ • d.ρs + ℓ g₁ • d.ms + ℓ g₂ • d.qs) := by
  obtain ⟨h1, h2, h3⟩ := h.max_mem hΔt
  have hPM : ∑ i, ℓ (d.MX (d.Xh i)) • d.Xh i = ℓ g₀ • d.ρs + ℓ g₁ • d.ms + ℓ g₂ • d.qs := by
    conv_rhs => rw [← Px_of_mem h.orth_Xh h1, ← Px_of_mem h.orth_Xh h2,
      ← Px_of_mem h.orth_Xh h3]
    simp only [MX, map_add, map_smul, smul_eq_mul, Px_apply, add_smul, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul]
    congr 1
    · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hK : ctr d.Ks d.Vs ℓ = ∑ i, ℓ (∑ j, d.Ss i j • d.Vs j) • d.Xs i :=
    ctr_factor d.Ss d.Xs d.Vs ℓ
  have hsplit : (ε + Δt) • ctr d.Xh d.Lh ℓ = ε • ∑ i, ℓ (∑ j, d.Ss i j • d.Vs j) • d.Xs i
      + Δt • ∑ i, ℓ (d.MX (d.Xh i)) • d.Xh i := by
    have hl : ∀ i, (ε + Δt) • (ℓ (d.Lh (Fin.castAdd t i)) • d.Xh (Fin.castAdd t i)) =
        ε • (ℓ (∑ j, d.Ss i j • d.Vs j) • d.Xs i) +
          Δt • (ℓ (d.MX (d.Xh (Fin.castAdd t i))) • d.Xh (Fin.castAdd t i)) := by
      intro i
      have h4 := congrArg ℓ (h.hlstep_left i)
      simp only [map_smul, map_sub, smul_eq_mul] at h4
      rw [h.Xh_left i] at h4 ⊢
      linear_combination (norm := module) h4 • d.Xs i
    have hr : ∀ i, (ε + Δt) • (ℓ (d.Lh (Fin.natAdd r i)) • d.Xh (Fin.natAdd r i)) =
        Δt • (ℓ (d.MX (d.Xh (Fin.natAdd r i))) • d.Xh (Fin.natAdd r i)) := by
      intro i
      have h4 := congrArg ℓ (h.hlstep_right i)
      simp only [map_smul, map_sub, smul_eq_mul] at h4
      linear_combination (norm := module) h4 • d.Xh (Fin.natAdd r i)
    have e1 : ctr d.Xh d.Lh ℓ = ∑ i, ℓ (d.Lh (Fin.castAdd t i)) • d.Xh (Fin.castAdd t i) +
        ∑ i, ℓ (d.Lh (Fin.natAdd r i)) • d.Xh (Fin.natAdd r i) := Fin.sum_univ_add _
    have e2 : ∑ i, ℓ (d.MX (d.Xh i)) • d.Xh i =
        ∑ i, ℓ (d.MX (d.Xh (Fin.castAdd t i))) • d.Xh (Fin.castAdd t i) +
        ∑ i, ℓ (d.MX (d.Xh (Fin.natAdd r i))) • d.Xh (Fin.natAdd r i) := Fin.sum_univ_add _
    rw [e1, e2, smul_add]
    simp only [Finset.smul_sum, hl, hr, smul_add, Finset.sum_add_distrib]
    abel
  rw [hsplit, hK, hPM]

/-- Step 6 on functionals: the truncation changes nothing when the discarded singular values vanish.
-/
lemma IsLowRankBGKStep.ctr_out (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V')
    (hσ : ∀ i : Fin t, d.σ (Fin.natAdd r i) = 0) (ℓ : ℝ[X] →ₗ[ℝ] ℝ) :
    ctr K' V' ℓ = ctr d.Xh d.Lh ℓ := by
  have hS : ∀ i j, d.Sh i j = ∑ m, d.Us i m * d.σ m * d.Ws j m := by
    intro i j
    rw [h.svd, Matrix.mul_apply]
    simp [Matrix.mul_diagonal]
  have h1 : ctr d.Xh d.Lh ℓ = ∑ m, (d.σ m * ∑ j, d.Ws j m * ℓ (d.Vh j)) •
      ∑ i, d.Us i m • d.Xh i := by
    have h2 : ∀ i, ℓ (d.Lh i) = ∑ m, d.Us i m * (d.σ m * ∑ j, d.Ws j m * ℓ (d.Vh j)) := by
      intro i
      simp only [h.qr i, map_sum, map_smul, smul_eq_mul, hS, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [ctr, h2, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [h1, Fin.sum_univ_add]
  simp only [hσ, zero_mul, zero_smul, Finset.sum_const_zero, add_zero]
  simp only [ctr, h.K_out, h.V_out, map_sum, map_smul, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- `r ≥ 6`: the properness of the basis contains the paper's rank condition. -/
lemma IsLowRankBGKStep.six_le (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') : 6 ≤ r := by
  have h1 : Module.finrank ℝ (degreeLT ℝ 6) ≤ Module.finrank ℝ
      (Submodule.span ℝ (Set.range V)) := by
    have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range V)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range V)
    exact Submodule.finrank_mono h.proper_V
  have h2 : Module.finrank ℝ (degreeLT ℝ 6) = 6 := by
    rw [(degreeLTEquiv ℝ 6).finrank_eq]
    simp
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range V)) ≤ r := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) V
  omega

/-- For `ε = 0`, `L̂ⁿ⁺¹ = ⟨X̂ M*⟩ₓ`: the display after (5.30). -/
lemma IsLowRankBGKStep.Lh_eq (h : d.IsLowRankBGKStep ev D 0 Δt sch K V K' V') (hΔt : Δt ≠ 0)
    (i : Fin (r + t)) : d.Lh i = d.MX (d.Xh i) := by
  induction i using Fin.addCases with
  | left i =>
    have h1 := h.hlstep_left i
    rw [zero_smul] at h1
    exact (sub_eq_zero.mp ((smul_eq_zero_iff_right hΔt).mp h1.symm)).symm
  | right i =>
    have h1 := h.hlstep_right i
    rw [zero_smul] at h1
    exact (sub_eq_zero.mp ((smul_eq_zero_iff_right hΔt).mp h1.symm)).symm

/-- `Ŝⁿ⁺¹` has rank at most `3` for `ε = 0`; so `Σ_s = diag(Σ₃ₓ₃, 0)`: Step 6. -/
lemma IsLowRankBGKStep.sigma_eq_zero (h : d.IsLowRankBGKStep ev D 0 Δt sch K V K' V') (hΔt : Δt ≠ 0)
    (m : Fin (r + t)) (hm : 3 ≤ (m : ℕ)) : d.σ m = 0 := by
  have hS : ∀ i j, d.Sh i j = vIP (d.Lh i) (d.Vh j) := by
    intro i j
    rw [h.qr i]
    simp only [← vIPL_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    simp [vIPL_apply, h.orth_Vh _ j]
  let A : Matrix (Fin (r + t)) (Fin 3) ℝ :=
    Matrix.of fun i k => ![⟪d.Xh i, d.ρs⟫, ⟪d.Xh i, d.ms⟫, ⟪d.Xh i, d.qs⟫] k
  let B : Matrix (Fin 3) (Fin (r + t)) ℝ :=
    Matrix.of fun k j => ![vIP g₀ (d.Vh j), vIP g₁ (d.Vh j), vIP g₂ (d.Vh j)] k
  have hAB : d.Sh = A * B := by
    ext i j
    rw [hS, h.Lh_eq hΔt, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [MX, ← vIPL_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    simp [A, B]
  have hr : d.Sh.rank ≤ 3 := by
    rw [hAB]
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    simpa using Matrix.rank_le_card_height B
  exact sv_eq_zero_of_rank_le h.orth_Us h.orth_Ws h.svd h.sorted h.nonneg hr m hm

end StepData

/-- `f = ∑ⱼ Kⱼ Vⱼ` is the Maxwellian with `x`-factors `ρ`, `m = ρ u`, `q = ρ u²`. -/
structure IsEq (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : Fin r → Ex) (V : Fin r → ℝ[X]) (ρ m q : Ex) : Prop where
  ctr_eq : ∀ ℓ : ℝ[X] →ₗ[ℝ] ℝ, ctr K V ℓ = ℓ g₀ • ρ + ℓ g₁ • m + ℓ g₂ • q
  rho_ne : ∀ x, ev ρ x ≠ 0
  q_eq : ∀ x, ev q x * ev ρ x = ev m x ^ 2

namespace IsEq

variable {ev : Ex →ₗ[ℝ] Ω → ℝ} {K : Fin r → Ex} {V : Fin r → ℝ[X]} {ρ m q : Ex}

lemma supp (h : IsEq ev K V ρ m q) : Supp (ctr K V) 3 := by
  intro ℓ ℓ' hℓ
  rw [h.ctr_eq, h.ctr_eq, hℓ _ g₀_mem, hℓ _ g₁_mem, hℓ _ g₂_mem]

/-- The moments of a Maxwellian. -/
lemma moments (h : IsEq ev K V ρ m q) :
    moment 0 K V = ρ ∧ moment 1 K V = m ∧ moment 2 K V = ρ + q ∧ moment 3 K V = (3 : ℝ) • m ∧
      moment 4 K V = (3 : ℝ) • ρ + (6 : ℝ) • q := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14, h15⟩⟩ := momL_table
  simp only [moment_eq_ctr, h.ctr_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15]
  simp

end IsEq

/-! ### The theorem -/

lemma ev_ctr {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex) (V : ι → ℝ[X])
    (ℓ : ℝ[X] →ₗ[ℝ] ℝ) (x : Ω) : ev (ctr K V ℓ) x = ∑ j, ℓ (V j) * ev (K j) x := by
  simp [ctr, map_sum, Finset.sum_apply]

lemma fval_eq_ev {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex) (V : ι → ℝ[X])
    (x : Ω) (v : ℝ) : fval ev K V x v = ev (ctr K V (pointL v)) x := by
  rw [ev_ctr, fval]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

lemma integrable_gaussFn (p : ℝ[X]) : MeasureTheory.Integrable (gaussFn p) := by
  have h := integrable_gauss p (b := 1 / 2) (by norm_num)
  refine h.congr (MeasureTheory.ae_of_all _ fun v => ?_)
  simp only [gaussFn]
  congr 2
  ring

lemma density_eq {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex) (V : ι → ℝ[X])
    (x : Ω) : density ev K V x = ev (moment 0 K V) x := by
  rw [moment_eq_ctr, ev_ctr, density]
  simp only [fval]
  rw [MeasureTheory.integral_finsetSum _ fun j _ => (integrable_gaussFn (V j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul]
  simp [vMean, mul_comm]

lemma momentum_eq {ι : Type*} [Fintype ι] (ev : Ex →ₗ[ℝ] Ω → ℝ) (K : ι → Ex) (V : ι → ℝ[X])
    (x : Ω) : (∫ v : ℝ, v * fval ev K V x v) = ev (moment 1 K V) x := by
  have hX : ∀ (p : ℝ[X]) (v : ℝ), v * gaussFn p v = gaussFn (X * p) v := fun p v => by
    simp [gaussFn, mul_assoc]
  have h1 : ∀ v : ℝ, v * fval ev K V x v = ∑ j, ev (K j) x * gaussFn (X * V j) v := by
    intro v
    simp only [fval, Finset.mul_sum, ← hX]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  rw [moment_eq_ctr, ev_ctr,
    MeasureTheory.integral_finsetSum _ fun j _ => (integrable_gaussFn _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul]
  simp [vMean, mul_comm]

namespace IsEq

variable {ev : Ex →ₗ[ℝ] Ω → ℝ} {K : Fin r → Ex} {V : Fin r → ℝ[X]} {ρ m q : Ex}

lemma density_eq' (h : IsEq ev K V ρ m q) (x : Ω) : density ev K V x = ev ρ x := by
  rw [density_eq, h.moments.1]

lemma meanVelocity_eq (h : IsEq ev K V ρ m q) (x : Ω) :
    meanVelocity ev K V x = ev m x / ev ρ x := by
  rw [meanVelocity, momentum_eq, h.moments.2.1, h.density_eq']

lemma ev_q (h : IsEq ev K V ρ m q) (x : Ω) :
    ev q x = ev ρ x * (ev m x / ev ρ x) ^ 2 := by
  have h1 := h.rho_ne x
  have h2 := h.q_eq x
  field_simp
  linarith

/-- (5.11) for a state with the structure `IsEq`. -/
lemma fval_eq (h : IsEq ev K V ρ m q) (x : Ω) (v : ℝ) :
    fval ev K V x v = maxwellianExpansion (density ev K V x) (meanVelocity ev K V x) v := by
  have h1 := h.rho_ne x
  rw [fval_eq_ev, h.ctr_eq, h.density_eq', h.meanVelocity_eq, maxwellianExpansion_eq]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, pointL_apply, smul_eq_mul]
  rw [h.ev_q]
  field_simp

end IsEq

/-- A state at equilibrium in the pointwise sense of Theorem 5.1 has the structure `IsEq`. -/
lemma exists_isEq {ev : Ex →ₗ[ℝ] Ω → ℝ} (hev : Function.Injective ev) {K : Fin r → Ex}
    {V : Fin r → ℝ[X]}
    (h0 : ∀ x v, fval ev K V x v = maxwellianExpansion (density ev K V x) (meanVelocity ev K V x) v)
    (hρ : ∀ x, density ev K V x ≠ 0) :
    ∃ ρ m q, IsEq ev K V ρ m q := by
  have hexp : ∀ v : ℝ, Real.exp (-v ^ 2 / 2) ≠ 0 := fun v => (Real.exp_pos _).ne'
  have hpoly : ∀ x, ∑ j, ev (K j) x • V j = density ev K V x • g₀ +
      (density ev K V x * meanVelocity ev K V x) • g₁ +
      (density ev K V x * meanVelocity ev K V x ^ 2) • g₂ := by
    intro x
    refine Polynomial.funext fun v => ?_
    have h1 := h0 x v
    rw [maxwellianExpansion_eq, fval] at h1
    simp only [gaussFn, ← mul_assoc, ← Finset.sum_mul, ← add_mul] at h1
    have h2 := mul_right_cancel₀ (hexp v) h1
    simpa [eval_finsetSum] using h2
  have hℓ : ∀ (ℓ : ℝ[X] →ₗ[ℝ] ℝ) x, ev (ctr K V ℓ) x = density ev K V x * ℓ g₀ +
      density ev K V x * meanVelocity ev K V x * ℓ g₁ +
      density ev K V x * meanVelocity ev K V x ^ 2 * ℓ g₂ := by
    intro ℓ x
    have h1 := congrArg ℓ (hpoly x)
    simp only [map_sum, map_add, map_smul, smul_eq_mul] at h1
    rw [ev_ctr, ← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := dual_table
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, -⟩ := momL_table
  have hρ' : ∀ x, ev (ctr K V (momL 0)) x = density ev K V x := fun x => by
    rw [hℓ, h1, h2, h3]
    ring
  have hm' : ∀ x, ev (ctr K V (momL 1)) x = density ev K V x * meanVelocity ev K V x := fun x => by
    rw [hℓ, h4, h5, h6]
    ring
  have hq' : ∀ x, ev (ctr K V (vIPL e₂)) x =
      density ev K V x * meanVelocity ev K V x ^ 2 := fun x => by
    rw [hℓ]
    simp only [vIPL_apply, c1, c2, c3]
    ring
  refine ⟨ctr K V (momL 0), ctr K V (momL 1), ctr K V (vIPL e₂), ?_, fun x => ?_, fun x => ?_⟩
  · intro ℓ
    refine hev (funext fun x => ?_)
    rw [hℓ]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ', hm', hq']
    ring
  · rw [hρ']
    exact hρ x
  · rw [hρ', hm', hq']
    ring

namespace StepData

variable {d : StepData Ex r t} {ev : Ex →ₗ[ℝ] Ω → ℝ} {D : Ex →ₗ[ℝ] Ex} {ε Δt : ℝ} {sch : Variant}
  {K K' : Fin r → Ex} {V V' : Fin r → ℝ[X]}

/-- arXiv 2502.08951, **(5.33)**: for `ε = 0`, whatever `f` is, `fⁿ⁺¹ = f̂ⁿ⁺¹ = M*`; the truncation
is lossless. -/
theorem IsLowRankBGKStep.isEq_next (h : d.IsLowRankBGKStep ev D 0 Δt sch K V K' V') (hΔt : 0 < Δt) :
    IsEq ev K' V' d.ρs d.ms d.qs where
  ctr_eq ℓ := by
    have h6 := h.six_le
    have hσ : ∀ i : Fin t, d.σ (Fin.natAdd r i) = 0 := fun i =>
      h.sigma_eq_zero hΔt.ne' _ (by simp only [Fin.val_natAdd]; omega)
    rw [h.ctr_out hσ]
    have h1 := h.ctr_Lh hΔt.ne' ℓ
    rw [zero_add, zero_smul, zero_add] at h1
    exact smul_right_injective _ hΔt.ne' h1
  rho_ne := h.rho_ne
  q_eq := h.qs_eq

/-- arXiv 2502.08951, **(5.26), (5.34) with the exact remainder**: for a Maxwellian `f` and `ε = 0`,
`j = 0, 1`: `(⟨vʲ fⁿ⁺¹⟩ - ⟨vʲ fⁿ⟩)/Δt = -∂ₓ⟨vʲ⁺¹ fⁿ⟩ - Δt P ∂ₓ P ∂ₓ (⟨vʲ⁺² fⁿ⟩ - Δt ∂ₓ ⟨vʲ⁺³ fⁿ⟩)`.
-/
theorem IsLowRankBGKStep.moment_update (h : d.IsLowRankBGKStep ev D 0 Δt sch K V K' V')
    (hΔt : 0 < Δt) {ρ m q : Ex} (hE : IsEq ev K V ρ m q) {j : ℕ} (hj : j ≤ 1) :
    Δt⁻¹ • (moment j K' V' - moment j K V) = -D (moment (j + 1) K V) -
      Δt • Px d.Xs (D (Px d.Xs (D (moment (j + 2) K V - Δt • D (moment (j + 3) K V))))) := by
  have hE' := h.isEq_next hΔt
  have h1 : moment j K' V' = ctr d.Ks d.Vs (momL j) := by
    interval_cases j
    · rw [hE'.moments.1, StepData.ρs, moment_eq_ctr]
    · rw [hE'.moments.2.1, StepData.ms, moment_eq_ctr]
  have hne : Δt ≠ 0 := hΔt.ne'
  rw [h1, h.ctr_Ks_eq hE.supp]
  simp only [shift_momL, ← moment_eq_ctr]
  have e : Δt⁻¹ • (moment j K V - Δt • D (moment (j + 1) K V) -
      Δt ^ 2 • Px d.Xs (D (Px d.Xs (D (moment (j + 1 + 1) K V -
        Δt • D (moment (j + 1 + 1 + 1) K V))))) - moment j K V) =
      (Δt⁻¹ * (-Δt)) • D (moment (j + 1) K V) + (Δt⁻¹ * (-Δt ^ 2)) •
        Px d.Xs (D (Px d.Xs (D (moment (j + 1 + 1) K V -
          Δt • D (moment (j + 1 + 1 + 1) K V))))) := by
    module
  rw [e]
  have e1 : Δt⁻¹ * (-Δt) = -1 := by field_simp
  have e2 : Δt⁻¹ * (-Δt ^ 2) = -Δt := by field_simp
  rw [e1, e2]
  module

end StepData

/-- A run of the limit scheme (`ε = 0`) of Section 5 of arXiv 2502.08951.  Each step starts from
`fⁿ = ∑ⱼ Kⁿⱼ Vⁿⱼ`.  The factors at step `n + 1` need not be the raw output `(K', V')` of Step 6:
they may be any refactorization of the same function.  The proof of Theorem 5.1 re-expresses `fⁿ`
in the Hermite basis at the start of every step, which Step 6 alone does not produce. -/
def IsRun (ev : Ex →ₗ[ℝ] Ω → ℝ) (D : Ex →ₗ[ℝ] Ex) (Δt : ℝ) (sch : Variant) (t : ℕ)
    (K : ℕ → Fin r → Ex) (V : ℕ → Fin r → ℝ[X]) : Prop :=
  ∀ n, ∃ (d : StepData Ex r t) (K' : Fin r → Ex) (V' : Fin r → ℝ[X]),
    d.IsLowRankBGKStep ev D 0 Δt sch (K n) (V n) K' V' ∧
      ∀ x v, fval ev (K (n + 1)) (V (n + 1)) x v = fval ev K' V' x v

/-- **Theorem 5.1 of arXiv 2502.08951 (AP property for the 1D1V BGK model).**  For a run of the
limit `ε → 0` of the low-rank scheme, XL or sXL, from equilibrium data `f⁰ = M⁰`, and for all `n`:

* (5.11) `fⁿ(x, v) = Mⁿ(x, v)`, with `Mⁿ` the Maxwellian (5.2) of `fⁿ`, whose density has no zero;
* the moments of `fⁿ`, which are `x`-functions in `Ex`, are `⟨fⁿ⟩ = ρⁿ`, `⟨v fⁿ⟩ = ρⁿ uⁿ`,
  `⟨v² fⁿ⟩ = ρⁿ + ρⁿ (uⁿ)²`;
* (5.12) `(Uⁿ⁺¹ - Uⁿ)/Δt = -∂ₓ(ρⁿuⁿ, ρⁿ + ρⁿ(uⁿ)²) + O(Δt)`, in the form of an exact identity for
  the components `j = 0, 1`: the remainder is `-Δt P ∂ₓ P ∂ₓ (⟨vʲ⁺² fⁿ⟩ - Δt ∂ₓ⟨vʲ⁺³ fⁿ⟩)`, with `P`
  the orthogonal projection on `span X*`.  See `theorem_5_1_rate` for the bound.

The differences from the paper are listed in the module docstring.  In short: `x`-functions form an
abstract inner product space with an operator `D` for `∂ₓ`; `r ≥ 6` is contained in the hypothesis
that the velocity basis is proper (`IsLowRankBGKStep.six_le`, `hermite_proper`); and the density
must not vanish, which (5.7) needs. -/
theorem theorem_5_1 {ev : Ex →ₗ[ℝ] Ω → ℝ} (hev : Function.Injective ev) {D : Ex →ₗ[ℝ] Ex}
    {Δt : ℝ} (hΔt : 0 < Δt) {sch : Variant} {K : ℕ → Fin r → Ex} {V : ℕ → Fin r → ℝ[X]}
    (hrun : IsRun ev D Δt sch t K V)
    (h0 : ∀ x v, fval ev (K 0) (V 0) x v =
      maxwellianExpansion (density ev (K 0) (V 0) x) (meanVelocity ev (K 0) (V 0) x) v)
    (hρ : ∀ x, density ev (K 0) (V 0) x ≠ 0) :
    (∀ n x v, fval ev (K n) (V n) x v =
      maxwellianExpansion (density ev (K n) (V n) x) (meanVelocity ev (K n) (V n) x) v) ∧
    (∀ n x, density ev (K n) (V n) x ≠ 0 ∧
      ev (moment 0 (K n) (V n)) x = density ev (K n) (V n) x ∧
      ev (moment 1 (K n) (V n)) x = density ev (K n) (V n) x * meanVelocity ev (K n) (V n) x ∧
      ev (moment 2 (K n) (V n)) x = density ev (K n) (V n) x +
        density ev (K n) (V n) x * meanVelocity ev (K n) (V n) x ^ 2) ∧
    (∀ n, ∃ Y : Fin r → Ex, Orthonormal ℝ Y ∧ ∀ j ≤ 1,
      Δt⁻¹ • (moment j (K (n + 1)) (V (n + 1)) - moment j (K n) (V n)) =
        -D (moment (j + 1) (K n) (V n)) -
        Δt • Px Y (D (Px Y (D (moment (j + 2) (K n) (V n) -
          Δt • D (moment (j + 3) (K n) (V n))))))) := by
  have hsame : ∀ n (K' : Fin r → Ex) (V' : Fin r → ℝ[X]),
      (∀ x v, fval ev (K (n + 1)) (V (n + 1)) x v = fval ev K' V' x v) →
      (∀ x, density ev (K (n + 1)) (V (n + 1)) x = density ev K' V' x) ∧
      (∀ x, meanVelocity ev (K (n + 1)) (V (n + 1)) x = meanVelocity ev K' V' x) ∧
      moment 0 (K (n + 1)) (V (n + 1)) = moment 0 K' V' ∧
      moment 1 (K (n + 1)) (V (n + 1)) = moment 1 K' V' := by
    intro n K' V' h
    have h1 : ∀ x, density ev (K (n + 1)) (V (n + 1)) x = density ev K' V' x := fun x => by
      simp only [density, h x]
    have h2 : ∀ x, (∫ v : ℝ, v * fval ev (K (n + 1)) (V (n + 1)) x v) =
        ∫ v : ℝ, v * fval ev K' V' x v := fun x => by
      simp only [h x]
    refine ⟨h1, fun x => ?_, hev (funext fun x => ?_), hev (funext fun x => ?_)⟩
    · rw [meanVelocity, meanVelocity, h1, h2]
    · rw [← density_eq, ← density_eq, h1]
    · rw [← momentum_eq, ← momentum_eq, h2]
  have hE : ∀ n, ∃ ρ m q, IsEq ev (K n) (V n) ρ m q := by
    intro n
    cases n with
    | zero => exact exists_isEq hev h0 hρ
    | succ n =>
      obtain ⟨d, K', V', hd, hf⟩ := hrun n
      obtain ⟨h1, h2, -, -⟩ := hsame n K' V' hf
      have hE' := hd.isEq_next hΔt
      refine exists_isEq hev (fun x v => ?_) fun x => ?_
      · rw [hf, h1, h2]
        exact hE'.fval_eq x v
      · rw [h1, hE'.density_eq']
        exact hE'.rho_ne x
  refine ⟨fun n x v => ?_, fun n x => ?_, fun n => ?_⟩
  · obtain ⟨ρ, m, q, h⟩ := hE n
    exact h.fval_eq x v
  · obtain ⟨ρ, m, q, h⟩ := hE n
    have h1 := h.rho_ne x
    refine ⟨by rw [h.density_eq']; exact h1, (density_eq _ _ _ _).symm, ?_, ?_⟩
    · rw [h.moments.2.1, h.density_eq', h.meanVelocity_eq]
      field_simp
    · rw [h.moments.2.2.1, h.density_eq', h.meanVelocity_eq, map_add, Pi.add_apply, h.ev_q]
  · obtain ⟨ρ, m, q, h⟩ := hE n
    obtain ⟨d, K', V', hd, hf⟩ := hrun n
    obtain ⟨-, -, h0', h1'⟩ := hsame n K' V' hf
    refine ⟨d.Xs, hd.orth_Xs, fun j hj => ?_⟩
    have h2 : moment j (K (n + 1)) (V (n + 1)) = moment j K' V' := by
      interval_cases j
      · exact h0'
      · exact h1'
    rw [h2]
    exact hd.moment_update hΔt h hj

/-- arXiv 2502.08951, **Theorem 5.1, (5.12) with an explicit `O(Δt)`.**  With the hypotheses of
`theorem_5_1` and `‖∂ₓ y‖ ≤ Λ ‖y‖` (a discretization of `∂ₓ`), for `j = 0, 1` `‖(⟨vʲ fⁿ⁺¹⟩ - ⟨vʲ
fⁿ⟩)/Δt + ∂ₓ⟨vʲ⁺¹ fⁿ⟩‖ ≤ Δt Λ² (‖⟨vʲ⁺² fⁿ⟩‖ + Δt Λ ‖⟨vʲ⁺³ fⁿ⟩‖)`. The moments are those of `Mⁿ`
(`IsEq.moments`), so the constant is uniform as long as `Mⁿ` is bounded. -/
theorem theorem_5_1_rate {ev : Ex →ₗ[ℝ] Ω → ℝ} (hev : Function.Injective ev) {D : Ex →ₗ[ℝ] Ex}
    {Δt Λ : ℝ} (hΔt : 0 < Δt) (hΛ : 0 ≤ Λ) (hD : ∀ y, ‖D y‖ ≤ Λ * ‖y‖) {sch : Variant}
    {K : ℕ → Fin r → Ex} {V : ℕ → Fin r → ℝ[X]} (hrun : IsRun ev D Δt sch t K V)
    (h0 : ∀ x v, fval ev (K 0) (V 0) x v =
      maxwellianExpansion (density ev (K 0) (V 0) x) (meanVelocity ev (K 0) (V 0) x) v)
    (hρ : ∀ x, density ev (K 0) (V 0) x ≠ 0) (n : ℕ) {j : ℕ} (hj : j ≤ 1) :
    ‖Δt⁻¹ • (moment j (K (n + 1)) (V (n + 1)) - moment j (K n) (V n)) +
        D (moment (j + 1) (K n) (V n))‖ ≤
      Δt * Λ ^ 2 * (‖moment (j + 2) (K n) (V n)‖ + Δt * Λ * ‖moment (j + 3) (K n) (V n)‖) := by
  obtain ⟨Y, hY, h⟩ := (theorem_5_1 hev hΔt hrun h0 hρ).2.2 n
  rw [h j hj]
  set w := moment (j + 2) (K n) (V n) - Δt • D (moment (j + 3) (K n) (V n)) with hw
  have h1 : -D (moment (j + 1) (K n) (V n)) - Δt • Px Y (D (Px Y (D w))) +
      D (moment (j + 1) (K n) (V n)) = -(Δt • Px Y (D (Px Y (D w)))) := by
    abel
  rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hΔt]
  have h2 : ‖Px Y (D (Px Y (D w)))‖ ≤ Λ ^ 2 * ‖w‖ := by
    calc ‖Px Y (D (Px Y (D w)))‖ ≤ ‖D (Px Y (D w))‖ := norm_Px_le hY _
      _ ≤ Λ * ‖Px Y (D w)‖ := hD _
      _ ≤ Λ * ‖D w‖ := by gcongr; exact norm_Px_le hY _
      _ ≤ Λ * (Λ * ‖w‖) := by gcongr; exact hD _
      _ = _ := by ring
  have h3 : ‖w‖ ≤ ‖moment (j + 2) (K n) (V n)‖ + Δt * Λ * ‖moment (j + 3) (K n) (V n)‖ := by
    calc ‖w‖ ≤ ‖moment (j + 2) (K n) (V n)‖ + ‖Δt • D (moment (j + 3) (K n) (V n))‖ :=
          norm_sub_le _ _
      _ = ‖moment (j + 2) (K n) (V n)‖ + Δt * ‖D (moment (j + 3) (K n) (V n))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hΔt]
      _ ≤ ‖moment (j + 2) (K n) (V n)‖ + Δt * (Λ * ‖moment (j + 3) (K n) (V n)‖) := by
          gcongr
          exact hD _
      _ = _ := by ring
  calc Δt * ‖Px Y (D (Px Y (D w)))‖ ≤ Δt * (Λ ^ 2 * ‖w‖) := by gcongr
    _ ≤ Δt * (Λ ^ 2 * (‖moment (j + 2) (K n) (V n)‖ +
        Δt * Λ * ‖moment (j + 3) (K n) (V n)‖)) := by gcongr
    _ = _ := by ring

namespace StepData

variable {d : StepData Ex r t} {ev : Ex →ₗ[ℝ] Ω → ℝ} {D : Ex →ₗ[ℝ] Ex} {ε Δt : ℝ} {sch : Variant}
  {K K' : Fin r → Ex} {V V' : Fin r → ℝ[X]}

/-- The value at `(x, v)` of `M*`, (5.7): `M*` is the Maxwellian (5.2) of `f*`. -/
lemma IsLowRankBGKStep.ev_max (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (x : Ω) (v : ℝ) :
    gaussFn g₀ v * ev d.ρs x + gaussFn g₁ v * ev d.ms x + gaussFn g₂ v * ev d.qs x =
      maxwellianExpansion (density ev d.Ks d.Vs x) (meanVelocity ev d.Ks d.Vs x) v := by
  have h1 := h.rho_ne x
  have h2 := h.qs_eq x
  have hq : ev d.qs x = ev d.ρs x * (ev d.ms x / ev d.ρs x) ^ 2 := by
    field_simp
    linarith
  have hd : density ev d.Ks d.Vs x = ev d.ρs x := density_eq ev _ _ x
  rw [maxwellianExpansion_eq, meanVelocity, hd, momentum_eq]
  change _ = ev d.ρs x * gaussFn g₀ v + ev d.ρs x * (ev d.ms x / ev d.ρs x) * gaussFn g₁ v +
    ev d.ρs x * (ev d.ms x / ev d.ρs x) ^ 2 * gaussFn g₂ v
  rw [hq]
  field_simp

/-- arXiv 2502.08951, **Step 5 for `ε > 0`, (5.29)–(5.31) and the limit `ε → 0`.**  Whatever `f` is,
one step gives exactly `f̂ⁿ⁺¹ - M* = ε/(ε + Δt) (f* - M*)` before truncation, with `M*` the
Maxwellian of `f*`. -/
theorem IsLowRankBGKStep.fhat_sub_max (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (hε : 0 ≤ ε)
    (hΔt : 0 < Δt) (x : Ω) (v : ℝ) :
    fval ev d.Xh d.Lh x v -
        maxwellianExpansion (density ev d.Ks d.Vs x) (meanVelocity ev d.Ks d.Vs x) v =
      ε / (ε + Δt) * (fval ev d.Ks d.Vs x v -
        maxwellianExpansion (density ev d.Ks d.Vs x) (meanVelocity ev d.Ks d.Vs x) v) := by
  have hw : ε + Δt ≠ 0 := by positivity
  have h1 := congrFun (congrArg ev (h.ctr_Lh hΔt.ne' (pointL v))) x
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, pointL_apply, smul_eq_mul,
    h.ev_max] at h1
  rw [fval_eq_ev, fval_eq_ev, div_mul_eq_mul_div, eq_div_iff hw]
  linear_combination h1

/-- arXiv 2502.08951, **(5.32)**: the collision step conserves `ρ` and `ρ u`, so the Maxwellian does
not change. -/
theorem IsLowRankBGKStep.moment_hat (h : d.IsLowRankBGKStep ev D ε Δt sch K V K' V') (hε : 0 ≤ ε)
    (hΔt : 0 < Δt) {j : ℕ} (hj : j ≤ 1) : moment j d.Xh d.Lh = moment j d.Ks d.Vs := by
  have hw : ε + Δt ≠ 0 := by positivity
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, -⟩ := momL_table
  have h7 := h.ctr_Lh hΔt.ne' (momL j)
  have h8 : ctr d.Ks d.Vs (momL j) =
      (momL j) g₀ • d.ρs + (momL j) g₁ • d.ms + (momL j) g₂ • d.qs := by
    interval_cases j
    · simp [h1, h2, h3, ρs, moment_eq_ctr]
    · simp [h4, h5, h6, ms, moment_eq_ctr]
  rw [← h8, ← add_smul] at h7
  rw [moment_eq_ctr, moment_eq_ctr]
  exact smul_right_injective _ hw h7

end StepData

/-- arXiv 2502.08951, The Hermite functions `V₁, …, V_r` of the paper's proof are an admissible
basis when `r ≥ 6`. -/
theorem hermite_proper (hr : 6 ≤ r) :
    VOrthonormal (fun j : Fin r => hermiteP j) ∧
      degreeLT ℝ 6 ≤ Submodule.span ℝ (Set.range fun j : Fin r => hermiteP j) := by
  refine ⟨fun i j => ?_, degreeLT_le_span_hermite hr⟩
  rw [vIP_hermiteP]
  simp [Fin.ext_iff]

/-! ### Non-vacuity -/

section NonVacuous

variable [FiniteDimensional ℝ Ex]

/-- The polynomial factor of `g₀` in terms of `V₁`. -/
lemma smul_hermiteP_zero : (κ / hAlpha 0) • hermiteP 0 = g₀ := by
  have h := (hAlpha_pos 0).ne'
  rw [hermiteP, smul_smul, div_mul_cancel₀ _ h, g₀]
  rfl

/-- arXiv 2502.08951, **Non-vacuity of Theorem 5.1**: if `∂ₓ ρ = 0`, there is a run of the limit
scheme with the Hermite functions as velocity basis from the Maxwellian `ρ e^{-v²/2}/√(2π)`, for XL
and sXL. It is stationary. Here `dim Ex = r ≥ 6`, and no augmentation is needed (`t = 0`). -/
theorem exists_stationary_run (hr : Module.finrank ℝ Ex = r) (h6 : 6 ≤ r) (ev : Ex →ₗ[ℝ] Ω → ℝ)
    (D : Ex →ₗ[ℝ] Ex) {ρ : Ex} (hρ : ∀ x, ev ρ x ≠ 0) (hρ0 : ρ ≠ 0) (hD : D ρ = 0) {Δt : ℝ}
    (sch : Variant) :
    ∃ (K : ℕ → Fin r → Ex) (V : ℕ → Fin r → ℝ[X]),
      IsRun ev D Δt sch 0 K V ∧ (∀ n j, V n j = hermiteP j) ∧
      (∀ x v, fval ev (K 0) (V 0) x v =
        maxwellianExpansion (density ev (K 0) (V 0) x) (meanVelocity ev (K 0) (V 0) x) v) ∧
      ∀ x, density ev (K 0) (V 0) x ≠ 0 := by
  have hr0 : 0 < r := by omega
  let i₀ : Fin r := ⟨0, hr0⟩
  have hnorm : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hρ0
  have hunit : ‖‖ρ‖⁻¹ • ρ‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin r) (by simpa using hr) (v := fun _ => ‖ρ‖⁻¹ • ρ) (s := {i₀})
    (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      obtain rfl : i = i₀ := hi
      obtain rfl : j = i₀ := hj
      simp [hunit])
  have hb₀ : b i₀ = ‖ρ‖⁻¹ • ρ := hb i₀ rfl
  have hρb : ρ = ‖ρ‖ • b i₀ := by
    rw [hb₀, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hDb : D (b i₀) = 0 := by
    rw [hb₀, map_smul, hD, smul_zero]
  set c : ℝ := κ / hAlpha 0 with hc
  have hcpos : 0 < c := div_pos κ_pos (hAlpha_pos 0)
  set s : ℝ := c * ‖ρ‖ with hs
  have hspos : 0 ≤ s := by positivity
  let K₀ : Fin r → Ex := fun j => if j = i₀ then c • ρ else 0
  let V₀ : Fin r → ℝ[X] := fun j => hermiteP j
  let w : Fin r → ℝ := fun j => if j = i₀ then s else 0
  let S : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal w
  have hsb : s • b i₀ = c • ρ := by
    rw [hb₀, smul_smul, hs, mul_assoc, mul_inv_cancel₀ hnorm, mul_one]
  have hKs : ∀ j, ∑ i, S i j • b i = K₀ j := by
    intro j
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [S, hij])
      (by simp)]
    by_cases hj : j = i₀
    · subst hj
      simp [S, w, K₀, hsb]
    · simp [S, w, K₀, hj]
  have hV₀ : VOrthonormal V₀ := (hermite_proper h6).1
  have hprop : degreeLT ℝ 6 ≤ Submodule.span ℝ (Set.range V₀) := (hermite_proper h6).2
  have hctr : ∀ ℓ : ℝ[X] →ₗ[ℝ] ℝ, ctr K₀ V₀ ℓ = ℓ g₀ • ρ := by
    intro ℓ
    rw [ctr, Finset.sum_eq_single i₀ (fun j _ hj => by simp [K₀, hj]) (by simp)]
    simp only [K₀, ite_true, V₀]
    rw [← smul_hermiteP_zero, map_smul, smul_smul, smul_eq_mul, mul_comm]
  have hE : IsEq ev K₀ V₀ ρ 0 0 :=
    ⟨fun ℓ => by simp [hctr], hρ, fun x => by simp⟩
  have hSk : ∀ k l, k ≠ i₀ → S k l = 0 := fun k l hk => by
    by_cases hkl : k = l
    · subst hkl
      simp [S, w, hk]
    · simp [S, hkl]
  have hDS : ∀ i k l, ⟪b i, D (b k)⟫ * S k l = 0 := by
    intro i k l
    by_cases hk : k = i₀
    · rw [hk, hDb, inner_zero_right, zero_mul]
    · rw [hSk k l hk, mul_zero]
  let d : StepData Ex r 0 :=
    { Xs := b, S₁ := S, S₂ := S, Ss := S, Vs := V₀, qs := 0, K₄ := fun j => vIP g₀ (V₀ j) • ρ,
      Xh := b, Lh := fun i => ⟪b i, ρ⟫ • g₀, Sh := S, Vh := V₀, Us := 1, Ws := 1, σ := w }
  have hdKs : d.Ks = K₀ := funext hKs
  have hdρ : d.ρs = ρ := by
    change moment 0 d.Ks V₀ = ρ
    rw [hdKs]
    exact hE.moments.1
  have hdm : d.ms = 0 := by
    change moment 1 d.Ks V₀ = 0
    rw [hdKs]
    exact hE.moments.2.1
  have hdq : d.qs = 0 := rfl
  have hMV : ∀ a, d.MV a = vIP g₀ a • ρ := fun a => by
    simp only [StepData.MV, hdρ, hdm, hdq, smul_zero, add_zero]
  have hMX : ∀ y, d.MX y = ⟪y, ρ⟫ • g₀ := fun y => by
    simp only [StepData.MX, hdρ, hdm, hdq, inner_zero_right, zero_smul, add_zero]
  have htop : ∀ y : Ex, y ∈ Submodule.span ℝ (Set.range d.Xh) := fun y => by
    have h1 : Submodule.span ℝ (Set.range ⇑b) = ⊤ := by
      rw [← b.coe_toBasis]
      exact b.toBasis.span_eq
    change y ∈ Submodule.span ℝ (Set.range ⇑b)
    rw [h1]
    exact Submodule.mem_top
  have hqr : ∀ i : Fin r, ⟪b i, ρ⟫ • g₀ = ∑ j, S i j • V₀ j := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hij => by simp [S, hij.symm]) (by simp)]
    by_cases hi : i = i₀
    · subst hi
      have h2 : ⟪b i₀, ρ⟫ = ‖ρ‖ := by
        rw [hρb, inner_smul_right, b.inner_eq_ite]
        simp [norm_smul, b.norm_eq_one]
      have h3 : V₀ i₀ = hermiteP 0 := rfl
      have hSii : S i₀ i₀ = s := by simp [S, w]
      rw [h2, hSii, h3, ← smul_hermiteP_zero, smul_smul, ← hc, hs, mul_comm]
    · have h2 : ⟪b i, ρ⟫ = 0 := by
        rw [hρb, inner_smul_right, b.inner_eq_ite]
        simp [hi]
      simp [h2, S, w, hi]
  have hstep : d.IsLowRankBGKStep ev D 0 Δt sch K₀ V₀ K₀ V₀ :=
    { orth_V := hV₀
      proper_V := hprop
      orth_Xs := b.orthonormal
      kstep := fun j => by
        have h1 : ∀ l, D (K₀ l) = 0 := fun l => by
          by_cases hl : l = i₀
          · simp [K₀, hl, hD]
          · simp [K₀, hl]
        simp only [h1, smul_zero, Finset.sum_const_zero, sub_zero]
        exact hKs j
      sstep := fun i j => by
        have h1 : ∀ k l, vIP (X * V₀ j) (V₀ l) * ⟪b i, D (b k)⟫ * S k l = 0 := fun k l => by
          rw [mul_assoc, hDS, mul_zero]
        change S i j = S i j + Δt * ∑ k, ∑ l, vIP (X * V₀ j) (V₀ l) * ⟪b i, D (b k)⟫ * S k l
        simp only [h1, Finset.sum_const_zero, mul_zero, add_zero]
      orth_Vs := hV₀
      lstep := fun i => by
        have h1 : ∀ k, ⟪b i, D (b k)⟫ • (X * d.L₂ V₀ k) = 0 := fun k => by
          simp only [StepData.L₂, Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
          exact Finset.sum_eq_zero fun j _ => by
            have := hDS i k j
            simp only [d, this, zero_smul]
        change ∑ j, S i j • V₀ j = d.L₂ V₀ i - Δt • ∑ k, ⟪b i, D (b k)⟫ • (X * d.L₂ V₀ k)
        rw [Finset.sum_eq_zero fun k _ => h1 k, smul_zero, sub_zero]
        rfl
      proper_Vs := (degreeLT_mono (by norm_num)).trans hprop
      rho_ne := fun x => by rw [hdρ]; exact hρ x
      qs_eq := fun x => by
        rw [hdm, hdq]
        simp
      xstep := fun j => by
        rw [zero_smul, hMV]
        simp [d, V₀]
      orth_Xh := b.orthonormal
      Xh_left := fun _ => rfl
      augment := fun _ => htop _
      hlstep_left := fun i => by
        rw [zero_smul, hMX]
        simp [d]
      hlstep_right := fun i => i.elim0
      orth_Vh := hV₀
      qr := hqr
      orth_Us := by simp [d]
      orth_Ws := by simp [d]
      svd := by simp [d, S]
      sorted := fun i j hij => by
        change w j ≤ w i
        by_cases hj : j = i₀
        · have hi : i = i₀ := by
            apply Fin.ext
            have : (i : ℕ) ≤ j := hij
            rw [hj] at this
            simpa [i₀] using this
          simp [w, hi, hj]
        · by_cases hi : i = i₀
          · simpa [w, hi, hj] using hspos
          · simp [w, hi, hj]
      nonneg := fun i => by
        change 0 ≤ w i
        simp only [w]
        split_ifs
        · exact hspos
        · exact le_rfl
      K_out := fun j => by
        change K₀ j = w j • ∑ i, (1 : Matrix (Fin r) (Fin r) ℝ) i j • b i
        rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
        by_cases hj : j = i₀
        · subst hj
          simp [K₀, w, hsb]
        · simp [K₀, w, hj]
      V_out := fun j => by
        change V₀ j = ∑ i, (1 : Matrix (Fin r) (Fin r) ℝ) i j • V₀ i
        rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
        simp }
  refine ⟨fun _ => K₀, fun _ => V₀, fun _ => ⟨d, K₀, V₀, hstep, fun _ _ => rfl⟩,
    fun _ _ => rfl, hE.fval_eq, fun x => ?_⟩
  rw [hE.density_eq']
  exact hρ x

/-- Non-vacuity of `theorem_5_1` and `theorem_5_1_rate` on a grid of six points: the hypotheses hold
for the Hermite basis, with `ρ ≡ 1` and `D = 0`.  (By `exists_stationary_run` the same holds for
every `D` with `D ρ = 0`.) -/
example (Δt : ℝ) (sch : Variant) :
    ∃ (K : ℕ → Fin 6 → EuclideanSpace ℝ (Fin 6)) (V : ℕ → Fin 6 → ℝ[X]),
      IsRun (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap 0 Δt sch 0 K V ∧
      (∀ n j, V n j = hermiteP j) ∧
      (∀ x v, fval (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap (K 0) (V 0) x v =
        maxwellianExpansion (density (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap (K 0) (V 0) x)
          (meanVelocity (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap (K 0) (V 0) x) v) ∧
      ∀ x, density (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap (K 0) (V 0) x ≠ 0 := by
  let ρ : EuclideanSpace ℝ (Fin 6) := WithLp.toLp 2 fun _ => 1
  have hρ : ∀ x, (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap ρ x ≠ 0 := fun x => by
    simp [ρ]
  have hρ0 : ρ ≠ 0 := fun h => hρ 0 (by simp [h])
  exact exists_stationary_run (by simp) le_rfl _ 0 hρ hρ0 rfl sch

end NonVacuous

end Scheme

/-! ### Non-vacuity of the penalized setting -/

section PenalizedExample

open Polynomial

/-- The spatially homogeneous BGK operator with the Maxwellian (5.2) of arXiv 2502.08951, as an
instance of `PenalizedSetting`: `E` is the space of velocity functions and the transport term
vanishes. -/
noncomputable def bgkSetting : PenalizedSetting ℝ ℝ[X] (ℝ × ℝ) where
  val := LinearMap.pi pointL
  mom := (momL 0).prod (momL 1)
  mx U := U.1 • g₀ + U.2 • g₁ + (U.2 ^ 2 / U.1) • g₂
  coll f := (momL 0 f • g₀ + momL 1 f • g₁ + (momL 1 f ^ 2 / momL 0 f) • g₂) - f
  adv := 0
  mom_mx U := by
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, -⟩ := momL_table
    refine Prod.ext ?_ ?_
    · change momL 0 (U.1 • g₀ + U.2 • g₁ + (U.2 ^ 2 / U.1) • g₂) = U.1
      rw [map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3]
      simp
    · change momL 1 (U.1 • g₀ + U.2 • g₁ + (U.2 ^ 2 / U.1) • g₂) = U.2
      rw [map_add, map_add, map_smul, map_smul, map_smul, h4, h5, h6]
      simp
  mom_coll f := by
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, -⟩ := momL_table
    refine Prod.ext ?_ ?_
    · change momL 0 ((momL 0 f • g₀ + momL 1 f • g₁ + (momL 1 f ^ 2 / momL 0 f) • g₂) - f) = 0
      rw [map_sub, map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3]
      simp
    · change momL 1 ((momL 0 f • g₀ + momL 1 f • g₁ + (momL 1 f ^ 2 / momL 0 f) • g₂) - f) = 0
      rw [map_sub, map_add, map_add, map_smul, map_smul, map_smul, h4, h5, h6]
      simp

lemma bgkSetting_coll (f : ℝ[X]) : bgkSetting.coll f = bgkSetting.maxw f - f := rfl

/-- Non-vacuity of `PenalizedSetting.abs_dev_le_pow` and `PenalizedSetting.exists_first_order`: from
every `f₀` the limit scheme with `λ = 1` runs, with `𝒟* = 0` (so `α = 0`) and vanishing brackets. -/
example (Δt : ℝ) (f₀ : ℝ[X]) :
    ∃ f : ℕ → ℝ[X], f 0 = f₀ ∧ ∀ n, bgkSetting.IsPenalizedBGKStep 0 1 Δt (f n) (f n) (f (n + 1)) ∧
      bgkSetting.IsMultiplier 1 (f n) (fun _ => 0) ∧
      ∀ ξ, bgkSetting.bracket Δt (f n) (f n) ξ = 0 := by
  refine ⟨fun n => Nat.rec f₀ (fun _ g => bgkSetting.maxw g) n, rfl, fun n => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · simp [bgkSetting]
  · rw [zero_smul, bgkSetting_coll]
    simp
  · simpa using PenalizedSetting.bgk_isMultiplier bgkSetting_coll 1 _
  · intro ξ
    simp [PenalizedSetting.bracket]

end PenalizedExample

end LeanDLRA.Literature.P2502_08951
