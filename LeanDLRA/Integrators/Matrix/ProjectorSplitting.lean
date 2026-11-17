import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Integrators.ProjectorSplitting

/-!
# The projector-splitting (KSL) integrator for matrices

This file instantiates the abstract robust error analysis of the projector-splitting integrator
(`LeanDLRA/Integrators/ProjectorSplitting.lean`) for real `m × n` matrices with the Frobenius
norm, **at the level of the factors** that the algorithm actually computes.

## The algorithm

Lubich–Oseledets, *A projector-splitting integrator for dynamical low-rank approximation*
(BIT 2014, [LubichOseledets2014, §3.1]–3.2, steps 1.–3. and (12)); Ceruti–Lubich,
[CerutiLubich2022], §2 (the "KSL" form for a general right-hand side `F`). One step from
`Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁ = t₀ + h` reads:

* **K-step**: `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`; QR factorization `K(t₁) = U₁ Ŝ₁` with
  `U₁ᵀ U₁ = I`;
* **backward S-step**: `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, `S(t₀) = Ŝ₁`;
* **L-step**: `L' = F(t, U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S(t₁)ᵀ`; the new approximation is
  `Y₁ = U₁ L(t₁)ᵀ`, and a QR factorization `L(t₁) = V₁ S₁ᵀ` gives `Y₁ = U₁ S₁ V₁ᵀ`.

The factor fields are `kField`, `sField` and `lField`; one step is bundled in `IsStep`.

## Main results

* `odeSolution_kField`, `odeSolution_sField`, `odeSolution_lField`: the factor trajectories lift
  to the full-space trajectories of the abstract integrator,
  `YK = K V₀ᵀ` solves `YK' = Q₀ F(t, YK)`, `YS = U₁ S V₀ᵀ` solves `YS' = -P₁ Q₀ F(t, YS)` and
  `YL = U₁ Lᵀ` solves `YL' = P₁ F(t, YL)`, with `P₁ = leftProj U₁ = (X ↦ U₁ U₁ᵀ X)` and
  `Q₀ = rightProj V₀ = (X ↦ X V₀ V₀ᵀ)`.
* `IsStep.isKSLStep`: the factor trajectories of one step satisfy all hypotheses of the abstract
  step `IsKSLStep` (including the capture `P₁ (K(t₁) V₀ᵀ) = K(t₁) V₀ᵀ` and the matching initial
  values), given the normal-component bound at the point `U₁ Ŝ₁ V₀ᵀ` of the manifold.
* `IsStep.local_error` (Kieri–Lubich–Walach 2016, Theorem 2.1; Theorem 2 of [CerutiLubich2022],
  local part): under the **factored normal-component assumption**
  `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for all `t`, all cores `S` and all `U`, `V` with
  orthonormal columns, `‖U₁ L(t₁)ᵀ - A(t₁)‖ ≤ h (11 L B h + ε)`; `IsStep.local_error_sharp`
  gives the constant `10`, `IsStep.proj_error` the bound `‖Y₁ - U₁ U₁ᵀ A(t₁)‖ ≤ 6 L B h²` and
  `IsStep.capture` the K-step capture bound `‖(I - U₁ U₁ᵀ) A(t₁)‖ ≤ h (4 L B h + ε)`.
* `global_error` (Theorem 2.1 of Kieri–Lubich–Walach, Theorem 2 of [CerutiLubich2022]): for the
  matrix KSL integrator over `n` steps, `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h` with
  `c₀ = e^{L T}`, `c₁ = T e^{L T}`, `c₂ = 11 L B T e^{L T}`.
* `IsStep.local_error_of_pointwise`, `IsStep.local_error_sharp_of_pointwise`,
  `IsStep.capture_of_pointwise`, `global_error_of_pointwise`: the same bounds with the
  normal-component bound assumed **only where it is used**, at the K-step result
  `U₁ Ŝ₁ V₀ᵀ` of each step and for `t` in that step (see the deviations below).
* `exists_qr`: the QR step exists (for `r ≤ m`, also for rank-deficient `K(t₁)`).
* Satisfiability: an `example` with a constant field `F ≡ C` on `2 × 2` matrices of rank `1`,
  where all hypotheses of `IsStep.local_error` hold (with `L = 0`, `ε = B = ‖C‖`); an `example`
  for `global_error` with one step; and `radial_normal_eq_zero` with an `example` showing that
  the field hypotheses also hold with `L = 2`, `B = 1` and `ε = 0` for the nonconstant radial
  retraction `Y ↦ Y / max(‖Y‖, 1)`.

## Deviations from the papers

* The orthonormality of `U₀` is not needed (only `Y₀ = U₀ S₀ V₀ᵀ` and `Q₀ = V₀ V₀ᵀ·` enter
  the K-step); it is therefore not assumed.  `V₀` and `U₁` have orthonormal columns.
* **The factored assumption is global, the paper's is local.**  Kieri–Lubich–Walach (Theorem
  2.1, as quoted in [CerutiLubich2022, Thm. 2], assumption 2) require
  `‖(I - P(Y)) F(t, Y)‖ ≤ ε` only for `0 ≤ t ≤ T` and for `Y ∈ M_r` *in a neighbourhood of
  `A(t)`*; for `Y = U S Vᵀ ∈ M_r` (`S` invertible) `(I - P(Y)) Z = (I - UUᵀ) Z (I - VVᵀ)`.
  The hypothesis `hε` of `IsStep.local_error`, `IsStep.local_error_sharp`, `IsStep.capture`,
  `IsStep.isKSLStep_of_factored` and `global_error` instead quantifies over **all** `t ∈ ℝ`,
  all `U`, `V` with orthonormal columns and all cores `S`, singular ones included.  This is
  strictly stronger and can make `ε` much larger than the paper's: since singular cores are
  allowed it constrains `F` at rank-deficient points; e.g. if `m, n > r`, taking `S = 0` and
  `U`, `V` orthogonal to a top singular pair of `F(t, 0)` forces `ε ≥ ‖F(t, 0)‖₂` for every
  `t`.  In the paper's main example `F(t, Y) = Ȧ(t)` with `rank A(t) = r`, the paper's `ε` is
  (close to) `0` while `hε` needs `ε ≥ sup_t ‖Ȧ(t)‖₂`.  For `F t` continuous, `hε` is
  equivalent to the paper's assumption imposed on *all* of `M_r` (one direction is
  `factored_normal_of_manifold` in `Integrators/ProjectorSplitting.lean`, the other is the
  identity above), but not to its neighbourhood version.
* Only the instance of `hε` at the K-step result `Y = U₁ Ŝ₁ V₀ᵀ`, for `t ∈ [t₀, t₁]`, is used.
  The `_of_pointwise` variants take exactly this instance as hypothesis.  When `Ŝ₁` is
  invertible and `U₁ Ŝ₁ V₀ᵀ` lies in the neighbourhood of `A(t)` where the paper's assumption
  holds, this hypothesis *is* the paper's assumption at that point; we do not prove that the
  iterates stay in such a neighbourhood.  `S` need not be invertible.
* Kieri–Lubich–Walach 2016 is not available in `papers/txt`; its attribution (including the
  "local part" of Theorem 2.1) rests on the summary in [CerutiLubich2022] (Theorem 2, eq. (5),
  §3.4).  The explicit constants (`11` resp. `10` for `L B h²`, coefficient `1` for `ε h`,
  `c₂ = 11 L B T e^{L T}`) are this library's own, from the direct proof in
  `Integrators/ProjectorSplitting.lean`; for `δ = 0` they are sharper than the local bound
  `ϑ = (4 e^{L h} B L + 9 B L) h² + (3 e^{L h} + 4) ε h + e^{L h} δ` quoted in
  [CerutiLubich2022, eq. (5)].
* As in the abstract file, the exact substep solutions and the exact flows from the numerical
  values are hypotheses (`ODESolution`); their existence for globally Lipschitz, time-continuous
  `F` is `Foundations/Existence.lean`.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixKSL

/-! ### Lifting factor trajectories along continuous linear maps -/

section Lift

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- **Lifting a solution.**  If a continuous linear map `Φ` intertwines two vector fields,
`g t (Φ x) = Φ (f t x)`, then it maps solutions of `y' = f(t, y)` to solutions of
`z' = g(t, z)`.  With `Φ K = K V₀ᵀ` etc. this lifts the factor ODEs of an integrator to the
full-space trajectories of the abstract theory. -/
theorem odeSolution_comp_clm {f : ℝ → E → E} {g : ℝ → E' → E'} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (Φ : E →L[ℝ] E') (h : ∀ t x, g t (Φ x) = Φ (f t x)) :
    ODESolution g (fun t => Φ (y t)) a b where
  cont := Φ.continuous.comp_continuousOn hy.cont
  deriv t ht := by
    rw [h]
    exact Φ.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)

omit [NormedAddCommGroup E'] [NormedSpace ℝ E'] in
/-- The affine function `t ↦ y₀ + (t - a) c` solves the ODE with the constant field `c` (used
in the satisfiability examples, where `F` is constant and all substeps are explicit). -/
theorem odeSolution_affine (y₀ c : E) (a b : ℝ) :
    ODESolution (fun _ _ => c) (fun t => y₀ + (t - a) • c) a b where
  cont := by fun_prop
  deriv t _ := by
    have h : HasDerivAt (fun t : ℝ => y₀ + (t - a) • c) c t := by
      simpa using (((hasDerivAt_id t).sub_const a).smul_const c).const_add y₀
    exact h.hasDerivWithinAt

end Lift

/-! ### Normal components of matrices -/

section Normal

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r]

/-- The normal component `(I - U Uᵀ) Z (I - V Vᵀ)` never exceeds `Z` in Frobenius norm when
`U` and `V` have orthonormal columns. -/
theorem norm_normal_le {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) : ‖(1 - U * Uᵀ) * Z * (1 - V * Vᵀ)‖ ≤ ‖Z‖ := by
  rw [← one_sub_leftProj_one_sub_rightProj_apply]
  exact ((isOrthProj_leftProj hU).compl.norm_le _).trans
    ((isOrthProj_rightProj hV).compl.norm_le _)

/-- A constant field `F ≡ C` satisfies the factored normal-component assumption with
`ε = ‖C‖`. -/
theorem normal_const_le (C : Matrix m n ℝ) (t : ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖(1 - U * Uᵀ) * (fun (_ : ℝ) (_ : Matrix m n ℝ) => C) t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤
      ‖C‖ :=
  norm_normal_le hU hV C

/-- A field of the form `F(t, Y) = c(t, Y) Y` is tangent on all factored matrices: its normal
component at `U S Vᵀ` vanishes, for every core `S` (singular ones included), so it satisfies
the factored normal-component assumption with `ε = 0`. -/
theorem normal_smul_self_eq_zero {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (c : ℝ) :
    (1 - U * Uᵀ) * (c • (U * S * Vᵀ)) * (1 - V * Vᵀ) = 0 := by
  have h0 : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0]
  simp

end Normal

/-! ### A nonconstant tangent field: the radial retraction -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction `x ↦ x / max(‖x‖, 1)` onto the closed unit ball. -/
noncomputable def radial (x : E) : E := (max ‖x‖ 1)⁻¹ • x

omit [NormedSpace ℝ E] in
/-- The normalizing factor of `radial` is at least `1`. -/
lemma one_le_max_norm (x : E) : 1 ≤ max ‖x‖ 1 := le_max_right _ _

/-- The radial retraction is bounded by `1`. -/
theorem norm_radial_le (x : E) : ‖radial x‖ ≤ 1 := by
  have ha : 0 < max ‖x‖ 1 := one_pos.trans_le (one_le_max_norm x)
  rw [radial, norm_smul, norm_inv, Real.norm_of_nonneg ha.le, inv_mul_le_iff₀ ha, mul_one]
  exact le_max_left _ _

/-- The radial retraction is `2`-Lipschitz. -/
theorem norm_radial_sub_le (x y : E) : ‖radial x - radial y‖ ≤ 2 * ‖x - y‖ := by
  set a := max ‖x‖ 1 with ha_def
  set b := max ‖y‖ 1 with hb_def
  have ha1 : 1 ≤ a := one_le_max_norm x
  have hb1 : 1 ≤ b := one_le_max_norm y
  have ha : 0 < a := one_pos.trans_le ha1
  have hb : 0 < b := one_pos.trans_le hb1
  have hyb : ‖y‖ ≤ b := le_max_left _ _
  have hab : |b - a| ≤ ‖x - y‖ :=
    (abs_max_sub_max_le_abs _ _ _).trans
      ((abs_sub_comm _ _).le.trans (abs_norm_sub_norm_le x y))
  have hsplit : radial x - radial y = a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y := by
    simp only [radial, ← ha_def, ← hb_def, smul_sub, sub_smul]
    abel
  have h1 : ‖a⁻¹ • (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ha1)
  have h2 : ‖(a⁻¹ - b⁻¹) • y‖ ≤ ‖x - y‖ := by
    rw [norm_smul, inv_sub_inv ha.ne' hb.ne', Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos ha hb), div_mul_eq_mul_div, div_le_iff₀ (mul_pos ha hb)]
    exact mul_le_mul hab (hyb.trans (le_mul_of_one_le_left hb.le ha1)) (norm_nonneg _)
      (norm_nonneg _)
  rw [hsplit]
  linarith [norm_add_le (a⁻¹ • (x - y)) ((a⁻¹ - b⁻¹) • y)]

end Radial

/-! ### The radial retraction satisfies the field hypotheses with `ε = 0` -/

section RadialField

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r]

/-- The radial retraction `F(t, Y) = Y / max(‖Y‖, 1)` satisfies the factored normal-component
assumption with `ε = 0` (it is a scalar multiple of `Y`, `normal_smul_self_eq_zero`). -/
theorem radial_normal_eq_zero (t : ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ)
    (V : Matrix n r ℝ) (hU : Uᵀ * U = 1) (_hV : Vᵀ * V = 1) :
    ‖(1 - U * Uᵀ) * (fun (_ : ℝ) (Y : Matrix m n ℝ) => radial Y) t (U * S * Vᵀ) *
      (1 - V * Vᵀ)‖ ≤ 0 := by
  simp only [radial, normal_smul_self_eq_zero hU, norm_zero, le_refl]

/-- **The field hypotheses are not limited to `ε ≈ B` or `L = 0`**: the nonconstant radial
retraction `F(t, Y) = Y / max(‖Y‖, 1)` on `2 × 2` matrices is `2`-Lipschitz, bounded by `1`, and
satisfies the factored normal-component assumption of `IsStep.local_error` and `global_error`
for rank `1` with `ε = 0`. -/
example :
    IsLipschitzField (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => radial Y) 2 ∧
      IsBoundedField (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => radial Y) 1 ∧
      ∀ t (U : Matrix (Fin 2) (Fin 1) ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ)
        (V : Matrix (Fin 2) (Fin 1) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 →
        ‖(1 - U * Uᵀ) * (fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => radial Y) t (U * S * Vᵀ) *
          (1 - V * Vᵀ)‖ ≤ 0 :=
  ⟨fun _ x y => norm_radial_sub_le x y, fun _ x => norm_radial_le x, radial_normal_eq_zero⟩

end RadialField

/-! ### The factor fields of the KSL integrator -/

section Fields

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- The K-step field `K ↦ F(t, K V₀ᵀ) V₀` ([LubichOseledets2014, §3.1], step 1; [CerutiLubich2022],
§2). -/
def kField (V₀ : Matrix n r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (K : Matrix m r ℝ) : Matrix m r ℝ :=
  F t (K * V₀ᵀ) * V₀

/-- The backward S-step field `S ↦ -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀` ([LubichOseledets2014, §3.1], step 2;
[CerutiLubich2022, §2]). -/
def sField (U₁ : Matrix m r ℝ) (V₀ : Matrix n r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (S : Matrix r r ℝ) : Matrix r r ℝ :=
  -(U₁ᵀ * F t (U₁ * S * V₀ᵀ) * V₀)

/-- The L-step field `L ↦ F(t, U₁ Lᵀ)ᵀ U₁` ([LubichOseledets2014, §3.1], step 3; [CerutiLubich2022],
§2). -/
def lField (U₁ : Matrix m r ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t : ℝ)
    (L : Matrix n r ℝ) : Matrix n r ℝ :=
  (F t (U₁ * Lᵀ))ᵀ * U₁

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}

/-- **K-step lift.**  If `K' = F(t, K V₀ᵀ) V₀`, then `YK = K V₀ᵀ` solves
`YK' = Q₀ F(t, YK)` with `Q₀ = rightProj V₀`. -/
theorem odeSolution_kField {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ}
    (hK : ODESolution (kField V₀ F) K t₀ t₁) :
    ODESolution (fun t x => rightProj V₀ (F t x)) (fun t => K t * V₀ᵀ) t₀ t₁ :=
  odeSolution_comp_clm hK (Frobenius.rightMulCLM V₀ᵀ) fun t x => by
    simp only [Frobenius.rightMulCLM_apply, rightProj_apply, kField]

/-- **S-step lift.**  If `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, then `YS = U₁ S V₀ᵀ` solves
`YS' = -P₁ Q₀ F(t, YS)` with `P₁ = leftProj U₁`, `Q₀ = rightProj V₀`. -/
theorem odeSolution_sField {U₁ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} {S : ℝ → Matrix r r ℝ}
    (hS : ODESolution (sField U₁ V₀ F) S t₀ t₁) :
    ODESolution (fun t x => -leftProj U₁ (rightProj V₀ (F t x))) (fun t => U₁ * S t * V₀ᵀ)
      t₀ t₁ :=
  odeSolution_comp_clm hS ((Frobenius.rightMulCLM V₀ᵀ).comp (Frobenius.leftMulCLM U₁))
    fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftProj_rightProj_apply, sField, Matrix.mul_neg,
        Matrix.neg_mul]

/-- **L-step lift.**  If `L' = F(t, U₁ Lᵀ)ᵀ U₁`, then `YL = U₁ Lᵀ` solves `YL' = P₁ F(t, YL)`
with `P₁ = leftProj U₁`. -/
theorem odeSolution_lField {U₁ : Matrix m r ℝ} {Lf : ℝ → Matrix n r ℝ}
    (hL : ODESolution (lField U₁ F) Lf t₀ t₁) :
    ODESolution (fun t x => leftProj U₁ (F t x)) (fun t => U₁ * (Lf t)ᵀ) t₀ t₁ :=
  odeSolution_comp_clm hL ((Frobenius.leftMulCLM U₁).comp Frobenius.transposeCLM) fun t x => by
    simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
      Frobenius.transposeCLM_apply, leftProj_apply, lField, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]

end Fields

/-! ### One step of the matrix KSL integrator -/

section Step

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- **One step of the matrix projector-splitting (KSL) integrator** from `Y₀ = U₀ S₀ V₀ᵀ` at
`t₀` to `t₁` ([LubichOseledets2014, §3.1]–3.2; [CerutiLubich2022, §2]), at the factor level:

* K-step `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and QR factorization `K(t₁) = U₁ Ŝ₁` with
  `U₁ᵀ U₁ = I`;
* backward S-step `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, `S(t₀) = Ŝ₁`;
* L-step `L' = F(t, U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S(t₁)ᵀ`.

The new approximation is `Y₁ = U₁ L(t₁)ᵀ`.  `V₀` has orthonormal columns; `U₀` need not. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (U₁ : Matrix m r ℝ) (Ŝ₁ : Matrix r r ℝ)
    (K : ℝ → Matrix m r ℝ) (S : ℝ → Matrix r r ℝ) (Lf : ℝ → Matrix n r ℝ) : Prop where
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = F(t, K V₀ᵀ) V₀`. -/
  kSol : ODESolution (kField V₀ F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- QR factorization of the K-step result. -/
  kQR : K t₁ = U₁ * Ŝ₁
  /-- Backward S-step `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`. -/
  sSol : ODESolution (sField U₁ V₀ F) S t₀ t₁
  sStart : S t₀ = Ŝ₁
  /-- L-step `L' = F(t, U₁ Lᵀ)ᵀ U₁`. -/
  lSol : ODESolution (lField U₁ F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * (S t₁)ᵀ

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ U₁ : Matrix m r ℝ}
  {S₀ Ŝ₁ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ} {S : ℝ → Matrix r r ℝ}
  {Lf : ℝ → Matrix n r ℝ}

namespace IsStep

/-- The new left basis captures the K-step result: `U₁ U₁ᵀ K(t₁) V₀ᵀ = K(t₁) V₀ᵀ`. -/
theorem kCap (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) :
    leftProj U₁ (K t₁ * V₀ᵀ) = K t₁ * V₀ᵀ := by
  rw [hs.kQR, Matrix.mul_assoc]
  exact leftProj_mul_left hs.orthU₁ _

/-- The new approximation `Y₁ = U₁ L(t₁)ᵀ` lies in the range of the new left basis
(`ksl_mem_range`; no normal-component bound is needed). -/
theorem mem_range (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) (hle : t₀ ≤ t₁) :
    leftProj U₁ (U₁ * (Lf t₁)ᵀ) = U₁ * (Lf t₁)ᵀ :=
  ksl_mem_range (YK := fun t => K t * V₀ᵀ) (YS := fun t => U₁ * S t * V₀ᵀ)
    (YL := fun t => U₁ * (Lf t)ᵀ) (isOrthProj_leftProj hs.orthU₁) hs.kCap
    (odeSolution_sField hs.sSol) (by simp only [hs.sStart, hs.kQR])
    (odeSolution_lField hs.lSol)
    (by simp only [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]) hle t₁ ⟨hle, le_rfl⟩

omit [Fintype m] [Fintype n] [DecidableEq r] in
/-- With a QR factorization `L(t₁) = V₁ S₁ᵀ` of the L-step result, `Y₁ = U₁ S₁ V₁ᵀ`. -/
theorem eq_factored {V₁ : Matrix n r ℝ} {S₁ : Matrix r r ℝ} (hQR : Lf t₁ = V₁ * S₁ᵀ) :
    U₁ * (Lf t₁)ᵀ = U₁ * S₁ * V₁ᵀ := by
  rw [hQR, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

variable [DecidableEq m] [DecidableEq n]

/-- **The factor trajectories satisfy the abstract hypotheses.**  One step of the matrix KSL
integrator (`IsStep`) gives an abstract KSL step (`IsKSLStep`) with `P₁ = leftProj U₁`,
`Q₀ = rightProj V₀`, `Y₀ = U₀ S₀ V₀ᵀ` and full-space trajectories `YK = K V₀ᵀ`,
`YS = U₁ S V₀ᵀ`, `YL = U₁ Lᵀ`, provided the normal component at `U₁ Ŝ₁ V₀ᵀ = K(t₁) V₀ᵀ` is
`ε`-small. -/
theorem isKSLStep (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε) :
    IsKSLStep F ε (leftProj U₁) (rightProj V₀) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ)
      (fun t => U₁ * S t * V₀ᵀ) (fun t => U₁ * (Lf t)ᵀ) where
  projP₁ := isOrthProj_leftProj hs.orthU₁
  projQ₀ := isOrthProj_rightProj hs.orthV₀
  kSol := odeSolution_kField hs.kSol
  kStart := by simp only [hs.kStart]
  kCap := hs.kCap
  kNormal t ht := by
    rw [one_sub_leftProj_one_sub_rightProj_apply, hs.kQR]
    exact hε t ht
  sSol := odeSolution_sField hs.sSol
  sStart := by simp only [hs.sStart, hs.kQR]
  lSol := odeSolution_lField hs.lSol
  lStart := by
    simp only [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The abstract step under the **factored normal-component assumption**
`∀ t U S V, Uᵀ U = 1 → Vᵀ V = 1 → ‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε`.  This assumption
is global (all `t`, all cores `S`, singular ones included), stronger than the paper's
assumption near `A(t)`; only its instance at `U₁ Ŝ₁ V₀ᵀ` is used (`IsStep.isKSLStep`). -/
theorem isKSLStep_of_factored (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε) :
    IsKSLStep F ε (leftProj U₁) (rightProj V₀) t₀ t₁ (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ)
      (fun t => U₁ * S t * V₀ᵀ) (fun t => U₁ * (Lf t)ᵀ) :=
  hs.isKSLStep fun t _ => hε t U₁ Ŝ₁ V₀ hs.orthU₁ hs.orthV₀

variable {L B : ℝ} {h : ℝ} {A : ℝ → Matrix m n ℝ}

omit [DecidableEq m] [DecidableEq n] in
/-- **Error in the range of `U₁`** (proof of Kieri–Lubich–Walach 2016, Theorem 2.1; see
`ksl_proj_error`): `‖U₁ L(t₁)ᵀ - U₁ U₁ᵀ A(t₁)‖ ≤ 6 L B h²`.  No normal-component bound is
needed. -/
theorem proj_error (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * (Lf t₁)ᵀ - U₁ * U₁ᵀ * A t₁‖ ≤ h * (6 * L * B * h) := by
  have hk := ksl_proj_error (P₁ := leftProj U₁) (Q₀ := rightProj V₀) (Y₀ := U₀ * S₀ * V₀ᵀ)
    (YK := fun t => K t * V₀ᵀ) (YS := fun t => U₁ * S t * V₀ᵀ)
    (YL := fun t => U₁ * (Lf t)ᵀ) hF hL hB (isOrthProj_leftProj hs.orthU₁)
    (isOrthProj_rightProj hs.orthV₀) ht₁ hh hA hA₀ (odeSolution_kField hs.kSol)
    (by simp only [hs.kStart]) hs.kCap (odeSolution_sField hs.sSol)
    (by simp only [hs.sStart, hs.kQR]) (odeSolution_lField hs.lSol)
    (by simp only [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc])
  rwa [leftProj_apply] at hk

/-- **K-step capture, pointwise normal-component bound**: if the normal component of `F` at the
K-step result `U₁ Ŝ₁ V₀ᵀ` is `ε`-small for `t ∈ [t₀, t₁]`, then
`‖(I - U₁ U₁ᵀ) A(t₁)‖ ≤ h (4 L B h + ε)`.  See `IsStep.capture`. -/
theorem capture_of_pointwise (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖(1 - U₁ * U₁ᵀ) * A t₁‖ ≤ h * (4 * L * B * h + ε) := by
  have hk := hs.isKSLStep hε
  rw [← one_sub_leftProj_apply]
  exact kstep_capture hF hL hB hk.projP₁ hk.projQ₀ ht₁ hh hA hk.kSol (hk.kStart.trans hA₀.symm)
    hk.kCap hk.kNormal

/-- **K-step capture** (the statement of Ceruti–Lubich, [CerutiLubich2022, Lemma 2], in the KSL
setting, with exact initial value `δ = 0`): under the (global) factored normal-component
assumption, `‖(I - U₁ U₁ᵀ) A(t₁)‖ ≤ h (4 L B h + ε)`.  Ceruti–Lubich bound this quantity by
the Kieri–Lubich–Walach local error `ϑ = (4 e^{L h} B L + 9 B L) h² + (3 e^{L h} + 4) ε h`
(their eq. (5)); the explicit bound here is sharper and comes from a direct proof
(`kstep_capture`). -/
theorem capture (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖(1 - U₁ * U₁ᵀ) * A t₁‖ ≤ h * (4 * L * B * h + ε) :=
  hs.capture_of_pointwise hF hL hB (fun t _ => hε t U₁ Ŝ₁ V₀ hs.orthU₁ hs.orthV₀) ht₁ hh hA hA₀

/-- **Robust local error, sharp constant, pointwise normal-component bound**: if the normal
component of `F` at the K-step result `U₁ Ŝ₁ V₀ᵀ` is `ε`-small for `t ∈ [t₀, t₁]`, then
`‖U₁ L(t₁)ᵀ - A(t₁)‖ ≤ h (10 L B h + ε)`. -/
theorem local_error_sharp_of_pointwise (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * (Lf t₁)ᵀ - A t₁‖ ≤ h * (10 * L * B * h + ε) := by
  have hk := hs.isKSLStep hε
  exact ksl_local_error_sharp (P₁ := leftProj U₁) (Q₀ := rightProj V₀) (Y₀ := U₀ * S₀ * V₀ᵀ)
    (YK := fun t => K t * V₀ᵀ) (YS := fun t => U₁ * S t * V₀ᵀ)
    (YL := fun t => U₁ * (Lf t)ᵀ) hF hL hB hk.projP₁ hk.projQ₀ ht₁ hh hA hA₀ hk.kSol
    hk.kStart hk.kCap hk.kNormal hk.sSol hk.sStart hk.lSol hk.lStart

/-- **Robust local error of the matrix KSL integrator, sharp constant**: under the hypotheses of
`IsStep.local_error`, `‖U₁ L(t₁)ᵀ - A(t₁)‖ ≤ h (10 L B h + ε)`. -/
theorem local_error_sharp (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * (Lf t₁)ᵀ - A t₁‖ ≤ h * (10 * L * B * h + ε) :=
  hs.local_error_sharp_of_pointwise hF hL hB (fun t _ => hε t U₁ Ŝ₁ V₀ hs.orthU₁ hs.orthV₀) ht₁
    hh hA hA₀

/-- **Robust local error, pointwise normal-component bound**: the conclusion
`‖U₁ L(t₁)ᵀ - A(t₁)‖ ≤ h (11 L B h + ε)` of `IsStep.local_error` under the hypothesis that is
actually used, the normal-component bound at the K-step result `U₁ Ŝ₁ V₀ᵀ` for
`t ∈ [t₀, t₁]`.  If `Ŝ₁` is invertible this is the assumption of Kieri–Lubich–Walach (as
quoted in [CerutiLubich2022, Thm. 2], assumption 2) at the single point `Y = U₁ Ŝ₁ V₀ᵀ ∈ M_r`;
`Ŝ₁` may also be singular. -/
theorem local_error_of_pointwise (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - U₁ * U₁ᵀ) * F t (U₁ * Ŝ₁ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * (Lf t₁)ᵀ - A t₁‖ ≤ h * (11 * L * B * h + ε) :=
  (hs.isKSLStep hε).local_error hF hL hB ht₁ hh hA hA₀

/-- **Robust local error of the matrix projector-splitting integrator** (Kieri–Lubich–Walach
2016, Theorem 2.1, local part, as quoted in Theorem 2 of Ceruti–Lubich, [CerutiLubich2022];
explicit constants ours).  Let `F : ℝ → ℝ^{m×n} → ℝ^{m×n}` be `L`-Lipschitz (`L ≥ 0`) and
bounded by `B` in the Frobenius norm, and assume the factored normal-component bound
`‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for all `t`, all cores `S` and all `U`, `V` with
orthonormal columns.  Let `A' = F(t, A)`, `A(t₀) = U₀ S₀ V₀ᵀ`, and run one step of the KSL
integrator (`IsStep`) on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`.  Then

    ‖U₁ L(t₁)ᵀ - A(t₁)‖ ≤ h (11 L B h + ε),

independently of the singular values of the approximations.  The normal-component assumption is
global, unlike the paper's (which is restricted to a neighbourhood of `A(t)`, see the module
docstring); `IsStep.local_error_of_pointwise` assumes it only at `U₁ Ŝ₁ V₀ᵀ`. -/
theorem local_error (hs : IsStep F t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * (Lf t₁)ᵀ - A t₁‖ ≤ h * (11 * L * B * h + ε) :=
  (hs.isKSLStep_of_factored hε).local_error hF hL hB ht₁ hh hA hA₀

end IsStep

/-- **Robust global error bound, pointwise normal-component bounds**: the conclusion of
`global_error` when the normal component of `F` is only assumed `ε`-small at the K-step result
`U₁ k · Ŝ k · (V k)ᵀ` of step `k`, for `t` in that step. -/
theorem global_error_of_pointwise [DecidableEq m] [DecidableEq n]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {U U₁ : ℕ → Matrix m r ℝ}
    {V : ℕ → Matrix n r ℝ} {S Ŝ : ℕ → Matrix r r ℝ} {K : ℕ → ℝ → Matrix m r ℝ}
    {Sf : ℕ → ℝ → Matrix r r ℝ} {Lf : ℕ → ℝ → Matrix n r ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (U₁ k) (Ŝ k)
      (K k) (Sf k) (Lf k))
    (hε : ∀ k < N, ∀ t ∈ Icc (t₀ + k * h) (t₀ + (k + 1) * h),
      ‖(1 - U₁ k * (U₁ k)ᵀ) * F t (U₁ k * Ŝ k * (V k)ᵀ) * (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hU : ∀ k < N, U (k + 1) = U₁ k)
    (hLQR : ∀ k < N, Lf k (t₀ + (k + 1) * h) = V (k + 1) * (S (k + 1))ᵀ)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T →
      ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * ε + 11 * L * B * T * Real.exp (L * T) * h :=
  ksl_global_error_le (Y := fun k => U k * S k * (V k)ᵀ) (P := fun k => leftProj (U₁ k))
    (Q := fun k => rightProj (V k)) (YK := fun k t => K k t * (V k)ᵀ)
    (YS := fun k t => U₁ k * Sf k t * (V k)ᵀ) (YL := fun k t => U₁ k * (Lf k t)ᵀ)
    hF hL hB hε0 hh hA (fun k hk => (hstep k hk).isKSLStep (hε k hk))
    (fun k hk => by rw [hU k hk, IsStep.eq_factored (hLQR k hk)])
    hΦ hΦ₀ hδ

/-- **Robust global error bound of the matrix projector-splitting integrator**
(Kieri–Lubich–Walach 2016, Theorem 2.1, as quoted in Theorem 2 of Ceruti–Lubich, [CerutiLubich2022];
explicit constants ours). Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B` in the Frobenius
norm, satisfy the (global) factored normal-component assumption with `ε ≥ 0`, and let `A' = F(t, A)`
on `[t₀, t₀ + N h]`, `h ≥ 0`. For `k < N` let step `k` of the KSL integrator go from
`Yₖ = Uₖ Sₖ Vₖᵀ` at `tₖ = t₀ + k h` to `tₖ₊₁` (`IsStep`, new basis `U₁ k`, K/S/L factor trajectories
`K k`, `Sf k`, `Lf k`), and let the next factors be `Uₖ₊₁ = U₁ k` and the QR factorization
`Lf k (tₖ₊₁) = Vₖ₊₁ Sₖ₊₁ᵀ` of the L-step result. If `Φ k` are the exact flows from `(tₖ, Yₖ)` and
`‖Y₀ - A(t₀)‖ ≤ δ`, then for `k ≤ N` with `k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ e^{L T} δ + T e^{L T} ε + 11 L B T e^{L T} h.

The constants depend only on `L`, `B` and `T`, not on singular values.  The normal-component
assumption is global, unlike the paper's neighbourhood version (see the module docstring);
`global_error_of_pointwise` assumes it only at the K-step results. -/
theorem global_error [DecidableEq m] [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε0 : 0 ≤ ε)
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {U U₁ : ℕ → Matrix m r ℝ} {V : ℕ → Matrix n r ℝ}
    {S Ŝ : ℕ → Matrix r r ℝ} {K : ℕ → ℝ → Matrix m r ℝ} {Sf : ℕ → ℝ → Matrix r r ℝ}
    {Lf : ℕ → ℝ → Matrix n r ℝ} {Φ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsStep F (t₀ + k * h) (t₀ + (k + 1) * h) (U k) (S k) (V k) (U₁ k) (Ŝ k)
      (K k) (Sf k) (Lf k))
    (hU : ∀ k < N, U (k + 1) = U₁ k)
    (hLQR : ∀ k < N, Lf k (t₀ + (k + 1) * h) = V (k + 1) * (S (k + 1))ᵀ)
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + (k + 1) * h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T →
      ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * ε + 11 * L * B * T * Real.exp (L * T) * h :=
  global_error_of_pointwise hF hL hB hε0 hh hA hstep
    (fun k hk _ _ => hε _ (U₁ k) (Ŝ k) (V k) (hstep k hk).orthU₁ (hstep k hk).orthV₀) hU hLQR
    hΦ hΦ₀ hδ

/-- **The QR step exists** ([LubichOseledets2014, §3.2], step 1, "using QR or SVD"): for `r ≤ m`,
every `K₁ ∈ ℝ^{m×r}` factors as `K₁ = U₁ Ŝ₁` with `U₁ᵀ U₁ = I` (also when `K₁` is
rank-deficient). -/
theorem exists_qr {m : Type*} [Fintype m] {r : ℕ} (K₁ : Matrix m (Fin r) ℝ)
    (hr : r ≤ Fintype.card m) :
    ∃ (U₁ : Matrix m (Fin r) ℝ) (Ŝ₁ : Matrix (Fin r) (Fin r) ℝ), U₁ᵀ * U₁ = 1 ∧ K₁ = U₁ * Ŝ₁ := by
  obtain ⟨U, hU, hcap⟩ := exists_orthonormal_capture_of_le_card K₁ hr
  exact ⟨U, Uᵀ * K₁, hU, by rw [← Matrix.mul_assoc, hcap]⟩

end Step

/-! ### Satisfiability examples -/

section Examples

/-- The basis vector `e₁ = (1, 0)ᵀ` of the examples (orthonormal, rank `1`). -/
private noncomputable def exE : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The constant right-hand side `F ≡ C` of the examples; its normal component at
`e₁ S e₁ᵀ`, `(I - e₁e₁ᵀ) C (I - e₁e₁ᵀ) = e₂ e₂ᵀ`, is nonzero. -/
private noncomputable def exC : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

private lemma exE_orth : exEᵀ * exE = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [exE, Matrix.mul_apply]

/-- The coefficient `Ŝ₁ = 2` of the QR factorization in the example. -/
private noncomputable def exŜ : Matrix (Fin 1) (Fin 1) ℝ := !![2]

/-- The backward S-step result `S(1) = Ŝ₁ - e₁ᵀ C e₁` of the example. -/
private noncomputable def exS₁ : Matrix (Fin 1) (Fin 1) ℝ :=
  exŜ + ((1 : ℝ) - 0) • -(exEᵀ * exC * exE)

private lemma exK_qr : exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 : ℝ) - 0) • (exC * exE) =
    exE * exŜ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exE, exC, exŜ, Matrix.mul_apply, Fin.sum_univ_two]

/-- One explicit KSL step for `F ≡ C`, `Y₀ = e₁ e₁ᵀ`, `t₀ = 0`, `t₁ = 1`: all substeps are
affine, `K(t) = e₁ + t C e₁`, `K(1) = e₁ · 2` (so `U₁ = e₁`, `Ŝ₁ = 2`),
`S(t) = 2 - t e₁ᵀ C e₁`, `L(t) = e₁ S(1)ᵀ + t Cᵀ e₁`. -/
private lemma exStep :
    IsStep (fun _ _ => exC) 0 1 exE 1 exE exE exŜ
      (fun t => exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - 0) • (exC * exE))
      (fun t => exŜ + (t - 0) • -(exEᵀ * exC * exE))
      (fun t => exE * exS₁ᵀ + (t - 0) • (exCᵀ * exE)) where
  orthV₀ := exE_orth
  kSol := odeSolution_affine (exE * (1 : Matrix (Fin 1) (Fin 1) ℝ)) (exC * exE) 0 1
  kStart := by simp
  orthU₁ := exE_orth
  kQR := exK_qr
  sSol := odeSolution_affine exŜ (-(exEᵀ * exC * exE)) 0 1
  sStart := by simp
  lSol := odeSolution_affine (exE * exS₁ᵀ) (exCᵀ * exE) 0 1
  lStart := by simp [exS₁]

/-- **The hypotheses of `IsStep.local_error` are jointly satisfiable**: for the constant field
`F ≡ C` (`L = 0`, `B = ε = ‖C‖`) on `2 × 2` matrices, with `Y₀ = e₁ e₁ᵀ` of rank `1`, one KSL
step with `h = 1` exists (`exStep`) and the theorem applies to it.  The normal component of `C`
at `Y₀` is nonzero, so the approximation error is not trivially zero.  Since `L = 0` the
Lipschitz term `11 L B h²` is not exercised, and since the factored assumption is global it
forces `ε ≥ σ₁(C)` here (take `S = 0`), so `ε` does not measure the normal component at `Y₀`;
the bound `h ‖C‖` is crude.  `radial_normal_eq_zero` shows that the field hypotheses also hold
with `L, B > 0` and `ε = 0`. -/
example :
    ‖exE * (exE * exS₁ᵀ + ((1 : ℝ) - 0) • (exCᵀ * exE))ᵀ
      - (exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exEᵀ + ((1 : ℝ) - 0) • exC)‖ ≤
      1 * (11 * 0 * ‖exC‖ * 1 + ‖exC‖) :=
  exStep.local_error (A := fun t => exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exEᵀ + (t - 0) • exC)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (normal_const_le exC) (by norm_num)
    zero_le_one (odeSolution_affine _ exC 0 1) (by simp)

/-- The L-step result `L(1)` of the example; the QR factorization `L(1) = V₁ S₁ᵀ` is taken
with `V₁ = L(1)`, `S₁ = 1` (orthonormality of `V₁` is only needed for a following step). -/
private noncomputable def exL₁ : Matrix (Fin 2) (Fin 1) ℝ :=
  exE * exS₁ᵀ + ((1 : ℝ) - 0) • (exCᵀ * exE)

/-- **The hypotheses of `global_error` are jointly satisfiable**: one step (`N = 1`, `h = 1`) of
the example `exStep`, with `U₁ = e₁`, `V₁ = L(1)`, `S₁ = 1`, and the exact solution
`A(t) = e₁ e₁ᵀ + t C` as exact flow.  As in the previous example `L = 0` and `ε = B = ‖C‖`, so
the Lipschitz term of the bound is not exercised. -/
example : ‖exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exL₁ᵀ
      - (exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exEᵀ + ((0 : ℝ) + ((1 : ℕ) : ℝ) * 1 - 0) • exC)‖ ≤
    Real.exp (0 * 1) * 0 + 1 * Real.exp (0 * 1) * ‖exC‖
      + 11 * 0 * ‖exC‖ * 1 * Real.exp (0 * 1) * 1 := by
  have key := global_error (F := fun _ _ => exC) (L := 0) (B := ‖exC‖) (ε := ‖exC‖)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) (norm_nonneg _) (normal_const_le exC)
    (t₀ := 0) (h := 1) zero_le_one (N := 1)
    (A := fun t => exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exEᵀ + (t - 0) • exC)
    (odeSolution_affine _ exC 0 _) (U := fun _ => exE) (U₁ := fun _ => exE)
    (V := fun k => if k = 0 then exE else exL₁) (S := fun _ => 1) (Ŝ := fun _ => exŜ)
    (K := fun _ t => exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) + (t - 0) • (exC * exE))
    (Sf := fun _ t => exŜ + (t - 0) • -(exEᵀ * exC * exE))
    (Lf := fun _ t => exE * exS₁ᵀ + (t - 0) • (exCᵀ * exE))
    (Φ := fun _ t => exE * (1 : Matrix (Fin 1) (Fin 1) ℝ) * exEᵀ + (t - 0) • exC)
    (fun k hk => by
      obtain rfl : k = 0 := by omega
      simpa using exStep)
    (fun _ _ => rfl)
    (fun k hk => by
      obtain rfl : k = 0 := by omega
      simp [exL₁])
    (fun k _ => (odeSolution_affine _ exC 0 _).mono (by positivity) le_rfl)
    (fun k hk => by
      obtain rfl : k = 0 := by omega
      simp)
    (δ := 0) (T := 1) (by simp) 1 le_rfl (by norm_num)
  simpa using key

end Examples

end MatrixKSL

end LeanDLRA
