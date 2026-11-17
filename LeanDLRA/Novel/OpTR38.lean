import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.GaugeODE

/-!
# Escape of spurious critical points by the Riemannian gradient flow on rank-`r` PSD matrices

Open problem OP-TR-38 of `docs/catalogue/survey/open-problems.json` (arXiv 2107.09207, Sec. 1, 6):
for `f(Z) = ½‖Z − X‖²` on the manifold of rank-`r` symmetric positive semidefinite matrices, the set
of initial values from which the Riemannian gradient flow converges to a spurious (rank-deficient)
critical point `Z# = ∑_{i∈J} dᵢ eᵢeᵢᵀ`, `|J| = s < r`, should have measure zero.  The paper proves
it for `s = r − 1` and distinct eigenvalues, by a rescaling and a stable-manifold argument that
breaks down for `s ≤ r − 2`.

This module proves three exact, unconditional mechanisms for the flow in factor form
(`IsSymGradFlow`: `U̇ = (1 − U Uᵀ) X U S⁻¹`, `Ṡ = −S + Uᵀ X U`, `Z = U S Uᵀ`, `t ≥ 0`; positive
definiteness of `S(t)` is derived from `S(0)` in `posDef_of_posDef_zero`).

* **Top-eigenvector barrier** (`IsSymGradFlow.quadForm_limit_pos`,
  `not_tendsto_partial_diagonal`, `example_1_1_escape`).  If `X e = d e` with `X ⪯ d`, `d > 0`,
  then `d/dt (eᵀ Z e) ≥ d ‖P e‖² − eᵀ Z e`; so from `eᵀ Z(0) e > 0` the flow cannot converge to
  any `Zlim ⪯ c < d` with `eᵀ Zlim e = 0`.  Every spurious point not containing the dominant
  eigenvector — `2^{r−1}` of the `2^r − 1`, of every rank `s`, including the ranks `s ≤ r − 2`
  left open in the paper — has its basin inside the hypersurface `{Z : eᵀ Z e = 0}`.  Repeated
  eigenvalues below the top one and `rank X > r` are allowed.
* **Monotone captured energy and trace barrier** (`IsSymGradFlow.monotoneOn_capture`,
  `IsSymGradFlow.capture_le_trace_limit`, `IsSymGradFlow.mul_eq_zero_of_tendsto_zero`).
  `tr(P X)` is nondecreasing along the flow (`Ṗ = (1 − P) X Z⁺ + Z⁺ X (1 − P)`, a
  `Z⁺`-preconditioned Oja flow), hence `tr Z(t) ≥ tr(P(0) X) + e^{−t}(tr Z(0) − tr(P(0) X))` and
  every limit `Zlim` has `tr Zlim ≥ tr(P(0) X)`: the open set `{Z₀ : tr(P(Z₀) X) > ∑_{i∈J} dᵢ}`
  escapes `Z#`, and `Z# = 0` (rank `0 ≤ r − 2`) is reached only from `range Z₀ ⊆ ker X`.
* **Kernel decay** (`IsSymGradFlow.quadForm_ker_le`): for `w ∈ ker X`,
  `wᵀ Z(t) w ≤ e^{−t} wᵀ Z(0) w`, the mechanism of the paper's Example 1.1.

Not proved: the barrier for spurious points that *contain* the dominant eigenvector (e.g.
`diag(2, 0, 0)` in Example 1.1).  Numerically (scratch script) the basin of `diag(2, 0, 0)` for
`X = diag(2, 1, 0)`, `r = 2`, is `{Z₀ : Z₀ e₃ ∥ e₃}` (codimension `2`), and
`log det(Π_Tᵀ Z Π_T)` (`Π_T` the top-`r` eigenvectors) is nondecreasing near every spurious
point; a proof of this local statement plus analyticity of the flow would give the full
conjecture for the gradient flow.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Novel.OpTR38

variable {n r : Type*} [Fintype n] [Fintype r]

section QuadForm

variable {X : Matrix n n ℝ}

/-- The quadratic form `M ↦ vᵀ M v` as a continuous linear functional. -/
noncomputable def quadForm (v : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => v ⬝ᵥ (M *ᵥ v)
      map_add' := fun M N => by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun a M => by simp [Matrix.smul_mulVec, dotProduct_smul] }

theorem quadForm_apply (v : n → ℝ) (M : Matrix n n ℝ) : quadForm v M = v ⬝ᵥ (M *ᵥ v) := rfl

/-- The quadratic form of the right-hand side `P X + X P − P X P − Z` at a vector `v`, in terms of
`p = P v`: `vᵀ Ż v = 2 pᵀ X v − pᵀ X p − vᵀ Z v` (for symmetric `P`, `X`). -/
theorem quadForm_rhs {P Z : Matrix n n ℝ} (hP : Pᵀ = P) (hX : Xᵀ = X) (v : n → ℝ) :
    quadForm v (P * X + X * P - P * X * P - Z) =
      2 * ((P *ᵥ v) ⬝ᵥ (X *ᵥ v)) - (P *ᵥ v) ⬝ᵥ (X *ᵥ (P *ᵥ v)) - quadForm v Z := by
  simp only [quadForm_apply, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add,
    dotProduct_sub, ← Matrix.mulVec_mulVec]
  have e1 : v ⬝ᵥ (P *ᵥ (X *ᵥ v)) = (P *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP]
  have e2 : v ⬝ᵥ (X *ᵥ (P *ᵥ v)) = (P *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hX, dotProduct_comm]
  have e3 : v ⬝ᵥ (P *ᵥ (X *ᵥ (P *ᵥ v))) = (P *ᵥ v) ⬝ᵥ (X *ᵥ (P *ᵥ v)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP]
  rw [e1, e2, e3]
  ring

end QuadForm


section ODE

/-- A real function with nonnegative derivative on `[a, ∞)` is monotone there. -/
private theorem monotoneOn_Ici_of_deriv_nonneg {f f' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, a ≤ t → HasDerivAt f (f' t) t) (hf' : ∀ t, a ≤ t → 0 ≤ f' t) :
    MonotoneOn f (Ici a) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici a)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Ici] at ht
    exact (hf t (le_of_lt ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at ht
    rw [(hf t (le_of_lt ht)).deriv]
    exact hf' t (le_of_lt ht)

/-- Grönwall lower bound: `q' ≥ −q` on `[0, ∞)` gives `q t ≥ e^{−t} q 0`. -/
private theorem exp_neg_mul_le_of_deriv_ge {q q' : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ t → HasDerivAt q (q' t) t) (hq' : ∀ t, 0 ≤ t → -q t ≤ q' t) {t : ℝ}
    (ht : 0 ≤ t) : Real.exp (-t) * q 0 ≤ q t := by
  have hg : ∀ s, 0 ≤ s → HasDerivAt (fun s => Real.exp s * q s)
      (Real.exp s * q s + Real.exp s * q' s) s := fun s hs =>
    (Real.hasDerivAt_exp s).mul (hq s hs)
  have hmono := monotoneOn_Ici_of_deriv_nonneg hg (fun s hs => by
    have := hq' s hs
    have := Real.exp_pos s
    nlinarith)
  have h := hmono Set.self_mem_Ici ht ht
  simp only [Real.exp_zero, one_mul] at h
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-t) * q 0 ≤ Real.exp (-t) * (Real.exp t * q t) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = q t := by rw [← mul_assoc, he, one_mul]

/-- Grönwall upper bound: `q' ≤ −q` on `[0, ∞)` gives `q t ≤ e^{−t} q 0`. -/
private theorem le_exp_neg_mul_of_deriv_le {q q' : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ t → HasDerivAt q (q' t) t) (hq' : ∀ t, 0 ≤ t → q' t ≤ -q t) {t : ℝ}
    (ht : 0 ≤ t) : q t ≤ Real.exp (-t) * q 0 := by
  have h := exp_neg_mul_le_of_deriv_ge (q := fun s => -q s) (q' := fun s => -q' s)
    (fun s hs => (hq s hs).neg) (fun s hs => by have := hq' s hs; simp only [neg_neg]; linarith) ht
  simp only [mul_neg] at h
  linarith

end ODE

section Frobenius

/-- `|vᵀ A v| ≤ ‖A‖ ‖v‖²` for the Frobenius norm (Cauchy–Schwarz twice). -/
private theorem abs_quadForm_le_norm_mul (A : Matrix n n ℝ) (v : n → ℝ) :
    |v ⬝ᵥ (A *ᵥ v)| ≤ ‖A‖ * (v ⬝ᵥ v) := by
  have hv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hAv : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ ‖A‖ ^ 2 * (v ⬝ᵥ v) := by
    rw [LeanDLRA.Frobenius.norm_sq_eq_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) (fun j => A i j) v
    simp only [dotProduct, Matrix.mulVec, ← sq] at this ⊢
    simpa [dotProduct] using this
  have hcs : (v ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (v ⬝ᵥ v) * ((A *ᵥ v) ⬝ᵥ (A *ᵥ v)) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) v (A *ᵥ v)
    simpa [dotProduct, sq] using this
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (norm_nonneg _) hv)
  calc (v ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (v ⬝ᵥ v) * ((A *ᵥ v) ⬝ᵥ (A *ᵥ v)) := hcs
    _ ≤ (v ⬝ᵥ v) * (‖A‖ ^ 2 * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left hAv hv
    _ = (‖A‖ * (v ⬝ᵥ v)) ^ 2 := by ring

end Frobenius

variable [DecidableEq n] [DecidableEq r]

/-- A factor path `t ↦ (U t, S t)` of the Riemannian gradient flow `Ż = −P(Z)(Z − X)` of
`f(Z) = ½‖Z − X‖²` on the manifold of rank-`r` symmetric positive definite-core matrices
`Z = U S Uᵀ` (`Uᵀ U = 1`, `S` symmetric positive definite), for `t ≥ 0`, in the gauge
`Uᵀ U̇ = 0` (arXiv 2107.09207, Lemma 2.6; Koch–Lubich, Prop. 2.1):
`U̇ = (1 − U Uᵀ) X U S⁻¹`, `Ṡ = −S + Uᵀ X U`.  The derivatives are two-sided derivatives of
functions defined on `ℝ`, required only at times `t ≥ 0`. -/
structure IsSymGradFlow (X : Matrix n n ℝ) (U : ℝ → Matrix n r ℝ) (S : ℝ → Matrix r r ℝ) :
    Prop where
  orth : ∀ t, 0 ≤ t → (U t)ᵀ * U t = 1
  posDef : ∀ t, 0 ≤ t → (S t).PosDef
  hU : ∀ t, 0 ≤ t → HasDerivAt U ((1 - U t * (U t)ᵀ) * X * U t * (S t)⁻¹) t
  hS : ∀ t, 0 ≤ t → HasDerivAt S (-S t + (U t)ᵀ * X * U t) t

omit [DecidableEq n] [DecidableEq r] in
/-- **Positive definiteness of the core is preserved** (a priori half of arXiv 2107.09207,
Lemma 2.7, by Grönwall: `d/dt vᵀ S v = −vᵀ S v + (U v)ᵀ X (U v) ≥ −vᵀ S v`, so
`vᵀ S(t) v ≥ e^{−t} vᵀ S(0) v`).  Given a symmetric solution of the core equation
`Ṡ = −S + Uᵀ X U` for `t ≥ 0` with `X` positive semidefinite and `S(0)` positive definite,
`S(t)` is positive definite for all `t ≥ 0`; no property of the path `U` is used. -/
theorem posDef_of_posDef_zero {X : Matrix n n ℝ} {U : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ}
    (hX : X.PosSemidef) (hsymm : ∀ t, 0 ≤ t → (S t)ᵀ = S t)
    (hS : ∀ t, 0 ≤ t → HasDerivAt S (-S t + (U t)ᵀ * X * U t) t) (h0 : (S 0).PosDef) {t : ℝ}
    (ht : 0 ≤ t) : (S t).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm t ht
  rw [star_trivial]
  have hq : ∀ s, 0 ≤ s → HasDerivAt (fun s => quadForm v (S s))
      (quadForm v (-S s + (U s)ᵀ * X * U s)) s := fun s hs =>
    (quadForm v).hasFDerivAt.comp_hasDerivAt s (hS s hs)
  have hge : ∀ s, 0 ≤ s → -quadForm v (S s) ≤ quadForm v (-S s + (U s)ᵀ * X * U s) := by
    intro s hs
    have key : v ⬝ᵥ (((U s)ᵀ * X * U s) *ᵥ v) = (U s *ᵥ v) ⬝ᵥ (X *ᵥ (U s *ᵥ v)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    simp only [map_add, map_neg, quadForm_apply]
    rw [key]
    have := hX.dotProduct_mulVec_nonneg (U s *ᵥ v)
    rw [star_trivial] at this
    linarith
  have h1 := exp_neg_mul_le_of_deriv_ge hq hge ht
  have h2 : 0 < quadForm v (S 0) := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 h0).2 hv
    rwa [star_trivial] at this
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) h2) h1

/-- A factor path with orthonormal `U`, symmetric `S`, the factor equations for `t ≥ 0`, and a
positive definite core at `t = 0` only, is a flow in the sense of `IsSymGradFlow`
(positive definiteness is derived, `posDef_of_posDef_zero`). -/
theorem IsSymGradFlow.of_posDef_zero {X : Matrix n n ℝ} {U : ℝ → Matrix n r ℝ}
    {S : ℝ → Matrix r r ℝ} (hX : X.PosSemidef) (orth : ∀ t, 0 ≤ t → (U t)ᵀ * U t = 1)
    (hsymm : ∀ t, 0 ≤ t → (S t)ᵀ = S t)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U ((1 - U t * (U t)ᵀ) * X * U t * (S t)⁻¹) t)
    (hS : ∀ t, 0 ≤ t → HasDerivAt S (-S t + (U t)ᵀ * X * U t) t) (h0 : (S 0).PosDef) :
    IsSymGradFlow X U S :=
  ⟨orth, fun _ ht => posDef_of_posDef_zero hX hsymm hS h0 ht, hU, hS⟩

namespace IsSymGradFlow

variable {X : Matrix n n ℝ} {U : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ}

theorem symm (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) : (S t)ᵀ = S t :=
  (Matrix.isHermitian_iff_isSymm.1 (h.posDef t ht).isHermitian).eq

theorem isUnit_det (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) : IsUnit (S t).det :=
  isUnit_iff_ne_zero.2 (h.posDef t ht).det_pos.ne'

/-- The projector `P = U Uᵀ` fixes `Z = U S Uᵀ` from the left and from the right. -/
private theorem proj_mul_Z (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) :
    U t * (U t)ᵀ * (U t * S t * (U t)ᵀ) = U t * S t * (U t)ᵀ := by
  calc U t * (U t)ᵀ * (U t * S t * (U t)ᵀ) = U t * ((U t)ᵀ * U t) * S t * (U t)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.orth t ht, Matrix.mul_one]

private theorem Z_mul_proj (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) :
    U t * S t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * S t * (U t)ᵀ := by
  calc U t * S t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * S t * ((U t)ᵀ * U t) * (U t)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.orth t ht, Matrix.mul_one]

/-- **The flow of `Z = U S Uᵀ`**: `Ż = P X + X P − P X P − Z` with `P = U Uᵀ`, which is
`−P(Z)(Z − X)` for the tangent projector `P(Z)`. -/
theorem hasDerivAt_Z (h : IsSymGradFlow X U S) (hX : Xᵀ = X) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => U t * S t * (U t)ᵀ)
      (U t * (U t)ᵀ * X + X * (U t * (U t)ᵀ) - U t * (U t)ᵀ * X * (U t * (U t)ᵀ) -
        U t * S t * (U t)ᵀ) t := by
  set Z := U t * S t * (U t)ᵀ with hZ
  set P := U t * (U t)ᵀ with hP
  have hPZ : P * Z = Z := h.proj_mul_Z ht
  have hZP : Z * P = Z := h.Z_mul_proj ht
  have hZt : Zᵀ = Z := by
    rw [hZ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h.symm ht,
      Matrix.mul_assoc]
  have h1P : (1 - P) * Z = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPZ, sub_self]
  have hU' : HasDerivAt U ((1 - U t * (U t)ᵀ) * (X - Z) * U t * (S t)⁻¹) t := by
    refine (h.hU t ht).congr_deriv ?_
    rw [Matrix.mul_sub, ← hP, h1P, sub_zero]
  have hS' : HasDerivAt S ((U t)ᵀ * (X - Z) * U t) t := by
    refine (h.hS t ht).congr_deriv ?_
    rw [Matrix.mul_sub, Matrix.sub_mul, hZ]
    have : (U t)ᵀ * (U t * S t * (U t)ᵀ) * U t = S t := by
      calc (U t)ᵀ * (U t * S t * (U t)ᵀ) * U t = ((U t)ᵀ * U t) * S t * ((U t)ᵀ * U t) := by
            simp only [Matrix.mul_assoc]
        _ = S t := by rw [h.orth t ht, Matrix.one_mul, Matrix.mul_one]
    rw [this]
    abel
  have hV' : HasDerivAt U ((1 - U t * (U t)ᵀ) * (X - Z)ᵀ * U t * ((S t)⁻¹)ᵀ) t := by
    refine (h.hU t ht).congr_deriv ?_
    rw [Matrix.transpose_sub, hX, hZt, Matrix.transpose_nonsing_inv, h.symm ht, Matrix.mul_sub,
      ← hP, h1P, sub_zero]
  have := hasDerivAt_factorProduct_of_factorODE (h.isUnit_det ht) hU' hS' hV'
  refine this.congr_deriv ?_
  rw [Matrix.mul_assoc (X - Z) (U t), Matrix.mul_assoc (P * (X - Z)) (U t), ← hP]
  simp only [Matrix.mul_sub, Matrix.sub_mul, hPZ, hZP]
  abel

/-- **Derivative of `vᵀ Z(t) v` along the flow**, with `p = U Uᵀ v = P v`:
`d/dt vᵀ Z v = 2 pᵀ X v − pᵀ X p − vᵀ Z v`. -/
theorem hasDerivAt_quadForm (h : IsSymGradFlow X U S) (hX : Xᵀ = X) (v : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivAt (fun t => quadForm v (U t * S t * (U t)ᵀ))
      (2 * (((U t * (U t)ᵀ) *ᵥ v) ⬝ᵥ (X *ᵥ v)) -
        ((U t * (U t)ᵀ) *ᵥ v) ⬝ᵥ (X *ᵥ ((U t * (U t)ᵀ) *ᵥ v)) -
        quadForm v (U t * S t * (U t)ᵀ)) t := by
  have hP : (U t * (U t)ᵀ)ᵀ = U t * (U t)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have := (quadForm v).hasFDerivAt.comp_hasDerivAt t (h.hasDerivAt_Z hX ht)
  refine this.congr_deriv ?_
  exact quadForm_rhs hP hX v

/-- `‖P v‖² = vᵀ P v` for the orthogonal projector `P = U Uᵀ`. -/
theorem proj_dotProduct_self (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) (v : n → ℝ) :
    ((U t * (U t)ᵀ) *ᵥ v) ⬝ᵥ ((U t * (U t)ᵀ) *ᵥ v) = v ⬝ᵥ ((U t * (U t)ᵀ) *ᵥ v) := by
  have hPP : U t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * (U t)ᵀ := by
    calc U t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * ((U t)ᵀ * U t) * (U t)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h.orth t ht, Matrix.mul_one]
  have hP : (U t * (U t)ᵀ)ᵀ = U t * (U t)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP, Matrix.mulVec_mulVec, hPP,
    dotProduct_comm]

/-- `vᵀ Z v = pᵀ Z p` with `p = P v`, since `Z = P Z P`. -/
theorem quadForm_eq_proj (h : IsSymGradFlow X U S) {t : ℝ} (ht : 0 ≤ t) (v : n → ℝ) :
    quadForm v (U t * S t * (U t)ᵀ) =
      ((U t * (U t)ᵀ) *ᵥ v) ⬝ᵥ ((U t * S t * (U t)ᵀ) *ᵥ ((U t * (U t)ᵀ) *ᵥ v)) := by
  have hP : (U t * (U t)ᵀ)ᵀ = U t * (U t)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [quadForm_apply, Matrix.mulVec_mulVec, h.Z_mul_proj ht]
  conv_rhs => rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, hP, Matrix.mulVec_mulVec,
    h.proj_mul_Z ht]

/-- **Top-eigenvector barrier.**  Let `X` be symmetric with `X e = d e` and `X ⪯ d` (so `d` is the
largest eigenvalue of `X`, `e` an eigenvector for it), `d > 0`.  Along the Riemannian gradient
flow `Z(t) = U(t) S(t) U(t)ᵀ` of `½‖Z − X‖²`, the energy `eᵀ Z(t) e` satisfies
`d/dt (eᵀ Z e) ≥ d ‖P e‖² − eᵀ Z e ≥ −eᵀ Z e`.  Hence if `eᵀ Z(0) e > 0` and `Z(t) → Zlim` with
`Zlim ⪯ c < d`, then `eᵀ Zlim e > 0`: the flow cannot converge to any matrix that is orthogonal
to the top eigenvector and has all eigenvalues below `d`.

Why it matters: every spurious critical point `Z# = ∑_{i∈J} dᵢ eᵢeᵢᵀ` with `1 ∉ J` (i.e. not
containing the dominant eigenvector; `2^{r−1}` of the `2^r − 1` spurious points of arXiv
2107.09207, Lemma 2.4, of every rank `s ≤ r − 1`, including the ranks `s ≤ r − 2` left open
there) satisfies `Z# e₁ = 0` and `Z# ⪯ d₂ < d₁`; so the set of initial values from which the flow
converges to such a point is contained in the proper algebraic subset `{Z : e₁ᵀ Z e₁ = 0}`
(`e₁ ⊥ range Z`) of the manifold.  No distinctness of the other eigenvalues of `X`, no rank
condition on `X`, no rescaling and no stable-manifold theorem is used. -/
theorem quadForm_limit_pos (h : IsSymGradFlow X U S) (hX : Xᵀ = X) {d : ℝ} {e : n → ℝ}
    (hd : 0 < d) (he : X *ᵥ e = d • e) (hXle : ∀ v, v ⬝ᵥ (X *ᵥ v) ≤ d * (v ⬝ᵥ v))
    (h0 : 0 < quadForm e (U 0 * S 0 * (U 0)ᵀ)) {Zlim : Matrix n n ℝ} {c : ℝ} (hc : c < d)
    (hZlim : ∀ v, v ⬝ᵥ (Zlim *ᵥ v) ≤ c * (v ⬝ᵥ v))
    (hlim : Tendsto (fun t => U t * S t * (U t)ᵀ) atTop (𝓝 Zlim)) :
    0 < quadForm e Zlim := by
  set Z : ℝ → Matrix n n ℝ := fun t => U t * S t * (U t)ᵀ with hZdef
  set q : ℝ → ℝ := fun t => quadForm e (Z t) with hqdef
  set p : ℝ → n → ℝ := fun t => (U t * (U t)ᵀ) *ᵥ e with hpdef
  set q' : ℝ → ℝ := fun t => 2 * (p t ⬝ᵥ (X *ᵥ e)) - p t ⬝ᵥ (X *ᵥ p t) - q t with hq'def
  have hq : ∀ t, 0 ≤ t → HasDerivAt q (q' t) t := fun t ht => h.hasDerivAt_quadForm hX e ht
  have hpp : ∀ t, 0 ≤ t → p t ⬝ᵥ p t = e ⬝ᵥ p t := fun t ht => h.proj_dotProduct_self ht e
  have hπ : ∀ t, 0 ≤ (p t ⬝ᵥ p t) := fun t => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  -- `d/dt q ≥ d ‖p‖² − q`
  have hlow : ∀ t, 0 ≤ t → d * (p t ⬝ᵥ p t) - q t ≤ q' t := by
    intro t ht
    have h1 : p t ⬝ᵥ (X *ᵥ e) = d * (p t ⬝ᵥ p t) := by
      rw [he, dotProduct_smul, smul_eq_mul, hpp t ht, dotProduct_comm]
    have h2 := hXle (p t)
    simp only [hq'def, h1]
    linarith
  have hge : ∀ t, 0 ≤ t → -q t ≤ q' t := fun t ht =>
    (by nlinarith [hlow t ht, hπ t, hd.le] : -q t ≤ q' t)
  -- `q(t) ≥ e^{-t} q(0) > 0`
  have hqpos : ∀ t, 0 ≤ t → 0 < q t := fun t ht =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) h0) (exp_neg_mul_le_of_deriv_ge hq hge ht)
  -- eventually `‖Z t − Zlim‖ ≤ (d − c)/2`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ((d - c) / 2) (by linarith)
  set T := max N 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hclose : ∀ t, T ≤ t → ‖Z t - Zlim‖ ≤ (d - c) / 2 := fun t ht => by
    have := hN t ((le_max_left _ _).trans ht)
    rw [dist_eq_norm] at this
    exact this.le
  -- on `[T, ∞)`, `q ≤ (c + (d − c)/2) ‖p‖²`, hence `q' ≥ 0`
  have hmono : MonotoneOn q (Ici T) := by
    refine monotoneOn_Ici_of_deriv_nonneg (fun t ht => hq t (hT0.trans ht)) fun t ht => ?_
    have ht0 : 0 ≤ t := hT0.trans ht
    have hqe : q t = p t ⬝ᵥ (Z t *ᵥ p t) := h.quadForm_eq_proj ht0 e
    have hsplit : p t ⬝ᵥ (Z t *ᵥ p t) =
        p t ⬝ᵥ (Zlim *ᵥ p t) + p t ⬝ᵥ ((Z t - Zlim) *ᵥ p t) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]; ring
    have hb1 := hZlim (p t)
    have hb2 := (le_abs_self _).trans (abs_quadForm_le_norm_mul (Z t - Zlim) (p t))
    have hb3 := mul_le_mul_of_nonneg_right (hclose t ht) (hπ t)
    have hqle : q t ≤ (c + (d - c) / 2) * (p t ⬝ᵥ p t) := by
      rw [hqe, hsplit]; nlinarith
    have := hlow t ht0
    nlinarith [hπ t]
  have hlimq : Tendsto q atTop (𝓝 (quadForm e Zlim)) :=
    ((quadForm e).continuous.tendsto Zlim).comp hlim
  have hTpos : 0 < q T := hqpos T hT0
  have hev : ∀ᶠ t in atTop, q T ≤ q t :=
    Filter.eventually_atTop.2 ⟨T, fun t ht => hmono Set.self_mem_Ici ht ht⟩
  exact lt_of_lt_of_le hTpos (le_of_tendsto_of_tendsto tendsto_const_nhds hlimq hev)

/-! ### The captured energy `tr(Uᵀ X U) = tr(P X)` is nondecreasing -/

/-- The trace as a continuous linear functional. -/
private noncomputable def traceCLM (k : Type*) [Fintype k] : Matrix k k ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap k ℝ ℝ)

private theorem traceCLM_apply {k : Type*} [Fintype k] (M : Matrix k k ℝ) :
    traceCLM k M = Matrix.trace M := rfl

/-- `tr(B S⁻¹ Bᵀ) ≥ 0` for positive definite `S`. -/
private theorem trace_mul_inv_mul_transpose_nonneg {k : Type*} [Fintype k] {S : Matrix r r ℝ}
    (hS : S.PosDef) (B : Matrix k r ℝ) : 0 ≤ Matrix.trace (B * S⁻¹ * Bᵀ) := by
  have hinv := hS.inv.posSemidef
  unfold Matrix.trace
  refine Finset.sum_nonneg fun i _ => ?_
  have : Matrix.diag (B * S⁻¹ * Bᵀ) i = B i ⬝ᵥ (S⁻¹ *ᵥ B i) := by
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  have := hinv.dotProduct_mulVec_nonneg (B i)
  rwa [star_trivial] at this

/-- **Derivative of the captured energy**: with `B = (1 − U Uᵀ) X U`,
`d/dt tr(Uᵀ X U) = 2 tr(B S⁻¹ Bᵀ)`. -/
theorem hasDerivAt_capture (h : IsSymGradFlow X U S) (hX : Xᵀ = X) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t => Matrix.trace ((U t)ᵀ * X * U t))
      (2 * Matrix.trace ((1 - U t * (U t)ᵀ) * X * U t * (S t)⁻¹ *
        ((1 - U t * (U t)ᵀ) * X * U t)ᵀ)) t := by
  have hd := LeanDLRA.Frobenius.hasDerivAt_mul_mul
    (LeanDLRA.Frobenius.hasDerivAt_transpose (h.hU t ht)) (hasDerivAt_const t X) (h.hU t ht)
  have := (traceCLM r).hasFDerivAt.comp_hasDerivAt t hd
  refine this.congr_deriv ?_
  simp only [traceCLM_apply, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.trace_add]
  set Q := 1 - U t * (U t)ᵀ with hQ
  have hQt : Qᵀ = Q := by
    rw [hQ, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hQQ : Q * Q = Q := by
    have hPP : U t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * (U t)ᵀ := by
      calc U t * (U t)ᵀ * (U t * (U t)ᵀ) = U t * ((U t)ᵀ * U t) * (U t)ᵀ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h.orth t ht, Matrix.mul_one]
    rw [hQ]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  set B := Q * X * U t with hB
  have hBt : Bᵀ = (U t)ᵀ * X * Q := by
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, hX, hQt, Matrix.mul_assoc]
  -- the first summand equals the second
  have h1 : Matrix.trace ((Q * X * U t * (S t)⁻¹)ᵀ * X * U t) =
      Matrix.trace ((U t)ᵀ * X * (Q * X * U t * (S t)⁻¹)) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hX]
    simp only [Matrix.mul_assoc]
  have h2 : (U t)ᵀ * X * (Q * X * U t * (S t)⁻¹) = Bᵀ * B * (S t)⁻¹ := by
    rw [hBt, hB]
    calc (U t)ᵀ * X * (Q * X * U t * (S t)⁻¹)
        = (U t)ᵀ * X * (Q * Q) * X * U t * (S t)⁻¹ := by rw [hQQ]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have h3 : Matrix.trace (Bᵀ * B * (S t)⁻¹) = Matrix.trace (B * (S t)⁻¹ * Bᵀ) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h1, h2, h3]
  ring

/-- **Monotone captured energy** (exact mechanism).  Along the Riemannian gradient
flow of `½‖Z − X‖²` on rank-`r` positive semidefinite matrices `Z = U S Uᵀ`, with `X` symmetric,
the energy of `X` captured by the range of `Z`,
`E(t) = tr(U(t)ᵀ X U(t)) = tr(P(t) X)` (`P = U Uᵀ` the orthogonal projector onto `range Z`),
is nondecreasing: `Ė = 2 tr(S⁻¹ Uᵀ X (1 − P) X U) ≥ 0`.  It is the preconditioned analogue
(`Z⁺` in place of `P` in the projector equation `Ṗ = (1 − P) X Z⁺ + Z⁺ X (1 − P)`) of the
monotonicity of `tr(P X)` for Oja's subspace flow.  `X` need not be positive semidefinite. -/
theorem monotoneOn_capture (h : IsSymGradFlow X U S) (hX : Xᵀ = X) :
    MonotoneOn (fun t => Matrix.trace ((U t)ᵀ * X * U t)) (Ici 0) :=
  monotoneOn_Ici_of_deriv_nonneg (fun _ ht => h.hasDerivAt_capture hX ht) fun t ht =>
    mul_nonneg zero_le_two (trace_mul_inv_mul_transpose_nonneg (h.posDef t ht) _)

/-! ### Trace barrier -/

/-- **Trace barrier**: `d/dt tr Z = tr(P X) − tr Z ≥ tr(P(0) X) − tr Z`, hence
`tr Z(t) ≥ E(0) + e^{−t} (tr Z(0) − E(0))` with `E(0) = tr(U(0)ᵀ X U(0))`. -/
theorem trace_ge (h : IsSymGradFlow X U S) (hX : Xᵀ = X) {t : ℝ} (ht : 0 ≤ t) :
    Matrix.trace ((U 0)ᵀ * X * U 0) +
      Real.exp (-t) * (Matrix.trace (S 0) - Matrix.trace ((U 0)ᵀ * X * U 0)) ≤
        Matrix.trace (S t) := by
  set E₀ := Matrix.trace ((U 0)ᵀ * X * U 0) with hE₀
  have hq : ∀ s, 0 ≤ s → HasDerivAt (fun s => Matrix.trace (S s) - E₀)
      (Matrix.trace (-S s + (U s)ᵀ * X * U s)) s := fun s hs => by
    have := ((traceCLM r).hasFDerivAt.comp_hasDerivAt s (h.hS s hs)).sub_const E₀
    exact this
  have hge : ∀ s, 0 ≤ s → -(Matrix.trace (S s) - E₀) ≤
      Matrix.trace (-S s + (U s)ᵀ * X * U s) := fun s hs => by
    rw [Matrix.trace_add, Matrix.trace_neg]
    have := h.monotoneOn_capture hX Set.self_mem_Ici hs hs
    simp only at this
    linarith
  have := exp_neg_mul_le_of_deriv_ge hq hge ht
  linarith

/-- **Trace barrier, limit form.**  If the flow converges, `Z(t) → Z∞`, then
`tr Z∞ ≥ tr(P(0) X) = tr(U(0)ᵀ X U(0))`.  In particular a spurious critical point
`Z# = ∑_{i∈J} dᵢ eᵢeᵢᵀ` (`tr Z# = ∑_{i∈J} dᵢ`) is not a limit of any trajectory whose initial
range captures more energy than `Z#` holds: `{Z₀ : tr(P(Z₀) X) > ∑_{i∈J} dᵢ}` is an explicit open
set of initial values that escape `Z#`. -/
theorem capture_le_trace_limit (h : IsSymGradFlow X U S) (hX : Xᵀ = X) {Zlim : Matrix n n ℝ}
    (hlim : Tendsto (fun t => U t * S t * (U t)ᵀ) atTop (𝓝 Zlim)) :
    Matrix.trace ((U 0)ᵀ * X * U 0) ≤ Matrix.trace Zlim := by
  set E₀ := Matrix.trace ((U 0)ᵀ * X * U 0) with hE₀
  have htr : ∀ t, 0 ≤ t → Matrix.trace (U t * S t * (U t)ᵀ) = Matrix.trace (S t) := fun t ht => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h.orth t ht, Matrix.one_mul]
  have hlimtr : Tendsto (fun t => Matrix.trace (U t * S t * (U t)ᵀ)) atTop
      (𝓝 (Matrix.trace Zlim)) :=
    ((traceCLM n).continuous.tendsto Zlim).comp hlim
  have hf : Tendsto (fun t : ℝ => E₀ + Real.exp (-t) * (Matrix.trace (S 0) - E₀)) atTop
      (𝓝 E₀) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const
      (Matrix.trace (S 0) - E₀)).const_add E₀
    simpa using this
  refine le_of_tendsto_of_tendsto hf hlimtr ?_
  refine Filter.eventually_atTop.2 ⟨0, fun t ht => ?_⟩
  change E₀ + Real.exp (-t) * (Matrix.trace (S 0) - E₀) ≤ Matrix.trace (U t * S t * (U t)ᵀ)
  rw [htr t ht]
  exact h.trace_ge hX ht

/-! ### The kernel block of `Z` decays -/

/-- **Kernel decay.**  For `X` positive semidefinite and `w ∈ ker X`,
`d/dt (wᵀ Z w) = −wᵀ P X P w − wᵀ Z w ≤ −wᵀ Z w`, so `wᵀ Z(t) w ≤ e^{−t} wᵀ Z(0) w`: the
component of the iterate in the kernel of `X` dies exponentially, whatever the limit.  (This is
the mechanism of Example 1.1 of arXiv 2107.09207, `Z_k = diag(2, 0, (1−α)^k)`.) -/
theorem quadForm_ker_le (h : IsSymGradFlow X U S) (hX : X.PosSemidef) {w : n → ℝ}
    (hw : X *ᵥ w = 0) {t : ℝ} (ht : 0 ≤ t) :
    quadForm w (U t * S t * (U t)ᵀ) ≤ Real.exp (-t) * quadForm w (U 0 * S 0 * (U 0)ᵀ) := by
  have hXt : Xᵀ = X := by
    have := hX.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine le_exp_neg_mul_of_deriv_le (fun s hs => h.hasDerivAt_quadForm hXt w hs) (fun s hs => ?_) ht
  have h1 := hX.dotProduct_mulVec_nonneg ((U s * (U s)ᵀ) *ᵥ w)
  rw [star_trivial] at h1
  rw [hw, dotProduct_zero, mul_zero, zero_sub]
  linarith

/-! ### Consequences for the spurious critical points -/

/-- **The rank-`0` spurious point attracts only ranges inside `ker X`.**  For `X` positive
semidefinite, if `Z(t) → 0` then `X U(0) = 0`, i.e. `range Z(0) ⊆ ker X`.  (`Z# = 0` is the
spurious point of rank `s = 0 ≤ r − 2` for every `r ≥ 2`, the case left open in arXiv 2107.09207;
`{Z : range Z ⊆ ker X}` is a proper algebraic subset of the manifold as soon as `X ≠ 0`.) -/
theorem mul_eq_zero_of_tendsto_zero (h : IsSymGradFlow X U S) (hX : X.PosSemidef)
    (hlim : Tendsto (fun t => U t * S t * (U t)ᵀ) atTop (𝓝 0)) : X * U 0 = 0 := by
  have hXt : Xᵀ = X := by
    have := hX.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hle := h.capture_le_trace_limit hXt hlim
  rw [Matrix.trace_zero] at hle
  have hdiag : ∀ j, Matrix.diag ((U 0)ᵀ * X * U 0) j = (U 0).col j ⬝ᵥ (X *ᵥ (U 0).col j) := by
    intro j
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      Matrix.mulVec, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hnn : ∀ j, 0 ≤ (U 0).col j ⬝ᵥ (X *ᵥ (U 0).col j) := fun j => by
    have := hX.dotProduct_mulVec_nonneg ((U 0).col j)
    rwa [star_trivial] at this
  have hsum : ∑ j, (U 0).col j ⬝ᵥ (X *ᵥ (U 0).col j) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hnn j)
    unfold Matrix.trace at hle
    simpa only [hdiag] using hle
  have hzero : ∀ j, X *ᵥ (U 0).col j = 0 := fun j => by
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 hsum j (Finset.mem_univ _)
    rw [← star_trivial ((U 0).col j)] at h0
    exact hX.dotProduct_mulVec_zero_iff.1 h0
  ext i j
  have := congrFun (hzero j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply] using this

end IsSymGradFlow

section Diagonal

variable {d : n → ℝ} {U : ℝ → Matrix n r ℝ} {S : ℝ → Matrix r r ℝ}

/-- **Spurious partial eigen-sums without a top eigenvector are not reached from
`(Z₀)_{i₀ i₀} > 0`.**  Let `X = diag(d)` with `d_{i₀} > 0` maximal.  For every index set `J` with
`d_i ≤ c < d_{i₀}` on `J` (so `i₀ ∉ J`, and `J` contains no index carrying the top eigenvalue),
the critical point `Z# = diag(1_J d) = ∑_{i∈J} dᵢ eᵢeᵢᵀ` of arXiv 2107.09207, Lemma 2.4 — of any
rank `|J| ≤ r − 1`, spurious or saddle — is not the limit of the Riemannian gradient flow from
any `Z₀ = U(0) S(0) U(0)ᵀ` with `(Z₀)_{i₀ i₀} > 0`.  Thus the basin of each such point lies in the
hypersurface `{Z : Z_{i₀ i₀} = 0}`; repeated eigenvalues of `X` are allowed.  Instance of
`IsSymGradFlow.quadForm_limit_pos`. -/
theorem not_tendsto_partial_diagonal (h : IsSymGradFlow (Matrix.diagonal d) U S) {i₀ : n}
    (hd0 : 0 < d i₀) (hmax : ∀ i, d i ≤ d i₀) (h0 : 0 < (U 0 * S 0 * (U 0)ᵀ) i₀ i₀)
    {J : Finset n} {c : ℝ} (hc0 : 0 ≤ c) (hJ : ∀ i ∈ J, d i ≤ c) (hc : c < d i₀) :
    ¬ Tendsto (fun t => U t * S t * (U t)ᵀ) atTop
      (𝓝 (Matrix.diagonal fun i => if i ∈ J then d i else 0)) := by
  intro hlim
  have hi₀ : i₀ ∉ J := fun hi => absurd (hJ i₀ hi) (not_le.2 hc)
  have hXt : (Matrix.diagonal d)ᵀ = Matrix.diagonal d := Matrix.diagonal_transpose d
  have he : Matrix.diagonal d *ᵥ Pi.single i₀ (1 : ℝ) = d i₀ • Pi.single i₀ 1 := by
    rw [Matrix.diagonal_mulVec_single, mul_one, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hXle : ∀ v : n → ℝ, v ⬝ᵥ (Matrix.diagonal d *ᵥ v) ≤ d i₀ * (v ⬝ᵥ v) := fun v => by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by nlinarith [hmax j, mul_self_nonneg (v j)]
  have hq0 : quadForm (Pi.single i₀ (1 : ℝ)) (U 0 * S 0 * (U 0)ᵀ) = (U 0 * S 0 * (U 0)ᵀ) i₀ i₀ := by
    rw [quadForm_apply, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
  have hZle : ∀ v : n → ℝ, v ⬝ᵥ ((Matrix.diagonal fun i => if i ∈ J then d i else 0) *ᵥ v) ≤
      c * (v ⬝ᵥ v) := fun v => by
    simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with hj
    · nlinarith [hJ j hj, mul_self_nonneg (v j)]
    · nlinarith [mul_self_nonneg (v j)]
  have := h.quadForm_limit_pos hXt hd0 he hXle (hq0 ▸ h0) hc hZle hlim
  rw [quadForm_apply, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
    Matrix.diagonal_apply_eq] at this
  simp only [hi₀, ite_false] at this
  exact lt_irrefl _ this

end Diagonal

section Example11

variable {U : ℝ → Matrix (Fin 3) (Fin 2) ℝ} {S : ℝ → Matrix (Fin 2) (Fin 2) ℝ}

/-- **Example 1.1 of arXiv 2107.09207, the two spurious points without `e₁`.**  For
`X = diag(2, 1, 0)` and `r = 2`, the Riemannian gradient flow from any `Z₀` with `(Z₀)₁₁ > 0`
converges neither to `diag(0, 1, 0)` nor to `0`.  (The third spurious point `diag(2, 0, 0)`, the
limit of the paper's example `Z₀ = diag(2, 0, 1)`, contains `e₁` and is not covered; see the
module docstring.) -/
theorem example_1_1_escape (h : IsSymGradFlow (Matrix.diagonal ![2, 1, 0]) U S)
    (h0 : 0 < (U 0 * S 0 * (U 0)ᵀ) 0 0) :
    ¬ Tendsto (fun t => U t * S t * (U t)ᵀ) atTop (𝓝 (Matrix.diagonal ![0, 1, 0])) ∧
      ¬ Tendsto (fun t => U t * S t * (U t)ᵀ) atTop (𝓝 0) := by
  have hmax : ∀ i, (![2, 1, 0] : Fin 3 → ℝ) i ≤ ![2, 1, 0] 0 := by
    intro i; fin_cases i <;> simp
  constructor
  · have := not_tendsto_partial_diagonal h (i₀ := 0) (by simp) hmax h0 (J := {1}) (c := 1)
      zero_le_one (by intro i hi; rw [Finset.mem_singleton] at hi; subst hi; simp) (by simp)
    convert this using 3
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have := not_tendsto_partial_diagonal h (i₀ := 0) (by simp) hmax h0 (J := ∅) (c := 0)
      le_rfl (by simp) (by simp)
    convert this using 3
    ext i j
    simp [Matrix.diagonal_apply]

end Example11

end LeanDLRA.Novel.OpTR38
