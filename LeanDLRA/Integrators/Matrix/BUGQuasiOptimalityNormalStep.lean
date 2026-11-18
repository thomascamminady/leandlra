import LeanDLRA.Integrators.Matrix.BUGQuasiOptimalityStep
import LeanDLRA.Classical.WeylSingular

/-!
# One BUG step for given data: the growth factor without the increment of the reference

`MatrixBUG.norm_projStep_sub_le_of_trace` bounds one step `Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` of the BUG
integrator of [CerutiLubich2022] against a reference `X₁` of the same rank with the factor
`1 + 23/10 η_X + 43/20 η_R` of the old error, where `η_X = g ‖X₁ - X₀‖₂` is the increment of the
reference (the whole velocity of the data) and `η_R = g ‖ΔR‖₂` the increment of the tail
`R = A - X` (for the truncated singular value decomposition: the velocity of the data normal to
the manifold of rank-`r` matrices, up to the tail). In this file the increment of the reference
enters the factor only multiplied by a small number: for `g ‖Y₀ - X₀‖ ≤ θ ≤ 1/16`,

  `‖Y₁ - X₁‖ ≤ (1 + 9/4 η_R + 5/2 η_X (θ + 2 η_F)) ‖Y₀ - X₀‖ + 9/4 η_F ‖A₁ - X₁‖₂
      + 4/3 η_F² ‖ΔR‖₂`,

the discrete form of the growth rate `ν/ρ + ν/(ρ - ε) + μ ε/ρ²` of
`LeanDLRA/DLRA/QuasiOptimalityNormalVelocity.lean`. All norms `‖·‖` are Frobenius norms and
`‖·‖₂` is the spectral norm.

## Main results

* `IsOrthProj.norm_sub_apply_add_sq`: `‖x - N x + b‖² = ‖x‖² - ‖N x‖² + ‖b‖²` for an orthogonal
  projector `N` and `N b = b`.
* `MatrixBUG.norm_sub_sub_one_sub_mul_sub_mul_one_sub_sq_le`: with `W = (1 - P₁) (X₁ - X₀)
  (1 - Q₀)`, `‖Y₀ - X₀ - W‖² ≤ ‖Y₀ - X₀‖² + 2 ‖(1 - P₁) X₁ (1 - Q₀)‖ ‖W‖`.
* `MatrixBUG.norm_one_sub_mul_mul_one_sub_le`: the component `(1 - P₁) X₁ (1 - Q₀)` is of second
  order, `≤ ‖(1 - P₁) X₁‖ g (‖X₁ - X₀‖₂ + ‖Y₀ - X₀‖)`.
* `MatrixBUG.norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le`: the one-step bound above.

## Implementation notes

In the identity of the step (`MatrixBUG.projStep_eq_add_sub`) the only term of first order in
the step that carries the increment of the reference is `W = (1 - P₁) (X₁ - X₀) (1 - Q₀)`. The map
`N : M ↦ (1 - P₁) M (1 - Q₀)` is an orthogonal projector of the Frobenius space with `N Y₀ = 0`,
so `W` meets the old error only in its component `N (Y₀ - X₀) = -N X₀`, and
`Y₀ - X₀ - W = (1 - N) (Y₀ - X₀) - N X₁`. By Pythagoras the norm changes by
`‖N X₁‖² - ‖N X₀‖² ≤ 2 ‖N X₁‖ ‖W‖`, and `N X₁` is of second order (the reference is captured by
`P₁` up to the error, and by `Q₀` up to the error and its increment). This is the mechanism of
`IsOrthProj.inner_sub_apply_sub_apply` for the step: the velocity is paired with components
normal to the mixed tangent space of the bases `P₁`, `Q₀` only. The terms with the tail increment
are those of `MatrixBUG.norm_projStep_sub_le_of_trace`.

## References

* [CerutiLubich2022]
-/

open Finset Matrix
open scoped LeanDLRA.Frobenius

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Exchange of a component in the range of an orthogonal projector.** For an orthogonal
projector `N` and `b` in its range, `‖x - N x + b‖² = ‖x‖² - ‖N x‖² + ‖b‖²`. -/
theorem IsOrthProj.norm_sub_apply_add_sq {N : E →L[ℝ] E} (hN : IsOrthProj N) (x : E) {b : E}
    (hb : N b = b) : ‖x - N x + b‖ ^ 2 = ‖x‖ ^ 2 - ‖N x‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 := hN.norm_sq_add (x - N x + b)
  have h2 := hN.norm_sq_add x
  have e1 : N (x - N x + b) = b := by rw [map_add, map_sub, hN.idem, sub_self, zero_add, hb]
  have e2 : x - N x + b - b = x - N x := by abel
  rw [e1, e2] at h1
  linarith

end Abstract

namespace MatrixBUG

open Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Normal

variable {P : Matrix m m ℝ} {Q₀ : Matrix n n ℝ} {Y₀ X₀ X₁ : Matrix m n ℝ} {G₁ : Matrix n m ℝ}
  {g : ℝ}

/-- **The increment of the reference between the new left and the old right basis meets the
error in normal components only.** For orthogonal projectors `P₁`, `Q₀` with `Y₀ Q₀ = Y₀` and
`W = (1 - P₁) (X₁ - X₀) (1 - Q₀)`,
`‖Y₀ - X₀ - W‖² ≤ ‖Y₀ - X₀‖² + 2 ‖(1 - P₁) X₁ (1 - Q₀)‖ ‖W‖`. -/
theorem norm_sub_sub_one_sub_mul_sub_mul_one_sub_sq_le (hP : IsOrthProjMat P)
    (hQ₀ : IsOrthProjMat Q₀) (hY₀Q : Y₀ * Q₀ = Y₀) :
    ‖Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀)‖ ^ 2 ≤
      ‖Y₀ - X₀‖ ^ 2 +
        2 * ‖(1 - P) * X₁ * (1 - Q₀)‖ * ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖ := by
  obtain ⟨N, hN, hNapp⟩ : ∃ N : Matrix m n ℝ →L[ℝ] Matrix m n ℝ, IsOrthProj N ∧
      ∀ M, N M = (1 - P) * (M * (1 - Q₀)) :=
    ⟨Frobenius.leftMulCLM (1 - P) * Frobenius.rightMulCLM (1 - Q₀),
      hP.compl.isOrthProj_leftMulCLM.mul hQ₀.compl.isOrthProj_rightMulCLM fun X => by
        simp only [Frobenius.leftMulCLM_apply, Frobenius.rightMulCLM_apply, Matrix.mul_assoc],
      fun _ => rfl⟩
  have hb : N (-((1 - P) * X₁ * (1 - Q₀))) = -((1 - P) * X₁ * (1 - Q₀)) := by
    rw [hNapp, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc ((1 - P) * X₁) (1 - Q₀) (1 - Q₀),
      hQ₀.compl.idem, Matrix.mul_assoc (1 - P) X₁ (1 - Q₀), ← Matrix.mul_assoc (1 - P) (1 - P),
      hP.compl.idem]
  have key := hN.norm_sub_apply_add_sq (Y₀ - X₀) hb
  have hy : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  have hNx : N (Y₀ - X₀) = -((1 - P) * X₀ * (1 - Q₀)) := by
    rw [hNapp, Matrix.sub_mul Y₀ X₀, hy, zero_sub, Matrix.mul_neg, Matrix.mul_assoc]
  have hz : Y₀ - X₀ - -((1 - P) * X₀ * (1 - Q₀)) + -((1 - P) * X₁ * (1 - Q₀)) =
      Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hNx, hz, norm_neg, norm_neg] at key
  have tri : ‖(1 - P) * X₁ * (1 - Q₀)‖ ≤
      ‖(1 - P) * X₀ * (1 - Q₀)‖ + ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖ := by
    have e : (1 - P) * X₁ * (1 - Q₀) =
        (1 - P) * X₀ * (1 - Q₀) + (1 - P) * (X₁ - X₀) * (1 - Q₀) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
      abel
    calc ‖(1 - P) * X₁ * (1 - Q₀)‖
        = ‖(1 - P) * X₀ * (1 - Q₀) + (1 - P) * (X₁ - X₀) * (1 - Q₀)‖ := congrArg (‖·‖) e
      _ ≤ _ := norm_add_le _ _
  have hp := norm_nonneg ((1 - P) * X₁ * (1 - Q₀))
  have hq := norm_nonneg ((1 - P) * X₀ * (1 - Q₀))
  have hw := norm_nonneg ((1 - P) * (X₁ - X₀) * (1 - Q₀))
  rw [key]
  by_cases hc : ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖ ≤ ‖(1 - P) * X₁ * (1 - Q₀)‖
  · nlinarith [mul_self_le_mul_self (sub_nonneg.mpr hc) (by linarith :
      ‖(1 - P) * X₁ * (1 - Q₀)‖ - ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖ ≤
        ‖(1 - P) * X₀ * (1 - Q₀)‖), sq_nonneg ‖(1 - P) * (X₁ - X₀) * (1 - Q₀)‖]
  · nlinarith [sq_nonneg ‖(1 - P) * X₀ * (1 - Q₀)‖,
      mul_nonneg hp (sub_nonneg.mpr (not_le.mp hc).le)]

/-- **The component of the reference normal to the new left and the old right basis is of second
order.** For `Y₀ Q₀ = Y₀` and a generalized inverse `G₁` of `X₁` with `‖G₁‖₂ ≤ g`,
`‖(1 - P₁) X₁ (1 - Q₀)‖ ≤ ‖(1 - P₁) X₁‖ g (‖X₁ - X₀‖₂ + ‖Y₀ - X₀‖)`. -/
theorem norm_one_sub_mul_mul_one_sub_le (hQ₀ : IsOrthProjMat Q₀) (hY₀Q : Y₀ * Q₀ = Y₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hG₁ : specNorm G₁ ≤ g) :
    ‖(1 - P) * X₁ * (1 - Q₀)‖ ≤
      ‖(1 - P) * X₁‖ * (g * (specNorm (X₁ - X₀) + ‖Y₀ - X₀‖)) := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₁
  have hy : Y₀ * (1 - Q₀) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hY₀Q, sub_self]
  have hx : X₁ * (1 - Q₀) = X₁ * (G₁ * ((X₁ - Y₀) * (1 - Q₀))) := by
    rw [Matrix.sub_mul X₁ Y₀, hy, sub_zero, ← Matrix.mul_assoc G₁, ← Matrix.mul_assoc X₁,
      ← Matrix.mul_assoc X₁ G₁, hX₁]
  have e : (1 - P) * X₁ * (1 - Q₀) = (1 - P) * X₁ * (G₁ * ((X₁ - Y₀) * (1 - Q₀))) := by
    rw [Matrix.mul_assoc (1 - P) X₁ (G₁ * ((X₁ - Y₀) * (1 - Q₀))), ← hx, Matrix.mul_assoc]
  have h1 : specNorm (X₁ - Y₀) ≤ specNorm (X₁ - X₀) + ‖Y₀ - X₀‖ := by
    have e1 : X₁ - Y₀ = X₁ - X₀ + (X₀ - Y₀) := by abel
    rw [e1]
    refine (WeylSingular.specNorm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [specNorm_sub_comm]
    exact specNorm_le_frob _
  have h2 : specNorm (G₁ * ((X₁ - Y₀) * (1 - Q₀))) ≤
      g * (specNorm (X₁ - X₀) + ‖Y₀ - X₀‖) :=
    calc specNorm (G₁ * ((X₁ - Y₀) * (1 - Q₀)))
        ≤ specNorm G₁ * specNorm ((X₁ - Y₀) * (1 - Q₀)) := specNorm_mul_le _ _
      _ ≤ g * (specNorm (X₁ - Y₀) * 1) :=
        mul_le_mul hG₁ ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          hQ₀.compl.specNorm_le_one (specNorm_nonneg _))) (specNorm_nonneg _) hg
      _ ≤ g * (specNorm (X₁ - X₀) + ‖Y₀ - X₀‖) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left h1 hg
  rw [e]
  exact (frob_mul_le' _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))

end Normal

/-! ### The one-step bound -/

section Main

/-- The error of the step: the old error with the increment of the reference between the new
left and the old right basis, the tail increment seen from the old bases and through the angles
between the old and the new bases, and the part of the increment of the reference that carries
the angle between the left bases. -/
private theorem err_split_normal (P P₀ : Matrix m m ℝ) (Q Q₀ : Matrix n n ℝ)
    (Y₀ X₀ Dx R : Matrix m n ℝ) :
    Y₀ + (Dx + R) - (1 - P) * (Dx + R) * (1 - Q₀) - P * ((1 - P₀) * (Dx + R) * (1 - Q)) -
        (X₀ + Dx) =
      Y₀ - X₀ - (1 - P) * Dx * (1 - Q₀) + ((1 - P) * (R * Q₀) + P * (P₀ * R) +
        P * (1 - P₀) * (R * Q₀) * Q + P * (1 - P₀) * R * ((1 - Q₀) * Q)) -
        P * ((1 - P₀) * Dx * (1 - Q)) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The old error with the exchanged normal component: from `M² ≤ e² + 2 c u (u + e)` with
`c ≤ 1/128` and `u ≤ 8/7 (e + α)`, `M ≤ e + 120/49 c e + α/7`. -/
private theorem norm_le_of_sq_le_normal {M e u α c : ℝ} (hM : 0 ≤ M) (he : 0 ≤ e) (hu0 : 0 ≤ u)
    (hα : 0 ≤ α) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 128) (hu : u ≤ 8 / 7 * (e + α))
    (h : M ^ 2 ≤ e ^ 2 + 2 * (c * (u * (u + e)))) : M ≤ e + 120 / 49 * (c * e) + 1 / 7 * α := by
  have hR : 0 ≤ e + 120 / 49 * (c * e) + 1 / 7 * α := by positivity
  refine (pow_le_pow_iff_left₀ hM hR two_ne_zero).mp (h.trans ?_)
  have hU : u * (u + e) ≤ 8 / 7 * (e + α) * (8 / 7 * (e + α) + e) :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h1 : c * (u * (u + e)) ≤ c * (8 / 7 * (e + α) * (8 / 7 * (e + α) + e)) :=
    mul_le_mul_of_nonneg_left hU hc0
  have h2 : c * (e * α) ≤ 1 / 128 * (e * α) := mul_le_mul_of_nonneg_right hc (by positivity)
  have h3 : c * α ^ 2 ≤ 1 / 128 * α ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
  have e1 : c * (8 / 7 * (e + α) * (8 / 7 * (e + α) + e)) =
      120 / 49 * (c * e ^ 2) + 184 / 49 * (c * (e * α)) + 64 / 49 * (c * α ^ 2) := by ring
  have e2 : (e + 120 / 49 * (c * e) + 1 / 7 * α) ^ 2 =
      e ^ 2 + 240 / 49 * (c * e ^ 2) + 2 / 7 * (e * α) + 1 / 49 * α ^ 2 +
        ((120 / 49 * (c * e)) ^ 2 + 2 * (120 / 49 * (c * e)) * (1 / 7 * α)) := by ring
  have h4 : 0 ≤ (120 / 49 * (c * e)) ^ 2 + 2 * (120 / 49 * (c * e)) * (1 / 7 * α) := by
    positivity
  have h5 : 0 ≤ e * α := mul_nonneg he hα
  have h6 : 0 ≤ α ^ 2 := sq_nonneg α
  rw [e2]
  linarith

/-- The arithmetic of the one-step bound. -/
private theorem step_arith_normal {e a b u v dK dL k ηX ηR ηF θ τ δ L M nb w : ℝ} (he : 0 ≤ e)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ha0 : 0 ≤ a) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hdL0 : 0 ≤ dL) (hk0 : 0 ≤ k) (hηR0 : 0 ≤ ηR) (hM0 : 0 ≤ M) (hw0 : 0 ≤ w) (hθ0 : 0 ≤ θ)
    (hηF : ηF ≤ 1 / 16) (hηX : ηX ≤ ηF) (hk : k ≤ ηX) (hθ : θ ≤ 1 / 16)
    (H : L ≤ M + (a + b + dK * a + dK * δ * dL) + dK * (k * (v + e)))
    (hM : M ^ 2 ≤ e ^ 2 + 2 * nb * w) (hnb : nb ≤ u * (k + θ)) (hw : w ≤ k * (u + e))
    (ha : a ≤ ηR * e + ηF * τ) (hb : b ≤ ηR * e + ηF * τ) (hu : 7 / 8 * u ≤ e + a)
    (hv : 7 / 8 * v ≤ e + b) (hdK : 7 / 8 * dK ≤ ηF) (hdL : 7 / 8 * dL ≤ ηF) :
    L ≤ (1 + 9 / 4 * ηR + 5 / 2 * ηX * (θ + 2 * ηF)) * e + 9 / 4 * ηF * τ +
      4 / 3 * ηF ^ 2 * δ := by
  have hηX0 : 0 ≤ ηX := hk0.trans hk
  have hηF0 : 0 ≤ ηF := hηX0.trans hηX
  have hηX16 : ηX ≤ 1 / 16 := hηX.trans hηF
  have hα0 : 0 ≤ ηR * e + ηF * τ := add_nonneg (mul_nonneg hηR0 he) (mul_nonneg hηF0 hτ)
  have hdK' : dK ≤ 8 / 7 * ηF := by linarith
  have hdL' : dL ≤ 8 / 7 * ηF := by linarith
  have hdK14 : dK ≤ 1 / 14 := by linarith
  have hu' : u ≤ 8 / 7 * (e + (ηR * e + ηF * τ)) := by linarith
  have hv' : v + e ≤ 15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ) := by linarith
  -- the old error with the exchanged normal component
  have hc0 : 0 ≤ ηX * (ηX + θ) := mul_nonneg hηX0 (add_nonneg hηX0 hθ0)
  have hc : ηX * (ηX + θ) ≤ 1 / 128 := by
    have := mul_le_mul hηX16 (by linarith : ηX + θ ≤ 1 / 8) (add_nonneg hηX0 hθ0)
      (by norm_num : (0 : ℝ) ≤ 1 / 16)
    linarith
  have hnbw : nb * w ≤ ηX * (ηX + θ) * (u * (u + e)) := by
    have h1 : nb * w ≤ u * (k + θ) * (k * (u + e)) :=
      mul_le_mul hnb hw hw0 (mul_nonneg hu0 (add_nonneg hk0 hθ0))
    have h2 : k * (k + θ) ≤ ηX * (ηX + θ) :=
      mul_le_mul hk (by linarith) (add_nonneg hk0 hθ0) hηX0
    have h3 : u * (k + θ) * (k * (u + e)) = k * (k + θ) * (u * (u + e)) := by ring
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (mul_nonneg hu0 (add_nonneg hu0 he)))
  have hM' : M ^ 2 ≤ e ^ 2 + 2 * (ηX * (ηX + θ) * (u * (u + e))) := by
    have e1 : 2 * nb * w = 2 * (nb * w) := by ring
    rw [e1] at hM
    linarith
  have hMle := norm_le_of_sq_le_normal hM0 he hu0 hα0 hc0 hc hu' hM'
  -- the terms of the tail increment and the second part of the increment of the reference
  have f1 : dK * a ≤ 1 / 14 * (ηR * e + ηF * τ) := mul_le_mul hdK14 ha ha0 (by norm_num)
  have f2 : dK * δ * dL ≤ 4 / 3 * ηF ^ 2 * δ := by
    have h1 : dK * δ * dL ≤ 8 / 7 * ηF * δ * (8 / 7 * ηF) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdK' hδ) hdL' hdL0
        (mul_nonneg (by positivity) hδ)
    have h2 : 0 ≤ ηF ^ 2 * δ := mul_nonneg (sq_nonneg ηF) hδ
    have h3 : 8 / 7 * ηF * δ * (8 / 7 * ηF) = 64 / 49 * (ηF ^ 2 * δ) := by ring
    have h4 : 4 / 3 * ηF ^ 2 * δ = 4 / 3 * (ηF ^ 2 * δ) := by ring
    linarith
  have f4 : k * (v + e) ≤ ηX * (15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ)) :=
    mul_le_mul hk hv' (add_nonneg hv0 he) hηX0
  have f5 : dK * (k * (v + e)) ≤
      8 / 7 * ηF * (ηX * (15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ))) :=
    mul_le_mul hdK' f4 (mul_nonneg hk0 (add_nonneg hv0 he)) (by positivity)
  have f6 : ηF * ηX * (ηR * e + ηF * τ) ≤ 1 / 256 * (ηR * e + ηF * τ) := by
    have : ηF * ηX ≤ 1 / 16 * (1 / 16) := mul_le_mul hηF hηX16 hηX0 (by norm_num)
    exact (mul_le_mul_of_nonneg_right this hα0).trans_eq (by ring)
  have f7 : ηX * ηX * e ≤ ηX * ηF * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηX hηX0) he
  have hXF0 : 0 ≤ ηX * ηF * e := mul_nonneg (mul_nonneg hηX0 hηF0) he
  have hXθ0 : 0 ≤ ηX * θ * e := mul_nonneg (mul_nonneg hηX0 hθ0) he
  have hz0 : 0 ≤ ηR * e := mul_nonneg hηR0 he
  have hy0 : 0 ≤ ηF * τ := mul_nonneg hηF0 hτ
  have e1 : 120 / 49 * (ηX * (ηX + θ) * e) =
      120 / 49 * (ηX * ηX * e) + 120 / 49 * (ηX * θ * e) := by ring
  have e2 : 8 / 7 * ηF * (ηX * (15 / 7 * e + 8 / 7 * (ηR * e + ηF * τ))) =
      120 / 49 * (ηX * ηF * e) + 64 / 49 * (ηF * ηX * (ηR * e + ηF * τ)) := by ring
  have e3 : (1 + 9 / 4 * ηR + 5 / 2 * ηX * (θ + 2 * ηF)) * e + 9 / 4 * ηF * τ =
      e + 9 / 4 * (ηR * e) + 5 / 2 * (ηX * θ * e) + 5 * (ηX * ηF * e) + 9 / 4 * (ηF * τ) := by
    ring
  rw [e3]
  rw [e1] at hMle
  rw [e2] at f5
  linarith

variable {P P₀ : Matrix m m ℝ} {Q Q₀ : Matrix n n ℝ} {Y₀ A₀ A₁ X₀ X₁ : Matrix m n ℝ}
  {G₀ G₁ : Matrix n m ℝ} {g ηX ηR ηF θ τ : ℝ}

/-- **One BUG step for given data: the growth factor without the increment of the reference.**
In the setting of `MatrixBUG.norm_projStep_sub_le_of_trace` (a BUG step
`Y₁ = P₁ (Y₀ + (A₁ - A₀)) Q₁` from `Y₀ = P₀ Y₀ Q₀`, projectors of the trace of the projectors of
the references `X₀`, `X₁`, generalized inverses with `‖G₀‖₂, ‖G₁‖₂ ≤ g`, tails orthogonal to the
references, `ΔR = (A₁ - X₁) - (A₀ - X₀)`,

  `g ‖X₁ - X₀‖₂ ≤ η_X`, `g ‖ΔR‖₂ ≤ η_R`, `g ‖X₁ - X₀‖ ≤ η_F`, `g ‖A₁ - A₀‖ ≤ η_F`,
  `η_X ≤ η_F ≤ 1/16`, `‖A₁ - X₁‖₂ ≤ τ`),

let `g ‖Y₀ - X₀‖ ≤ θ ≤ 1/16`. Then

  `‖Y₁ - X₁‖ ≤ (1 + 9/4 η_R + 5/2 η_X (θ + 2 η_F)) ‖Y₀ - X₀‖ + 9/4 η_F τ + 4/3 η_F² ‖ΔR‖₂`.

The increment of the reference enters the factor of the old error only multiplied by the
relative size `θ` of the error and by the step number `η_F`; at first order in the step the
factor has the increment of the tail only. -/
theorem norm_projStep_sub_le_of_trace_of_ginv_mul_norm_le (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (hP₀ : IsOrthProjMat P₀) (hQ₀ : IsOrthProjMat Q₀)
    (hY₀P : P₀ * Y₀ = Y₀) (hY₀Q : Y₀ * Q₀ = Y₀)
    (hK : P * ((Y₀ + (A₁ - A₀)) * Q₀) = (Y₀ + (A₁ - A₀)) * Q₀)
    (hL : P₀ * (Y₀ + (A₁ - A₀)) * Q = P₀ * (Y₀ + (A₁ - A₀)))
    (hX₀ : X₀ * G₀ * X₀ = X₀) (hc₀ : (X₀ * G₀)ᵀ = X₀ * G₀) (hr₀ : (G₀ * X₀)ᵀ = G₀ * X₀)
    (hX₁ : X₁ * G₁ * X₁ = X₁) (hc₁ : (X₁ * G₁)ᵀ = X₁ * G₁) (hr₁ : (G₁ * X₁)ᵀ = G₁ * X₁)
    (hRG₀ : (A₀ - X₀) * G₀ = 0) (hGR₀ : G₀ * (A₀ - X₀) = 0) (hRG₁ : (A₁ - X₁) * G₁ = 0)
    (hGR₁ : G₁ * (A₁ - X₁) = 0) (htrP : trace P = trace P₀) (htrQ : trace Q = trace Q₀)
    (htrP₀ : trace P₀ = trace (X₀ * G₀)) (htrQ₀ : trace Q₀ = trace (G₀ * X₀))
    (hG₀ : specNorm G₀ ≤ g) (hG₁ : specNorm G₁ ≤ g) (hξ₂ : g * specNorm (X₁ - X₀) ≤ ηX)
    (hδ : g * specNorm (A₁ - X₁ - (A₀ - X₀)) ≤ ηR) (hξ : g * ‖X₁ - X₀‖ ≤ ηF)
    (hν : g * ‖A₁ - A₀‖ ≤ ηF) (hηX : ηX ≤ ηF) (hηF : ηF ≤ 1 / 16)
    (he : g * ‖Y₀ - X₀‖ ≤ θ) (hθ : θ ≤ 1 / 16) (hτ : specNorm (A₁ - X₁) ≤ τ) :
    ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      (1 + 9 / 4 * ηR + 5 / 2 * ηX * (θ + 2 * ηF)) * ‖Y₀ - X₀‖ + 9 / 4 * ηF * τ +
        4 / 3 * ηF ^ 2 * specNorm (A₁ - X₁ - (A₀ - X₀)) := by
  have hg : 0 ≤ g := (specNorm_nonneg _).trans hG₀
  have hτ0 : 0 ≤ τ := (specNorm_nonneg _).trans hτ
  have he16 : g * ‖Y₀ - X₀‖ ≤ 1 / 16 := he.trans hθ
  have hθ0 : 0 ≤ θ := (mul_nonneg hg (norm_nonneg _)).trans he
  have hmis : Y₀ + (A₁ - A₀) - X₁ = Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  have hD : A₁ - A₀ = X₁ - X₀ + (A₁ - X₁ - (A₀ - X₀)) := by abel
  -- the tail increment seen from the old bases
  have ha0 := norm_tail_sub_mul_le_of_trace hQ₀ hY₀Q hX₀ hr₀ htrQ₀ hX₁ hr₁ hRG₀ hRG₁ hG₀ hτ
    le_rfl
  have hb0 := norm_mul_tail_sub_le_of_trace hP₀ hY₀P hX₀ hc₀ htrP₀ hX₁ hc₁ hGR₀ hGR₁ hG₀ hτ
    le_rfl
  have hαle : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) + τ * g * ‖X₁ - X₀‖ ≤
      ηR * ‖Y₀ - X₀‖ + ηF * τ := by
    have h1 : specNorm (A₁ - X₁ - (A₀ - X₀)) * (g * ‖Y₀ - X₀‖) =
        g * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖Y₀ - X₀‖ := by ring
    have h2 : τ * g * ‖X₁ - X₀‖ = g * ‖X₁ - X₀‖ * τ := by ring
    rw [h1, h2]
    exact add_le_add (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hξ hτ0)
  have ha := ha0.trans hαle
  have hb := hb0.trans hαle
  -- the angles between the old and the new bases
  have hdK := one_sub_mul_norm_mul_one_sub_le_of_capture hP hP₀ hQ₀ hY₀P hY₀Q hK hX₀ hc₀ htrP
    htrP₀ hG₀
  have hdL := one_sub_mul_norm_one_sub_mul_le_of_capture hQ hP₀ hQ₀ hY₀P hY₀Q hL hX₀ hr₀ htrQ
    htrQ₀ hG₀
  have hdK' : 7 / 8 * ‖P * (1 - P₀)‖ ≤ ηF := by
    have := mul_le_mul_of_nonneg_right (by linarith : 7 / 8 ≤ 1 - 2 * (g * ‖Y₀ - X₀‖))
      (norm_nonneg (P * (1 - P₀)))
    linarith
  have hdL' : 7 / 8 * ‖(1 - Q₀) * Q‖ ≤ ηF := by
    have := mul_le_mul_of_nonneg_right (by linarith : 7 / 8 ≤ 1 - 2 * (g * ‖Y₀ - X₀‖))
      (norm_nonneg ((1 - Q₀) * Q))
    linarith
  -- capture of the reference
  have hs : specNorm G₁ * specNorm (X₁ - Y₀) ≤ 1 / 8 := by
    have h1 : specNorm (X₁ - Y₀) ≤ ‖X₁ - X₀‖ + ‖Y₀ - X₀‖ :=
      (specNorm_le_frob _).trans ((norm_sub_le_norm_sub_add_norm_sub X₁ X₀ Y₀).trans_eq
        (by rw [norm_sub_rev X₀ Y₀]))
    have h2 : specNorm G₁ * specNorm (X₁ - Y₀) ≤ g * (‖X₁ - X₀‖ + ‖Y₀ - X₀‖) :=
      mul_le_mul hG₁ h1 (specNorm_nonneg _) hg
    linarith
  have hu0 := one_sub_mul_norm_one_sub_mul_le hP hQ₀ hY₀Q hK hX₁ hs
  have hv0 := one_sub_mul_norm_mul_one_sub_le hQ hP₀ hY₀P hL hX₁ hs
  rw [hmis] at hu0 hv0
  have hu : 7 / 8 * ‖(1 - P) * X₁‖ ≤ ‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ := by
    have h1 : ‖(Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀))) * Q₀‖ ≤
        ‖Y₀ - X₀‖ + ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ := by
      rw [Matrix.add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hQ₀.norm_mul_le' _) le_rfl)
    norm_num at hu0
    linarith
  have hv : 7 / 8 * ‖X₁ * (1 - Q)‖ ≤ ‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ := by
    have h1 : ‖P₀ * (Y₀ - X₀ + (A₁ - X₁ - (A₀ - X₀)))‖ ≤
        ‖Y₀ - X₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ := by
      rw [Matrix.mul_add]
      exact (norm_add_le _ _).trans (add_le_add (hP₀.norm_mul_le _) le_rfl)
    norm_num at hv0
    linarith
  -- the increment of the reference between the bases
  have ht5 := norm_one_sub_mul_sub_mul_one_sub_le hP hQ₀ hY₀Q hX₀ hX₁ hc₁ hG₀ hG₁
    (le_refl (specNorm (X₁ - X₀)))
  have ht6 := norm_mul_one_sub_mul_sub_mul_one_sub_le (P := 1)
    ⟨Matrix.transpose_one, Matrix.mul_one 1⟩ hP₀ hQ hY₀P hX₀ hX₁ hr₁ hG₀ hG₁
    (le_refl (specNorm (X₁ - X₀)))
  rw [Matrix.one_mul] at ht6
  have hW : (1 - P₀) * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) = (1 - P₀) * (X₁ - X₀) * (1 - Q) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP₀.compl.idem]
  have n6 : ‖P * ((1 - P₀) * (X₁ - X₀) * (1 - Q))‖ ≤
      ‖P * (1 - P₀)‖ * (g * specNorm (X₁ - X₀) * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖)) := by
    rw [← hW, ← Matrix.mul_assoc P (1 - P₀)]
    exact (frob_mul_le _ _).trans
      (mul_le_mul (specNorm_le_frob _) ht6 (norm_nonneg _) (norm_nonneg _))
  -- the normal component of the reference and the exchanged old error
  have hsq := norm_sub_sub_one_sub_mul_sub_mul_one_sub_sq_le (X₀ := X₀) (X₁ := X₁) hP hQ₀ hY₀Q
  have hnb : ‖(1 - P) * X₁ * (1 - Q₀)‖ ≤ ‖(1 - P) * X₁‖ * (g * specNorm (X₁ - X₀) + θ) := by
    refine (norm_one_sub_mul_mul_one_sub_le (X₀ := X₀) hQ₀ hY₀Q hX₁ hG₁).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [mul_add]
    linarith
  -- the tail increment through the new bases
  have n1 : ‖(1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀)‖ ≤ ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ :=
    hP.compl.norm_mul_le _
  have n2 : ‖P * (P₀ * (A₁ - X₁ - (A₀ - X₀)))‖ ≤ ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ :=
    hP.norm_mul_le _
  have n3 : ‖P * (1 - P₀) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) * Q‖ ≤
      ‖P * (1 - P₀)‖ * ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ :=
    (hQ.norm_mul_le' _).trans ((frob_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (specNorm_le_frob _) (norm_nonneg _)))
  have n4 : ‖P * (1 - P₀) * (A₁ - X₁ - (A₀ - X₀)) * ((1 - Q₀) * Q)‖ ≤
      ‖P * (1 - P₀)‖ * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖(1 - Q₀) * Q‖ :=
    (frob_mul_le' _ _).trans (mul_le_mul (frob_mul_le' _ _) (specNorm_le_frob _)
      (specNorm_nonneg _) (mul_nonneg (norm_nonneg _) (specNorm_nonneg _)))
  -- the error of the step
  have hstep : P * (Y₀ + (A₁ - A₀)) * Q - X₁ =
      Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀) +
        ((1 - P) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) + P * (P₀ * (A₁ - X₁ - (A₀ - X₀))) +
        P * (1 - P₀) * ((A₁ - X₁ - (A₀ - X₀)) * Q₀) * Q +
        P * (1 - P₀) * (A₁ - X₁ - (A₀ - X₀)) * ((1 - Q₀) * Q)) -
        P * ((1 - P₀) * (X₁ - X₀) * (1 - Q)) := by
    rw [projStep_eq_add_sub hY₀P hY₀Q hK hL, ← err_split_normal, ← hD]
    abel
  have H : ‖P * (Y₀ + (A₁ - A₀)) * Q - X₁‖ ≤
      ‖Y₀ - X₀ - (1 - P) * (X₁ - X₀) * (1 - Q₀)‖ +
        (‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ + ‖P₀ * (A₁ - X₁ - (A₀ - X₀))‖ +
        ‖P * (1 - P₀)‖ * ‖(A₁ - X₁ - (A₀ - X₀)) * Q₀‖ +
        ‖P * (1 - P₀)‖ * specNorm (A₁ - X₁ - (A₀ - X₀)) * ‖(1 - Q₀) * Q‖) +
        ‖P * (1 - P₀)‖ * (g * specNorm (X₁ - X₀) * (‖X₁ * (1 - Q)‖ + ‖Y₀ - X₀‖)) := by
    rw [hstep]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl ?_)) n6)
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add n1 n2)) n3)) n4)
  exact step_arith_normal (norm_nonneg _) hτ0 (specNorm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg hg (specNorm_nonneg _)) ((mul_nonneg hg (specNorm_nonneg _)).trans hδ)
    (norm_nonneg _) (norm_nonneg _) hθ0 hηF hηX hξ₂ hθ H hsq hnb ht5 ha hb hu hv hdK' hdL'

end Main

end MatrixBUG

end LeanDLRA
