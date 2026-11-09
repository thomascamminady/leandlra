import LeanDLRA.Foundations.Existence
import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.KStep
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Integrators.Matrix.ProjectorSplitting
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Training.Descent
import LeanDLRA.Training.FactorizedDynamics

/-!
# Results of arXiv 2502.03006: Augmented backward-corrected PSI for low-rank training

Kusch, Schotthöfer, Walter, *An augmented backward-corrected projector splitting integrator for
dynamical low-rank training*.  This module treats real `m × n` matrices with the Frobenius norm, at
the level of the factors `U, S, V, K, L` that the algorithms compute, for the gradient flow
`W' = -∇ℓ(W)`.  With A1 `‖Y₀ - W₀‖ ≤ δ`, A2 `∇ℓ` `c`-Lipschitz (the paper's `c_l`), A3 `‖∇ℓ‖ ≤ B`
and A4 `ResidualBound` (`‖(I - P(Y)) ∇ℓ(Y)‖ ≤ ε` on the manifold `M_r`), it proves: Lemma 5.1 for
PSI (`psi_loss_le`, with the library's `MatrixKSL.IsStep`, and `psi_sStep_loss_ge` for the claim
that the backward S-step can raise the loss); Lemma 5.4 for bc-PSI (`IsBcPsiStep.loss_le`); Theorem
5.3 (`IsBcPsiStep.local_error`, `IsBcPsiStep.local_error_le`, `bcPsi_global_error`); Theorem 5.6
(`IsAbcPsiStep.local_error`, `IsAbcPsiStep.local_error_truncated`, `abcPsi_global_error`,
`abcPsi_global_error_le`, and `IsAbcPsiStep.loss_le` for the remark after Lemma 5.4); and the
deterministic form of Theorem 5.9 (`abcPsi_liminf_tangentGrad_eq_zero`, for Algorithm 4.1,
`abcPsiEulerStep`).  `exists_isBcPsiStep`, `exists_isAbcPsiStep`, `exists_isAbcPsiEulerBasis` and
the `example` at the end, with the loss `cosLoss`, show that the hypotheses hold.  Lemma 5.7 and
Theorem 5.8 are `descent_lemma` and `loss_projGradStep_le` of `Training/Descent.lean`.

**False claim.**  The bound of Theorem 5.6 as printed, `ε + c₁ h + c₂ δ + ϑ/h`, has coefficient `1`
on `ε`.  `abcPsi_literal_bound_false` refutes it on `3 × 2` matrices; the correct coefficient
contains `T`, as in `abcPsi_global_error_le`.  The paper's local bound before truncation,
`h ε + 3 c_l B h²` (5.12), is correct (`IsAbcPsiStep.local_error`).

**Differences from the paper.**  (1) A4 is stated on `M_r` (invertible `S`), and
`ResidualBound.normal_le` extends it to singular `S` by density, so that `K(t₁)` may be
rank-deficient, which the paper does not discuss.  (2) Theorem 5.3 is proved directly with
`kstep_capture` and `galerkin_step_error`, where the paper compares with PSI and quotes
Kieri-Lubich-Walach; the intermediate PSI versus bc-PSI bound of the paper is therefore not
formalized.  (3) All constants are explicit; in Theorem 5.3 they are the library's `bugC₁`, `bugC₂`
for step sizes `h ≤ H`.  (4) The paper uses both `ϑ` and `ϑ/h` for the local truncation term; the
local term is `ϑ`, and `ϑ/h` arises only in the global bound.  (5) In Theorem 5.6, A4 is required
at every rank of the run, since truncation changes the rank.  (6) Theorem 5.9 is deterministic:
gradients are exact, so there are no expectations.  It is proved for Algorithm 4.1, as is the
paper's Theorem 5.8, and needs `h_t > 0`.  The mini-batch statement is left out because the
paper's argument does not carry over: a batch K-step does not capture `P(Y) ∇ℓ(Y)`, and the
telescoping mixes losses of different batches (`InexactGradient.variance_term_necessary`).  (7) The
proof of Theorem 5.9 replaces the false identity `P_Û ∇ℓ = P(Y) ∇ℓ`
(`FactorizedDynamics.exists_leftProj_ne_tangentProj_of_capture`) by the inequality
`‖P(Y) ∇ℓ‖ ≤ ‖P_Û ∇ℓ‖`, and bounds the truncation error of the loss with `B`, the Lipschitz
constant of `ℓ`, not with `c_l`.  The conclusion of the theorem is not affected.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2502_03006

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### Abstract estimates on an inner product space -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Upper bound for the loss along an ascent flow `y' = +P ∇ℒ(y)` (the backward S-step of
arXiv 2502.03006, Eq. (3.3b)): if `‖P ∇ℒ(y t)‖ ≤ α`, then `ℒ(y t) ≤ ℒ(y a) + α² (t - a)`. -/
theorem loss_le_of_ascent {ℒ : E → ℝ} {g : E → E} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ x => P (g x)) y a b) {α : ℝ}
    (hα : ∀ t ∈ Ico a b, ‖P (g (y t))‖ ^ 2 ≤ α ^ 2) :
    ∀ t ∈ Icc a b, ℒ (y t) ≤ ℒ (y a) + α ^ 2 * (t - a) := by
  have hc : ContinuousOn (ℒ ∘ y) (Icc a b) :=
    (continuous_of_hasFDerivAt_innerSL hℒ).comp_continuousOn hy.cont
  have hd : ∀ t ∈ Ico a b, HasDerivWithinAt (ℒ ∘ y) (‖P (g (y t))‖ ^ 2) (Ici t) t :=
    fun t ht => (hasDerivWithinAt_energy_comp hℒ (hy.deriv t ht)).congr_deriv (by
      rw [real_inner_comm, hP.inner_self_apply])
  have hB : ∀ t, HasDerivWithinAt (fun s => ℒ (y a) + α ^ 2 * (s - a)) (α ^ 2) (Ici t) t :=
    fun t => by
      simpa using (((hasDerivWithinAt_id t (Ici t)).sub_const a).const_mul (α ^ 2)).const_add
        (ℒ (y a))
  have h := image_le_of_deriv_right_le_deriv_boundary hc hd
    (B := fun s => ℒ (y a) + α ^ 2 * (s - a)) (by simp)
    (Continuous.continuousOn (by fun_prop)) (fun t _ => hB t) hα
  exact fun t ht => h ht

/-- Lower bound for the loss along an ascent flow `y' = +P ∇ℒ(y)`: if `α ≤ ‖P ∇ℒ(y t)‖`, then
`ℒ(y a) + α² (t - a) ≤ ℒ(y t)`, so the flow strictly increases the loss whenever `α ≠ 0`. -/
theorem le_loss_of_ascent {ℒ : E → ℝ} {g : E → E} (hℒ : ∀ x, HasFDerivAt ℒ (innerSL ℝ (g x)) x)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun _ x => P (g x)) y a b) {α : ℝ}
    (hα : ∀ t ∈ Ico a b, α ^ 2 ≤ ‖P (g (y t))‖ ^ 2) :
    ∀ t ∈ Icc a b, ℒ (y a) + α ^ 2 * (t - a) ≤ ℒ (y t) := by
  have hℒ' : ∀ x, HasFDerivAt (fun x => -ℒ x) (innerSL ℝ (-g x)) x := fun x => by
    rw [map_neg]
    exact (hℒ x).neg
  have h := loss_le_of_projGradFlow hℒ' (P := fun _ => P) (fun _ => hP) hy.cont
    (fun t ht => by simpa [map_neg] using hy.deriv t ht) (α := α)
    (fun t ht => by simpa [map_neg] using hα t ht)
  intro t ht
  have := h t ht
  linarith

/-- **Abstract core of the local error of abc-PSI** (arXiv 2502.03006, proof of Theorem 5.6).
Let `G` be `c`-Lipschitz and bounded by `B`, `W' = -G(W)`, `YK' = -Q₀ G(YK)`, `YL' = -Π G(YL)`,
all three started at `Y₀` on `[t₀, t₁]`, `t₁ = t₀ + h`, where `Π` and `Q₀` are orthogonal
projectors with `Π Y₀ = Y₀` and `Π (YK t₁) = YK t₁`.  If `‖(1 - Π)(1 - Q₀) G(Y₀)‖ ≤ ε`, then
`‖YL t₁ - W t₁‖ ≤ h ε + 3 c B h²`. -/
theorem augmented_local_error {G : E → E} {c B ε t₀ t₁ h : ℝ}
    (hG : ∀ x y, ‖G x - G y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hB : ∀ x, ‖G x‖ ≤ B)
    {Pi Q₀ : E →L[ℝ] E} (hPi : IsOrthProj Pi) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {W YK YL : ℝ → E} {Y₀ : E}
    (hW : ODESolution (fun _ x => -G x) W t₀ t₁) (hW₀ : W t₀ = Y₀)
    (hK : ODESolution (fun _ x => Q₀ (-G x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hPiY : Pi Y₀ = Y₀) (hPiK : Pi (YK t₁) = YK t₁)
    (hL : ODESolution (fun _ x => Pi (-G x)) YL t₀ t₁) (hL₀ : YL t₀ = Y₀)
    (hε : ‖(1 - Pi) ((1 - Q₀) (G Y₀))‖ ≤ ε) :
    ‖YL t₁ - W t₁‖ ≤ h * ε + 3 * c * B * h ^ 2 := by
  have hle : t₀ ≤ t₁ := by linarith
  have hBF : IsBoundedField (fun (_ : ℝ) (x : E) => -G x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hB0 : 0 ≤ B := hBF.nonneg
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  have hsK : ∀ t ∈ Icc t₀ t₁, ‖YK t - Y₀‖ ≤ B * h := fun t ht => by
    simpa [hK₀] using ODESolution.norm_sub_start_le_of_proj hBF hQ₀ ht₁ hK t ht
  have hsL : ∀ t ∈ Icc t₀ t₁, ‖YL t - Y₀‖ ≤ B * h := fun t ht => by
    simpa [hL₀] using ODESolution.norm_sub_start_le_of_proj hBF hPi ht₁ hL t ht
  have hsW : ∀ t ∈ Icc t₀ t₁, ‖W t - Y₀‖ ≤ B * h := fun t ht => by
    simpa [hW₀] using hW.norm_sub_start_le hBF ht₁ t ht
  -- Step 7-9 of the paper: the K-step increment removes `(1 - Π) Q₀ G(Y₀)` up to `c B h²`.
  set v : E := (1 - Pi) (Q₀ (G Y₀)) with hv
  have hstep : ‖h • v‖ ≤ c * (B * h) * h := by
    set φ : ℝ → E := fun t => (1 - Pi) (YK t + (t - t₀) • Q₀ (G Y₀)) with hφ
    have hφc : ContinuousOn φ (Icc t₀ t₁) :=
      (1 - Pi).continuous.comp_continuousOn
        (hK.cont.add (ContinuousOn.smul (by fun_prop) continuousOn_const))
    have hφd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt φ
        ((1 - Pi) (Q₀ (-G (YK t)) + Q₀ (G Y₀))) (Ici t) t := fun t ht => by
      have h1 : HasDerivWithinAt (fun t => (t - t₀) • Q₀ (G Y₀)) (Q₀ (G Y₀)) (Ici t) t := by
        simpa using ((hasDerivWithinAt_id t (Ici t)).sub_const t₀).smul_const (Q₀ (G Y₀))
      exact (1 - Pi).hasFDerivAt.comp_hasDerivWithinAt t ((hK.deriv t ht).add h1)
    have hφb : ∀ t ∈ Ico t₀ t₁, ‖(1 - Pi) (Q₀ (-G (YK t)) + Q₀ (G Y₀))‖ ≤ c * (B * h) := by
      intro t ht
      have e : Q₀ (-G (YK t)) + Q₀ (G Y₀) = Q₀ (G Y₀ - G (YK t)) := by
        rw [map_neg, map_sub]; abel
      rw [e]
      calc _ ≤ ‖Q₀ (G Y₀ - G (YK t))‖ := hPi.compl.norm_le _
        _ ≤ ‖G Y₀ - G (YK t)‖ := hQ₀.norm_le _
        _ ≤ c * ‖Y₀ - YK t‖ := hG _ _
        _ ≤ c * (B * h) := by
            rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_left (hsK t (Ico_subset_Icc_self ht)) hc
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd hφb t₁ ⟨hle, le_rfl⟩
    have h0 : φ t₀ = 0 := by
      simp [hφ, hK₀, hPiY]
    have h1 : φ t₁ = h • v := by
      simp [hφ, hv, hlen, hPiK, map_add, map_smul]
    rw [h0, h1, sub_zero, hlen] at hmvt
    exact hmvt
  have hhv : h * ‖v‖ ≤ c * (B * h) * h := by
    rw [norm_smul, Real.norm_of_nonneg hh] at hstep
    exact hstep
  -- the error equation
  set e : ℝ → E := fun t => YL t - W t with he
  have hec : ContinuousOn e (Icc t₀ t₁) := hL.cont.sub hW.cont
  have hed : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt e (Pi (-G (YL t)) - -G (W t)) (Ici t) t :=
    fun t ht => (hL.deriv t ht).sub (hW.deriv t ht)
  have heb : ∀ t ∈ Ico t₀ t₁, ‖Pi (-G (YL t)) - -G (W t)‖ ≤ 2 * (c * (B * h)) + ‖v‖ + ε := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hdec : Pi (-G (YL t)) - -G (W t) =
        Pi (G Y₀ - G (YL t)) + (G (W t) - G Y₀) + (v + (1 - Pi) ((1 - Q₀) (G Y₀))) := by
      simp only [hv, map_sub, map_neg, sub_apply, one_apply_eq_self]
      abel
    have h1 : ‖Pi (G Y₀ - G (YL t))‖ ≤ c * (B * h) :=
      calc _ ≤ ‖G Y₀ - G (YL t)‖ := hPi.norm_le _
        _ ≤ c * ‖Y₀ - YL t‖ := hG _ _
        _ ≤ c * (B * h) := by
            rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_left (hsL t ht') hc
    have h2 : ‖G (W t) - G Y₀‖ ≤ c * (B * h) :=
      (hG _ _).trans (mul_le_mul_of_nonneg_left (hsW t ht') hc)
    rw [hdec]
    have h3 := norm_add₃_le (a := Pi (G Y₀ - G (YL t))) (b := G (W t) - G Y₀)
      (c := v + (1 - Pi) ((1 - Q₀) (G Y₀)))
    have h4 := norm_add_le v ((1 - Pi) ((1 - Q₀) (G Y₀)))
    linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hec hed heb t₁ ⟨hle, le_rfl⟩
  have he0 : e t₀ = 0 := by simp [he, hL₀, hW₀]
  rw [he0, sub_zero, hlen] at hmvt
  have hexp : (2 * (c * (B * h)) + ‖v‖ + ε) * h ≤ h * ε + 3 * c * B * h ^ 2 := by nlinarith
  exact hmvt.trans hexp

end Abstract

/-! ### Assumption A4 on the manifold of rank-`r` matrices -/

section Residual

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- **Assumption A4** of arXiv 2502.03006: `‖R(Y)‖ ≤ ε` for all `Y ∈ M_r`, where
`R(Y) = ∇ℓ(Y) - M(Y)` and `M(Y) = P(Y) ∇ℓ(Y)` is the tangential part.  Every `Y ∈ M_r` is
`U S Vᵀ` with `U`, `V` orthonormal and `S` invertible, and then `P(Y) = tangentProj U V`, so this
is literally the paper's assumption; singular `S` is not included. -/
def ResidualBound (g : Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (V : Matrix n (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S →
      ‖g (U * S * Vᵀ) - tangentProj U V (g (U * S * Vᵀ))‖ ≤ ε

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Invertible matrices are dense: `S + t I` is invertible for arbitrarily small `t > 0`, since the
characteristic polynomial of `-S` has finitely many roots. -/
lemma exists_isUnit_add_smul (S : Matrix (Fin r) (Fin r) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < η ∧ IsUnit (S + t • (1 : Matrix (Fin r) (Fin r) ℝ)) := by
  set p := (-S).charpoly with hp
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hinf : (Set.Ioo 0 η \ (p.roots.toFinset : Set ℝ)).Infinite :=
    (Set.Ioo_infinite hη).sdiff (Finset.finite_toSet _)
  obtain ⟨t, ⟨ht0, ht1⟩, htr⟩ := hinf.nonempty
  refine ⟨t, ht0, ht1, ?_⟩
  have hne : p.eval t ≠ 0 := fun h0 =>
    htr (by simpa [Polynomial.mem_roots hp0] using h0)
  rw [hp, Matrix.eval_charpoly] at hne
  have e : Matrix.scalar (Fin r) t - -S = S + t • (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, add_comm]
  rw [e] at hne
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)

/-- **Assumption A4 extends to rank `≤ r`.**  For a Lipschitz gradient, the bound of
`ResidualBound` on `M_r` passes to `U S Vᵀ` with singular `S`: perturb `S` to `S + t I`, which has
the same `U`, `V`, hence the same normal projector.  So no rank assumption on the K-step result
`K(t₁) = U₁ R₁` is needed in Theorems 5.3 and 5.6. -/
theorem ResidualBound.normal_le {g : Matrix m n ℝ → Matrix m n ℝ} {c ε : ℝ}
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hA4 : ResidualBound g r ε)
    {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix (Fin r) (Fin r) ℝ) :
    ‖(1 - U * Uᵀ) * g (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  set D : ℝ := ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have hpos : 0 < c * D + 1 := by positivity
  obtain ⟨t, ht0, ht1, hunit⟩ := exists_isUnit_add_smul S (div_pos hη hpos)
  set S' := S + t • (1 : Matrix (Fin r) (Fin r) ℝ) with hS'
  have h1 := hA4 U S' V hU hV hunit
  have hN := isOrthProj_normal_leftProj_rightProj (m := m) (n := n) hU hV
  have h2 : ‖g (U * S' * Vᵀ) - tangentProj U V (g (U * S' * Vᵀ))‖ =
      ‖(1 - U * Uᵀ) * g (U * S' * Vᵀ) * (1 - V * Vᵀ)‖ := by
    congr 1
    rw [sub_eq_iff_eq_add']
    exact (tangentProj_add_normal U V _).symm
  have hdist : ‖U * S * Vᵀ - U * S' * Vᵀ‖ = t * D := by
    have e : U * S * Vᵀ - U * S' * Vᵀ = U * (-(t • (1 : Matrix (Fin r) (Fin r) ℝ))) * Vᵀ := by
      rw [hS']
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul]
      abel
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU,
      norm_neg, norm_smul, Real.norm_of_nonneg ht0.le]
  have h3 : ‖(1 - U * Uᵀ) * g (U * S * Vᵀ) * (1 - V * Vᵀ)
      - (1 - U * Uᵀ) * g (U * S' * Vᵀ) * (1 - V * Vᵀ)‖ ≤ c * (t * D) := by
    rw [← normal_leftProj_rightProj_apply, ← normal_leftProj_rightProj_apply, ← map_sub]
    refine (hN.norm_le _).trans ((hg _ _).trans ?_)
    rw [hdist]
  have h4 : c * (t * D) ≤ η := by
    have : t * (c * D + 1) < η := (lt_div_iff₀ hpos).1 ht1
    nlinarith
  have h5 := norm_sub_norm_le ((1 - U * Uᵀ) * g (U * S * Vᵀ) * (1 - V * Vᵀ))
    ((1 - U * Uᵀ) * g (U * S' * Vᵀ) * (1 - V * Vᵀ))
  rw [h2] at h1
  linarith

/-- Assumption A4 gives the factored normal-component assumption of the library for the gradient
flow field `F(t, Y) = -∇ℓ(Y)`. -/
theorem ResidualBound.factoredNormalBound {g : Matrix m n ℝ → Matrix m n ℝ} {c ε : ℝ}
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hA4 : ResidualBound g r ε) :
    MatrixBUG.FactoredNormalBound (fun _ Y => -g Y) r ε := by
  intro _ U V S hU hV
  simpa [Matrix.mul_neg, Matrix.neg_mul] using hA4.normal_le hg hc hU hV S

end Residual

/-! ### The loss along the substeps -/

section Loss

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]

/-- `α_K = min_{s ∈ [t₀, t₁]} ‖∇ℓ(Y_K(s)) V₀‖`, with `Y_K = K V₀ᵀ` (proof of Lemma 5.1 of
arXiv 2502.03006). -/
noncomputable def alphaK (g : Matrix m n ℝ → Matrix m n ℝ) (V₀ : Matrix n r ℝ)
    (K : ℝ → Matrix m r ℝ) (t₀ t₁ : ℝ) : ℝ :=
  sInf ((fun s => ‖g (K s * V₀ᵀ) * V₀‖) '' Icc t₀ t₁)

/-- `α_S = max_{s ∈ [t₀, t₁]} ‖U₁ᵀ ∇ℓ(Y_S(s)) V₀‖`, with `Y_S = U₁ S V₀ᵀ` (proof of Lemma 5.1 of
arXiv 2502.03006). -/
noncomputable def alphaS (g : Matrix m n ℝ → Matrix m n ℝ) (U₁ : Matrix m r ℝ)
    (V₀ : Matrix n r ℝ) (S : ℝ → Matrix r r ℝ) (t₀ t₁ : ℝ) : ℝ :=
  sSup ((fun s => ‖U₁ᵀ * g (U₁ * S s * V₀ᵀ) * V₀‖) '' Icc t₀ t₁)

/-- `α_L = min_{s ∈ [t₀, t₁]} ‖∇ℓ(Y_L(s))ᵀ U₁‖`, with `Y_L = U₁ Lᵀ` (proof of Lemmas 5.1 and 5.4
of arXiv 2502.03006). -/
noncomputable def alphaL (g : Matrix m n ℝ → Matrix m n ℝ) (U₁ : Matrix m r ℝ)
    (Lf : ℝ → Matrix n r ℝ) (t₀ t₁ : ℝ) : ℝ :=
  sInf ((fun s => ‖(g (U₁ * (Lf s)ᵀ))ᵀ * U₁‖) '' Icc t₀ t₁)

omit [Fintype m] [Fintype n] [Fintype r] in
/-- `(min f)² ≤ f(s)²` for a nonnegative `f` (used for `alphaK`, `alphaL`). -/
lemma sq_sInf_image_le {f : ℝ → ℝ} (hf : ∀ s, 0 ≤ f s) {a b s : ℝ} (hs : s ∈ Icc a b) :
    sInf (f '' Icc a b) ^ 2 ≤ f s ^ 2 := by
  have hb : BddBelow (f '' Icc a b) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hf x⟩
  exact pow_le_pow_left₀ (Real.sInf_nonneg (by rintro _ ⟨x, -, rfl⟩; exact hf x))
    (csInf_le hb ⟨s, hs, rfl⟩) 2

omit [Fintype m] [Fintype n] [Fintype r] in
/-- `f(s)² ≤ (max f)²` for a nonnegative `f` continuous on `[a, b]` (used for `alphaS`). -/
lemma sq_le_sSup_image {f : ℝ → ℝ} (hf : ∀ s, 0 ≤ f s) {a b s : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hs : s ∈ Icc a b) : f s ^ 2 ≤ sSup (f '' Icc a b) ^ 2 :=
  pow_le_pow_left₀ (hf s)
    (le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove ⟨s, hs, rfl⟩) 2

variable [DecidableEq r]

/-- `‖X V Vᵀ‖ = ‖X V‖` for orthonormal `V`. -/
lemma norm_rightProj_eq {V : Matrix n r ℝ} (hV : Vᵀ * V = 1) (X : Matrix m n ℝ) :
    ‖rightProj V X‖ = ‖X * V‖ := by
  rw [rightProj_apply, Frobenius.norm_mul_transpose_of_orthonormal hV]

/-- `‖U Uᵀ X‖ = ‖Xᵀ U‖` for orthonormal `U`. -/
lemma norm_leftProj_eq {U : Matrix m r ℝ} (hU : Uᵀ * U = 1) (X : Matrix m n ℝ) :
    ‖leftProj U X‖ = ‖Xᵀ * U‖ := by
  rw [leftProj_apply, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU,
    ← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- `‖U Uᵀ X V Vᵀ‖ = ‖Uᵀ X V‖` for orthonormal `U`, `V`. -/
lemma norm_leftProj_rightProj_eq {U : Matrix m r ℝ} {V : Matrix n r ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (X : Matrix m n ℝ) :
    ‖leftProj U (rightProj V X)‖ = ‖Uᵀ * X * V‖ := by
  rw [leftProj_rightProj_apply, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_of_orthonormal hU]

variable [DecidableEq m] [DecidableEq n]

variable {g : Matrix m n ℝ → Matrix m n ℝ} {ℓ : Matrix m n ℝ → ℝ} {c t₀ t₁ h : ℝ}
  {U₀ U₁ : Matrix m r ℝ} {S₀ Ŝ₁ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {K : ℝ → Matrix m r ℝ}
  {S : ℝ → Matrix r r ℝ} {Lf : ℝ → Matrix n r ℝ}

/-- A Lipschitz gradient is continuous. -/
lemma continuous_of_lipschitz (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) : Continuous g := by
  have hc' : ∀ x y, ‖g x - g y‖ ≤ max c 0 * ‖x - y‖ := fun x y =>
    (hg x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  exact (LipschitzWith.of_dist_le_mul (K := ⟨max c 0, le_max_right _ _⟩) fun x y => by
    rw [dist_eq_norm, dist_eq_norm]; exact hc' x y).continuous

/-- **The K-substep of PSI decreases the loss by `h α_K²`** (proof of Lemma 5.1 of
arXiv 2502.03006): `ℓ(K(t₁) V₀ᵀ) ≤ ℓ(K(t₀) V₀ᵀ) - h α_K²`. -/
theorem loss_kStep_le (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (hV₀ : V₀ᵀ * V₀ = 1)
    (hK : ODESolution (MatrixKSL.kField V₀ fun _ Y => -g Y) K t₀ t₁) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) :
    ℓ (K t₁ * V₀ᵀ) ≤ ℓ (K t₀ * V₀ᵀ) - alphaK g V₀ K t₀ t₁ ^ 2 * h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hY := MatrixKSL.odeSolution_kField hK
  have hB := loss_le_of_projGradFlow hℓ (P := fun _ => rightProj V₀)
    (fun _ => isOrthProj_rightProj hV₀) hY.cont
    (fun t ht => by simpa using hY.deriv t ht) (α := alphaK g V₀ K t₀ t₁)
    (fun t ht => by
      rw [norm_rightProj_eq hV₀]
      exact sq_sInf_image_le (f := fun s => ‖g (K s * V₀ᵀ) * V₀‖) (fun _ => norm_nonneg _)
        (Ico_subset_Icc_self ht)) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rwa [hlen] at hB

/-- **The L-substep decreases the loss by `h α_L²`** (proof of Lemmas 5.1 and 5.4 of
arXiv 2502.03006): `ℓ(U₁ L(t₁)ᵀ) ≤ ℓ(U₁ L(t₀)ᵀ) - h α_L²`. -/
theorem loss_lStep_le (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (hU₁ : U₁ᵀ * U₁ = 1)
    (hL : ODESolution (MatrixKSL.lField U₁ fun _ Y => -g Y) Lf t₀ t₁) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) :
    ℓ (U₁ * (Lf t₁)ᵀ) ≤ ℓ (U₁ * (Lf t₀)ᵀ) - alphaL g U₁ Lf t₀ t₁ ^ 2 * h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hY := MatrixKSL.odeSolution_lField hL
  have hB := loss_le_of_projGradFlow hℓ (P := fun _ => leftProj U₁)
    (fun _ => isOrthProj_leftProj hU₁) hY.cont
    (fun t ht => by simpa using hY.deriv t ht) (α := alphaL g U₁ Lf t₀ t₁)
    (fun t ht => by
      rw [norm_leftProj_eq hU₁]
      exact sq_sInf_image_le (f := fun s => ‖(g (U₁ * (Lf s)ᵀ))ᵀ * U₁‖) (fun _ => norm_nonneg _)
        (Ico_subset_Icc_self ht)) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rwa [hlen] at hB

/-- The backward S-step of PSI is the ascent flow `Y_S' = +P₁ Q₀ ∇ℓ(Y_S)` (`Ṡ = U₁ᵀ ∇ℓ V₀`). -/
lemma odeSolution_sStep (hS : ODESolution (MatrixKSL.sField U₁ V₀ fun _ Y => -g Y) S t₀ t₁) :
    ODESolution (fun _ x => (leftProj U₁ * rightProj V₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (g x))
      (fun t => U₁ * S t * V₀ᵀ) t₀ t₁ := by
  have hY := MatrixKSL.odeSolution_sField hS
  have e : (fun (_ : ℝ) (x : Matrix m n ℝ) =>
      -leftProj U₁ (rightProj V₀ (-g x))) = fun _ x =>
        (leftProj U₁ * rightProj V₀ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (g x) := by
    funext _ x
    simp only [map_neg, neg_neg]
    rfl
  rwa [e] at hY

/-- **Lemma 5.1 of arXiv 2502.03006 (loss along the PSI substeps).**  Let `∇ℓ = g` be Lipschitz
(Assumption A2) and let `(K, S, L)` be one step of PSI, Eq. (3.3) of the paper:
`K' = -∇ℓ(K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, `K(t₁) = U₁ Ŝ₁`; `Ṡ = U₁ᵀ ∇ℓ(U₁ S V₀ᵀ) V₀`,
`S(t₀) = Ŝ₁`; `L' = -∇ℓ(U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S(t₁)ᵀ`
(the library's `MatrixKSL.IsStep` for `F = -∇ℓ`).  Then

`ℓ(U₁ L(t₁)ᵀ) ≤ ℓ(U₀ S₀ V₀ᵀ) - α_K² h + α_S² h - α_L² h`,

with `α_K`, `α_S`, `α_L` the paper's minima and maximum along the trajectories (`alphaK`, `alphaS`,
`alphaL`).  No difference from the paper. -/
theorem psi_loss_le (hs : MatrixKSL.IsStep (fun _ Y => -g Y) t₀ t₁ U₀ S₀ V₀ U₁ Ŝ₁ K S Lf)
    (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) :
    ℓ (U₁ * (Lf t₁)ᵀ) ≤ ℓ (U₀ * S₀ * V₀ᵀ) - alphaK g V₀ K t₀ t₁ ^ 2 * h
      + alphaS g U₁ V₀ S t₀ t₁ ^ 2 * h - alphaL g U₁ Lf t₀ t₁ ^ 2 * h := by
  have hle : t₀ ≤ t₁ := by linarith
  have hgc : Continuous g := continuous_of_lipschitz hg
  have h1 := loss_kStep_le hℓ hs.orthV₀ hs.kSol ht₁ hh
  have h3 := loss_lStep_le hℓ hs.orthU₁ hs.lSol ht₁ hh
  have hYS := odeSolution_sStep hs.sSol
  have hcont : ContinuousOn (fun s => ‖U₁ᵀ * g (U₁ * S s * V₀ᵀ) * V₀‖) (Icc t₀ t₁) := by
    have : ContinuousOn (fun s => U₁ * S s * V₀ᵀ) (Icc t₀ t₁) := hYS.cont
    have h' : ContinuousOn (fun s => g (U₁ * S s * V₀ᵀ)) (Icc t₀ t₁) :=
      hgc.comp_continuousOn this
    have h'' : ContinuousOn (fun s => U₁ᵀ * g (U₁ * S s * V₀ᵀ) * V₀) (Icc t₀ t₁) :=
      ((Frobenius.rightMulCLM V₀).comp (Frobenius.leftMulCLM U₁ᵀ)).continuous.comp_continuousOn h'
    exact h''.norm
  have h2 := loss_le_of_ascent hℓ (isOrthProj_leftProj_mul_rightProj hs.orthU₁ hs.orthV₀) hYS
    (α := alphaS g U₁ V₀ S t₀ t₁) (fun t ht => by
      refine (congrArg (· ^ 2) (norm_leftProj_rightProj_eq hs.orthU₁ hs.orthV₀ _)).le.trans ?_
      exact sq_le_sSup_image (f := fun s => ‖U₁ᵀ * g (U₁ * S s * V₀ᵀ) * V₀‖)
        (fun _ => norm_nonneg _) hcont (Ico_subset_Icc_self ht)) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hlen] at h2
  have e1 : K t₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ := by rw [hs.kStart]
  have e2 : U₁ * S t₀ * V₀ᵀ = K t₁ * V₀ᵀ := by rw [hs.sStart, hs.kQR]
  have e3 : U₁ * (Lf t₀)ᵀ = U₁ * S t₁ * V₀ᵀ := by
    rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  linarith

/-- **The backward S-step can increase the loss** (Lemma 5.1 of arXiv 2502.03006, remark after
the bound): along the S-step, `ℓ(Y_S(t₁)) ≥ ℓ(Y_S(t₀)) + h β²` for every lower bound
`β ≤ ‖U₁ᵀ ∇ℓ(Y_S(s)) V₀‖` on `[t₀, t₁)`; the loss strictly increases as soon as `β ≠ 0`, `h > 0`. -/
theorem psi_sStep_loss_ge (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x)
    (hS : ODESolution (MatrixKSL.sField U₁ V₀ fun _ Y => -g Y) S t₀ t₁) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {β : ℝ} (hβ : 0 ≤ β)
    (hβs : ∀ s ∈ Ico t₀ t₁, β ≤ ‖U₁ᵀ * g (U₁ * S s * V₀ᵀ) * V₀‖) :
    ℓ (U₁ * S t₀ * V₀ᵀ) + β ^ 2 * h ≤ ℓ (U₁ * S t₁ * V₀ᵀ) := by
  have hle : t₀ ≤ t₁ := by linarith
  have h2 := le_loss_of_ascent hℓ (isOrthProj_leftProj_mul_rightProj hU₁ hV₀)
    (odeSolution_sStep hS) (α := β) (fun t ht => by
      refine le_trans ?_ (congrArg (· ^ 2) (norm_leftProj_rightProj_eq hU₁ hV₀ _)).ge
      exact pow_le_pow_left₀ hβ (hβs t ht) 2) t₁ ⟨hle, le_rfl⟩
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rwa [hlen] at h2

/-- The backward S-step strictly increases the loss in an example (Lemma 5.1 of arXiv 2502.03006,
remark): for `ℓ(Y) = ⟪1, Y⟫` on `1 × 1` matrices, `∇ℓ ≡ 1`, `U₁ = V₀ = 1` and `S(t) = t`, the loss
increases by at least `1` on `[0, 1]`. -/
example : ∃ (g : Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ)
    (ℓ : Matrix (Fin 1) (Fin 1) ℝ → ℝ) (S : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    (∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) ∧
      ODESolution (MatrixKSL.sField 1 1 fun _ Y => -g Y) S 0 1 ∧
      ℓ (1 * S 0 * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) <
        ℓ (1 * S 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) := by
  have hS : ODESolution (MatrixKSL.sField (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
      fun _ _ => -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun t => 0 + (t - 0) • 1) 0 1 := by
    have h := MatrixBUG.odeSolution_affine (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 1
    have e : (fun (_ : ℝ) (_ : Matrix (Fin 1) (Fin 1) ℝ) => (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        MatrixKSL.sField (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
          fun _ _ => -(1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      funext t Z
      simp [MatrixKSL.sField]
    rwa [e] at h
  have hn : ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    rw [Frobenius.norm_def]
    simp
  have hℓ : ∀ _x : Matrix (Fin 1) (Fin 1) ℝ,
      HasFDerivAt (fun Z : Matrix (Fin 1) (Fin 1) ℝ => ⟪(1 : Matrix (Fin 1) (Fin 1) ℝ), Z⟫)
        (innerSL ℝ (1 : Matrix (Fin 1) (Fin 1) ℝ)) _x :=
    fun _ => (innerSL ℝ (1 : Matrix (Fin 1) (Fin 1) ℝ)).hasFDerivAt
  refine ⟨fun _ => 1, fun Z => ⟪(1 : Matrix (Fin 1) (Fin 1) ℝ), Z⟫, _, hℓ, hS, ?_⟩
  have h := psi_sStep_loss_ge (g := fun _ => 1) (U₁ := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (V₀ := 1) (by simp) (by simp) hℓ hS (h := 1) (by norm_num) zero_le_one zero_le_one
    (fun s _ => by simpa using hn.ge)
  norm_num at h ⊢

end Loss

/-! ### Backward-corrected PSI -/

section BcPsi

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- One step of **backward-corrected PSI**, Eq. (3.4) of arXiv 2502.03006, for the gradient
`g = ∇ℓ`, from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`:

* K-step `K' = -∇ℓ(K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and QR factorization `K(t₁) = U₁ R₁`;
* the backward S-step is replaced by the projection `S̄₁ = U₁ᵀ U₀ S₀`;
* L-step `L' = -∇ℓ(U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S̄₁ᵀ`.

The result is `Ȳ₁ = U₁ L(t₁)ᵀ`.  `R₁` need not be invertible. -/
structure IsBcPsiStep (g : Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (K : ℝ → Matrix m (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ) (R₁ : Matrix (Fin r) (Fin r) ℝ)
    (Lf : ℝ → Matrix n (Fin r) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = -∇ℓ(K V₀ᵀ) V₀`. -/
  kSol : ODESolution (MatrixKSL.kField V₀ fun _ Y => -g Y) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  orthU₁ : U₁ᵀ * U₁ = 1
  /-- QR factorization of the K-step result. -/
  kQR : K t₁ = U₁ * R₁
  /-- L-step `L' = -∇ℓ(U₁ Lᵀ)ᵀ U₁`. -/
  lSol : ODESolution (MatrixKSL.lField U₁ fun _ Y => -g Y) Lf t₀ t₁
  /-- `L(t₀) = V₀ S̄₁ᵀ` with `S̄₁ = U₁ᵀ U₀ S₀`. -/
  lStart : Lf t₀ = V₀ * (U₁ᵀ * U₀ * S₀)ᵀ

variable {g : Matrix m n ℝ → Matrix m n ℝ} {ℓ : Matrix m n ℝ → ℝ} {c B ε t₀ t₁ h : ℝ}
  {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ R₁ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}

/-- The L-step of bc-PSI starts at the projection `U₁ U₁ᵀ Y₀` of `Y₀`. -/
lemma IsBcPsiStep.yL_start (hs : IsBcPsiStep g t₀ t₁ U₀ S₀ V₀ K U₁ R₁ Lf) :
    U₁ * (Lf t₀)ᵀ = leftProj U₁ (U₀ * S₀ * V₀ᵀ) := by
  rw [hs.lStart, leftProj_apply]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Lemma 5.4 of arXiv 2502.03006 (loss along bc-PSI).**  Under A2 (`∇ℓ` is `c`-Lipschitz) and
A3 (`‖∇ℓ‖ ≤ B`),

`ℓ(Y(t₁)) ≤ ℓ(Y₀) + B ‖(I - U₁U₁ᵀ) Y₀‖ + (c/2) ‖(I - U₁U₁ᵀ) Y₀‖² - h α_L²`,

with `Y(t₁) = U₁ L(t₁)ᵀ`, `Y₀ = U₀ S₀ V₀ᵀ` and `α_L = min_s ‖∇ℓ(Y_L(s))ᵀ U₁‖`.  No difference
from the paper.  (The library's `Novel.OpSB64.loss_bcPsiStep_le` is a different statement: it
concerns the explicit Euler step and shows that the positive terms are in fact a descent term.) -/
theorem IsBcPsiStep.loss_le (hs : IsBcPsiStep g t₀ t₁ U₀ S₀ V₀ K U₁ R₁ Lf)
    (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖)
    (hB : ∀ x, ‖g x‖ ≤ B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) :
    ℓ (U₁ * (Lf t₁)ᵀ) ≤ ℓ (U₀ * S₀ * V₀ᵀ) + B * ‖(1 - U₁ * U₁ᵀ) * (U₀ * S₀ * V₀ᵀ)‖
      + c / 2 * ‖(1 - U₁ * U₁ᵀ) * (U₀ * S₀ * V₀ᵀ)‖ ^ 2 - h * alphaL g U₁ Lf t₀ t₁ ^ 2 := by
  have h1 := loss_lStep_le hℓ hs.orthU₁ hs.lSol ht₁ hh
  rw [hs.yL_start] at h1
  set Y₀ := U₀ * S₀ * V₀ᵀ with hY₀
  have h2 := descent_lemma hℓ hg Y₀ (leftProj U₁ Y₀)
  have hd : leftProj U₁ Y₀ - Y₀ = -((1 - U₁ * U₁ᵀ) * Y₀) := by
    rw [leftProj_apply, Matrix.sub_mul, Matrix.one_mul, neg_sub]
  have h3 : ⟪g Y₀, leftProj U₁ Y₀ - Y₀⟫ ≤ B * ‖(1 - U₁ * U₁ᵀ) * Y₀‖ := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hd, norm_neg]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have h4 : ‖leftProj U₁ Y₀ - Y₀‖ = ‖(1 - U₁ * U₁ᵀ) * Y₀‖ := by rw [hd, norm_neg]
  rw [h4] at h2
  linarith

/-- **Robust local error of bc-PSI** (arXiv 2502.03006, proof of Theorem 5.3).  Under A2, A3, A4,
for the exact gradient flow `W' = -∇ℓ(W)`, `W(t₀) = Y₀`:

`‖W(t₁) - Ȳ₁‖ ≤ (e^{c h} - 1) (B h + ϑ) + ϑ`, `ϑ = h (4 c B h + ε)`,

with no dependence on singular values.  The paper bounds the difference to the PSI step and
quotes Kieri–Lubich–Walach for PSI.  This proof is direct: the capture lemma `kstep_capture`
for `U₁`, then `galerkin_step_error` for the L-step `YL' = -P₁ ∇ℓ(YL)` from `P₁ Y₀`. -/
theorem IsBcPsiStep.local_error (hs : IsBcPsiStep g t₀ t₁ U₀ S₀ V₀ K U₁ R₁ Lf)
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hB : ∀ x, ‖g x‖ ≤ B)
    (hA4 : ResidualBound g r ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {W : ℝ → Matrix m n ℝ}
    (hW : ODESolution (fun _ x => -g x) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖W t₁ - U₁ * (Lf t₁)ᵀ‖ ≤ (Real.exp (c * h) - 1) * (B * h + h * (4 * c * B * h + ε))
      + h * (4 * c * B * h + ε) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) c := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hP₁ := isOrthProj_leftProj (n := n) hs.orthU₁
  have hQ₀ := isOrthProj_rightProj (m := m) hs.orthV₀
  have hK := MatrixKSL.odeSolution_kField hs.kSol
  have hcap : leftProj U₁ (K t₁ * V₀ᵀ) = K t₁ * V₀ᵀ := by
    rw [hs.kQR, Matrix.mul_assoc]
    exact leftProj_mul_left hs.orthU₁ _
  have hKt : U₁ * U₁ᵀ * K t₁ = K t₁ := MatrixBUG.kCap_of_qr hs.orthU₁ hs.kQR
  have hUU : U₁ * U₁ᵀ * U₁ = U₁ := by rw [Matrix.mul_assoc, hs.orthU₁, Matrix.mul_one]
  have hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj U₁) ((1 - rightProj V₀)
      ((fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) t (K t₁ * V₀ᵀ)))‖ ≤ ε := fun t _ =>
    MatrixBUG.kNormal_le (hA4.factoredNormalBound hg hc) hs.orthU₁ hs.orthU₁ hUU hKt hs.orthV₀ t
  have hcapW := kstep_capture hF hc hBF hP₁ hQ₀ ht₁ hh hW hK
    (by rw [hs.kStart, hW₀]) hcap hε
  have hθ : ‖W t₁ - leftProj U₁ (W t₁)‖ ≤ h * (4 * c * B * h + ε) := by
    simpa using hcapW
  have hgal := galerkin_step_error hP₁ hF hc hBF ht₁ hh hW (MatrixKSL.odeSolution_lField hs.lSol)
    (by rw [hs.yL_start, hW₀]) hθ
  rw [norm_sub_rev]
  exact hgal

/-- **Robust local error of bc-PSI, `O`-form** (arXiv 2502.03006, proof of Theorem 5.3): for
`0 ≤ h ≤ H`, `‖W(t₁) - Ȳ₁‖ ≤ h (c₁ ε + c₂ h)` with the library's constants
`c₁ = bugC₁ c H`, `c₂ = bugC₂ c B H`, which depend only on `c`, `B`, `H`. -/
theorem IsBcPsiStep.local_error_le (hs : IsBcPsiStep g t₀ t₁ U₀ S₀ V₀ K U₁ R₁ Lf)
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hB : ∀ x, ‖g x‖ ≤ B)
    (hA4 : ResidualBound g r ε) (hε₀ : 0 ≤ ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ}
    (hhH : h ≤ H) {W : ℝ → Matrix m n ℝ} (hW : ODESolution (fun _ x => -g x) W t₀ t₁)
    (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖W t₁ - U₁ * (Lf t₁)ᵀ‖ ≤ h * (bugC₁ c H * ε + bugC₂ c B H * h) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 := hs.local_error hg hc hB hA4 ht₁ hh hW hW₀
  have h2 := bug_bound_le hc hB0 hε₀ hh hhH
  have hθ : 0 ≤ h * (4 * c * B * h + ε) := by positivity
  have hexp : 0 ≤ Real.exp (c * h) - 1 := by
    have := Real.add_one_le_exp (c * h)
    have : 0 ≤ c * h := mul_nonneg hc hh
    linarith
  have h3 : (Real.exp (c * h) - 1) * (B * h + h * (4 * c * B * h + ε)) ≤
      (Real.exp (c * h) - 1) * (B * h + 2 * (h * (4 * c * B * h + ε))) :=
    mul_le_mul_of_nonneg_left (by linarith) hexp
  linarith

/-- **Theorem 5.3 of arXiv 2502.03006 (robust error of bc-PSI).**  Assume A1
(`‖Y₀ - W₀‖ ≤ δ`), A2, A3, A4, and run bc-PSI on the grid `tⱼ = t₀ + j h`, `0 ≤ h ≤ H`, with the
QR factorizations `L(tⱼ₊₁) = Vⱼ₊₁ Sⱼ₊₁ᵀ`, so that `Ȳⱼ = Uⱼ Sⱼ Vⱼᵀ`.  Let `W' = -∇ℓ(W)`.  Then
for `j h ≤ T`

`‖W(tⱼ) - Ȳⱼ‖ ≤ c₁ h + c₂ ε + c₃ δ`

with `c₁ = T e^{c T} bugC₂ c B H`, `c₂ = T e^{c T} bugC₁ c H`, `c₃ = e^{c T}`, which depend only
on the Lipschitz constant, `B`, `T` and `H`, not on singular values.  Differences from the paper:
the constants are explicit, and the proof is direct (it does not pass through PSI).  The
hypothesis `ε ≥ 0` is automatic for `N ≥ 1`. -/
theorem bcPsi_global_error (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c)
    (hB : ∀ x, ‖g x‖ ≤ B) (hA4 : ResidualBound g r ε) (hε₀ : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h)
    (hhH : h ≤ H) {N : ℕ} {W : ℝ → Matrix m n ℝ}
    (hW : ODESolution (fun _ x => -g x) W t₀ (t₀ + N * h))
    {U : ℕ → Matrix m (Fin r) ℝ} {Sm : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → ℝ → Matrix m (Fin r) ℝ}
    {R : ℕ → Matrix (Fin r) (Fin r) ℝ} {Lf : ℕ → ℝ → Matrix n (Fin r) ℝ}
    (hstep : ∀ j < N, IsBcPsiStep g (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (Sm j) (V j) (K j)
      (U (j + 1)) (R j) (Lf j))
    (hnext : ∀ j < N, Lf j (t₀ + (j + 1) * h) = V (j + 1) * (Sm (j + 1))ᵀ) {δ T : ℝ}
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - W t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T →
      ‖W (t₀ + j * h) - U j * Sm j * (V j)ᵀ‖ ≤ T * Real.exp (c * T) * bugC₂ c B H * h
        + T * Real.exp (c * T) * bugC₁ c H * ε + Real.exp (c * T) * δ := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) c := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hB0 : 0 ≤ B := hBF.nonneg
  have hH : 0 ≤ H := hh.trans hhH
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily hF hBF (fun _ => continuous_const) (t₀ := t₀) hh
    (fun j => U j * Sm j * (V j)ᵀ)
  have hg0 : 0 ≤ bugC₁ c H * ε + bugC₂ c B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hc hH) hε₀) (mul_nonneg (bugC₂_nonneg hc hB0 hH) hh)
  have hloc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * (bugC₁ c H * ε + bugC₂ c B H * h) := by
    intro j hj
    have h1 := (hstep j hj).local_error_le hg hc hB hA4 hε₀ (by ring) hh hhH (hΦ j).1 (hΦ j).2
    rw [hnext j hj, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h1
    rwa [norm_sub_rev]
  intro j hj hT
  have h2 := lady_windermere_of_le (Y := fun j => U j * Sm j * (V j)ᵀ) hF hc hh hW
    (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) hg0 hloc j hj hT
  have hT0 : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg j) hh).trans hT
  have hE := Real.exp_pos (c * T)
  have h3 : Real.exp (c * T) * (‖U 0 * Sm 0 * (V 0)ᵀ - W t₀‖
      + T * (bugC₁ c H * ε + bugC₂ c B H * h)) ≤
      Real.exp (c * T) * (δ + T * (bugC₁ c H * ε + bugC₂ c B H * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) hE.le
  rw [norm_sub_rev]
  refine h2.trans (h3.trans (le_of_eq ?_))
  ring

/-- **The steps of bc-PSI exist.**  For a Lipschitz, bounded gradient, orthonormal `U₀`, `V₀`,
any `S₀`, and `r ≤ m`, `r ≤ n`, there is a complete bc-PSI step, including the QR factorization
`L(t₁) = V₁ S₁ᵀ` that starts the next one.  So the hypotheses of `bcPsi_global_error` hold for
every such gradient. -/
theorem exists_isBcPsiStep (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B)
    (h01 : t₀ ≤ t₁) (S₀ : Matrix (Fin r) (Fin r) ℝ) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hrm : r ≤ Fintype.card m) (hrn : r ≤ Fintype.card n) :
    ∃ (K : ℝ → Matrix m (Fin r) ℝ) (U₁ : Matrix m (Fin r) ℝ) (R₁ : Matrix (Fin r) (Fin r) ℝ)
      (Lf : ℝ → Matrix n (Fin r) ℝ) (V₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix (Fin r) (Fin r) ℝ),
      IsBcPsiStep g t₀ t₁ U₀ S₀ V₀ K U₁ R₁ Lf ∧ V₁ᵀ * V₁ = 1 ∧ Lf t₁ = V₁ * S₁ᵀ := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) c := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hcont : ∀ Y : Matrix m n ℝ, Continuous fun _ : ℝ => -g Y := fun _ => continuous_const
  obtain ⟨K, hK, hK₀⟩ := MatrixBUG.exists_odeSolution_conj hF hBF hcont
    (Frobenius.rightMulCLM V₀ᵀ) (Frobenius.rightMulCLM V₀)
    (f := MatrixKSL.kField V₀ fun _ Y => -g Y) (fun _ _ => rfl) h01 (U₀ * S₀)
  obtain ⟨U₁, hU₁, hcap⟩ := MatrixBUG.exists_qr hrm (K t₁)
  obtain ⟨Lf, hL, hL₀⟩ := MatrixBUG.exists_odeSolution_conj hF hBF hcont
    ((Frobenius.leftMulCLM U₁).comp Frobenius.transposeCLM)
    ((Frobenius.rightMulCLM U₁).comp Frobenius.transposeCLM)
    (f := MatrixKSL.lField U₁ fun _ Y => -g Y) (fun _ _ => rfl) h01 (V₀ * (U₁ᵀ * U₀ * S₀)ᵀ)
  obtain ⟨V₁, hV₁, hcapL⟩ := MatrixBUG.exists_qr hrn (Lf t₁)
  refine ⟨K, U₁, U₁ᵀ * K t₁, Lf, V₁, (V₁ᵀ * Lf t₁)ᵀ, ⟨hU₀, hV₀, hK, hK₀, hU₁, ?_, hL, hL₀⟩, hV₁, ?_⟩
  · rw [← Matrix.mul_assoc, hcap]
  · rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, hcapL]

end BcPsi

/-! ### Augmented backward-corrected PSI -/

section AbcPsi

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k : ℕ}

/-- One step of **augmented backward-corrected PSI**, Eq. (4.1) of arXiv 2502.03006, before
truncation, for the gradient `g = ∇ℓ`, from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁`:

* K-step `K' = -∇ℓ(K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`;
* `Û₁ = ortho([U₀, K(t₁)])`, encoded by `Û₁ᵀ Û₁ = I`, `Û₁ Û₁ᵀ U₀ = U₀`, `Û₁ Û₁ᵀ K(t₁) = K(t₁)`;
  any number `k` of columns is allowed, the paper's choice being `k = 2 r`;
* `S̄₁ = Û₁ᵀ U₀ S₀` and the L-step `L' = -∇ℓ(Û₁ Lᵀ)ᵀ Û₁`, `L(t₀) = V₀ S̄₁ᵀ`.

The untruncated result is `Ŷ₁ = Û₁ L(t₁)ᵀ`. -/
structure IsAbcPsiStep (g : Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (K : ℝ → Matrix m (Fin r) ℝ) (Uh : Matrix m (Fin k) ℝ) (Lf : ℝ → Matrix n (Fin k) ℝ) :
    Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  /-- K-step `K' = -∇ℓ(K V₀ᵀ) V₀`. -/
  kSol : ODESolution (MatrixKSL.kField V₀ fun _ Y => -g Y) K t₀ t₁
  kStart : K t₀ = U₀ * S₀
  orthUh : Uhᵀ * Uh = 1
  /-- The augmented basis contains the old basis. -/
  capU₀ : Uh * Uhᵀ * U₀ = U₀
  /-- The augmented basis contains the K-step result. -/
  capK : Uh * Uhᵀ * K t₁ = K t₁
  /-- L-step `L' = -∇ℓ(Û₁ Lᵀ)ᵀ Û₁`. -/
  lSol : ODESolution (MatrixKSL.lField Uh fun _ Y => -g Y) Lf t₀ t₁
  /-- `L(t₀) = V₀ S̄₁ᵀ` with `S̄₁ = Û₁ᵀ U₀ S₀`. -/
  lStart : Lf t₀ = V₀ * (Uhᵀ * U₀ * S₀)ᵀ

/-- A run of abc-PSI on the grid `tⱼ = t₀ + j h` with rank-adaptive truncation: `Yⱼ = Uⱼ Sⱼ Vⱼᵀ`
has rank parameter `rⱼ`, step `j` (`IsAbcPsiStep`) has an augmented basis with `ρⱼ` columns and
result `Ŷⱼ₊₁`, and the truncation satisfies `‖Ŷⱼ₊₁ - Yⱼ₊₁‖ ≤ ϑ` (arXiv 2502.03006, Sec. 5.5). -/
structure IsAbcPsiRun (g : Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ) (N : ℕ) (ϑ : ℝ)
    {r ρ : ℕ → ℕ} (U : (j : ℕ) → Matrix m (Fin (r j)) ℝ)
    (S : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ) (V : (j : ℕ) → Matrix n (Fin (r j)) ℝ)
    (K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ) (Uh : (j : ℕ) → Matrix m (Fin (ρ j)) ℝ)
    (Lf : (j : ℕ) → ℝ → Matrix n (Fin (ρ j)) ℝ) : Prop where
  step : ∀ j < N, IsAbcPsiStep g (t₀ + j * h) (t₀ + (j + 1) * h) (U j) (S j) (V j) (K j) (Uh j)
    (Lf j)
  trunc : ∀ j < N, ‖Uh j * (Lf j (t₀ + (j + 1) * h))ᵀ - U (j + 1) * S (j + 1) * (V (j + 1))ᵀ‖ ≤ ϑ

variable {g : Matrix m n ℝ → Matrix m n ℝ} {ℓ : Matrix m n ℝ → ℝ} {c B ε ϑ t₀ t₁ h : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Uh : Matrix m (Fin k) ℝ} {Lf : ℝ → Matrix n (Fin k) ℝ}

/-- The augmented projector fixes `Y₀`: `(P¹ - I) Y₀ = 0`. -/
lemma IsAbcPsiStep.proj_Y₀ (hs : IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf) :
    leftProj Uh (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
  rw [leftProj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hs.capU₀]

/-- The L-step of abc-PSI starts exactly at `Y₀` (no initial projection error). -/
lemma IsAbcPsiStep.yL_start (hs : IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf) :
    Uh * (Lf t₀)ᵀ = U₀ * S₀ * V₀ᵀ := by
  have e : Uh * (Lf t₀)ᵀ = leftProj Uh (U₀ * S₀ * V₀ᵀ) := by
    rw [hs.lStart, leftProj_apply]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, hs.proj_Y₀]

/-- **The bound of Lemma 5.4 for abc-PSI** (arXiv 2502.03006, discussion after Lemma 5.4): both
positive terms vanish, because the augmented basis contains `U₀`, and
`ℓ(Ŷ₁) ≤ ℓ(Y₀) - h α_L²`. -/
theorem IsAbcPsiStep.loss_le (hs : IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf)
    (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) :
    ℓ (Uh * (Lf t₁)ᵀ) ≤ ℓ (U₀ * S₀ * V₀ᵀ) - h * alphaL g Uh Lf t₀ t₁ ^ 2 := by
  have h1 := loss_lStep_le hℓ hs.orthUh hs.lSol ht₁ hh
  rw [hs.yL_start] at h1
  linarith

/-- **Local error of abc-PSI before truncation** (arXiv 2502.03006, proof of Theorem 5.6): under
A2, A3, A4 and for the gradient flow `W' = -∇ℓ(W)`, `W(t₀) = Y₀`,

`‖Ŷ₁ - W(t₁)‖ ≤ h ε + 3 c B h²`,

where `c` is the paper's `c_l`.  No difference from the paper. -/
theorem IsAbcPsiStep.local_error (hs : IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf)
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hB : ∀ x, ‖g x‖ ≤ B)
    (hA4 : ResidualBound g r ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {W : ℝ → Matrix m n ℝ}
    (hW : ODESolution (fun _ x => -g x) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖Uh * (Lf t₁)ᵀ - W t₁‖ ≤ h * ε + 3 * c * B * h ^ 2 := by
  refine augmented_local_error hg hc hB (isOrthProj_leftProj hs.orthUh)
    (isOrthProj_rightProj hs.orthV₀) ht₁ hh hW hW₀ (YK := fun t => K t * V₀ᵀ)
    (MatrixKSL.odeSolution_kField hs.kSol) (by simp only [hs.kStart]) hs.proj_Y₀ ?_
    (YL := fun t => Uh * (Lf t)ᵀ) (MatrixKSL.odeSolution_lField hs.lSol) hs.yL_start ?_
  · simp only [leftProj_apply]
    rw [← Matrix.mul_assoc, hs.capK]
  · rw [one_sub_leftProj_one_sub_rightProj_apply]
    exact (MatrixBUG.norm_normal_le_of_left hs.orthUh hs.capU₀ V₀ _).trans
      (hA4.normal_le hg hc hs.orthU₀ hs.orthV₀ S₀)

/-- **Local error of abc-PSI** (arXiv 2502.03006, proof of Theorem 5.6): after a truncation
`‖Ŷ₁ - Y₁‖ ≤ ϑ`, `‖Y₁ - W(t₁)‖ ≤ h ε + 3 c B h² + ϑ`.  The paper writes `ϑ/h` for the truncation
term in its proof and `ϑ` in its Section 5.5; `ϑ` is the correct local term, and `ϑ/h` appears in
the global bound `abcPsi_global_error_le`. -/
theorem IsAbcPsiStep.local_error_truncated (hs : IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf)
    (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c) (hB : ∀ x, ‖g x‖ ≤ B)
    (hA4 : ResidualBound g r ε) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {W : ℝ → Matrix m n ℝ}
    (hW : ODESolution (fun _ x => -g x) W t₀ t₁) (hW₀ : W t₀ = U₀ * S₀ * V₀ᵀ)
    {Y₁ : Matrix m n ℝ} (htr : ‖Uh * (Lf t₁)ᵀ - Y₁‖ ≤ ϑ) :
    ‖Y₁ - W t₁‖ ≤ h * ε + 3 * c * B * h ^ 2 + ϑ := by
  have h1 := hs.local_error hg hc hB hA4 ht₁ hh hW hW₀
  have h2 := norm_sub_le_norm_sub_add_norm_sub Y₁ (Uh * (Lf t₁)ᵀ) (W t₁)
  have h3 : ‖Y₁ - Uh * (Lf t₁)ᵀ‖ ≤ ϑ := by rwa [norm_sub_rev]
  linarith

/-- **Theorem 5.6 of arXiv 2502.03006 (robust error of abc-PSI), explicit form.**  Assume A1, A2,
A3, A4 (at each rank used by the run, `ε ≥ 0`) and let `Y₀, Y₁, …` be a run of abc-PSI with
truncation tolerance `ϑ ≥ 0` (`IsAbcPsiRun`) on `tⱼ = t₀ + j h`.  For `j h ≤ T`

`‖Yⱼ - W(tⱼ)‖ ≤ e^{c T} (δ + T ε + 3 c B T h + j ϑ)`.

Differences from the paper are stated in `abcPsi_global_error_le`. -/
theorem abcPsi_global_error (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c)
    (hB : ∀ x, ‖g x‖ ≤ B) (hε₀ : 0 ≤ ε) (hϑ₀ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    {W : ℝ → Matrix m n ℝ} (hW : ODESolution (fun _ x => -g x) W t₀ (t₀ + N * h)) {r ρ : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {S : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Uh : (j : ℕ) → Matrix m (Fin (ρ j)) ℝ} {Lf : (j : ℕ) → ℝ → Matrix n (Fin (ρ j)) ℝ}
    (hrun : IsAbcPsiRun g t₀ h N ϑ U S V K Uh Lf) (hA4 : ∀ j < N, ResidualBound g (r j) ε)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - W t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T → ‖U j * S j * (V j)ᵀ - W (t₀ + j * h)‖ ≤
      Real.exp (c * T) * (δ + T * ε + 3 * c * B * T * h + j * ϑ) := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) c := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hB0 : 0 ≤ B := hBF.nonneg
  obtain ⟨Φ, hΦ⟩ := exists_exactFlowFamily hF hBF (fun _ => continuous_const) (t₀ := t₀) hh
    (fun j => U j * S j * (V j)ᵀ)
  have hloc : ∀ j < N, ‖U (j + 1) * S (j + 1) * (V (j + 1))ᵀ - Φ j (t₀ + (j + 1) * h)‖ ≤
      h * ε + 3 * c * B * h ^ 2 + ϑ := fun j hj =>
    (hrun.step j hj).local_error_truncated hg hc hB (hA4 j hj) (by ring) hh (hΦ j).1 (hΦ j).2
      (hrun.trunc j hj)
  intro j hj hT
  have h1 := lady_windermere (Y := fun j => U j * S j * (V j)ᵀ) hF hc hh hW
    (fun n _ => (hΦ n).1) (fun n _ => (hΦ n).2) hloc j hj
  have hnh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
  have hT0 : 0 ≤ T := hnh.trans hT
  have hexp : Real.exp (c * (j * h)) ≤ Real.exp (c * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hc)
  have hcB : 0 ≤ 3 * c * B * h := by positivity
  have hsum : ‖U 0 * S 0 * (V 0)ᵀ - W t₀‖ + j * (h * ε + 3 * c * B * h ^ 2 + ϑ) ≤
      δ + T * ε + 3 * c * B * T * h + j * ϑ := by
    have e : (j : ℝ) * (h * ε + 3 * c * B * h ^ 2 + ϑ) =
        (j * h) * ε + (j * h) * (3 * c * B * h) + j * ϑ := by ring
    have e2 : 3 * c * B * T * h = T * (3 * c * B * h) := by ring
    rw [e, e2]
    have := mul_le_mul_of_nonneg_right hT hε₀
    have := mul_le_mul_of_nonneg_right hT hcB
    linarith
  have hsum0 : 0 ≤ ‖U 0 * S 0 * (V 0)ᵀ - W t₀‖ + j * (h * ε + 3 * c * B * h ^ 2 + ϑ) := by
    positivity
  exact h1.trans (mul_le_mul hexp hsum hsum0 (Real.exp_pos _).le)

/-- **Theorem 5.6 of arXiv 2502.03006 (robust error of abc-PSI), final form.**  Under the
assumptions of `abcPsi_global_error` and `h > 0`,

`‖Yⱼ - W(tⱼ)‖ ≤ T e^{c T} ε + c₁ h + c₂ δ + T e^{c T} ϑ / h`

with `c₁ = 3 c B T e^{c T}` and `c₂ = e^{c T}`, independent of singular values.  The paper states
`ε + c₁ h + c₂ δ + ϑ / h`, with coefficient `1` on `ε` and on `ϑ / h`, and cites Lady Windermere's
fan for the global step.  That literal form is false: see `abcPsi_literal_bound_false`.  The
factor `T e^{c T}` above is what the fan gives; for `ε` it cannot be replaced by `1`.  Hypothesis
A4 is required at each rank `rⱼ` used by the run, since the paper's truncation changes the
rank. -/
theorem abcPsi_global_error_le (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hc : 0 ≤ c)
    (hB : ∀ x, ‖g x‖ ≤ B) (hε₀ : 0 ≤ ε) (hϑ₀ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 < h) {N : ℕ}
    {W : ℝ → Matrix m n ℝ} (hW : ODESolution (fun _ x => -g x) W t₀ (t₀ + N * h)) {r ρ : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {S : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Uh : (j : ℕ) → Matrix m (Fin (ρ j)) ℝ} {Lf : (j : ℕ) → ℝ → Matrix n (Fin (ρ j)) ℝ}
    (hrun : IsAbcPsiRun g t₀ h N ϑ U S V K Uh Lf) (hA4 : ∀ j < N, ResidualBound g (r j) ε)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - W t₀‖ ≤ δ) :
    ∀ j ≤ N, (j : ℝ) * h ≤ T → ‖U j * S j * (V j)ᵀ - W (t₀ + j * h)‖ ≤
      T * Real.exp (c * T) * ε + 3 * c * B * T * Real.exp (c * T) * h + Real.exp (c * T) * δ
        + T * Real.exp (c * T) * (ϑ / h) := by
  intro j hj hT
  have h1 := abcPsi_global_error hg hc hB hε₀ hϑ₀ hh.le hW hrun hA4 hδ j hj hT
  have hj' : (j : ℝ) * ϑ ≤ T * (ϑ / h) := by
    have : (j : ℝ) * ϑ = (j * h) * (ϑ / h) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hT (div_nonneg hϑ₀ hh.le)
  have hE := (Real.exp_pos (c * T)).le
  refine h1.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hj' hE
  nlinarith

/-- **The steps of abc-PSI exist.**  For a Lipschitz, bounded gradient, orthonormal `U₀`, `V₀`,
any `S₀`, and `2 r ≤ m`, there is a complete abc-PSI step with an augmented basis of `2 r`
columns.  Together with any truncation `‖Ŷ₁ - Y₁‖ ≤ ϑ`, this gives the runs of
`abcPsi_global_error`; `abcPsi_literal_bound_false` contains an explicit run. -/
theorem exists_isAbcPsiStep (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖) (hB : ∀ x, ‖g x‖ ≤ B)
    (h01 : t₀ ≤ t₁) (S₀ : Matrix (Fin r) (Fin r) ℝ) (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hrm : 2 * r ≤ Fintype.card m) :
    ∃ (K : ℝ → Matrix m (Fin r) ℝ) (Uh : Matrix m (Fin (2 * r)) ℝ)
      (Lf : ℝ → Matrix n (Fin (2 * r)) ℝ), IsAbcPsiStep g t₀ t₁ U₀ S₀ V₀ K Uh Lf := by
  have hF : IsLipschitzField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) c := fun _ x y => by
    rw [neg_sub_neg, norm_sub_rev]; exact hg x y
  have hBF : IsBoundedField (fun (_ : ℝ) (x : Matrix m n ℝ) => -g x) B := fun _ x => by
    rw [norm_neg]; exact hB x
  have hcont : ∀ Y : Matrix m n ℝ, Continuous fun _ : ℝ => -g Y := fun _ => continuous_const
  obtain ⟨K, hK, hK₀⟩ := MatrixBUG.exists_odeSolution_conj hF hBF hcont
    (Frobenius.rightMulCLM V₀ᵀ) (Frobenius.rightMulCLM V₀)
    (f := MatrixKSL.kField V₀ fun _ Y => -g Y) (fun _ _ => rfl) h01 (U₀ * S₀)
  obtain ⟨Uh, hUh, hcapK, hcapU⟩ := MatrixBUG.exists_aug_qr hrm (K t₁) U₀
  obtain ⟨Lf, hL, hL₀⟩ := MatrixBUG.exists_odeSolution_conj hF hBF hcont
    ((Frobenius.leftMulCLM Uh).comp Frobenius.transposeCLM)
    ((Frobenius.rightMulCLM Uh).comp Frobenius.transposeCLM)
    (f := MatrixKSL.lField Uh fun _ Y => -g Y) (fun _ _ => rfl) h01 (V₀ * (Uhᵀ * U₀ * S₀)ᵀ)
  exact ⟨K, Uh, Lf, hU₀, hV₀, hK, hK₀, hUh, hcapU, hcapK, hL, hL₀⟩

end AbcPsi

/-! ### The coefficient `1` in the paper's statement of Theorem 5.6 fails -/

section Counterexample

/-- The constant gradient `G = e₂ f₁ᵀ + e₃ f₂ᵀ` of the linear loss `ℓ(Y) = ⟪G, Y⟫` on `3 × 2`
matrices. -/
def exG : Matrix (Fin 3) (Fin 2) ℝ := !![0, 0; 1, 0; 0, 1]

/-- The gradient field `∇ℓ ≡ G`. -/
def exField (_ : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ := exG

/-- The right basis `V = f₁`, which does not change along the run. -/
def exV : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The augmented basis `Û = [e₁, e₂]`, which does not change along the run. -/
def exUh : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- The K-step trajectory `K(t) = e₁ - t e₂`. -/
def exK (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := !![1; -t; 0]

/-- The L-step trajectory `L(t) = f₁ (1, -t)`. -/
def exL (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -t; 0, 0]

/-- The norm `√(1 + t²)` of `K(t)`. -/
noncomputable def exNu (t : ℝ) : ℝ := √(1 + t ^ 2)

/-- The orthonormal factor of `K(t)`. -/
noncomputable def exU (t : ℝ) : Matrix (Fin 3) (Fin 1) ℝ := (exNu t)⁻¹ • exK t

/-- The coefficient of `K(t)`. -/
noncomputable def exS (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := exNu t • 1

/-- The gradient flow `W(t) = Y₀ - t G`, `Y₀ = e₁ f₁ᵀ`. -/
noncomputable def exW (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := exK 0 * exVᵀ + (t - 0) • -exG

/-- The norm `√(1 + t²)` is positive. -/
lemma exNu_pos (t : ℝ) : 0 < exNu t := Real.sqrt_pos.2 (by positivity)

/-- `(√(1 + t²))² = 1 + t²`. -/
lemma exNu_sq (t : ℝ) : exNu t ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)

/-- `V = f₁` is orthonormal. -/
lemma exV_orth : exVᵀ * exV = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [exV, Matrix.mul_apply]

/-- `Û = [e₁, e₂]` is orthonormal. -/
lemma exUh_orth : exUhᵀ * exUh = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [exUh, Matrix.mul_apply, Fin.sum_univ_three]

/-- The factor `K(t) / ‖K(t)‖` is orthonormal. -/
lemma exU_orth (t : ℝ) : (exU t)ᵀ * exU t = 1 := by
  have hK : (exK t)ᵀ * exK t = (exNu t ^ 2) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [exNu_sq]
    ext i j; fin_cases i; fin_cases j
    simp [exK, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hν := (exNu_pos t).ne'
  rw [exU, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hK, smul_smul, smul_smul]
  have e : (exNu t)⁻¹ * (exNu t)⁻¹ * exNu t ^ 2 = 1 := by field_simp
  rw [e, one_smul]

/-- `U S = K(t)`. -/
lemma exU_mul_exS (t : ℝ) : exU t * exS t = exK t := by
  have hν := (exNu_pos t).ne'
  rw [exU, exS, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hν,
    one_smul]

/-- `Û` contains `K(t)`. -/
lemma exUh_cap_K (t : ℝ) : exUh * exUhᵀ * exK t = exK t := by
  refine MatrixBUG.kCap_of_qr exUh_orth (R₁ := !![1; -t]) ?_
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [exUh, exK, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Û` contains `U = K(t) / ‖K(t)‖`. -/
lemma exUh_cap_U (t : ℝ) : exUh * exUhᵀ * exU t = exU t := by
  rw [exU, Matrix.mul_smul, exUh_cap_K]

/-- `K(t) = e₁ - t e₂` solves the K-step for `∇ℓ ≡ G`, `V = f₁`. -/
lemma odeSolution_exK (a b : ℝ) :
    ODESolution (MatrixKSL.kField exV fun _ Y => -exField Y) exK a b := by
  have h := MatrixBUG.odeSolution_affine (exK a) (!![0; -1; 0] : Matrix (Fin 3) (Fin 1) ℝ) a b
  have e1 : (fun t => exK a + (t - a) • (!![0; -1; 0] : Matrix (Fin 3) (Fin 1) ℝ)) = exK := by
    funext t
    ext i j; fin_cases i <;> fin_cases j <;> simp [exK]
    ring
  have e2 : (fun (_ : ℝ) (_ : Matrix (Fin 3) (Fin 1) ℝ) =>
      (!![0; -1; 0] : Matrix (Fin 3) (Fin 1) ℝ)) =
      MatrixKSL.kField exV fun _ Y => -exField Y := by
    funext t K
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [MatrixKSL.kField, exField, exG, exV, Matrix.mul_apply, Fin.sum_univ_two]
  rwa [e1, e2] at h

/-- `L(t) = f₁ (1, -t)` solves the L-step for `∇ℓ ≡ G`, `Û = [e₁, e₂]`. -/
lemma odeSolution_exL (a b : ℝ) :
    ODESolution (MatrixKSL.lField exUh fun _ Y => -exField Y) exL a b := by
  have h := MatrixBUG.odeSolution_affine (exL a) (!![0, -1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) a b
  have e1 : (fun t => exL a + (t - a) • (!![0, -1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) = exL := by
    funext t
    ext i j; fin_cases i <;> fin_cases j <;> simp [exL]
    ring
  have e2 : (fun (_ : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) =>
      (!![0, -1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) =
      MatrixKSL.lField exUh fun _ Y => -exField Y := by
    funext t L
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [MatrixKSL.lField, exField, exG, exUh, Matrix.mul_apply, Fin.sum_univ_three]
  rwa [e1, e2] at h

/-- From the point `(e₁ - a e₂) f₁ᵀ`, the trajectories above form an abc-PSI step. -/
lemma isAbcPsiStep_ex (a b : ℝ) :
    IsAbcPsiStep exField a b (exU a) (exS a) exV exK exUh exL where
  orthU₀ := exU_orth a
  orthV₀ := exV_orth
  kSol := odeSolution_exK a b
  kStart := (exU_mul_exS a).symm
  orthUh := exUh_orth
  capU₀ := exUh_cap_U a
  capK := exUh_cap_K b
  lSol := odeSolution_exL a b
  lStart := by
    rw [Matrix.mul_assoc, exU_mul_exS]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [exL, exV, exK, exUh, Matrix.mul_apply, Fin.sum_univ_three]

/-- The result of the step is `U S Vᵀ` at the new time, so no truncation is needed. -/
lemma exUh_mul_exL (t : ℝ) : exUh * (exL t)ᵀ = exU t * exS t * exVᵀ := by
  rw [exU_mul_exS]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [exL, exV, exK, exUh, Matrix.mul_apply, Fin.sum_univ_two]

/-- `‖G‖ ≤ 2`. -/
lemma norm_exG_le : ‖exG‖ ≤ 2 := by
  have h : ‖exG‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp [exG, Fin.sum_univ_two, Fin.sum_univ_three]
    norm_num
  nlinarith [norm_nonneg exG]

/-- The error at `T = 3` is exactly `3`. -/
lemma norm_error_ex : ‖exU 3 * exS 3 * exVᵀ - exW 3‖ = 3 := by
  have hY : ∀ t, exK t * exVᵀ = !![1, 0; -t, 0; 0, 0] := fun t => by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_one] <;> simp [exK, exV]
  have e : exU 3 * exS 3 * exVᵀ - exW 3 =
      (3 : ℝ) • (!![0, 0; 0, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ) := by
    rw [exU_mul_exS, exW, hY, hY]
    ext i j; fin_cases i <;> fin_cases j <;> simp [exG]
  have h1 : ‖(!![0, 0; 0, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)‖ = 1 := by
    rw [Frobenius.norm_def]
    simp [Fin.sum_univ_two, Fin.sum_univ_three]
  rw [e, norm_smul, h1]
  norm_num

/-- **The literal statement of Theorem 5.6 of arXiv 2502.03006 is false.**  The paper states
`‖Y(tₙ) - W(tₙ)‖ ≤ ε + c₁ h + c₂ δ + ϑ/h`.  Take the linear loss `ℓ(Y) = ⟪G, Y⟫` on `3 × 2`
matrices with `G = e₂ f₁ᵀ + e₃ f₂ᵀ`: A2 holds with `c_l = 1`, A3 with `B = 2` and A4 with `r = 1`,
`ε = 2`.  Start at `Y₀ = e₁ f₁ᵀ` (`δ = 0`) with `V = f₁`.  Then `K(t) = e₁ - t e₂`, so `U_j` and
`K(t_{j+1})` are independent for `h > 0` and `Û = [e₁, e₂]` is the orthonormal basis of their span,
with the paper's `2 r = 2` columns.  The result of each step is `(e₁ - t e₂) f₁ᵀ`, of rank one, so
no truncation is needed (`ϑ = 0`).  The component `e₃ f₂ᵀ` of `G` is never captured, and
`W(t) = Y₀ - t G`, so the error at `T = 3`, where `N h = 3`, is `3` (`norm_error_ex`).  The claimed
bound then reads `3 ≤ 2 + c₁ h`, which fails for small `h`, whatever `c₁`, `c₂` are.
Constants may depend on `T`, `c_l`, `B`, which are fixed here.  The coefficient of `ε` must grow
with `T`, as in `abcPsi_global_error_le`. -/
theorem abcPsi_literal_bound_false :
    (∀ Y, HasFDerivAt (fun Z : Matrix (Fin 3) (Fin 2) ℝ => ⟪exG, Z⟫) (innerSL ℝ (exField Y)) Y) ∧
    (∀ x y, ‖exField x - exField y‖ ≤ 1 * ‖x - y‖) ∧ (∀ x, ‖exField x‖ ≤ 2) ∧
    ResidualBound exField 1 2 ∧
    ∀ c₁ c₂ : ℝ, ∃ (N : ℕ) (h : ℝ), 0 < h ∧ (N : ℝ) * h = 3 ∧
      IsAbcPsiRun exField 0 h N 0 (r := fun _ => 1) (ρ := fun _ => 2)
        (fun j => exU (0 + j * h)) (fun j => exS (0 + j * h)) (fun _ => exV) (fun _ => exK)
        (fun _ => exUh) (fun _ => exL) ∧
      ODESolution (fun _ x => -exField x) exW 0 (0 + N * h) ∧
      ‖exU (0 + (0 : ℕ) * h) * exS (0 + (0 : ℕ) * h) * exVᵀ - exW 0‖ ≤ 0 ∧
      2 + c₁ * h + c₂ * 0 + 0 / h <
        ‖exU (0 + N * h) * exS (0 + N * h) * exVᵀ - exW (0 + N * h)‖ := by
  refine ⟨fun Y => (innerSL ℝ exG).hasFDerivAt, fun x y => ?_, fun x => norm_exG_le, ?_,
    fun c₁ c₂ => ?_⟩
  · simp only [exField, sub_self, norm_zero, one_mul]
    exact norm_nonneg _
  · intro U S V hU hV _
    exact ((isOrthProj_tangentProj hU hV).norm_sub_le _).trans norm_exG_le
  · obtain ⟨M, hM⟩ := exists_nat_gt (3 * c₁)
    set N : ℕ := M + 1 with hN
    have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
    have hMN : (M : ℝ) < N := by rw [hN]; push_cast; linarith
    have hNh : (N : ℝ) * (3 / N) = 3 := by field_simp
    refine ⟨N, 3 / N, by positivity, hNh, ⟨fun j _ => isAbcPsiStep_ex _ _, fun j _ => ?_⟩,
      MatrixBUG.odeSolution_affine (exK 0 * exVᵀ) (-exG) 0 _, ?_, ?_⟩
    · rw [exUh_mul_exL]
      have e : (0 : ℝ) + ((j + 1 : ℕ) : ℝ) * (3 / N) = 0 + ((j : ℝ) + 1) * (3 / N) := by
        push_cast; ring
      rw [e, sub_self, norm_zero]
    · have e : exU (0 + ((0 : ℕ) : ℝ) * (3 / N)) * exS (0 + ((0 : ℕ) : ℝ) * (3 / N)) * exVᵀ =
          exW 0 := by
        simp only [Nat.cast_zero, zero_mul, add_zero]
        rw [exU_mul_exS]
        simp [exW]
      rw [e, sub_self, norm_zero]
    · rw [zero_add, hNh, norm_error_ex]
      have h2 : c₁ * (3 / N) < 1 := by
        have : c₁ * (3 / N) = 3 * c₁ / N := by ring
        rw [this, div_lt_one hNpos]
        linarith
      simp only [mul_zero, zero_div, add_zero]
      linarith

end Counterexample

/-! ### Convergence of abc-PSI (Theorem 5.9, deterministic form) -/

section Euler

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r k : ℕ}

/-- The result `Ŷ₁ = Û L₁ᵀ` of one step of Algorithm 4.1 of arXiv 2502.03006 (abc-PSI with explicit
Euler for the L-step, before truncation): `S̄₁ = Ûᵀ U₀ S₀`, `L₀ = V₀ S̄₁ᵀ`,
`L₁ = L₀ - h ∇_L ℓ(Û L₀ᵀ) = L₀ - h ∇ℓ(Û L₀ᵀ)ᵀ Û`. -/
noncomputable def abcPsiEulerStep (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Uh : Matrix m (Fin k) ℝ) : Matrix m n ℝ :=
  Uh * (V₀ * (Uhᵀ * U₀ * S₀)ᵀ -
    h • ((g (Uh * (V₀ * (Uhᵀ * U₀ * S₀)ᵀ)ᵀ))ᵀ * Uh))ᵀ

/-- The augmented basis of Algorithm 4.1 of arXiv 2502.03006: `Û` is orthonormal and contains `U₀`
and the K-step result `K₁ = U₀ S₀ - h ∇_K ℓ(U₀ S₀ V₀ᵀ) = U₀ S₀ - h ∇ℓ(Y₀) V₀`. -/
structure IsAbcPsiEulerBasis (g : Matrix m n ℝ → Matrix m n ℝ) (h : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Uh : Matrix m (Fin k) ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  orthUh : Uhᵀ * Uh = 1
  capU₀ : Uh * Uhᵀ * U₀ = U₀
  capK : Uh * Uhᵀ * (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) =
    U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)

variable {g : Matrix m n ℝ → Matrix m n ℝ} {h : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m (Fin k) ℝ}

/-- The identity `Ŷ₁ = Y₀ - h P_Û ∇ℓ(Y₀)` used in the proof of Theorem 5.8 of
arXiv 2502.03006: one step of Algorithm 4.1 is a projected gradient step. -/
theorem IsAbcPsiEulerBasis.step_eq (hs : IsAbcPsiEulerBasis g h U₀ S₀ V₀ Uh) :
    abcPsiEulerStep g h U₀ S₀ V₀ Uh = projGradStep (leftProj Uh) g h (U₀ * S₀ * V₀ᵀ) := by
  have hY : Uh * (V₀ * (Uhᵀ * U₀ * S₀)ᵀ)ᵀ = U₀ * S₀ * V₀ᵀ := by
    have e : Uh * (V₀ * (Uhᵀ * U₀ * S₀)ᵀ)ᵀ = Uh * Uhᵀ * U₀ * S₀ * V₀ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [e, hs.capU₀]
  unfold abcPsiEulerStep projGradStep
  rw [hY, Matrix.transpose_sub, Matrix.mul_sub, hY, Matrix.transpose_smul, Matrix.mul_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, leftProj_apply, Matrix.mul_assoc Uh Uhᵀ]

/-- The K-step augmentation captures the Riemannian gradient: for `h ≠ 0`, the projector
`P_Û` of Algorithm 4.1 fixes `P(Y₀) ∇ℓ(Y₀)`.  This replaces the false identity
`P_Û ∇ℓ = P(Y) ∇ℓ` in the proof of Theorem 5.9 of arXiv 2502.03006, see
`FactorizedDynamics.exists_leftProj_ne_tangentProj_of_capture`. -/
theorem IsAbcPsiEulerBasis.absorbs (hs : IsAbcPsiEulerBasis g h U₀ S₀ V₀ Uh) (hh : h ≠ 0) :
    leftProj Uh (tangentProj U₀ V₀ (g (U₀ * S₀ * V₀ᵀ))) = tangentProj U₀ V₀ (g (U₀ * S₀ * V₀ᵀ)) :=
  FactorizedDynamics.leftProj_tangentProj_of_capture hs.capU₀
    ((FactorizedDynamics.capture_kStep_iff S₀ _ hh hs.capU₀).1 hs.capK)

/-- **Theorem 5.9 of arXiv 2502.03006 (convergence of abc-PSI), deterministic form.**  Assume A2,
A3, a loss bounded below (the paper has `ℓ ≥ 0`), learning rates `h_t > 0` with `∑ h_t = ∞`,
`∑ h_t² < ∞`, and let `Y_t = U_t S_t V_tᵀ` be iterates of Algorithm 4.1 with accumulated truncation
errors `∑_{t<T} ‖Y_{t+1} - Ŷ_{t+1}‖ ≤ D`.  Then

`liminf_t ‖P(Y_t) ∇ℓ(Y_t)‖² = 0`.

Differences from the paper: the gradient is exact, so the expectation over mini-batches is absent.
With mini-batch gradients the K-step augments by a batch gradient, which does not capture
`P(Y) ∇ℓ(Y)`, and the proof below does not apply (see also
`Research.SameMinibatchAugmentation` and `InexactGradient.variance_term_necessary`).  The proof
differs from the paper's in two places: `P_Û ∇ℓ = P(Y) ∇ℓ` is false and is replaced by
`‖P(Y) ∇ℓ‖ ≤ ‖P_Û ∇ℓ‖` (`IsAbcPsiEulerBasis.absorbs`), and the truncation error of the loss is
bounded with `B`, not with `c_l`, since `B` is the Lipschitz constant of `ℓ`.  The positivity
`h_t > 0` is added: `h_t = 0` gives no augmentation by the gradient. -/
theorem abcPsi_liminf_tangentGrad_eq_zero {ℓ : Matrix m n ℝ → ℝ} {c B ℓinf D : ℝ}
    (hℓ : ∀ x, HasFDerivAt ℓ (innerSL ℝ (g x)) x) (hg : ∀ x y, ‖g x - g y‖ ≤ c * ‖x - y‖)
    (hB : ∀ x, ‖g x‖ ≤ B) (hinf : ∀ x, ℓinf ≤ ℓ x) {r ρ : ℕ → ℕ}
    {U : (t : ℕ) → Matrix m (Fin (r t)) ℝ} {S : (t : ℕ) → Matrix (Fin (r t)) (Fin (r t)) ℝ}
    {V : (t : ℕ) → Matrix n (Fin (r t)) ℝ} {Uh : (t : ℕ) → Matrix m (Fin (ρ t)) ℝ} {lr : ℕ → ℝ}
    (hlr : ∀ t, 0 < lr t) (hdiv : ¬ Summable lr) (hsq : Summable fun t => lr t ^ 2)
    (hstep : ∀ t, IsAbcPsiEulerBasis g (lr t) (U t) (S t) (V t) (Uh t))
    (hD : ∀ T, ∑ t ∈ range T, ‖U (t + 1) * S (t + 1) * (V (t + 1))ᵀ -
      abcPsiEulerStep g (lr t) (U t) (S t) (V t) (Uh t)‖ ≤ D) :
    liminf (fun t => ‖tangentProj (U t) (V t) (g (U t * S t * (V t)ᵀ))‖ ^ 2) atTop = 0 := by
  set u : ℕ → ℝ := fun t => ‖tangentProj (U t) (V t) (g (U t * S t * (V t)ᵀ))‖ ^ 2 with hu
  have hnn : ∀ t, 0 ≤ u t := fun t => by positivity
  have hup : ∀ t, u t ≤ B ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _)
      (((isOrthProj_tangentProj (hstep t).orthU₀ (hstep t).orthV₀).norm_le _).trans (hB _)) 2
  have hbdd : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, hnn⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop u :=
    (isBoundedUnder_of ⟨B ^ 2, hup⟩).isCoboundedUnder_ge
  have hfreq : ∀ ε : ℝ, 0 < ε → ∀ N, ∃ t, N ≤ t ∧ u t < ε := fun ε hε N =>
    frequently_tangentGrad_sq_lt_of_absorbs hℓ hg
      (P := fun t => (leftProj (Uh t) : Matrix m n ℝ →L[ℝ] Matrix m n ℝ))
      (T := fun t => tangentProj (U t) (V t)) (fun t => isOrthProj_leftProj (hstep t).orthUh)
      (fun t => isOrthProj_tangentProj (hstep t).orthU₀ (hstep t).orthV₀)
      (x := fun t => U t * S t * (V t)ᵀ) (fun t => (hstep t).absorbs (hlr t).ne') (h := lr)
      (ϑ := fun t => ‖U (t + 1) * S (t + 1) * (V (t + 1))ᵀ -
        abcPsiEulerStep g (lr t) (U t) (S t) (V t) (Uh t)‖) (G := B)
      (fun t => by rw [(hstep t).step_eq]) (fun _ w _ => hB w) hD (fun _ => hinf _)
      (fun t => (hlr t).le) hdiv hsq hε N
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    refine liminf_le_of_frequently_le (frequently_atTop.2 fun N => ?_) hbdd
    obtain ⟨t, ht, hlt⟩ := hfreq ε hε N
    exact ⟨t, ht, hlt.le⟩
  · exact le_liminf_of_le hcob (Eventually.of_forall hnn)

/-- **The augmented basis of Algorithm 4.1 exists** for `2 r ≤ m`, with `2 r` columns. -/
theorem exists_isAbcPsiEulerBasis (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hrm : 2 * r ≤ Fintype.card m) :
    ∃ Uh : Matrix m (Fin (2 * r)) ℝ, IsAbcPsiEulerBasis g h U₀ S₀ V₀ Uh := by
  obtain ⟨Uh, hUh, hK, hU⟩ := MatrixBUG.exists_aug_qr hrm
    (U₀ * S₀ - h • (g (U₀ * S₀ * V₀ᵀ) * V₀)) U₀
  exact ⟨Uh, hU₀, hV₀, hUh, hU, hK⟩

/-- Satisfiability of the hypotheses of `abcPsi_liminf_tangentGrad_eq_zero` for every gradient: at
full rank (`U₀ = V₀ = Û = I`) every step is admissible. -/
theorem isAbcPsiEulerBasis_one (g : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (h : ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) :
    IsAbcPsiEulerBasis g h (1 : Matrix (Fin r) (Fin r) ℝ) S₀ 1 (1 : Matrix (Fin r) (Fin r) ℝ) where
  orthU₀ := by simp
  orthV₀ := by simp
  orthUh := by simp
  capU₀ := by simp
  capK := by simp

/-- At full rank, a step of Algorithm 4.1 without truncation is the gradient descent step, so the
truncation errors in `abcPsi_liminf_tangentGrad_eq_zero` vanish along gradient descent. -/
theorem abcPsiEulerStep_one (g : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (h : ℝ)
    (S₀ : Matrix (Fin r) (Fin r) ℝ) :
    abcPsiEulerStep g h 1 S₀ 1 (1 : Matrix (Fin r) (Fin r) ℝ) = S₀ - h • g S₀ := by
  simp [abcPsiEulerStep]

/-- A nonconstant loss `ℓ(Y) = 1 + cos ⟪A, Y⟫ ≥ 0` with bounded Lipschitz gradient, used to show
that the hypotheses of `abcPsi_liminf_tangentGrad_eq_zero` hold without degeneracy. -/
noncomputable def cosLoss (A Y : Matrix m n ℝ) : ℝ := 1 + Real.cos ⟪A, Y⟫

/-- The gradient `∇ℓ(Y) = -sin ⟪A, Y⟫ A` of `cosLoss`. -/
noncomputable def cosGrad (A Y : Matrix m n ℝ) : Matrix m n ℝ := (-Real.sin ⟪A, Y⟫) • A

/-- `cosGrad` is the gradient of `cosLoss`. -/
lemma hasFDerivAt_cosLoss (A Y : Matrix m n ℝ) :
    HasFDerivAt (cosLoss A) (innerSL ℝ (cosGrad A Y)) Y := by
  have h1 : HasFDerivAt (fun Z : Matrix m n ℝ => ⟪A, Z⟫) (innerSL ℝ A) Y :=
    (innerSL ℝ A).hasFDerivAt
  have h2 := ((Real.hasDerivAt_cos ⟪A, Y⟫).comp_hasFDerivAt Y h1).const_add 1
  have e : innerSL ℝ (cosGrad A Y) = (-Real.sin ⟪A, Y⟫) • innerSL ℝ A := by
    simp [cosGrad, map_smul]
  rw [e]
  exact h2

/-- `cosGrad A` is `‖A‖²`-Lipschitz. -/
lemma norm_cosGrad_sub_le (A x y : Matrix m n ℝ) :
    ‖cosGrad A x - cosGrad A y‖ ≤ ‖A‖ ^ 2 * ‖x - y‖ := by
  have e : cosGrad A x - cosGrad A y = (Real.sin ⟪A, y⟫ - Real.sin ⟪A, x⟫) • A := by
    simp only [cosGrad]
    rw [← sub_smul]
    congr 1
    ring
  rw [e, norm_smul, Real.norm_eq_abs]
  have h1 := Real.abs_sin_sub_sin_le ⟪A, y⟫ ⟪A, x⟫
  have h2 : |⟪A, y⟫ - ⟪A, x⟫| ≤ ‖A‖ * ‖x - y‖ := by
    rw [← inner_sub_right, norm_sub_rev x y]
    exact abs_real_inner_le_norm _ _
  have hA := norm_nonneg A
  nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) hA]

/-- `cosGrad A` is bounded by `‖A‖`. -/
lemma norm_cosGrad_le (A Y : Matrix m n ℝ) : ‖cosGrad A Y‖ ≤ ‖A‖ := by
  rw [cosGrad, norm_smul, norm_neg, Real.norm_eq_abs]
  have := Real.abs_sin_le_one ⟪A, Y⟫
  nlinarith [norm_nonneg A]

/-- **All hypotheses of Theorem 5.9 hold** for the loss `ℓ(Y) = 1 + cos ⟪A, Y⟫ ≥ 0`, learning rates
`h_t = 1 / (t + 1)` and the full-rank iteration (`U_t = V_t = Û_t = I`, no truncation). -/
example {r : ℕ} (A y₀ : Matrix (Fin r) (Fin r) ℝ) :
    ∃ y : ℕ → Matrix (Fin r) (Fin r) ℝ, y 0 = y₀ ∧
      liminf (fun t => ‖tangentProj (1 : Matrix (Fin r) (Fin r) ℝ)
        (1 : Matrix (Fin r) (Fin r) ℝ) (cosGrad A (1 * y t * (1 : Matrix (Fin r) (Fin r) ℝ)ᵀ))‖ ^ 2)
        atTop = 0 := by
  set lr : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 1) with hlr
  set y : ℕ → Matrix (Fin r) (Fin r) ℝ := fun t =>
    Nat.rec y₀ (fun k yk => yk - lr k • cosGrad A yk) t with hy
  have hy1 : ∀ t, y (t + 1) = y t - lr t • cosGrad A (y t) := fun _ => rfl
  have hpos : ∀ t, 0 < lr t := fun t => by
    simp only [hlr]
    positivity
  have hdiv : ¬ Summable lr := by
    intro hs
    apply Real.not_summable_one_div_natCast
    refine (summable_nat_add_iff 1).1 ?_
    simpa [hlr] using hs
  have hsq : Summable fun t => lr t ^ 2 := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow (p := 2).2 (by norm_num))
    refine h.congr fun t => ?_
    simp [hlr]
  refine ⟨y, rfl, abcPsi_liminf_tangentGrad_eq_zero (ℓ := cosLoss A) (c := ‖A‖ ^ 2) (B := ‖A‖)
    (ℓinf := 0) (D := 0) (r := fun _ => r) (ρ := fun _ => r) (U := fun _ => 1) (S := y)
    (V := fun _ => 1) (Uh := fun _ => 1) (lr := lr) (hasFDerivAt_cosLoss A) (norm_cosGrad_sub_le A)
    (norm_cosGrad_le A) (fun x => ?_) hpos hdiv hsq (fun t => isAbcPsiEulerBasis_one _ _ _)
    (fun T => ?_)⟩
  · have := Real.neg_one_le_cos ⟪A, x⟫
    simp only [cosLoss]
    linarith
  · refine (Finset.sum_eq_zero fun t _ => ?_).le
    rw [abcPsiEulerStep_one, hy1]
    simp

end Euler

end LeanDLRA.Literature.P2502_03006
