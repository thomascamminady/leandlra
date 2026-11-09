import LeanDLRA.HighOrder.MidpointBUG
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Integrators.Matrix.BUG
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2402.08607: Robust second-order midpoint BUG integrator

Ceruti–Einkemmer–Kusch–Lubich, *A robust second-order low-rank BUG integrator based on the
midpoint rule*, formalized for real `m × n` matrices with the Frobenius norm, at the level of the
factors the algorithm computes.  `IsMidpoint4rStep` is one step of the Midpoint BUG (4r) scheme
(augmented BUG half step, `MatrixBUG.IsRankAdaptiveStep`, then the Galerkin step
`IsGalerkinPart` in `Ū = orth(Û, h F V̂)`, `V̄ = orth(V̂, h Fᵀ Û)`), `IsMidpoint3rStep` the
3r variant of Remark 1, and `NormalBoundNear` the assumption (16) (`‖P_r^⊥(Y) F(t, Y)‖ ≤ ε_r` for
`Y ∈ M_r` in an open `ρ`-neighbourhood of `A(t)`).  Proved: the structure of the algorithm
(`IsMidpoint4rStep.algorithm`: `P̄`, `Q̄` commute and fix `Y₀` and `F_T`, the S-step is the Galerkin
flow from `Y₀`); **Theorem 1** (`IsMidpoint4rStep.local_error_le`, and
`local_error_of_second` with an explicit bound `M₂` on `A''`): `‖Ȳ₁ - A(t₁)‖ ≤ C h (h² + h ε_r +
ε_r̂)`; **Theorem 2** (`midpoint_global_error`, `midpoint_global_error_of_second`):
`‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε̂ + c₂ h ε + c₃ h² + c₄ n ϑ`, by Lady Windermere's fan with an induction
that keeps the iterates in the neighbourhood of (16); **Remark 4**
(`IsMidpoint4rStep.trunc_tolerance_le`, `norm_bestTrunc_near_le`, `IsMidpoint4rStep.trunc_rank_le`,
`IsMidpoint4rStep.trunc_rank_le'`); **Remark 5** (`IsMidpoint3rStep.local_error_le`:
`C h (h² + ε_r)`); existence of the steps (`exists_isMidpoint4rStep`, `exists_isMidpoint3rStep`).
All constants are explicit (`midC`, `truncC`, `secondBound`) and do not involve singular values.
The library already had the abstract core `MidpointBUG.IsMidpointBUGStep.local_error_le` (with `F`
Lipschitz in time and the capture properties as hypotheses); here they are derived from the
algorithm, and the Galerkin estimates of `HighOrder/MidpointBUG.lean` are reused.

Differences from the paper.  (i) The paper's constants depend on "a bound of the third derivatives";
its proof also uses `A'' = O(1)`.  We either assume `‖A''‖ ≤ M₂` or derive
`M₂ = secondBound B M₃ (b - a) = 2B/(b - a) + (3/2) M₃ (b - a)` from `C³` regularity on an interval
`[a, b]` (the paper's `[0, T]`), so the constants also depend on `b - a`.  No time regularity of `F`
is assumed (unlike the library's `MidpointBUG.midpointGalerkin_local_error`).  (ii) (16) is
stated for `Y = U S Vᵀ` with `S` invertible, as in the paper; it extends to singular `S` by
continuity (`NormalBoundNear.factored`), which is needed since BUG points may be rank deficient.
The radius must exceed `B h` (`2 B h` for the 3r scheme); in Theorem 2 the hypothesis `hsmall`
asks the error bound plus `B h` to stay below it.  (iii) `orth(…)` is any orthonormal system whose
range contains the given columns; `S₀` need not be invertible.  (iv) The exact flows through the
iterates (Lady Windermere) are hypotheses, as elsewhere in the library.  (v) **False claim**: the
first inequality of Remark 4, `‖Y₁ - A(t₁)‖ ≤ h ε_r + 2 ‖Ȳ₁ - A(t₁)‖`, fails with the constant `1`
(`remark4_constant_false`); we prove it with `2 e^{L h} h ε_r` (needs `F` continuous in time), and
the final form `C' h (h² + ε_r)` needs `ε_r̂ ≤ ε_r` (otherwise `C' h (h² + ε_r + ε_r̂)`).
-/

open Set Filter Topology
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2402_08607

/-! ### The Galerkin step on an inner product space, without time regularity of `F` -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regularity of the exact solution used by the paper: `A` has three derivatives `a₁, a₂, a₃` on
`[a, b]` (one-sided at the ends), with `‖a₂‖ ≤ M₂` and `‖a₃‖ ≤ M₃`. -/
structure HasDerivData (A a₁ a₂ a₃ : ℝ → E) (a b M₂ M₃ : ℝ) : Prop where
  d₀ : ∀ t ∈ Icc a b, HasDerivWithinAt A (a₁ t) (Icc a b) t
  d₁ : ∀ t ∈ Icc a b, HasDerivWithinAt a₁ (a₂ t) (Icc a b) t
  d₂ : ∀ t ∈ Icc a b, HasDerivWithinAt a₂ (a₃ t) (Icc a b) t
  b₂ : ∀ t ∈ Icc a b, ‖a₂ t‖ ≤ M₂
  b₃ : ∀ t ∈ Icc a b, ‖a₃ t‖ ≤ M₃

namespace HasDerivData

variable {A a₁ a₂ a₃ : ℝ → E} {a b M₂ M₃ : ℝ}

/-- The derivative data restrict to subintervals. -/
theorem mono (hD : HasDerivData A a₁ a₂ a₃ a b M₂ M₃) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    HasDerivData A a₁ a₂ a₃ a' b' M₂ M₃ where
  d₀ t ht := (hD.d₀ t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)
  d₁ t ht := (hD.d₁ t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)
  d₂ t ht := (hD.d₂ t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)
  b₂ t ht := hD.b₂ t (Icc_subset_Icc ha hb ht)
  b₃ t ht := hD.b₃ t (Icc_subset_Icc ha hb ht)

lemma cont₀ (hD : HasDerivData A a₁ a₂ a₃ a b M₂ M₃) : ContinuousOn A (Icc a b) :=
  fun t ht => (hD.d₀ t ht).continuousWithinAt

lemma cont₁ (hD : HasDerivData A a₁ a₂ a₃ a b M₂ M₃) : ContinuousOn a₁ (Icc a b) :=
  fun t ht => (hD.d₁ t ht).continuousWithinAt

lemma cont₂ (hD : HasDerivData A a₁ a₂ a₃ a b M₂ M₃) : ContinuousOn a₂ (Icc a b) :=
  fun t ht => (hD.d₂ t ht).continuousWithinAt

lemma right_deriv {f : ℝ → E} {f' : E} {a b s : ℝ} (hf : HasDerivWithinAt f f' (Icc a b) s)
    (hs : s ∈ Ico a b) : HasDerivWithinAt f f' (Ici s) s :=
  (hf.mono (Icc_subset_Icc_left hs.1)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hs.2)

/-- On `[a, b)` the first derivative is the vector field along the solution. -/
theorem eq_field {F : ℝ → E → E} (hD : HasDerivData A a₁ a₂ a₃ a b M₂ M₃)
    (hA : ODESolution F A a b) {t : ℝ} (ht : t ∈ Ico a b) : a₁ t = F t (A t) := by
  have h1 := right_deriv (hD.d₀ t (Ico_subset_Icc_self ht)) ht
  exact (uniqueDiffOn_Ici t t self_mem_Ici).eq_deriv _ h1 (hA.deriv t ht)

end HasDerivData

/-- The bound `2 B / T + (3/2) M₃ T` for the second derivative on an interval of length `T`. -/
noncomputable def secondBound (B M₃ T : ℝ) : ℝ := 2 * B / T + 3 / 2 * M₃ * T

/-- **Interpolation between first and third derivative**: on `[a, b]`, `a < b`, a function `g` with
`‖g‖ ≤ B` and `‖g''‖ ≤ M₃` has `‖g'‖ ≤ 2 B / (b - a) + (3/2) M₃ (b - a)`.  This bound blows up for
`b - a → 0`, which is why the second derivative enters the local error constant. -/
theorem norm_deriv_le_secondBound {g g₁ g₂ : ℝ → E} {a b B M₃ : ℝ} (hab : a < b)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (g₁ t) (Icc a b) t)
    (hg₁ : ∀ t ∈ Icc a b, HasDerivWithinAt g₁ (g₂ t) (Icc a b) t)
    (hB : ∀ t ∈ Icc a b, ‖g t‖ ≤ B) (hM : ∀ t ∈ Icc a b, ‖g₂ t‖ ≤ M₃) :
    ∀ t ∈ Icc a b, ‖g₁ t‖ ≤ secondBound B M₃ (b - a) := by
  have hc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  have hc₁ : ContinuousOn g₁ (Icc a b) := fun t ht => (hg₁ t ht).continuousWithinAt
  have hd : ∀ s ∈ Ico a b, HasDerivWithinAt g (g₁ s) (Ici s) s := fun s hs =>
    HasDerivData.right_deriv (hg s (Ico_subset_Icc_self hs)) hs
  have hd₁ : ∀ s ∈ Ico a b, HasDerivWithinAt g₁ (g₂ s) (Ici s) s := fun s hs =>
    HasDerivData.right_deriv (hg₁ s (Ico_subset_Icc_self hs)) hs
  have hM' : ∀ s ∈ Ico a b, ‖g₂ s‖ ≤ M₃ := fun s hs => hM s (Ico_subset_Icc_self hs)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  set T := b - a with hT
  have hT0 : 0 < T := sub_pos.2 hab
  have h1 := MidpointBUG.norm_taylor_one_le hc hd hc₁ hd₁ hM' b hb
  have h2 : T * ‖g₁ a‖ ≤ 2 * B + M₃ * T ^ 2 / 2 := by
    have e : T • g₁ a = (g b - g a) - (g b - g a - T • g₁ a) := by abel
    have h3 := norm_sub_le (g b - g a) (g b - g a - T • g₁ a)
    have h4 := norm_sub_le (g b) (g a)
    rw [← e, norm_smul, Real.norm_of_nonneg hT0.le] at h3
    linarith [hB b hb, hB a ha]
  have h3 : ‖g₁ a‖ ≤ 2 * B / T + M₃ * T / 2 := by
    have e : 2 * B / T + M₃ * T / 2 = (2 * B + M₃ * T ^ 2 / 2) / T := by
      field_simp
    rw [e, le_div_iff₀ hT0]
    linarith
  have hM0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM a ha)
  intro t ht
  have h4 := norm_image_sub_le_of_norm_deriv_right_le_segment hc₁ hd₁ hM' t ht
  have h5 : M₃ * (t - a) ≤ M₃ * T := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM0
  have h6 := norm_add_le (g₁ t - g₁ a) (g₁ a)
  rw [sub_add_cancel] at h6
  have e : secondBound B M₃ T = 2 * B / T + M₃ * T / 2 + M₃ * T := by
    unfold secondBound; ring
  rw [e]
  linarith

/-- **Derivative data from `C³`.**  A solution of `A' = F(t, A)` with `‖F‖ ≤ B` that is `C³` on
`[a, b]`, `a < b`, with `‖A'''‖ ≤ M₃`, has `‖A''‖ ≤ secondBound B M₃ (b - a)`. -/
theorem hasDerivData_of_contDiffOn {F : ℝ → E → E} {A : ℝ → E} {a b B M₃ : ℝ} (hab : a < b)
    (hB : IsBoundedField F B) (hA : ODESolution F A a b) (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃) :
    HasDerivData A (iteratedDerivWithin 1 A (Icc a b)) (iteratedDerivWithin 2 A (Icc a b))
      (iteratedDerivWithin 3 A (Icc a b)) a b (secondBound B M₃ (b - a)) M₃ := by
  obtain ⟨T, hT, rfl⟩ : ∃ T, 0 < T ∧ b = a + T := ⟨b - a, by linarith, by ring⟩
  obtain ⟨hc, hw, -⟩ := MidpointBUG.contDiffOn_three_data hT hA3
  have h0 := hw 0 (by norm_num)
  have h1 := hw 1 (by norm_num)
  have h2 := hw 2 (by norm_num)
  simp only [iteratedDerivWithin_zero, zero_add, one_add_one_eq_two] at h0 h1
  have h2' : ∀ x ∈ Icc a (a + T), HasDerivWithinAt (iteratedDerivWithin 2 A (Icc a (a + T)))
      (iteratedDerivWithin 3 A (Icc a (a + T)) x) (Icc a (a + T)) x := h2
  have hbd : ∀ t ∈ Icc a (a + T), ‖iteratedDerivWithin 1 A (Icc a (a + T)) t‖ ≤ B := by
    intro t ht
    have hab' : a ≠ a + T := by linarith
    have hIco : ∀ t ∈ Ico a (a + T), ‖iteratedDerivWithin 1 A (Icc a (a + T)) t‖ ≤ B := by
      intro t ht
      have h3 := HasDerivData.right_deriv (h0 t (Ico_subset_Icc_self ht)) ht
      rw [(uniqueDiffOn_Ici t t self_mem_Ici).eq_deriv _ h3 (hA.deriv t ht)]
      exact hB t (A t)
    refine le_on_closure (f := fun t => ‖iteratedDerivWithin 1 A (Icc a (a + T)) t‖)
      (g := fun _ => B) hIco ?_ continuousOn_const ?_
    · rw [closure_Ico hab']
      exact (hc 1 (by norm_num)).norm
    · rwa [closure_Ico hab']
  exact ⟨h0, h1, h2', norm_deriv_le_secondBound (by linarith) h1 h2' hbd hM₃, hM₃⟩

/-- **The Galerkin step of the midpoint BUG integrator** (arXiv 2402.08607, proof of Theorem 1,
parts (a)-(c), on an inner product space).  `R` is an orthogonal projector fixing `A(t₀)`,
`Yh` a midpoint approximation with `‖Yh - A(t₀ + h/2)‖ ≤ η`, and `‖(1 - R) F(t₀ + h/2, Yh)‖ ≤ ε`.
Then the Galerkin trajectory `YS' = R F(t, YS)`, `YS(t₀) = A(t₀)` satisfies
`‖YS(t₀ + h) - A(t₀ + h)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ`, `θ = M₃ h³/24 + h (L η + ε)`.
This is `MidpointBUG.midpointGalerkin_local_error` without its hypothesis that `F` is Lipschitz in
time: as in the paper, only the derivatives of the exact solution enter. -/
theorem midpoint_galerkin_error {F : ℝ → E → E} {L : ℝ} {R : E →L[ℝ] E} (hR : IsOrthProj R)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 < h) {A a₁ a₂ a₃ : ℝ → E}
    {M₂ M₃ : ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hD : HasDerivData A a₁ a₂ a₃ t₀ (t₀ + h) M₂ M₃) (hfix : R (A t₀) = A t₀) {Yh : E} {η ε : ℝ}
    (hYh : ‖Yh - A (t₀ + h / 2)‖ ≤ η) (hnormal : ‖(1 - R) (F (t₀ + h / 2) Yh)‖ ≤ ε) {YS : ℝ → E}
    (hS : ODESolution (fun t x => R (F t x)) YS t₀ (t₀ + h)) (hS₀ : YS t₀ = A t₀) :
    ‖YS (t₀ + h) - A (t₀ + h)‖ ≤
      (Real.exp (L * h) - 1) * (M₃ * h ^ 3 / 24 + h * (L * η + ε) + M₂ * h ^ 2)
        + (M₃ * h ^ 3 / 24 + h * (L * η + ε)) := by
  have hmid : t₀ + h / 2 ∈ Ico t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
  have hq : ‖A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ M₃ * h ^ 3 / 24 := by
    have := MidpointBUG.midpoint_defect_le_sharp (A := A) hh hD.cont₀ hD.cont₁ hD.cont₂
      (fun x hx => (hD.d₀ x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      (fun x hx => (hD.d₁ x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      (fun x hx => (hD.d₂ x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      (fun x hx => hD.b₃ x (Ioo_subset_Icc_self hx))
    rwa [hD.eq_field hA hmid] at this
  have hθ := MidpointBUG.midpoint_capture hR hF hL hh.le hfix hq (Yh := Yh) (η := η) (ε' := ε)
    (by rw [norm_sub_rev]; exact hYh) (by simpa using hnormal)
  have hρ : ∀ t ∈ Icc t₀ (t₀ + h), ‖A t - R (A t)‖
      ≤ (M₃ * h ^ 3 / 24 + h * (L * η + ε)) + M₂ * h ^ 2 := by
    refine MidpointBUG.norm_le_of_second_deriv (g := fun t => A t - R (A t))
      (g₁ := fun t => a₁ t - R (a₁ t)) (g₂ := fun s => a₂ s - R (a₂ s)) rfl hh.le
      (hD.cont₀.sub (R.continuous.comp_continuousOn hD.cont₀)) ?_
      (hD.cont₁.sub (R.continuous.comp_continuousOn hD.cont₁)) ?_ ?_ (by simp [hfix]) hθ
    · intro s hs
      have := HasDerivData.right_deriv (hD.d₀ s (Ico_subset_Icc_self hs)) hs
      exact this.sub (R.hasFDerivAt.comp_hasDerivWithinAt s this)
    · intro s hs
      have := HasDerivData.right_deriv (hD.d₁ s (Ico_subset_Icc_self hs)) hs
      exact this.sub (R.hasFDerivAt.comp_hasDerivWithinAt s this)
    · intro s hs
      exact (hR.norm_sub_le _).trans (hD.b₂ s (Ico_subset_Icc_self hs))
  exact MidpointBUG.galerkin_step_error_interior hR hF hL rfl hh.le hA hS (hS₀.trans hfix.symm)
    hρ hθ

/-- Two trajectories with the same start and speed at most `B` stay `2 B τ`-close on `[t₀, t₀ + τ]`:
the points computed in a step lie near the exact solution. -/
lemma near_of_proj {F : ℝ → E → E} {B t₀ τ : ℝ} {P : E →L[ℝ] E} (hP : IsOrthProj P)
    (hB : IsBoundedField F B) {y A : ℝ → E} (hy : ODESolution (fun t x => P (F t x)) y t₀ (t₀ + τ))
    (hA : ODESolution F A t₀ (t₀ + τ)) (hy₀ : y t₀ = A t₀) {s t : ℝ} (hs : s ∈ Icc t₀ (t₀ + τ))
    (ht : t ∈ Icc t₀ (t₀ + τ)) : ‖y s - A t‖ ≤ 2 * B * τ := by
  have h1 := hy.norm_sub_start_le_of_proj hB hP rfl s hs
  have h2 := hA.norm_sub_start_le hB rfl t ht
  have e : y s - A t = (y s - y t₀) - (A t - A t₀) := by rw [hy₀]; abel
  rw [e]
  calc _ ≤ ‖y s - y t₀‖ + ‖A t - A t₀‖ := norm_sub_le _ _
    _ ≤ B * τ + B * τ := add_le_add h1 h2
    _ = _ := by ring

end Abstract

/-! ### The explicit constant -/

section Constant

/-- The constant of the local error bound (step sizes `h ≤ H`):
`(1 + L H K) (M₃/24 + L c₂/4 + L c₁/2 + 1) + L K M₂`, `K = e^{L H}`, `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H`. It depends only on `L`, `B`, `M₂`, `M₃` and `H`. -/
noncomputable def midC (L B M₂ M₃ H : ℝ) : ℝ :=
  (1 + L * H * Real.exp (L * H))
      * (M₃ / 24 + L * bugC₂ L B H / 4 + L * bugC₁ L H / 2 + 1)
    + L * Real.exp (L * H) * M₂

lemma midC_nonneg {L B M₂ M₃ H : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hH : 0 ≤ H) : 0 ≤ midC L B M₂ M₃ H := by
  have h1 := bugC₁_nonneg hL hH
  have h2 := bugC₂_nonneg hL hB hH
  unfold midC
  positivity

/-- The scalar estimate behind the local error bound. -/
theorem midpoint_scalar {L B M₂ M₃ H h ε ε' : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (hh : 0 ≤ h) (hhH : h ≤ H) (hε : 0 ≤ ε) (hε' : 0 ≤ ε') :
    (Real.exp (L * h) - 1) * (M₃ * h ^ 3 / 24
        + h * (L * (h / 2 * (bugC₁ L H * ε + bugC₂ L B H * (h / 2))) + ε') + M₂ * h ^ 2)
      + (M₃ * h ^ 3 / 24 + h * (L * (h / 2 * (bugC₁ L H * ε + bugC₂ L B H * (h / 2))) + ε'))
      ≤ midC L B M₂ M₃ H * h * (h ^ 2 + h * ε + ε') := by
  have hH : 0 ≤ H := hh.trans hhH
  set K := Real.exp (L * H) with hK
  set c₁ := bugC₁ L H with hc₁
  set c₂ := bugC₂ L B H with hc₂
  have hc₁0 : 0 ≤ c₁ := bugC₁_nonneg hL hH
  have hc₂0 : 0 ≤ c₂ := bugC₂_nonneg hL hB hH
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have he0 : 0 ≤ Real.exp (L * h) - 1 := by linarith [Real.one_le_exp hLh]
  have hexp : Real.exp (L * h) - 1 ≤ L * h * K :=
    (exp_sub_one_le_mul_exp (L * h)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)) hLh)
  have hexp' : Real.exp (L * h) - 1 ≤ L * H * K :=
    hexp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhH hL) hK0)
  set a := M₃ / 24 + L * c₂ / 4 with ha
  set b := L * c₁ / 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set θ := M₃ * h ^ 3 / 24 + h * (L * (h / 2 * (c₁ * ε + c₂ * (h / 2))) + ε') with hθ
  have hθe : θ = h * (a * h ^ 2 + b * (h * ε) + ε') := by rw [hθ, ha, hb]; ring
  have hθ0 : 0 ≤ θ := by rw [hθe]; positivity
  have hM : 0 ≤ M₂ * h ^ 2 := by positivity
  have h1 : (Real.exp (L * h) - 1) * θ ≤ L * H * K * θ := mul_le_mul_of_nonneg_right hexp' hθ0
  have h2 : (Real.exp (L * h) - 1) * (M₂ * h ^ 2) ≤ L * h * K * (M₂ * h ^ 2) :=
    mul_le_mul_of_nonneg_right hexp hM
  have hq : 0 ≤ h ^ 2 := sq_nonneg h
  have hp : 0 ≤ h * ε := mul_nonneg hh hε
  have h3 : a * h ^ 2 + b * (h * ε) + ε' ≤ (a + b + 1) * (h ^ 2 + h * ε + ε') := by
    linarith [mul_nonneg ha0 hp, mul_nonneg ha0 hε', mul_nonneg hb0 hq, mul_nonneg hb0 hε']
  have h4 : θ ≤ h * ((a + b + 1) * (h ^ 2 + h * ε + ε')) := by
    rw [hθe]; exact mul_le_mul_of_nonneg_left h3 hh
  have hLHK : 0 ≤ 1 + L * H * K := by positivity
  have h5 : (1 + L * H * K) * θ ≤ (1 + L * H * K) * (h * ((a + b + 1) * (h ^ 2 + h * ε + ε'))) :=
    mul_le_mul_of_nonneg_left h4 hLHK
  have h6 : L * h * K * (M₂ * h ^ 2) ≤ L * K * M₂ * h * (h ^ 2 + h * ε + ε') := by
    have : 0 ≤ L * K * M₂ * h * (h * ε + ε') := by positivity
    linarith
  have hC : midC L B M₂ M₃ H = (1 + L * H * K) * (a + b + 1) + L * K * M₂ := by
    simp only [midC, ha, hb, hK, hc₁, hc₂]
  rw [hC]
  have e1 : (Real.exp (L * h) - 1) * (θ + M₂ * h ^ 2) + θ
      = (Real.exp (L * h) - 1) * θ + (Real.exp (L * h) - 1) * (M₂ * h ^ 2) + θ := by ring
  rw [e1]
  have e2 : ((1 + L * H * K) * (a + b + 1) + L * K * M₂) * h * (h ^ 2 + h * ε + ε')
      = (1 + L * H * K) * (h * ((a + b + 1) * (h ^ 2 + h * ε + ε')))
        + L * K * M₂ * h * (h ^ 2 + h * ε + ε') := by ring
  rw [e2]
  linarith

end Constant

/-! ### Assumption (16): small normal components near the exact solution -/

section Near

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Assumption (16) of arXiv 2402.08607** at rank `r`: for `a ≤ t ≤ b` and every
`Y = U S Vᵀ ∈ M_r` (`U`, `V` with `r` orthonormal columns, `S` invertible) in the open `ρ`-ball
around `A(t)`, `‖P_r^⊥(Y) F(t, Y)‖ ≤ ε`, where `P_r^⊥(Y) = 1 - tangentProj U V` as in (4). -/
def NormalBoundNear (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε : ℝ)
    (A : ℝ → Matrix m n ℝ) (ρ a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ (U : Matrix m (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S → ‖U * S * Vᵀ - A t‖ < ρ →
      ‖(1 - tangentProj U V) (F t (U * S * Vᵀ))‖ ≤ ε

/-- All but finitely many shifts of a square matrix are invertible, so `0` is a limit of shifts
`δ` with `S + δ I` invertible. -/
lemma dense_isUnit_shift {r : ℕ} (S : Matrix (Fin r) (Fin r) ℝ) :
    Dense {δ : ℝ | IsUnit (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ))} := by
  have hfin : ((fun x : ℝ => -x) '' spectrum ℝ S).Finite := (Matrix.finite_spectrum S).image _
  refine (hfin.countable.dense_compl ℝ).mono ?_
  intro δ hδ
  by_contra hn
  refine hδ ⟨-δ, ?_, neg_neg δ⟩
  rw [spectrum.mem_iff]
  intro hu
  apply hn
  have e : S + δ • (1 : Matrix (Fin r) (Fin r) ℝ) = -(algebraMap ℝ _ (-δ) - S) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [neg_smul, neg_sub, sub_neg_eq_add]
  change IsUnit (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ))
  rw [e]
  exact hu.neg

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {r : ℕ} {ε ρ a b L : ℝ} {A : ℝ → Matrix m n ℝ}

/-- Shrinking the time interval. -/
lemma NormalBoundNear.mono_time (hN : NormalBoundNear F r ε A ρ a b) {a' b' : ℝ} (ha : a ≤ a')
    (hb : b' ≤ b) : NormalBoundNear F r ε A ρ a' b' :=
  fun t ht => hN t (Icc_subset_Icc ha hb ht)

/-- Moving the centre curve: a neighbourhood of `Φ` of radius `ρ'` lies in the neighbourhood of
`A` of radius `ρ` if `‖Φ - A‖ + ρ' ≤ ρ`. -/
lemma NormalBoundNear.recentre (hN : NormalBoundNear F r ε A ρ a b) {Φ : ℝ → Matrix m n ℝ}
    {e ρ' : ℝ} (he : ∀ t ∈ Icc a b, ‖Φ t - A t‖ ≤ e) (hρ : e + ρ' ≤ ρ) :
    NormalBoundNear F r ε Φ ρ' a b := fun t ht U S V hU hV hu hd =>
  hN t ht U S V hU hV hu (by
    have := norm_sub_le_norm_sub_add_norm_sub (U * S * Vᵀ) (Φ t) (A t)
    linarith [he t ht])

variable [DecidableEq m] [DecidableEq n]

/-- `P_r^⊥(Y) Z = (I - U Uᵀ) Z (I - V Vᵀ)`. -/
lemma one_sub_tangentProj_apply {k k' : Type*} [Fintype k] [Fintype k'] (U : Matrix m k ℝ)
    (V : Matrix n k' ℝ) (Z : Matrix m n ℝ) :
    (1 - tangentProj U V) Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  have h := tangentProj_add_normal U V Z
  change Z - tangentProj U V Z = _
  exact sub_eq_of_eq_add' h.symm

/-- **Assumption (16) passes to singular `S`.**  The paper's assumption concerns `Y ∈ M_r`, but the
BUG points `K(t₁) V₀ᵀ` and `Û Ŝ V̂ᵀ` need not have full rank.  Since `F` is Lipschitz and the
neighbourhood is open, the bound extends to `U S Vᵀ` with arbitrary `S`: perturb `S` to the
invertible `S + δ I`. -/
theorem NormalBoundNear.factored (hN : NormalBoundNear F r ε A ρ a b) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc a b) {U : Matrix m (Fin r) ℝ}
    (S : Matrix (Fin r) (Fin r) ℝ) {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hd : ‖U * S * Vᵀ - A t‖ < ρ) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
  set φ : ℝ → Matrix m n ℝ := fun δ => U * S * Vᵀ + δ • (U * Vᵀ) with hφ
  have hφc : Continuous φ := by fun_prop
  have hFc : Continuous fun δ => F t (φ δ) := ((hF.lipschitzWith hL t).continuous).comp hφc
  set Ψ : Matrix m n ℝ →L[ℝ] Matrix m n ℝ := 1 - tangentProj U V with hΨ
  have hg : Continuous fun δ => ‖Ψ (F t (φ δ))‖ := (Ψ.continuous.comp hFc).norm
  have hk : Continuous fun δ => ‖φ δ - A t‖ := (hφc.sub continuous_const).norm
  have hφS : ∀ δ, φ δ = U * (S + δ • 1) * Vᵀ := fun δ => by
    simp only [hφ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  have h0 : φ 0 = U * S * Vᵀ := by simp [hφ]
  by_contra hcon
  rw [not_le, ← one_sub_tangentProj_apply, ← h0] at hcon
  rw [← h0] at hd
  have hopen : IsOpen ({δ | ε < ‖Ψ (F t (φ δ))‖} ∩ {δ | ‖φ δ - A t‖ < ρ}) :=
    (isOpen_lt continuous_const hg).inter (isOpen_lt hk continuous_const)
  obtain ⟨δ, ⟨h1, h2⟩, hu⟩ := (dense_isUnit_shift S).inter_open_nonempty _ hopen ⟨0, hcon, hd⟩
  have h2' : ‖U * (S + δ • 1) * Vᵀ - A t‖ < ρ := by rwa [← hφS]
  have := hN t ht U (S + δ • 1) V hU hV hu h2'
  rw [← hφS] at this
  exact absurd h1 (not_lt.2 this)

omit [DecidableEq m] [DecidableEq n] in
/-- `ε ≥ 0` as soon as one factored point lies in the neighbourhood. -/
lemma NormalBoundNear.nonneg (hN : NormalBoundNear F r ε A ρ a b) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {t : ℝ} (ht : t ∈ Icc a b) {U : Matrix m (Fin r) ℝ}
    (S : Matrix (Fin r) (Fin r) ℝ) {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hd : ‖U * S * Vᵀ - A t‖ < ρ) : 0 ≤ ε := by
  classical
  exact (norm_nonneg _).trans (hN.factored hF hL ht S hU hV hd)

end Near

/-! ### The Galerkin step for matrices -/

section Galerkin

variable {m n : Type*} [Fintype m] [Fintype n]

/-! The Galerkin projector `X ↦ Ū Ūᵀ X V̄ V̄ᵀ` onto the matrices `Ū S̄ V̄ᵀ` is the core
`LeanDLRA.galerkinProj`; the local `galProj` of an earlier version of this file was the same
definition (unification batch C2). -/

lemma galProj_apply {b b' : Type*} [Fintype b] [Fintype b'] (Ub : Matrix m b ℝ)
    (Vb : Matrix n b' ℝ) (X : Matrix m n ℝ) :
    galerkinProj Ub Vb X = leftProj Ub (rightProj Vb X) := rfl

/-- The trajectory `Ū S̄ V̄ᵀ` of the S-step solves the full-space Galerkin equation. -/
lemma odeSolution_galProj {b b' : Type*} [Fintype b] [Fintype b'] {Ub : Matrix m b ℝ}
    {Vb : Matrix n b' ℝ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Sb : ℝ → Matrix b b' ℝ} {a c : ℝ}
    (h : ODESolution (MatrixBUG.sField Ub Vb F) Sb a c) :
    ODESolution (fun t x => galerkinProj Ub Vb (F t x)) (fun t => Ub * Sb t * Vbᵀ) a c := by
  have h1 := MatrixBUG.odeSolution_sField h
  simp only [galProj_apply]
  exact h1

/-- The Galerkin projector of orthonormal bases is an orthogonal projector. -/
lemma isOrthProj_galProj {b b' : Type*} [Fintype b] [Fintype b'] [DecidableEq b] [DecidableEq b']
    {Ub : Matrix m b ℝ} {Vb : Matrix n b' ℝ} (hUb : Ubᵀ * Ub = 1) (hVb : Vbᵀ * Vb = 1) :
    IsOrthProj (galerkinProj Ub Vb : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  (isOrthProj_leftProj hUb).mul (isOrthProj_rightProj hVb) (leftProj_rightProj_comm Ub Vb)

omit [Fintype n] in
/-- Capture in transposed form: `V₁ V₁ᵀ X = X` gives `Xᵀ V₁ V₁ᵀ = Xᵀ`. -/
lemma transpose_mul_cap {k k' : Type*} [Fintype k'] {V₁ : Matrix m k' ℝ} {X : Matrix m k ℝ}
    (h : V₁ * V₁ᵀ * X = X) : Xᵀ * V₁ * V₁ᵀ = Xᵀ := by
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc] at this

/-- The Galerkin projector fixes `U₀ S₀ V₀ᵀ` if the ranges of `Ū`, `V̄` contain those of `U₀`, `V₀`:
the same-starting-value property stated after (8) in the paper. -/
lemma galProj_fix {b b' k k' : Type*} [Fintype b] [Fintype b'] [Fintype k] [Fintype k']
    {Ub : Matrix m b ℝ} {Vb : Matrix n b' ℝ} {U₀ : Matrix m k ℝ} {V₀ : Matrix n k' ℝ}
    (S₀ : Matrix k k' ℝ) (capU₀ : Ub * Ubᵀ * U₀ = U₀) (capV₀ : Vb * Vbᵀ * V₀ = V₀) :
    galerkinProj Ub Vb (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
  have e1 : rightProj Vb (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [rightProj_apply, Matrix.mul_assoc (U₀ * S₀), Matrix.mul_assoc (U₀ * S₀),
      transpose_mul_cap capV₀]
  have e2 : leftProj Ub (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [leftProj_apply, Matrix.mul_assoc U₀, ← Matrix.mul_assoc, capU₀]
  rw [galProj_apply, e1, e2]

/-- **The key relations of the proof of Theorem 1** (arXiv 2402.08607, part (a)).  If the ranges of
`Ū`, `V̄` contain those of `U`, `G V` and `V`, `Gᵀ U`, then `Ū Ūᵀ · V̄ V̄ᵀ` fixes the tangential
part `P(U, V) G = F_T`: `(I - Ū Ūᵀ) F_T = 0` and `F_T (I - V̄ V̄ᵀ) = 0`. -/
theorem galProj_tangent {k k' b b' : Type*} [Fintype k] [Fintype k'] [Fintype b] [Fintype b']
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} {Ub : Matrix m b ℝ} {Vb : Matrix n b' ℝ}
    (capU : Ub * Ubᵀ * U = U) (capV : Vb * Vbᵀ * V = V) {G : Matrix m n ℝ}
    (capF : Ub * Ubᵀ * (G * V) = G * V) (capFt : Vb * Vbᵀ * (Gᵀ * U) = Gᵀ * U) :
    galerkinProj Ub Vb (tangentProj U V G) = tangentProj U V G := by
  have f1 : Uᵀ * G * (Vb * Vbᵀ) = Uᵀ * G := by
    have := transpose_mul_cap capFt
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at this
  have f2 : Vᵀ * (Vb * Vbᵀ) = Vᵀ := by
    rw [← Matrix.mul_assoc]; exact transpose_mul_cap capV
  have hr : tangentProj U V G * (Vb * Vbᵀ) = tangentProj U V G := by
    rw [tangentProj_apply, Matrix.sub_mul, Matrix.add_mul]
    have e1 : U * Uᵀ * G * (Vb * Vbᵀ) = U * Uᵀ * G := by
      rw [Matrix.mul_assoc U, Matrix.mul_assoc U, f1, ← Matrix.mul_assoc]
    have e2 : G * V * Vᵀ * (Vb * Vbᵀ) = G * V * Vᵀ := by rw [Matrix.mul_assoc _ Vᵀ, f2]
    have e3 : U * Uᵀ * G * V * Vᵀ * (Vb * Vbᵀ) = U * Uᵀ * G * V * Vᵀ := by
      rw [Matrix.mul_assoc _ Vᵀ, f2]
    rw [e1, e2, e3]
  have hl : Ub * Ubᵀ * tangentProj U V G = tangentProj U V G := by
    rw [tangentProj_apply, Matrix.mul_sub, Matrix.mul_add]
    have e1 : Ub * Ubᵀ * (U * Uᵀ * G) = U * Uᵀ * G := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, capU]
    have e2 : Ub * Ubᵀ * (G * V * Vᵀ) = G * V * Vᵀ := by
      rw [← Matrix.mul_assoc, capF]
    have e3 : Ub * Ubᵀ * (U * Uᵀ * G * V * Vᵀ) = U * Uᵀ * G * V * Vᵀ := by
      rw [show U * Uᵀ * G * V * Vᵀ = U * (Uᵀ * G * V * Vᵀ) by simp only [Matrix.mul_assoc],
        ← Matrix.mul_assoc, capU]
    rw [e1, e2, e3]
  rw [galProj_apply, rightProj_apply', hr, leftProj_apply, hl]

/-- Consequently the Galerkin projector captures `G` up to the normal component at `(U, V)`:
`‖G - Ū Ūᵀ G V̄ V̄ᵀ‖ ≤ ‖(1 - P(U, V)) G‖` (best approximation in the range). -/
theorem norm_one_sub_galerkin_le {k k' b b' : Type*} [Fintype k] [Fintype k'] [Fintype b]
    [Fintype b'] [DecidableEq b] [DecidableEq b'] {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    {Ub : Matrix m b ℝ} {Vb : Matrix n b' ℝ} (hUb : Ubᵀ * Ub = 1) (hVb : Vbᵀ * Vb = 1)
    (capU : Ub * Ubᵀ * U = U) (capV : Vb * Vbᵀ * V = V) {G : Matrix m n ℝ}
    (capF : Ub * Ubᵀ * (G * V) = G * V) (capFt : Vb * Vbᵀ * (Gᵀ * U) = Gᵀ * U) :
    ‖(1 - galerkinProj Ub Vb) G‖ ≤ ‖(1 - tangentProj U V) G‖ := by
  have h := (isOrthProj_galProj hUb hVb).norm_sub_le_of_mem_range G _
    (galProj_tangent capU capV capF capFt)
  simpa using h

/-- **Step 2 of the midpoint BUG integrator** (arXiv 2402.08607, eqs. (10)-(12)), given a midpoint
approximation `Yh` with bases `Uh`, `Vh`: bases `Ū = Ub`, `V̄ = Vb` with orthonormal columns whose
ranges contain `(Uh, h F(t_{1/2}, Yh) Vh)` and `(Vh, h F(t_{1/2}, Yh)ᵀ Uh)`, and the Galerkin
equation `S̄' = Ūᵀ F(t, Ū S̄ V̄ᵀ) V̄`, `S̄(t₀) = M̄ S₀ N̄ᵀ`, `M̄ = Ūᵀ U₀`, `N̄ = V̄ᵀ V₀`, on
`[t₀, t₀ + h]`. The result is `Ȳ₁ = Ū S̄(t₁) V̄ᵀ`. As everywhere in the library, `orth(…)` is any
orthonormal system whose range contains the given columns. -/
structure IsGalerkinPart {r k rb : ℕ} (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Uh : Matrix m (Fin k) ℝ) (Vh : Matrix n (Fin k) ℝ) (Yh : Matrix m n ℝ)
    (Ub : Matrix m (Fin rb) ℝ) (Vb : Matrix n (Fin rb) ℝ) (Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ) :
    Prop where
  orthUb : Ubᵀ * Ub = 1
  orthVb : Vbᵀ * Vb = 1
  capU : Ub * Ubᵀ * Uh = Uh
  capF : Ub * Ubᵀ * (h • F (t₀ + h / 2) Yh * Vh) = h • F (t₀ + h / 2) Yh * Vh
  capV : Vb * Vbᵀ * Vh = Vh
  capFt : Vb * Vbᵀ * (h • (F (t₀ + h / 2) Yh)ᵀ * Uh) = h • (F (t₀ + h / 2) Yh)ᵀ * Uh
  sSol : ODESolution (MatrixBUG.sField Ub Vb F) Sb t₀ (t₀ + h)
  sStart : Sb t₀ = Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb)

namespace IsGalerkinPart

variable {r k rb : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ h : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {Uh : Matrix m (Fin k) ℝ}
  {Vh : Matrix n (Fin k) ℝ} {Yh : Matrix m n ℝ} {Ub : Matrix m (Fin rb) ℝ}
  {Vb : Matrix n (Fin rb) ℝ} {Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ}

/-- The full-space projector `P̄ Q̄` of the Galerkin step is orthogonal. -/
lemma proj (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb) :
    IsOrthProj (galerkinProj Ub Vb : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  isOrthProj_galProj hg.orthUb hg.orthVb

lemma capF' (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb) (hh : 0 < h) :
    Ub * Ubᵀ * (F (t₀ + h / 2) Yh * Vh) = F (t₀ + h / 2) Yh * Vh := by
  have := hg.capF
  simp only [Matrix.smul_mul, Matrix.mul_smul] at this
  exact smul_right_injective _ hh.ne' this

lemma capFt' (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb) (hh : 0 < h) :
    Vb * Vbᵀ * ((F (t₀ + h / 2) Yh)ᵀ * Uh) = (F (t₀ + h / 2) Yh)ᵀ * Uh := by
  have := hg.capFt
  simp only [Matrix.smul_mul, Matrix.mul_smul] at this
  exact smul_right_injective _ hh.ne' this

/-- The Galerkin projector captures `F(t_{1/2}, Yh)` up to its normal component at `(Uh, Vh)`. -/
theorem norm_normal_le (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb) (hh : 0 < h) :
    ‖(1 - galerkinProj Ub Vb) (F (t₀ + h / 2) Yh)‖
      ≤ ‖(1 - tangentProj Uh Vh) (F (t₀ + h / 2) Yh)‖ :=
  norm_one_sub_galerkin_le hg.orthUb hg.orthVb hg.capU hg.capV (hg.capF' hh) (hg.capFt' hh)

/-- The Galerkin step starts at `Y₀`: `Ū S̄(t₀) V̄ᵀ = Y₀`, if the ranges of `Ū`, `V̄` contain those
of `U₀`, `V₀`. -/
theorem start_eq (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb)
    (capU₀ : Ub * Ubᵀ * U₀ = U₀) (capV₀ : Vb * Vbᵀ * V₀ = V₀) :
    Ub * Sb t₀ * Vbᵀ = U₀ * S₀ * V₀ᵀ := by
  calc Ub * Sb t₀ * Vbᵀ = galerkinProj Ub Vb (U₀ * S₀ * V₀ᵀ) := by
        rw [galProj_apply, leftProj_apply, rightProj_apply', hg.sStart]
        simp only [Matrix.mul_assoc]
    _ = U₀ * S₀ * V₀ᵀ := galProj_fix S₀ capU₀ capV₀

/-- **Parts (b), (c) of the proof of Theorem 1**: if the ranges of `Ū`, `V̄` contain those of `U₀`,
`V₀`, then `Ȳ₁` is a Galerkin trajectory started at `Y₀` and
`‖Ȳ₁ - A(t₁)‖ ≤ (e^{L h} - 1) (θ + M₂ h²) + θ`, `θ = M₃ h³/24 + h (L η + ε')`. -/
theorem error (hg : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh Yh Ub Vb Sb)
    (capU₀ : Ub * Ubᵀ * U₀ = U₀) (capV₀ : Vb * Vbᵀ * V₀ = V₀) {L M₂ M₃ η ε' : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hh : 0 < h) {A a₁ a₂ a₃ : ℝ → Matrix m n ℝ}
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hD : HasDerivData A a₁ a₂ a₃ t₀ (t₀ + h) M₂ M₃) (hη : ‖Yh - A (t₀ + h / 2)‖ ≤ η)
    (hn : ‖(1 - tangentProj Uh Vh) (F (t₀ + h / 2) Yh)‖ ≤ ε') :
    ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤
      (Real.exp (L * h) - 1) * (M₃ * h ^ 3 / 24 + h * (L * η + ε') + M₂ * h ^ 2)
        + (M₃ * h ^ 3 / 24 + h * (L * η + ε')) := by
  have hstart := hg.start_eq capU₀ capV₀
  have hfix : galerkinProj Ub Vb (A t₀) = A t₀ := by rw [hA₀]; exact galProj_fix S₀ capU₀ capV₀
  have hn' : ‖(1 - galerkinProj Ub Vb) (F (t₀ + h / 2) Yh)‖ ≤ ε' := (hg.norm_normal_le hh).trans hn
  have hS₀ : (fun t => Ub * Sb t * Vbᵀ) t₀ = A t₀ := hstart.trans hA₀.symm
  exact midpoint_galerkin_error (YS := fun t => Ub * Sb t * Vbᵀ) hg.proj hF hL hh hA hD hfix hη hn'
    (odeSolution_galProj hg.sSol) hS₀

end IsGalerkinPart

end Galerkin

/-! ### The midpoint BUG (4r) step: Theorem 1 -/

section Step4r

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **One step of the Midpoint BUG (4r) integrator** (arXiv 2402.08607, Section 3, Steps 1 and 2)
from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` with step size `h`: an augmented BUG step of size `h/2`
(`MatrixBUG.IsRankAdaptiveStep`, without truncation) gives `Ŷ_{1/2} = Û Ŝ(t₁/₂) V̂ᵀ`, followed by
the Galerkin step `IsGalerkinPart` in the bases `Ū = orth(Û, h F V̂)`, `V̄ = orth(V̂, h Fᵀ Û)`. -/
structure IsMidpoint4rStep {r rh rb : ℕ} (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Uh : Matrix m (Fin rh) ℝ) (Vh : Matrix n (Fin rh) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
    (Lf : ℝ → Matrix n (Fin r) ℝ) (Sh : ℝ → Matrix (Fin rh) (Fin rh) ℝ)
    (Ub : Matrix m (Fin rb) ℝ) (Vb : Matrix n (Fin rb) ℝ)
    (Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ) : Prop where
  half : MatrixBUG.IsRankAdaptiveStep F 0 t₀ (t₀ + h / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
    (Uh * Sh (t₀ + h / 2) * Vhᵀ)
  galerkin : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh (Uh * Sh (t₀ + h / 2) * Vhᵀ) Ub Vb Sb

variable {r rh rb : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ τ h L B ε ε' ρ H M₂ M₃ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {A a₁ a₂ a₃ : ℝ → Matrix m n ℝ}

/-- The BUG half step in the augmented bases is an abstract `IsBUGStep` under assumption (16)
near the exact solution from `Y₀`: the K-, L-step end points stay within `2 B τ` of `A(t)`, and
factored points are allowed by `NormalBoundNear.factored`. -/
theorem isBUGStep_of_aug {k k' : Type*} [Fintype k] [Fintype k'] [DecidableEq k] [DecidableEq k']
    {Ua : Matrix m k ℝ} {Va : Matrix n k' ℝ} {Sa : ℝ → Matrix k k' ℝ} {ϑ : ℝ} {Y₁ : Matrix m n ℝ}
    (hs : MatrixBUG.IsRankAdaptiveStep F ϑ t₀ (t₀ + τ) U₀ S₀ V₀ Ua Va K Lf Sa Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hτ : 0 ≤ τ)
    (hA : ODESolution F A t₀ (t₀ + τ)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : 2 * B * τ < ρ)
    (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + τ)) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj Ua) (rightProj Va) t₀ (t₀ + τ)
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => Ua * Sa t * Vaᵀ) := by
  classical
  have hmem : t₀ + τ ∈ Icc t₀ (t₀ + τ) := ⟨by linarith, le_rfl⟩
  refine
    { projP₀ := isOrthProj_leftProj hs.orthU₀
      projQ₀ := isOrthProj_rightProj hs.orthV₀
      projP₁ := isOrthProj_leftProj hs.orthUa
      projQ₁ := isOrthProj_rightProj hs.orthVa
      comm₁ := leftProj_rightProj_comm Ua Va
      kSol := MatrixBUG.odeSolution_kField hs.kSol
      kStart := by rw [hs.kStart]
      kCap := by rw [leftProj_apply, ← Matrix.mul_assoc, hs.kCap]
      kNormal := fun t ht => ?_
      lSol := MatrixBUG.odeSolution_lField hs.lSol
      lStart := by
        rw [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      lCap := by
        have hT : (Lf (t₀ + τ))ᵀ * Va * Vaᵀ = (Lf (t₀ + τ))ᵀ := transpose_mul_cap hs.lCap
        rw [rightProj_apply, Matrix.mul_assoc U₀, Matrix.mul_assoc U₀, hT]
      lNormal := fun t ht => ?_
      sSol := MatrixBUG.odeSolution_sField hs.sSol
      sStart := hs.ys_start }
  · obtain ⟨U', hU', hcap, hin⟩ := hs.exists_kBasis
    have hd : ‖K (t₀ + τ) * V₀ᵀ - A t‖ < ρ := lt_of_le_of_lt
      (near_of_proj (isOrthProj_rightProj hs.orthV₀) hB (MatrixBUG.odeSolution_kField hs.kSol) hA
        (by rw [hs.kStart, hA₀]) hmem ht) hρ
    rw [one_sub_leftProj_one_sub_rightProj_apply]
    have hK' : K (t₀ + τ) * V₀ᵀ = U' * (U'ᵀ * K (t₀ + τ)) * V₀ᵀ := by
      rw [← Matrix.mul_assoc, hcap]
    rw [hK'] at hd ⊢
    exact (MatrixBUG.norm_normal_le_of_left hs.orthUa hin V₀ _).trans
      (hN.factored hF hL ht _ hU' hs.orthV₀ hd)
  · obtain ⟨V', hV', hcap, hin⟩ := hs.exists_lBasis
    have hd : ‖U₀ * (Lf (t₀ + τ))ᵀ - A t‖ < ρ := lt_of_le_of_lt
      (near_of_proj (isOrthProj_leftProj hs.orthU₀) hB (MatrixBUG.odeSolution_lField hs.lSol) hA
        (by rw [hs.lStart, hA₀, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_assoc]) hmem ht) hρ
    rw [MatrixBUG.one_sub_rightProj_one_sub_leftProj_apply]
    have hL' : U₀ * (Lf (t₀ + τ))ᵀ = U₀ * ((Lf (t₀ + τ))ᵀ * V') * V'ᵀ := by
      rw [Matrix.mul_assoc U₀, transpose_mul_cap hcap]
    rw [hL'] at hd ⊢
    exact (MatrixBUG.norm_normal_le_of_right hs.orthVa hin U₀ _).trans
      (hN.factored hF hL ht _ hs.orthU₀ hV' hd)

namespace IsMidpoint4rStep

variable {Uh : Matrix m (Fin rh) ℝ} {Vh : Matrix n (Fin rh) ℝ}
  {Sh : ℝ → Matrix (Fin rh) (Fin rh) ℝ} {Ub : Matrix m (Fin rb) ℝ} {Vb : Matrix n (Fin rb) ℝ}
  {Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ}

/-- `Ū` contains `U₀` through `Û`, and `V̄` contains `V₀` through `V̂`. -/
lemma capU₀ (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    Ub * Ubᵀ * U₀ = U₀ := by
  calc Ub * Ubᵀ * U₀ = Ub * Ubᵀ * (Uh * Uhᵀ * U₀) := by rw [hs.half.augU]
    _ = (Ub * Ubᵀ * Uh) * Uhᵀ * U₀ := by simp only [Matrix.mul_assoc]
    _ = U₀ := by rw [hs.galerkin.capU, hs.half.augU]

lemma capV₀ (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) :
    Vb * Vbᵀ * V₀ = V₀ := by
  calc Vb * Vbᵀ * V₀ = Vb * Vbᵀ * (Vh * Vhᵀ * V₀) := by rw [hs.half.augV]
    _ = (Vb * Vbᵀ * Vh) * Vhᵀ * V₀ := by simp only [Matrix.mul_assoc]
    _ = V₀ := by rw [hs.galerkin.capV, hs.half.augV]

/-- **Algorithm of arXiv 2402.08607, Section 3: structure of the Galerkin step.**  The projectors
`P̄ X = Ū Ūᵀ X` and `Q̄ X = X V̄ V̄ᵀ` commute, `P̄ Q̄` fixes `Y₀` and the tangential part
`F_T = P_r̂(Ŷ_{1/2}) F(t_{1/2}, Ŷ_{1/2})`, and `Ū S̄ V̄ᵀ` is the Galerkin trajectory
`Y' = P̄ Q̄ F(t, Y)` from `Y₀`. -/
theorem algorithm (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb) (hh : 0 < h) :
    (∀ X : Matrix m n ℝ, leftProj Ub (rightProj Vb X) = rightProj Vb (leftProj Ub X)) ∧
      galerkinProj Ub Vb (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ ∧
      galerkinProj Ub Vb (tangentProj Uh Vh (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ)))
        = tangentProj Uh Vh (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ)) ∧
      ODESolution (fun t x => galerkinProj Ub Vb (F t x)) (fun t => Ub * Sb t * Vbᵀ) t₀ (t₀ + h) ∧
      Ub * Sb t₀ * Vbᵀ = U₀ * S₀ * V₀ᵀ :=
  ⟨leftProj_rightProj_comm Ub Vb, galProj_fix S₀ hs.capU₀ hs.capV₀,
    galProj_tangent hs.galerkin.capU hs.galerkin.capV (hs.galerkin.capF' hh)
      (hs.galerkin.capFt' hh),
    odeSolution_galProj hs.galerkin.sSol, hs.galerkin.start_eq hs.capU₀ hs.capV₀⟩

/-- **Theorem 1 of arXiv 2402.08607 (robust local error), Midpoint BUG (4r), with an explicit bound
on `A''`.**  Let `F` be `L`-Lipschitz and bounded by `B` (15), let `A` be the exact solution with
`A(t₀) = Y₀ = U₀ S₀ V₀ᵀ`, with `‖A''‖ ≤ M₂`, `‖A'''‖ ≤ M₃` on the step, and let (16) hold on the
step with `ε = ε_r` at rank `r` and `ε' = ε_r̂` at rank `r̂`, in the `ρ`-neighbourhood of `A`, where
`B h < ρ`.  Then for `0 < h ≤ H`,

    ‖Ȳ₁ - A(t₁)‖ ≤ C h (h² + h ε_r + ε_r̂),   `C = midC L B M₂ M₃ H`.

Difference from the paper: no invertibility of `S₀` is needed; the paper does not list `M₂`, and see
`local_error_le` for the form with `M₃` only. -/
theorem local_error_of_second (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hh : 0 < h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hD : HasDerivData A a₁ a₂ a₃ t₀ (t₀ + h) M₂ M₃) (hρ : B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) (hε' : NormalBoundNear F rh ε' A ρ t₀ (t₀ + h)) :
    ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤ midC L B M₂ M₃ H * h * (h ^ 2 + h * ε + ε') := by
  classical
  have hh2 : 0 ≤ h / 2 := by linarith
  have hsub : t₀ + h / 2 ≤ t₀ + h := by linarith
  have hA' : ODESolution F A t₀ (t₀ + h / 2) := hA.mono le_rfl hsub
  have hρ' : 2 * B * (h / 2) < ρ := by linarith
  have hb := isBUGStep_of_aug hs.half hF hL hB hh2 hA' hA₀ hρ'
    (hε.mono_time le_rfl hsub)
  have hmem : t₀ ∈ Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hmid : t₀ + h / 2 ∈ Icc t₀ (t₀ + h) := ⟨by linarith, hsub⟩
  have hmid' : t₀ + h / 2 ∈ Icc t₀ (t₀ + h / 2) := ⟨by linarith, le_rfl⟩
  have hρ0 : 0 < ρ := lt_of_le_of_lt (mul_nonneg hB.nonneg hh.le) hρ
  have hε0 : 0 ≤ ε := hε.nonneg hF hL hmem S₀ hs.half.orthU₀ hs.half.orthV₀
    (by rw [hA₀, sub_self, norm_zero]; exact hρ0)
  have hη := hb.local_error_le hF hL hB rfl hh2 (H := H) (by linarith) hA' hA₀
  have hd : ‖Uh * Sh (t₀ + h / 2) * Vhᵀ - A (t₀ + h / 2)‖ < ρ := by
    have h1 := near_of_proj (isOrthProj_galProj hs.half.orthUa hs.half.orthVa) hB
      (odeSolution_galProj hs.half.sSol) hA' (hs.half.start_eq.trans hA₀.symm) hmid' hmid'
    linarith
  have hn : ‖(1 - tangentProj Uh Vh) (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ))‖ ≤ ε' := by
    rw [one_sub_tangentProj_apply]
    exact hε'.factored hF hL hmid _ hs.half.orthUa hs.half.orthVa hd
  have hε'0 : 0 ≤ ε' := (norm_nonneg _).trans hn
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hD.b₂ t₀ hmem)
  have hM₃ : 0 ≤ M₃ := (norm_nonneg _).trans (hD.b₃ t₀ hmem)
  exact (hs.galerkin.error hs.capU₀ hs.capV₀ hF hL hh hA hA₀ hD hη hn).trans
    (midpoint_scalar hL hB.nonneg hM₂ hM₃ hh.le hhH hε0 hε'0)

/-- **Theorem 1 of arXiv 2402.08607 (robust local error), Midpoint BUG (4r).**  Let `F` be
`L`-Lipschitz and bounded by `B` (15).  Let `A` be an exact solution on `[a, b] ⊇ [t₀, t₀ + h]`,
`a < b` (the paper's `[0, T]`), `C³` with `‖A'''‖ ≤ M₃`, with `A(t₀) = Y₀ = U₀ S₀ V₀ᵀ`, and let (16)
hold near `A` on the step, for rank `r` with `ε_r` and for rank `r̂` with `ε_r̂`, in a neighbourhood
of radius `ρ > B h`.  Then for `0 < h ≤ H`

    ‖Ȳ₁ - A(t₁)‖ ≤ C h (h² + h ε_r + ε_r̂),

with `C = midC L B (secondBound B M₃ (b - a)) M₃ H`, so independently of singular values, of `m, n`
and of the ranks.

Differences from the paper: `C` also depends on the length `b - a`, through the bound of `A''`; the
paper lists only "the bound of third derivatives", but its proof uses `R'' = O(1)`, and a bound of
`A'''` alone controls `A''` only together with `B` and the length of the interval
(`norm_deriv_le_secondBound`).  `S₀` need not be invertible.  (16) is used for factored points with
possibly singular `S` by `NormalBoundNear.factored`. -/
theorem local_error_le (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hh : 0 < h) (hhH : h ≤ H)
    {a b : ℝ} (hab : a < b) (ha : a ≤ t₀) (hb : t₀ + h ≤ b) (hA : ODESolution F A a b)
    (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) (hε' : NormalBoundNear F rh ε' A ρ t₀ (t₀ + h)) :
    ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤
      midC L B (secondBound B M₃ (b - a)) M₃ H * h * (h ^ 2 + h * ε + ε') :=
  hs.local_error_of_second hF hL hB hh hhH (hA.mono ha hb) hA₀
    ((hasDerivData_of_contDiffOn hab hB hA hA3 hM₃).mono ha hb) hρ hε hε'

end IsMidpoint4rStep

end Step4r

/-! ### The Midpoint BUG (3r) variant: Remark 5 -/

section Step3r

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **One step of the Midpoint BUG (3r) integrator** (arXiv 2402.08607, Remark 1, eq. (14)): a
fixed-rank BUG step of size `h/2` (`MatrixBUG.IsStep`) gives `Y_{1/2} = U_{1/2} S V_{1/2}ᵀ` of rank
`r`, followed by the Galerkin step in the bases `Ū = orth(U₀, U_{1/2}, h F V_{1/2})`,
`V̄ = orth(V₀, V_{1/2}, h Fᵀ U_{1/2})`. -/
structure IsMidpoint3rStep {r rb : ℕ} (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ)
    (U₀ : Matrix m (Fin r) ℝ) (S₀ : Matrix (Fin r) (Fin r) ℝ) (V₀ : Matrix n (Fin r) ℝ)
    (Uh : Matrix m (Fin r) ℝ) (Vh : Matrix n (Fin r) ℝ) (K : ℝ → Matrix m (Fin r) ℝ)
    (Lf : ℝ → Matrix n (Fin r) ℝ) (Sh : ℝ → Matrix (Fin r) (Fin r) ℝ)
    (Ub : Matrix m (Fin rb) ℝ) (Vb : Matrix n (Fin rb) ℝ)
    (Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ) : Prop where
  half : MatrixBUG.IsStep F t₀ (t₀ + h / 2) U₀ S₀ V₀ Uh Vh K Lf Sh
  galerkin : IsGalerkinPart F t₀ h U₀ S₀ V₀ Uh Vh (Uh * Sh (t₀ + h / 2) * Vhᵀ) Ub Vb Sb
  /-- `Ū` contains `U₀`: in (14) this is an explicit part of the augmentation. -/
  capU₀ : Ub * Ubᵀ * U₀ = U₀
  /-- `V̄` contains `V₀`. -/
  capV₀ : Vb * Vbᵀ * V₀ = V₀

variable {r rb : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ τ h L B ε ρ H M₂ M₃ : ℝ}
  {U₀ U₁ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ V₁ : Matrix n (Fin r) ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ}
  {S : ℝ → Matrix (Fin r) (Fin r) ℝ} {A a₁ a₂ a₃ : ℝ → Matrix m n ℝ}

/-- The fixed-rank half step is an abstract `IsBUGStep` under assumption (16) near the exact
solution. -/
theorem isBUGStep_of_fixed (hs : MatrixBUG.IsStep F t₀ (t₀ + τ) U₀ S₀ V₀ U₁ V₁ K Lf S)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hτ : 0 ≤ τ)
    (hA : ODESolution F A t₀ (t₀ + τ)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : 2 * B * τ < ρ)
    (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + τ)) :
    IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁) t₀ (t₀ + τ)
      (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => U₁ * S t * V₁ᵀ) := by
  classical
  have hmem : t₀ + τ ∈ Icc t₀ (t₀ + τ) := ⟨by linarith, le_rfl⟩
  refine hs.isBUGStep_of_normal (fun t ht => ?_) (fun t ht => ?_)
  · have hd : ‖K (t₀ + τ) * V₀ᵀ - A t‖ < ρ := lt_of_le_of_lt
      (near_of_proj (isOrthProj_rightProj hs.orthV₀) hB (MatrixBUG.odeSolution_kField hs.kSol) hA
        (by rw [hs.kStart, hA₀]) hmem ht) hρ
    have hK' : K (t₀ + τ) * V₀ᵀ = U₁ * (U₁ᵀ * K (t₀ + τ)) * V₀ᵀ := by
      rw [← Matrix.mul_assoc, hs.kCap]
    rw [hK'] at hd ⊢
    exact hN.factored hF hL ht _ hs.orthU₁ hs.orthV₀ hd
  · have hd : ‖U₀ * (Lf (t₀ + τ))ᵀ - A t‖ < ρ := lt_of_le_of_lt
      (near_of_proj (isOrthProj_leftProj hs.orthU₀) hB (MatrixBUG.odeSolution_lField hs.lSol) hA
        (by rw [hs.lStart, hA₀, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_assoc]) hmem ht) hρ
    have hL' : U₀ * (Lf (t₀ + τ))ᵀ = U₀ * ((Lf (t₀ + τ))ᵀ * V₁) * V₁ᵀ := by
      rw [Matrix.mul_assoc U₀, transpose_mul_cap hs.lCap]
    rw [hL'] at hd ⊢
    exact hN.factored hF hL ht _ hs.orthU₀ hs.orthV₁ hd

/-- The result of a fixed-rank BUG step stays within `4 B τ` of the exact solution from `Y₀`: its
S-step moves by at most `B τ`, its start `P₁ Q₁ Y₀` differs from `Y₀` by at most `2 B τ` and `A`
moves by at most `B τ`. -/
theorem fixed_near (hb : IsBUGStep F ε (leftProj U₀) (rightProj V₀) (leftProj U₁) (rightProj V₁)
      t₀ (t₀ + τ) (U₀ * S₀ * V₀ᵀ) (fun t => K t * V₀ᵀ) (fun t => U₀ * (Lf t)ᵀ)
      (fun t => U₁ * S t * V₁ᵀ)) (hB : IsBoundedField F B) (hτ : 0 ≤ τ)
    (hA : ODESolution F A t₀ (t₀ + τ)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ‖U₁ * S (t₀ + τ) * V₁ᵀ - A (t₀ + τ)‖ ≤ 4 * B * τ := by
  have hmem : t₀ + τ ∈ Icc t₀ (t₀ + τ) := ⟨by linarith, le_rfl⟩
  have hk : ‖(1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ)‖ ≤ B * τ := by
    have h1 := hb.kSol.norm_sub_start_le_of_proj hB hb.projQ₀ rfl (t₀ + τ) hmem
    have e : (1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ)
        = (1 - leftProj U₁) (U₀ * S₀ * V₀ᵀ - K (t₀ + τ) * V₀ᵀ) := by
      rw [map_sub _ _ (K (t₀ + τ) * V₀ᵀ)]
      have : (1 - leftProj U₁) (K (t₀ + τ) * V₀ᵀ) = 0 := by
        have hc : leftProj U₁ (K (t₀ + τ) * V₀ᵀ) = K (t₀ + τ) * V₀ᵀ := hb.kCap
        change K (t₀ + τ) * V₀ᵀ - leftProj U₁ (K (t₀ + τ) * V₀ᵀ) = 0
        rw [hc, sub_self]
      rw [this, sub_zero]
    rw [e]
    refine (hb.projP₁.compl.norm_le _).trans ?_
    rw [norm_sub_rev, ← hb.kStart]
    exact h1
  have hl : ‖(1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ)‖ ≤ B * τ := by
    have h1 := hb.lSol.norm_sub_start_le_of_proj hB hb.projP₀ rfl (t₀ + τ) hmem
    have e : (1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ)
        = (1 - rightProj V₁) (U₀ * S₀ * V₀ᵀ - U₀ * (Lf (t₀ + τ))ᵀ) := by
      rw [map_sub _ _ (U₀ * (Lf (t₀ + τ))ᵀ)]
      have : (1 - rightProj V₁) (U₀ * (Lf (t₀ + τ))ᵀ) = 0 := by
        have hc : rightProj V₁ (U₀ * (Lf (t₀ + τ))ᵀ) = U₀ * (Lf (t₀ + τ))ᵀ := hb.lCap
        change U₀ * (Lf (t₀ + τ))ᵀ - rightProj V₁ (U₀ * (Lf (t₀ + τ))ᵀ) = 0
        rw [hc, sub_self]
      rw [this, sub_zero]
    rw [e]
    refine (hb.projQ₁.compl.norm_le _).trans ?_
    rw [norm_sub_rev, ← hb.lStart]
    exact h1
  have hsS := hb.sSol.norm_sub_start_le_of_proj hB (P := leftProj U₁ * rightProj V₁)
    (hb.projP₁.mul hb.projQ₁ hb.comm₁) rfl (t₀ + τ) hmem
  have hst := norm_sub_apply_apply_le (Q := rightProj V₁) hb.projP₁ (U₀ * S₀ * V₀ᵀ)
  have hA1 := hA.norm_sub_start_le hB rfl (t₀ + τ) hmem
  rw [hA₀] at hA1
  have e : U₁ * S (t₀ + τ) * V₁ᵀ - A (t₀ + τ)
      = (U₁ * S (t₀ + τ) * V₁ᵀ - U₁ * S t₀ * V₁ᵀ)
        - ((U₀ * S₀ * V₀ᵀ - leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)))
          + (A (t₀ + τ) - U₀ * S₀ * V₀ᵀ)) := by
    have hs₀ : U₁ * S t₀ * V₁ᵀ = leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) := hb.sStart
    rw [hs₀]; abel
  rw [e]
  have hs₀ : U₁ * S t₀ * V₁ᵀ = leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ)) := hb.sStart
  calc _ ≤ ‖U₁ * S (t₀ + τ) * V₁ᵀ - U₁ * S t₀ * V₁ᵀ‖
        + (‖U₀ * S₀ * V₀ᵀ - leftProj U₁ (rightProj V₁ (U₀ * S₀ * V₀ᵀ))‖
          + ‖A (t₀ + τ) - U₀ * S₀ * V₀ᵀ‖) :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ B * τ + (B * τ + B * τ + B * τ) := by
        refine add_le_add hsS (add_le_add (hst.trans (add_le_add hk hl)) hA1)
    _ = 4 * B * τ := by ring

namespace IsMidpoint3rStep

variable {Uh : Matrix m (Fin r) ℝ} {Vh : Matrix n (Fin r) ℝ} {Sh : ℝ → Matrix (Fin r) (Fin r) ℝ}
  {Ub : Matrix m (Fin rb) ℝ} {Vb : Matrix n (Fin rb) ℝ} {Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ}

/-- **Remark 5 of arXiv 2402.08607 (Midpoint BUG (3r)), with an explicit bound on `A''`.**  With the
assumptions of Theorem 1 at rank `r` only, in a neighbourhood of radius `ρ > 2 B h`:
`‖Ȳ₁ - A(t₁)‖ ≤ C' h (h² + ε_r)`, `C' = (1 + H) midC L B M₂ M₃ H`.  The radius is `2 B h` rather
than `B h` because the fixed-rank half step does not start at `Y₀`. -/
theorem local_error_of_second (hs : IsMidpoint3rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hh : 0 < h) (hhH : h ≤ H)
    (hA : ODESolution F A t₀ (t₀ + h)) (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ)
    (hD : HasDerivData A a₁ a₂ a₃ t₀ (t₀ + h) M₂ M₃) (hρ : 2 * B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) :
    ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤ (1 + H) * midC L B M₂ M₃ H * h * (h ^ 2 + ε) := by
  classical
  have hh2 : 0 ≤ h / 2 := by linarith
  have hsub : t₀ + h / 2 ≤ t₀ + h := by linarith
  have hA' : ODESolution F A t₀ (t₀ + h / 2) := hA.mono le_rfl hsub
  have hB0 := hB.nonneg
  have hρ' : 2 * B * (h / 2) < ρ := by nlinarith [mul_nonneg hB0 hh.le]
  have hb := isBUGStep_of_fixed hs.half hF hL hB hh2 hA' hA₀ hρ' (hε.mono_time le_rfl hsub)
  have hmem : t₀ ∈ Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hmid : t₀ + h / 2 ∈ Icc t₀ (t₀ + h) := ⟨by linarith, hsub⟩
  have hρ0 : 0 < ρ := lt_of_le_of_lt (by positivity) hρ
  have hε0 : 0 ≤ ε := hε.nonneg hF hL hmem S₀ hs.half.orthU₀ hs.half.orthV₀
    (by rw [hA₀, sub_self, norm_zero]; exact hρ0)
  have hη := hb.local_error_le hF hL hB rfl hh2 (H := H) (by linarith) hA' hA₀
  have hd : ‖Uh * Sh (t₀ + h / 2) * Vhᵀ - A (t₀ + h / 2)‖ < ρ := by
    have h1 := fixed_near hb hB hh2 hA' hA₀
    linarith
  have hn : ‖(1 - tangentProj Uh Vh) (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ))‖ ≤ ε := by
    rw [one_sub_tangentProj_apply]
    exact hε.factored hF hL hmid _ hs.half.orthU₁ hs.half.orthV₁ hd
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hD.b₂ t₀ hmem)
  have hM₃ : 0 ≤ M₃ := (norm_nonneg _).trans (hD.b₃ t₀ hmem)
  have hH : 0 ≤ H := hh.le.trans hhH
  have h1 := (hs.galerkin.error hs.capU₀ hs.capV₀ hF hL hh hA hA₀ hD hη hn).trans
    (midpoint_scalar hL hB0 hM₂ hM₃ hh.le hhH hε0 hε0)
  have hC := midC_nonneg hL hB0 hM₂ hM₃ hH
  refine h1.trans ?_
  have h2 : h ^ 2 + h * ε + ε ≤ (1 + H) * (h ^ 2 + ε) := by
    nlinarith [mul_nonneg hH (sq_nonneg h), mul_le_mul_of_nonneg_right hhH hε0]
  calc midC L B M₂ M₃ H * h * (h ^ 2 + h * ε + ε)
      ≤ midC L B M₂ M₃ H * h * ((1 + H) * (h ^ 2 + ε)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hh.le)
    _ = _ := by ring

/-- **Remark 5 of arXiv 2402.08607 (Midpoint BUG (3r)).**  Under the assumptions of Theorem 1 at
rank `r` only (`local_error_le` for the 4r scheme), in a neighbourhood of radius `ρ > 2 B h`:

    ‖Ȳ₁ - A(t₁)‖ ≤ C h (h² + ε_r),

with `C = (1 + H) midC L B (secondBound B M₃ (b - a)) M₃ H`. -/
theorem local_error_le (hs : IsMidpoint3rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hh : 0 < h) (hhH : h ≤ H)
    {a b : ℝ} (hab : a < b) (ha : a ≤ t₀) (hb : t₀ + h ≤ b) (hA : ODESolution F A a b)
    (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : 2 * B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) :
    ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤
      (1 + H) * midC L B (secondBound B M₃ (b - a)) M₃ H * h * (h ^ 2 + ε) :=
  hs.local_error_of_second hF hL hB hh hhH (hA.mono ha hb) hA₀
    ((hasDerivData_of_contDiffOn hab hB hA hA3 hM₃).mono ha hb) hρ hε

end IsMidpoint3rStep

end Step3r

/-! ### Theorem 2: the global error -/

section Global

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Theorem 2 of arXiv 2402.08607 (robust second-order global error), with an explicit bound on
second derivatives.**  This is the main form of `midpoint_global_error`, for exact flows `Φ j` given
on one step `[tⱼ, tⱼ₊₁]` only, with `‖Φ j''‖ ≤ M₂`, `‖Φ j'''‖ ≤ M₃`.

The proof is Lady Windermere's fan, with an induction that keeps the iterates in the neighbourhood:
(16) is assumed only near `A`, and `hsmall` says that the error bound itself, plus `B h`, stays
below the radius `ρ`. -/
theorem midpoint_global_error_of_second {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε ε' ϑ ρ δ T H M₂ M₃ t₀ h : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) (hε'0 : 0 ≤ ε') (hϑ0 : 0 ≤ ϑ) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (hh : 0 < h) (hhH : h ≤ H) {N : ℕ} (hNT : (N : ℝ) * h ≤ T)
    {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h)) {r rh rb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Uh : (j : ℕ) → Matrix m (Fin (rh j)) ℝ}
    {Vh : (j : ℕ) → Matrix n (Fin (rh j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sh : (j : ℕ) → ℝ → Matrix (Fin (rh j)) (Fin (rh j)) ℝ}
    {Ub : (j : ℕ) → Matrix m (Fin (rb j)) ℝ} {Vb : (j : ℕ) → Matrix n (Fin (rb j)) ℝ}
    {Sb : (j : ℕ) → ℝ → Matrix (Fin (rb j)) (Fin (rb j)) ℝ}
    (hstep : ∀ j < N, IsMidpoint4rStep F (t₀ + j * h) h (U j) (Sm j) (V j) (Uh j) (Vh j) (K j)
      (Lf j) (Sh j) (Ub j) (Vb j) (Sb j))
    (htrunc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ
      - Ub j * Sb j (t₀ + j * h + h) * (Vb j)ᵀ‖ ≤ ϑ)
    {Φ a₁ a₂ a₃ : ℕ → ℝ → Matrix m n ℝ}
    (hΦ : ∀ j < N, ODESolution F (Φ j) (t₀ + j * h) (t₀ + j * h + h))
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ)
    (hD : ∀ j < N, HasDerivData (Φ j) (a₁ j) (a₂ j) (a₃ j) (t₀ + j * h) (t₀ + j * h + h) M₂ M₃)
    (hN : ∀ j < N, NormalBoundNear F (r j) ε A ρ (t₀ + j * h) (t₀ + j * h + h))
    (hN' : ∀ j < N, NormalBoundNear F (rh j) ε' A ρ (t₀ + j * h) (t₀ + j * h + h))
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + T * (midC L B M₂ M₃ H * (h ^ 2 + h * ε + ε')) + N * ϑ)
      + B * h < ρ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
      + T * Real.exp (L * T) * midC L B M₂ M₃ H * ε'
      + T * Real.exp (L * T) * midC L B M₂ M₃ H * (h * ε)
      + T * Real.exp (L * T) * midC L B M₂ M₃ H * h ^ 2 + Real.exp (L * T) * j * ϑ := by
  have hB0 := hB.nonneg
  have hH : 0 ≤ H := hh.le.trans hhH
  have hC0 : 0 ≤ midC L B M₂ M₃ H := midC_nonneg hL hB0 hM₂ hM₃ hH
  set C := midC L B M₂ M₃ H with hC
  set S := h ^ 2 + h * ε + ε' with hS
  have hS0 : 0 ≤ S := by positivity
  set ℓ := C * h * S + ϑ with hℓ
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hT0 : 0 ≤ T := le_trans (by positivity) hNT
  set X := Real.exp (L * T) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set e := X * (δ + T * (C * S) + N * ϑ) with he
  have hmono : ∀ j : ℕ, j ≤ N → δ + j * ℓ ≤ δ + T * (C * S) + N * ϑ := by
    intro j hj
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
    have h1 : (j : ℝ) * h ≤ T := (mul_le_mul_of_nonneg_right hj' hh.le).trans hNT
    have h2 : (j : ℝ) * h * (C * S) ≤ T * (C * S) :=
      mul_le_mul_of_nonneg_right h1 (mul_nonneg hC0 hS0)
    have h3 : (j : ℝ) * ϑ ≤ N * ϑ := mul_le_mul_of_nonneg_right hj' hϑ0
    have e1 : (j : ℝ) * ℓ = (j : ℝ) * h * (C * S) + j * ϑ := by rw [hℓ]; ring
    rw [e1]; linarith
  have hfan : ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖
      ≤ Real.exp (L * (j * h)) * (δ + j * ℓ) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hδ
    | succ j ih =>
      intro hj
      have hjN : j < N := hj
      have hE := ih hjN.le
      have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hNr : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hj
      have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg hjr hh.le
      have hle : ((j : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hNr hh.le
      have hj1T : ((j : ℝ) + 1) * h ≤ T := hle.trans hNT
      have hAj : ODESolution F A (t₀ + j * h) (t₀ + j * h + h) :=
        hA.mono (by linarith) (by linarith)
      have hexp : Real.exp (L * h) * Real.exp (L * (j * h))
          = Real.exp (L * (((j : ℝ) + 1) * h)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexpT : Real.exp (L * (((j : ℝ) + 1) * h)) ≤ X :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hj1T hL)
      have hp0 : 0 ≤ δ + j * ℓ := by positivity
      have hstab : ∀ t ∈ Icc (t₀ + j * h) (t₀ + j * h + h),
          ‖Φ j t - A t‖ ≤ Real.exp (L * (((j : ℝ) + 1) * h)) * (δ + j * ℓ) := by
        intro t ht
        have h1 := (hΦ j hjN).norm_sub_le_exp hF hL hAj t ht
        rw [hΦ₀ j hjN] at h1
        have h2 : Real.exp (L * (t - (t₀ + j * h))) ≤ Real.exp (L * h) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hL)
        calc ‖Φ j t - A t‖ ≤ Real.exp (L * h) * ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ :=
              h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
          _ ≤ Real.exp (L * h) * (Real.exp (L * (j * h)) * (δ + j * ℓ)) :=
              mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
          _ = _ := by rw [← mul_assoc, hexp]
      have hstab' : ∀ t ∈ Icc (t₀ + j * h) (t₀ + j * h + h), ‖Φ j t - A t‖ ≤ e := fun t ht =>
        (hstab t ht).trans (mul_le_mul hexpT (hmono j hjN.le) hp0 hX0.le)
      have hρ' : B * h < ρ - e := by linarith
      have hloc := (hstep j hjN).local_error_of_second hF hL hB hh hhH (hΦ j hjN) (hΦ₀ j hjN)
        (hD j hjN) hρ' ((hN j hjN).recentre hstab' (by linarith))
        ((hN' j hjN).recentre hstab' (by linarith))
      have hend : t₀ + j * h + h ∈ Icc (t₀ + j * h) (t₀ + j * h + h) := ⟨by linarith, le_rfl⟩
      have hcast : t₀ + ((j + 1 : ℕ) : ℝ) * h = t₀ + j * h + h := by push_cast; ring
      rw [hcast]
      have h4 : ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ - Φ j (t₀ + j * h + h)‖ ≤ ℓ := by
        have := norm_sub_le_norm_sub_add_norm_sub (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ)
          (Ub j * Sb j (t₀ + j * h + h) * (Vb j)ᵀ) (Φ j (t₀ + j * h + h))
        linarith [htrunc j hjN]
      have h5 := norm_sub_le_norm_sub_add_norm_sub (U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ)
        (Φ j (t₀ + j * h + h)) (A (t₀ + j * h + h))
      have h6 := hstab _ hend
      have hE1 : Real.exp (L * (((j + 1 : ℕ) : ℝ) * h)) = Real.exp (L * (((j : ℝ) + 1) * h)) := by
        push_cast; ring_nf
      rw [hE1]
      set Xj := Real.exp (L * (((j : ℝ) + 1) * h)) with hXj
      have hXj1 : 1 ≤ Xj := Real.one_le_exp (by
        have : 0 ≤ ((j : ℝ) + 1) * h := by positivity
        positivity)
      have h7 : ℓ ≤ Xj * ℓ := le_mul_of_one_le_left hℓ0 hXj1
      calc _ ≤ ℓ + Xj * (δ + j * ℓ) := by linarith
        _ ≤ Xj * ℓ + Xj * (δ + j * ℓ) := by linarith
        _ = Xj * (δ + ((j + 1 : ℕ) : ℝ) * ℓ) := by push_cast; ring
  intro j hj
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hjT : (j : ℝ) * h ≤ T := (mul_le_mul_of_nonneg_right hj' hh.le).trans hNT
  have h1 : Real.exp (L * (j * h)) ≤ X := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hjT hL)
  have h2 : δ + j * ℓ ≤ δ + T * (C * S) + j * ϑ := by
    have h3 : (j : ℝ) * h * (C * S) ≤ T * (C * S) :=
      mul_le_mul_of_nonneg_right hjT (mul_nonneg hC0 hS0)
    have e1 : (j : ℝ) * ℓ = (j : ℝ) * h * (C * S) + j * ϑ := by rw [hℓ]; ring
    rw [e1]; linarith
  have hp : 0 ≤ δ + j * ℓ := by positivity
  calc _ ≤ _ := hfan j hj
    _ ≤ X * (δ + T * (C * S) + j * ϑ) := mul_le_mul h1 h2 hp hX0.le
    _ = _ := by rw [hS]; ring

/-- **Theorem 2 of arXiv 2402.08607 (robust second-order global error bound).**  Let `F` be
`L`-Lipschitz and bounded by `B`, and `A` the exact solution from `A(t₀)` on `[t₀, t₀ + N h]`,
`tⱼ = t₀ + j h`, `0 < h ≤ H`, `N h ≤ T`.  Let `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` of rank `rⱼ` be obtained by `N` steps
of the Midpoint BUG (4r) integrator (`IsMidpoint4rStep`, intermediate ranks `r̂ⱼ`, `r̄ⱼ`) with
truncation tolerance `ϑ`, and `‖Y₀ - A(t₀)‖ ≤ δ`.  Let `Φ j` be the exact solutions through
`(tⱼ, Yⱼ)` on `[a, b] ⊇ [t₀, t₀ + N h]`, `a < b`, `C³` with `‖Φ j'''‖ ≤ M₃`.  If (16) holds near `A`
with `ε` at the ranks `rⱼ` and with `ε̂` at the ranks `r̂ⱼ`, within a radius `ρ` exceeding the bound
below plus `B h`, then for `j ≤ N`:

    ‖Yⱼ - A(tⱼ)‖ ≤ c₀ δ + c₁ ε̂ + c₂ h ε + c₃ h² + c₄ j ϑ,

`c₀ = c₄ = e^{L T}`, `c₁ = c₂ = c₃ = T e^{L T} midC L B (secondBound B M₃ (b - a)) M₃ H`.

Differences from the paper: the constants depend explicitly also on `H` and on `b - a` (with
`H = b - a = T` on the paper's `[0, T]` they depend only on `B`, `L`, `T`, `M₃`); `ε`, `ε̂` are
uniform in `j`; the existence of the `Φ j` and their `C³` regularity are hypotheses (the paper's
"bound of the third derivative of exact solutions"); the smallness of the error compared to the
neighbourhood, implicit in the paper, is the explicit hypothesis `hsmall`. -/
theorem midpoint_global_error {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L B ε ε' ϑ ρ δ T H M₃ t₀ h a b : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε0 : 0 ≤ ε) (hε'0 : 0 ≤ ε') (hϑ0 : 0 ≤ ϑ) (hM₃ : 0 ≤ M₃)
    (hh : 0 < h) (hhH : h ≤ H) {N : ℕ} (hNT : (N : ℝ) * h ≤ T) (hab : a < b) (ha : a ≤ t₀)
    (hb : t₀ + N * h ≤ b) {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {r rh rb : ℕ → ℕ}
    {U : (j : ℕ) → Matrix m (Fin (r j)) ℝ} {Sm : (j : ℕ) → Matrix (Fin (r j)) (Fin (r j)) ℝ}
    {V : (j : ℕ) → Matrix n (Fin (r j)) ℝ} {Uh : (j : ℕ) → Matrix m (Fin (rh j)) ℝ}
    {Vh : (j : ℕ) → Matrix n (Fin (rh j)) ℝ} {K : (j : ℕ) → ℝ → Matrix m (Fin (r j)) ℝ}
    {Lf : (j : ℕ) → ℝ → Matrix n (Fin (r j)) ℝ}
    {Sh : (j : ℕ) → ℝ → Matrix (Fin (rh j)) (Fin (rh j)) ℝ}
    {Ub : (j : ℕ) → Matrix m (Fin (rb j)) ℝ} {Vb : (j : ℕ) → Matrix n (Fin (rb j)) ℝ}
    {Sb : (j : ℕ) → ℝ → Matrix (Fin (rb j)) (Fin (rb j)) ℝ}
    (hstep : ∀ j < N, IsMidpoint4rStep F (t₀ + j * h) h (U j) (Sm j) (V j) (Uh j) (Vh j) (K j)
      (Lf j) (Sh j) (Ub j) (Vb j) (Sb j))
    (htrunc : ∀ j < N, ‖U (j + 1) * Sm (j + 1) * (V (j + 1))ᵀ
      - Ub j * Sb j (t₀ + j * h + h) * (Vb j)ᵀ‖ ≤ ϑ)
    {Φ : ℕ → ℝ → Matrix m n ℝ} (hΦ : ∀ j < N, ODESolution F (Φ j) a b)
    (hΦ₀ : ∀ j < N, Φ j (t₀ + j * h) = U j * Sm j * (V j)ᵀ)
    (hΦ3 : ∀ j < N, ContDiffOn ℝ 3 (Φ j) (Icc a b))
    (hM : ∀ j < N, ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 (Φ j) (Icc a b) t‖ ≤ M₃)
    (hN : ∀ j < N, NormalBoundNear F (r j) ε A ρ (t₀ + j * h) (t₀ + j * h + h))
    (hN' : ∀ j < N, NormalBoundNear F (rh j) ε' A ρ (t₀ + j * h) (t₀ + j * h + h))
    (hδ : ‖U 0 * Sm 0 * (V 0)ᵀ - A t₀‖ ≤ δ)
    (hsmall : Real.exp (L * T) * (δ + T * (midC L B (secondBound B M₃ (b - a)) M₃ H
      * (h ^ 2 + h * ε + ε')) + N * ϑ) + B * h < ρ) :
    ∀ j ≤ N, ‖U j * Sm j * (V j)ᵀ - A (t₀ + j * h)‖ ≤ Real.exp (L * T) * δ
      + T * Real.exp (L * T) * midC L B (secondBound B M₃ (b - a)) M₃ H * ε'
      + T * Real.exp (L * T) * midC L B (secondBound B M₃ (b - a)) M₃ H * (h * ε)
      + T * Real.exp (L * T) * midC L B (secondBound B M₃ (b - a)) M₃ H * h ^ 2
      + Real.exp (L * T) * j * ϑ := by
  have hB0 := hB.nonneg
  have hT : 0 < b - a := sub_pos.2 hab
  have hM₂ : 0 ≤ secondBound B M₃ (b - a) := by unfold secondBound; positivity
  have hsub : ∀ j < N, a ≤ t₀ + j * h ∧ t₀ + j * h + h ≤ b := by
    intro j hj
    have hNr : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hj
    have hle : ((j : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hNr hh.le
    have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh.le
    constructor <;> linarith
  exact midpoint_global_error_of_second hF hL hB hε0 hε'0 hϑ0 hM₂ hM₃ hh hhH hNT hA hstep htrunc
    (Φ := Φ)
    (a₁ := fun j => iteratedDerivWithin 1 (Φ j) (Icc a b))
    (a₂ := fun j => iteratedDerivWithin 2 (Φ j) (Icc a b))
    (a₃ := fun j => iteratedDerivWithin 3 (Φ j) (Icc a b))
    (fun j hj => (hΦ j hj).mono (hsub j hj).1 (hsub j hj).2) hΦ₀
    (fun j hj => (hasDerivData_of_contDiffOn hab hB (hΦ j hj) (hΦ3 j hj) (hM j hj)).mono
      (hsub j hj).1 (hsub j hj).2) hN hN' hδ hsmall

end Global

/-! ### Remark 4: truncation -/

section Truncation

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L B ε ρ t₀ h : ℝ} {A : ℝ → Matrix m n ℝ}

/-- One step of the recursion for `dist(A(t), M_{≤ r})`, with (16) only near `A`: this is
`distLR_flow_step` for a neighbourhood instead of the whole of `M_r`. The exact flow is started at
a best approximation `Z` of `A(a)`, which is within `B (a - t₀)` of `A(a)`. -/
theorem distLR_near_step (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) {a τ : ℝ} (hτ : 0 ≤ τ) (ha : t₀ ≤ a)
    (hb : a + τ ≤ t₀ + h) (hA : ODESolution F A t₀ (t₀ + h)) (hrank : (A t₀).rank ≤ r)
    (hρ : B * (h + τ) < ρ) (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) :
    distLR r (A (a + τ)) ≤ Real.exp (L * τ) * distLR r (A a) + 2 * (τ * (4 * L * B * τ + ε)) := by
  classical
  have hB0 := hB.nonneg
  obtain ⟨Z, hZ, hAZ⟩ := exists_best_approx r (A a)
  have hab : a ≤ a + τ := by linarith
  obtain ⟨Φ, hΦ, hΦ₀⟩ := exists_ODESolution hF hB hc hab Z
  have hdZ : ‖A a - Z‖ ≤ B * (a - t₀) := by
    rw [hAZ]
    exact (distLR_le_norm_sub hrank).trans
      ((hA.mono le_rfl (by linarith)).norm_sub_le_of_bounded hB a ⟨ha, le_rfl⟩)
  have hAa : ODESolution F A a (a + τ) := hA.mono ha hb
  have hnear : NearNormalBound F r ε a (a + τ) (Φ a) (B * τ) := by
    intro t ht U V S hU hV hd
    refine hN.factored hF hL ⟨ha.trans ht.1, ht.2.trans hb⟩ S hU hV ?_
    rw [hΦ₀] at hd
    have h1 : ‖A t - A a‖ ≤ B * (t - a) := hAa.norm_sub_le_of_bounded hB t ht
    have h2 : ‖U * S * Vᵀ - A t‖ ≤ ‖U * S * Vᵀ - Z‖ + ‖A a - Z‖ + ‖A t - A a‖ := by
      have e : U * S * Vᵀ - A t = (U * S * Vᵀ - Z) - ((A a - Z) + (A t - A a)) := by abel
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have := norm_add_le (A a - Z) (A t - A a)
      linarith
    have h3 : B * (a - t₀) + B * (t - a) ≤ B * h :=
      calc _ = B * (t - t₀) := by ring
        _ ≤ B * h := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB0
    nlinarith
  have h1 := distLR_flow_le hF hL hB hc rfl hτ hΦ (by rw [hΦ₀]; exact hZ) hε0 hnear
  have h2 := norm_sub_le_exp_of_odeSolution hF hL hab hAa hΦ
  rw [hΦ₀, show a + τ - a = τ by ring, hAZ] at h2
  have h3 := distLR_le_add (r := r) (A (a + τ)) (Φ (a + τ))
  linarith

/-- Grid version of `distLR_near_step`. -/
theorem distLR_near_grid (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) {τ : ℝ} (hτ : 0 ≤ τ) {N : ℕ}
    (hNτ : (N : ℝ) * τ = h) (hA : ODESolution F A t₀ (t₀ + h)) (hrank : (A t₀).rank ≤ r)
    (hρ : B * (h + τ) < ρ) (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) :
    ∀ j ≤ N, distLR r (A (t₀ + j * τ)) ≤
      j * (2 * (τ * (4 * L * B * τ + ε))) * Real.exp (L * (j * τ)) := by
  have hB0 := hB.nonneg
  intro j
  induction j with
  | zero => intro _; simp [distLR_eq_zero_of_rank_le hrank]
  | succ j ih =>
    intro hj
    have hj' : j ≤ N := by omega
    have hjτ : 0 ≤ (j : ℝ) * τ := by positivity
    have hle : ((j + 1 : ℕ) : ℝ) * τ ≤ h := by
      rw [← hNτ]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hτ
    have hstep := distLR_near_step hF hL hB hc hε0 hτ (a := t₀ + j * τ) (by linarith)
      (by push_cast at hle; linarith) hA hrank hρ hN
    have hih := ih hj'
    set c := 2 * (τ * (4 * L * B * τ + ε)) with hcdef
    have hc0 : 0 ≤ c := by positivity
    have ecast : t₀ + j * τ + τ = t₀ + ((j + 1 : ℕ) : ℝ) * τ := by push_cast; ring
    rw [ecast] at hstep
    have e1 : Real.exp (L * τ) * Real.exp (L * (j * τ)) =
        Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have e2 : 1 ≤ Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := Real.one_le_exp (by positivity)
    have hexp0 : 0 ≤ Real.exp (L * τ) := (Real.exp_pos _).le
    have h5 : Real.exp (L * τ) * distLR r (A (t₀ + j * τ)) ≤
        Real.exp (L * τ) * (j * c * Real.exp (L * (j * τ))) :=
      mul_le_mul_of_nonneg_left hih hexp0
    have h6 : Real.exp (L * τ) * (j * c * Real.exp (L * (j * τ))) =
        j * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by
      rw [← e1]; ring
    have h7 : c ≤ c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := le_mul_of_one_le_right hc0 e2
    calc distLR r (A (t₀ + ((j + 1 : ℕ) : ℝ) * τ))
        ≤ Real.exp (L * τ) * distLR r (A (t₀ + j * τ)) + c := hstep
      _ ≤ j * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ))
          + c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by linarith
      _ = ((j + 1 : ℕ) : ℝ) * c * Real.exp (L * (((j + 1 : ℕ) : ℝ) * τ)) := by push_cast; ring

/-- **The distance bound behind Remark 4, with (16) only near `A`**: if `A(t₀)` has rank `≤ r` and
(16) holds at rank `r` in the `ρ`-neighbourhood of `A`, `ρ > B h`, then
`dist(A(t₀ + h), M_{≤ r}) ≤ 2 h ε e^{L h}`.  This localizes the library's `distLR_flow_le_exp`.
The paper's `h ε_r` has the constant `1` instead of `2 e^{L h}`, see `remark4_constant_false`. -/
theorem distLR_near_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) (hh : 0 < h)
    (hA : ODESolution F A t₀ (t₀ + h)) (hrank : (A t₀).rank ≤ r) (hρ : B * h < ρ)
    (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) :
    distLR r (A (t₀ + h)) ≤ 2 * h * ε * Real.exp (L * h) := by
  have hB0 := hB.nonneg
  have hgap : 0 < ρ - B * h := by linarith
  apply le_of_forall_pos_le_add
  intro η hη
  set K := 8 * L * B * h ^ 2 * Real.exp (L * h) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨N, hN'⟩ := exists_nat_gt (max (K / η) (B * h / (ρ - B * h)))
  have hN1 : K / η < N := (le_max_left _ _).trans_lt hN'
  have hN2 : B * h / (ρ - B * h) < N := (le_max_right _ _).trans_lt hN'
  have hq : 0 ≤ K / η := by positivity
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt hq hN1
  have hτ : 0 ≤ h / N := by positivity
  have hNτ : (N : ℝ) * (h / N) = h := by field_simp
  have hρ' : B * (h + h / N) < ρ := by
    rw [div_lt_iff₀ hgap] at hN2
    have : B * h / N < ρ - B * h := by
      rw [div_lt_iff₀ hNr]
      linarith [mul_comm (ρ - B * h) (N : ℝ)]
    have e : B * (h + h / N) = B * h + B * h / N := by ring
    linarith
  have hg := distLR_near_grid hF hL hB hc hε0 hτ hNτ hA hrank hρ' hN N le_rfl
  rw [hNτ] at hg
  have e : (N : ℝ) * (2 * (h / N * (4 * L * B * (h / N) + ε))) =
      2 * h * ε + 8 * L * B * h ^ 2 / N := by
    field_simp; ring
  rw [e] at hg
  have hlt : K / N ≤ η := by
    rw [div_le_iff₀ hNr]
    rw [div_lt_iff₀ hη] at hN1
    linarith [mul_comm η (N : ℝ)]
  calc distLR r (A (t₀ + h)) ≤ (2 * h * ε + 8 * L * B * h ^ 2 / N) * Real.exp (L * h) := hg
    _ = 2 * h * ε * Real.exp (L * h) + K / N := by rw [hK]; ring
    _ ≤ _ := by linarith

end Truncation

/-! ### Remark 4: truncation of the augmented result -/

section TruncationStep

variable {m n : Type*} [Fintype m] [Fintype n] {r rh rb : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ h L B ε ε' ρ H M₃ a b : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K : ℝ → Matrix m (Fin r) ℝ} {Lf : ℝ → Matrix n (Fin r) ℝ} {A : ℝ → Matrix m n ℝ}
  {Uh : Matrix m (Fin rh) ℝ} {Vh : Matrix n (Fin rh) ℝ} {Sh : ℝ → Matrix (Fin rh) (Fin rh) ℝ}
  {Ub : Matrix m (Fin rb) ℝ} {Vb : Matrix n (Fin rb) ℝ} {Sb : ℝ → Matrix (Fin rb) (Fin rb) ℝ}

/-- **Remark 4 of arXiv 2402.08607, tolerance truncation**: truncation with a tolerance `ϑ` adds
`ϑ` to the bound of Theorem 1. -/
theorem IsMidpoint4rStep.trunc_tolerance_le
    (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hh : 0 < h) (hhH : h ≤ H)
    (hab : a < b) (ha : a ≤ t₀) (hb : t₀ + h ≤ b) (hA : ODESolution F A a b)
    (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) (hε' : NormalBoundNear F rh ε' A ρ t₀ (t₀ + h))
    {Y₁ : Matrix m n ℝ} {ϑ : ℝ} (hT : ‖Y₁ - Ub * Sb (t₀ + h) * Vbᵀ‖ ≤ ϑ) :
    ‖Y₁ - A (t₀ + h)‖ ≤
      midC L B (secondBound B M₃ (b - a)) M₃ H * h * (h ^ 2 + h * ε + ε') + ϑ := by
  have h1 := hs.local_error_le hF hL hB hh hhH hab ha hb hA hA3 hM₃ hA₀ hρ hε hε'
  have h2 := norm_sub_le_norm_sub_add_norm_sub Y₁ (Ub * Sb (t₀ + h) * Vbᵀ) (A (t₀ + h))
  linarith

/-- **Remark 4 of arXiv 2402.08607, rank truncation, first inequality (corrected constant).**  If
`A(t₀)` has rank `≤ r`, (16) holds at rank `r` near `A`, `ρ > B h`, and `T` is a best rank-`r`
approximation of any `Ŷ`, then `‖T - A(t₁)‖ ≤ 2 e^{L h} h ε_r + 2 ‖Ŷ - A(t₁)‖`.  The constant `1`
of the paper in front of `h ε_r` is false, see `remark4_constant_false`. -/
theorem norm_bestTrunc_near_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hε0 : 0 ≤ ε) (hh : 0 < h)
    (hA : ODESolution F A t₀ (t₀ + h)) (hrank : (A t₀).rank ≤ r) (hρ : B * h < ρ)
    (hN : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) {Yb T : Matrix m n ℝ}
    (hT : ‖T - Yb‖ ≤ distLR r Yb) :
    ‖T - A (t₀ + h)‖ ≤ 2 * h * ε * Real.exp (L * h) + 2 * ‖Yb - A (t₀ + h)‖ := by
  have h1 := norm_bestTrunc_sub_le (A₁ := A (t₀ + h)) hT
  have h2 := distLR_near_le hF hL hB hc hε0 hh hA hrank hρ hN
  linarith

/-- The constant of the rank-truncated local error. -/
noncomputable def truncC (L B M₃ T H : ℝ) : ℝ :=
  2 * Real.exp (L * H) + 2 * (1 + H) * midC L B (secondBound B M₃ T) M₃ H

/-- **Remark 4 of arXiv 2402.08607, rank truncation.**  Under the assumptions of Theorem 1, for
`T` a best rank-`r` approximation of `Ȳ₁` and `F` continuous in time,

    ‖T - A(t₁)‖ ≤ C' h (h² + ε_r + ε_r̂),   `C' = truncC L B M₃ (b - a) H`.

With `ε_r̂ ≤ ε_r` this is the paper's `C' h (h² + ε_r)`, see `IsMidpoint4rStep.trunc_rank_le'`. In
the paper the term `ε_r̂` is absorbed tacitly, which needs such a comparison: `ε_r` and `ε_r̂` bound
the normal component at different points. -/
theorem IsMidpoint4rStep.trunc_rank_le
    (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hh : 0 < h) (hhH : h ≤ H)
    (hab : a < b) (ha : a ≤ t₀) (hb : t₀ + h ≤ b) (hA : ODESolution F A a b)
    (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) (hε' : NormalBoundNear F rh ε' A ρ t₀ (t₀ + h))
    {T : Matrix m n ℝ} (hT : ‖T - Ub * Sb (t₀ + h) * Vbᵀ‖ ≤ distLR r (Ub * Sb (t₀ + h) * Vbᵀ)) :
    ‖T - A (t₀ + h)‖ ≤ truncC L B M₃ (b - a) H * h * (h ^ 2 + ε + ε') := by
  have hB0 := hB.nonneg
  have hρ0 : 0 < ρ := lt_of_le_of_lt (mul_nonneg hB0 hh.le) hρ
  have hmem : t₀ ∈ Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hε0 : 0 ≤ ε := hε.nonneg hF hL hmem S₀ hs.half.orthU₀ hs.half.orthV₀
    (by rw [hA₀, sub_self, norm_zero]; exact hρ0)
  have hloc := hs.local_error_le hF hL hB hh hhH hab ha hb hA hA3 hM₃ hA₀ hρ hε hε'
  have hrank : (A t₀).rank ≤ r := by rw [hA₀]; exact rank_mul_mul_transpose_le U₀ S₀ V₀
  have htr := norm_bestTrunc_near_le hF hL hB hc hε0 hh (hA.mono ha hb) hrank hρ hε hT
  set C := midC L B (secondBound B M₃ (b - a)) M₃ H with hC
  have hH : 0 ≤ H := hh.le.trans hhH
  have hmid : ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤ C * h * (h ^ 2 + h * ε + ε') := hloc
  have hC0 : 0 ≤ C := by
    have h0 : 0 ≤ C * h * (h ^ 2 + h * ε + ε') := (norm_nonneg _).trans hmid
    by_cases hS : h ^ 2 + h * ε + ε' = 0
    · have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ a ⟨le_rfl, hab.le⟩)
      have hab' : 0 < b - a := sub_pos.2 hab
      refine midC_nonneg hL hB0 ?_ hM₃0 hH
      unfold secondBound; positivity
    · have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ a ⟨le_rfl, hab.le⟩)
      have hab' : 0 < b - a := sub_pos.2 hab
      refine midC_nonneg hL hB0 ?_ hM₃0 hH
      unfold secondBound; positivity
  have hε'0 : 0 ≤ ε' := by
    have hmid' : t₀ + h / 2 ∈ Icc t₀ (t₀ + h) := ⟨by linarith, by linarith⟩
    have hd : ‖Uh * Sh (t₀ + h / 2) * Vhᵀ - A (t₀ + h / 2)‖ < ρ := by
      have h1 := near_of_proj (isOrthProj_galProj hs.half.orthUa hs.half.orthVa) hB
        (odeSolution_galProj hs.half.sSol) (hA.mono ha (by linarith : t₀ + h / 2 ≤ b) |>.mono
          le_rfl le_rfl) (hs.half.start_eq.trans hA₀.symm)
        (⟨by linarith, le_rfl⟩ : t₀ + h / 2 ∈ Icc t₀ (t₀ + h / 2))
        (⟨by linarith, le_rfl⟩ : t₀ + h / 2 ∈ Icc t₀ (t₀ + h / 2))
      linarith
    exact hε'.nonneg hF hL hmid' _ hs.half.orthUa hs.half.orthVa hd
  have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hK0 : 0 ≤ Real.exp (L * H) := (Real.exp_pos _).le
  have hP : 0 ≤ h ^ 2 + ε + ε' := by positivity
  have h1 : 2 * h * ε * Real.exp (L * h) ≤ 2 * Real.exp (L * H) * h * (h ^ 2 + ε + ε') := by
    have h2 : 2 * h * ε * Real.exp (L * h) ≤ 2 * h * ε * Real.exp (L * H) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h3 : 0 ≤ 2 * Real.exp (L * H) * h * (h ^ 2 + ε') := by positivity
    nlinarith
  have h2 : h ^ 2 + h * ε + ε' ≤ (1 + H) * (h ^ 2 + ε + ε') := by
    have h3 : h * ε ≤ H * ε := mul_le_mul_of_nonneg_right hhH hε0
    nlinarith [mul_nonneg hH hP, sq_nonneg h]
  have h3 : 2 * ‖Ub * Sb (t₀ + h) * Vbᵀ - A (t₀ + h)‖ ≤
      2 * (1 + H) * C * h * (h ^ 2 + ε + ε') := by
    have h4 : C * h * (h ^ 2 + h * ε + ε') ≤ C * h * ((1 + H) * (h ^ 2 + ε + ε')) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 hh.le)
    nlinarith
  have e : truncC L B M₃ (b - a) H * h * (h ^ 2 + ε + ε')
      = 2 * Real.exp (L * H) * h * (h ^ 2 + ε + ε') + 2 * (1 + H) * C * h * (h ^ 2 + ε + ε') := by
    rw [truncC, hC]; ring
  rw [e]
  linarith

/-- **Remark 4 of arXiv 2402.08607, rank truncation, the paper's form**: if `ε_r̂ ≤ ε_r`, then
`‖T - A(t₁)‖ ≤ C' h (h² + ε_r)` for a best rank-`r` approximation `T` of `Ȳ₁`. -/
theorem IsMidpoint4rStep.trunc_rank_le'
    (hs : IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) (hh : 0 < h) (hhH : h ≤ H)
    (hab : a < b) (ha : a ≤ t₀) (hb : t₀ + h ≤ b) (hA : ODESolution F A a b)
    (hA3 : ContDiffOn ℝ 3 A (Icc a b))
    (hM₃ : ∀ t ∈ Icc a b, ‖iteratedDerivWithin 3 A (Icc a b) t‖ ≤ M₃)
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) (hρ : B * h < ρ)
    (hε : NormalBoundNear F r ε A ρ t₀ (t₀ + h)) (hε' : NormalBoundNear F rh ε' A ρ t₀ (t₀ + h))
    (hεε' : ε' ≤ ε)
    {T : Matrix m n ℝ} (hT : ‖T - Ub * Sb (t₀ + h) * Vbᵀ‖ ≤ distLR r (Ub * Sb (t₀ + h) * Vbᵀ)) :
    ‖T - A (t₀ + h)‖ ≤ 2 * truncC L B M₃ (b - a) H * h * (h ^ 2 + ε) := by
  have h1 := hs.trunc_rank_le hF hL hB hc hh hhH hab ha hb hA hA3 hM₃ hA₀ hρ hε hε' hT
  have hB0 := hB.nonneg
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ a ⟨le_rfl, hab.le⟩)
  have hab' : 0 < b - a := sub_pos.2 hab
  have hH : 0 ≤ H := hh.le.trans hhH
  have hM₂ : 0 ≤ secondBound B M₃ (b - a) := by unfold secondBound; positivity
  have hC : 0 ≤ truncC L B M₃ (b - a) H := by
    have := midC_nonneg hL hB0 hM₂ hM₃0 hH
    unfold truncC
    positivity
  refine h1.trans ?_
  have hmem : t₀ ∈ Icc t₀ (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hρ0 : 0 < ρ := lt_of_le_of_lt (mul_nonneg hB0 hh.le) hρ
  have hε0 : 0 ≤ ε := hε.nonneg hF hL hmem S₀ hs.half.orthU₀ hs.half.orthV₀
    (by rw [hA₀, sub_self, norm_zero]; exact hρ0)
  have h2 : h ^ 2 + ε + ε' ≤ 2 * (h ^ 2 + ε) := by nlinarith [sq_nonneg h]
  calc _ ≤ truncC L B M₃ (b - a) H * h * (2 * (h ^ 2 + ε)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hh.le)
    _ = _ := by ring

end TruncationStep

/-! ### Well-posedness and satisfiability -/

section WellPosed

variable {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
  {L B : ℝ}

/-- **The Midpoint BUG (4r) step exists**, with `r̂ = 2 r` and `r̄ = 4 r` columns, for `F`
Lipschitz, bounded and continuous in time and `4 r ≤ m, n`: the substep equations are solved by
`MatrixBUG.exists_odeSolution_conj` and the augmented bases exist by
`exists_orthonormal_capture_fromCols`. -/
theorem exists_isMidpoint4rStep (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {t₀ h : ℝ} (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ}
    (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (hm : 4 * r ≤ Fintype.card m) (hn : 4 * r ≤ Fintype.card n) :
    ∃ (Uh : Matrix m (Fin (2 * r)) ℝ) (Vh : Matrix n (Fin (2 * r)) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ) (Ub : Matrix m (Fin (4 * r)) ℝ)
      (Vb : Matrix n (Fin (4 * r)) ℝ) (Sb : ℝ → Matrix (Fin (4 * r)) (Fin (4 * r)) ℝ),
      IsMidpoint4rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb := by
  obtain ⟨Uh, Vh, K, Lf, Sh, hs⟩ := MatrixBUG.exists_isRankAdaptiveStep hF hB hc
    (t₀ := t₀) (t₁ := t₀ + h / 2) (by linarith) S₀ hU₀ hV₀ (by omega) (by omega) (ϑ := 0) le_rfl
  have hwm : ∀ X Y : Matrix m (Fin (2 * r)) ℝ, (Matrix.fromCols X Y).rank ≤ 4 * r := by
    intro X Y
    have := (Matrix.fromCols X Y).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hwn : ∀ X Y : Matrix n (Fin (2 * r)) ℝ, (Matrix.fromCols X Y).rank ≤ 4 * r := by
    intro X Y
    have := (Matrix.fromCols X Y).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ub, hUb, h1, h2⟩ := exists_orthonormal_capture_fromCols Uh
    (h • F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ) * Vh) (hwm _ _) hm
  obtain ⟨Vb, hVb, h3, h4⟩ := exists_orthonormal_capture_fromCols Vh
    (h • (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ))ᵀ * Uh) (hwn _ _) hn
  obtain ⟨Sb, hSb, hSb₀⟩ := MatrixBUG.exists_odeSolution_conj hF hB hc _ _
    (fun t x => MatrixBUG.sField_eq Ub Vb t x) (show t₀ ≤ t₀ + h by linarith)
    (Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb))
  exact ⟨Uh, Vh, K, Lf, Sh, Ub, Vb, Sb, hs, hUb, hVb, h1, h2, h3, h4, hSb, hSb₀⟩

/-- **The Midpoint BUG (3r) step exists**, with `r̄ = 3 r` columns, for `F` Lipschitz, bounded and
continuous in time and `3 r ≤ m, n`. -/
theorem exists_isMidpoint3rStep (hF : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hc : ∀ Y, Continuous fun t => F t Y) {t₀ h : ℝ} (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ}
    (S₀ : Matrix (Fin r) (Fin r) ℝ) {V₀ : Matrix n (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1)
    (hV₀ : V₀ᵀ * V₀ = 1) (hm : 3 * r ≤ Fintype.card m) (hn : 3 * r ≤ Fintype.card n) :
    ∃ (Uh : Matrix m (Fin r) ℝ) (Vh : Matrix n (Fin r) ℝ)
      (K : ℝ → Matrix m (Fin r) ℝ) (Lf : ℝ → Matrix n (Fin r) ℝ)
      (Sh : ℝ → Matrix (Fin r) (Fin r) ℝ) (Ub : Matrix m (Fin (3 * r)) ℝ)
      (Vb : Matrix n (Fin (3 * r)) ℝ) (Sb : ℝ → Matrix (Fin (3 * r)) (Fin (3 * r)) ℝ),
      IsMidpoint3rStep F t₀ h U₀ S₀ V₀ Uh Vh K Lf Sh Ub Vb Sb := by
  obtain ⟨Uh, Vh, K, Lf, Sh, hs⟩ := MatrixBUG.exists_isStep hF hB hc
    (t₀ := t₀) (t₁ := t₀ + h / 2) (by linarith) S₀ hU₀ hV₀ (by omega) (by omega)
  have hwm : ∀ X Y Z : Matrix m (Fin r) ℝ,
      (Matrix.fromCols (Matrix.fromCols X Y) Z).rank ≤ 3 * r := by
    intro X Y Z
    have := (Matrix.fromCols (Matrix.fromCols X Y) Z).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  have hwn : ∀ X Y Z : Matrix n (Fin r) ℝ,
      (Matrix.fromCols (Matrix.fromCols X Y) Z).rank ≤ 3 * r := by
    intro X Y Z
    have := (Matrix.fromCols (Matrix.fromCols X Y) Z).rank_le_card_width
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨Ub, hUb, h1, h2⟩ := exists_orthonormal_capture_fromCols (Matrix.fromCols U₀ Uh)
    (h • F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ) * Vh) (hwm _ _ _) hm
  obtain ⟨Vb, hVb, h3, h4⟩ := exists_orthonormal_capture_fromCols (Matrix.fromCols V₀ Vh)
    (h • (F (t₀ + h / 2) (Uh * Sh (t₀ + h / 2) * Vhᵀ))ᵀ * Uh) (hwn _ _ _) hn
  rw [Matrix.mul_fromCols] at h1 h3
  obtain ⟨h1a, h1b⟩ := Matrix.fromCols_inj.eq_iff.mp h1
  obtain ⟨h3a, h3b⟩ := Matrix.fromCols_inj.eq_iff.mp h3
  obtain ⟨Sb, hSb, hSb₀⟩ := MatrixBUG.exists_odeSolution_conj hF hB hc _ _
    (fun t x => MatrixBUG.sField_eq Ub Vb t x) (show t₀ ≤ t₀ + h by linarith)
    (Ubᵀ * U₀ * S₀ * (V₀ᵀ * Vb))
  exact ⟨Uh, Vh, K, Lf, Sh, Ub, Vb, Sb, hs, ⟨hUb, hVb, h1b, h2, h3b, h4, hSb, hSb₀⟩, h1a, h3a⟩

/-- **A Midpoint BUG (4r) step with full bases** `Û = V̂ = Ū = V̄ = I` on `d × d` matrices: the
Galerkin steps are then the exact flow, and `Ȳ₁ = A(t₁)`. -/
theorem isMidpoint4rStep_full {d : ℕ} {F : ℝ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ Y, Continuous fun t => F t Y)
    {t₀ h : ℝ} (hh : 0 ≤ h) {U₀ : Matrix (Fin d) (Fin r) ℝ} (S₀ : Matrix (Fin r) (Fin r) ℝ)
    {V₀ : Matrix (Fin d) (Fin r) ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {A : ℝ → Matrix (Fin d) (Fin d) ℝ} (hA : ODESolution F A t₀ (t₀ + h))
    (hA₀ : A t₀ = U₀ * S₀ * V₀ᵀ) :
    ∃ (K : ℝ → Matrix (Fin d) (Fin r) ℝ) (Lf : ℝ → Matrix (Fin d) (Fin r) ℝ),
      IsMidpoint4rStep F t₀ h U₀ S₀ V₀ (1 : Matrix (Fin d) (Fin d) ℝ) 1 K Lf A 1 1 A := by
  have h01 : t₀ ≤ t₀ + h / 2 := by linarith
  obtain ⟨K, hK, hK₀⟩ := MatrixBUG.exists_odeSolution_conj hF hB hc _ _
    (fun t x => MatrixBUG.kField_eq V₀ t x) h01 (U₀ * S₀)
  obtain ⟨Lf, hLf, hLf₀⟩ := MatrixBUG.exists_odeSolution_conj hF hB hc _ _
    (fun t x => MatrixBUG.lField_eq U₀ t x) h01 (V₀ * S₀ᵀ)
  have e : MatrixBUG.sField (1 : Matrix (Fin d) (Fin d) ℝ) (1 : Matrix (Fin d) (Fin d) ℝ) F
      = F := by
    funext t S; simp [MatrixBUG.sField]
  have hst : A t₀
      = (1 : Matrix (Fin d) (Fin d) ℝ)ᵀ * U₀ * S₀ * (V₀ᵀ * (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    simp [hA₀]
  refine ⟨K, Lf, ⟨hU₀, hV₀, hK, hK₀, hLf, hLf₀, by simp, by simp, by simp, by simp, by simp,
    by simp, by rw [e]; exact hA.mono le_rfl (by linarith), hst, by simp⟩,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by rw [e]; exact hA, hst⟩⟩

end WellPosed

/-! ### The constant `1` in Remark 4 is false -/

section Counterexample

/-- `E = diag(0, 1)`. -/
noncomputable def cxE : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 1]

/-- The field `F(t, Y) = (1 + min(dist(Y, M_{≤ 1}), 2)) E` of the counterexample: on `M_{≤ 1}` it
equals `E`, so its normal component is at most `ε_1 = 1`, but off `M_{≤ 1}` it grows with the
distance, with Lipschitz constant `L = 1`. -/
noncomputable def cxF (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 + min (distLR 1 Y) 2) • cxE

/-- The exact solution `A(t) = diag(2, e^t - 1)` from `A(0) = diag(2, 0)`. -/
noncomputable def cxA (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2, Real.exp t - 1]

/-- Its derivatives `e^t E`. -/
noncomputable def cxa (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.exp t • cxE

/-- `S₀ = (2)`, so that `A(0) = e₁ S₀ e₁ᵀ` has rank `1` exactly. -/
noncomputable def cxS₀ : Matrix (Fin 1) (Fin 1) ℝ := (2 : ℝ) • 1

lemma norm_cxE : ‖cxE‖ = 1 := by
  rw [Frobenius.norm_def]
  simp [cxE, Fin.sum_univ_two, Matrix.diagonal_apply]

lemma cxA_eq (t : ℝ) : cxA t = cxA 0 + (Real.exp t - 1) • cxE := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxA, cxE]

lemma cxA_zero : cxA 0 = MatrixBUG.unitCol * cxS₀ * MatrixBUG.unitColᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxA, cxS₀, Matrix.mul_apply]

lemma distLR_cxA {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : distLR 1 (cxA t) = Real.exp t - 1 := by
  have he0 : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp h0]
  have he1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 h1
  have he2 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  refine le_antisymm ?_ ?_
  · have hr : (cxA 0).rank ≤ 1 := by
      rw [cxA_zero]; exact rank_mul_mul_transpose_le _ _ _
    refine (distLR_le_norm_sub hr).trans (le_of_eq ?_)
    rw [cxA_eq t, add_sub_cancel_left, norm_smul, norm_cxE, mul_one, Real.norm_of_nonneg he0]
  · refine le_distLR_diagonal he0 (fun i => ?_) (by simp)
    fin_cases i
    · simp; linarith
    · simp [abs_of_nonneg he0]

lemma cxF_lowRank {k : ℕ} (hk : k ≤ 1) (t : ℝ) (U : Matrix (Fin 2) (Fin k) ℝ)
    (S : Matrix (Fin k) (Fin k) ℝ) (V : Matrix (Fin 2) (Fin k) ℝ) : cxF t (U * S * Vᵀ) = cxE := by
  have h : (U * S * Vᵀ).rank ≤ 1 := (rank_mul_mul_transpose_le U S V).trans hk
  rw [cxF, distLR_eq_zero_of_rank_le h, min_eq_left zero_le_two, add_zero, one_smul]

lemma cxF_lipschitz : IsLipschitzField cxF 1 := by
  intro t X Y
  have e : cxF t X - cxF t Y = (min (distLR 1 X) 2 - min (distLR 1 Y) 2) • cxE := by
    simp only [cxF, ← sub_smul]; congr 1; ring
  rw [e, norm_smul, norm_cxE, mul_one, Real.norm_eq_abs, one_mul]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  exact max_le (abs_distLR_sub_le X Y) (norm_nonneg _)

lemma cxF_bounded : IsBoundedField cxF 3 := by
  intro t X
  have h0 : 0 ≤ distLR 1 X := distLR_nonneg
  have h1 : 0 ≤ min (distLR 1 X) 2 := le_min h0 zero_le_two
  rw [cxF, norm_smul, norm_cxE, mul_one, Real.norm_of_nonneg (by linarith)]
  linarith [min_le_right (distLR 1 X) 2]

lemma hasDerivAt_cxA (t : ℝ) : HasDerivAt cxA (cxa t) t := by
  have h := (((Real.hasDerivAt_exp t).sub_const 1).smul_const cxE).const_add (cxA 0)
  have e : cxA = fun t => cxA 0 + (Real.exp t - 1) • cxE := funext cxA_eq
  rw [e]
  exact h

lemma cxF_cxA {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cxF t (cxA t) = cxa t := by
  have he1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.2 h1
  have he2 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  rw [cxF, distLR_cxA h0 h1, min_eq_left (by linarith), cxa]
  congr 1; ring

lemma odeSolution_cxA : ODESolution cxF cxA 0 1 where
  cont := fun t _ => (hasDerivAt_cxA t).continuousAt.continuousWithinAt
  deriv t ht := by
    rw [cxF_cxA ht.1 ht.2.le]
    exact (hasDerivAt_cxA t).hasDerivWithinAt

lemma hasDerivData_cxA : HasDerivData cxA cxa cxa cxa 0 1 (Real.exp 1) (Real.exp 1) where
  d₀ t _ := (hasDerivAt_cxA t).hasDerivWithinAt
  d₁ t _ := ((Real.hasDerivAt_exp t).smul_const cxE).hasDerivWithinAt
  d₂ t _ := ((Real.hasDerivAt_exp t).smul_const cxE).hasDerivWithinAt
  b₂ t ht := by
    rw [cxa, norm_smul, norm_cxE, mul_one, Real.norm_of_nonneg (Real.exp_pos t).le]
    exact Real.exp_le_exp.2 ht.2
  b₃ t ht := by
    rw [cxa, norm_smul, norm_cxE, mul_one, Real.norm_of_nonneg (Real.exp_pos t).le]
    exact Real.exp_le_exp.2 ht.2

lemma normalBoundNear_cx (k : ℕ) (hk : k ≤ 1) (ρ : ℝ) : NormalBoundNear cxF k 1 cxA ρ 0 1 := by
  intro t _ U S V hU hV _ _
  rw [cxF_lowRank hk]
  exact ((isOrthProj_tangentProj hU hV).compl.norm_le _).trans norm_cxE.le

lemma normalBoundNear_cx_two (ρ : ℝ) : NormalBoundNear cxF 2 0 cxA ρ 0 1 := by
  intro t _ U S V hU hV _ _
  rw [one_sub_tangentProj_apply, mul_transpose_eq_one_of_transpose_mul_eq_one hU]
  simp

/-- **The first inequality of Remark 4 of arXiv 2402.08607 is false as stated** (constant `1` in
front of `h ε_r`).  For `2 × 2` matrices, rank `r = 1`, `h = 1`, the field `cxF` is `1`-Lipschitz,
bounded by `3`, time-independent, with normal components `≤ ε_1 = 1` on all of `M_1` (and `0` on
`M_2`), the exact solution `cxA` from `Y₀ = e₁ (2) e₁ᵀ` (rank `1`) has all derivatives bounded by
`e`, and a Midpoint BUG (4r) step (`Û = V̂ = Ū = V̄ = I`) gives `Ȳ₁ = A(t₁)`.  Yet every rank-`1`
matrix `T`, in particular every rank-`1` truncation of `Ȳ₁`, satisfies
`‖T - A(t₁)‖ ≥ dist(A(1), M_1) = e - 1 > h ε_1 + 2 ‖Ȳ₁ - A(t₁)‖ = 1`.  The bound holds with
`2 e^{L h} h ε_r` (`norm_bestTrunc_near_le`). -/
theorem remark4_constant_false :
    ∃ (K Lf : ℝ → Matrix (Fin 2) (Fin 1) ℝ),
      IsLipschitzField cxF 1 ∧ IsBoundedField cxF 3 ∧ (∀ Y, Continuous fun t => cxF t Y) ∧
      ODESolution cxF cxA 0 1 ∧ HasDerivData cxA cxa cxa cxa 0 1 (Real.exp 1) (Real.exp 1) ∧
      cxA 0 = MatrixBUG.unitCol * cxS₀ * MatrixBUG.unitColᵀ ∧ IsUnit cxS₀ ∧
      (∀ ρ, NormalBoundNear cxF 1 1 cxA ρ 0 1) ∧ (∀ ρ, NormalBoundNear cxF 2 0 cxA ρ 0 1) ∧
      IsMidpoint4rStep cxF 0 1 MatrixBUG.unitCol cxS₀ MatrixBUG.unitCol
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 K Lf cxA 1 1 cxA ∧
      ∀ T : Matrix (Fin 2) (Fin 2) ℝ, T.rank ≤ 1 →
        1 * 1 + 2 * ‖1 * cxA (0 + 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - cxA (0 + 1)‖
          < ‖T - cxA (0 + 1)‖ := by
  have hc : ∀ Y, Continuous fun t => cxF t Y := fun Y => continuous_const
  have hA : ODESolution cxF cxA 0 (0 + 1) := by rw [zero_add]; exact odeSolution_cxA
  obtain ⟨K, Lf, hs⟩ := isMidpoint4rStep_full cxF_lipschitz cxF_bounded hc zero_le_one cxS₀
    MatrixBUG.unitCol_orth MatrixBUG.unitCol_orth hA cxA_zero
  refine ⟨K, Lf, cxF_lipschitz, cxF_bounded, hc, odeSolution_cxA, hasDerivData_cxA, cxA_zero,
    ?_, normalBoundNear_cx 1 le_rfl, normalBoundNear_cx_two, hs, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, cxS₀, Matrix.det_smul, Matrix.det_one]
    simp
  · intro T hT
    have h1 := distLR_le_norm_sub (X := cxA 1) hT
    rw [distLR_cxA zero_le_one le_rfl, norm_sub_rev] at h1
    have h2 := Real.exp_one_gt_d9
    simp only [zero_add, Matrix.transpose_one, Matrix.one_mul, sub_self, norm_zero, mul_zero,
      add_zero, mul_one]
    linarith

/-- The hypotheses of Theorem 1 (`IsMidpoint4rStep.local_error_of_second`) are jointly satisfiable
with a non-tangential field: the instance of `remark4_constant_false` (`L = 1`, `B = 3`,
`M₂ = M₃ = e`, `ε_1 = 1`, `ε_2 = 0`, `ρ = 4`). -/
example : ‖1 * cxA (0 + 1) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ - cxA (0 + 1)‖ ≤
    midC 1 3 (Real.exp 1) (Real.exp 1) 1 * 1 * (1 ^ 2 + 1 * 1 + 0) := by
  obtain ⟨_, _, -, -, -, -, -, h0, -, hN, hN', hs, -⟩ := remark4_constant_false
  have hA : ODESolution cxF cxA 0 (0 + 1) := by rw [zero_add]; exact odeSolution_cxA
  have hD : HasDerivData cxA cxa cxa cxa 0 (0 + 1) (Real.exp 1) (Real.exp 1) := by
    rw [zero_add]; exact hasDerivData_cxA
  have h1 : NormalBoundNear cxF 1 1 cxA 4 0 (0 + 1) := by rw [zero_add]; exact hN 4
  have h2 : NormalBoundNear cxF 2 0 cxA 4 0 (0 + 1) := by rw [zero_add]; exact hN' 4
  exact hs.local_error_of_second cxF_lipschitz zero_le_one cxF_bounded one_pos le_rfl hA h0 hD
    (by norm_num) h1 h2

end Counterexample

/-- The local Galerkin projector of this file, replaced by the core `LeanDLRA.galerkinProj` (same
definition `leftProj Ub * rightProj Vb`). -/
@[deprecated (since := "2026-11-09")] alias galProj := LeanDLRA.galerkinProj

end LeanDLRA.Literature.P2402_08607
