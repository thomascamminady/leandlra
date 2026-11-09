import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Classical.EckartYoung

/-!
# Dynamical randomized SVD and generalized Nyström as BUG-type steps

B. Carrel, *Randomized methods for dynamical low-rank approximation*
(arXiv 2410.17091, §§2–3; quoted in arXiv 2506.15259, §2.3.1) proposes two randomized DLRA
integrators.  One step of the **dynamical randomized SVD (DRSVD)** from `Y₀ = U₀ S₀ V₀ᵀ` is

1. *B-step* (dynamical range finder): `B' = F(B Ω†) Ω`, `B(0) = Y₀ Ω`, `Q_h = orth(B(h))`,
   `Q = orth([U₀, Q_h])`;
2. *C-step*: `C' = F(Q Cᵀ)ᵀ Q`, `C(0) = Y₀ᵀ Q` (`n × (2r + p)`);
3. truncation `Y₁ = T_r(Q C(h)ᵀ)`.

The **dynamical generalized Nyström (DGN)** method runs a B-step with a co-range basis `W`,
the C-step, and a core step `D' = Qᵀ F(Q D Wᵀ) W`, `D(0) = Qᵀ Y₀ W`, and assembles
`Y₁ = B(h) T_r(D(h))† C(h)ᵀ`.

## Main results

**OP-RS-01 (robust error bounds; resolved for augmented sketches).**  We write the sketch
through an orthonormal basis `W` of `range Ω` (`Ω Ω† = W Wᵀ`, avoiding pseudo-inverses).  Then
`Y_B = B Wᵀ` solves `Y_B' = F(Y_B) W Wᵀ` (`bStep_full`), i.e. the B-step **is a BUG K-step**
with `Q₀ = rightProj W`, and it starts at `Y₀` exactly when the sketch is augmented,
`Y₀ W Wᵀ = Y₀` (e.g. `range V₀ ⊆ range W`, `mul_mul_transpose_eq_self_of_factors`).  The C-step
is the one-sided Galerkin step `Y_C = Q C(·)ᵀ`, `Y_C' = Q Qᵀ F(Y_C)`, `Y_C(0) = Q Qᵀ Y₀`
(`cStep_full`).  With these identifications (`IsDRSVDStep`, `isDRSVDStep_matrix`):

* `IsDRSVDStep.range_capture`: `‖A(t₁) - Q Qᵀ A(t₁)‖ ≤ h (4 L B h + ε)`, from `kstep_capture`,
  where `ε` bounds the doubly-normal part `(I - QQᵀ) F(Y_B(t₁)) (I - WWᵀ)`;
* `IsDRSVDStep.local_error`: `‖Y₁ - A(t₁)‖ ≤ (e^{Lh} - 1)(Bh + θ) + θ + ϑ`,
  `θ = h (4 L B h + ε)`, where `ϑ ≥ ‖Y₁ - Q C(h)ᵀ‖` is the truncation error (from
  `galerkin_step_error`); `IsDRSVDStep.local_error_le` gives `h (c₁ ε + c₂ h) + ϑ` with the
  BUG constants `bugC₁`, `bugC₂`;
* `drsvd_global_error`, `drsvd_global_error_le`: over `n` steps with `n h ≤ T`,
  `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ n ϑ`, `c₀ = e^{LT}`, `c₁ = T e^{LT} bugC₁`,
  `c₂ = T e^{LT} bugC₂`, `c₃ = e^{LT}` (Lady Windermere's fan).

All constants depend only on `L`, `B`, `T` and the step-size bound, **not on singular values**,
and the non-checkable range-inclusion hypothesis of arXiv 2410.17091 is replaced by the
quantitative normal-component bound `ε`.  This is new: the paper gives only exactness results
and numerical evidence.  Two by-products: the robust bound does not need the augmentation of
`Q` by `U₀` (the C-step starts at `Q Qᵀ Y₀` and is compared with `Q Qᵀ A`), but it does need
the augmentation of the *sketch* (`Y_B(t₀) = Y₀`); without it the B-step starts at
`Y₀ W Wᵀ ≠ Y₀` in general (`Counterexample.not_augmented_start`), and an additional
`O(L h ‖Y₀ (I - WWᵀ)‖)` term appears (not formalized).  **Scope caveat.**  The DRSVD of
arXiv 2410.17091 (Algorithms 1 and 3) sketches with a plain Gaussian `Ω`, which is *not*
augmented by `V₀`; the robust bound above therefore covers the variant whose sketch is
`W = orth([V₀, Ω])` (`r` extra columns, the same augmentation that (15) applies to the co-range
basis of DGN), not Algorithm 3 verbatim.  *Remaining:* the non-augmented case (extra
`O(L h ‖Y₀ (I - WWᵀ)‖)` term, and its `p`-dependence via HMT-type probabilistic bounds), and a
robust bound for DGN, which needs a perturbation bound for the oblique Nyström assembly; none of
these is formalized.  The paper's heuristic `B(h) ≈ A(h) Ω` is not formalized either.

**OP-RS-07 (erratum; resolved).**  For `F(t, Y) = Ȧ(t)` every substep is an explicit
increment: `B(h) = A(h) W` (`bStep_exact`), `C(h) = A(h)ᵀ Q`, i.e. `C(h)ᵀ = Qᵀ A(h)`
(`cStep_exact`; the proof of Lemma 3.3 of arXiv 2410.17091 writes `Q A(h)ᵀ`, a transposition
slip), and `D(h) = Qᵀ A(h) W` (`dStep_exact`).  Hence, if `Q` captures `A(h)`:

* `drsvd_exact_iff`: `Q C(h)ᵀ = A(h)`, and `T_r(Q C(h)ᵀ) = A(h)` **iff `rank A(h) ≤ r`**
  (`truncation_eq_self_iff`, via Eckart–Young);
* `dgn_exact`: if `rank A(h) ≤ r`, the row range is captured by `W` and `G` is a `{1}`-inverse
  of `T_r(D(h))` (e.g. the Moore–Penrose inverse), then `B(h) G C(h)ᵀ = A(h)`
  (`nystrom_eq_self`, the generalized Nyström identity `A W (Qᵀ A W)⁻ Qᵀ A = A`); conversely,
  exactness with a core of rank `≤ r` forces `rank A(h) ≤ r` (`rank_assembly_le`);
* `Counterexample.drsvd_not_exact`, `Counterexample.dgn_not_exact`: with `r = p = 1`,
  `A(t) = diag(1, 0) + t diag(0, 1)` (`rank Y₀ = r`, `rank G = p`, `rank A(1) = 2 ≤ r + p`) and
  full sketches `Q = W = I` (all range inclusions hold), DRSVD and DGN are **not** exact.
  So Lemmas 3.2 and 3.3 of arXiv 2410.17091 (hypothesis `rank A(h) ≤ r + p`) are false as
  stated; the correct hypothesis is `rank A(h) ≤ r`.  (`Q = I` is what (13) yields, up to an
  orthogonal change of basis that leaves `Q Qᵀ = I` unchanged, whenever the sketch `B(1) = Ω`
  is invertible; the B-step itself is not part of the Lean counterexample.  For DGN the Lean
  statement covers every core of rank `≤ 1`; that `T_1(D(1))†` has rank `≤ 1` is the standard
  fact `rank X† = rank X`, not formalized here.)

**OP-RA-11 (a), (b) (exactness under over-approximation; resolved algebraically).**
`exists_eq_mul_mul_of_rightInv`: if `A₁ = U S Vᵀ` with `k ≤ r` columns and
`G = S (Vᵀ V₀)` has a right inverse (`Q₀ = V₀V₀ᵀ` injective on the row space of `A₁`; rank
`A₁ = k < r` allowed), then `A₁ = A₁ V₀ C`.  Under this range condition (and its transpose),
`bug_exact_of_range` and `ksl_exact_of_range` give exactness of BUG and KSL with no
non-singularity of an `r × r` overlap, which explains the KSL column of the over-approximation
experiment of arXiv 2001.08599 (Table 1, `r = 20`, rank 10); the chart-based column follows
from the paper's Lemma 3.11 (chart method = KSL under its assumptions), which is not formalized
here.  Part (b) is `drsvd_exact_iff`.  Parts (c)
(conservative rank-adaptive scheme) and (d) (rank-reduced Kalman filter) are not addressed
here.

## Formalization notes

* The norm on matrices is the Frobenius norm (`LeanDLRA.Frobenius`).
* Truncation is `EckartYoung.truncation`; in the robust analysis it enters only through
  `ϑ ≥ ‖Y₁ - Q C(h)ᵀ‖`.
* Orthonormal bases are hypotheses (`Wᵀ W = 1`, `Qᵀ Q = 1`); `orth(·)` is replaced by the
  capture property `Q Qᵀ B(h) = B(h)`.  The paper's `B' = F(B Ω†) Ω` with `Ω = W R`
  (`R` invertible) is `B̃' = F(B̃ Wᵀ) W` for `B̃ = B R⁻¹`, which has the same range.
* Satisfiability: `MatrixExample` instantiates `isDRSVDStep_matrix` on `ℝ^{2×2}` with a nonzero
  field and rank-one (non-identity) sketch and range projectors.
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA.RandomizedBUG

/-! ## Abstract robust error analysis -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : ℝ → E → E} {L B ε ϑ : ℝ} {t₀ t₁ h : ℝ} {A : ℝ → E}

/-- All hypotheses of one step of the (augmented) dynamical randomized SVD (arXiv 2410.17091,
Algorithm 3) from `(t₀, Y₀)` to `t₁`, written in the full space: `QΩ` is the orthogonal projector
onto the sketch space (`X ↦ X W Wᵀ`), `YB` the B-step trajectory (`YB = B Wᵀ`), `P` the
projector onto the range basis (`X ↦ Q Qᵀ X`), which captures `YB t₁` (`Q = orth([U₀, B(h)])`),
`ε` bounds the doubly-normal part of the vector field at `YB t₁`, `YC` the C-step trajectory
(`YC = Q Cᵀ`), and `Y₁` the truncated result with `‖Y₁ - YC t₁‖ ≤ ϑ`.  The B-step starting at
`Y₀` is the augmentation hypothesis. -/
structure IsDRSVDStep (F : ℝ → E → E) (ε ϑ : ℝ) (QΩ P : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YB YC : ℝ → E) (Y₁ : E) : Prop where
  projΩ : IsOrthProj QΩ
  projP : IsOrthProj P
  bSol : ODESolution (fun t x => QΩ (F t x)) YB t₀ t₁
  bStart : YB t₀ = Y₀
  rangeCap : P (YB t₁) = YB t₁
  bNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P) ((1 - QΩ) (F t (YB t₁)))‖ ≤ ε
  cSol : ODESolution (fun t x => P (F t x)) YC t₀ t₁
  cStart : YC t₀ = P Y₀
  trunc : ‖Y₁ - YC t₁‖ ≤ ϑ

namespace IsDRSVDStep

variable {QΩ P : E →L[ℝ] E} {Y₀ Y₁ : E} {YB YC : ℝ → E}

/-- The normal-component bound forces `ε ≥ 0` on a nonempty step. -/
lemma eps_nonneg (hs : IsDRSVDStep F ε ϑ QΩ P t₀ t₁ Y₀ YB YC Y₁) (h01 : t₀ ≤ t₁) : 0 ≤ ε :=
  (norm_nonneg _).trans (hs.bNormal t₀ ⟨le_rfl, h01⟩)

/-- The truncation bound forces `ϑ ≥ 0`. -/
lemma trunc_nonneg (hs : IsDRSVDStep F ε ϑ QΩ P t₀ t₁ Y₀ YB YC Y₁) : 0 ≤ ϑ :=
  (norm_nonneg _).trans hs.trunc

/-- **Range capture of the dynamical range finder** (OP-RS-01): the range basis captures the
exact solution, `‖A(t₁) - P A(t₁)‖ ≤ h (4 L B h + ε)`, because the B-step is a BUG K-step with
`Q₀ = QΩ` (`kstep_capture`). -/
theorem range_capture (hs : IsDRSVDStep F ε ϑ QΩ P t₀ t₁ Y₀ YB YC Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - P (A t₁)‖ ≤ h * (4 * L * B * h + ε) := by
  have := kstep_capture hF hL hB hs.projP hs.projΩ ht₁ hh hA hs.bSol (hs.bStart.trans hA₀.symm)
    hs.rangeCap hs.bNormal
  simpa using this

/-- **Robust local error of DRSVD** (OP-RS-01): with `θ = h (4 L B h + ε)`,
`‖Y₁ - A(t₁)‖ ≤ (e^{L h} - 1)(B h + θ) + θ + ϑ`. -/
theorem local_error (hs : IsDRSVDStep F ε ϑ QΩ P t₀ t₁ Y₀ YB YC Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + h * (4 * L * B * h + ε))
      + h * (4 * L * B * h + ε) + ϑ := by
  have hcap := hs.range_capture hF hL hB ht₁ hh hA hA₀
  have hC := galerkin_step_error hs.projP hF hL hB ht₁ hh hA hs.cSol
    (by rw [hs.cStart, hA₀]) hcap
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YC t₁‖ + ‖YC t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith [hs.trunc]

/-- **Robust local error of DRSVD, `O`-form**: for `0 ≤ h ≤ H`,
`‖Y₁ - A(t₁)‖ ≤ h (c₁ ε + c₂ h) + ϑ` with the BUG constants `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H`, independent of singular values. -/
theorem local_error_le (hs : IsDRSVDStep F ε ϑ QΩ P t₀ t₁ Y₀ YB YC Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := by
  have h1 := hs.local_error hF hL hB ht₁ hh hA hA₀
  have hε := hs.eps_nonneg (by linarith)
  have hθ : 0 ≤ h * (4 * L * B * h + ε) := by
    have := hB.nonneg; positivity
  have he : 0 ≤ Real.exp (L * h) - 1 := by
    have := Real.add_one_le_exp (L * h); nlinarith [mul_nonneg hL hh]
  have h2 := bug_bound_le hL hB.nonneg hε hh hhH
  nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hθ :
    B * h + h * (4 * L * B * h + ε) ≤ B * h + h * (4 * L * B * h + ε) + h * (4 * L * B * h + ε))
    he]

end IsDRSVDStep

/-- **Robust global error of DRSVD** (OP-RS-01): for a sequence of DRSVD steps on the grid
`tₙ = t₀ + n h` with exact flows `Φ n` from `Y n`,
`‖Yₙ - A(tₙ)‖ ≤ e^{L n h} (‖Y₀ - A(t₀)‖ + n (h (c₁ ε + c₂ h) + ϑ))`. -/
theorem drsvd_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {QΩ P : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YB YC Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsDRSVDStep F ε ϑ (QΩ n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YB n) (YC n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ)) :=
  lady_windermere hF hL hh hA hΦ hΦ₀ fun n hn =>
    (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)

/-- **Robust global error of DRSVD, final form** (OP-RS-01): for `n h ≤ T` and
`‖Y₀ - A(t₀)‖ ≤ δ`, `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ n ϑ` with `c₀ = c₃ = e^{L T}`,
`c₁ = T e^{L T} bugC₁ L H`, `c₂ = T e^{L T} bugC₂ L B H`. -/
theorem drsvd_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {QΩ P : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YB YC Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsDRSVDStep F ε ϑ (QΩ n) (P n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YB n) (YC n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) (hϑ : 0 ≤ ϑ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * n * ϑ := by
  intro n hn hT
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ bugC₁ L H * ε + bugC₂ L B H * h :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  have h1 := drsvd_global_error hF hL hB hh hhH hA hstep hΦ hΦ₀ n hn
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hin : ‖Y 0 - A t₀‖ + n * (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ)
      ≤ δ + T * (bugC₁ L H * ε + bugC₂ L B H * h) + n * ϑ := by
    have : (n : ℝ) * (h * (bugC₁ L H * ε + bugC₂ L B H * h))
        ≤ T * (bugC₁ L H * ε + bugC₂ L B H * h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hT hg
    nlinarith
  have hpos : 0 ≤ ‖Y 0 - A t₀‖ + n * (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ) := by
    positivity
  calc _ ≤ _ := h1
    _ ≤ Real.exp (L * T) * (δ + T * (bugC₁ L H * ε + bugC₂ L B H * h) + n * ϑ) :=
        mul_le_mul hexp hin hpos (Real.exp_pos _).le
    _ = _ := by ring

end Abstract

/-! ## Matrix layer: the sketched substeps are full-space projected ODEs -/

section MatrixSteps

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- Pushing an ODE solution forward by a continuous linear map `T`: if `S' = f(t, S)` and
`T (f(t, S(t))) = g(t, T S(t))`, then `(T S)' = g(t, T S)`. -/
theorem odeSolution_map {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : ℝ → E₁ → E₁} {g : ℝ → E₂ → E₂}
    {S : ℝ → E₁} {a b : ℝ} (hS : ODESolution f S a b) (T : E₁ →L[ℝ] E₂)
    (hfg : ∀ t ∈ Ico a b, T (f t (S t)) = g t (T (S t))) :
    ODESolution g (fun t => T (S t)) a b :=
  ⟨T.continuous.comp_continuousOn hS.cont, fun t ht => by
    have h := T.hasFDerivAt.comp_hasDerivWithinAt t (hS.deriv t ht)
    rw [hfg t ht] at h
    exact h⟩

/-- **The B-step is a K-step** (OP-RS-01): if `B' = F(B Wᵀ) W` (the dynamical range finder of
arXiv 2410.17091, eq. (7), with `Ω Ω† = W Wᵀ`), then `Y_B = B Wᵀ` solves
`Y_B' = F(Y_B) W Wᵀ`, a BUG K-step with `Q₀ = rightProj W`. -/
theorem bStep_full {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {W : Matrix n k ℝ}
    {Bs : ℝ → Matrix m k ℝ} {a b : ℝ}
    (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs a b) :
    ODESolution (fun t Y => rightProj W (F t Y)) (fun t => Bs t * Wᵀ) a b :=
  odeSolution_map hB (Frobenius.rightMulCLM Wᵀ) fun t _ => by
    simp [rightProj_apply]

/-- The continuous linear map `C ↦ Q Cᵀ`. -/
noncomputable def mulTransposeCLM (Q : Matrix m k ℝ) : Matrix n k ℝ →L[ℝ] Matrix m n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C => Q * Cᵀ
      map_add' := fun X Y => by rw [Matrix.transpose_add, Matrix.mul_add]
      map_smul' := fun c X => by simp [Matrix.transpose_smul, Matrix.mul_smul] }

/-- **The C-step is a one-sided Galerkin step**: if `C' = F(Q Cᵀ)ᵀ Q` (arXiv 2410.17091,
eq. (14)), then `Y_C = Q Cᵀ` solves `Y_C' = Q Qᵀ F(Y_C)`. -/
theorem cStep_full {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Q : Matrix m k ℝ}
    {Cs : ℝ → Matrix n k ℝ} {a b : ℝ}
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs a b) :
    ODESolution (fun t Y => leftProj Q (F t Y)) (fun t => Q * (Cs t)ᵀ) a b :=
  odeSolution_map hC (mulTransposeCLM Q) (g := fun t Y => leftProj Q (F t Y)) fun t _ => by
    change Q * ((F t (Q * (Cs t)ᵀ))ᵀ * Q)ᵀ = Q * Qᵀ * F t (Q * (Cs t)ᵀ)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **The DGN core step is a two-sided Galerkin step**: if `D' = Qᵀ F(Q D Wᵀ) W`
(arXiv 2410.17091, eq. (16)), then `Y_D = Q D Wᵀ` solves `Y_D' = Q Qᵀ F(Y_D) W Wᵀ`. -/
theorem dStep_full {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Q : Matrix m k ℝ} {W : Matrix n l ℝ}
    {Ds : ℝ → Matrix k l ℝ} {a b : ℝ}
    (hD : ODESolution (fun t D => Qᵀ * F t (Q * D * Wᵀ) * W) Ds a b) :
    ODESolution (fun t Y => leftProj Q (rightProj W (F t Y))) (fun t => Q * Ds t * Wᵀ) a b := by
  have h := odeSolution_map hD (Exactness.sandwichCLM Q Wᵀ)
    (g := fun t Y => leftProj Q (rightProj W (F t Y))) fun t _ => by
      change Q * (Qᵀ * F t (Q * Ds t * Wᵀ) * W) * Wᵀ
        = Q * Qᵀ * (F t (Q * Ds t * Wᵀ) * (W * Wᵀ))
      simp only [Matrix.mul_assoc]
  exact h

omit [Fintype m] in
/-- **Augmented sketch**: if `Y₀ = X Wᵀ` (row space in `range W`) and `Wᵀ W = 1`, then
`Y₀ W Wᵀ = Y₀`, so the B-step started at `B(t₀) = Y₀ W` has `Y_B(t₀) = Y₀`. -/
theorem mul_mul_transpose_eq_self [DecidableEq k] {W : Matrix n k ℝ} (hW : Wᵀ * W = 1)
    {Y₀ : Matrix m n ℝ} {X : Matrix m k ℝ} (hY : Y₀ = X * Wᵀ) : Y₀ * W * Wᵀ = Y₀ := by
  subst hY
  rw [Matrix.mul_assoc X, hW, Matrix.mul_one]

omit [Fintype m] in
/-- **Augmented sketch from factors**: if `range V₀ ⊆ range W` (`V₀ = W M`, e.g.
`W = orth([V₀, Ω])`) then `Y₀ W Wᵀ = Y₀` for `Y₀ = U₀ S₀ V₀ᵀ`. -/
theorem mul_mul_transpose_eq_self_of_factors [DecidableEq k] {r : Type*} [Fintype r]
    {W : Matrix n k ℝ} (hW : Wᵀ * W = 1) {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {M : Matrix k r ℝ} (hV : V₀ = W * M) :
    U₀ * S₀ * V₀ᵀ * W * Wᵀ = U₀ * S₀ * V₀ᵀ :=
  mul_mul_transpose_eq_self hW (X := U₀ * S₀ * Mᵀ) (by
    rw [hV, Matrix.transpose_mul, Matrix.mul_assoc (U₀ * S₀)])

/-- **The DRSVD step on matrices is an `IsDRSVDStep`**: orthonormal sketch basis `W`, B-step
`B' = F(B Wᵀ) W`, `B(t₀) = Y₀ W` with augmented sketch `Y₀ W Wᵀ = Y₀`, orthonormal range basis
`Q` capturing `B(t₁)`, C-step `C' = F(Q Cᵀ)ᵀ Q`, `C(t₀) = Y₀ᵀ Q`, and a result `Y₁` within
`ϑ` of `Q C(t₁)ᵀ` (e.g. `Y₁ = EckartYoung.truncation (Q C(t₁)ᵀ) r`).  Hence all bounds of
`IsDRSVDStep` apply to the matrix algorithm. -/
theorem isDRSVDStep_matrix [DecidableEq k] [DecidableEq l]
    {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε ϑ t₀ t₁ : ℝ} {Y₀ Y₁ : Matrix m n ℝ}
    {W : Matrix n k ℝ} (hW : Wᵀ * W = 1) {Q : Matrix m l ℝ} (hQ : Qᵀ * Q = 1)
    {Bs : ℝ → Matrix m k ℝ} (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁)
    (hB₀ : Bs t₀ = Y₀ * W) (haug : Y₀ * W * Wᵀ = Y₀) (hcap : Q * Qᵀ * Bs t₁ = Bs t₁)
    (hε : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - leftProj Q) ((1 - rightProj W) (F t (Bs t₁ * Wᵀ)))‖ ≤ ε)
    {Cs : ℝ → Matrix n l ℝ} (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁)
    (hC₀ : Cs t₀ = Y₀ᵀ * Q) (htr : ‖Y₁ - Q * (Cs t₁)ᵀ‖ ≤ ϑ) :
    IsDRSVDStep F ε ϑ (rightProj W) (leftProj Q) t₀ t₁ Y₀ (fun t => Bs t * Wᵀ)
      (fun t => Q * (Cs t)ᵀ) Y₁ where
  projΩ := isOrthProj_rightProj hW
  projP := isOrthProj_leftProj hQ
  bSol := bStep_full hB
  bStart := by simp only [hB₀, haug]
  rangeCap := by
    change Q * Qᵀ * (Bs t₁ * Wᵀ) = Bs t₁ * Wᵀ
    rw [← Matrix.mul_assoc, hcap]
  bNormal := hε
  cSol := cStep_full hC
  cStart := by
    simp only [hC₀, leftProj_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  trunc := htr

end MatrixSteps

/-! ## Exactness for `F(t, Y) = Ȧ(t)` (OP-RS-07) -/

section Exact

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- **Exact B-step** for `F(t, Y) = Ȧ(t)`: `B(t) = A(t) W` when `B(t₀) = A(t₀) W`. -/
theorem bStep_exact {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
    (hA : IsDerivRHS F A t₀ t₁) {W : Matrix n k ℝ} {Bs : ℝ → Matrix m k ℝ}
    (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁) (hB₀ : Bs t₀ = A t₀ * W) :
    ∀ t ∈ Icc t₀ t₁, Bs t = A t * W := by
  intro t ht
  rw [Exactness.kStepODE_eq_add hA hB t ht, hB₀, Matrix.sub_mul]
  abel

/-- **Exact C-step** for `F(t, Y) = Ȧ(t)`: `C(t) = A(t)ᵀ Q`, i.e. `C(t)ᵀ = Qᵀ A(t)` (this
corrects the transposition slip `C(h)ᵀ = Q A(h)ᵀ` in the proof of Lemma 3.3 of
arXiv 2410.17091, OP-RS-07). -/
theorem cStep_exact {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
    (hA : IsDerivRHS F A t₀ t₁) {Q : Matrix m k ℝ} {Cs : ℝ → Matrix n k ℝ}
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁) (hC₀ : Cs t₀ = (A t₀)ᵀ * Q) :
    ∀ t ∈ Icc t₀ t₁, Cs t = (A t)ᵀ * Q ∧ (Cs t)ᵀ = Qᵀ * A t := by
  intro t ht
  have h : Cs t = (A t)ᵀ * Q := by
    rw [Exactness.lStepODE_eq_add hA hC t ht, hC₀, Matrix.transpose_sub, Matrix.sub_mul]
    abel
  refine ⟨h, ?_⟩
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **Exact core step** of DGN for `F(t, Y) = Ȧ(t)`: `D(t) = Qᵀ A(t) W`. -/
theorem dStep_exact {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ}
    (hA : IsDerivRHS F A t₀ t₁) {Q : Matrix m k ℝ} {W : Matrix n l ℝ} {Ds : ℝ → Matrix k l ℝ}
    (hD : ODESolution (fun t D => Qᵀ * F t (Q * D * Wᵀ) * W) Ds t₀ t₁)
    (hD₀ : Ds t₀ = Qᵀ * A t₀ * W) :
    ∀ t ∈ Icc t₀ t₁, Ds t = Qᵀ * A t * W := by
  intro t ht
  rw [Exactness.factorODE_eq_add hA Qᵀ W (fun D => Q * D * Wᵀ) (fun _ _ => rfl) hD t ht, hD₀,
    Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The truncated SVD `T_r` fixes exactly the matrices of rank `≤ r` (from Eckart–Young). -/
theorem truncation_eq_self_iff [DecidableEq n] (X : Matrix m n ℝ) (r : ℕ) :
    EckartYoung.truncation X r = X ↔ X.rank ≤ r := by
  constructor
  · intro h
    rw [← h]
    exact EckartYoung.rank_truncation_le X r
  · intro h
    have h1 := EckartYoung.norm_sub_truncation_le X h
    rw [sub_self, norm_zero] at h1
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp h1)).symm

/-- **Corrected exactness of DRSVD** (arXiv 2410.17091, Lemma 3.2, corrected per OP-RS-07; also
the exact-reconstruction remark of arXiv 2506.15259, §2.3.1, OP-RA-11 (b)).  For
`F(t, Y) = Ȧ(t)`, if the range basis `Q` captures `A(t₁)`, then the C-step reproduces `A(t₁)`
(`Q C(t₁)ᵀ = A(t₁)`), and the truncated result `T_r(Q C(t₁)ᵀ)` equals `A(t₁)` **iff
`rank A(t₁) ≤ r`**; the paper's hypothesis `rank A(t₁) ≤ r + p` is not sufficient
(`Counterexample.drsvd_not_exact`). -/
theorem drsvd_exact_iff [DecidableEq n] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {Q : Matrix m k ℝ} {Cs : ℝ → Matrix n k ℝ}
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁) (hC₀ : Cs t₀ = (A t₀)ᵀ * Q)
    (hcap : Q * Qᵀ * A t₁ = A t₁) (r : ℕ) :
    Q * (Cs t₁)ᵀ = A t₁ ∧
      (EckartYoung.truncation (Q * (Cs t₁)ᵀ) r = A t₁ ↔ (A t₁).rank ≤ r) := by
  have h := (cStep_exact hA hC hC₀ t₁ ⟨ht, le_rfl⟩).2
  have hY : Q * (Cs t₁)ᵀ = A t₁ := by rw [h, ← Matrix.mul_assoc, hcap]
  exact ⟨hY, by rw [hY, truncation_eq_self_iff]⟩

/-- **Deterministic range finder**: if `Q` captures the exact sketch `A₁ W` and the row range
of `A₁` is reached through `W` (`A₁ = A₁ W Z`; e.g. `rank A₁ ≤ r + p` and `Vᵀ W` of full row
rank), then `Q Qᵀ A₁ = A₁`.  This is the deterministic content of Lemma 2.1/3.1 of
arXiv 2410.17091 (the Gaussian sketch satisfies the row condition almost surely, which is not
formalized). -/
theorem capture_of_sketch {A₁ : Matrix m n ℝ} {W : Matrix n k ℝ} {Q : Matrix m l ℝ}
    (hcapB : Q * Qᵀ * (A₁ * W) = A₁ * W) (hrow : ∃ Z : Matrix k n ℝ, A₁ = A₁ * W * Z) :
    Q * Qᵀ * A₁ = A₁ :=
  Exactness.mul_eq_self_of_capture rfl hcapB hrow

end Exact

/-! ## Generalized Nyström (DGN) -/

section Nystrom

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- **Generalized Nyström identity** (`{1}`-inverse form).  If `Q Qᵀ A = A`, `A = A W Z` and
`G` is a `{1}`-inverse of the core `D = Qᵀ A W` (`D G D = D`, e.g. the Moore–Penrose inverse or
`D⁻¹`), then `A W G Qᵀ A = A`.  This is the identity `A W (Qᵀ A W)† Qᵀ A = A` used in the
proof of Lemma 3.3 of arXiv 2410.17091, with the correct transposition. -/
theorem nystrom_eq_self {A : Matrix m n ℝ} {Q : Matrix m k ℝ} {W : Matrix n l ℝ}
    {G : Matrix l k ℝ} (hcol : Q * Qᵀ * A = A) (hrow : ∃ Z : Matrix l n ℝ, A = A * W * Z)
    (hG : Qᵀ * A * W * G * (Qᵀ * A * W) = Qᵀ * A * W) :
    A * W * G * (Qᵀ * A) = A := by
  obtain ⟨Z, hZ⟩ := hrow
  have h1 : Q * (Qᵀ * A * W) = A * W := by
    simp only [← Matrix.mul_assoc]; rw [hcol]
  have h2 : Qᵀ * A = Qᵀ * A * W * Z := by
    nth_rewrite 1 [hZ]; simp only [Matrix.mul_assoc]
  calc A * W * G * (Qᵀ * A) = Q * (Qᵀ * A * W) * G * (Qᵀ * A * W * Z) := by rw [h1, ← h2]
    _ = Q * (Qᵀ * A * W * G * (Qᵀ * A * W)) * Z := by simp only [Matrix.mul_assoc]
    _ = Q * (Qᵀ * A * W) * Z := by rw [hG]
    _ = A := by rw [h1, ← hZ]

omit [Fintype m] in
/-- A Nyström assembly `B G Cᵀ` has rank at most `rank G`; in DGN, `G = T_r(D)†` has rank
`≤ r`, so DGN can only be exact for `rank A(h) ≤ r`. -/
theorem rank_assembly_le (Bm : Matrix m l ℝ) (G : Matrix l k ℝ) (C : Matrix n k ℝ) :
    (Bm * G * Cᵀ).rank ≤ G.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- **Corrected exactness of DGN** (arXiv 2410.17091, Lemma 3.3, corrected per OP-RS-07).  For
`F(t, Y) = Ȧ(t)` with `Q` capturing `A(t₁)` and `A(t₁) = A(t₁) W Z`:
if `rank A(t₁) ≤ r` and `G` is a `{1}`-inverse of `T_r(D(t₁))`, then
`B(t₁) G C(t₁)ᵀ = A(t₁)`; conversely, if `rank G ≤ r` (true for the pseudo-inverse of
`T_r(D(t₁))`) and the method is exact, then `rank A(t₁) ≤ r`. -/
theorem dgn_exact [DecidableEq l] {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {A : ℝ → Matrix m n ℝ}
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {Q : Matrix m k ℝ}
    {W : Matrix n l ℝ} {Bs : ℝ → Matrix m l ℝ} {Cs : ℝ → Matrix n k ℝ} {Ds : ℝ → Matrix k l ℝ}
    (hB : ODESolution (fun t X => F t (X * Wᵀ) * W) Bs t₀ t₁) (hB₀ : Bs t₀ = A t₀ * W)
    (hC : ODESolution (fun t C => (F t (Q * Cᵀ))ᵀ * Q) Cs t₀ t₁) (hC₀ : Cs t₀ = (A t₀)ᵀ * Q)
    (hD : ODESolution (fun t D => Qᵀ * F t (Q * D * Wᵀ) * W) Ds t₀ t₁)
    (hD₀ : Ds t₀ = Qᵀ * A t₀ * W)
    (hcol : Q * Qᵀ * A t₁ = A t₁) (hrow : ∃ Z : Matrix l n ℝ, A t₁ = A t₁ * W * Z)
    {r : ℕ} {G : Matrix l k ℝ} :
    ((A t₁).rank ≤ r →
      EckartYoung.truncation (Ds t₁) r * G * EckartYoung.truncation (Ds t₁) r
        = EckartYoung.truncation (Ds t₁) r → Bs t₁ * G * (Cs t₁)ᵀ = A t₁) ∧
    (G.rank ≤ r → Bs t₁ * G * (Cs t₁)ᵀ = A t₁ → (A t₁).rank ≤ r) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have eB := bStep_exact hA hB hB₀ t₁ h1
  have eC := (cStep_exact hA hC hC₀ t₁ h1).2
  have eD := dStep_exact hA hD hD₀ t₁ h1
  refine ⟨fun hr hG => ?_, fun hr hex => ?_⟩
  · have hDr : (Ds t₁).rank ≤ r := by
      rw [eD]
      exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hr
    rw [(truncation_eq_self_iff _ r).2 hDr, eD] at hG
    rw [eB, eC]
    exact nystrom_eq_self hcol hrow hG
  · rw [← hex]
    exact (rank_assembly_le _ _ _).trans hr

end Nystrom

/-! ## Exactness under over-approximation (OP-RA-11 (a)) -/

section OverApprox

variable {m n r p q k : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]
  [Fintype k]

omit [Fintype m] [Fintype p] [Fintype q] in
/-- **Range condition from a rank-deficient factorization** (OP-RA-11 (a)).  If
`A = U S Vᵀ` with `k` columns (`k ≤ r`, `rank A < r` allowed) and `G = S (Vᵀ V₀)` (`k × r`)
has a right inverse `G'` — i.e. `X ↦ X V₀ V₀ᵀ` is injective on the row space of `A` — then
`A = A V₀ C` with `C = G' S Vᵀ`.  For `k = r` and `S`, `Vᵀ V₀` invertible this is the
non-degeneracy hypothesis of Ceruti–Lubich (arXiv 2010.02022, Lemma 1). -/
theorem exists_eq_mul_mul_of_rightInv [DecidableEq k] {U : Matrix m k ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} {V₀ : Matrix n r ℝ} {A : Matrix m n ℝ} (hA : A = U * S * Vᵀ)
    {G' : Matrix r k ℝ} (hG : S * (Vᵀ * V₀) * G' = 1) :
    ∃ C : Matrix r n ℝ, A = A * V₀ * C := by
  refine ⟨G' * S * Vᵀ, ?_⟩
  have h1 : ∀ X : Matrix k n ℝ, S * (Vᵀ * (V₀ * (G' * X))) = X := fun X => by
    simp only [← Matrix.mul_assoc] at hG ⊢
    rw [hG, Matrix.one_mul]
  subst hA
  simp only [Matrix.mul_assoc, h1]

omit [Fintype k] in
/-- **BUG exactness under over-approximation** (OP-RA-11 (a); generalizes Ceruti–Lubich,
arXiv 2010.02022, Theorem 3).  If `A₁ = A₁ V₀ C` and `A₁ᵀ = A₁ᵀ U₀ D` (e.g. via
`exists_eq_mul_mul_of_rightInv`, for `rank A₁ < r`), and the new bases capture the K- and
L-step results, then the BUG step for `F = Ȧ` is exact. -/
theorem bug_exact_of_range [DecidableEq r] {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {A₀ A₁ : Matrix m n ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) (hrow : ∃ C : Matrix r n ℝ, A₁ = A₁ * V₀ * C)
    (hcol : ∃ D : Matrix r m ℝ, A₁ᵀ = A₁ᵀ * U₀ * D) {U₁ : Matrix m p ℝ} {V₁ : Matrix n q ℝ}
    {S₁ : Matrix p q ℝ}
    (hU₁ : U₁ * U₁ᵀ * (U₀ * S₀ + (A₁ - A₀) * V₀) = U₀ * S₀ + (A₁ - A₀) * V₀)
    (hV₁ : V₁ * V₁ᵀ * (V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀) = V₀ * S₀ᵀ + (A₁ - A₀)ᵀ * U₀)
    (hS₁ : S₁ = U₁ᵀ * U₀ * S₀ * (V₁ᵀ * V₀)ᵀ + U₁ᵀ * (A₁ - A₀) * V₁) :
    U₁ * S₁ * V₁ᵀ = A₁ := by
  have hP := Exactness.mul_eq_self_of_capture (Exactness.kStep_eq hV₀ hY₀) hU₁ hrow
  have hQ := Exactness.mul_eq_self_of_capture (Exactness.lStep_eq hU₀ hY₀) hV₁ hcol
  have hQ' : A₁ * (V₁ * V₁ᵀ) = A₁ := by
    have := congrArg Matrix.transpose hQ
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at this
    exact this
  rw [(Exactness.bug_eq_proj hY₀ hS₁).2, hP, hQ']

omit [Fintype q] [Fintype k] in
/-- **KSL exactness under over-approximation** (OP-RA-11 (a); generalizes Lubich–Oseledets,
arXiv 1301.1058, Theorem 4.1): only the row range condition `A₁ = A₁ V₀ C` is needed. -/
theorem ksl_exact_of_range [DecidableEq r] {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {A₀ A₁ : Matrix m n ℝ} (hV₀ : V₀ᵀ * V₀ = 1)
    (hY₀ : U₀ * S₀ * V₀ᵀ = A₀) (hrow : ∃ C : Matrix r n ℝ, A₁ = A₁ * V₀ * C)
    {K₁ : Matrix m r ℝ} {U₁ : Matrix m p ℝ} {Ŝ₁ St₀ : Matrix p r ℝ} {L₁ : Matrix n p ℝ}
    (hK₁ : K₁ = U₀ * S₀ + (A₁ - A₀) * V₀) (hU₁ : U₁ * U₁ᵀ * K₁ = K₁)
    (hŜ₁ : Ŝ₁ = U₁ᵀ * K₁) (hSt₀ : St₀ = Ŝ₁ - U₁ᵀ * (A₁ - A₀) * V₀)
    (hL₁ : L₁ = V₀ * St₀ᵀ + (A₁ - A₀)ᵀ * U₁) :
    U₁ * L₁ᵀ = A₁ := by
  rw [Exactness.ksl_exact_iff hY₀ hK₁ hŜ₁ hSt₀ hL₁]
  rw [hK₁] at hU₁
  exact Exactness.mul_eq_self_of_capture (Exactness.kStep_eq hV₀ hY₀) hU₁ hrow

end OverApprox

/-! ## Counterexample to `rank ≤ r + p` (OP-RS-07) -/

namespace Counterexample

/-- `Y₀ = diag(1, 0)`. -/
noncomputable def Y₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- `G = diag(0, 1)`. -/
noncomputable def G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]

/-- `A(t) = Y₀ + t G`. -/
noncomputable def A (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Y₀ + t • G

/-- `A(1) = I`. -/
theorem A_one : A 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, Y₀, G]

/-- `rank A(1) = 2 = r + p`. -/
theorem rank_A_one : (A 1).rank = 2 := by
  rw [A_one, Matrix.rank_one, Fintype.card_fin]

/-- `rank Y₀ = 1 = r`. -/
theorem rank_Y₀ : Y₀.rank = 1 := by
  have : Y₀ = Matrix.diagonal ![1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Y₀]
  rw [this, Matrix.rank_diagonal, Fintype.card_eq_one_iff]
  refine ⟨⟨0, by simp⟩, fun ⟨y, hy⟩ => ?_⟩
  fin_cases y
  · rfl
  · simp at hy

/-- `rank G = 1 = p`. -/
theorem rank_G : G.rank = 1 := by
  have : G = Matrix.diagonal ![0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [G]
  rw [this, Matrix.rank_diagonal, Fintype.card_eq_one_iff]
  refine ⟨⟨1, by simp⟩, fun ⟨y, hy⟩ => ?_⟩
  fin_cases y
  · simp at hy
  · rfl

/-- The C-step trajectory `C(t) = A(t)ᵀ`. -/
noncomputable def Cs (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Y₀ᵀ + t • Gᵀ

/-- `F(t, Y) = G = Ȧ(t)`. -/
theorem isDerivRHS_A : IsDerivRHS (fun _ _ => G) A 0 1 :=
  Exactness.isDerivRHS_add_smul Y₀ G 0 1

/-- `C(t) = Y₀ᵀ + t Gᵀ` solves the C-step with `Q = I`. -/
theorem cSol : ODESolution (fun t C => (((fun _ _ => G) : ℝ → Matrix (Fin 2) (Fin 2) ℝ → _) t
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) * Cᵀ))ᵀ * 1) Cs 0 1 :=
  Exactness.odeSolution_add_smul_of_const (fun _ _ => by simp) Y₀ᵀ 0 1

/-- **Counterexample to Lemma 3.2 of arXiv 2410.17091 as stated** (OP-RS-07): `r = p = 1`,
`rank Y₀ = r`, `rank G = p`, `rank A(1) ≤ r + p`, the range inclusion `Range A(t) ⊆ Range Q`
holds for all `t` (`Q = I`), the C-step is exact before truncation, and yet the DRSVD result
`T_1(Q C(1)ᵀ)` differs from `A(1)`. -/
theorem drsvd_not_exact :
    Y₀.rank = 1 ∧ G.rank = 1 ∧ (A 1).rank ≤ 1 + 1 ∧
      (∀ t, (1 : Matrix (Fin 2) (Fin 2) ℝ) * 1ᵀ * A t = A t) ∧
      Cs 0 = (A 0)ᵀ * 1 ∧ (1 : Matrix (Fin 2) (Fin 2) ℝ) * (Cs 1)ᵀ = A 1 ∧
      EckartYoung.truncation ((1 : Matrix (Fin 2) (Fin 2) ℝ) * (Cs 1)ᵀ) 1 ≠ A 1 := by
  have hcap : (1 : Matrix (Fin 2) (Fin 2) ℝ) * 1ᵀ * A 1 = A 1 := by simp
  have hC₀ : Cs 0 = (A 0)ᵀ * 1 := by simp [Cs, A]
  obtain ⟨hY, hiff⟩ := drsvd_exact_iff zero_le_one isDerivRHS_A cSol hC₀ hcap 1
  refine ⟨rank_Y₀, rank_G, by rw [rank_A_one], fun t => by simp, hC₀, hY, fun h => ?_⟩
  have := hiff.1 h
  rw [rank_A_one] at this
  omega

/-- The sketch vector `w = e₂`. -/
noncomputable def w : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- Non-augmented sketch: the B-step starts at `Y₀ w wᵀ ≠ Y₀` although `wᵀ w = 1`. -/
theorem not_augmented_start : Y₀ * w * wᵀ ≠ Y₀ ∧ wᵀ * w = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h 0) 0
    simp [Y₀, w, Matrix.mul_apply] at this
  · ext i j
    fin_cases i; fin_cases j
    simp [w, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Counterexample to Lemma 3.3 of arXiv 2410.17091 as stated** (OP-RS-07): in the same
setting, every Nyström assembly through a core of rank `≤ r = 1` (in particular
`B(1) T_1(D(1))† C(1)ᵀ`) differs from `A(1)`, although `rank A(1) ≤ r + p`. -/
theorem dgn_not_exact (Bm C G' : Matrix (Fin 2) (Fin 2) ℝ) (hG : G'.rank ≤ 1) :
    Bm * G' * Cᵀ ≠ A 1 := by
  intro h
  have := (rank_assembly_le Bm G' C).trans hG
  rw [h, rank_A_one] at this
  omega

end Counterexample

/-! ## Satisfiability of the hypotheses -/

/-- The hypotheses of one DRSVD step are jointly satisfiable with a nonzero vector field: on `ℝ`,
`F ≡ 1`, all projectors the identity, `Y₀ = 0`, trajectories `t ↦ t` on `[0, 1]`, `Y₁ = 1`,
`ε = ϑ = 0`. -/
example : IsDRSVDStep (E := ℝ) (fun _ _ => 1) 0 0 1 1 0 1 0 (fun t => t) (fun t => t) 1 where
  projΩ := IsOrthProj.one
  projP := IsOrthProj.one
  bSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  bStart := rfl
  rangeCap := rfl
  bNormal _ _ := by simp
  cSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  cStart := by simp
  trunc := by simp

namespace MatrixExample

/-- The forcing `G = e₁ e₂ᵀ` on `ℝ^{2×2}`. -/
noncomputable def Gm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The sketch basis `W = e₂` (a rank-one sketch, not the identity). -/
noncomputable def W : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The range basis `Q = e₁` (a rank-one range basis, not the identity). -/
noncomputable def Q : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The B-step trajectory `B(t) = t G W`. -/
noncomputable def Bs (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := 0 + t • (Gm * W)

/-- The C-step trajectory `C(t) = t Gᵀ Q`. -/
noncomputable def Cs (t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := 0 + t • (Gmᵀ * Q)

lemma W_orth : Wᵀ * W = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [W, Matrix.mul_apply, Fin.sum_univ_two]

lemma Q_orth : Qᵀ * Q = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [Q, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Non-degenerate satisfiability of the matrix DRSVD step**: on `ℝ^{2×2}` with the constant
nonzero field `F ≡ G = e₁ e₂ᵀ`, `Y₀ = 0`, the rank-one sketch `W = e₂` (`rightProj W ≠ 1`) and
the rank-one range basis `Q = e₁` (`leftProj Q ≠ 1`), all hypotheses of `isDRSVDStep_matrix`
hold with `ε = ϑ = 0` and `Y₁ = G`; the step reproduces the exact solution `A(1) = G`. -/
example : IsDRSVDStep (fun _ _ => Gm) 0 0 (rightProj W) (leftProj Q) 0 1 0
    (fun t => Bs t * Wᵀ) (fun t => Q * (Cs t)ᵀ) Gm :=
  isDRSVDStep_matrix W_orth Q_orth
    (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp [Bs])
    (by simp)
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Bs, Gm, W, Q, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct])
    (fun _ _ => by
      have h0 : Gm - Gm * W * Wᵀ - Q * Qᵀ * (Gm - Gm * W * Wᵀ) = 0 := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Gm, W, Q, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
            Matrix.vecHead, Matrix.vecTail]
      simp [h0])
    (Exactness.odeSolution_add_smul_of_const (fun _ _ => rfl) _ 0 1) (by simp [Cs])
    (by
      have h0 : Gm - Q * (Cs 1)ᵀ = 0 := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Cs, Gm, Q, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      simp [h0])

end MatrixExample

namespace OverApproxExample

/-- `e₁ ∈ ℝ³`. -/
noncomputable def e₁ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 0; 0]

/-- `V₀ = [e₁, e₂]`. -/
noncomputable def V₀ : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- The over-approximation hypothesis is satisfiable with `k = 1 < r = 2`: `A = e₁ e₁ᵀ` on
`ℝ³`, `V₀ = [e₁, e₂]`; `Vᵀ V₀ = [1, 0]` has the right inverse `[1; 0]`. -/
example : ∃ C : Matrix (Fin 2) (Fin 3) ℝ,
    e₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * e₁ᵀ
      = e₁ * (1 : Matrix (Fin 1) (Fin 1) ℝ) * e₁ᵀ * V₀ * C :=
  exists_eq_mul_mul_of_rightInv (U := e₁) (S := 1) (V := e₁) (V₀ := V₀) rfl (G' := !![1; 0])
    (by
      ext i j
      fin_cases i; fin_cases j
      simp [e₁, V₀, Matrix.mul_apply, Fin.sum_univ_succ])

end OverApproxExample

end LeanDLRA.RandomizedBUG
