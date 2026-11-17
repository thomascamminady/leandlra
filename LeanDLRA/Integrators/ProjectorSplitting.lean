import LeanDLRA.Integrators.KStep
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Matrix.Projectors

/-!
# Robust error bound of the projector-splitting (KSL) integrator

This file formalises the robust error bound of the Lubich–Oseledets projector-splitting
integrator for dynamical low-rank approximation (Lubich–Oseledets, *A projector-splitting
integrator for dynamical low-rank approximation*, BIT 2014, [LubichOseledets2014, §3]) proved by
Kieri–Lubich–Walach (*Discretized dynamical low-rank approximation in the presence of small
singular values*, SINUM 2016, Theorem 2.1; quoted as Theorem 2 in Ceruti–Lubich,
[CerutiLubich2022]): the local error is `O(h (h + ε))` and the global error is `O(δ + ε + h)`, with
constants that only depend on the Lipschitz constant `L`, the bound `B` of the vector field and
the final time, and **not on singular values**.

## The integrator as full-space trajectories

As in the rest of the library, the integrator is written abstractly on a real inner product
space `E` with orthogonal projectors. The splitting is that of [LubichOseledets2014, §3.1] (abstract
formulation) and §3.2 (practical algorithm); the substep differential equations with a general
right-hand side `F(t, ·)` are those of Kieri–Lubich–Walach 2016, §2, as restated in
[CerutiLubich2022, §2] One step from `Y₀ = U₀ S₀ V₀ᵀ` at `t₀` to `t₁ = t₀ + h` consists of, with
`Q₀ X = X V₀ V₀ᵀ` and `P₁ X = U₁ U₁ᵀ X`:

* **K-step** `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, `K(t₁) = U₁ Ŝ₁`: the trajectory
  `YK = K V₀ᵀ` solves `YK' = Q₀ F(t, YK)`, `YK t₀ = Y₀`, and the new basis captures it:
  `P₁ (YK t₁) = YK t₁`;
* **backward S-step** `S' = -U₁ᵀ F(t, U₁ S V₀ᵀ) V₀`, `S(t₀) = Ŝ₁`: the trajectory
  `YS = U₁ S V₀ᵀ` solves `YS' = -P₁ Q₀ F(t, YS)`, `YS t₀ = YK t₁`;
* **L-step** `L' = F(t, U₁ Lᵀ)ᵀ U₁`, `L(t₀) = V₀ S̃₀ᵀ`: the trajectory `YL = U₁ Lᵀ` solves
  `YL' = P₁ F(t, YL)`, `YL t₀ = YS t₁`, and the new approximation is `Y₁ = YL t₁`.

The normal-component assumption (assumption 2 of Theorem 2 of [CerutiLubich2022]) is only used at
the point `YK t₁ = U₁ Ŝ₁ V₀ᵀ` (which lies on the rank-`r` manifold only if `Ŝ₁` is invertible),
in the form `‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε`.  All hypotheses of one step are bundled
in the predicate `IsKSLStep`.

## Main results

With `F` `L`-Lipschitz and bounded by `B`:

* `ksl_proj_error`: `‖Y₁ - P₁ A(t₁)‖ ≤ 6 L B h²`;
* `ksl_local_error_sharp`, `ksl_local_error` (local error, cf. Kieri–Lubich–Walach 2016, proof of
  Theorem 2.1, with improved constants, see below): `‖Y₁ - A(t₁)‖ ≤ h (10 L B h + ε)
  ≤ h (11 L B h + ε)`; the coefficient `1` of `ε h` is attained (`KSLExample`);
* `ksl_S_mem_range`, `ksl_mem_range`: the S- and L-step trajectories stay in the range of `P₁`;
  in particular `P₁ Y₁ = Y₁` (`IsKSLStep.mem_range`); `ksl_K_mem_range_Q₀`,
  `ksl_S_mem_range_Q₀`: the K- and S-step trajectories stay in the range of `Q₀` (for commuting
  `P₁`, `Q₀`), i.e. `YS = U₁ S V₀ᵀ` lies in the range of `P₁ Q₀`;
* `ksl_global_error`, `ksl_global_error_le` (global error, Theorem 2.1 of Kieri–Lubich–Walach,
  Theorem 2 of [CerutiLubich2022]): `‖Yₙ - A(tₙ)‖ ≤ c₀ δ + c₁ ε + c₂ h` with `c₀ = e^{L T}`,
  `c₁ = T e^{L T}`, `c₂ = 11 L B T e^{L T}`; the term `c₁ ε` is attained (`KSLExample`);
* **matrix layer, normal component** (`P₁ = leftProj U₁`, `Q₀ = rightProj V₀`):
  `ksl_normal_le_of_factored` and `ksl_kNormal_of_factored` derive the point hypothesis
  `kNormal` of `IsKSLStep` from the *factored* assumption
  `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` (all `U`, `V` with orthonormal columns and **all**
  `S`, singular or not); `normal_le_of_invertible_core` and `factored_normal_of_manifold` derive
  the factored assumption from the paper's assumption `‖(I - P(Y)) F(t, Y)‖ ≤ ε` on the manifold
  (invertible `S` only) by a density argument, for `F t` continuous; `ksl_kNormal_of_manifold`
  combines both;
* **inexact substeps** (cf. Kieri–Lubich–Walach 2016, §2.6.3; [CerutiLubich2022] only states, after
  Theorem 2, that the additional error is bounded in terms of the local errors of the inexact
  substeps): if the three substep differential equations are solved only approximately, with
  local errors `ηK`, `ηS`, `ηL` (`IsInexactKSLStep`), then `ksl_local_error_inexact` gives
  `‖Y₁ - A(t₁)‖ ≤ h (11 L B h + ε) + (2 + 3 L h) (ηK + ηS + ηL)`, and
  `ksl_global_error_inexact` shows that the global error grows by the accumulated substep errors,
  `e^{L T} (2 + 3 L H) ∑ₖ (ηK k + ηS k + ηL k)` (perturbed discrete Grönwall /
  Lady Windermere's fan); `ksl_global_error_inexact_le` is the form with a uniform bound `η`,
  where the additional term is `e^{L T} (2 + 3 L H) n η ≤ e^{L T} (2 + 3 L H) T η / h`.
  `substep_error_of_defect` bounds the local error of a substep solved with a continuous
  approximation of defect `η` by `h e^{L h} η`.

## Proof of the local error bound

By the K-step capture lemma `kstep_capture`, `‖(1 - P₁) A(t₁)‖ ≤ h (4 L B h + ε)`.  For the
component in the range of `P₁`, consider

    g = P₁ YK + (YS - YS t₀) + (YL - YL t₀) - P₁ A.

Then `g t₀ = 0`, `g t₁ = Y₁ - P₁ A(t₁)` (since `P₁ YK t₁ = YK t₁ = YS t₀` and `YL t₀ = YS t₁`),
and

    g' = P₁ Q₀ (F(t, YK) - F(t, YS)) + P₁ (F(t, YL) - F(t, A)),

so that `‖g'‖ ≤ L ‖YK - YS‖ + L ‖YL - A‖ ≤ 2 L B h + 4 L B h`, because every substep trajectory
moves at most `B h`.  The mean value inequality gives `‖Y₁ - P₁ A(t₁)‖ ≤ 6 L B h²`.  No
commutation of `P₁` and `Q₀` is needed.  The exact results are obtained as the special case
`ηK = ηS = ηL = 0` of the inexact ones, whose proof is the same argument with the substep errors
added in.

## Deviations from the paper

* Kieri–Lubich–Walach (and Ceruti–Lubich) state the global result as `c₀ δ + c₁ ε + c₂ h` with
  constants depending only on `L`, `B`, `T`; we give explicit constants.  The local bound of
  Kieri–Lubich–Walach does have explicit constants: as quoted in [CerutiLubich2022, eq. (5)], it
  is `(4 e^{L h} B L + 9 B L) h² + (3 e^{L h} + 4) ε h + e^{L h} δ`.  For an exact starting value
  (`δ = 0`, the setting of a local error) our bound `h (10 L B h + ε)` improves both constants
  (`10 < 4 e^{L h} + 9` and `1 < 3 e^{L h} + 4`), and the coefficient `1` of `ε h` cannot be
  improved (`KSLExample`).  It is proved by the direct argument above (the function `g`), which
  differs from the comparison of the substeps with the exact solution in Kieri–Lubich–Walach,
  and it needs the normal-component bound only at `YK t₁`.  The global constants
  `c₁ = T e^{L T}`, `c₂ = 11 L B T e^{L T}` follow by Lady Windermere's fan.
* The normal-component assumption is used only at the point `YK t₁` (for inexact substeps: at
  the computed K-step result `K₁`).  The paper assumes `‖(I - P(Y)) F(t, Y)‖ ≤ ε` for `Y` on the
  rank-`r` manifold `M` (near `A(t)`), but `YK t₁ = U₁ Ŝ₁ V₀ᵀ` lies on `M` only when `Ŝ₁` is
  invertible, and only then is `I - P(YK t₁) = (1 - P₁) (1 - Q₀)`.  The bridge is formalised in
  the matrix layer at the end of this file: the *factored* assumption (all `S`, including
  singular ones) gives `kNormal` at every matrix fixed by `P₁` and `Q₀`, with no invertibility
  of `Ŝ₁` (`ksl_normal_le_of_factored`, `ksl_kNormal_of_factored`); the assumption on `M` implies
  the factored one through the density of invertible cores `Ŝ₁ + η I` and continuity of `F t`
  (`normal_le_of_invertible_core`, `factored_normal_of_manifold`, `ksl_kNormal_of_manifold`).
  This is where the independence of singular values enters.  The instantiation of the whole
  `IsKSLStep` from the factor ODEs of the matrix algorithm is
  `MatrixKSL.IsStep.isKSLStep_of_factored` (`Integrators/Matrix/ProjectorSplitting.lean`).
  Our assumptions are global (all `t`
  and all factored matrices), whereas the paper only requires them in a neighbourhood of the
  exact solution.
* The exact flows `Φ n` from the numerical values (needed for Lady Windermere's fan) are
  hypotheses; their existence for globally Lipschitz, time-continuous `F` is proved in
  `Foundations/Existence.lean`.  Similarly the exact substep solutions are hypotheses.
* In the global theorems the right projector `Q n` of step `n` is arbitrary: we do not require
  that it is the projector `X ↦ X V_n V_nᵀ` of the basis computed in the L-step of step `n - 1`,
  so the theorems are slightly more general than the algorithm.
* Inexact substeps: the inexactness is measured by the *local errors* of the substeps, i.e. the
  distance of the computed result of each substep from the exact solution of the substep
  differential equation started at the computed input of that substep.  The new basis `U₁` is
  computed from the *computed* K-step result `K₁` (`P₁ K₁ = K₁`), and the S- and L-steps start
  from computed values.  In matrix form the full-space local errors equal the local errors of
  `K`, `S` and `L`, because `U₁` and `V₀` have orthonormal columns.  The explicit form of the
  bounds is ours; Kieri–Lubich–Walach 2016 (§2.6.3) is not available in this repository, so the
  attribution of these results is by reference to the summary in [CerutiLubich2022].
-/

open Set Filter Topology

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Auxiliary lemmas -/

section Aux

/-- **Range invariance.**  If all values of the vector field `f` are fixed by a continuous linear
map `P` (e.g. `f = P F` or `f = -P F` with an idempotent `P`) and the solution of `y' = f(t, y)`
starts in the fixed space of `P`, then it stays there. -/
theorem ODESolution.fixed_of_fixed_field {f : ℝ → E → E} {P : E →L[ℝ] E} {y : ℝ → E}
    {a b : ℝ} (hy : ODESolution f y a b) (hf : ∀ t x, P (f t x) = f t x)
    (h0 : P (y a) = y a) : ∀ t ∈ Icc a b, P (y t) = y t := by
  intro t ht
  set z : ℝ → E := fun s => y s - P (y s) with hz
  have hzc : ContinuousOn z (Icc a b) := hy.cont.sub (P.continuous.comp_continuousOn hy.cont)
  have hzd : ∀ s ∈ Ico a b, HasDerivWithinAt z (f s (y s) - P (f s (y s))) (Ici s) s :=
    fun s hs => (hy.deriv s hs).sub (P.hasFDerivAt.comp_hasDerivWithinAt s (hy.deriv s hs))
  have hzb : ∀ s ∈ Ico a b, ‖f s (y s) - P (f s (y s))‖ ≤ 0 := fun s _ => by simp [hf]
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hzc hzd hzb t ht
  have hza : z a = 0 := by simp [hz, h0]
  rw [hza, sub_zero, zero_mul] at hmvt
  have h1 : z t = 0 := norm_le_zero_iff.1 hmvt
  simp only [hz] at h1
  exact (sub_eq_zero.1 h1).symm

/-- The vector field `-P Q F` of the backward S-step is bounded by `B` if `F` is. -/
lemma isBoundedField_kslS {F : ℝ → E → E} {B : ℝ} (hB : IsBoundedField F B)
    {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q) :
    IsBoundedField (fun t x => -P (Q (F t x))) B := fun t x => by
  rw [norm_neg]
  exact (hP.norm_le _).trans ((hQ.norm_le _).trans (hB t x))

/-- Pointwise derivative bound of the capture lemma, at an arbitrary reference point `z` of the
normal-component assumption: if `‖a - y‖ ≤ d₁`, `‖a - z‖ ≤ d₂` and
`‖(1 - P) ((1 - Q) (F t z))‖ ≤ ε`, then `‖(1 - P) (F t a - Q (F t y))‖ ≤ L d₁ + L d₂ + ε`. -/
lemma norm_compl_sub_le_of_dist {F : ℝ → E → E} {L ε : ℝ} (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q) (t : ℝ)
    {a y z : E} {d₁ d₂ : ℝ} (h₁ : ‖a - y‖ ≤ d₁) (h₂ : ‖a - z‖ ≤ d₂)
    (hε : ‖(1 - P) ((1 - Q) (F t z))‖ ≤ ε) :
    ‖(1 - P) (F t a - Q (F t y))‖ ≤ L * d₁ + L * d₂ + ε := by
  have hsplit : (1 - P) (F t a - Q (F t y)) =
      (1 - P) (Q (F t a - F t y)) + (1 - P) ((1 - Q) (F t a - F t z))
        + (1 - P) ((1 - Q) (F t z)) := by
    rw [← map_add, ← map_add]
    congr 1
    simp only [sub_apply, one_apply_eq_self, map_sub]
    abel
  have hc1 : ‖(1 - P) (Q (F t a - F t y))‖ ≤ L * d₁ :=
    calc _ ≤ ‖Q (F t a - F t y)‖ := hP.compl.norm_le _
      _ ≤ ‖F t a - F t y‖ := hQ.norm_le _
      _ ≤ L * ‖a - y‖ := hF t _ _
      _ ≤ L * d₁ := mul_le_mul_of_nonneg_left h₁ hL
  have hc2 : ‖(1 - P) ((1 - Q) (F t a - F t z))‖ ≤ L * d₂ :=
    calc _ ≤ ‖(1 - Q) (F t a - F t z)‖ := hP.compl.norm_le _
      _ ≤ ‖F t a - F t z‖ := hQ.compl.norm_le _
      _ ≤ L * ‖a - z‖ := hF t _ _
      _ ≤ L * d₂ := mul_le_mul_of_nonneg_left h₂ hL
  rw [hsplit]
  have h3 := norm_add₃_le (a := (1 - P) (Q (F t a - F t y)))
    (b := (1 - P) ((1 - Q) (F t a - F t z))) (c := (1 - P) ((1 - Q) (F t z)))
  linarith

/-- **Local error of a substep solved with a defect.**  If a substep `y' = f(t, y)` (with `f`
`L`-Lipschitz, `L ≥ 0`) is solved approximately by a continuous approximation `z` (e.g. the
continuous extension of a Runge–Kutta solution) whose defect is at most `η`,
`‖z'(t) - f(t, z(t))‖ ≤ η`, and `z t₀ = y t₀`, then the local error of the substep is
`‖z t₁ - y t₁‖ ≤ h e^{L h} η` (`t₁ = t₀ + h`, `h ≥ 0`).  Together with `ksl_local_error_inexact`
this bounds the error of the KSL integrator with inexact substeps in terms of the defects. -/
theorem substep_error_of_defect {f : ℝ → E → E} {L η : ℝ} (hf : IsLipschitzField f L)
    (hL : 0 ≤ L) (hη : 0 ≤ η) {y z v : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hy : ODESolution f y t₀ t₁) (hzc : ContinuousOn z (Icc t₀ t₁))
    (hzd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt z (v t) (Ici t) t)
    (hdef : ∀ t ∈ Ico t₀ t₁, ‖v t - f t (z t)‖ ≤ η) (h₀ : z t₀ = y t₀) :
    ‖z t₁ - y t₁‖ ≤ h * (Real.exp (L * h) * η) := by
  have hle : t₀ ≤ t₁ := by linarith
  have h1 := norm_sub_le_gronwallBound hf hL (y := z) (z := y) (u := v)
    (w := fun t => f t (y t)) (ηy := η) (ηz := 0) (δ := 0) hzc hzd hdef hy.cont hy.deriv
    (fun _ _ => by simp) (by simp [h₀]) t₁ ⟨hle, le_rfl⟩
  rw [add_zero, show t₁ - t₀ = h by rw [ht₁]; ring] at h1
  have h2 := gronwallBound_le_exp_mul (δ := 0) (x := h) hL hη
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Aux

/-! ### The local error -/

section Local

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {Y₀ : E}
  {A YK YS YL : ℝ → E}

/-- **K-step capture lemma for an inexact K-step.**  As `kstep_capture`, but the new basis
captures a computed value `K₁` (`P₁ K₁ = K₁`) with `‖K₁ - YK t₁‖ ≤ ηK`, and the normal-component
assumption holds at `K₁`.  Then `‖(1 - P₁) A(t₁)‖ ≤ h (4 L B h + L ηK + ε) + ηK`. -/
theorem kstep_capture_inexact (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀) {K₁ : E} {ηK : ℝ}
    (hKerr : ‖K₁ - YK t₁‖ ≤ ηK) (hKcap : P₁ K₁ = K₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + L * ηK + ε) + ηK := by
  have hle : t₀ ≤ t₁ := by linarith
  have hBK : IsBoundedField (fun t x => Q₀ (F t x)) B := hB.comp_contraction Q₀ hQ₀.norm_le
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - Q₀ (F t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖
      ≤ 4 * L * B * h + L * ηK + ε := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have ht₁I : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
    have hd1 : ‖A t - YK t‖ ≤ 2 * B * h :=
      norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t htI t htI
    have hd2 : ‖A t - K₁‖ ≤ 2 * B * h + ηK := by
      have e1 := norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t htI t₁ ht₁I
      have e2 := norm_sub_le_norm_sub_add_norm_sub (A t) (YK t₁) K₁
      rw [norm_sub_rev (YK t₁)] at e2
      linarith
    have := norm_compl_sub_le_of_dist hF hL hP₁ hQ₀ t hd1 hd2 (hε t htI)
    linarith
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, sub_zero, hlen] at hmvt
  have hdec : (1 - P₁) (A t₁) = g t₁ + (1 - P₁) (YK t₁ - K₁) := by
    simp only [hg, map_sub, sub_apply, one_apply_eq_self, hKcap]
    abel
  have hK1 : ‖(1 - P₁) (YK t₁ - K₁)‖ ≤ ηK := by
    calc _ ≤ ‖YK t₁ - K₁‖ := hP₁.compl.norm_le _
      _ ≤ ηK := by rw [norm_sub_rev]; exact hKerr
  rw [hdec]
  calc _ ≤ ‖g t₁‖ + ‖(1 - P₁) (YK t₁ - K₁)‖ := norm_add_le _ _
    _ ≤ (4 * L * B * h + L * ηK + ε) * h + ηK := add_le_add hmvt hK1
    _ = _ := by ring

/-- **Error of the KSL step in the range of `P₁`, inexact substeps.**  Let the K-step `YK`
(from `Y₀ = A t₀`), the backward S-step `YS` (from the computed K-step value `K₁`,
`P₁ K₁ = K₁`) and the L-step `YL` (from the computed S-step value `S₁`) be exact solutions of the
substep equations, and let the computed values satisfy `‖K₁ - YK t₁‖ ≤ ηK`,
`‖S₁ - YS t₁‖ ≤ ηS` and `‖Y₁ - YL t₁‖ ≤ ηL`.  Then
`‖Y₁ - P₁ A(t₁)‖ ≤ h (6 L B h + L (2 ηK + ηS)) + ηK + ηS + ηL`. -/
theorem ksl_proj_error_inexact (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    {K₁ S₁ Y₁ : E} {ηK ηS ηL : ℝ} (hKerr : ‖K₁ - YK t₁‖ ≤ ηK) (hKcap : P₁ K₁ = K₁)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = K₁)
    (hSerr : ‖S₁ - YS t₁‖ ≤ ηS)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = S₁)
    (hLerr : ‖Y₁ - YL t₁‖ ≤ ηL) :
    ‖Y₁ - P₁ (A t₁)‖ ≤ h * (6 * L * B * h + L * (2 * ηK + ηS)) + ηK + ηS + ηL := by
  have hle : t₀ ≤ t₁ := by linarith
  have hBK : IsBoundedField (fun t x => Q₀ (F t x)) B := hB.comp_contraction Q₀ hQ₀.norm_le
  have hBS : IsBoundedField (fun t x => -P₁ (Q₀ (F t x))) B := isBoundedField_kslS hB hP₁ hQ₀
  have hBL : IsBoundedField (fun t x => P₁ (F t x)) B := hB.comp_contraction P₁ hP₁.norm_le
  set g : ℝ → E := fun t => P₁ (YK t) + (YS t - YS t₀) + (YL t - YL t₀) - P₁ (A t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (((P₁.continuous.comp_continuousOn hK.cont).add (hS.cont.sub continuousOn_const)).add
      (hLs.cont.sub continuousOn_const)).sub (P₁.continuous.comp_continuousOn hA.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g
      (P₁ (Q₀ (F t (YK t))) + -P₁ (Q₀ (F t (YS t))) + P₁ (F t (YL t)) - P₁ (F t (A t)))
      (Ici t) t := fun t ht =>
    (((P₁.hasFDerivAt.comp_hasDerivWithinAt t (hK.deriv t ht)).add
      ((hS.deriv t ht).sub_const (YS t₀))).add ((hLs.deriv t ht).sub_const (YL t₀))).sub
      (P₁.hasFDerivAt.comp_hasDerivWithinAt t (hA.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁,
      ‖P₁ (Q₀ (F t (YK t))) + -P₁ (Q₀ (F t (YS t))) + P₁ (F t (YL t)) - P₁ (F t (A t))‖
        ≤ 6 * L * B * h + L * (2 * ηK + ηS) := by
    intro t ht
    have htI := Ico_subset_Icc_self ht
    have ht₁I : t₁ ∈ Icc t₀ t₁ := ⟨hle, le_rfl⟩
    have hK1 := hK.norm_end_sub_le hBK ht₁ t htI
    have hK2 := hK.norm_sub_start_le hBK ht₁ t₁ ht₁I
    have hS1 := hS.norm_sub_start_le hBS ht₁ t htI
    have hS2 := hS.norm_sub_start_le hBS ht₁ t₁ ht₁I
    have hL1 := hLs.norm_sub_start_le hBL ht₁ t htI
    have hA1 := hA.norm_sub_start_le hB ht₁ t htI
    have hdKS : ‖YK t - YS t‖ ≤ 2 * B * h + ηK := by
      have hdec : YK t - YS t = -(YK t₁ - YK t) - (K₁ - YK t₁) - (YS t - YS t₀) := by
        rw [hS₀]; abel
      rw [hdec]
      have e1 := norm_sub_le (-(YK t₁ - YK t) - (K₁ - YK t₁)) (YS t - YS t₀)
      have e2 := norm_sub_le (-(YK t₁ - YK t)) (K₁ - YK t₁)
      rw [norm_neg] at e2
      linarith
    have hdLA : ‖YL t - A t‖ ≤ 4 * B * h + ηK + ηS := by
      have hdec : YL t - A t = (YL t - YL t₀) + (S₁ - YS t₁) + (YS t₁ - YS t₀) + (K₁ - YK t₁)
          + (YK t₁ - YK t₀) - (A t - A t₀) := by
        rw [hL₀, hS₀, hK₀, hA₀]; abel
      rw [hdec]
      have e1 := norm_sub_le ((YL t - YL t₀) + (S₁ - YS t₁) + (YS t₁ - YS t₀) + (K₁ - YK t₁)
        + (YK t₁ - YK t₀)) (A t - A t₀)
      have e2 := norm_add_le ((YL t - YL t₀) + (S₁ - YS t₁) + (YS t₁ - YS t₀) + (K₁ - YK t₁))
        (YK t₁ - YK t₀)
      have e3 := norm_add_le ((YL t - YL t₀) + (S₁ - YS t₁) + (YS t₁ - YS t₀)) (K₁ - YK t₁)
      have e4 := norm_add₃_le (a := YL t - YL t₀) (b := S₁ - YS t₁) (c := YS t₁ - YS t₀)
      linarith
    have hsplit : P₁ (Q₀ (F t (YK t))) + -P₁ (Q₀ (F t (YS t))) + P₁ (F t (YL t))
        - P₁ (F t (A t)) = P₁ (Q₀ (F t (YK t) - F t (YS t))) + P₁ (F t (YL t) - F t (A t)) := by
      simp only [map_sub]; abel
    rw [hsplit]
    have hc1 : ‖P₁ (Q₀ (F t (YK t) - F t (YS t)))‖ ≤ L * (2 * B * h + ηK) :=
      calc _ ≤ ‖Q₀ (F t (YK t) - F t (YS t))‖ := hP₁.norm_le _
        _ ≤ ‖F t (YK t) - F t (YS t)‖ := hQ₀.norm_le _
        _ ≤ L * ‖YK t - YS t‖ := hF t _ _
        _ ≤ L * (2 * B * h + ηK) := mul_le_mul_of_nonneg_left hdKS hL
    have hc2 : ‖P₁ (F t (YL t) - F t (A t))‖ ≤ L * (4 * B * h + ηK + ηS) :=
      calc _ ≤ ‖F t (YL t) - F t (A t)‖ := hP₁.norm_le _
        _ ≤ L * ‖YL t - A t‖ := hF t _ _
        _ ≤ L * (4 * B * h + ηK + ηS) := mul_le_mul_of_nonneg_left hdLA hL
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ L * (2 * B * h + ηK) + L * (4 * B * h + ηK + ηS) := add_le_add hc1 hc2
      _ = 6 * L * B * h + L * (2 * ηK + ηS) := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀, hA₀]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, sub_zero, hlen] at hmvt
  have hdec : Y₁ - P₁ (A t₁) = g t₁ + P₁ (K₁ - YK t₁) + (S₁ - YS t₁) + (Y₁ - YL t₁) := by
    simp only [hg, map_sub, hKcap, hS₀, hL₀]
    abel
  rw [hdec]
  have e1 := norm_add_le (g t₁ + P₁ (K₁ - YK t₁) + (S₁ - YS t₁)) (Y₁ - YL t₁)
  have e2 := norm_add₃_le (a := g t₁) (b := P₁ (K₁ - YK t₁)) (c := S₁ - YS t₁)
  have e3 : ‖P₁ (K₁ - YK t₁)‖ ≤ ηK := (hP₁.norm_le _).trans hKerr
  have e4 : (6 * L * B * h + L * (2 * ηK + ηS)) * h
      = h * (6 * L * B * h + L * (2 * ηK + ηS)) := by ring
  linarith

/-- **Robust local error of the KSL integrator with inexact substeps, sharp form**
(cf. Kieri–Lubich–Walach 2016, §2.6.3; explicit constants ours).  Under the hypotheses of
`ksl_proj_error_inexact` and the normal-component bound `‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε`
at the computed K-step value,

    ‖Y₁ - A(t₁)‖ ≤ h (10 L B h + ε) + (2 + 3 L h) ηK + (1 + L h) ηS + ηL. -/
theorem ksl_local_error_inexact_sharp (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    {K₁ S₁ Y₁ : E} {ηK ηS ηL : ℝ} (hKerr : ‖K₁ - YK t₁‖ ≤ ηK) (hKcap : P₁ K₁ = K₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = K₁)
    (hSerr : ‖S₁ - YS t₁‖ ≤ ηS)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = S₁)
    (hLerr : ‖Y₁ - YL t₁‖ ≤ ηL) :
    ‖Y₁ - A t₁‖ ≤ h * (10 * L * B * h + ε) + (2 + 3 * L * h) * ηK + (1 + L * h) * ηS + ηL := by
  have h1 := ksl_proj_error_inexact hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hK hK₀ hKerr hKcap hS hS₀
    hSerr hLs hL₀ hLerr
  have h2 := kstep_capture_inexact hF hL hB hP₁ hQ₀ ht₁ hh hA hK (hK₀.trans hA₀.symm) hKerr
    hKcap hε
  have hdec : Y₁ - A t₁ = (Y₁ - P₁ (A t₁)) - (1 - P₁) (A t₁) := by
    simp only [sub_apply, one_apply_eq_self]; abel
  rw [hdec]
  calc _ ≤ ‖Y₁ - P₁ (A t₁)‖ + ‖(1 - P₁) (A t₁)‖ := norm_sub_le _ _
    _ ≤ (h * (6 * L * B * h + L * (2 * ηK + ηS)) + ηK + ηS + ηL)
        + (h * (4 * L * B * h + L * ηK + ε) + ηK) := add_le_add h1 h2
    _ = _ := by ring

/-- **Robust local error of the KSL integrator with inexact substeps** (cf. Kieri–Lubich–Walach
2016, §2.6.3, summarized in [CerutiLubich2022] after Theorem 2; explicit constants ours).  If the
K-, S- and L-substeps are solved with local errors `ηK`, `ηS`, `ηL` (see
`ksl_local_error_inexact_sharp` for the precise hypotheses), then

    ‖Y₁ - A(t₁)‖ ≤ h (11 L B h + ε) + (2 + 3 L h) (ηK + ηS + ηL),

i.e. the local error grows by a multiple of the substep errors, with constants independent of
singular values. -/
theorem ksl_local_error_inexact (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    {K₁ S₁ Y₁ : E} {ηK ηS ηL : ℝ} (hKerr : ‖K₁ - YK t₁‖ ≤ ηK) (hKcap : P₁ K₁ = K₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = K₁)
    (hSerr : ‖S₁ - YS t₁‖ ≤ ηS)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = S₁)
    (hLerr : ‖Y₁ - YL t₁‖ ≤ ηL) :
    ‖Y₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) + (2 + 3 * L * h) * (ηK + ηS + ηL) := by
  have h1 := ksl_local_error_inexact_sharp hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hK hK₀ hKerr hKcap hε
    hS hS₀ hSerr hLs hL₀ hLerr
  have hηS : 0 ≤ ηS := (norm_nonneg _).trans hSerr
  have hηL : 0 ≤ ηL := (norm_nonneg _).trans hLerr
  have hLh : 0 ≤ L * h := mul_nonneg hL hh
  have h3 : 0 ≤ L * B * h * h := mul_nonneg (mul_nonneg (mul_nonneg hL hB.nonneg) hh) hh
  have h4 : 0 ≤ (1 + 2 * (L * h)) * ηS := mul_nonneg (by linarith) hηS
  have h5 : 0 ≤ (1 + 3 * (L * h)) * ηL := mul_nonneg (by linarith) hηL
  linarith

/-- **Error of the KSL step in the range of `P₁`.**  Under the hypotheses of the KSL step (see
`ksl_local_error`; the normal-component bound is not needed here),
`‖YL t₁ - P₁ A(t₁)‖ ≤ 6 L B h²`. -/
theorem ksl_proj_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = YS t₁) :
    ‖YL t₁ - P₁ (A t₁)‖ ≤ h * (6 * L * B * h) :=
  (ksl_proj_error_inexact hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hK hK₀ (ηK := 0) (by simp) hKcap hS
    hS₀ (ηS := 0) (by simp) hLs hL₀ (ηL := 0) (by simp)).trans (le_of_eq (by ring))

/-- **Robust local error of the KSL integrator, sharp form.**  Under the hypotheses of
`ksl_local_error`, `‖YL t₁ - A t₁‖ ≤ h (10 L B h + ε)`.  This improves the explicit local bound
`(4 e^{L h} + 9) L B h² + (3 e^{L h} + 4) ε h` of Kieri–Lubich–Walach 2016 (proof of
Theorem 2.1, quoted in [CerutiLubich2022, eq. (5)], with `δ = 0`); the coefficient `1` of `ε h`
is attained for a constant field (`KSLExample`). -/
theorem ksl_local_error_sharp (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = YS t₁) :
    ‖YL t₁ - A t₁‖ ≤ h * (10 * L * B * h + ε) :=
  (ksl_local_error_inexact_sharp hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hK hK₀ (ηK := 0) (by simp)
    hKcap hε hS hS₀ (ηS := 0) (by simp) hLs hL₀ (ηL := 0) (by simp)).trans
    (le_of_eq (by ring))

/-- **Robust local error of the projector-splitting integrator** (cf. Kieri–Lubich–Walach 2016,
proof of Theorem 2.1, local bound quoted in [CerutiLubich2022, eq. (5)]; our constants are smaller,
see `ksl_local_error_sharp`).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and
bounded by `B`, `A` the exact solution on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, with `A t₀ = Y₀`,
and let `P₁`, `Q₀` be orthogonal projectors.  Assume

* K-step: `YK' = Q₀ F(t, YK)`, `YK t₀ = Y₀`, `P₁ (YK t₁) = YK t₁`, and
  `‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε` on `[t₀, t₁]`;
* backward S-step: `YS' = -P₁ Q₀ F(t, YS)`, `YS t₀ = YK t₁`;
* L-step: `YL' = P₁ F(t, YL)`, `YL t₀ = YS t₁`.

Then the new approximation `Y₁ = YL t₁` satisfies

    ‖Y₁ - A t₁‖ ≤ h (11 L B h + ε)  ( = O(h (h + ε)) ).

No rank or invertibility assumption is made, so the bound does not depend on singular values;
no commutation of `P₁` and `Q₀` is needed either.  For matrices, the normal-component hypothesis
follows from the factored assumption for any `Ŝ₁` (`ksl_kNormal_of_factored`). -/
theorem ksl_local_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀)
    (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = YS t₁) :
    ‖YL t₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) := by
  have h1 := ksl_local_error_sharp hF hL hB hP₁ hQ₀ ht₁ hh hA hA₀ hK hK₀ hKcap hε hS hS₀ hLs hL₀
  have h3 : 0 ≤ L * B * h * h := mul_nonneg (mul_nonneg (mul_nonneg hL hB.nonneg) hh) hh
  linarith

end Local

/-! ### Range invariance -/

section Range

variable {F : ℝ → E → E} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YS YL : ℝ → E}

/-- The backward S-step trajectory `YS = U₁ S V₀ᵀ` stays in the range of `P₁` (Galerkin-type
invariance: its velocity `-P₁ Q₀ F` lies in the range of `P₁`, and it starts at `YK t₁`, which is
captured by `P₁`). -/
theorem ksl_S_mem_range (hP₁ : IsOrthProj P₁)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hKcap : P₁ (YK t₁) = YK t₁) : ∀ t ∈ Icc t₀ t₁, P₁ (YS t) = YS t :=
  hS.fixed_of_fixed_field (fun t x => by simp only [map_neg, hP₁.idem]) (by rw [hS₀, hKcap])

/-- The L-step trajectory `YL = U₁ Lᵀ` stays in the range of `P₁`; in particular the new
approximation `Y₁ = YL t₁` satisfies `P₁ Y₁ = Y₁`, i.e. `Y₁ = U₁ S₁ V₁ᵀ` has its column space in
the range of the new basis `U₁`. -/
theorem ksl_mem_range (hP₁ : IsOrthProj P₁) (hKcap : P₁ (YK t₁) = YK t₁)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hLs : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁) (hL₀ : YL t₀ = YS t₁)
    (hle : t₀ ≤ t₁) : ∀ t ∈ Icc t₀ t₁, P₁ (YL t) = YL t :=
  hLs.fixed_of_fixed_field (fun t x => hP₁.idem _)
    (by rw [hL₀]; exact ksl_S_mem_range hP₁ hS hS₀ hKcap t₁ ⟨hle, le_rfl⟩)

/-- The K-step trajectory `YK = K V₀ᵀ` stays in the range of `Q₀` if `Y₀` does. -/
theorem ksl_K_mem_range_Q₀ (hQ₀ : IsOrthProj Q₀)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀) (hY₀ : Q₀ Y₀ = Y₀) :
    ∀ t ∈ Icc t₀ t₁, Q₀ (YK t) = YK t :=
  hK.fixed_of_fixed_field (fun t x => hQ₀.idem _) (by rw [hK₀, hY₀])

/-- If `P₁` and `Q₀` commute (left and right multiplication) and `Y₀` lies in the range of `Q₀`,
then the backward S-step trajectory `YS = U₁ S V₀ᵀ` stays in the range of `Q₀`; together with
`ksl_S_mem_range` it stays in the range of `P₁ Q₀`. -/
theorem ksl_S_mem_range_Q₀ (hQ₀ : IsOrthProj Q₀) (hc : ∀ x, P₁ (Q₀ x) = Q₀ (P₁ x))
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = Y₀) (hY₀ : Q₀ Y₀ = Y₀)
    (hS : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁) (hS₀ : YS t₀ = YK t₁)
    (hle : t₀ ≤ t₁) : ∀ t ∈ Icc t₀ t₁, Q₀ (YS t) = YS t :=
  hS.fixed_of_fixed_field (fun t x => by simp only [map_neg, ← hc, hQ₀.idem])
    (by rw [hS₀]; exact ksl_K_mem_range_Q₀ hQ₀ hK hK₀ hY₀ t₁ ⟨hle, le_rfl⟩)

end Range

/-! ### One step of the KSL integrator -/

/-- All hypotheses of one step of the projector-splitting (KSL) integrator from `(t₀, Y₀)` to
`t₁`, with right projector `Q₀` (basis `V₀`), new left projector `P₁` (basis `U₁`), K-, S- and
L-step trajectories `YK`, `YS`, `YL` (the new approximation is `YL t₁`), and normal-component
bound `ε` at the point `YK t₁`. -/
structure IsKSLStep (F : ℝ → E → E) (ε : ℝ) (P₁ Q₀ : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YK YS YL : ℝ → E) : Prop where
  projP₁ : IsOrthProj P₁
  projQ₀ : IsOrthProj Q₀
  /-- K-step: `YK' = Q₀ F(t, YK)` (the matrix K-step for `K = YK V₀`). -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  /-- The new left basis captures `K(t₁)`. -/
  kCap : P₁ (YK t₁) = YK t₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- Backward S-step: `YS' = -P₁ Q₀ F(t, YS)` (the matrix S-step for `S = U₁ᵀ YS V₀`). -/
  sSol : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁
  sStart : YS t₀ = YK t₁
  /-- L-step: `YL' = P₁ F(t, YL)` (the matrix L-step for `Lᵀ = U₁ᵀ YL`). -/
  lSol : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁
  lStart : YL t₀ = YS t₁

namespace IsKSLStep

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {Y₀ : E}
  {A YK YS YL : ℝ → E}

/-- The normal-component bound forces `ε ≥ 0` on a nonempty step. -/
lemma eps_nonneg (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (h01 : t₀ ≤ t₁) : 0 ≤ ε :=
  (norm_nonneg _).trans (hs.kNormal t₀ ⟨le_rfl, h01⟩)

/-- **Robust local error of the KSL integrator** (cf. Kieri–Lubich–Walach 2016, proof of
Theorem 2.1), bundled form of `ksl_local_error`: `‖YL t₁ - A t₁‖ ≤ h (11 L B h + ε)`. -/
theorem local_error (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YL t₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) :=
  ksl_local_error hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hA₀ hs.kSol hs.kStart hs.kCap
    hs.kNormal hs.sSol hs.sStart hs.lSol hs.lStart

/-- The new approximation of a KSL step lies in the range of the new left projector. -/
theorem mem_range (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) (hle : t₀ ≤ t₁) :
    P₁ (YL t₁) = YL t₁ :=
  ksl_mem_range hs.projP₁ hs.kCap hs.sSol hs.sStart hs.lSol hs.lStart hle t₁ ⟨hle, le_rfl⟩

end IsKSLStep

/-! ### Global error -/

section Global

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Robust global error bound of the projector-splitting integrator** (Kieri–Lubich–Walach
2016, Theorem 2.1; Theorem 2 of [CerutiLubich2022], with explicit constants).  Let `F` be
`L`-Lipschitz (`L ≥ 0`) and bounded by `B`, let `tₙ = t₀ + n h` with `h ≥ 0`, and let `A` solve
`A' = F(t, A)` on `[t₀, t₀ + N h]`.  For `n < N` let step `n` of the KSL integrator go from
`(tₙ, Y n)` to `Y (n+1) = YL n tₙ₊₁` with right projector `Q n` and new left projector `P n`, as
described by `IsKSLStep`, and let `Φ n` be the exact flow on `[tₙ, tₙ₊₁]` started at `Y n`.
Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (11 L B h + ε)).

(Proof: local error `ksl_local_error` and Lady Windermere's fan `lady_windermere`.) -/
theorem ksl_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h))
    {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YS YL Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsKSLStep F ε (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n) (YL n))
    (hY : ∀ n < N, Y (n + 1) = YL n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤
      Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖ + n * h * (11 * L * B * h + ε)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * (11 * L * B * h + ε) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error hF hL hB (by ring) hh (hΦ n hn) (hΦ₀ n hn)
  intro n hn
  calc _ ≤ _ := lady_windermere hF hL hh hA hΦ hΦ₀ hloc n hn
    _ = _ := by ring

/-- **Robust global error bound of the projector-splitting integrator, final form**
(Kieri–Lubich–Walach 2016, Theorem 2.1; Theorem 2 of [CerutiLubich2022]): under the hypotheses of
`ksl_global_error`, with `ε ≥ 0`, an initial error `‖Y 0 - A t₀‖ ≤ δ` and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h,

with `c₀ = e^{L T}`, `c₁ = T e^{L T}`, `c₂ = 11 L B T e^{L T}`, which only depend on `L`, `B`, `T`
— in particular not on singular values.  The term `c₁ ε` is attained for a constant field
(`KSLExample`). -/
theorem ksl_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hε : 0 ≤ ε) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YS YL Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsKSLStep F ε (P n) (Q n) (t₀ + n * h) (t₀ + (n + 1) * h) (Y n)
      (YK n) (YS n) (YL n))
    (hY : ∀ n < N, Y (n + 1) = YL n (t₀ + (n + 1) * h))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ + T * Real.exp (L * T) * ε
        + 11 * L * B * T * Real.exp (L * T) * h := by
  intro n hn hT
  have hg : 0 ≤ 11 * L * B * h + ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB.nonneg) hh) hε
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤ h * (11 * L * B * h + ε) := by
    intro n hn
    rw [hY n hn]
    exact (hstep n hn).local_error hF hL hB (by ring) hh (hΦ n hn) (hΦ₀ n hn)
  have h1 := lady_windermere_of_le hF hL hh hA hΦ hΦ₀ hg hloc n hn hT
  have h2 : Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * (11 * L * B * h + ε))
      ≤ Real.exp (L * T) * (δ + T * (11 * L * B * h + ε)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc _ ≤ _ := h1.trans h2
    _ = _ := by ring

end Global

/-! ### Inexact substeps -/

/-- All hypotheses of one step of the projector-splitting integrator with **inexactly solved
substeps** (cf. Kieri–Lubich–Walach 2016, §2.6.3), from `(t₀, Y₀)` to `t₁`:

* the exact K-step solution `YK` from `Y₀` and the computed K-step value `K₁` (`= K̃(t₁) V₀ᵀ`)
  with local error `‖K₁ - YK t₁‖ ≤ ηK`; the new basis captures the computed value,
  `P₁ K₁ = K₁`, and the normal-component bound holds at `K₁`;
* the exact backward S-step solution `YS` from `K₁` and the computed value `S₁` (`= U₁ S̃₀ V₀ᵀ`)
  with `‖S₁ - YS t₁‖ ≤ ηS`;
* the exact L-step solution `YL` from `S₁` and the computed new approximation `Y₁`
  with `‖Y₁ - YL t₁‖ ≤ ηL`.

An exact KSL step (`IsKSLStep`) is the special case `ηK = ηS = ηL = 0`
(`IsKSLStep.isInexactKSLStep`). -/
structure IsInexactKSLStep (F : ℝ → E → E) (ε ηK ηS ηL : ℝ) (P₁ Q₀ : E →L[ℝ] E) (t₀ t₁ : ℝ)
    (Y₀ K₁ S₁ Y₁ : E) (YK YS YL : ℝ → E) : Prop where
  projP₁ : IsOrthProj P₁
  projQ₀ : IsOrthProj Q₀
  /-- Exact K-step from the current approximation. -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  /-- Local error of the computed K-step. -/
  kErr : ‖K₁ - YK t₁‖ ≤ ηK
  /-- The new left basis is computed from (and captures) the computed K-step value. -/
  kCap : P₁ K₁ = K₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t K₁))‖ ≤ ε
  /-- Exact backward S-step from the computed K-step value. -/
  sSol : ODESolution (fun t x => -P₁ (Q₀ (F t x))) YS t₀ t₁
  sStart : YS t₀ = K₁
  /-- Local error of the computed S-step. -/
  sErr : ‖S₁ - YS t₁‖ ≤ ηS
  /-- Exact L-step from the computed S-step value. -/
  lSol : ODESolution (fun t x => P₁ (F t x)) YL t₀ t₁
  lStart : YL t₀ = S₁
  /-- Local error of the computed L-step, i.e. of the new approximation. -/
  lErr : ‖Y₁ - YL t₁‖ ≤ ηL

/-- An exact KSL step is an inexact KSL step with zero substep errors. -/
lemma IsKSLStep.isInexactKSLStep {F : ℝ → E → E} {ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ : ℝ}
    {Y₀ : E} {YK YS YL : ℝ → E} (hs : IsKSLStep F ε P₁ Q₀ t₀ t₁ Y₀ YK YS YL) :
    IsInexactKSLStep F ε 0 0 0 P₁ Q₀ t₀ t₁ Y₀ (YK t₁) (YS t₁) (YL t₁) YK YS YL where
  projP₁ := hs.projP₁
  projQ₀ := hs.projQ₀
  kSol := hs.kSol
  kStart := hs.kStart
  kErr := by simp
  kCap := hs.kCap
  kNormal := hs.kNormal
  sSol := hs.sSol
  sStart := hs.sStart
  sErr := by simp
  lSol := hs.lSol
  lStart := hs.lStart
  lErr := by simp

namespace IsInexactKSLStep

variable {F : ℝ → E → E} {L B ε ηK ηS ηL : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ}
  {Y₀ K₁ S₁ Y₁ : E} {A YK YS YL : ℝ → E}

/-- The substep errors are nonnegative. -/
lemma eta_nonneg (hs : IsInexactKSLStep F ε ηK ηS ηL P₁ Q₀ t₀ t₁ Y₀ K₁ S₁ Y₁ YK YS YL) :
    0 ≤ ηK + ηS + ηL :=
  add_nonneg (add_nonneg ((norm_nonneg _).trans hs.kErr) ((norm_nonneg _).trans hs.sErr))
    ((norm_nonneg _).trans hs.lErr)

/-- **Local error of the KSL integrator with inexact substeps** (cf. Kieri–Lubich–Walach 2016,
§2.6.3), bundled form of `ksl_local_error_inexact`:
`‖Y₁ - A t₁‖ ≤ h (11 L B h + ε) + (2 + 3 L h) (ηK + ηS + ηL)`. -/
theorem local_error (hs : IsInexactKSLStep F ε ηK ηS ηL P₁ Q₀ t₀ t₁ Y₀ K₁ S₁ Y₁ YK YS YL)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) + (2 + 3 * L * h) * (ηK + ηS + ηL) :=
  ksl_local_error_inexact hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hA₀ hs.kSol hs.kStart hs.kErr
    hs.kCap hs.kNormal hs.sSol hs.sStart hs.sErr hs.lSol hs.lStart hs.lErr

/-- Local error of the KSL integrator with inexact substeps for step sizes `0 ≤ h ≤ H`:
`‖Y₁ - A t₁‖ ≤ h (11 L B h + ε) + (2 + 3 L H) (ηK + ηS + ηL)`. -/
theorem local_error_le (hs : IsInexactKSLStep F ε ηK ηS ηL P₁ Q₀ t₀ t₁ Y₀ K₁ S₁ Y₁ YK YS YL)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (11 * L * B * h + ε) + (2 + 3 * L * H) * (ηK + ηS + ηL) := by
  have h1 := hs.local_error hF hL hB ht₁ hh hA hA₀
  have h2 : (2 + 3 * L * h) * (ηK + ηS + ηL) ≤ (2 + 3 * L * H) * (ηK + ηS + ηL) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hs.eta_nonneg
  linarith

end IsInexactKSLStep

section GlobalInexact

variable {F : ℝ → E → E} {L B ε : ℝ}

/-- **Global error of the KSL integrator with inexact substeps** (cf. Kieri–Lubich–Walach 2016,
§2.6.3, summarized in [CerutiLubich2022] after Theorem 2; explicit constants ours).  Under the
hypotheses of `ksl_global_error`, but with step `n` an inexact KSL step (`IsInexactKSLStep`)
from `Y n` to `Y (n+1)` with substep errors `ηK n`, `ηS n`, `ηL n`, and `0 ≤ h ≤ H`: for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n h (11 L B h + ε)
                    + (2 + 3 L H) ∑_{k<n} (ηK k + ηS k + ηL k)).

The global error thus grows by the accumulated substep errors, with constants independent of
singular values (perturbed discrete Grönwall inequality, `lady_windermere_sum`). -/
theorem ksl_global_error_inexact (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E} {Y K₁ S₁ : ℕ → E}
    {YK YS YL Φ : ℕ → ℝ → E} {ηK ηS ηL : ℕ → ℝ}
    (hstep : ∀ n < N, IsInexactKSLStep F ε (ηK n) (ηS n) (ηL n) (P n) (Q n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (K₁ n) (S₁ n) (Y (n + 1)) (YK n) (YS n) (YL n))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * (‖Y 0 - A t₀‖
      + n * h * (11 * L * B * h + ε)
      + (2 + 3 * L * H) * ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (11 * L * B * h + ε) + (2 + 3 * L * H) * (ηK n + ηS n + ηL n) := fun n hn =>
    (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  intro n hn
  have h1 := lady_windermere_sum hF hL hh hA hΦ hΦ₀
    (ℓ := fun k => h * (11 * L * B * h + ε) + (2 + 3 * L * H) * (ηK k + ηS k + ηL k)) hloc n hn
  have hsum : ∑ k ∈ Finset.range n,
      (h * (11 * L * B * h + ε) + (2 + 3 * L * H) * (ηK k + ηS k + ηL k))
      = n * h * (11 * L * B * h + ε)
        + (2 + 3 * L * H) * ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.mul_sum]
    ring
  rw [hsum] at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- **Global error of the KSL integrator with inexact substeps, final form**: if in addition the
substep errors of every step are bounded by `η`, the initial error by `δ`, `ε ≥ 0` and
`n h ≤ T`, then

    ‖Y n - A tₙ‖ ≤ e^{L T} (δ + T (11 L B h + ε) + (2 + 3 L H) n η).

Since `n ≤ T / h`, the additional error is at most `e^{L T} (2 + 3 L H) T η / h`, so the substep
local errors `η` must be `o(h)` (cf. Kieri–Lubich–Walach 2016, §2.6.3). -/
theorem ksl_global_error_inexact_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q : ℕ → E →L[ℝ] E}
    {Y K₁ S₁ : ℕ → E} {YK YS YL Φ : ℕ → ℝ → E} {ηK ηS ηL : ℕ → ℝ}
    (hstep : ∀ n < N, IsInexactKSLStep F ε (ηK n) (ηS n) (ηL n) (P n) (Q n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (K₁ n) (S₁ n) (Y (n + 1)) (YK n) (YS n) (YL n))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {η δ T : ℝ}
    (hη : ∀ n < N, ηK n + ηS n + ηL n ≤ η) (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) *
        (δ + T * (11 * L * B * h + ε) + (2 + 3 * L * H) * (n * η)) := by
  intro n hn hT
  have h1 := ksl_global_error_inexact hF hL hB hh hhH hA hstep hΦ hΦ₀ n hn
  have hH : 0 ≤ 2 + 3 * L * H := by nlinarith
  have hg : 0 ≤ 11 * L * B * h + ε :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hB.nonneg) hh) hε
  have hsum : ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k) ≤ n * η := by
    have := Finset.sum_le_sum (s := Finset.range n) (g := fun _ => η)
      (fun k hk => hη k ((Finset.mem_range.1 hk).trans_le hn))
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k) :=
    Finset.sum_nonneg fun k hk => (hstep k ((Finset.mem_range.1 hk).trans_le hn)).eta_nonneg
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hin : ‖Y 0 - A t₀‖ + n * h * (11 * L * B * h + ε)
      + (2 + 3 * L * H) * ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k)
      ≤ δ + T * (11 * L * B * h + ε) + (2 + 3 * L * H) * (n * η) := by
    have e1 : n * h * (11 * L * B * h + ε) ≤ T * (11 * L * B * h + ε) :=
      mul_le_mul_of_nonneg_right hT hg
    have e2 := mul_le_mul_of_nonneg_left hsum hH
    linarith
  have hin0 : 0 ≤ ‖Y 0 - A t₀‖ + n * h * (11 * L * B * h + ε)
      + (2 + 3 * L * H) * ∑ k ∈ Finset.range n, (ηK k + ηS k + ηL k) :=
    add_nonneg (add_nonneg (norm_nonneg _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hh) hg)) (mul_nonneg hH hsum0)
  exact h1.trans (mul_le_mul hexp hin hin0 (Real.exp_pos _).le)

end GlobalInexact

/-! ### Matrix layer: the normal-component assumption

For `E = ℝ^{m × n}` with the Frobenius inner product, `P₁ = leftProj U₁` (`X ↦ U₁ U₁ᵀ X`) and
`Q₀ = rightProj V₀` (`X ↦ X V₀ V₀ᵀ`), the point hypothesis `kNormal` of `IsKSLStep` is
`‖(I - U₁ U₁ᵀ) F(t, U₁ Ŝ₁ V₀ᵀ) (I - V₀ V₀ᵀ)‖ ≤ ε` with `Ŝ₁ = U₁ᵀ (YK t₁) V₀`, possibly singular.
We derive it from the factored assumption, and the factored assumption
from the paper's assumption on the rank-`r` manifold by a density argument. -/

section MatrixLayer

open scoped Matrix LeanDLRA.Frobenius

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]
  [DecidableEq r]

omit [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- A matrix fixed by `leftProj U` and `rightProj V` factors as `Y = U (Uᵀ Y V) Vᵀ`. -/
lemma mul_mul_transpose_eq_of_fixed {U : Matrix m r ℝ} {V : Matrix n r ℝ} {Y : Matrix m n ℝ}
    (hP : leftProj U Y = Y) (hQ : rightProj V Y = Y) : U * (Uᵀ * Y * V) * Vᵀ = Y := by
  rw [leftProj_apply] at hP
  rw [rightProj_apply] at hQ
  calc U * (Uᵀ * Y * V) * Vᵀ = U * Uᵀ * Y * V * Vᵀ := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [hP, hQ]

/-- **Normal-component bound from the factored assumption.**  If
`‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for all `t`, all `U`, `V` with orthonormal columns
and **all** `S` (singular or not), then the normal-component bound
`‖(1 - P₁) ((1 - Q₀) (F t Y))‖ ≤ ε` of the abstract theory holds, with `P₁ = leftProj U₁` and
`Q₀ = rightProj V₀`, at every matrix `Y` fixed by `P₁` and `Q₀`: such a `Y` is
`U₁ Ŝ₁ V₀ᵀ` with `Ŝ₁ = U₁ᵀ Y V₀`.  No invertibility of `Ŝ₁` is needed.  This applies to
`Y = YK t₁ = U₁ Ŝ₁ V₀ᵀ` (`ksl_kNormal_of_factored`) and to the computed K-step value `K₁` of
an inexact step (`IsInexactKSLStep.kNormal`). -/
theorem ksl_normal_le_of_factored {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    {U₁ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {Y : Matrix m n ℝ} (hP : leftProj U₁ Y = Y) (hQ : rightProj V₀ Y = Y) (t : ℝ) :
    ‖(1 - leftProj U₁) ((1 - rightProj V₀) (F t Y))‖ ≤ ε := by
  rw [one_sub_leftProj_one_sub_rightProj_apply, ← mul_mul_transpose_eq_of_fixed hP hQ]
  exact hε t U₁ _ V₀ hU₁ hV₀

/-- **The hypothesis `kNormal` of the matrix KSL step from the factored assumption.**  Let
`V₀`, `U₁` have orthonormal columns, `Y₀ = Y₀ V₀ V₀ᵀ` (e.g. `Y₀ = U₀ S₀ V₀ᵀ`), let `YK = K V₀ᵀ`
solve the K-step `YK' = F(t, YK) V₀ V₀ᵀ`, `YK t₀ = Y₀`, and let the new basis capture it,
`U₁ U₁ᵀ YK(t₁) = YK(t₁)` (`K(t₁) = U₁ Ŝ₁`).  Under the factored normal-component assumption,
`kNormal` holds for `P₁ = leftProj U₁`, `Q₀ = rightProj V₀`, whatever the singular values of
`Ŝ₁`. -/
theorem ksl_kNormal_of_factored {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    {U₁ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) {Y₀ : Matrix m n ℝ} (hY₀ : rightProj V₀ Y₀ = Y₀)
    {YK : ℝ → Matrix m n ℝ} (hK : ODESolution (fun t x => rightProj V₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = Y₀) (hKcap : leftProj U₁ (YK t₁) = YK t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj U₁) ((1 - rightProj V₀) (F t (YK t₁)))‖ ≤ ε :=
  fun t _ => ksl_normal_le_of_factored hε hU₁ hV₀ hKcap
    (ksl_K_mem_range_Q₀ (isOrthProj_rightProj hV₀) hK hK₀ hY₀ t₁ ⟨hle, le_rfl⟩) t

/-- **From invertible cores to all cores (density).**  Let `G` be continuous (e.g. `G = F t`
for a Lipschitz field, `IsLipschitzField.lipschitzWith`).  If the normal component of `G` is
`ε`-small at all matrices `U S Vᵀ` with **invertible** `S`,
`‖(1 - tangentProj U V) (G (U S Vᵀ))‖ ≤ ε`, then it is `ε`-small at `U S Vᵀ` for **every** `S`:
`‖(I - U Uᵀ) G(U S Vᵀ) (I - V Vᵀ)‖ ≤ ε`.  (`S + η I` is invertible for all `η ≠ 0` close to
`0`, since the characteristic polynomial of `-S` has finitely many roots; let `η → 0`.)  No
orthonormality is needed for this step. -/
theorem normal_le_of_invertible_core {G : Matrix m n ℝ → Matrix m n ℝ} (hG : Continuous G)
    {ε : ℝ} (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (hε : ∀ S : Matrix r r ℝ, IsUnit S.det → ‖(1 - tangentProj U V) (G (U * S * Vᵀ))‖ ≤ ε)
    (S : Matrix r r ℝ) : ‖(1 - U * Uᵀ) * G (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
  set g : ℝ → ℝ := fun η =>
    ‖(1 - leftProj U) ((1 - rightProj V) (G (U * S * Vᵀ + η • (U * Vᵀ))))‖ with hg
  have hgc : Continuous g :=
    (((1 - leftProj U).comp (1 - rightProj V)).continuous.comp
      (hG.comp (continuous_const.add (continuous_id.smul continuous_const)))).norm
  have hmat : ∀ η : ℝ, U * (S + η • 1) * Vᵀ = U * S * Vᵀ + η • (U * Vᵀ) := fun η => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hN : ∀ Z, (1 - tangentProj U V) Z = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := fun Z =>
    sub_eq_of_eq_add' (tangentProj_add_normal U V Z).symm
  -- `det (S + η I)` is the characteristic polynomial of `-S` at `η`: finitely many zeros
  set p := (-S).charpoly with hp
  have hfin : {x | p.IsRoot x}.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-S)).ne_zero
  have hdet : ∀ η, ¬ p.IsRoot η → IsUnit (S + η • (1 : Matrix r r ℝ)).det := fun η hη => by
    have h1 : p.eval η = (S + η • (1 : Matrix r r ℝ)).det := by
      rw [hp, Matrix.eval_charpoly, sub_neg_eq_add, add_comm, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
    exact Ne.isUnit (h1 ▸ hη)
  have hev : ∀ᶠ η in 𝓝[≠] (0 : ℝ), g η ≤ ε := by
    have hmem : ({x | p.IsRoot x} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
      hfin.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with η h1 h2
    have := hε (S + η • 1) (hdet η fun h => h1 ⟨h, h2⟩)
    rw [hmat, hN] at this
    simpa only [hg, one_sub_leftProj_one_sub_rightProj_apply] using this
  have h0 := le_of_tendsto (hgc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
  simpa only [hg, zero_smul, add_zero, one_sub_leftProj_one_sub_rightProj_apply] using h0

/-- **The factored assumption from the assumption on the manifold.**  For `U`, `V` with
orthonormal columns and invertible `S`, `Y = U S Vᵀ` lies on the manifold `M` of rank-`r`
matrices and `tangentProj U V` is its tangent-space projector `P(Y)` (independent of the
factorization, `tangentProj_eq_of_factorization`); every `Y ∈ M` has such a factorization.
So the hypothesis below is assumption 2 of Theorem 2 of [CerutiLubich2022],
`‖(I - P(Y)) F(t, Y)‖ ≤ ε` for `Y ∈ M` (globally, for all `t` and all `Y ∈ M`).  If `F t` is
continuous for every `t`, it implies the factored assumption for **all** cores `S`, including
singular ones (`normal_le_of_invertible_core`). -/
theorem factored_normal_of_manifold {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    (hc : ∀ t, Continuous (F t))
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → IsUnit S.det → ‖(1 - tangentProj U V) (F t (U * S * Vᵀ))‖ ≤ ε)
    (t : ℝ) (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) : ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε :=
  normal_le_of_invertible_core (hc t) U V (fun S' hS' => hε t U S' V hU hV hS') S

omit [DecidableEq m] [DecidableEq n] in
/-- **The hypothesis `kNormal` of the matrix KSL step from the paper's assumption on the
manifold** (assumption 2 of Theorem 2 of [CerutiLubich2022], in global form, see
`factored_normal_of_manifold`), for `F t` continuous: under the hypotheses of
`ksl_kNormal_of_factored`, `kNormal` holds at `YK t₁ = U₁ Ŝ₁ V₀ᵀ` even if `Ŝ₁` is singular, i.e.
even if `YK t₁` is not on the manifold. -/
theorem ksl_kNormal_of_manifold {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε : ℝ}
    (hc : ∀ t, Continuous (F t))
    (hε : ∀ t (U : Matrix m r ℝ) (S : Matrix r r ℝ) (V : Matrix n r ℝ), Uᵀ * U = 1 →
      Vᵀ * V = 1 → IsUnit S.det → ‖(1 - tangentProj U V) (F t (U * S * Vᵀ))‖ ≤ ε)
    {U₁ : Matrix m r ℝ} {V₀ : Matrix n r ℝ} (hU₁ : U₁ᵀ * U₁ = 1) (hV₀ : V₀ᵀ * V₀ = 1)
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) {Y₀ : Matrix m n ℝ} (hY₀ : rightProj V₀ Y₀ = Y₀)
    {YK : ℝ → Matrix m n ℝ} (hK : ODESolution (fun t x => rightProj V₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = Y₀) (hKcap : leftProj U₁ (YK t₁) = YK t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖(1 - leftProj U₁) ((1 - rightProj V₀) (F t (YK t₁)))‖ ≤ ε := by
  classical
  exact ksl_kNormal_of_factored (factored_normal_of_manifold hc hε) hU₁ hV₀ hle hY₀ hK hK₀ hKcap

/-- The hypotheses of `ksl_kNormal_of_manifold` on the field are satisfiable with `ε = 0` by a
field that is not tangent everywhere: for `F(t, Y) = Y` the normal component vanishes on the
manifold (`P(Y) Y = Y`), while `(I - U Uᵀ) Z (I - V Vᵀ) ≠ 0` for general `Z`. -/
example : ∀ t (U : Matrix (Fin 2) (Fin 1) ℝ) (S : Matrix (Fin 1) (Fin 1) ℝ)
    (V : Matrix (Fin 2) (Fin 1) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
    ‖(1 - tangentProj U V) ((fun (_ : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) => Y) t
      (U * S * Vᵀ))‖ ≤ 0 := fun _ U S V hU _ _ => by
  simp [tangentProj_mul_mul_transpose hU]

end MatrixLayer

/-! ### Satisfiability of the hypotheses -/

section Examples

/-- Auxiliary for the examples: an affine function `t ↦ d + c t` solves `y' = F(t, y)` whenever
`F ≡ c`. -/
lemma odeSolution_of_affine {F : ℝ → ℝ → ℝ} {c d : ℝ} (hF : ∀ t x, F t x = c) {y : ℝ → ℝ}
    (hy : ∀ t, y t = d + c * t) (a b : ℝ) : ODESolution F y a b := by
  obtain rfl : y = fun t => d + c * t := funext hy
  exact ⟨by fun_prop, fun t _ => by
    rw [hF]; simpa using ((hasDerivWithinAt_id t (Ici t)).const_mul c).const_add d⟩

/-- The hypotheses of one KSL step are jointly satisfiable with a nonzero vector field: on `ℝ`,
`F(t, y) = 1`, `P₁ = Q₀ = 1`, step `[0, 1]` from `Y₀ = 0`, K-step `t ↦ t`, backward S-step
`t ↦ 1 - t` (which undoes the K-step), L-step `t ↦ t`, `ε = 0`; the new approximation is
`YL 1 = 1 = A 1`. -/
example : IsKSLStep (E := ℝ) (fun _ _ => 1) 0 1 1 0 1 0 (fun t => t) (fun t => 1 - t)
    (fun t => t) where
  projP₁ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  kSol := odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring) _ _
  kStart := rfl
  kCap := by simp
  kNormal _ _ := by simp
  sSol := odeSolution_of_affine (c := -1) (d := 1) (fun _ _ => by simp) (fun _ => by ring) _ _
  sStart := by norm_num
  lSol := odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring) _ _
  lStart := by norm_num

/-- The hypotheses of an inexact KSL step are jointly satisfiable with a nonzero substep error:
as in the previous example, but the K-step is computed with local error `ηK = 1`
(`K₁ = 2` instead of `YK 1 = 1`), so the S-step runs from `2` to `S₁ = YS 1 = 1` and the
L-step from `1` to `Y₁ = YL 1 = 2`. -/
example : IsInexactKSLStep (E := ℝ) (fun _ _ => 1) 0 1 0 0 1 1 0 1 0 2 1 2 (fun t => t)
    (fun t => 2 - t) (fun t => 1 + t) where
  projP₁ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  kSol := odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring) _ _
  kStart := rfl
  kErr := by norm_num
  kCap := by simp
  kNormal _ _ := by simp
  sSol := odeSolution_of_affine (c := -1) (d := 2) (fun _ _ => by simp) (fun _ => by ring) _ _
  sStart := by norm_num
  sErr := by norm_num
  lSol := odeSolution_of_affine (c := 1) (d := 1) (fun _ _ => by simp) (fun _ => by ring) _ _
  lStart := by norm_num
  lErr := by norm_num

/-- The hypotheses of `ksl_global_error` are jointly satisfiable: on `ℝ` with `F(t, y) = 1`
(`L = 0`, `B = 1`), step size `h = 1`, five steps, exact solution `A t = t`, numerical values
`Y n = n`, all projectors the identity, K- and L-step trajectories and exact flows `t ↦ t`, and
backward S-step trajectories `t ↦ 2 n + 1 - t` on `[n, n + 1]`. -/
example : ∀ n ≤ 5, ‖((n : ℕ) : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * (n * 1)) *
    (‖((0 : ℕ) : ℝ) - 0‖ + n * 1 * (11 * 0 * 1 * 1 + 0)) :=
  ksl_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (t₀ := 0) (h := 1) zero_le_one
    (N := 5) (A := fun t => t)
    (odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => rfl) (fun _ => by ring) _ _)
    (P := fun _ => 1) (Q := fun _ => 1) (Y := fun n => (n : ℝ))
    (YK := fun _ t => t) (YS := fun n t => 2 * n + 1 - t) (YL := fun _ t => t)
    (Φ := fun _ t => t)
    (fun n _ => {
      projP₁ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      kSol := odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring)
        _ _
      kStart := by simp
      kCap := by simp
      kNormal := fun _ _ => by simp
      sSol := odeSolution_of_affine (c := -1) (d := 2 * n + 1) (fun _ _ => by simp)
        (fun _ => by ring) _ _
      sStart := by ring
      lSol := odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring)
        _ _
      lStart := by ring })
    (fun n _ => by simp)
    (fun _ _ => odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => by simp) (fun _ => by ring)
      _ _)
    (fun n _ => by simp)

/-- The hypotheses of `ksl_global_error_inexact_le` are jointly satisfiable with a **nonzero**
substep error: on `ℝ` with `F(t, y) = 1` (`L = 0`, `B = 1`, `ε = 0`), `h = H = 1`, two steps,
`A t = t`, every K-step computed with local error `ηK = 1` (`K₁ = YK tₙ₊₁ + 1`) and exact S- and
L-steps; then `Y n = 2 n`, and the error `‖Y 2 - A 2‖ = 2` is within the bound
`e^{L T} (δ + T (11 L B h + ε) + (2 + 3 L H) n η) = 4` (`η = 1`, `δ = 0`, `T = 2`). -/
example : ‖((2 * 2 : ℕ) : ℝ) - (0 + (2 : ℕ) * 1)‖ ≤
    Real.exp (0 * 2) * (0 + 2 * (11 * 0 * 1 * 1 + 0) + (2 + 3 * 0 * 1) * ((2 : ℕ) * 1)) :=
  ksl_global_error_inexact_le (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) le_rfl (t₀ := 0) (h := 1) (H := 1)
    zero_le_one le_rfl (N := 2) (A := fun t => t)
    (odeSolution_of_affine (c := 1) (d := 0) (fun _ _ => rfl) (fun _ => by ring) _ _)
    (P := fun _ => 1) (Q := fun _ => 1) (Y := fun n => ((2 * n : ℕ) : ℝ))
    (K₁ := fun n => 2 * n + 2) (S₁ := fun n => 2 * n + 1)
    (YK := fun n t => n + 1 * t) (YS := fun n t => (3 * n + 2) + -1 * t)
    (YL := fun n t => (n + 1) + 1 * t) (Φ := fun n t => n + 1 * t)
    (ηK := fun _ => 1) (ηS := fun _ => 0) (ηL := fun _ => 0)
    (fun n _ => {
      projP₁ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      kSol := odeSolution_of_affine (c := 1) (d := n) (fun _ _ => by simp) (fun _ => rfl) _ _
      kStart := by push_cast; ring
      kErr := by norm_num; ring_nf; norm_num
      kCap := by simp
      kNormal := fun _ _ => by simp
      sSol := odeSolution_of_affine (c := -1) (d := 3 * n + 2) (fun _ _ => by simp)
        (fun _ => rfl) _ _
      sStart := by ring
      sErr := by norm_num; ring_nf
      lSol := odeSolution_of_affine (c := 1) (d := n + 1) (fun _ _ => by simp) (fun _ => rfl) _ _
      lStart := by ring
      lErr := by push_cast; ring_nf; norm_num })
    (fun _ _ => odeSolution_of_affine (c := 1) (d := _) (fun _ _ => rfl) (fun _ => rfl) _ _)
    (fun n _ => by push_cast; ring) (η := 1) (δ := 0) (T := 2) (fun _ _ => by norm_num)
    (by simp) 2 le_rfl (by norm_num)

namespace KSLExample

/-- The orthogonal projector of `ℂ` (a real inner product space) onto the real axis. -/
noncomputable def reProj : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

/-- `reProj z = Re z`. -/
lemma reProj_apply (z : ℂ) : reProj z = (z.re : ℂ) := rfl

/-- `reProj` is an orthogonal projector (of rank one) on `ℂ ≅ ℝ²`. -/
lemma isOrthProj_reProj : IsOrthProj reProj where
  idem x := by simp [reProj_apply]
  symm x y := by
    simp only [reProj_apply, Complex.inner, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring

/-- An affine function `t ↦ d + t c` solves `y' = c` in `ℂ`. -/
lemma odeSolution_affine {F : ℝ → ℂ → ℂ} {c : ℂ} (hF : ∀ t x, F t x = c) (d : ℂ) (a b : ℝ) :
    ODESolution F (fun t => d + (t : ℂ) * c) a b := by
  refine ⟨by fun_prop, fun t _ => ?_⟩
  rw [hF]
  have := ((Complex.ofRealCLM.hasDerivAt (x := t)).hasDerivWithinAt (s := Ici t)).mul_const c
  simpa using this.const_add d

/-- **A nondegenerate KSL step.**  On `E = ℂ ≅ ℝ²` (a real inner product space), with the
constant field `F ≡ 1 + i` (`L = 0`, `B = ‖1 + i‖`), the rank-one projectors
`P₁ = Q₀ = reProj` onto the real axis, step `[0, 1]` from `Y₀ = 0`: the K-step `t ↦ t` (the
real part of `F`), the backward S-step `t ↦ 1 - t` and the L-step `t ↦ t`.  The normal component
is `(1 - P₁) (1 - Q₀) (1 + i) = i`, so `ε = 1` is the smallest admissible value. -/
lemma isKSLStep : IsKSLStep (E := ℂ) (fun _ _ => 1 + Complex.I) 1 reProj reProj 0 1 0
    (fun t => 0 + (t : ℂ) * 1) (fun t => 1 + (t : ℂ) * (-1)) (fun t => 0 + (t : ℂ) * 1) where
  projP₁ := isOrthProj_reProj
  projQ₀ := isOrthProj_reProj
  kSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
  kStart := by simp
  kCap := by simp [reProj_apply]
  kNormal _ _ := by simp [reProj_apply]
  sSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
  sStart := by simp
  lSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
  lStart := by simp

end KSLExample

open KSLExample

/-- **The coefficient `1` of `ε h` in `ksl_local_error_sharp` is attained.**  For the step
`KSLExample.isKSLStep` with exact solution `A(t) = t (1 + i)`, the bound
`h (10 L B h + ε) = 1` (`L = 0`, `h = 1`, `ε = 1`) holds and is an equality:
`‖YL 1 - A 1‖ = ‖-i‖ = 1`.  So no bound `h (c L B h + c' ε)` with `c' < 1` is possible, and all
hypotheses of the local error theorems hold with proper (non-identity) projectors. -/
example : ‖(0 + ((1 : ℝ) : ℂ) * 1) - (0 + ((1 : ℝ) : ℂ) * (1 + Complex.I))‖ ≤
      1 * (10 * 0 * ‖1 + Complex.I‖ * 1 + 1) ∧
    ‖(0 + ((1 : ℝ) : ℂ) * 1) - (0 + ((1 : ℝ) : ℂ) * (1 + Complex.I))‖ =
      1 * (10 * 0 * ‖1 + Complex.I‖ * 1 + 1) :=
  ⟨ksl_local_error_sharp (E := ℂ) (F := fun _ _ => 1 + Complex.I) (L := 0)
    (B := ‖1 + Complex.I‖) (ε := 1) (P₁ := reProj) (Q₀ := reProj) (t₀ := 0) (t₁ := 1) (h := 1)
    (Y₀ := 0) (A := fun t => 0 + (t : ℂ) * (1 + Complex.I)) (YK := fun t => 0 + (t : ℂ) * 1)
    (YS := fun t => 1 + (t : ℂ) * (-1)) (YL := fun t => 0 + (t : ℂ) * 1)
    (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl) isOrthProj_reProj isOrthProj_reProj
    (by norm_num) zero_le_one (odeSolution_affine (fun _ _ => rfl) _ _ _) (by simp)
    isKSLStep.kSol isKSLStep.kStart isKSLStep.kCap isKSLStep.kNormal isKSLStep.sSol
    isKSLStep.sStart isKSLStep.lSol isKSLStep.lStart, by simp⟩

/-- **The term `c₁ ε = T e^{L T} ε` of `ksl_global_error_le` is attained.**  Five KSL steps of
size `h = 1` as in `KSLExample.isKSLStep` (on `[n, n + 1]`: K-step `t ↦ t`, backward S-step
`t ↦ 2 n + 1 - t`, L-step `t ↦ t`), from `Y 0 = 0`, for `A(t) = t (1 + i)`; then `Y n = n`, and
the exact flows from the numerical values are `Φ n t = t (1 + i) - n i`.  With `L = 0`, `δ = 0`,
`ε = 1` and `T = 5` the bound `c₀ δ + c₁ ε + c₂ h` equals `5`, and `‖Y 5 - A 5‖ = ‖-5 i‖ = 5`. -/
example : ‖((5 : ℕ) : ℂ) - (0 + ((0 + ((5 : ℕ) : ℝ) * 1 : ℝ) : ℂ) * (1 + Complex.I))‖ ≤
      Real.exp (0 * 5) * 0 + 5 * Real.exp (0 * 5) * 1
        + 11 * 0 * ‖1 + Complex.I‖ * 5 * Real.exp (0 * 5) * 1 ∧
    ‖((5 : ℕ) : ℂ) - (0 + ((0 + ((5 : ℕ) : ℝ) * 1 : ℝ) : ℂ) * (1 + Complex.I))‖ = 5 := by
  refine ⟨ksl_global_error_le (E := ℂ) (F := fun _ _ => 1 + Complex.I) (L := 0)
    (B := ‖1 + Complex.I‖) (ε := 1) (fun _ _ _ => by simp) le_rfl (fun _ _ => le_rfl)
    zero_le_one (t₀ := 0) (h := 1) zero_le_one (N := 5)
    (A := fun t => 0 + (t : ℂ) * (1 + Complex.I)) (odeSolution_affine (fun _ _ => rfl) _ _ _)
    (P := fun _ => reProj) (Q := fun _ => reProj) (Y := fun n => (n : ℂ))
    (YK := fun _ t => 0 + (t : ℂ) * 1) (YS := fun n t => (2 * n + 1 : ℂ) + (t : ℂ) * (-1))
    (YL := fun _ t => 0 + (t : ℂ) * 1)
    (Φ := fun n t => -(n : ℂ) * Complex.I + (t : ℂ) * (1 + Complex.I))
    (fun n _ => {
      projP₁ := isOrthProj_reProj
      projQ₀ := isOrthProj_reProj
      kSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
      kStart := by simp
      kCap := by simp [reProj_apply]
      kNormal := fun _ _ => by simp [reProj_apply]
      sSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
      sStart := by push_cast; ring
      lSol := odeSolution_affine (fun _ _ => by simp [reProj_apply]) _ _ _
      lStart := by push_cast; ring })
    (fun n _ => by push_cast; ring) (fun _ _ => odeSolution_affine (fun _ _ => rfl) _ _ _)
    (fun n _ => by push_cast; ring) (δ := 0) (T := 5) (by simp) 5 le_rfl (by norm_num), ?_⟩
  have : ((5 : ℕ) : ℂ) - (0 + ((0 + ((5 : ℕ) : ℝ) * 1 : ℝ) : ℂ) * (1 + Complex.I))
      = -(5 * Complex.I) := by push_cast; ring
  rw [this, norm_neg, norm_mul, Complex.norm_I]
  norm_num

end Examples

end LeanDLRA
