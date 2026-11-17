import LeanDLRA.Foundations.Gronwall

/-!
# The K-step capture lemma

The robust error analysis of the basis-update & Galerkin (BUG) integrator
(Ceruti–Lubich, *An unconventional robust integrator for dynamical low-rank approximation*,
[CerutiLubich2022], Lemmas 2–3) and of the projector-splitting integrator (Kieri–Lubich–Walach 2016,
Theorem 2.1, quoted as Theorem 2 in [CerutiLubich2022]) rests on one estimate: the new basis
computed by the K-step *captures* the exact solution at the end of the step up to `O(h (h + ε))`,
with a constant that does not depend on singular values.

We formalise this abstractly.  `E` is a real inner product space (matrices with the Frobenius
inner product, Tucker tensors, ...), `F : ℝ → E → E` is an `L`-Lipschitz vector field bounded by
`B`, and `A` solves the full problem `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`.  The matrix K-step
`K' = F(t, K V₀ᵀ) V₀` is written as the full-space trajectory `YK = K V₀ᵀ`, which solves
`YK' = Q₀ F(t, YK)` with the orthogonal projector `Q₀ X = X V₀ V₀ᵀ`, and `YK t₀ = Y₀ = A t₀`.
The new basis `U₁` spans the range of `K(t₁)`; with `P₁ X = U₁ U₁ᵀ X` this reads
`P₁ (YK t₁) = YK t₁`.  The normal-component assumption (assumption 2 of Theorem 2 of
[CerutiLubich2022], at the point `YK t₁ = U₁ (U₁ᵀ K(t₁)) V₀ᵀ` of the manifold) is used only in the
form `‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε`.

## Main results

* Speed lemmas (`ODESolution.norm_sub_start_le`, `ODESolution.norm_end_sub_le`,
  `ODESolution.norm_sub_start_le_of_proj`, `norm_sub_le_two_mul_of_start`): all substep
  trajectories whose velocity is bounded by `B` stay within `B h` of their initial value (and of
  their final value), so two trajectories with the same starting value stay `2 B h`-close.
* `kstep_capture` (**K-step capture lemma**): `‖(1 - P₁) (A t₁)‖ ≤ h (4 L B h + ε)`.

## Proof of the capture lemma

Put `g = (1 - P₁) (A - YK)`.  Then `g t₀ = 0` and `g t₁ = (1 - P₁) (A t₁)` because `P₁` fixes
`YK t₁`.  Its derivative splits as

`g' = (1-P₁) Q₀ (F(t,A) - F(t,YK)) + (1-P₁)(1-Q₀) (F(t,A) - F(t,YK t₁)) + (1-P₁)(1-Q₀) F(t,YK t₁)`,

and since all trajectories move at most `B h`, `‖A t - YK t‖ ≤ 2 B h` and
`‖A t - YK t₁‖ ≤ 2 B h`, hence `‖g'‖ ≤ 4 L B h + ε`.  The mean value inequality concludes.  Only
the facts that `P₁` and `Q₀` are orthogonal projectors (hence `1 - P₁`, `Q₀`, `1 - Q₀` are
contractions) are used; no commutation is needed.
-/

open Set

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Speed lemmas -/

section Speed

omit [InnerProductSpace ℝ E] in
/-- A bound of a vector field is nonnegative. -/
lemma IsBoundedField.nonneg {f : ℝ → E → E} {B : ℝ} (hf : IsBoundedField f B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf 0 0)

/-- **Speed lemma.**  A trajectory of a vector field bounded by `B` stays within `B h` of its
initial value on a step `[t₀, t₁]`, `t₁ = t₀ + h`. -/
lemma ODESolution.norm_sub_start_le {f : ℝ → E → E} {B : ℝ} (hf : IsBoundedField f B)
    {y : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hy : ODESolution f y t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖y t - y t₀‖ ≤ B * h := by
  intro t ht
  refine (hy.norm_sub_le_of_bounded hf t ht).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hf.nonneg

/-- **Speed lemma** (distance to the final value).  A trajectory of a vector field bounded by `B`
stays within `B h` of its final value on a step `[t₀, t₁]`, `t₁ = t₀ + h`. -/
lemma ODESolution.norm_end_sub_le {f : ℝ → E → E} {B : ℝ} (hf : IsBoundedField f B)
    {y : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h) (hy : ODESolution f y t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖y t₁ - y t‖ ≤ B * h := by
  intro t ht
  have hy' : ODESolution f y t t₁ := hy.mono ht.1 le_rfl
  refine (hy'.norm_sub_le_of_bounded hf t₁ ⟨ht.2, le_rfl⟩).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [ht.1]) hf.nonneg

/-- **Speed lemma for projected substeps.**  A trajectory of `y' = P F(t, y)` with an orthogonal
projector `P` and `‖F‖ ≤ B` stays within `B h` of its initial value. -/
lemma ODESolution.norm_sub_start_le_of_proj {F : ℝ → E → E} {B : ℝ} (hF : IsBoundedField F B)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h)
    (hy : ODESolution (fun t x => P (F t x)) y t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖y t - y t₀‖ ≤ B * h :=
  hy.norm_sub_start_le (hF.comp_contraction P hP.norm_le) ht₁

/-- **Speed lemma for projected substeps** (distance to the final value). -/
lemma ODESolution.norm_end_sub_le_of_proj {F : ℝ → E → E} {B : ℝ} (hF : IsBoundedField F B)
    {P : E →L[ℝ] E} (hP : IsOrthProj P) {y : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h)
    (hy : ODESolution (fun t x => P (F t x)) y t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, ‖y t₁ - y t‖ ≤ B * h :=
  hy.norm_end_sub_le (hF.comp_contraction P hP.norm_le) ht₁

/-- Two trajectories of (possibly different) vector fields bounded by `B`, started at the same
value, stay `2 B h`-close on the step, also when evaluated at different times. -/
lemma norm_sub_le_two_mul_of_start {f g : ℝ → E → E} {B : ℝ} (hf : IsBoundedField f B)
    (hg : IsBoundedField g B) {y z : ℝ → E} {t₀ t₁ h : ℝ} (ht₁ : t₁ = t₀ + h)
    (hy : ODESolution f y t₀ t₁) (hz : ODESolution g z t₀ t₁) (h₀ : y t₀ = z t₀) :
    ∀ t ∈ Icc t₀ t₁, ∀ s ∈ Icc t₀ t₁, ‖y t - z s‖ ≤ 2 * B * h := by
  intro t ht s hs
  have h1 := hy.norm_sub_start_le hf ht₁ t ht
  have h2 := hz.norm_sub_start_le hg ht₁ s hs
  have hdecomp : y t - z s = (y t - y t₀) - (z s - z t₀) := by rw [h₀]; abel
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  linarith

end Speed

/-! ### The K-step capture lemma -/

section Capture

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- Pointwise bound on the derivative of `g = (1 - P₁) (A - YK)` used in the capture lemma. -/
lemma kstep_deriv_bound (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hA : ODESolution F A t₀ t₁) (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = A t₀) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (hεt : ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖ ≤ 4 * L * B * h + ε := by
  have hBK : IsBoundedField (fun t x => Q₀ (F t x)) B := hB.comp_contraction Q₀ hQ₀.norm_le
  have ht₁mem : t₁ ∈ Icc t₀ t₁ := ⟨ht.1.trans ht.2, le_rfl⟩
  -- both distances are at most `2 B h`
  have hd1 : ‖A t - YK t‖ ≤ 2 * B * h :=
    norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t ht t ht
  have hd2 : ‖A t - YK t₁‖ ≤ 2 * B * h :=
    norm_sub_le_two_mul_of_start hB hBK ht₁ hA hK hK₀.symm t ht t₁ ht₁mem
  -- splitting of the derivative
  have hsplit : (1 - P₁) (F t (A t) - Q₀ (F t (YK t))) =
      (1 - P₁) (Q₀ (F t (A t) - F t (YK t)))
        + (1 - P₁) ((1 - Q₀) (F t (A t) - F t (YK t₁)))
        + (1 - P₁) ((1 - Q₀) (F t (YK t₁))) := by
    rw [← map_add, ← map_add]
    congr 1
    simp only [sub_apply, one_apply_eq_self, map_sub]
    abel
  have hc1 : ‖(1 - P₁) (Q₀ (F t (A t) - F t (YK t)))‖ ≤ L * (2 * B * h) :=
    calc _ ≤ ‖Q₀ (F t (A t) - F t (YK t))‖ := hP₁.compl.norm_le _
      _ ≤ ‖F t (A t) - F t (YK t)‖ := hQ₀.norm_le _
      _ ≤ L * ‖A t - YK t‖ := hF t _ _
      _ ≤ L * (2 * B * h) := mul_le_mul_of_nonneg_left hd1 hL
  have hc2 : ‖(1 - P₁) ((1 - Q₀) (F t (A t) - F t (YK t₁)))‖ ≤ L * (2 * B * h) :=
    calc _ ≤ ‖(1 - Q₀) (F t (A t) - F t (YK t₁))‖ := hP₁.compl.norm_le _
      _ ≤ ‖F t (A t) - F t (YK t₁)‖ := hQ₀.compl.norm_le _
      _ ≤ L * ‖A t - YK t₁‖ := hF t _ _
      _ ≤ L * (2 * B * h) := mul_le_mul_of_nonneg_left hd2 hL
  rw [hsplit]
  have h3 := norm_add₃_le (a := (1 - P₁) (Q₀ (F t (A t) - F t (YK t))))
    (b := (1 - P₁) ((1 - Q₀) (F t (A t) - F t (YK t₁)))) (c := (1 - P₁) ((1 - Q₀) (F t (YK t₁))))
  linarith

/-- **K-step capture lemma, general form** (normal-component bound only needed on `[t₀, t₁)`).
See `kstep_capture`. -/
theorem kstep_capture_of_Ico (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = A t₀) (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) := by
  have hle : t₀ ≤ t₁ := by linarith
  -- the auxiliary function `g = (1 - P₁) (A - YK)`
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - Q₀ (F t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖
      ≤ 4 * L * B * h + ε := fun t ht =>
    kstep_deriv_bound hF hL hB hP₁ hQ₀ ht₁ hA hK hK₀ (Ico_subset_Icc_self ht) (hε t ht)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hg₁ : g t₁ = (1 - P₁) (A t₁) := by
    simp only [hg, map_sub, sub_apply, one_apply_eq_self,
      hKcap, sub_self, sub_zero]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, hg₁, sub_zero, hlen] at hmvt
  rw [mul_comm h]
  exact hmvt

/-- **K-step capture lemma** (Ceruti–Lubich, [CerutiLubich2022, Lemma 2]; Kieri–Lubich–Walach
2016, proof of Theorem 2.1).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and bounded by `B`, let `A`
solve `A' = F(t, A)` on `[t₀, t₁]`, `t₁ = t₀ + h`, `h ≥ 0`, and let the K-step trajectory `YK`
solve `YK' = Q₀ F(t, YK)` with `YK t₀ = A t₀`, where `Q₀` is an orthogonal projector.  If the
orthogonal projector `P₁` (the new basis) captures `YK t₁`, i.e. `P₁ (YK t₁) = YK t₁`, and the
doubly-normal component of the vector field at `YK t₁` is `ε`-small,
`‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε` for `t ∈ [t₀, t₁]`, then the new basis captures the exact
solution:

    ‖(1 - P₁) (A t₁)‖ ≤ h (4 L B h + ε).

In matrix language (`P₁ X = U₁ U₁ᵀ X`) this is `‖U₁ U₁ᵀ A(t₁) - A(t₁)‖ ≤ ϑ` with
`ϑ = h (4 L B h + ε)`, an explicit version of the bound of Lemma 2 of [CerutiLubich2022] for exact
starting values (`δ = 0`).  The abstract formulation only uses that `P₁`, `Q₀` are orthogonal
projectors. -/
theorem kstep_capture (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h)
    (hA : ODESolution F A t₀ t₁) (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁)
    (hK₀ : YK t₀ = A t₀) (hKcap : P₁ (YK t₁) = YK t₁)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) :=
  kstep_capture_of_Ico hF hL hB hP₁ hQ₀ ht₁ hh hA hK hK₀ hKcap fun t ht =>
    hε t (Ico_subset_Icc_self ht)

/-- The hypotheses of `kstep_capture` are jointly satisfiable with a nontrivial vector field:
on `ℝ` with `F(t, y) = 1` (so `L = 0`, `B = 1`), `A t = t`, `Q₀ = 1`, `YK = A`, `P₁ = 1`, `ε = 0`
on the step `[0, 1]`. -/
example : ‖((1 : ℝ →L[ℝ] ℝ) - 1) ((fun t : ℝ => t) 1)‖ ≤ 1 * (4 * 0 * 1 * 1 + 0) :=
  kstep_capture (E := ℝ) (F := fun _ _ => 1) (fun _ _ _ => by simp) le_rfl
    (fun _ _ => by simp) IsOrthProj.one IsOrthProj.one (t₀ := 0) (t₁ := 1) (h := 1)
    (by norm_num) zero_le_one
    ⟨continuousOn_id, fun t _ => hasDerivWithinAt_id t _⟩
    ⟨continuousOn_id, fun t _ => by simpa using hasDerivWithinAt_id t _⟩
    rfl (by simp) (fun _ _ => by simp)

end Capture

end LeanDLRA
