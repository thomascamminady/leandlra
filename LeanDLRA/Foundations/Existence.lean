import LeanDLRA.Foundations.ODE

/-!
# Global existence of solutions under the standing DLRA assumptions

The error analyses of dynamical low-rank integrators (Kieri–Lubich–Walach 2016;
Ceruti–Lubich 2022, arXiv 2010.02022, Section 2 and Theorems 2–4; Ceruti–Kusch–Lubich 2022,
arXiv 2104.05247; Ceruti–Kusch–Lubich 2024, arXiv 2304.05660) work under the standing
assumption that the right-hand side `F(t, Y)` of the full matrix/tensor ODE `Ȧ = F(t, A)` is

* Lipschitz continuous in `Y`, uniformly in `t`, with constant `L`, and
* bounded by `B`,

and they take for granted that the full problem and all substeps of the integrators
(the K-, L- and S-substeps, which are ODEs with right-hand sides `Q₀ F`, `P₀ F`, `P₁ Q₁ F`,
`-P₁ Q₀ F`, ...) have solutions on each time step. In the abstract setting of this library
(see `Foundations/ODE.lean`) these solutions appear as hypotheses `ODESolution F y a b`.
This file discharges those existence hypotheses.

## Main results

* `LeanDLRA.exists_ODESolution`: if `F` is globally Lipschitz in the state, bounded, and
  continuous in time, then for every `a ≤ b` and every initial value `y₀` there is a solution
  of `y' = F(t, y)` on `[a, b]` with `y a = y₀` (global Picard–Lindelöf).
* `LeanDLRA.existsUnique_ODESolution`, `LeanDLRA.existsUnique_restrict_ODESolution`: existence
  together with uniqueness on `[a, b]` (uniqueness from Grönwall, `ODESolution.eqOn`).
* `LeanDLRA.exists_ODESolution_of_mem`: the value may be prescribed at any `t₁ ∈ [a, b]`.
* `LeanDLRA.exists_ODESolution_Ici`: one global forward solution `y` with `y a = y₀` that solves
  the ODE on every `[a, b]` (glued from interval solutions by uniqueness).
* `LeanDLRA.exists_ODESolution_clm`, `LeanDLRA.exists_ODESolution_comp`,
  `LeanDLRA.exists_ODESolution_neg_comp`: existence for the projected fields
  `t x ↦ G (F t x)` with `G` an arbitrary continuous linear map, in particular for all DLRA
  substeps (`G = Q₀`, `P₀`, `P₁ ∘ Q₁`, `-(P₁ ∘ Q₀)`, ...).
* `LeanDLRA.ODESolution.of_hasDerivAt`: a function with derivative `f t (y t)` at every `t` is a
  solution on every interval.
* `LeanDLRA.exists_flowFamily`, `LeanDLRA.exists_exactFlowFamily`: existence of the family of
  exact flows `Φ n` started from arbitrary values `Y n` at the grid points `t₀ + n h` on
  `[t₀ + n h, t₀ + (n + 1) h]`, as used in Lady Windermere's fan
  (Hairer–Nørsett–Wanner, *Solving ODEs I*, Section II.3; Ceruti–Lubich 2022, proof of Thm 4).

## Proof

We apply Mathlib's Picard–Lindelöf theorem
(`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) on the whole interval
`[a, b]` at once: since `‖F t x‖ ≤ B` everywhere, every candidate trajectory stays in the closed
ball of radius `B * (b - a)` around the initial value, so the hypothesis
`B * max (b - t₁) (t₁ - a) ≤ B * (b - a) - 0` of Picard–Lindelöf (initial time `t₁ ∈ [a, b]`)
holds without any smallness condition on `b - a`. No step-by-step continuation argument is
needed.

## Generalizations with respect to the literature

* `E` is an arbitrary real Banach space (`[CompleteSpace E]`), not only `ℝ^{m×n}`.
* Time continuity is only needed on `[a, b]` (`exists_ODESolution_of_continuousOn`), resp. on
  `[a, ∞)` for the global forward solution.
* The Lipschitz constant `L` may be any real number (only `max L 0` is used), and the bound `B`
  is automatically nonnegative.
* The projected-field results hold for every continuous linear map, not only for
  orthogonal projectors or maps of operator norm `≤ 1`.
-/

open Set Metric
open scoped NNReal

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Auxiliary facts -/

section Auxiliary

variable {F : ℝ → E → E}

omit [NormedSpace ℝ E] in
/-- A field that is Lipschitz with constant `L` is Lipschitz with constant `max L 0`. -/
private lemma isLipschitzField_max_zero {L : ℝ} (hL : IsLipschitzField F L) :
    IsLipschitzField F (max L 0) := fun t x y =>
  (hL t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

omit [NormedSpace ℝ E] in
/-- The bound of a bounded field is nonnegative. -/
private lemma isBoundedField_nonneg {B : ℝ} (hB : IsBoundedField F B) : 0 ≤ B :=
  (norm_nonneg _).trans (hB 0 0)

/-- Composition with a continuous linear map `G` multiplies the Lipschitz constant by `‖G‖`. -/
lemma IsLipschitzField.clm_comp {L : ℝ} (hL : IsLipschitzField F L) (G : E →L[ℝ] E) :
    IsLipschitzField (fun t x => G (F t x)) (‖G‖ * L) := fun t x y => by
  rw [← map_sub, mul_assoc]
  exact (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hL t x y) (norm_nonneg G))

/-- Composition with a continuous linear map `G` multiplies the bound by `‖G‖`. -/
lemma IsBoundedField.clm_comp {B : ℝ} (hB : IsBoundedField F B) (G : E →L[ℝ] E) :
    IsBoundedField (fun t x => G (F t x)) (‖G‖ * B) := fun t x =>
  (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB t x) (norm_nonneg G))

/-- The solutions produced by Mathlib's Picard–Lindelöf theorem (derivatives within `Icc a b`)
are solutions in the sense of `ODESolution` (continuity on `Icc a b`, right derivatives on
`Ico a b`). -/
lemma ODESolution.of_hasDerivWithinAt_Icc {f : ℝ → E → E} {y : ℝ → E} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t) : ODESolution f y a b where
  cont := HasDerivWithinAt.continuousOn h
  deriv t ht := (h t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

/-- A function with derivative `f t (y t)` at every `t` is a solution on every interval. -/
lemma ODESolution.of_hasDerivAt {f : ℝ → E → E} {y : ℝ → E}
    (h : ∀ t, HasDerivAt y (f t (y t)) t) (a b : ℝ) : ODESolution f y a b :=
  ⟨fun t _ => (h t).continuousAt.continuousWithinAt, fun t _ => (h t).hasDerivWithinAt⟩

/-- Solutions are determined by their values on `[a, b]`: a function agreeing with a solution
on `Icc a b` is again a solution on `[a, b]`. -/
lemma ODESolution.congr {f : ℝ → E → E} {y z : ℝ → E} {a b : ℝ} (hy : ODESolution f y a b)
    (h : EqOn y z (Icc a b)) : ODESolution f z a b where
  cont := hy.cont.congr h.symm
  deriv t ht := by
    have hyz : y t = z t := h (Ico_subset_Icc_self ht)
    have hd := hy.deriv t ht
    rw [hyz] at hd
    refine hd.congr_of_eventuallyEq ?_ hyz.symm
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
      fun s hs => (h ⟨ht.1.trans hs.1, hs.2⟩).symm

end Auxiliary

/-! ### Global existence and uniqueness -/

section Existence

variable [CompleteSpace E] {F : ℝ → E → E} {L B : ℝ}

/-- **Global existence (Picard–Lindelöf) on a compact interval, value prescribed at any time
`t₁ ∈ [a, b]`**, with time continuity only required on `[a, b]`.  If `F` is Lipschitz in the
state (uniformly in time) and bounded, then `y' = F(t, y)`, `y t₁ = y₁` has a solution on
`[a, b]` (forwards and backwards from `t₁`). -/
theorem exists_ODESolution_of_mem_of_continuousOn (hL : IsLipschitzField F L)
    (hB : IsBoundedField F B) {a b : ℝ} (hcont : ∀ x, ContinuousOn (fun t => F t x) (Icc a b))
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) (y₁ : E) : ∃ y : ℝ → E, ODESolution F y a b ∧ y t₁ = y₁ := by
  have hB0 : 0 ≤ B := isBoundedField_nonneg hB
  have hab : a ≤ b := ht₁.1.trans ht₁.2
  have hL' := isLipschitzField_max_zero hL
  let K : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩
  let M : ℝ≥0 := ⟨B, hB0⟩
  let R : ℝ≥0 := ⟨B * (b - a), mul_nonneg hB0 (sub_nonneg.2 hab)⟩
  have hPL : IsPicardLindelof F (tmin := a) (tmax := b) ⟨t₁, ht₁⟩ y₁ R 0 M K :=
    { lipschitzOnWith := fun t _ => (hL'.lipschitzWith (le_max_right _ _) t).lipschitzOnWith
      continuousOn := fun x _ => hcont x
      norm_le := fun t _ x _ => hB t x
      mul_max_le := by
        change B * max (b - t₁) (t₁ - a) ≤ B * (b - a) - ((0 : ℝ≥0) : ℝ)
        rw [NNReal.coe_zero, sub_zero]
        exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht₁.1]) (by linarith [ht₁.2])) hB0 }
  obtain ⟨y, hy0, hy⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨y, ODESolution.of_hasDerivWithinAt_Icc hy, hy0⟩

/-- **Global existence (Picard–Lindelöf) on a compact interval**, with time continuity only
required on `[a, b]`.  If `F` is Lipschitz in the state (uniformly in time) and bounded, then
`y' = F(t, y)`, `y a = y₀` has a solution on `[a, b]`.  This is the standing existence
assumption of the DLRA error analyses (e.g. Ceruti–Lubich, arXiv 2010.02022, Section 2). -/
theorem exists_ODESolution_of_continuousOn (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    {a b : ℝ} (hcont : ∀ x, ContinuousOn (fun t => F t x) (Icc a b)) (hab : a ≤ b) (y₀ : E) :
    ∃ y : ℝ → E, ODESolution F y a b ∧ y a = y₀ :=
  exists_ODESolution_of_mem_of_continuousOn hL hB hcont (left_mem_Icc.2 hab) y₀

/-- **Global existence (Picard–Lindelöf) on a compact interval.**  If `F` is Lipschitz in the
state uniformly in time (`IsLipschitzField F L`), bounded (`IsBoundedField F B`) and continuous
in time, then for every `a ≤ b` and `y₀` the initial value problem `y' = F(t, y)`, `y a = y₀`
has a solution on `[a, b]`.  These are exactly the standing assumptions of
Ceruti–Lubich (arXiv 2010.02022, Section 2) and Kieri–Lubich–Walach (2016). -/
theorem exists_ODESolution (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {a b : ℝ} (hab : a ≤ b) (y₀ : E) :
    ∃ y : ℝ → E, ODESolution F y a b ∧ y a = y₀ :=
  exists_ODESolution_of_continuousOn hL hB (fun x => (hcont x).continuousOn) hab y₀

/-- **Existence and uniqueness on `[a, b]`.**  Under the assumptions of `exists_ODESolution`
there is a solution `y` with `y a = y₀`, and every other solution with the same initial value
agrees with `y` on `[a, b]`. -/
theorem existsUnique_ODESolution (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {a b : ℝ} (hab : a ≤ b) (y₀ : E) :
    ∃ y : ℝ → E, (ODESolution F y a b ∧ y a = y₀) ∧
      ∀ z : ℝ → E, ODESolution F z a b → z a = y₀ → EqOn z y (Icc a b) := by
  obtain ⟨y, hy, hy0⟩ := exists_ODESolution hL hB hcont hab y₀
  refine ⟨y, ⟨hy, hy0⟩, fun z hz hz0 => ?_⟩
  exact hz.eqOn hy (isLipschitzField_max_zero hL) (le_max_right _ _) (hz0.trans hy0.symm)

/-- **Existence and uniqueness on `[a, b]`, as a genuine `∃!`.**  Solutions are only determined
on `[a, b]`, so uniqueness is stated for their restrictions to `Icc a b`: there is exactly one
function `u : Icc a b → E` that is the restriction of a solution with initial value `y₀`. -/
theorem existsUnique_restrict_ODESolution (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {a b : ℝ} (hab : a ≤ b) (y₀ : E) :
    ∃! u : Icc a b → E,
      ∃ y : ℝ → E, ODESolution F y a b ∧ y a = y₀ ∧ (Icc a b).domRestrict y = u := by
  obtain ⟨y, ⟨hy, hy0⟩, huniq⟩ := existsUnique_ODESolution hL hB hcont hab y₀
  refine ⟨(Icc a b).domRestrict y, ⟨y, hy, hy0, rfl⟩, ?_⟩
  rintro u ⟨z, hz, hz0, rfl⟩
  funext t
  exact huniq z hz hz0 t.2

/-- **Existence with the value prescribed at an arbitrary time `t₁ ∈ [a, b]`** (e.g. a terminal
value): under the assumptions of `exists_ODESolution`, `y' = F(t, y)`, `y t₁ = y₁` has a
solution on `[a, b]`. -/
theorem exists_ODESolution_of_mem (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {a b t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) (y₁ : E) :
    ∃ y : ℝ → E, ODESolution F y a b ∧ y t₁ = y₁ :=
  exists_ODESolution_of_mem_of_continuousOn hL hB (fun x => (hcont x).continuousOn) ht₁ y₁

/-- **A single global forward solution**, with time continuity only required on `[a, ∞)`.
Under the standing assumptions there is one function `y` with `y a = y₀` which solves
`y' = F(t, y)` on every interval `[a, b]`.  It is obtained by gluing the solutions on
`[a, a + n]`, `n ∈ ℕ`, which agree on their common domains by uniqueness. -/
theorem exists_ODESolution_Ici_of_continuousOn (hL : IsLipschitzField F L)
    (hB : IsBoundedField F B) {a : ℝ} (hcont : ∀ x, ContinuousOn (fun t => F t x) (Ici a))
    (y₀ : E) : ∃ y : ℝ → E, y a = y₀ ∧ ∀ b, ODESolution F y a b := by
  choose Y hY hY0 using fun n : ℕ =>
    exists_ODESolution_of_continuousOn hL hB (fun x => (hcont x).mono Icc_subset_Ici_self)
      (le_add_of_nonneg_right (Nat.cast_nonneg n) : a ≤ a + n) y₀
  have hagree : ∀ m n : ℕ, m ≤ n → EqOn (Y m) (Y n) (Icc a (a + m)) := fun m n hmn =>
    (hY m).eqOn ((hY n).mono le_rfl (by gcongr)) (isLipschitzField_max_zero hL)
      (le_max_right _ _) ((hY0 m).trans (hY0 n).symm)
  refine ⟨fun t => Y ⌈t - a⌉₊ t, by simp [hY0], fun b => ?_⟩
  have hb : b ≤ a + ⌈b - a⌉₊ := by linarith [Nat.le_ceil (b - a)]
  refine ((hY ⌈b - a⌉₊).mono le_rfl hb).congr fun t ht => ?_
  have hm : ⌈t - a⌉₊ ≤ ⌈b - a⌉₊ := Nat.ceil_mono (by linarith [ht.2])
  have ht' : t ∈ Icc a (a + ⌈t - a⌉₊) := ⟨ht.1, by linarith [Nat.le_ceil (t - a)]⟩
  exact (hagree _ _ hm ht').symm

/-- **A single global forward solution.**  Under the standing assumptions there is one function
`y` with `y a = y₀` which solves `y' = F(t, y)` on every interval `[a, b]`; e.g. the exact
solution `A` of the full problem in the global error analyses, valid for all step numbers. -/
theorem exists_ODESolution_Ici (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (a : ℝ) (y₀ : E) :
    ∃ y : ℝ → E, y a = y₀ ∧ ∀ b, ODESolution F y a b :=
  exists_ODESolution_Ici_of_continuousOn hL hB (fun x => (hcont x).continuousOn) y₀

/-! ### Projected fields: the DLRA substeps -/

/-- **Existence for projected fields.**  For every continuous linear map `G` (e.g. an orthogonal
projector `Q₀` or `P₀`, a product `P₁ ∘ Q₁` of projectors, or its negative), the projected
ODE `y' = G (F(t, y))`, `y a = y₀`, has a solution on `[a, b]`.  This covers the K-, L- and
S-substeps of the projector-splitting and (augmented, parallel) BUG integrators. The paper
setting is `‖G‖ ≤ 1`; no norm restriction is needed for existence. -/
theorem exists_ODESolution_clm (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (G : E →L[ℝ] E) {a b : ℝ} (hab : a ≤ b) (y₀ : E) :
    ∃ y : ℝ → E, ODESolution (fun t x => G (F t x)) y a b ∧ y a = y₀ :=
  exists_ODESolution (hL.clm_comp G) (hB.clm_comp G) (fun x => G.continuous.comp (hcont x)) hab
    y₀

/-- **Existence for doubly projected fields** `y' = P (Q (F(t, y)))` (e.g. the Galerkin S-step
`YS' = P₁ Q₁ F(t, YS)` of the BUG integrator, Ceruti–Lubich arXiv 2010.02022, Section 3). -/
theorem exists_ODESolution_comp (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (P Q : E →L[ℝ] E) {a b : ℝ} (hab : a ≤ b)
    (y₀ : E) : ∃ y : ℝ → E, ODESolution (fun t x => P (Q (F t x))) y a b ∧ y a = y₀ :=
  exists_ODESolution_clm hL hB hcont (P.comp Q) hab y₀

/-- **Existence for negatively doubly projected fields** `y' = -P (Q (F(t, y)))` (the backward
S-step `YS' = -P₁ Q₀ F(t, YS)` of the projector-splitting integrator, Lubich–Oseledets 2014;
Kieri–Lubich–Walach 2016). -/
theorem exists_ODESolution_neg_comp (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) (P Q : E →L[ℝ] E) {a b : ℝ} (hab : a ≤ b)
    (y₀ : E) : ∃ y : ℝ → E, ODESolution (fun t x => -P (Q (F t x))) y a b ∧ y a = y₀ :=
  exists_ODESolution_clm hL hB hcont (-(P.comp Q)) hab y₀

/-! ### Exact flow families for Lady Windermere's fan -/

/-- **Flow family on arbitrary subintervals.**  For arbitrary intervals `[s n, s' n]` and
arbitrary starting values `Y n`, there are solutions `Φ n` of `y' = F(t, y)` on `[s n, s' n]`
with `Φ n (s n) = Y n`. -/
theorem exists_flowFamily (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {ι : Type*} {s s' : ι → ℝ} (hss' : ∀ n, s n ≤ s' n)
    (Y : ι → E) : ∃ Φ : ι → ℝ → E, ∀ n, ODESolution F (Φ n) (s n) (s' n) ∧ Φ n (s n) = Y n := by
  choose Φ hΦ using fun n => exists_ODESolution hL hB hcont (hss' n) (Y n)
  exact ⟨Φ, hΦ⟩

/-- **Exact flow family for Lady Windermere's fan.**  On the grid `tₙ = t₀ + n h` (`h ≥ 0`),
for arbitrary values `Y n` (the numerical approximations) there are exact solutions `Φ n` of
`y' = F(t, y)` on `[tₙ, tₙ₊₁]` with `Φ n tₙ = Y n`.  These are the "fan" trajectories of the
global error analysis (Hairer–Nørsett–Wanner I.II.3; Ceruti–Lubich arXiv 2010.02022, proof of
Theorem 4). -/
theorem exists_exactFlowFamily (hL : IsLipschitzField F L) (hB : IsBoundedField F B)
    (hcont : ∀ x, Continuous fun t => F t x) {t₀ h : ℝ} (hh : 0 ≤ h) (Y : ℕ → E) :
    ∃ Φ : ℕ → ℝ → E, ∀ n : ℕ,
      ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h) ∧ Φ n (t₀ + n * h) = Y n :=
  exists_flowFamily hL hB hcont (fun n => by nlinarith) Y

end Existence

/-! ### The hypotheses are jointly satisfiable by a genuinely state-dependent field -/

/-- The standing assumptions (`1`-Lipschitz, bounded by `2`, continuous in time) hold for the
nonlinear, time-dependent scalar field `F t x = sin x + cos t`, so `exists_ODESolution` is not
vacuous. -/
example : ∃ y : ℝ → ℝ,
    ODESolution (fun t x => Real.sin x + Real.cos t) y 0 1 ∧ y 0 = 3 := by
  refine exists_ODESolution (L := 1) (B := 2) (fun t x y => ?_) (fun t x => ?_)
    (fun x => by fun_prop) zero_le_one 3
  · simpa [Real.norm_eq_abs] using Real.abs_sin_sub_sin_le x y
  · rw [Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_one x
    have h2 := Real.abs_cos_le_one t
    linarith [abs_add_le (Real.sin x) (Real.cos t)]

end LeanDLRA
