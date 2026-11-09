import LeanDLRA.Foundations.Galerkin
import LeanDLRA.Foundations.Gronwall
import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.Matrix.ParallelBUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2403.02834: Second-order robust parallel BUG integrators (Kusch)

This module proves the robust error analysis of both second-order parallel BUG integrators of
the paper, first on a real inner product space with commuting orthogonal projectors (section
`Abstract`), then for matrices at the level of the computed factors: `IsStep` (pre-augmented bases
`Û₀ = orth([U₀, F₀V₀])`, `V̂₀ = orth([V₀, F₀ᵀU₀])` and the K-, L-, S-steps), `IsVariant1` (Sec.
3.1, with `U⋆`, `V⋆`), `IsVariant2` (Sec. 3.3), `augSol` (`Ŷ₁ = Û₁ Ŝ₁ V̂₁ᵀ`) and `IsOrth`
(`orth`). Proved, with explicit constants: Lemma 4.3 (`lemma_4_3_matrix`), Lemma 4.4
(`lemma_4_4_variant1`, `lemma_4_4_variant2`), Theorem 4.5 (`theorem_4_5_variant1`,
`theorem_4_5_variant2`), Theorem 4.1 (`theorem_4_1_variant1`, `theorem_4_1_variant2`, rank
adaptive) and Theorem 5.1 (`theorem_5_1_variant1`, `theorem_5_1_variant2`,
`theorem_5_1_variant2_of_le`). **Theorem 5.1 is false as stated**: the paper claims
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ² / (‖Y₁‖ + ‖Y₀‖) + C (h⁴ + h³ ε_r + h² ε_r²)` with `C` independent of the
singular values of the solution, but its proof divides `c₃ (h⁴ + h³ ε_r + h² ε_r²)` by
`‖Y₁‖ + ‖Y₀‖` as well; `theorem_5_1_counterexample` gives, for every `C`, a `2 × 2`, rank-1,
norm-conserving instance satisfying all hypotheses (with `L = 2`, `B ≤ 1`, derivative bounds `2`,
`h ≤ 1`) that violates the bound, with `‖Y₀‖ = h → 0`. The correct statement divides the whole
right side by `‖Y₁‖ + ‖Y₀‖` (`theorem_5_1_variant2`), which gives the paper's form with constant
`C / μ` when `‖Y₀‖ ≥ μ > 0` (`theorem_5_1_variant2_of_le`). **Differences from the paper.**
Assumption 2.1(3) enters through the instances that are used, as explicit hypotheses: `ε_r` at
`Y₀`; for Variant 1 also at the rank-`r` points `(Y₀ + h/2 F₀)V₀V₀ᵀ` (bases `U⋆`, `V₀`),
`U₀U₀ᵀ(Y₀ + h/2 F₀)` (bases `U₀`, `V⋆`) and `Y⋆` of (4.3c); `ε_2r` at `Ŷ⋆` of (4.2a) for
Variant 2. The "bounded third derivatives of the exact solution" are `IsRegularSolution` (the
second derivative is bounded by `M₂` and `M₃`-Lipschitz, which a bound `M₃` on the third
derivative implies, `IsRegularSolution.of_third_deriv`); in Theorem 4.1 they are assumed for the
exact flows started at the iterates, which is what the local error needs, and the constants also
depend on `M₂` and `T`. The paper's proofs apply the midpoint rule to the K- and L-substeps, which
needs third derivatives of those flows; here the midpoint rule is applied only to the exact
solution, and the Galerkin defects of the substeps are shown to be `O(h² ε_r + h³)` from Lipschitz
continuity alone (`galerkin_defect`). Theorem 4.5 for Variant 2 follows directly from the
four-block decomposition, without Lemma 4.2 (not formalized here). Lemma 4.4 is proved for any
enlarged bases (`IsNested`), covering both variants; for Variant 1 its doubly normal block is
bounded through the rank-`r` point `Y⋆`, so `ε_2r` does not appear and the bound has `h ε_r`
where the paper states `h ε_2r` for both variants (weaker when `ε_2r < ε_r`), and the `h² ε_r`
term of Theorems 4.5 and 4.1 (Variant 1) is absorbed using `h ≤ h̄`. The SVD truncation is
abstracted to `‖Y₁ - Ŷ₁‖ ≤ ϑ`, plus
`‖Y₁‖² + ‖Ŷ₁ - Y₁‖² = ‖Ŷ₁‖²` for Theorem 5.1 (the identity `‖Ŷ₁‖² - ‖Y₁‖² = Σ σⱼ²` the paper
uses). Substep and exact solutions are hypotheses (`ODESolution`). Non-vacuity: the counterexample
satisfies all hypotheses of `theorem_5_1_variant2` and is a Variant 2 step; an `example` gives a
Variant 1 step.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace LeanDLRA.Literature.P2403_02834

open LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Exact solutions with bounded higher derivatives -/

/-- *arXiv 2403.02834, assumption of Sec. 4 (bounded second derivative of the exact solution).*
`A` solves `A' = F(t, A)` on `[a, b]` and `‖A''‖ ≤ M₂`, where `A₂` is the second derivative,
`A₂ = d/dt F(t, A(t))`. -/
structure IsC2Solution (F : ℝ → E → E) (A A₂ : ℝ → E) (a b M₂ : ℝ) : Prop where
  sol : ODESolution F A a b
  contF : ContinuousOn (fun t => F t (A t)) (Icc a b)
  deriv₂ : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => F s (A s)) (A₂ t) (Ici t) t
  bound₂ : ∀ t ∈ Ico a b, ‖A₂ t‖ ≤ M₂

/-- *arXiv 2403.02834, assumption of Sec. 4 (bounded third derivatives of the exact solution).*
`A` solves `A' = F(t, A)` on `[a, b]`, `‖A''‖ ≤ M₂`, and the third derivative is bounded by
`M₃` in the sense that `A''` is `M₃`-Lipschitz (see `IsRegularSolution.of_third_deriv`). -/
structure IsRegularSolution (F : ℝ → E → E) (A A₂ : ℝ → E) (a b M₂ M₃ : ℝ) : Prop
    extends IsC2Solution F A A₂ a b M₂ where
  lip₃ : ∀ s ∈ Ico a b, ∀ t ∈ Ico a b, ‖A₂ t - A₂ s‖ ≤ M₃ * |t - s|

/-- *arXiv 2403.02834, auxiliary for Sec. 4.*
Mean value inequality with a quadratic bound on the (right) derivative. -/
private theorem norm_le_poly {f f' : ℝ → E} {a b δ c₀ c₁ c₂ : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (h0 : ‖f a‖ ≤ δ)
    (hb : ∀ x ∈ Ico a b, ‖f' x‖ ≤ c₀ + c₁ * (x - a) + c₂ * (x - a) ^ 2) :
    ∀ x ∈ Icc a b,
      ‖f x‖ ≤ δ + c₀ * (x - a) + c₁ * (x - a) ^ 2 / 2 + c₂ * (x - a) ^ 3 / 3 := by
  intro x hx
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (B := fun x => δ + c₀ * (x - a) + c₁ * (x - a) ^ 2 / 2 + c₂ * (x - a) ^ 3 / 3)
    (B' := fun x => c₀ + c₁ * (x - a) + c₂ * (x - a) ^ 2) hf hf' (by simpa using h0) ?_ hb hx
  intro y
  have h1 : HasDerivAt (fun x : ℝ => x - a) 1 y := (hasDerivAt_id y).sub_const a
  have h2 := (((hasDerivAt_const y δ).add (h1.const_mul c₀)).add
    (((h1.pow 2).const_mul c₁).div_const 2)).add (((h1.pow 3).const_mul c₂).div_const 3)
  refine h2.congr_deriv ?_
  simp
  ring

namespace IsC2Solution

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {a b M₂ : ℝ}

/-- *arXiv 2403.02834, proof of Lemmas 4.2-4.4.*
`‖d/dt A‖` changes at rate at most `M₂`. -/
theorem field_sub_le (hA : IsC2Solution F A A₂ a b M₂) :
    ∀ t ∈ Icc a b, ‖F t (A t) - F a (A a)‖ ≤ M₂ * (t - a) :=
  norm_image_sub_le_of_norm_deriv_right_le_segment hA.contF hA.deriv₂ hA.bound₂

/-- *arXiv 2403.02834, proof of Lemmas 4.2-4.4.*
First order Taylor bound of the exact solution. -/
theorem taylor₁ (hA : IsC2Solution F A A₂ a b M₂) :
    ∀ t ∈ Icc a b, ‖A t - A a - (t - a) • F a (A a)‖ ≤ M₂ * (t - a) ^ 2 / 2 := by
  intro t ht
  have h := norm_le_poly (a := a) (b := b) (δ := 0) (c₀ := 0) (c₁ := M₂) (c₂ := 0)
    (f := fun t => A t - A a - (t - a) • F a (A a))
    (f' := fun t => F t (A t) - F a (A a))
    (by
      refine (hA.sol.cont.sub continuousOn_const).sub ?_
      fun_prop)
    (fun x hx => by
      have h1 : HasDerivAt (fun t : ℝ => (t - a) • F a (A a)) (F a (A a)) x := by
        simpa using ((hasDerivAt_id x).sub_const a).smul_const (F a (A a))
      exact ((hA.sol.deriv x hx).sub_const (A a)).sub h1.hasDerivWithinAt)
    (by simp)
    (fun x hx => by
      have := hA.field_sub_le x (Ico_subset_Icc_self hx)
      simpa using this) t ht
  simpa using h

end IsC2Solution

namespace IsRegularSolution

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {a b M₂ M₃ : ℝ}

/-- *arXiv 2403.02834, proof of Lemmas 4.2-4.4.*
Second order Taylor bound of `t ↦ F(t, A t)`. -/
theorem taylor₂ (hA : IsRegularSolution F A A₂ a b M₂ M₃) (hab : a < b) :
    ∀ t ∈ Icc a b,
      ‖F t (A t) - F a (A a) - (t - a) • A₂ a‖ ≤ M₃ * (t - a) ^ 2 / 2 := by
  intro t ht
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have h := norm_le_poly (a := a) (b := b) (δ := 0) (c₀ := 0) (c₁ := M₃) (c₂ := 0)
    (f := fun t => F t (A t) - F a (A a) - (t - a) • A₂ a)
    (f' := fun t => A₂ t - A₂ a)
    (by
      refine (hA.contF.sub continuousOn_const).sub ?_
      fun_prop)
    (fun x hx => by
      have h1 : HasDerivAt (fun t : ℝ => (t - a) • A₂ a) (A₂ a) x := by
        simpa using ((hasDerivAt_id x).sub_const a).smul_const (A₂ a)
      exact ((hA.deriv₂ x hx).sub_const (F a (A a))).sub h1.hasDerivWithinAt)
    (by simp)
    (fun x hx => by
      have := hA.lip₃ a ha x hx
      rw [abs_of_nonneg (sub_nonneg.2 hx.1)] at this
      simpa using this) t ht
  simpa using h

/-- *arXiv 2403.02834, proof of Lemmas 4.2-4.4 (midpoint rule).*
Third order Taylor bound of the exact solution. -/
theorem taylor₃ (hA : IsRegularSolution F A A₂ a b M₂ M₃) (hab : a < b) :
    ∀ t ∈ Icc a b,
      ‖A t - A a - (t - a) • F a (A a) - ((t - a) ^ 2 / 2) • A₂ a‖ ≤ M₃ * (t - a) ^ 3 / 6 := by
  intro t ht
  have h := norm_le_poly (a := a) (b := b) (δ := 0) (c₀ := 0) (c₁ := 0) (c₂ := M₃ / 2)
    (f := fun t => A t - A a - (t - a) • F a (A a) - ((t - a) ^ 2 / 2) • A₂ a)
    (f' := fun t => F t (A t) - F a (A a) - (t - a) • A₂ a)
    (by
      refine ((hA.sol.cont.sub continuousOn_const).sub ?_).sub ?_ <;> fun_prop)
    (fun x hx => by
      have h1 : HasDerivAt (fun t : ℝ => (t - a) • F a (A a)) (F a (A a)) x := by
        simpa using ((hasDerivAt_id x).sub_const a).smul_const (F a (A a))
      have h2 : HasDerivAt (fun t : ℝ => ((t - a) ^ 2 / 2) • A₂ a) ((x - a) • A₂ a) x := by
        have := ((((hasDerivAt_id x).sub_const a).pow 2).div_const 2).smul_const (A₂ a)
        refine this.congr_deriv ?_
        simp
      exact (((hA.sol.deriv x hx).sub_const (A a)).sub h1.hasDerivWithinAt).sub
        h2.hasDerivWithinAt)
    (by simp)
    (fun x hx => by
      have := hA.taylor₂ hab x (Ico_subset_Icc_self hx)
      simp only [zero_add, zero_mul]
      linarith) t ht
  have h3 : M₃ / 2 * (t - a) ^ 3 / 3 = M₃ * (t - a) ^ 3 / 6 := by ring
  simpa [h3] using h

/-- *arXiv 2403.02834, proof of Lemmas 4.2-4.4.*
**The midpoint rule for the exact solution**, the only place where the third derivative
enters the error analysis: `‖A(a + h) - A(a) - h F(a + h/2, A(a + h/2))‖ ≤ (7/24) M₃ h³`. -/
theorem midpoint_defect {h : ℝ} (hA : IsRegularSolution F A A₂ a (a + h) M₂ M₃) (hh : 0 < h) :
    ‖A (a + h) - A a - h • F (a + h / 2) (A (a + h / 2))‖ ≤ 7 / 24 * M₃ * h ^ 3 := by
  have hab : a < a + h := by linarith
  have h1 := hA.taylor₃ hab (a + h) ⟨hab.le, le_rfl⟩
  have h2 := hA.taylor₂ hab (a + h / 2) ⟨by linarith, by linarith⟩
  rw [add_sub_cancel_left] at h1
  rw [add_sub_cancel_left] at h2
  have e : A (a + h) - A a - h • F (a + h / 2) (A (a + h / 2)) =
      (A (a + h) - A a - h • F a (A a) - (h ^ 2 / 2) • A₂ a) -
        h • (F (a + h / 2) (A (a + h / 2)) - F a (A a) - (h / 2) • A₂ a) := by
    simp only [smul_sub, smul_smul]
    rw [show h * (h / 2) = h ^ 2 / 2 by ring]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hh.le]
  have h3 : h * ‖F (a + h / 2) (A (a + h / 2)) - F a (A a) - (h / 2) • A₂ a‖ ≤
      h * (M₃ * (h / 2) ^ 2 / 2) := mul_le_mul_of_nonneg_left h2 hh.le
  nlinarith

end IsRegularSolution

/-- *arXiv 2403.02834, assumption of Sec. 4.*
**A bound on the third derivative gives `IsRegularSolution`.** -/
theorem IsRegularSolution.of_third_deriv {F : ℝ → E → E} {A A₂ A₃ : ℝ → E} {a b M₂ M₃ : ℝ}
    (hA₁ : ∀ t ∈ Icc a b, HasDerivAt A (F t (A t)) t)
    (hA₂ : ∀ t ∈ Icc a b, HasDerivAt (fun s => F s (A s)) (A₂ t) t)
    (hA₃ : ∀ t ∈ Icc a b, HasDerivAt A₂ (A₃ t) t)
    (hM₂ : ∀ t ∈ Icc a b, ‖A₂ t‖ ≤ M₂) (hM₃ : ∀ t ∈ Icc a b, ‖A₃ t‖ ≤ M₃) :
    IsRegularSolution F A A₂ a b M₂ M₃ where
  sol :=
    { cont := fun t ht => (hA₁ t ht).continuousAt.continuousWithinAt
      deriv := fun t ht => (hA₁ t (Ico_subset_Icc_self ht)).hasDerivWithinAt }
  contF := fun t ht => (hA₂ t ht).continuousAt.continuousWithinAt
  deriv₂ := fun t ht => (hA₂ t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  bound₂ := fun t ht => hM₂ t (Ico_subset_Icc_self ht)
  lip₃ := fun s hs t ht => by
    have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A₂) (f' := A₃) (C := M₃) (s := Icc a b)
      (fun x hx => (hA₃ x hx).hasDerivWithinAt) hM₃
      (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht)
    simpa [Real.norm_eq_abs] using this

/-! ### Galerkin substeps -/

section Galerkin

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {a b L B M₂ : ℝ}

/-- *arXiv 2403.02834, proof of Lemma 4.4.*
A Galerkin substep stays `h η + O(h²)` close to the exact solution, if `η` bounds the part of
`F(a, A a)` that the projector misses. -/
theorem galerkin_close {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hA : IsC2Solution F A A₂ a b M₂) {Y : ℝ → E}
    (hY : ODESolution (fun t x => R (F t x)) Y a b) (hY0 : Y a = A a) {η : ℝ}
    (hη : ‖F a (A a) - R (F a (A a))‖ ≤ η) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ η * (t - a) + (2 * L * B + M₂) * (t - a) ^ 2 / 2 := by
  have hspeed : ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ 2 * B * (t - a) := by
    intro t ht
    have h1 := hY.norm_sub_le_of_bounded (hB.comp_contraction R hR.norm_le) t ht
    have h2 := hA.sol.norm_sub_le_of_bounded hB t ht
    have e : Y t - A t = (Y t - Y a) - (A t - A a) := by rw [hY0]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  intro t ht
  have h := norm_le_poly (a := a) (b := b) (δ := 0) (c₀ := η) (c₁ := 2 * L * B + M₂) (c₂ := 0)
    (f := fun t => Y t - A t) (f' := fun t => R (F t (Y t)) - F t (A t))
    (hY.cont.sub hA.sol.cont) (fun x hx => (hY.deriv x hx).sub (hA.sol.deriv x hx))
    (by simp [hY0])
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      set G := F x (A x)
      set G₀ := F a (A a)
      have e : R (F x (Y x)) - G =
          R (F x (Y x) - G) - ((G₀ - R G₀) + ((G - G₀) - R (G - G₀))) := by
        simp only [map_sub]
        abel
      rw [e]
      have h1 : ‖R (F x (Y x) - G)‖ ≤ L * (2 * B * (x - a)) :=
        (hR.norm_le _).trans ((hF x _ _).trans (mul_le_mul_of_nonneg_left (hspeed x hx') hL))
      have h2 : ‖(G - G₀) - R (G - G₀)‖ ≤ M₂ * (x - a) :=
        (hR.norm_sub_le _).trans (hA.field_sub_le x hx')
      have h3 := norm_add_le (G₀ - R G₀) ((G - G₀) - R (G - G₀))
      have h4 := norm_sub_le (R (F x (Y x) - G)) ((G₀ - R G₀) + ((G - G₀) - R (G - G₀)))
      simp only [zero_mul, add_zero]
      nlinarith) t ht
  simpa using h

/-- *arXiv 2403.02834, proof of Lemma 4.4 (Galerkin defects of the S-, K-, L-steps).*
**The Galerkin defect is third order**: if `R` fixes the starting value, then
`‖R A(t) - Y(t)‖ ≤ L (η τ² / 2 + (2 L B + M₂) τ³ / 6)`, `τ = t - a`.  No smoothness of the
substep flow `Y` is needed (the paper uses bounds of its third derivative). -/
theorem galerkin_defect {R : E →L[ℝ] E} (hR : IsOrthProj R) (hF : IsLipschitzField F L)
    (hL : 0 ≤ L) (hB : IsBoundedField F B) (hA : IsC2Solution F A A₂ a b M₂) {Y : ℝ → E}
    (hY : ODESolution (fun t x => R (F t x)) Y a b) (hY0 : Y a = A a) (hfix : R (A a) = A a)
    {η : ℝ} (hη : ‖F a (A a) - R (F a (A a))‖ ≤ η) :
    ∀ t ∈ Icc a b,
      ‖R (A t) - Y t‖ ≤ L * (η * (t - a) ^ 2 / 2 + (2 * L * B + M₂) * (t - a) ^ 3 / 6) := by
  have hc := galerkin_close hR hF hL hB hA hY hY0 hη
  intro t ht
  have h := norm_le_poly (a := a) (b := b) (δ := 0) (c₀ := 0) (c₁ := L * η)
    (c₂ := L * ((2 * L * B + M₂) / 2))
    (f := fun t => R (A t) - Y t) (f' := fun t => R (F t (A t)) - R (F t (Y t)))
    ((R.continuous.comp_continuousOn hA.sol.cont).sub hY.cont)
    (fun x hx => (R.hasFDerivAt.comp_hasDerivWithinAt x (hA.sol.deriv x hx)).sub (hY.deriv x hx))
    (by simp [hY0, hfix])
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      rw [← map_sub]
      refine (hR.norm_le _).trans ((hF x _ _).trans ?_)
      rw [norm_sub_rev]
      have := mul_le_mul_of_nonneg_left (hc x hx') hL
      nlinarith) t ht
  have e : L * η * (t - a) ^ 2 / 2 + L * ((2 * L * B + M₂) / 2) * (t - a) ^ 3 / 3 =
      L * (η * (t - a) ^ 2 / 2 + (2 * L * B + M₂) * (t - a) ^ 3 / 6) := by ring
  simp only [zero_add, zero_mul, add_zero] at h
  rw [e] at h
  exact h

end Galerkin

/-! ### Projector calculus -/

section Projectors

/-- *arXiv 2403.02834, projector calculus of Sec. 4.*
The normal projector of two orthogonal projectors is a contraction. -/
theorem norm_normal_le {P Q : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q) (x : E) :
    ‖normal P Q x‖ ≤ ‖x‖ := by
  rw [normal_apply]
  exact (hP.norm_sub_le _).trans (hQ.norm_sub_le _)

/-- *arXiv 2403.02834, projector calculus of Sec. 4.*
Enlarging the bases decreases the normal component: if `range Pz ⊆ range P` and
`range Qz ⊆ range Q`, then `‖(1 - P)(1 - Q) y‖ ≤ ‖(1 - Pz)(1 - Qz) y‖`. -/
theorem norm_normal_le_of_absorb {P Q Pz Qz : E →L[ℝ] E} (hP : IsOrthProj P) (hQ : IsOrthProj Q)
    (hc : ∀ x, P (Q x) = Q (P x)) (absP : ∀ x, P (Pz x) = Pz x) (absQ : ∀ x, Q (Qz x) = Qz x)
    (y : E) : ‖normal P Q y‖ ≤ ‖normal Pz Qz y‖ := by
  set w := normal Pz Qz y with hw
  have hq : Q (P (Qz y)) = P (Qz y) := by rw [← hc, absQ]
  have e : normal P Q y = (w - P w) - Q (w - P w) := by
    simp only [hw, normal_apply, map_sub, absP, absQ, hc, hq]
    abel
  rw [e]
  exact (hQ.norm_sub_le _).trans (hP.norm_sub_le _)

/-- **Pre-augmentation** (arXiv 2403.02834, Sec. 3.1, step 1): `P₀`, `Q₀` are the commuting
projectors of `Y₀ = U₀ S₀ V₀ᵀ`, and the projectors `Ph`, `Qh` onto
`Û₀ = orth([U₀, F₀ V₀])`, `V̂₀ = orth([V₀, F₀ᵀ U₀])` contain them and capture `F₀ V₀ V₀ᵀ`,
`U₀ U₀ᵀ F₀` (here `F₀ = F(t₀, Y₀)`). -/
structure IsPreAugmented (F₀ Y₀ : E) (P₀ Q₀ Ph Qh : E →L[ℝ] E) : Prop where
  orthP₀ : IsOrthProj P₀
  orthQ₀ : IsOrthProj Q₀
  comm₀ : ∀ x, P₀ (Q₀ x) = Q₀ (P₀ x)
  fixP₀ : P₀ Y₀ = Y₀
  fixQ₀ : Q₀ Y₀ = Y₀
  absP : ∀ x, Ph (P₀ x) = P₀ x
  absQ : ∀ x, Qh (Q₀ x) = Q₀ x
  capP : Ph (Q₀ F₀) = Q₀ F₀
  capQ : Qh (P₀ F₀) = P₀ F₀

namespace IsPreAugmented

variable {F₀ Y₀ : E} {P₀ Q₀ Ph Qh : E →L[ℝ] E}

/-- *arXiv 2403.02834, Sec. 3.1, Step 1, and proof of Lemma 4.4.*
The augmented left basis captures `F₀` up to the normal component at `Y₀`
(`(I - Û₀Û₀ᵀ) F₀ = (I - Û₀Û₀ᵀ) P⊥(Y₀) F₀`). -/
theorem norm_sub_left_le (hp : IsPreAugmented F₀ Y₀ P₀ Q₀ Ph Qh) (hPh : IsOrthProj Ph) :
    ‖F₀ - Ph F₀‖ ≤ ‖normal P₀ Q₀ F₀‖ := by
  set n := normal P₀ Q₀ F₀ with hn
  have e : F₀ = Q₀ F₀ + P₀ (F₀ - Q₀ F₀) + n := by
    simp only [hn, normal_apply]
    abel
  have e' : F₀ - Ph F₀ = n - Ph n := by
    conv_lhs => rw [e]
    simp only [map_add, hp.absP, hp.capP]
    abel
  rw [e']
  exact hPh.norm_sub_le n

/-- *arXiv 2403.02834, Sec. 3.1, Step 1, and proof of Lemma 4.4.*
The augmented right basis captures `F₀` up to the normal component at `Y₀`. -/
theorem norm_sub_right_le (hp : IsPreAugmented F₀ Y₀ P₀ Q₀ Ph Qh) (hQh : IsOrthProj Qh) :
    ‖F₀ - Qh F₀‖ ≤ ‖normal P₀ Q₀ F₀‖ := by
  set n := normal P₀ Q₀ F₀ with hn
  have e : F₀ = P₀ F₀ + Q₀ (F₀ - P₀ F₀) + n := by
    simp only [hn, normal_apply, map_sub, hp.comm₀]
    abel
  have e' : F₀ - Qh F₀ = n - Qh n := by
    conv_lhs => rw [e]
    simp only [map_add, hp.absQ, hp.capQ]
    abel
  rw [e']
  exact hQh.norm_sub_le n

/-- *arXiv 2403.02834, Sec. 3.1, Step 1, and proof of Lemma 4.4.*
`P̂ Q̂` captures `F₀` up to twice the normal component at `Y₀`. -/
theorem norm_sub_mul_le (hp : IsPreAugmented F₀ Y₀ P₀ Q₀ Ph Qh) (hPh : IsOrthProj Ph)
    (hQh : IsOrthProj Qh) (hc : ∀ x, Ph (Qh x) = Qh (Ph x)) :
    ‖F₀ - Ph (Qh F₀)‖ ≤ 2 * ‖normal P₀ Q₀ F₀‖ := by
  have e : F₀ - Ph (Qh F₀) = (F₀ - Qh F₀) + Qh (F₀ - Ph F₀) := by
    simp only [map_sub, hc]
    abel
  rw [e]
  have h1 := hp.norm_sub_right_le hQh
  have h2 := (hQh.norm_le (F₀ - Ph F₀)).trans (hp.norm_sub_left_le hPh)
  have h3 := norm_add_le (F₀ - Qh F₀) (Qh (F₀ - Ph F₀))
  linarith

end IsPreAugmented

/-- *arXiv 2403.02834, Step 2 of Secs. 3.1 and 3.3 (augmented bases).*
The bases after the basis update: `P1 = Û₁Û₁ᵀ·`, `Q1 = ·V̂₁V̂₁ᵀ` contain `Ph`, `Qh`, and all
left projectors commute with all right projectors. -/
structure IsNested (Ph Qh P1 Q1 : E →L[ℝ] E) : Prop where
  orthP1 : IsOrthProj P1
  orthQ1 : IsOrthProj Q1
  absP : ∀ x, P1 (Ph x) = Ph x
  absQ : ∀ x, Q1 (Qh x) = Qh x
  commPhQ1 : ∀ x, Ph (Q1 x) = Q1 (Ph x)
  commP1Qh : ∀ x, P1 (Qh x) = Qh (P1 x)
  commP1Q1 : ∀ x, P1 (Q1 x) = Q1 (P1 x)

/-- *arXiv 2403.02834, Theorem 4.5, Variant 2.*
The trivial enlargement `P1 = Q1 = 1`. -/
theorem IsNested.one (Ph Qh : E →L[ℝ] E) : IsNested Ph Qh 1 1 where
  orthP1 := IsOrthProj.one
  orthQ1 := IsOrthProj.one
  absP _ := rfl
  absQ _ := rfl
  commPhQ1 _ := rfl
  commP1Qh _ := rfl
  commP1Q1 _ := rfl

/-- *arXiv 2403.02834, Step 3 (Augment) of Secs. 3.1 and 3.3.*
The result `Ŷ₁ = Û₁ Ŝ₁ V̂₁ᵀ` of Step 3 (Augment) in both variants, as a full-space formula:
`Ŷ₁ = YS + Ũ₂Ũ₂ᵀ YK + YL Ṽ₂Ṽ₂ᵀ`, where `Ũ₂Ũ₂ᵀ = P1 - Ph` and `Ṽ₂Ṽ₂ᵀ = Q1 - Qh`. -/
def update (Ph Qh P1 Q1 : E →L[ℝ] E) (yK yL yS : E) : E :=
  yS + (P1 yK - Ph yK) + (Q1 yL - Qh yL)

/-- *arXiv 2403.02834, Sec. 3.3.*
In Variant 2 the new bases contain all of `YK(t₁)` and `YL(t₁)`, and `Ŷ₁` is the parallel BUG
update with the pre-augmented projectors. -/
theorem update_eq_parallelBUG {Ph Qh P1 Q1 : E →L[ℝ] E} {yK yL yS : E} (hK : P1 yK = yK)
    (hL : Q1 yL = yL) : update Ph Qh P1 Q1 yK yL yS = parallelBUG Ph Qh yK yL yS := by
  simp [update, parallelBUG, hK, hL]

/-- *arXiv 2403.02834, Lemma 4.4 (four-block decomposition).*
The four blocks of `P1 Q1 a - Ŷ₁`. -/
theorem update_sub_le {Ph Qh P1 Q1 : E →L[ℝ] E} (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh)
    (hc : ∀ x, Ph (Qh x) = Qh (Ph x)) (hn : IsNested Ph Qh P1 Q1) (a yK yL yS : E) :
    ‖P1 (Q1 a) - update Ph Qh P1 Q1 yK yL yS‖ ≤
      ‖Ph (Qh a) - yS‖ + ‖Qh a - yK‖ + ‖Ph a - yL‖ + ‖normal Ph Qh a‖ := by
  have hP2 : IsOrthProj (P1 - Ph) := hPh.sub_of_le hn.orthP1 hn.absP
  have hQ2 : IsOrthProj (Q1 - Qh) := hQh.sub_of_le hn.orthQ1 hn.absQ
  set n := normal Ph Qh a with hnn
  have e1 : (Q1 - Qh) n = Q1 a - Qh a - Q1 (Ph a) + Qh (Ph a) := by
    simp only [hnn, normal_apply, sub_apply, map_sub, hn.absQ, hQh.idem, hc]
    abel
  have e2 : (P1 - Ph) ((Q1 - Qh) n) =
      P1 (Q1 a) - P1 (Qh a) - Q1 (Ph a) + Qh (Ph a) := by
    rw [e1]
    simp only [sub_apply, map_sub, map_add, hn.commP1Qh, hn.commP1Q1,
      hn.absP, hn.commPhQ1, hc, hPh.idem]
    abel
  have e : P1 (Q1 a) - update Ph Qh P1 Q1 yK yL yS =
      (Ph (Qh a) - yS) + (P1 - Ph) (Qh a - yK) + (Q1 - Qh) (Ph a - yL) +
        (P1 - Ph) ((Q1 - Qh) n) := by
    rw [e2]
    simp only [update, sub_apply, map_sub, hc]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add₃_le).trans ?_) ?_)
  · exact add_le_add (add_le_add le_rfl (hP2.norm_le _)) (hQ2.norm_le _)
  · exact (hP2.norm_le _).trans (hQ2.norm_le _)

end Projectors

/-! ### One step: the blocks -/

section Step

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {t₀ t₁ h L B M₂ M₃ ε : ℝ}
  {Y₀ : E} {P₀ Q₀ Ph Qh P1 Q1 : E →L[ℝ] E} {YK YL YS : ℝ → E}

/-- The Galerkin defects of the three substeps (proof of arXiv 2403.02834, Lemma 4.4). -/
theorem step_defects (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ t₁ Y₀ YK YL YS) (hA : IsC2Solution F A A₂ t₀ t₁ M₂)
    (hA0 : A t₀ = Y₀) (ht : t₀ ≤ t₁) (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) :
    ‖Qh (A t₁) - YK t₁‖ ≤
        L * (ε * (t₁ - t₀) ^ 2 / 2 + (2 * L * B + M₂) * (t₁ - t₀) ^ 3 / 6) ∧
      ‖Ph (A t₁) - YL t₁‖ ≤
        L * (ε * (t₁ - t₀) ^ 2 / 2 + (2 * L * B + M₂) * (t₁ - t₀) ^ 3 / 6) ∧
      ‖Ph (Qh (A t₁)) - YS t₁‖ ≤
        L * (2 * ε * (t₁ - t₀) ^ 2 / 2 + (2 * L * B + M₂) * (t₁ - t₀) ^ 3 / 6) := by
  have hm : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hη1 : ‖F t₀ (A t₀) - Qh (F t₀ (A t₀))‖ ≤ ε := by
    rw [hA0]; exact (hp.norm_sub_right_le hs.orthQ).trans hε
  have hη2 : ‖F t₀ (A t₀) - Ph (F t₀ (A t₀))‖ ≤ ε := by
    rw [hA0]; exact (hp.norm_sub_left_le hs.orthP).trans hε
  have hη3 : ‖F t₀ (A t₀) - (Ph * Qh) (F t₀ (A t₀))‖ ≤ 2 * ε := by
    rw [hA0]
    exact (hp.norm_sub_mul_le hs.orthP hs.orthQ hs.comm).trans (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact galerkin_defect hs.orthQ hF hL hB hA hs.solK (by rw [hs.initK, hA0])
      (by rw [hA0, hs.fixQ]) hη1 t₁ hm
  · exact galerkin_defect hs.orthP hF hL hB hA hs.solL (by rw [hs.initL, hA0])
      (by rw [hA0, hs.fixP]) hη2 t₁ hm
  · exact galerkin_defect (R := Ph * Qh) (hs.orthP.mul hs.orthQ hs.comm) hF hL hB hA hs.solS
      (by rw [hs.initS, hA0]) (by
        rw [hA0]
        change Ph (Qh Y₀) = Y₀
        rw [hs.fixQ, hs.fixP]) hη3 t₁ hm

/-- **Lemma 4.4 of arXiv 2403.02834, first three blocks**: the distance of `P1 Q1 A(t₁)` to `Ŷ₁` is
`2 L ε h² + L (2 L B + M₂) h³ / 2` plus the doubly normal block of `A(t₁)`. -/
theorem update_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ t₁ Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ t₁ M₂) (hA0 : A t₀ = Y₀) (ht : t₀ ≤ t₁)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) :
    ‖P1 (Q1 (A t₁)) - update Ph Qh P1 Q1 (YK t₁) (YL t₁) (YS t₁)‖ ≤
      2 * L * ε * (t₁ - t₀) ^ 2 + L * (2 * L * B + M₂) * (t₁ - t₀) ^ 3 / 2 +
        ‖normal Ph Qh (A t₁)‖ := by
  obtain ⟨h1, h2, h3⟩ := step_defects hF hL hB hp hs hA hA0 ht hε
  have h4 := update_sub_le hs.orthP hs.orthQ hs.comm hn (A t₁) (YK t₁) (YL t₁) (YS t₁)
  nlinarith

/-- *arXiv 2403.02834, Lemmas 4.2-4.4 (doubly normal block).*
**The doubly normal block of the exact solution.**  Let `Z` approximate `A(t₀ + h/2)` up to
`ρ`, let the normal component of `F(t₀ + h/2, Z)` for smaller bases `Pz`, `Qz` be at most `η`.
By the midpoint rule, `‖(1 - Ph)(1 - Qh) A(t₀ + h)‖ ≤ h η + h L ρ + (7/24) M₃ h³`. -/
theorem normal_block_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) {Pz Qz : E →L[ℝ] E}
    (hPh : IsOrthProj Ph) (hQh : IsOrthProj Qh) (hc : ∀ x, Ph (Qh x) = Qh (Ph x))
    (absP : ∀ x, Ph (Pz x) = Pz x) (absQ : ∀ x, Qh (Qz x) = Qz x)
    (h0 : normal Ph Qh Y₀ = 0) (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃)
    (hA0 : A t₀ = Y₀) (hh : 0 < h)
    {Z : E} {ρ η : ℝ} (hZ : ‖Z - A (t₀ + h / 2)‖ ≤ ρ)
    (hη : ‖normal Pz Qz (F (t₀ + h / 2) Z)‖ ≤ η) :
    ‖normal Ph Qh (A (t₀ + h))‖ ≤ h * η + h * L * ρ + 7 / 24 * M₃ * h ^ 3 := by
  set y := F (t₀ + h / 2) Z with hy
  set r := A (t₀ + h) - Y₀ - h • y with hr
  have e : A (t₀ + h) = Y₀ + h • y + r := by
    simp only [hr]
    abel
  have hd := hA.midpoint_defect hh
  have hdiff : ‖y - F (t₀ + h / 2) (A (t₀ + h / 2))‖ ≤ L * ρ :=
    (hF _ _ _).trans (mul_le_mul_of_nonneg_left hZ hL)
  have hrb : ‖r‖ ≤ h * (L * ρ) + 7 / 24 * M₃ * h ^ 3 := by
    have e2 : r = (A (t₀ + h) - A t₀ - h • F (t₀ + h / 2) (A (t₀ + h / 2))) -
        h • (y - F (t₀ + h / 2) (A (t₀ + h / 2))) := by
      simp only [hr, hA0, smul_sub]
      abel
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hh.le]
    have := mul_le_mul_of_nonneg_left hdiff hh.le
    linarith
  have e3 : normal Ph Qh (A (t₀ + h)) = h • normal Ph Qh y + normal Ph Qh r := by
    conv_lhs => rw [e]
    rw [map_add, map_add, h0, zero_add, map_smul]
  rw [e3]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hh.le]
  have h1 := (norm_normal_le_of_absorb (y := y) hPh hQh hc absP absQ).trans hη
  have h2 := norm_normal_le hPh hQh r
  have := mul_le_mul_of_nonneg_left h1 hh.le
  nlinarith

end Step

/-! ### Variant 2 -/

section Variant2

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {t₀ t₁ h L B M₂ M₃ ε ε₂ ϑ : ℝ}
  {Y₀ : E} {P₀ Q₀ Ph Qh P1 Q1 : E →L[ℝ] E} {YK YL YS : ℝ → E}

/-- *arXiv 2403.02834, (4.2a).*
The Euler half step `Ŷ⋆ = Û₀Û₀ᵀ (Y₀ + h/2 F(t₀, Y₀)) V̂₀V̂₀ᵀ` of (4.2a). -/
noncomputable def halfStepHat (Ph Qh : E →L[ℝ] E) (F : ℝ → E → E) (t₀ h : ℝ) (Y₀ : E) : E :=
  Ph (Qh (Y₀ + (h / 2) • F t₀ Y₀))

/-- `‖Ŷ⋆ - A(t₀ + h/2)‖ ≤ h ε + M₂ h² / 8` (arXiv 2403.02834, proof of Lemma 4.2). -/
theorem halfStepHat_close (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh) (hPh : IsOrthProj Ph)
    (hQh : IsOrthProj Qh) (hc : ∀ x, Ph (Qh x) = Qh (Ph x)) (hfP : Ph Y₀ = Y₀)
    (hfQ : Qh Y₀ = Y₀) (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) :
    ‖halfStepHat Ph Qh F t₀ h Y₀ - A (t₀ + h / 2)‖ ≤ h * ε + M₂ * h ^ 2 / 8 := by
  have h1 := hA.taylor₁ (t₀ + h / 2) ⟨by linarith, by linarith⟩
  rw [add_sub_cancel_left, hA0] at h1
  have e : halfStepHat Ph Qh F t₀ h Y₀ - A (t₀ + h / 2) =
      -((h / 2) • (F t₀ Y₀ - Ph (Qh (F t₀ Y₀)))) -
        (A (t₀ + h / 2) - Y₀ - (h / 2) • F t₀ Y₀) := by
    simp only [halfStepHat, map_add, map_smul, hfQ, hfP, smul_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
  have h2 := (hp.norm_sub_mul_le hPh hQh hc).trans (mul_le_mul_of_nonneg_left hε (by norm_num))
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ h / 2 by positivity)
  nlinarith

/-- *arXiv 2403.02834, Lemma 4.4 and Theorem 4.5.*
The constant `L² B + (5/8) L M₂ + (7/24) M₃` of `h³` in Lemma 4.4 and Theorem 4.5 (V2). -/
noncomputable def constV2 (L B M₂ M₃ : ℝ) : ℝ := L ^ 2 * B + 5 / 8 * L * M₂ + 7 / 24 * M₃

/-- **Lemma 4.4 of arXiv 2403.02834, with the rank-`2r` normal component** (abstract form):
`‖P1 Q1 A(t₁) - Ŷ₁‖ ≤ 3 L h² ε + h ε₂ + c h³`, for any enlargement `P1`, `Q1`. -/
theorem update_error_variant2 (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε)
    (hε₂ : ‖normal Ph Qh (F (t₀ + h / 2) (halfStepHat Ph Qh F t₀ h Y₀))‖ ≤ ε₂) :
    ‖P1 (Q1 (A (t₀ + h))) - update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ≤
      3 * L * h ^ 2 * ε + h * ε₂ + constV2 L B M₂ M₃ * h ^ 3 := by
  have h1 := update_error_le hF hL hB hp hs hn hA.toIsC2Solution hA0 (by linarith) hε
  have h2 := halfStepHat_close hp hs.orthP hs.orthQ hs.comm hs.fixP hs.fixQ hA.toIsC2Solution
    hA0 hh hε
  have h3 := normal_block_le hF hL hs.orthP hs.orthQ hs.comm (Pz := Ph) (Qz := Qh)
    hs.orthP.idem hs.orthQ.idem (by simp [normal_apply, hs.fixQ]) hA hA0 hh h2 hε₂
  rw [add_sub_cancel_left] at h1
  have e : 3 * L * h ^ 2 * ε + h * ε₂ + constV2 L B M₂ M₃ * h ^ 3 =
      2 * L * ε * h ^ 2 + L * (2 * L * B + M₂) * h ^ 3 / 2 +
        (h * ε₂ + h * L * (h * ε + M₂ * h ^ 2 / 8) + 7 / 24 * M₃ * h ^ 3) := by
    unfold constV2
    ring
  rw [e]
  linarith

/-- **Theorem 4.5 of arXiv 2403.02834, Variant 2, before truncation** (abstract form):
`‖A(t₁) - Ŷ₁‖ ≤ 3 L h² ε + h ε₂ + c h³`. -/
theorem local_error_variant2 (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε)
    (hε₂ : ‖normal Ph Qh (F (t₀ + h / 2) (halfStepHat Ph Qh F t₀ h Y₀))‖ ≤ ε₂) :
    ‖A (t₀ + h) - parallelBUG Ph Qh (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ≤
      3 * L * h ^ 2 * ε + h * ε₂ + constV2 L B M₂ M₃ * h ^ 3 := by
  have h1 := update_error_variant2 hF hL hB hp hs (IsNested.one Ph Qh) hA hA0 hh hε hε₂
  rwa [update_eq_parallelBUG (P1 := 1) (Q1 := 1) rfl rfl] at h1

end Variant2

/-! ### Variant 1 -/

section Variant1

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {t₀ h L B M₂ M₃ ε : ℝ}
  {Y₀ : E} {P₀ Q₀ Ph Qh P1 Q1 Ps Qs : E →L[ℝ] E} {YK YL YS : ℝ → E}

/-- *arXiv 2403.02834, (4.3c).*
The rank-`r` half step `Y⋆ = U⋆U⋆ᵀ (Y₀ + h/2 F(t₀, U⋆U⋆ᵀ Y₀ V⋆V⋆ᵀ)) V⋆V⋆ᵀ` of (4.3c). -/
noncomputable def halfStepStar (Ps Qs : E →L[ℝ] E) (F : ℝ → E → E) (t₀ h : ℝ) (Y₀ : E) : E :=
  Ps (Qs (Y₀ + (h / 2) • F t₀ (Ps (Qs Y₀))))

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.*
The half-step bases of Variant 1: `Ps = U⋆U⋆ᵀ·` with `U⋆` spanning `Y₀ V₀ + h/2 F₀ V₀`, and
`Qs = ·V⋆V⋆ᵀ` with `V⋆` spanning `Y₀ᵀ U₀ + h/2 F₀ᵀ U₀`, in full-space form. -/
structure IsHalfStepBasis (F₀ Y₀ : E) (h : ℝ) (P₀ Q₀ Ps Qs : E →L[ℝ] E) : Prop where
  orthPs : IsOrthProj Ps
  orthQs : IsOrthProj Qs
  commP₀Qs : ∀ x, P₀ (Qs x) = Qs (P₀ x)
  fixK : Ps (Y₀ + (h / 2) • Q₀ F₀) = Y₀ + (h / 2) • Q₀ F₀
  fixL : Qs (Y₀ + (h / 2) • P₀ F₀) = Y₀ + (h / 2) • P₀ F₀

/-- *arXiv 2403.02834, Assumption 2.1(3), instances used in Lemma 4.3.*
The instances of Assumption 2.1(3) used in Variant 1 at the rank-`r` points
`(Y₀ + h/2 F₀) V₀V₀ᵀ`, `U₀U₀ᵀ (Y₀ + h/2 F₀)` and `Y⋆`. -/
structure IsStarNormal (F : ℝ → E → E) (t₀ h ε : ℝ) (Y₀ : E) (P₀ Q₀ Ps Qs : E →L[ℝ] E) :
    Prop where
  atK : ‖normal Ps Q₀ (F t₀ (Y₀ + (h / 2) • Q₀ (F t₀ Y₀)))‖ ≤ ε
  atL : ‖normal P₀ Qs (F t₀ (Y₀ + (h / 2) • P₀ (F t₀ Y₀)))‖ ≤ ε
  atStar : ‖normal Ps Qs (F (t₀ + h / 2) (halfStepStar Ps Qs F t₀ h Y₀))‖ ≤ ε

/-- **`Y⋆` is a robust first order approximation at the half step** (arXiv 2403.02834, proof of
Lemma 4.3, where this is quoted from the first-order error bound of the fixed-rank BUG integrator):
`‖Y⋆ - A(t₀ + h/2)‖ ≤ h ε + h² (L B + M₂ / 8)`.  The normal component is used at the rank-`r`
points `X_K = Y₀ + h/2 F₀ V₀V₀ᵀ` and `X_L = Y₀ + h/2 U₀U₀ᵀ F₀`, not at `Y₀`. -/
theorem halfStepStar_close (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hP₀ : IsOrthProj P₀) (hQ₀ : IsOrthProj Q₀)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hN : IsStarNormal F t₀ h ε Y₀ P₀ Q₀ Ps Qs) :
    ‖halfStepStar Ps Qs F t₀ h Y₀ - A (t₀ + h / 2)‖ ≤ h * ε + h ^ 2 * (L * B + M₂ / 8) := by
  have hh2 : 0 ≤ h / 2 := by positivity
  set F₀ := F t₀ Y₀ with hF₀
  have hB₀ : ‖F₀‖ ≤ B := hB _ _
  set X := Y₀ + (h / 2) • F₀ with hX
  -- the normal components at `Y₀` with respect to the half-step bases
  have hKn : ‖normal Ps Q₀ F₀‖ ≤ ε + L * (h / 2 * B) := by
    have h1 : ‖F₀ - F t₀ (Y₀ + (h / 2) • Q₀ F₀)‖ ≤ L * (h / 2 * B) := by
      refine (hF _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh2]
      exact mul_le_mul_of_nonneg_left ((hQ₀.norm_le _).trans hB₀) hh2
    have e : normal Ps Q₀ F₀ = normal Ps Q₀ (F t₀ (Y₀ + (h / 2) • Q₀ F₀)) +
        normal Ps Q₀ (F₀ - F t₀ (Y₀ + (h / 2) • Q₀ F₀)) := by
      rw [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans
      (add_le_add hN.atK ((norm_normal_le hb.orthPs hQ₀ _).trans h1))
  have hLn : ‖normal P₀ Qs F₀‖ ≤ ε + L * (h / 2 * B) := by
    have h1 : ‖F₀ - F t₀ (Y₀ + (h / 2) • P₀ F₀)‖ ≤ L * (h / 2 * B) := by
      refine (hF _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hh2]
      exact mul_le_mul_of_nonneg_left ((hP₀.norm_le _).trans hB₀) hh2
    have e : normal P₀ Qs F₀ = normal P₀ Qs (F t₀ (Y₀ + (h / 2) • P₀ F₀)) +
        normal P₀ Qs (F₀ - F t₀ (Y₀ + (h / 2) • P₀ F₀)) := by
      rw [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans
      (add_le_add hN.atL ((norm_normal_le hP₀ hb.orthQs _).trans h1))
  -- `X` is almost in the half-step bases
  have hX1 : X - Ps X = (h / 2) • normal Ps Q₀ F₀ := by
    have e : X = (Y₀ + (h / 2) • Q₀ F₀) + (h / 2) • (F₀ - Q₀ F₀) := by
      simp only [hX, smul_sub]
      abel
    have e2 : Ps X = (Y₀ + (h / 2) • Q₀ F₀) + (h / 2) • Ps (F₀ - Q₀ F₀) := by
      rw [e, map_add, hb.fixK, map_smul]
    rw [e2, normal_apply, smul_sub]
    simp only [hX, smul_sub]
    abel
  have hX2 : X - Qs X = (h / 2) • normal P₀ Qs F₀ := by
    have e : X = (Y₀ + (h / 2) • P₀ F₀) + (h / 2) • (F₀ - P₀ F₀) := by
      simp only [hX, smul_sub]
      abel
    have e2 : Qs X = (Y₀ + (h / 2) • P₀ F₀) + (h / 2) • Qs (F₀ - P₀ F₀) := by
      rw [e, map_add, hb.fixL, map_smul]
    rw [e2, normal_apply]
    simp only [hX, smul_sub, map_sub, hb.commP₀Qs]
    abel
  have hX3 : ‖X - Ps (Qs X)‖ ≤ h * (ε + L * (h / 2 * B)) := by
    have e : X - Ps (Qs X) = (X - Ps X) + Ps (X - Qs X) := by
      rw [map_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖X - Ps X‖ ≤ h / 2 * (ε + L * (h / 2 * B)) := by
      rw [hX1, norm_smul, Real.norm_of_nonneg hh2]
      exact mul_le_mul_of_nonneg_left hKn hh2
    have h2 : ‖Ps (X - Qs X)‖ ≤ h / 2 * (ε + L * (h / 2 * B)) := by
      refine (hb.orthPs.norm_le _).trans ?_
      rw [hX2, norm_smul, Real.norm_of_nonneg hh2]
      exact mul_le_mul_of_nonneg_left hLn hh2
    linarith
  -- `Y₀` is almost in the half-step bases
  have hY1 : ‖Y₀ - Ps Y₀‖ ≤ h / 2 * B := by
    have e : Y₀ - Ps Y₀ = -((h / 2) • (Q₀ F₀ - Ps (Q₀ F₀))) := by
      have e2 : Ps Y₀ = Y₀ + (h / 2) • Q₀ F₀ - (h / 2) • Ps (Q₀ F₀) := by
        conv_rhs => rw [← hb.fixK]
        rw [map_add, map_smul]
        abel
      rw [e2, smul_sub]
      abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hh2]
    exact mul_le_mul_of_nonneg_left ((hb.orthPs.norm_sub_le _).trans
      ((hQ₀.norm_le _).trans hB₀)) hh2
  have hY2 : ‖Y₀ - Qs Y₀‖ ≤ h / 2 * B := by
    have e : Y₀ - Qs Y₀ = -((h / 2) • (P₀ F₀ - Qs (P₀ F₀))) := by
      have e2 : Qs Y₀ = Y₀ + (h / 2) • P₀ F₀ - (h / 2) • Qs (P₀ F₀) := by
        conv_rhs => rw [← hb.fixL]
        rw [map_add, map_smul]
        abel
      rw [e2, smul_sub]
      abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hh2]
    exact mul_le_mul_of_nonneg_left ((hb.orthQs.norm_sub_le _).trans
      ((hP₀.norm_le _).trans hB₀)) hh2
  have hZ : ‖F t₀ (Ps (Qs Y₀)) - F₀‖ ≤ L * (h * B) := by
    refine (hF _ _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
    have e : Ps (Qs Y₀) - Y₀ = -((Y₀ - Ps Y₀) + Ps (Y₀ - Qs Y₀)) := by
      rw [map_sub]; abel
    rw [e, norm_neg]
    refine (norm_add_le _ _).trans ?_
    have := (hb.orthPs.norm_le (Y₀ - Qs Y₀)).trans hY2
    linarith
  have hS : ‖halfStepStar Ps Qs F t₀ h Y₀ - Ps (Qs X)‖ ≤ h / 2 * (L * (h * B)) := by
    have e : halfStepStar Ps Qs F t₀ h Y₀ - Ps (Qs X) =
        (h / 2) • Ps (Qs (F t₀ (Ps (Qs Y₀)) - F₀)) := by
      simp only [halfStepStar, hX, map_add, map_smul, map_sub, smul_sub]
      abel
    rw [e, norm_smul, Real.norm_of_nonneg hh2]
    exact mul_le_mul_of_nonneg_left
      ((hb.orthPs.norm_le _).trans ((hb.orthQs.norm_le _).trans hZ)) hh2
  have hT := hA.taylor₁ (t₀ + h / 2) ⟨by linarith, by linarith⟩
  rw [add_sub_cancel_left, hA0] at hT
  have e : halfStepStar Ps Qs F t₀ h Y₀ - A (t₀ + h / 2) =
      (halfStepStar Ps Qs F t₀ h Y₀ - Ps (Qs X)) - (X - Ps (Qs X)) -
        (A (t₀ + h / 2) - Y₀ - (h / 2) • F₀) := by
    simp only [hX]
    abel
  rw [e]
  have h1 := norm_sub_le (halfStepStar Ps Qs F t₀ h Y₀ - Ps (Qs X)) (X - Ps (Qs X))
  have h2 := norm_sub_le (halfStepStar Ps Qs F t₀ h Y₀ - Ps (Qs X) - (X - Ps (Qs X)))
    (A (t₀ + h / 2) - Y₀ - (h / 2) • F₀)
  linarith

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.*
The enlargement of Variant 1: `Ph ⊇ Ps`, `Qh ⊇ Qs`, and the left-right commutations. -/
structure IsStarNested (Ph Qh P1 Q1 Ps Qs : E →L[ℝ] E) : Prop where
  absPs : ∀ x, Ph (Ps x) = Ps x
  absQs : ∀ x, Qh (Qs x) = Qs x
  commP1Qs : ∀ x, P1 (Qs x) = Qs (P1 x)
  commPsQ1 : ∀ x, Ps (Q1 x) = Q1 (Ps x)

/-- One half of **Lemma 4.3 of arXiv 2403.02834**: if `P1` contains `YK(t₁) Qs` (the paper's
`Û₁ = orth([Û₀, K(t₁) V̂₀ᵀ V⋆])`), then `‖(1 - P1) A(t₁)‖` is bounded by the K-step defect plus
`h η + h L ρ + (7/24) M₃ h³`, where `ρ` bounds `‖Z - A(t₀ + h/2)‖` and `η` the normal
component of `F(t₀ + h/2, Z)` with respect to `Ps`, `Qs`. -/
theorem norm_sub_left_new_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs) (hsn : IsStarNested Ph Qh P1 Q1 Ps Qs)
    (hcap : P1 (Qs (YK (t₀ + h))) = Qs (YK (t₀ + h)))
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    {Z : E} {ρ η : ℝ} (hZ : ‖Z - A (t₀ + h / 2)‖ ≤ ρ)
    (hη : ‖normal Ps Qs (F (t₀ + h / 2) Z)‖ ≤ η) :
    ‖A (t₀ + h) - P1 (A (t₀ + h))‖ ≤
      ‖Qh (A (t₀ + h)) - YK (t₀ + h)‖ + (h * η + h * L * ρ + 7 / 24 * M₃ * h ^ 3) := by
  set a := A (t₀ + h)
  set w := Qh a - YK (t₀ + h)
  have hP1Ps : ∀ x, P1 (Ps x) = Ps x := fun x => by rw [← hsn.absPs, hn.absP]
  have hQsQh : ∀ x, Qs (Qh x) = Qs x := hb.orthQs.comp_eq_of_comp_eq hs.orthQ hsn.absQs
  have hY : P1 Y₀ = Y₀ := by rw [← hs.fixP, hn.absP]
  have h0 : normal P1 Qs Y₀ = 0 := by
    simp only [normal_apply, map_sub, hsn.commP1Qs, hY]
    abel
  have hnb := normal_block_le hF hL hn.orthP1 hb.orthQs hsn.commP1Qs hP1Ps hb.orthQs.idem h0 hA
    hA0 hh hZ hη
  have e : a - P1 a = (Qs w - P1 (Qs w)) + normal P1 Qs a := by
    have e1 : Qs w = Qs a - Qs (YK (t₀ + h)) := by
      simp only [w, map_sub, hQsQh]
    rw [e1, normal_apply]
    simp only [map_sub]
    rw [hcap]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hnb)
  exact (hn.orthP1.norm_sub_le _).trans (hb.orthQs.norm_le _)

/-- *arXiv 2403.02834, Lemma 4.3.*
The other half of **Lemma 4.3**: if `Q1` contains `Ps YL(t₁)`, then `‖(1 - Q1) A(t₁)‖` is
bounded by the L-step defect plus `h η + h L ρ + (7/24) M₃ h³`. -/
theorem norm_sub_right_new_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs) (hsn : IsStarNested Ph Qh P1 Q1 Ps Qs)
    (hcap : Q1 (Ps (YL (t₀ + h))) = Ps (YL (t₀ + h)))
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    {Z : E} {ρ η : ℝ} (hZ : ‖Z - A (t₀ + h / 2)‖ ≤ ρ)
    (hη : ‖normal Ps Qs (F (t₀ + h / 2) Z)‖ ≤ η) :
    ‖A (t₀ + h) - Q1 (A (t₀ + h))‖ ≤
      ‖Ph (A (t₀ + h)) - YL (t₀ + h)‖ + (h * η + h * L * ρ + 7 / 24 * M₃ * h ^ 3) := by
  set a := A (t₀ + h)
  set w := Ph a - YL (t₀ + h)
  have hQ1Qs : ∀ x, Q1 (Qs x) = Qs x := fun x => by rw [← hsn.absQs, hn.absQ]
  have hPsPh : ∀ x, Ps (Ph x) = Ps x := hb.orthPs.comp_eq_of_comp_eq hs.orthP hsn.absPs
  have hY : Q1 Y₀ = Y₀ := by rw [← hs.fixQ, hn.absQ]
  have h0 : normal Ps Q1 Y₀ = 0 := by
    simp only [normal_apply, hY, sub_self, map_zero]
  have hnb := normal_block_le hF hL hb.orthPs hn.orthQ1 hsn.commPsQ1 hb.orthPs.idem hQ1Qs h0 hA
    hA0 hh hZ hη
  have e : a - Q1 a = (Ps w - Q1 (Ps w)) + normal Ps Q1 a := by
    have e1 : Ps w = Ps a - Ps (YL (t₀ + h)) := by
      simp only [w, map_sub, hPsPh]
    rw [e1, normal_apply]
    simp only [map_sub]
    rw [hcap, hsn.commPsQ1]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hnb)
  exact (hn.orthQ1.norm_sub_le _).trans (hb.orthPs.norm_le _)

/-- *arXiv 2403.02834, Lemma 4.3.*
The constant `(8/3) L² B + (7/12) L M₂ + (7/12) M₃` of `h³` in Lemma 4.3. -/
noncomputable def constL43 (L B M₂ M₃ : ℝ) : ℝ := 8 / 3 * L ^ 2 * B + 7 / 12 * L * M₂ + 7 / 12 * M₃

/-- *arXiv 2403.02834, Lemma 4.4, Variant 1.*
The constant `2 L² B + (5/8) L M₂ + (7/24) M₃` of `h³` in Lemma 4.4 (Variant 1). -/
noncomputable def constV1' (L B M₂ M₃ : ℝ) : ℝ := 2 * L ^ 2 * B + 5 / 8 * L * M₂ + 7 / 24 * M₃

/-- *arXiv 2403.02834, Theorem 4.5, Variant 1.*
The constant `(14/3) L² B + (29/24) L M₂ + (7/8) M₃` of `h³` in Theorem 4.5 (Variant 1). -/
noncomputable def constV1 (L B M₂ M₃ : ℝ) : ℝ := 14 / 3 * L ^ 2 * B + 29 / 24 * L * M₂ + 7 / 8 * M₃

/-- **Lemma 4.3 of arXiv 2403.02834** (abstract form, Variant 1):
`‖A(t₁) - P1 Q1 A(t₁)‖ ≤ 2 h ε + 3 L h² ε + c h³`. -/
theorem lemma_4_3 (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs) (hsn : IsStarNested Ph Qh P1 Q1 Ps Qs)
    (hcapK : P1 (Qs (YK (t₀ + h))) = Qs (YK (t₀ + h)))
    (hcapL : Q1 (Ps (YL (t₀ + h))) = Ps (YL (t₀ + h)))
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hN : IsStarNormal F t₀ h ε Y₀ P₀ Q₀ Ps Qs) :
    ‖A (t₀ + h) - P1 (Q1 (A (t₀ + h)))‖ ≤
      2 * h * ε + 3 * L * h ^ 2 * ε + constL43 L B M₂ M₃ * h ^ 3 := by
  have hρ := halfStepStar_close hF hL hB hp.orthP₀ hp.orthQ₀ hb hA.toIsC2Solution hA0 hh hN
  obtain ⟨hK, hLd, -⟩ := step_defects hF hL hB hp hs hA.toIsC2Solution hA0 (by linarith) hε
  rw [add_sub_cancel_left] at hK hLd
  have h1 := norm_sub_left_new_le hF hL hs hn hb hsn hcapK hA hA0 hh hρ hN.atStar
  have h2 := norm_sub_right_new_le hF hL hs hn hb hsn hcapL hA hA0 hh hρ hN.atStar
  have e : A (t₀ + h) - P1 (Q1 (A (t₀ + h))) =
      (A (t₀ + h) - P1 (A (t₀ + h))) + P1 (A (t₀ + h) - Q1 (A (t₀ + h))) := by
    rw [map_sub]; abel
  rw [e]
  have h3 := hn.orthP1.norm_le (A (t₀ + h) - Q1 (A (t₀ + h)))
  have h4 := norm_add_le (A (t₀ + h) - P1 (A (t₀ + h))) (P1 (A (t₀ + h) - Q1 (A (t₀ + h))))
  have e2 : 2 * h * ε + 3 * L * h ^ 2 * ε + constL43 L B M₂ M₃ * h ^ 3 =
      2 * (L * (ε * h ^ 2 / 2 + (2 * L * B + M₂) * h ^ 3 / 6) +
        (h * ε + h * L * (h * ε + h ^ 2 * (L * B + M₂ / 8)) + 7 / 24 * M₃ * h ^ 3)) := by
    unfold constL43; ring
  rw [e2]
  linarith

/-- **Lemma 4.4 of arXiv 2403.02834, Variant 1** (abstract form): with the rank-`r` half step
`Y⋆` in the doubly normal block, `‖P1 Q1 A(t₁) - Ŷ₁‖ ≤ h ε + 3 L h² ε + c h³`. -/
theorem update_error_variant1 (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs) (hsn : IsStarNested Ph Qh P1 Q1 Ps Qs)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hN : IsStarNormal F t₀ h ε Y₀ P₀ Q₀ Ps Qs) :
    ‖P1 (Q1 (A (t₀ + h))) - update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ≤
      h * ε + 3 * L * h ^ 2 * ε + constV1' L B M₂ M₃ * h ^ 3 := by
  have hρ := halfStepStar_close hF hL hB hp.orthP₀ hp.orthQ₀ hb hA.toIsC2Solution hA0 hh hN
  have h1 := update_error_le hF hL hB hp hs hn hA.toIsC2Solution hA0 (by linarith) hε
  have h3 := normal_block_le hF hL hs.orthP hs.orthQ hs.comm hsn.absPs hsn.absQs
    (by simp [normal_apply, hs.fixQ]) hA hA0 hh hρ hN.atStar
  rw [add_sub_cancel_left] at h1
  have e : h * ε + 3 * L * h ^ 2 * ε + constV1' L B M₂ M₃ * h ^ 3 =
      2 * L * ε * h ^ 2 + L * (2 * L * B + M₂) * h ^ 3 / 2 +
        (h * ε + h * L * (h * ε + h ^ 2 * (L * B + M₂ / 8)) + 7 / 24 * M₃ * h ^ 3) := by
    unfold constV1'; ring
  rw [e]
  linarith

/-- **Theorem 4.5 of arXiv 2403.02834, Variant 1, before truncation** (abstract form):
`‖A(t₁) - Ŷ₁‖ ≤ 3 h ε + 6 L h² ε + c h³`. -/
theorem local_error_variant1 (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hb : IsHalfStepBasis (F t₀ Y₀) Y₀ h P₀ Q₀ Ps Qs) (hsn : IsStarNested Ph Qh P1 Q1 Ps Qs)
    (hcapK : P1 (Qs (YK (t₀ + h))) = Qs (YK (t₀ + h)))
    (hcapL : Q1 (Ps (YL (t₀ + h))) = Ps (YL (t₀ + h)))
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hN : IsStarNormal F t₀ h ε Y₀ P₀ Q₀ Ps Qs) :
    ‖A (t₀ + h) - update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ≤
      3 * h * ε + 6 * L * h ^ 2 * ε + constV1 L B M₂ M₃ * h ^ 3 := by
  have h1 := lemma_4_3 hF hL hB hp hs hn hb hsn hcapK hcapL hA hA0 hh hε hN
  have h2 := update_error_variant1 hF hL hB hp hs hn hb hsn hA hA0 hh hε hN
  have h3 := norm_sub_le_norm_sub_add_norm_sub (A (t₀ + h)) (P1 (Q1 (A (t₀ + h))))
    (update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)))
  have e : constV1 L B M₂ M₃ = constL43 L B M₂ M₃ + constV1' L B M₂ M₃ := by
    unfold constV1 constL43 constV1'; ring
  rw [e]
  linarith

end Variant1

/-! ### Norm preservation (Section 5) -/

section Norm

variable {F : ℝ → E → E} {A A₂ : ℝ → E} {t₀ t₁ h L B M₂ ε ϑ : ℝ}
  {Y₀ : E} {P₀ Q₀ Ph Qh P1 Q1 : E →L[ℝ] E} {YK YL YS : ℝ → E}

/-- *arXiv 2403.02834, proof of Theorem 5.1.*
A Galerkin substep leaves the range of a commuting projector `T` at rate
`‖(1 - T) F₀‖ + O(h)`: `‖(1 - T) Y(t)‖ ≤ η τ + (2 L B + M₂) τ² / 2`. -/
theorem galerkin_compl_le {R T : E →L[ℝ] E} (hR : IsOrthProj R) (hT : IsOrthProj T)
    (hc : ∀ x, T (R x) = R (T x)) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hA : IsC2Solution F A A₂ t₀ t₁ M₂) {Y : ℝ → E}
    (hY : ODESolution (fun t x => R (F t x)) Y t₀ t₁) (hY0 : Y t₀ = A t₀)
    (hfix : T (A t₀) = A t₀) {η : ℝ} (hη : ‖F t₀ (A t₀) - T (F t₀ (A t₀))‖ ≤ η) :
    ∀ t ∈ Icc t₀ t₁, ‖Y t - T (Y t)‖ ≤ η * (t - t₀) + (2 * L * B + M₂) * (t - t₀) ^ 2 / 2 := by
  have hspeed : ∀ t ∈ Icc t₀ t₁, ‖Y t - A t‖ ≤ 2 * B * (t - t₀) := by
    intro t ht
    have h1 := hY.norm_sub_le_of_bounded (hB.comp_contraction R hR.norm_le) t ht
    have h2 := hA.sol.norm_sub_le_of_bounded hB t ht
    have e : Y t - A t = (Y t - Y t₀) - (A t - A t₀) := by rw [hY0]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith
  intro t ht
  have h := norm_le_poly (a := t₀) (b := t₁) (δ := 0) (c₀ := η) (c₁ := 2 * L * B + M₂) (c₂ := 0)
    (f := fun t => Y t - T (Y t)) (f' := fun t => R (F t (Y t)) - T (R (F t (Y t))))
    (hY.cont.sub (T.continuous.comp_continuousOn hY.cont))
    (fun x hx => (hY.deriv x hx).sub (T.hasFDerivAt.comp_hasDerivWithinAt x (hY.deriv x hx)))
    (by simp [hY0, hfix])
    (fun x hx => by
      have hx' := Ico_subset_Icc_self hx
      set v := F x (Y x)
      set v₀ := F t₀ (A t₀)
      have e : R v - T (R v) = R (v₀ - T v₀) + (R (v - v₀) - T (R (v - v₀))) := by
        simp only [map_sub, hc]
        abel
      rw [e]
      have h1 : ‖R (v₀ - T v₀)‖ ≤ η := (hR.norm_le _).trans hη
      have h2 : ‖v - v₀‖ ≤ L * (2 * B * (x - t₀)) + M₂ * (x - t₀) := by
        have e2 : v - v₀ = (v - F x (A x)) + (F x (A x) - v₀) := by abel
        rw [e2]
        refine (norm_add_le _ _).trans (add_le_add ?_ (hA.field_sub_le x hx'))
        exact (hF _ _ _).trans (mul_le_mul_of_nonneg_left (hspeed x hx') hL)
      have h3 : ‖R (v - v₀) - T (R (v - v₀))‖ ≤ ‖v - v₀‖ :=
        (hT.norm_sub_le _).trans (hR.norm_le _)
      have h4 := norm_add_le (R (v₀ - T v₀)) (R (v - v₀) - T (R (v - v₀)))
      simp only [zero_mul, add_zero]
      nlinarith) t ht
  simpa using h

/-- **Pythagoras for `Ŷ₁`** (proof of arXiv 2403.02834, Theorem 5.1 and Remark 5.3): for a
norm-conserving field, `‖Ŷ₁‖² = ‖Y₀‖² + ‖Ũ₂Ũ₂ᵀ YK(t₁)‖² + ‖YL(t₁) Ṽ₂Ṽ₂ᵀ‖²`. -/
theorem norm_sq_update (hs : IsParallelBUGStep F Ph Qh t₀ t₁ Y₀ YK YL YS)
    (hn : IsNested Ph Qh P1 Q1) (ht : t₀ ≤ t₁) (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) :
    ‖update Ph Qh P1 Q1 (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 =
      ‖Y₀‖ ^ 2 + ‖P1 (YK t₁) - Ph (YK t₁)‖ ^ 2 + ‖Q1 (YL t₁) - Qh (YL t₁)‖ ^ 2 := by
  have hm : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hPQ := hs.orthP.mul hs.orthQ hs.comm
  have hS : Ph (Qh (YS t₁)) = YS t₁ :=
    hs.solS.galerkin_mem_range (P := Ph * Qh) hPQ (by
      change Ph (Qh (YS t₀)) = YS t₀
      rw [hs.initS, hs.fixQ, hs.fixP]) t₁ hm
  have hSP : Ph (YS t₁) = YS t₁ := by rw [← hS, hs.orthP.idem]
  have hSQ : Qh (YS t₁) = YS t₁ := by rw [← hS, ← hs.comm, hs.orthQ.idem]
  have hL1 : Ph (YL t₁) = YL t₁ :=
    hs.solL.galerkin_mem_range hs.orthP (by rw [hs.initL, hs.fixP]) t₁ hm
  have hnorm : ‖YS t₁‖ = ‖Y₀‖ := by
    have := hs.solS.galerkin_norm_eq' (P := Ph * Qh) hPQ (by
      change Ph (Qh (YS t₀)) = YS t₀
      rw [hs.initS, hs.fixQ, hs.fixP]) (fun t x _ => by rw [real_inner_comm]; exact hsk t x)
      t₁ hm
    rwa [hs.initS] at this
  have hPP1 : ∀ x, Ph (P1 x) = Ph x := hs.orthP.comp_eq_of_comp_eq hn.orthP1 hn.absP
  have hQQ1 : ∀ x, Qh (Q1 x) = Qh x := hs.orthQ.comp_eq_of_comp_eq hn.orthQ1 hn.absQ
  set a := P1 (YK t₁) - Ph (YK t₁)
  set b := Q1 (YL t₁) - Qh (YL t₁)
  have hPa : Ph a = 0 := by simp [a, hPP1, hs.orthP.idem]
  have hQb : Qh b = 0 := by simp [b, hQQ1, hs.orthQ.idem]
  have hPb : Ph b = b := by simp [b, hn.commPhQ1, hs.comm, hL1]
  have i1 : ⟪YS t₁, a⟫ = 0 := by rw [← hSP, hs.orthP.symm, hPa, inner_zero_right]
  have i2 : ⟪YS t₁, b⟫ = 0 := by rw [← hSQ, hs.orthQ.symm, hQb, inner_zero_right]
  have i3 : ⟪a, b⟫ = 0 := by rw [← hPb, ← hs.orthP.symm, hPa, inner_zero_left]
  have e : update Ph Qh P1 Q1 (YK t₁) (YL t₁) (YS t₁) = YS t₁ + a + b := rfl
  rw [e, norm_add_sq_real, norm_add_sq_real, inner_add_left, i1, i2, i3, hnorm]
  ring

/-- *arXiv 2403.02834, proof of Theorem 5.1.*
`‖Ũ₂Ũ₂ᵀ YK(t₁)‖, ‖YL(t₁) Ṽ₂Ṽ₂ᵀ‖ ≤ h ε + (2 L B + M₂) h² / 2` (proof of Theorem 5.1). -/
theorem norm_new_blocks_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ t₁ Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ t₁ M₂) (hA0 : A t₀ = Y₀) (ht : t₀ ≤ t₁)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) :
    ‖P1 (YK t₁) - Ph (YK t₁)‖ ≤ ε * (t₁ - t₀) + (2 * L * B + M₂) * (t₁ - t₀) ^ 2 / 2 ∧
      ‖Q1 (YL t₁) - Qh (YL t₁)‖ ≤ ε * (t₁ - t₀) + (2 * L * B + M₂) * (t₁ - t₀) ^ 2 / 2 := by
  have hm : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  have hP2 : IsOrthProj (P1 - Ph) := hs.orthP.sub_of_le hn.orthP1 hn.absP
  have hQ2 : IsOrthProj (Q1 - Qh) := hs.orthQ.sub_of_le hn.orthQ1 hn.absQ
  have hK0 : ‖F t₀ (A t₀) - Ph (F t₀ (A t₀))‖ ≤ ε := by
    rw [hA0]; exact (hp.norm_sub_left_le hs.orthP).trans hε
  have hL0 : ‖F t₀ (A t₀) - Qh (F t₀ (A t₀))‖ ≤ ε := by
    rw [hA0]; exact (hp.norm_sub_right_le hs.orthQ).trans hε
  have hK := galerkin_compl_le hs.orthQ hs.orthP (fun x => hs.comm x) hF hL hB hA hs.solK
    (by rw [hs.initK, hA0]) (by rw [hA0, hs.fixP]) hK0 t₁ hm
  have hLl := galerkin_compl_le hs.orthP hs.orthQ (fun x => (hs.comm x).symm) hF hL hB hA
    hs.solL (by rw [hs.initL, hA0]) (by rw [hA0, hs.fixQ]) hL0 t₁ hm
  constructor
  · have e : P1 (YK t₁) - Ph (YK t₁) = (P1 - Ph) (YK t₁ - Ph (YK t₁)) := by
      simp [map_sub, hn.absP, hs.orthP.idem]
    rw [e]
    exact (hP2.norm_le _).trans hK
  · have e : Q1 (YL t₁) - Qh (YL t₁) = (Q1 - Qh) (YL t₁ - Qh (YL t₁)) := by
      simp [map_sub, hn.absQ, hs.orthQ.idem]
    rw [e]
    exact (hQ2.norm_le _).trans hLl

/-- *arXiv 2403.02834, proof of Theorem 5.1.*
Norm drift of `Ŷ₁`: `0 ≤ ‖Ŷ₁‖² - ‖Y₀‖² ≤ 2 (h ε + c h² / 2)²`, `c = 2 L B + M₂`. -/
theorem norm_sq_update_bounds (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ t₁ Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ t₁ M₂) (hA0 : A t₀ = Y₀) (ht : t₀ ≤ t₁)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) :
    ‖Y₀‖ ^ 2 ≤ ‖update Ph Qh P1 Q1 (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 ∧
      ‖update Ph Qh P1 Q1 (YK t₁) (YL t₁) (YS t₁)‖ ^ 2 ≤ ‖Y₀‖ ^ 2 +
        2 * (ε * (t₁ - t₀) + (2 * L * B + M₂) * (t₁ - t₀) ^ 2 / 2) ^ 2 := by
  rw [norm_sq_update hs hn ht hsk]
  obtain ⟨h1, h2⟩ := norm_new_blocks_le hF hL hB hp hs hn hA hA0 ht hε
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  constructor <;> nlinarith [sq_nonneg ‖P1 (YK t₁) - Ph (YK t₁)‖,
    sq_nonneg ‖Q1 (YL t₁) - Qh (YL t₁)‖]

/-- *arXiv 2403.02834, Theorem 5.1.*
The constant `2 + 2 c + c² / 2`, `c = 2 L B + M₂`, of Theorem 5.1. -/
noncomputable def constNorm (L B M₂ : ℝ) : ℝ :=
  2 + 2 * (2 * L * B + M₂) + (2 * L * B + M₂) ^ 2 / 2

/-- *arXiv 2403.02834, Theorem 5.1.* The constant of Theorem 5.1 is nonnegative. -/
theorem constNorm_nonneg (L B M₂ : ℝ) : 0 ≤ constNorm L B M₂ := by
  unfold constNorm
  nlinarith [sq_nonneg (2 * L * B + M₂ + 2)]

/-- **Theorem 5.1 of arXiv 2403.02834, squared form**: for an orthogonal truncation
(`‖Y₁‖² + ‖Ŷ₁ - Y₁‖² = ‖Ŷ₁‖²`, as for SVD truncation) with tolerance `ϑ`,
`|‖Y₁‖² - ‖Y₀‖²| ≤ ϑ² + C (h⁴ + h³ ε + h² ε²)`. -/
theorem norm_sq_drift_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : E}
    (horth : ‖Y₁‖ ^ 2 + ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ^ 2 =
      ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ^ 2)
    (htr : ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ≤ ϑ) :
    |‖Y₁‖ ^ 2 - ‖Y₀‖ ^ 2| ≤
      ϑ ^ 2 + constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) := by
  obtain ⟨hlo, hhi⟩ := norm_sq_update_bounds hF hL hB hp hs hn hA hA0 (by linarith) hε hsk
  rw [add_sub_cancel_left] at hhi
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t₀ Y₀)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hA.bound₂ t₀ ⟨le_rfl, by linarith⟩)
  set c := 2 * L * B + M₂ with hc
  have hc0 : 0 ≤ c := by positivity
  have hϑ := pow_le_pow_left₀ (norm_nonneg _) htr 2
  have hpoly : 2 * (ε * h + c * h ^ 2 / 2) ^ 2 ≤
      constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) := by
    have e : constNorm L B M₂ = 2 + 2 * c + c ^ 2 / 2 := rfl
    rw [e]
    have h4 : 0 ≤ h ^ 4 := by positivity
    have h3 : 0 ≤ h ^ 3 * ε := by positivity
    have h2 : 0 ≤ h ^ 2 * ε ^ 2 := by positivity
    have : 2 * (ε * h + c * h ^ 2 / 2) ^ 2 =
        c ^ 2 / 2 * h ^ 4 + 2 * c * (h ^ 3 * ε) + 2 * (h ^ 2 * ε ^ 2) := by ring
    rw [this]
    nlinarith [mul_nonneg hc0 h4, mul_nonneg hc0 h3, mul_nonneg (sq_nonneg c) h2,
      mul_nonneg (sq_nonneg c) h3, mul_nonneg hc0 h2]
  rw [abs_le]
  have h0 : 0 ≤ ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ^ 2 := by
    positivity
  have hC : 0 ≤ constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) :=
    mul_nonneg (constNorm_nonneg L B M₂) (by positivity)
  constructor <;> nlinarith [sq_nonneg ϑ]

/-- **Theorem 5.1 of arXiv 2403.02834, corrected form** (both variants): for a norm-conserving
field and an orthogonal truncation with tolerance `ϑ`,
`|‖Y₁‖ - ‖Y₀‖| ≤ (ϑ² + C (h⁴ + h³ ε + h² ε²)) / (‖Y₁‖ + ‖Y₀‖)` with
`C = constNorm L B M₂`.  The `C`-term is divided by `‖Y₁‖ + ‖Y₀‖` as well, see
`norm_preservation_of_le` and the counterexample below. -/
theorem norm_preservation (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : E}
    (horth : ‖Y₁‖ ^ 2 + ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ^ 2 =
      ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ^ 2)
    (htr : ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ≤ ϑ) :
    |‖Y₁‖ - ‖Y₀‖| ≤
      (ϑ ^ 2 + constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2)) / (‖Y₁‖ + ‖Y₀‖) := by
  have h1 := norm_sq_drift_le hF hL hB hp hs hn hA hA0 hh hε hsk horth htr
  rcases (add_nonneg (norm_nonneg Y₁) (norm_nonneg Y₀)).eq_or_lt with h0 | hpos
  · have hY₁ : ‖Y₁‖ = 0 := by linarith [norm_nonneg Y₁, norm_nonneg Y₀]
    have hY₀ : ‖Y₀‖ = 0 := by linarith [norm_nonneg Y₁, norm_nonneg Y₀]
    rw [hY₁, hY₀]
    simp
  · rw [le_div_iff₀ hpos]
    have hid : |‖Y₁‖ - ‖Y₀‖| * (‖Y₁‖ + ‖Y₀‖) = |‖Y₁‖ ^ 2 - ‖Y₀‖ ^ 2| := by
      rw [← abs_of_pos hpos, ← abs_mul]
      congr 1
      ring
    rw [hid]
    exact h1

/-- **Theorem 5.1 of arXiv 2403.02834 in the paper's form**, valid when the solution is bounded
away from zero, `‖Y₀‖ ≥ m > 0`:
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ² / (‖Y₁‖ + ‖Y₀‖) + (C / m) (h⁴ + h³ ε + h² ε²)`.  The constant `C / m`
depends on `m`; by `theorem_5_1_counterexample` it cannot be chosen independently of the
solution. -/
theorem norm_preservation_of_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hp : IsPreAugmented (F t₀ Y₀) Y₀ P₀ Q₀ Ph Qh)
    (hs : IsParallelBUGStep F Ph Qh t₀ (t₀ + h) Y₀ YK YL YS) (hn : IsNested Ph Qh P1 Q1)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = Y₀) (hh : 0 < h)
    (hε : ‖normal P₀ Q₀ (F t₀ Y₀)‖ ≤ ε) (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : E}
    (horth : ‖Y₁‖ ^ 2 + ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ^ 2 =
      ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h))‖ ^ 2)
    (htr : ‖update Ph Qh P1 Q1 (YK (t₀ + h)) (YL (t₀ + h)) (YS (t₀ + h)) - Y₁‖ ≤ ϑ)
    {m : ℝ} (hm : 0 < m) (hY₀ : m ≤ ‖Y₀‖) :
    |‖Y₁‖ - ‖Y₀‖| ≤ ϑ ^ 2 / (‖Y₁‖ + ‖Y₀‖) +
      constNorm L B M₂ / m * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) := by
  have h1 := norm_preservation hF hL hB hp hs hn hA hA0 hh hε hsk horth htr
  have hpos : 0 < ‖Y₁‖ + ‖Y₀‖ := by linarith [norm_nonneg Y₁]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hC : 0 ≤ constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) :=
    mul_nonneg (constNorm_nonneg L B M₂) (by positivity)
  rw [add_div] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left hC hm (by linarith [norm_nonneg Y₁])

end Norm

/-! ### Global error (Theorem 4.1) -/

section Global

variable {F : ℝ → E → E} {L : ℝ}

/-- *arXiv 2403.02834, Theorem 4.1 (Lady Windermere's fan).*
Lady Windermere's fan with local errors `h g + ϑ`. -/
theorem fan_le (hF : IsLipschitzField F L) (hL : 0 ≤ L) {t₀ h : ℝ} (hh : 0 ≤ h) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {Y : ℕ → E} {Φ : ℕ → ℝ → E}
    (hΦ : ∀ k < N, ODESolution F (Φ k) (t₀ + k * h) (t₀ + k * h + h))
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = Y k) {g ϑ : ℝ} (hg : 0 ≤ g) (hϑ : 0 ≤ ϑ)
    (hloc : ∀ k < N, ‖Φ k (t₀ + k * h + h) - Y (k + 1)‖ ≤ h * g + ϑ) {T : ℝ} :
    ∀ k ≤ N, (k : ℝ) * h ≤ T →
      ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * g + k * ϑ) := by
  have e : ∀ k : ℕ, t₀ + ((k : ℝ) + 1) * h = t₀ + k * h + h := fun k => by ring
  intro k hk hT
  have h1 := lady_windermere hF hL hh hA (Φ := Φ) (Y := Y) (ℓ := h * g + ϑ)
    (fun n hn => by rw [e]; exact hΦ n hn) hΦ₀
    (fun n hn => by rw [e, norm_sub_rev]; exact hloc n hn) k hk
  have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
  have hexp : Real.exp (L * (k * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have h2 : ‖Y 0 - A t₀‖ + k * (h * g + ϑ) ≤ ‖Y 0 - A t₀‖ + T * g + k * ϑ := by
    have := mul_le_mul_of_nonneg_right hT hg
    nlinarith
  calc ‖Y k - A (t₀ + k * h)‖ ≤ Real.exp (L * (k * h)) * (‖Y 0 - A t₀‖ + k * (h * g + ϑ)) := h1
    _ ≤ Real.exp (L * T) * (‖Y 0 - A t₀‖ + T * g + k * ϑ) := by
      apply mul_le_mul hexp h2 (by positivity) (Real.exp_pos _).le

end Global

end Abstract

/-! ## The integrators on matrices -/

section Matrices

open scoped LeanDLRA.Frobenius
open Matrix (fromCols fromBlocks)

variable {m n r a b c d e f : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype a] [Fintype b]
  [Fintype c] [Fintype d] [Fintype e] [Fintype f] [DecidableEq m] [DecidableEq n] [DecidableEq r]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [DecidableEq e] [DecidableEq f]

/-- *arXiv 2403.02834, the map orth(·) of Sec. 3.*
`W = orth(X)`: `W` has orthonormal columns and the same range as `X`. -/
structure IsOrth {k l : Type*} [Fintype k] [Fintype l] [DecidableEq l] (W : Matrix m l ℝ)
    (X : Matrix m k ℝ) : Prop where
  orthonormal : Wᵀ * W = 1
  capture : W * Wᵀ * X = X
  span : ∃ C : Matrix k l ℝ, W = X * C

/-- *arXiv 2403.02834, the map orth(·) of Sec. 3.* `orth([X₁, X₂])` captures `X₁`. -/
theorem IsOrth.capture_left {k₁ k₂ l : Type*} [Fintype k₁] [Fintype k₂] [Fintype l]
    [DecidableEq l] {W : Matrix m l ℝ} {X₁ : Matrix m k₁ ℝ} {X₂ : Matrix m k₂ ℝ}
    (hW : IsOrth W (fromCols X₁ X₂)) : W * Wᵀ * X₁ = X₁ := by
  have h := hW.capture
  rw [Matrix.mul_fromCols] at h
  exact ((Matrix.fromCols_ext_iff _ _ _ _).1 h).1

/-- *arXiv 2403.02834, the map orth(·) of Sec. 3.* `orth([X₁, X₂])` captures `X₂`. -/
theorem IsOrth.capture_right {k₁ k₂ l : Type*} [Fintype k₁] [Fintype k₂] [Fintype l]
    [DecidableEq l] {W : Matrix m l ℝ} {X₁ : Matrix m k₁ ℝ} {X₂ : Matrix m k₂ ℝ}
    (hW : IsOrth W (fromCols X₁ X₂)) : W * Wᵀ * X₂ = X₂ := by
  have h := hW.capture
  rw [Matrix.mul_fromCols] at h
  exact ((Matrix.fromCols_ext_iff _ _ _ _).1 h).2

/-- *arXiv 2403.02834, the map orth(·) of Sec. 3.*
If `range X ⊆ range W'`, then `range orth(X) ⊆ range W'`. -/
theorem IsOrth.range_le {k l l' : Type*} [Fintype k] [Fintype l] [Fintype l'] [DecidableEq l]
    {W : Matrix m l ℝ} {X : Matrix m k ℝ} (hW : IsOrth W X) {W' : Matrix m l' ℝ}
    (h : W' * W'ᵀ * X = X) : W' * W'ᵀ * W = W := by
  obtain ⟨C, hC⟩ := hW.span
  rw [hC, ← Matrix.mul_assoc, h]

/-- *arXiv 2403.02834, the map orth(·) of Sec. 3.*
Transposed capture: `W Wᵀ X = X` gives `Xᵀ W Wᵀ = Xᵀ`. -/
theorem transpose_capture {k l : Type*} [Fintype k] [Fintype l] {W : Matrix m l ℝ}
    {X : Matrix m k ℝ} (h : W * Wᵀ * X = X) : Xᵀ * (W * Wᵀ) = Xᵀ := by
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose h

/-- *arXiv 2403.02834, S-step of Secs. 3.1 and 3.3.*
The augmented Galerkin field of the S-step, `S ↦ Û₀ᵀ F(t, Û₀ S V̂₀ᵀ) V̂₀`. -/
def sFieldAug (Uh : Matrix m a ℝ) (Vh : Matrix n b ℝ) (F : ℝ → Matrix m n ℝ → Matrix m n ℝ)
    (t : ℝ) (S : Matrix a b ℝ) : Matrix a b ℝ :=
  Uhᵀ * F t (Uh * S * Vhᵀ) * Vh

/-- *arXiv 2403.02834, S-step of Secs. 3.1 and 3.3.* The S-step trajectory `Û₀ S̄ V̂₀ᵀ` solves
`Y' = Ph Qh F(t, Y)`. -/
theorem odeSolution_sFieldAug {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {Uh : Matrix m a ℝ}
    {Vh : Matrix n b ℝ} {S : ℝ → Matrix a b ℝ} {t₀ t₁ : ℝ}
    (hS : ODESolution (sFieldAug Uh Vh F) S t₀ t₁) :
    ODESolution (fun t x => leftProj Uh (rightProj Vh (F t x))) (fun t => Uh * S t * Vhᵀ)
      t₀ t₁ :=
  MatrixKSL.odeSolution_comp_clm hS
    ((Frobenius.rightMulCLM Vhᵀ).comp (Frobenius.leftMulCLM Uh)) fun t x => by
      simp only [ContinuousLinearMap.comp_apply, Frobenius.leftMulCLM_apply,
        Frobenius.rightMulCLM_apply, leftProj_rightProj_apply, sFieldAug]

/-- **Steps 1 and 2 of both second-order parallel integrators** (arXiv 2403.02834, Secs. 3.1 and
3.3): from `Y₀ = U₀ S₀ V₀ᵀ`, the pre-augmented bases `Û₀ = orth([U₀, F(t₀, Y₀) V₀])`,
`V̂₀ = orth([V₀, F(t₀, Y₀)ᵀ U₀])`, and the K-, L- and S-steps
`K' = F(t, K V̂₀ᵀ) V̂₀`, `K(t₀) = U₀ S₀ V₀ᵀ V̂₀`; `L' = F(t, Û₀ Lᵀ)ᵀ Û₀`,
`L(t₀) = V₀ S₀ᵀ U₀ᵀ Û₀`; `S̄' = Û₀ᵀ F(t, Û₀ S̄ V̂₀ᵀ) V̂₀`, `S̄(t₀) = Û₀ᵀ U₀ S₀ V₀ᵀ V̂₀`. -/
structure IsStep (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (Uh : Matrix m a ℝ) (Vh : Matrix n b ℝ)
    (K : ℝ → Matrix m b ℝ) (Lf : ℝ → Matrix n a ℝ) (Sb : ℝ → Matrix a b ℝ) : Prop where
  orthU₀ : U₀ᵀ * U₀ = 1
  orthV₀ : V₀ᵀ * V₀ = 1
  augU : IsOrth Uh (fromCols U₀ (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀))
  augV : IsOrth Vh (fromCols V₀ ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀))
  kSol : ODESolution (MatrixKSL.kField Vh F) K t₀ t₁
  kStart : K t₀ = U₀ * S₀ * V₀ᵀ * Vh
  lSol : ODESolution (MatrixKSL.lField Uh F) Lf t₀ t₁
  lStart : Lf t₀ = V₀ * S₀ᵀ * U₀ᵀ * Uh
  sSol : ODESolution (sFieldAug Uh Vh F) Sb t₀ t₁
  sStart : Sb t₀ = Uhᵀ * U₀ * S₀ * V₀ᵀ * Vh

/-- *arXiv 2403.02834, Step 3 (Augment) of Secs. 3.1 and 3.3.*
The augmented coefficient matrix `Ŝ₁ = [[S̄(t₁), L(t₁)ᵀ Ṽ₂], [Ũ₂ᵀ K(t₁), 0]]` (Step 3 of
both variants). -/
def augCoeff (Sb₁ : Matrix a b ℝ) (U₂ : Matrix m c ℝ) (V₂ : Matrix n d ℝ) (K₁ : Matrix m b ℝ)
    (L₁ : Matrix n a ℝ) : Matrix (a ⊕ c) (b ⊕ d) ℝ :=
  fromBlocks Sb₁ (L₁ᵀ * V₂) (U₂ᵀ * K₁) 0

/-- *arXiv 2403.02834, Step 3 (Augment) of Secs. 3.1 and 3.3.*
The untruncated result `Ŷ₁ = Û₁ Ŝ₁ V̂₁ᵀ`, `Û₁ = [Û₀, Ũ₂]`, `V̂₁ = [V̂₀, Ṽ₂]`. -/
def augSol (Uh : Matrix m a ℝ) (U₂ : Matrix m c ℝ) (Vh : Matrix n b ℝ) (V₂ : Matrix n d ℝ)
    (Sb₁ : Matrix a b ℝ) (K₁ : Matrix m b ℝ) (L₁ : Matrix n a ℝ) : Matrix m n ℝ :=
  fromCols Uh U₂ * augCoeff Sb₁ U₂ V₂ K₁ L₁ * (fromCols Vh V₂)ᵀ

/-- *arXiv 2403.02834, Step 3 (Augment).*
`Û₁ Ŝ₁ V̂₁ᵀ = Û₀ S̄ V̂₀ᵀ + Û₀ L(t₁)ᵀ Ṽ₂Ṽ₂ᵀ + Ũ₂Ũ₂ᵀ K(t₁) V̂₀ᵀ`. -/
theorem augSol_eq_sum (Uh : Matrix m a ℝ) (U₂ : Matrix m c ℝ) (Vh : Matrix n b ℝ)
    (V₂ : Matrix n d ℝ) (Sb₁ : Matrix a b ℝ) (K₁ : Matrix m b ℝ) (L₁ : Matrix n a ℝ) :
    augSol Uh U₂ Vh V₂ Sb₁ K₁ L₁ =
      Uh * Sb₁ * Vhᵀ + Uh * L₁ᵀ * (V₂ * V₂ᵀ) + U₂ * U₂ᵀ * K₁ * Vhᵀ := by
  rw [augSol, augCoeff, Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- *arXiv 2403.02834, Step 3 (Augment).*
`Ŷ₁` is the abstract update `YS + (P1 - Ph) YK + (Q1 - Qh) YL`. -/
theorem augSol_eq_update (Uh : Matrix m a ℝ) (U₂ : Matrix m c ℝ) (Vh : Matrix n b ℝ)
    (V₂ : Matrix n d ℝ) (Sb₁ : Matrix a b ℝ) (K₁ : Matrix m b ℝ) (L₁ : Matrix n a ℝ) :
    augSol Uh U₂ Vh V₂ Sb₁ K₁ L₁ =
      update (leftProj Uh) (rightProj Vh) (leftProj (fromCols Uh U₂))
        (rightProj (fromCols Vh V₂)) (K₁ * Vhᵀ) (Uh * L₁ᵀ) (Uh * Sb₁ * Vhᵀ) := by
  rw [augSol_eq_sum]
  simp only [update, leftProj_apply, rightProj_apply', matrix_augmented_proj, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc]
  abel

namespace IsStep

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ}
  {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ} {Sb : ℝ → Matrix a b ℝ}

/-- *arXiv 2403.02834, Sec. 3.1, Step 1.* `Û₀Û₀ᵀ U₀ = U₀`, in right-associated form. -/
theorem absU (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb) {k : Type*} [Fintype k]
    (X : Matrix r k ℝ) :
    Uh * (Uhᵀ * (U₀ * X)) = U₀ * X := by
  simp only [← Matrix.mul_assoc, hs.augU.capture_left]

/-- *arXiv 2403.02834, Sec. 3.1, Step 1.* `V̂₀V̂₀ᵀ V₀ = V₀`, in right-associated form. -/
theorem absVc (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb) {k : Type*} [Fintype k]
    (X : Matrix r k ℝ) :
    Vh * (Vhᵀ * (V₀ * X)) = V₀ * X := by
  simp only [← Matrix.mul_assoc, hs.augV.capture_left]

/-- *arXiv 2403.02834, Sec. 3.1, Step 1.* `V₀ᵀ V̂₀V̂₀ᵀ = V₀ᵀ`. -/
theorem absV (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb) :
    V₀ᵀ * (Vh * Vhᵀ) = V₀ᵀ :=
  transpose_capture hs.augV.capture_left

/-- *arXiv 2403.02834, Sec. 3.1, Step 1.*
**The matrix step is an abstract pre-augmented step.** -/
theorem isPreAugmented (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb) :
    IsPreAugmented (F t₀ (U₀ * S₀ * V₀ᵀ)) (U₀ * S₀ * V₀ᵀ) (leftProj U₀) (rightProj V₀)
      (leftProj Uh) (rightProj Vh) where
  orthP₀ := isOrthProj_leftProj hs.orthU₀
  orthQ₀ := isOrthProj_rightProj hs.orthV₀
  comm₀ := leftProj_rightProj_comm U₀ V₀
  fixP₀ := by rw [Matrix.mul_assoc]; exact leftProj_mul_left hs.orthU₀ _
  fixQ₀ := rightProj_mul_transpose hs.orthV₀ _
  absP := leftProj_leftProj_of_mul hs.augU.capture_left
  absQ := rightProj_rightProj_of_mul hs.augV.capture_left
  capP := by
    simp only [leftProj_apply, rightProj_apply]
    rw [← Matrix.mul_assoc, hs.augU.capture_right]
  capQ := by
    have h := transpose_capture hs.augV.capture_right
    generalize F t₀ (U₀ * S₀ * V₀ᵀ) = F₀ at h ⊢
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    simp only [leftProj_apply, rightProj_apply, Matrix.mul_assoc] at h ⊢
    rw [h]

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.*
**The matrix step is an abstract parallel BUG step** with the pre-augmented projectors. -/
theorem isParallelBUGStep (hs : IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb) :
    IsParallelBUGStep F (leftProj Uh) (rightProj Vh) t₀ t₁ (U₀ * S₀ * V₀ᵀ)
      (fun t => K t * Vhᵀ) (fun t => Uh * (Lf t)ᵀ) (fun t => Uh * Sb t * Vhᵀ) where
  orthP := isOrthProj_leftProj hs.augU.orthonormal
  orthQ := isOrthProj_rightProj hs.augV.orthonormal
  comm := leftProj_rightProj_comm Uh Vh
  fixP := by simp only [leftProj_apply, Matrix.mul_assoc, hs.absU]
  fixQ := by simp only [rightProj_apply, Matrix.mul_assoc, hs.absV]
  solK := MatrixKSL.odeSolution_kField hs.kSol
  initK := by simp only [hs.kStart, Matrix.mul_assoc, hs.absV]
  solL := MatrixKSL.odeSolution_lField hs.lSol
  initL := by
    simp only [hs.lStart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      hs.absU]
  solS := odeSolution_sFieldAug hs.sSol
  initS := by simp only [hs.sStart, Matrix.mul_assoc, hs.absV, hs.absU]

end IsStep

/-- **Variant 2** (arXiv 2403.02834, Sec. 3.3): `Û₁ = [Û₀, Ũ₂] = orth([Û₀, K(t₁)])` and
`V̂₁ = [V̂₀, Ṽ₂] = orth([V̂₀, L(t₁)])`. -/
structure IsVariant2 (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ t₁ : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (Uh : Matrix m a ℝ) (Vh : Matrix n b ℝ)
    (U₂ : Matrix m c ℝ) (V₂ : Matrix n d ℝ) (K : ℝ → Matrix m b ℝ) (Lf : ℝ → Matrix n a ℝ)
    (Sb : ℝ → Matrix a b ℝ) : Prop extends IsStep F t₀ t₁ U₀ S₀ V₀ Uh Vh K Lf Sb where
  newU : IsOrth (fromCols Uh U₂) (fromCols Uh (K t₁))
  newV : IsOrth (fromCols Vh V₂) (fromCols Vh (Lf t₁))

/-- **Variant 1** (arXiv 2403.02834, Sec. 3.1): `U⋆ = orth(Y₀ V₀ + h/2 F(t₀, Y₀) V₀)`,
`V⋆ = orth(Y₀ᵀ U₀ + h/2 F(t₀, Y₀)ᵀ U₀)`, `Û₁ = [Û₀, Ũ₂] = orth([Û₀, K(t₁) V̂₀ᵀ V⋆])` and
`V̂₁ = [V̂₀, Ṽ₂] = orth([V̂₀, L(t₁) Û₀ᵀ U⋆])`, on `[t₀, t₁] = [t₀, t₀ + h]`. -/
structure IsVariant1 (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (t₀ h : ℝ) (U₀ : Matrix m r ℝ)
    (S₀ : Matrix r r ℝ) (V₀ : Matrix n r ℝ) (Uh : Matrix m a ℝ) (Vh : Matrix n b ℝ)
    (Us : Matrix m e ℝ) (Vs : Matrix n f ℝ) (U₂ : Matrix m c ℝ) (V₂ : Matrix n d ℝ)
    (K : ℝ → Matrix m b ℝ) (Lf : ℝ → Matrix n a ℝ) (Sb : ℝ → Matrix a b ℝ) : Prop
    extends IsStep F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh K Lf Sb where
  starU : IsOrth Us (U₀ * S₀ * V₀ᵀ * V₀ + (h / 2) • (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀))
  starV : IsOrth Vs ((U₀ * S₀ * V₀ᵀ)ᵀ * U₀ + (h / 2) • ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀))
  newU : IsOrth (fromCols Uh U₂) (fromCols Uh (K (t₀ + h) * Vhᵀ * Vs))
  newV : IsOrth (fromCols Vh V₂) (fromCols Vh (Lf (t₀ + h) * Uhᵀ * Us))

/-- *arXiv 2403.02834, Step 2 of Secs. 3.1 and 3.3.*
The projectors after the basis update of either variant form an abstract enlargement. -/
theorem isNested_of_capture {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ} {U₂ : Matrix m c ℝ}
    {V₂ : Matrix n d ℝ} (hU : (fromCols Uh U₂)ᵀ * fromCols Uh U₂ = 1)
    (hV : (fromCols Vh V₂)ᵀ * fromCols Vh V₂ = 1)
    (hcU : fromCols Uh U₂ * (fromCols Uh U₂)ᵀ * Uh = Uh)
    (hcV : fromCols Vh V₂ * (fromCols Vh V₂)ᵀ * Vh = Vh) :
    IsNested (leftProj Uh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (rightProj Vh)
      (leftProj (fromCols Uh U₂)) (rightProj (fromCols Vh V₂)) where
  orthP1 := isOrthProj_leftProj hU
  orthQ1 := isOrthProj_rightProj hV
  absP := leftProj_leftProj_of_mul hcU
  absQ := rightProj_rightProj_of_mul hcV
  commPhQ1 := leftProj_rightProj_comm _ _
  commP1Qh := leftProj_rightProj_comm _ _
  commP1Q1 := leftProj_rightProj_comm _ _

namespace IsVariant2

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} {U₀ : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ}
  {U₂ : Matrix m c ℝ} {V₂ : Matrix n d ℝ} {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ}
  {Sb : ℝ → Matrix a b ℝ}

/-- *arXiv 2403.02834, Step 2.* The bases after the basis update form an abstract enlargement. -/
theorem isNested (hv : IsVariant2 F t₀ t₁ U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb) :
    IsNested (leftProj Uh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (rightProj Vh)
      (leftProj (fromCols Uh U₂)) (rightProj (fromCols Vh V₂)) :=
  isNested_of_capture hv.newU.orthonormal hv.newV.orthonormal hv.newU.capture_left
    hv.newV.capture_left

/-- *arXiv 2403.02834, Sec. 3.3.*
In Variant 2, `Ŷ₁ = Û₁ Ŝ₁ V̂₁ᵀ` is the parallel BUG update with the pre-augmented bases:
`Ŷ₁ = YS(t₁) + (I - Û₀Û₀ᵀ) YK(t₁) + YL(t₁) (I - V̂₀V̂₀ᵀ)`. -/
theorem augSol_eq_parallelBUG (hv : IsVariant2 F t₀ t₁ U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb) :
    augSol Uh U₂ Vh V₂ (Sb t₁) (K t₁) (Lf t₁) =
      parallelBUG (leftProj Uh) (rightProj Vh) (K t₁ * Vhᵀ) (Uh * (Lf t₁)ᵀ)
        (Uh * Sb t₁ * Vhᵀ) := by
  rw [augSol_eq_update]
  apply update_eq_parallelBUG
  · rw [leftProj_apply, ← Matrix.mul_assoc, hv.newU.capture_right]
  · rw [rightProj_apply', Matrix.mul_assoc, transpose_capture hv.newV.capture_right]

end IsVariant2

/-- *arXiv 2403.02834, (4.2a).*
The matrix form of the normal component of `Ŷ⋆`. -/
theorem halfStepHat_eq (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (Uh : Matrix m a ℝ)
    (Vh : Matrix n b ℝ) (t₀ h : ℝ) (Y₀ : Matrix m n ℝ) :
    halfStepHat (leftProj Uh) (rightProj Vh) F t₀ h Y₀ =
      Uh * Uhᵀ * (Y₀ + (h / 2) • F t₀ Y₀) * (Vh * Vhᵀ) := by
  simp only [halfStepHat, leftProj_apply, rightProj_apply', Matrix.mul_assoc]

/-- *arXiv 2403.02834, (4.3c).*
The matrix form of `Y⋆`. -/
theorem halfStepStar_eq (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (Us : Matrix m e ℝ)
    (Vs : Matrix n f ℝ) (t₀ h : ℝ) (Y₀ : Matrix m n ℝ) :
    halfStepStar (leftProj Us) (rightProj Vs) F t₀ h Y₀ =
      Us * Usᵀ * (Y₀ + (h / 2) • F t₀ (Us * Usᵀ * Y₀ * (Vs * Vsᵀ))) * (Vs * Vsᵀ) := by
  simp only [halfStepStar, leftProj_apply, rightProj_apply', Matrix.mul_assoc]

namespace IsVariant1

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ h : ℝ} {U₀ : Matrix m r ℝ}
  {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ}
  {Us : Matrix m e ℝ} {Vs : Matrix n f ℝ} {U₂ : Matrix m c ℝ} {V₂ : Matrix n d ℝ}
  {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ} {Sb : ℝ → Matrix a b ℝ}

/-- *arXiv 2403.02834, Step 2.* The bases after the basis update form an abstract enlargement. -/
theorem isNested (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb) :
    IsNested (leftProj Uh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (rightProj Vh)
      (leftProj (fromCols Uh U₂)) (rightProj (fromCols Vh V₂)) :=
  isNested_of_capture hv.newU.orthonormal hv.newV.orthonormal hv.newU.capture_left
    hv.newV.capture_left

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.* `U⋆`, `V⋆` give abstract half-step bases. -/
theorem isHalfStepBasis (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb) :
    IsHalfStepBasis (F t₀ (U₀ * S₀ * V₀ᵀ)) (U₀ * S₀ * V₀ᵀ) h (leftProj U₀) (rightProj V₀)
      (leftProj Us) (rightProj Vs) where
  orthPs := isOrthProj_leftProj hv.starU.orthonormal
  orthQs := isOrthProj_rightProj hv.starV.orthonormal
  commP₀Qs := leftProj_rightProj_comm _ _
  fixK := by
    have hY : U₀ * S₀ * V₀ᵀ * V₀ * V₀ᵀ = U₀ * S₀ * V₀ᵀ := by
      rw [Matrix.mul_assoc (U₀ * S₀) V₀ᵀ V₀, hv.orthV₀, Matrix.mul_one]
    have e : U₀ * S₀ * V₀ᵀ + (h / 2) • rightProj V₀ (F t₀ (U₀ * S₀ * V₀ᵀ)) =
        (U₀ * S₀ * V₀ᵀ * V₀ + (h / 2) • (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀)) * V₀ᵀ := by
      rw [Matrix.add_mul, Matrix.smul_mul, hY, rightProj_apply]
    rw [e, leftProj_apply, ← Matrix.mul_assoc, hv.starU.capture]
  fixL := by
    have hY : ∀ X : Matrix r n ℝ, U₀ * (U₀ᵀ * (U₀ * X)) = U₀ * X := fun X => by
      rw [← Matrix.mul_assoc U₀ᵀ, hv.orthU₀, Matrix.one_mul]
    have e : U₀ * S₀ * V₀ᵀ + (h / 2) • leftProj U₀ (F t₀ (U₀ * S₀ * V₀ᵀ)) =
        U₀ * ((U₀ * S₀ * V₀ᵀ)ᵀ * U₀ + (h / 2) • ((F t₀ (U₀ * S₀ * V₀ᵀ))ᵀ * U₀))ᵀ := by
      simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.transpose_mul, Matrix.transpose_transpose, leftProj_apply, Matrix.mul_assoc, hY]
    rw [e, rightProj_apply', Matrix.mul_assoc, transpose_capture hv.starV.capture]

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.* `range U⋆ ⊆ range Û₀`, `range V⋆ ⊆ range V̂₀`. -/
theorem isStarNested (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb) :
    IsStarNested (leftProj Uh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) (rightProj Vh)
      (leftProj (fromCols Uh U₂)) (rightProj (fromCols Vh V₂)) (leftProj Us)
      (rightProj Vs) where
  absPs := by
    refine leftProj_leftProj_of_mul (hv.starU.range_le ?_)
    rw [Matrix.mul_add, Matrix.mul_smul, hv.augU.capture_right]
    congr 1
    simp only [Matrix.mul_assoc, hv.toIsStep.absU]
  absQs := by
    refine rightProj_rightProj_of_mul (hv.starV.range_le ?_)
    rw [Matrix.mul_add, Matrix.mul_smul, hv.augV.capture_right]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      hv.toIsStep.absVc]
  commP1Qs := leftProj_rightProj_comm _ _
  commPsQ1 := leftProj_rightProj_comm _ _

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.* `Û₁` captures `K(t₁) V̂₀ᵀ V⋆`. -/
theorem capK (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb) :
    leftProj (fromCols Uh U₂) (rightProj Vs (K (t₀ + h) * Vhᵀ)) =
      rightProj Vs (K (t₀ + h) * Vhᵀ) := by
  rw [rightProj_apply, leftProj_apply, ← Matrix.mul_assoc, hv.newU.capture_right]

/-- *arXiv 2403.02834, Sec. 3.1, Step 2.* `V̂₁` captures `L(t₁) Û₀ᵀ U⋆`. -/
theorem capL (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb) :
    rightProj (fromCols Vh V₂) (leftProj Us (Uh * (Lf (t₀ + h))ᵀ)) =
      leftProj Us (Uh * (Lf (t₀ + h))ᵀ) := by
  have h1 := transpose_capture hv.newV.capture_right
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
  rw [rightProj_apply', leftProj_apply]
  simp only [Matrix.mul_assoc] at h1 ⊢
  rw [h1]

end IsVariant1

/-! ### Local error, matrix form -/

section LocalMatrix

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {t₀ h L B M₂ M₃ ε ε₂ ϑ : ℝ}
  {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ}
  {Vh : Matrix n b ℝ} {Us : Matrix m e ℝ} {Vs : Matrix n f ℝ} {U₂ : Matrix m c ℝ}
  {V₂ : Matrix n d ℝ} {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ} {Sb : ℝ → Matrix a b ℝ}
  {A A₂ : ℝ → Matrix m n ℝ}

/-- **Lemma 4.4 of arXiv 2403.02834 for Variant 2** (matrix form, explicit constants).  Let `F`
be `L`-Lipschitz and bounded by `B`, let the exact solution `A` with `A(t₀) = Y₀ = U₀ S₀ V₀ᵀ`
have second derivative bounded by `M₂` and third derivative bounded by `M₃`
(`IsRegularSolution`), and let the normal components satisfy
`‖(I - U₀U₀ᵀ) F(t₀, Y₀) (I - V₀V₀ᵀ)‖ ≤ ε_r` and, at the rank-`2r` half step
`Ŷ⋆ = Û₀Û₀ᵀ (Y₀ + h/2 F(t₀, Y₀)) V̂₀V̂₀ᵀ` of (4.2a),
`‖(I - Û₀Û₀ᵀ) F(t₀ + h/2, Ŷ⋆) (I - V̂₀V̂₀ᵀ)‖ ≤ ε_2r`.  Then
`‖Û₁Û₁ᵀ A(t₁) V̂₁V̂₁ᵀ - Ŷ₁‖ ≤ 3 L h² ε_r + h ε_2r + c h³`, `c = L² B + (5/8) L M₂ + (7/24) M₃`. -/
theorem lemma_4_4_variant2 (hv : IsVariant2 F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hε₂ : ‖(1 - Uh * Uhᵀ) * F (t₀ + h / 2) (Uh * Uhᵀ *
      (U₀ * S₀ * V₀ᵀ + (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ)) * (Vh * Vhᵀ)) * (1 - Vh * Vhᵀ)‖ ≤ ε₂) :
    ‖fromCols Uh U₂ * (fromCols Uh U₂)ᵀ * A (t₀ + h) * (fromCols Vh V₂ * (fromCols Vh V₂)ᵀ) -
        augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ≤
      3 * L * h ^ 2 * ε + h * ε₂ + constV2 L B M₂ M₃ * h ^ 3 := by
  have h1 := update_error_variant2 (ε := ε) (ε₂ := ε₂) hF hL hB
    hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hv.isNested hA hA0 hh
    (by rw [normal_leftProj_rightProj_apply]; exact hε)
    (by rw [halfStepHat_eq, normal_leftProj_rightProj_apply]; exact hε₂)
  rw [augSol_eq_update]
  simpa only [leftProj_apply, rightProj_apply', Matrix.mul_assoc] using h1

/-- **Theorem 4.5 of arXiv 2403.02834, Variant 2** (matrix form): under the hypotheses of
`lemma_4_4_variant2`, if `Y₁` is the truncation of `Ŷ₁ = Û₁ Ŝ₁ V̂₁ᵀ` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`, then
`‖A(t₁) - Y₁‖ ≤ 3 L h² ε_r + h ε_2r + c h³ + ϑ`. -/
theorem theorem_4_5_variant2 (hv : IsVariant2 F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hε₂ : ‖(1 - Uh * Uhᵀ) * F (t₀ + h / 2) (Uh * Uhᵀ *
      (U₀ * S₀ * V₀ᵀ + (h / 2) • F t₀ (U₀ * S₀ * V₀ᵀ)) * (Vh * Vhᵀ)) * (1 - Vh * Vhᵀ)‖ ≤ ε₂)
    {Y₁ : Matrix m n ℝ}
    (htr : ‖Y₁ - augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ≤ ϑ) :
    ‖A (t₀ + h) - Y₁‖ ≤ 3 * L * h ^ 2 * ε + h * ε₂ + constV2 L B M₂ M₃ * h ^ 3 + ϑ := by
  have h1 := local_error_variant2 (ε := ε) (ε₂ := ε₂) hF hL hB
    hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hA hA0 hh
    (by rw [normal_leftProj_rightProj_apply]; exact hε)
    (by rw [halfStepHat_eq, normal_leftProj_rightProj_apply]; exact hε₂)
  rw [← hv.augSol_eq_parallelBUG] at h1
  have h2 := norm_sub_le_norm_sub_add_norm_sub (A (t₀ + h))
    (augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))) Y₁
  have h3 := norm_sub_rev Y₁ (augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)))
  linarith

/-- *arXiv 2403.02834, Assumption 2.1(3), instances used in Lemma 4.3.*
The matrix forms of the normal components used in Variant 1. -/
theorem isStarNormal_of_matrix {Y₀ : Matrix m n ℝ}
    (hK : ‖(1 - Us * Usᵀ) * F t₀ (Y₀ + (h / 2) • (F t₀ Y₀ * V₀ * V₀ᵀ)) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hL : ‖(1 - U₀ * U₀ᵀ) * F t₀ (Y₀ + (h / 2) • (U₀ * U₀ᵀ * F t₀ Y₀)) * (1 - Vs * Vsᵀ)‖ ≤ ε)
    (hS : ‖(1 - Us * Usᵀ) * F (t₀ + h / 2) (Us * Usᵀ *
      (Y₀ + (h / 2) • F t₀ (Us * Usᵀ * Y₀ * (Vs * Vsᵀ))) * (Vs * Vsᵀ)) * (1 - Vs * Vsᵀ)‖ ≤ ε) :
    IsStarNormal F t₀ h ε Y₀ (leftProj U₀) (rightProj V₀) (leftProj Us) (rightProj Vs) where
  atK := by
    rw [normal_leftProj_rightProj_apply, rightProj_apply]
    exact hK
  atL := by
    rw [normal_leftProj_rightProj_apply, leftProj_apply]
    exact hL
  atStar := by
    rw [normal_leftProj_rightProj_apply, halfStepStar_eq]
    exact hS

/-- **Lemma 4.3 of arXiv 2403.02834** (matrix form, Variant 1): with the normal components bounded
by `ε_r` at `Y₀` and at the rank-`r` points `X_K = (Y₀ + h/2 F(t₀, Y₀)) V₀V₀ᵀ` (bases `U⋆`, `V₀`),
`X_L = U₀U₀ᵀ (Y₀ + h/2 F(t₀, Y₀))` (bases `U₀`, `V⋆`) and `Y⋆` of (4.3c) (bases `U⋆`, `V⋆`),
`‖A(t₁) - Û₁Û₁ᵀ A(t₁) V̂₁V̂₁ᵀ‖ ≤ 2 h ε_r + 3 L h² ε_r + c h³`,
`c = (8/3) L² B + (7/12) L M₂ + (7/12) M₃`.  For `h ≤ h̄` this is the printed form
`C₁ h³ + C₂ ε_r h` with `C₂ = 2 + 3 L h̄`. -/
theorem lemma_4_3_matrix (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hK : ‖(1 - Us * Usᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀ * V₀ᵀ)) *
      (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hLn : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (U₀ * U₀ᵀ * F t₀ (U₀ * S₀ * V₀ᵀ))) *
      (1 - Vs * Vsᵀ)‖ ≤ ε)
    (hS : ‖(1 - Us * Usᵀ) * F (t₀ + h / 2) (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ +
      (h / 2) • F t₀ (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ) * (Vs * Vsᵀ))) * (Vs * Vsᵀ)) *
        (1 - Vs * Vsᵀ)‖ ≤ ε) :
    ‖A (t₀ + h) - fromCols Uh U₂ * (fromCols Uh U₂)ᵀ * A (t₀ + h) *
        (fromCols Vh V₂ * (fromCols Vh V₂)ᵀ)‖ ≤
      2 * h * ε + 3 * L * h ^ 2 * ε + constL43 L B M₂ M₃ * h ^ 3 := by
  have h1 := lemma_4_3 (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hv.isNested hv.isHalfStepBasis hv.isStarNested hv.capK
    hv.capL hA hA0 hh (by rw [normal_leftProj_rightProj_apply]; exact hε)
    (isStarNormal_of_matrix hK hLn hS)
  simpa only [leftProj_apply, rightProj_apply', Matrix.mul_assoc] using h1

/-- **Lemma 4.4 of arXiv 2403.02834 for Variant 1** (matrix form): under the hypotheses of
`lemma_4_3_matrix`, `‖Û₁Û₁ᵀ A(t₁) V̂₁V̂₁ᵀ - Ŷ₁‖ ≤ h ε_r + 3 L h² ε_r + c h³`,
`c = 2 L² B + (5/8) L M₂ + (7/24) M₃`.  Here the doubly normal block is estimated with the
rank-`r` point `Y⋆`, so no rank-`2r` normal component is needed.  This is weaker than the printed
Lemma 4.4, which has `Ĉ₁ h ε_2r` in place of `h ε_r` for both variants (the two agree when
`ε_2r = ε_r`); it suffices for Theorems 4.5 and 4.1 of Variant 1, which only claim `h ε_r`. -/
theorem lemma_4_4_variant1 (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hK : ‖(1 - Us * Usᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀ * V₀ᵀ)) *
      (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hLn : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (U₀ * U₀ᵀ * F t₀ (U₀ * S₀ * V₀ᵀ))) *
      (1 - Vs * Vsᵀ)‖ ≤ ε)
    (hS : ‖(1 - Us * Usᵀ) * F (t₀ + h / 2) (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ +
      (h / 2) • F t₀ (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ) * (Vs * Vsᵀ))) * (Vs * Vsᵀ)) *
        (1 - Vs * Vsᵀ)‖ ≤ ε) :
    ‖fromCols Uh U₂ * (fromCols Uh U₂)ᵀ * A (t₀ + h) * (fromCols Vh V₂ * (fromCols Vh V₂)ᵀ) -
        augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ≤
      h * ε + 3 * L * h ^ 2 * ε + constV1' L B M₂ M₃ * h ^ 3 := by
  have h1 := update_error_variant1 (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hv.isNested hv.isHalfStepBasis hv.isStarNested hA hA0 hh
    (by rw [normal_leftProj_rightProj_apply]; exact hε) (isStarNormal_of_matrix hK hLn hS)
  rw [augSol_eq_update]
  simpa only [leftProj_apply, rightProj_apply', Matrix.mul_assoc] using h1

/-- **Theorem 4.5 of arXiv 2403.02834, Variant 1** (matrix form): under the hypotheses of
`lemma_4_3_matrix`, for `0 < h ≤ h̄` and a truncation with `‖Y₁ - Ŷ₁‖ ≤ ϑ`,
`‖A(t₁) - Y₁‖ ≤ C̃₁ h ε_r + C̃₂ h³ + ϑ` with `C̃₁ = 3 + 6 L h̄` and
`C̃₂ = (14/3) L² B + (29/24) L M₂ + (7/8) M₃`. -/
theorem theorem_4_5_variant1 (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsRegularSolution F A A₂ t₀ (t₀ + h) M₂ M₃) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    {hbar : ℝ} (hhb : h ≤ hbar)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hK : ‖(1 - Us * Usᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (F t₀ (U₀ * S₀ * V₀ᵀ) * V₀ * V₀ᵀ)) *
      (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hLn : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ + (h / 2) • (U₀ * U₀ᵀ * F t₀ (U₀ * S₀ * V₀ᵀ))) *
      (1 - Vs * Vsᵀ)‖ ≤ ε)
    (hS : ‖(1 - Us * Usᵀ) * F (t₀ + h / 2) (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ +
      (h / 2) • F t₀ (Us * Usᵀ * (U₀ * S₀ * V₀ᵀ) * (Vs * Vsᵀ))) * (Vs * Vsᵀ)) *
        (1 - Vs * Vsᵀ)‖ ≤ ε)
    {Y₁ : Matrix m n ℝ}
    (htr : ‖Y₁ - augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ≤ ϑ) :
    ‖A (t₀ + h) - Y₁‖ ≤ (3 + 6 * L * hbar) * h * ε + constV1 L B M₂ M₃ * h ^ 3 + ϑ := by
  have h1 := local_error_variant1 (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hv.isNested hv.isHalfStepBasis hv.isStarNested hv.capK
    hv.capL hA hA0 hh (by rw [normal_leftProj_rightProj_apply]; exact hε)
    (isStarNormal_of_matrix hK hLn hS)
  rw [← augSol_eq_update] at h1
  have h2 := norm_sub_le_norm_sub_add_norm_sub (A (t₀ + h))
    (augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))) Y₁
  have h3 := norm_sub_rev Y₁ (augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)))
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have h3 : 6 * L * h ^ 2 * ε ≤ 6 * L * hbar * h * ε := by
    have : 0 ≤ L * h * ε := by positivity
    nlinarith
  linarith

end LocalMatrix

/-! ### Norm preservation and global error, matrix form -/

section GlobalMatrix

variable {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {L B M₂ M₃ : ℝ}

/-- **Theorem 5.1 of arXiv 2403.02834, Variant 2, corrected** (matrix form).  If
`⟨Z, F(t, Z)⟩ = 0` (5.1), `F` is `L`-Lipschitz and bounded by `B`, the exact solution through
`Y₀` has `‖A''‖ ≤ M₂`, `‖(I - U₀U₀ᵀ) F(t₀, Y₀) (I - V₀V₀ᵀ)‖ ≤ ε_r`, and `Y₁` is an orthogonal
truncation of `Ŷ₁` (`‖Y₁‖² + ‖Ŷ₁ - Y₁‖² = ‖Ŷ₁‖²`, as for the SVD truncation of Step 4) with
`‖Ŷ₁ - Y₁‖ ≤ ϑ`, then
`|‖Y₁‖ - ‖Y₀‖| ≤ (ϑ² + C (h⁴ + h³ ε_r + h² ε_r²)) / (‖Y₁‖ + ‖Y₀‖)`,
`C = 2 + 2 c + c² / 2`, `c = 2 L B + M₂`. -/
theorem theorem_5_1_variant2 {t₀ h ε ϑ : ℝ} {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ} {U₂ : Matrix m c ℝ}
    {V₂ : Matrix n d ℝ} {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ}
    {Sb : ℝ → Matrix a b ℝ} {A A₂ : ℝ → Matrix m n ℝ}
    (hv : IsVariant2 F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : Matrix m n ℝ}
    (horth : ‖Y₁‖ ^ 2 + ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ^ 2 =
      ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ^ 2)
    (htr : ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ≤ ϑ) :
    |‖Y₁‖ - ‖U₀ * S₀ * V₀ᵀ‖| ≤ (ϑ ^ 2 + constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2)) /
      (‖Y₁‖ + ‖U₀ * S₀ * V₀ᵀ‖) := by
  rw [augSol_eq_update] at horth htr
  exact norm_preservation (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep
    hv.isNested hA hA0 hh (by rw [normal_leftProj_rightProj_apply]; exact hε) hsk horth htr

/-- **Theorem 5.1 of arXiv 2403.02834, Variant 2, in the paper's form**, for solutions bounded
away from zero: under the hypotheses of `theorem_5_1_variant2` and `‖Y₀‖ ≥ μ > 0`,
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ² / (‖Y₁‖ + ‖Y₀‖) + (C / μ) (h⁴ + h³ ε_r + h² ε_r²)`. -/
theorem theorem_5_1_variant2_of_le {t₀ h ε ϑ μ : ℝ} {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ} {U₂ : Matrix m c ℝ}
    {V₂ : Matrix n d ℝ} {K : ℝ → Matrix m b ℝ} {Lf : ℝ → Matrix n a ℝ}
    {Sb : ℝ → Matrix a b ℝ} {A A₂ : ℝ → Matrix m n ℝ}
    (hv : IsVariant2 F t₀ (t₀ + h) U₀ S₀ V₀ Uh Vh U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : Matrix m n ℝ}
    (horth : ‖Y₁‖ ^ 2 + ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ^ 2 =
      ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ^ 2)
    (htr : ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ≤ ϑ)
    (hμ : 0 < μ) (hY₀ : μ ≤ ‖U₀ * S₀ * V₀ᵀ‖) :
    |‖Y₁‖ - ‖U₀ * S₀ * V₀ᵀ‖| ≤ ϑ ^ 2 / (‖Y₁‖ + ‖U₀ * S₀ * V₀ᵀ‖) +
      constNorm L B M₂ / μ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2) := by
  rw [augSol_eq_update] at horth htr
  exact norm_preservation_of_le (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep hv.isNested hA hA0 hh
    (by rw [normal_leftProj_rightProj_apply]; exact hε) hsk horth htr hμ hY₀

/-- **Theorem 5.1 of arXiv 2403.02834, Variant 1, corrected** (matrix form): the statement of
`theorem_5_1_variant2` for the integrator of Sec. 3.1. -/
theorem theorem_5_1_variant1 {t₀ h ε ϑ : ℝ} {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ}
    {V₀ : Matrix n r ℝ} {Uh : Matrix m a ℝ} {Vh : Matrix n b ℝ} {Us : Matrix m e ℝ}
    {Vs : Matrix n f ℝ} {U₂ : Matrix m c ℝ} {V₂ : Matrix n d ℝ} {K : ℝ → Matrix m b ℝ}
    {Lf : ℝ → Matrix n a ℝ} {Sb : ℝ → Matrix a b ℝ} {A A₂ : ℝ → Matrix m n ℝ}
    (hv : IsVariant1 F t₀ h U₀ S₀ V₀ Uh Vh Us Vs U₂ V₂ K Lf Sb)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : IsC2Solution F A A₂ t₀ (t₀ + h) M₂) (hA0 : A t₀ = U₀ * S₀ * V₀ᵀ) (hh : 0 < h)
    (hε : ‖(1 - U₀ * U₀ᵀ) * F t₀ (U₀ * S₀ * V₀ᵀ) * (1 - V₀ * V₀ᵀ)‖ ≤ ε)
    (hsk : ∀ t Z, ⟪Z, F t Z⟫ = 0) {Y₁ : Matrix m n ℝ}
    (horth : ‖Y₁‖ ^ 2 + ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ^ 2 =
      ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h))‖ ^ 2)
    (htr : ‖augSol Uh U₂ Vh V₂ (Sb (t₀ + h)) (K (t₀ + h)) (Lf (t₀ + h)) - Y₁‖ ≤ ϑ) :
    |‖Y₁‖ - ‖U₀ * S₀ * V₀ᵀ‖| ≤ (ϑ ^ 2 + constNorm L B M₂ * (h ^ 4 + h ^ 3 * ε + h ^ 2 * ε ^ 2)) /
      (‖Y₁‖ + ‖U₀ * S₀ * V₀ᵀ‖) := by
  rw [augSol_eq_update] at horth htr
  exact norm_preservation (ε := ε) hF hL hB hv.toIsStep.isPreAugmented
    hv.toIsStep.isParallelBUGStep
    hv.isNested hA hA0 hh (by rw [normal_leftProj_rightProj_apply]; exact hε) hsk horth htr

/-- **Theorem 4.1 of arXiv 2403.02834, Variant 2** (matrix form, rank-adaptive).  Let `F` be
`L`-Lipschitz and bounded by `B`, `A' = F(t, A)` on `[t₀, t₀ + N h]`, `h > 0`.  For `k < N` let
step `k` (`tₖ = t₀ + k h`) start from `Yₖ = Uₖ Sₖ Vₖᵀ` of rank `rₖ` (`IsVariant2`), let the exact
flow `Φₖ` from `(tₖ, Yₖ)` satisfy `‖Φₖ''‖ ≤ M₂`, `‖Φₖ'''‖ ≤ M₃`, let the normal components be
bounded by `ε_r` at `Yₖ` and by `ε_2r` at the half step `Ŷ⋆ₖ`, and let `Yₖ₊₁` be a truncation of
`Ŷₖ₊₁ = Ûₖ Ŝₖ V̂ₖᵀ` with `‖Yₖ₊₁ - Ŷₖ₊₁‖ ≤ ϑ`.  If `‖Y₀ - A(t₀)‖ ≤ δ`, then for `k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ C₀ δ + C₁ h² + C₂ ε_2r + C₃ h ε_r + C₄ k ϑ

with `C₀ = C₄ = e^{LT}`, `C₁ = c T e^{LT}` (`c = constV2 L B M₂ M₃`), `C₂ = T e^{LT}`,
`C₃ = 3 L T e^{LT}`. -/
theorem theorem_4_1_variant2 {rk au av cu cv : ℕ → ℕ} {ε ε₂ ϑ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (hε0 : 0 ≤ ε) (hε₂0 : 0 ≤ ε₂) (hϑ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 < h)
    {N : ℕ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {Uh : (k : ℕ) → Matrix m (Fin (au k)) ℝ}
    {Vh : (k : ℕ) → Matrix n (Fin (av k)) ℝ} {U₂ : (k : ℕ) → Matrix m (Fin (cu k)) ℝ}
    {V₂ : (k : ℕ) → Matrix n (Fin (cv k)) ℝ} {K : (k : ℕ) → ℝ → Matrix m (Fin (av k)) ℝ}
    {Lf : (k : ℕ) → ℝ → Matrix n (Fin (au k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (au k)) (Fin (av k)) ℝ} {Φ Φ₂ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsVariant2 F (t₀ + k * h) (t₀ + k * h + h) (U k) (S k) (V k) (Uh k)
      (Vh k) (U₂ k) (V₂ k) (K k) (Lf k) (Sb k))
    (hΦ : ∀ k < N, IsRegularSolution F (Φ k) (Φ₂ k) (t₀ + k * h) (t₀ + k * h + h) M₂ M₃)
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ)
    (hε : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ) *
      (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hε₂ : ∀ k < N, ‖(1 - Uh k * (Uh k)ᵀ) * F (t₀ + k * h + h / 2) (Uh k * (Uh k)ᵀ *
      (U k * S k * (V k)ᵀ + (h / 2) • F (t₀ + k * h) (U k * S k * (V k)ᵀ)) *
        (Vh k * (Vh k)ᵀ)) * (1 - Vh k * (Vh k)ᵀ)‖ ≤ ε₂)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augSol (Uh k) (U₂ k) (Vh k) (V₂ k)
      (Sb k (t₀ + k * h + h)) (K k (t₀ + k * h + h)) (Lf k (t₀ + k * h + h))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * δ + constV2 L B M₂ M₃ * T * Real.exp (L * T) * h ^ 2 +
        T * Real.exp (L * T) * ε₂ + 3 * L * T * Real.exp (L * T) * (h * ε) +
          Real.exp (L * T) * (k * ϑ) := by
  intro k hk hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hc : 0 ≤ constV2 L B M₂ M₃ := by unfold constV2; positivity
  have hg : 0 ≤ 3 * L * h * ε + ε₂ + constV2 L B M₂ M₃ * h ^ 2 := by positivity
  have h1 := fan_le hF hL hh.le hA (Y := fun k => U k * S k * (V k)ᵀ) (Φ := Φ)
    (fun j hj => (hΦ j hj).sol) hΦ₀ hg hϑ (fun j hj => by
      have := theorem_4_5_variant2 (hstep j hj) hF hL hB (hΦ j hj) (hΦ₀ j hj) hh (hε j hj)
        (hε₂ j hj) (htr j hj)
      calc _ ≤ _ := this
        _ = h * (3 * L * h * ε + ε₂ + constV2 L B M₂ M₃ * h ^ 2) + ϑ := by ring) k hk hT
  have hexp := (Real.exp_pos (L * T)).le
  calc ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖
      ≤ Real.exp (L * T) * (‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ +
          T * (3 * L * h * ε + ε₂ + constV2 L B M₂ M₃ * h ^ 2) + k * ϑ) := h1
    _ ≤ Real.exp (L * T) * (δ + T * (3 * L * h * ε + ε₂ + constV2 L B M₂ M₃ * h ^ 2) +
          k * ϑ) := by gcongr
    _ = _ := by ring

/-- **Theorem 4.1 of arXiv 2403.02834, Variant 1** (matrix form, rank-adaptive).  Under the
hypotheses of `theorem_4_1_variant2` with Variant 1 steps (`IsVariant1`), the normal components
bounded by `ε_r` at the four rank-`r` points of `lemma_4_3_matrix` in every step, and
`0 < h ≤ h̄`, for `k h ≤ T`

    ‖Yₖ - A(tₖ)‖ ≤ C₀ δ + C₁ h² + C₂ ε_r + C₃ k ϑ

with `C₀ = C₃ = e^{LT}`, `C₁ = c T e^{LT}` (`c = constV1 L B M₂ M₃`),
`C₂ = (3 + 6 L h̄) T e^{LT}`. -/
theorem theorem_4_1_variant1 {rk au av cu cv eu ev : ℕ → ℕ} {ε ϑ hbar : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 ≤ M₃) (hε0 : 0 ≤ ε) (hϑ : 0 ≤ ϑ) {t₀ h : ℝ} (hh : 0 < h) (hhb : h ≤ hbar)
    {N : ℕ} {A : ℝ → Matrix m n ℝ} (hA : ODESolution F A t₀ (t₀ + N * h))
    {U : (k : ℕ) → Matrix m (Fin (rk k)) ℝ} {S : (k : ℕ) → Matrix (Fin (rk k)) (Fin (rk k)) ℝ}
    {V : (k : ℕ) → Matrix n (Fin (rk k)) ℝ} {Uh : (k : ℕ) → Matrix m (Fin (au k)) ℝ}
    {Vh : (k : ℕ) → Matrix n (Fin (av k)) ℝ} {Us : (k : ℕ) → Matrix m (Fin (eu k)) ℝ}
    {Vs : (k : ℕ) → Matrix n (Fin (ev k)) ℝ} {U₂ : (k : ℕ) → Matrix m (Fin (cu k)) ℝ}
    {V₂ : (k : ℕ) → Matrix n (Fin (cv k)) ℝ} {K : (k : ℕ) → ℝ → Matrix m (Fin (av k)) ℝ}
    {Lf : (k : ℕ) → ℝ → Matrix n (Fin (au k)) ℝ}
    {Sb : (k : ℕ) → ℝ → Matrix (Fin (au k)) (Fin (av k)) ℝ} {Φ Φ₂ : ℕ → ℝ → Matrix m n ℝ}
    (hstep : ∀ k < N, IsVariant1 F (t₀ + k * h) h (U k) (S k) (V k) (Uh k) (Vh k) (Us k)
      (Vs k) (U₂ k) (V₂ k) (K k) (Lf k) (Sb k))
    (hΦ : ∀ k < N, IsRegularSolution F (Φ k) (Φ₂ k) (t₀ + k * h) (t₀ + k * h + h) M₂ M₃)
    (hΦ₀ : ∀ k < N, Φ k (t₀ + k * h) = U k * S k * (V k)ᵀ)
    (hε : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ) *
      (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hK : ∀ k < N, ‖(1 - Us k * (Us k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ +
      (h / 2) • (F (t₀ + k * h) (U k * S k * (V k)ᵀ) * V k * (V k)ᵀ)) *
        (1 - V k * (V k)ᵀ)‖ ≤ ε)
    (hLn : ∀ k < N, ‖(1 - U k * (U k)ᵀ) * F (t₀ + k * h) (U k * S k * (V k)ᵀ +
      (h / 2) • (U k * (U k)ᵀ * F (t₀ + k * h) (U k * S k * (V k)ᵀ))) *
        (1 - Vs k * (Vs k)ᵀ)‖ ≤ ε)
    (hS : ∀ k < N, ‖(1 - Us k * (Us k)ᵀ) * F (t₀ + k * h + h / 2) (Us k * (Us k)ᵀ *
      (U k * S k * (V k)ᵀ + (h / 2) • F (t₀ + k * h) (Us k * (Us k)ᵀ * (U k * S k * (V k)ᵀ) *
        (Vs k * (Vs k)ᵀ))) * (Vs k * (Vs k)ᵀ)) * (1 - Vs k * (Vs k)ᵀ)‖ ≤ ε)
    (htr : ∀ k < N, ‖U (k + 1) * S (k + 1) * (V (k + 1))ᵀ - augSol (Uh k) (U₂ k) (Vh k) (V₂ k)
      (Sb k (t₀ + k * h + h)) (K k (t₀ + k * h + h)) (Lf k (t₀ + k * h + h))‖ ≤ ϑ)
    {δ T : ℝ} (hδ : ‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ ≤ δ) :
    ∀ k ≤ N, (k : ℝ) * h ≤ T → ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖ ≤
      Real.exp (L * T) * δ + constV1 L B M₂ M₃ * T * Real.exp (L * T) * h ^ 2 +
        (3 + 6 * L * hbar) * T * Real.exp (L * T) * ε + Real.exp (L * T) * (k * ϑ) := by
  intro k hk hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hc : 0 ≤ constV1 L B M₂ M₃ := by unfold constV1; positivity
  have hhb0 : 0 ≤ hbar := hh.le.trans hhb
  have hg : 0 ≤ (3 + 6 * L * hbar) * ε + constV1 L B M₂ M₃ * h ^ 2 := by positivity
  have h1 := fan_le hF hL hh.le hA (Y := fun k => U k * S k * (V k)ᵀ) (Φ := Φ)
    (fun j hj => (hΦ j hj).sol) hΦ₀ hg hϑ (fun j hj => by
      have := theorem_4_5_variant1 (hstep j hj) hF hL hB (hΦ j hj) (hΦ₀ j hj) hh hhb (hε j hj)
        (hK j hj) (hLn j hj) (hS j hj) (htr j hj)
      calc _ ≤ _ := this
        _ = h * ((3 + 6 * L * hbar) * ε + constV1 L B M₂ M₃ * h ^ 2) + ϑ := by ring) k hk hT
  have hexp := (Real.exp_pos (L * T)).le
  calc ‖U k * S k * (V k)ᵀ - A (t₀ + k * h)‖
      ≤ Real.exp (L * T) * (‖U 0 * S 0 * (V 0)ᵀ - A t₀‖ +
          T * ((3 + 6 * L * hbar) * ε + constV1 L B M₂ M₃ * h ^ 2) + k * ϑ) := h1
    _ ≤ Real.exp (L * T) * (δ + T * ((3 + 6 * L * hbar) * ε + constV1 L B M₂ M₃ * h ^ 2) +
          k * ϑ) := by gcongr
    _ = _ := by ring

end GlobalMatrix

end Matrices

/-! ## Theorem 5.1: the constant cannot be independent of the solution -/

section Counterexample

open scoped LeanDLRA.Frobenius
open Matrix (fromCols fromBlocks fromRows)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The radial retraction `x ↦ (s / max s ‖x‖) x` onto the ball of radius `s` is
`2`-Lipschitz. -/
theorem norm_radial_sub_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {s : ℝ}
    (hs : 0 < s) (x y : G) :
    ‖(s / max s ‖x‖) • x - (s / max s ‖y‖) • y‖ ≤ 2 * ‖x - y‖ := by
  wlog hxy : ‖y‖ ≤ ‖x‖ generalizing x y
  · rw [norm_sub_rev, norm_sub_rev x]
    exact this y x (not_le.1 hxy).le
  have hA : 0 < max s ‖x‖ := lt_of_lt_of_le hs (le_max_left _ _)
  have hB : 0 < max s ‖y‖ := lt_of_lt_of_le hs (le_max_left _ _)
  have hAB : max s ‖y‖ ≤ max s ‖x‖ := max_le_max le_rfl hxy
  have hd : max s ‖x‖ - max s ‖y‖ ≤ ‖x - y‖ := by
    have h1 := abs_max_sub_max_le_abs ‖x‖ ‖y‖ s
    rw [max_comm ‖x‖, max_comm ‖y‖] at h1
    have h2 := abs_norm_sub_norm_le x y
    linarith [le_abs_self (max s ‖x‖ - max s ‖y‖)]
  have e : (s / max s ‖x‖) • x - (s / max s ‖y‖) • y =
      (s / max s ‖x‖) • (x - y) + (s / max s ‖x‖ - s / max s ‖y‖) • y := by
    rw [smul_sub, sub_smul]; abel
  have hA' := hA.ne'
  have hB' := hB.ne'
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_nonneg hs.le hA.le)]
  have h1 : s / max s ‖x‖ ≤ 1 := (div_le_one hA).2 (le_max_left _ _)
  have h2 : ‖s / max s ‖x‖ - s / max s ‖y‖‖ * ‖y‖ ≤ max s ‖x‖ - max s ‖y‖ := by
    have e2 : s / max s ‖x‖ - s / max s ‖y‖ =
        -(s * (max s ‖x‖ - max s ‖y‖) / (max s ‖x‖ * max s ‖y‖)) := by
      field_simp
      ring
    rw [e2, norm_neg, Real.norm_of_nonneg (by
      have : 0 ≤ max s ‖x‖ - max s ‖y‖ := by linarith
      positivity), div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hy : ‖y‖ ≤ max s ‖y‖ := le_max_right _ _
    have hs' : s ≤ max s ‖x‖ := le_max_left _ _
    have h0 : 0 ≤ max s ‖x‖ - max s ‖y‖ := by linarith
    have h3 : s * ‖y‖ ≤ max s ‖x‖ * max s ‖y‖ := mul_le_mul hs' hy (norm_nonneg y) hA.le
    nlinarith [mul_le_mul_of_nonneg_left h3 h0]
  have h3 : s / max s ‖x‖ * ‖x - y‖ ≤ ‖x - y‖ := by
    have := norm_nonneg (x - y)
    nlinarith
  linarith

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
`e₁ ∈ ℝ²`. -/
def cxE1 : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then 1 else 0

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
`e₂ ∈ ℝ²`. -/
def cxE2 : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 1 then 1 else 0

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
`E₁₁ = e₁ e₁ᵀ`. -/
def cxE11 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
`W = (3/5) e₁ e₂ᵀ + (4/5) e₂ e₂ᵀ`, a unit matrix orthogonal to `E₁₁`. -/
noncomputable def cxW : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if j = 1 then (if i = 0 then 3 / 5 else 4 / 5) else 0

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The `1 × 1` matrix `(s)`, the coefficient matrix `S₀` of the counterexample. -/
def cxS0 (s : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => s

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The skew-symmetric linear map `Φ(Y) = Y₁₁ W - ⟨W, Y⟩ E₁₁` (a rotation in the plane spanned by
`E₁₁` and `W`). -/
noncomputable def cxPhi (Y : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Y 0 0 • cxW - (3 / 5 * Y 0 1 + 4 / 5 * Y 1 1) • cxE11

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The norm-conserving field of the counterexample, `F(t, Y) = Φ(ρₛ(Y))` with `ρₛ` the radial
retraction onto the ball of radius `s`: bounded by `s`, `2`-Lipschitz, and linear on the ball. -/
noncomputable def cxF (s : ℝ) (_t : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (s / max s ‖Y‖) • cxPhi Y

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The K-step (and exact) solution `s (cos t E₁₁ + sin t W)`. -/
noncomputable def cxK (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (s * Real.cos t) • cxE11 + (s * Real.sin t) • cxW

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The L-step solution `s (cos(3t/5) e₁ + sin(3t/5) e₂)`. -/
noncomputable def cxL (s t : ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  (s * Real.cos (3 / 5 * t)) • cxE1 + (s * Real.sin (3 / 5 * t)) • cxE2

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The S-step solution `S̄(t) = L(t)ᵀ`. -/
noncomputable def cxS (s t : ℝ) : Matrix (Fin 1) (Fin 2) ℝ := (cxL s t)ᵀ

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The second derivative of the exact solution. -/
noncomputable def cxA₂ (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (-(s * Real.cos t)) • cxE11 + (-(s * Real.sin t)) • cxW

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
No new right directions: `Ṽ₂` has zero columns. -/
def cxV2 : Matrix (Fin 2) (Fin 0) ℝ := 0

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxPhi_sub (Y Z : Matrix (Fin 2) (Fin 2) ℝ) : cxPhi (Y - Z) = cxPhi Y - cxPhi Z := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxPhi, cxW, cxE11] <;> ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxPhi_smul (c : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ) : cxPhi (c • Y) = c • cxPhi Y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxPhi, cxW, cxE11] <;> ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_cxPhi_le (Y : Matrix (Fin 2) (Fin 2) ℝ) : ‖cxPhi Y‖ ≤ ‖Y‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, cxPhi, cxW, cxE11]
  nlinarith [sq_nonneg (4 / 5 * Y 0 1 - 3 / 5 * Y 1 1), sq_nonneg (Y 1 0)]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem inner_cxPhi (Y : Matrix (Fin 2) (Fin 2) ℝ) : ⟪Y, cxPhi Y⟫ = 0 := by
  rw [Frobenius.inner_def]
  simp [Fin.sum_univ_two, cxPhi, cxW, cxE11]
  ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxF_lipschitz {s : ℝ} (hs : 0 < s) : IsLipschitzField (cxF s) 2 := fun t Y Z => by
  have e : cxF s t Y - cxF s t Z = cxPhi ((s / max s ‖Y‖) • Y - (s / max s ‖Z‖) • Z) := by
    change (s / max s ‖Y‖) • cxPhi Y - (s / max s ‖Z‖) • cxPhi Z = _
    rw [cxPhi_sub, cxPhi_smul, cxPhi_smul]
  rw [e]
  exact (norm_cxPhi_le _).trans (norm_radial_sub_le hs Y Z)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxF_bounded {s : ℝ} (hs : 0 < s) : IsBoundedField (cxF s) s := fun t Y => by
  have hA : 0 < max s ‖Y‖ := lt_of_lt_of_le hs (le_max_left _ _)
  rw [cxF, norm_smul, Real.norm_of_nonneg (div_nonneg hs.le hA.le), div_mul_eq_mul_div,
    div_le_iff₀ hA]
  exact mul_le_mul_of_nonneg_left ((norm_cxPhi_le Y).trans (le_max_right _ _)) hs.le

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxF_skew (s : ℝ) : ∀ t Z, ⟪Z, cxF s t Z⟫ = 0 := fun t Z => by
  rw [cxF, inner_smul_right, inner_cxPhi, mul_zero]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxF_of_norm {s : ℝ} (hs : 0 < s) (t : ℝ) {Y : Matrix (Fin 2) (Fin 2) ℝ}
    (hY : ‖Y‖ = s) : cxF s t Y = cxPhi Y := by
  rw [cxF, hY, max_self, div_self hs.ne', one_smul]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_cxK {s : ℝ} (hs : 0 < s) (t : ℝ) : ‖cxK s t‖ = s := by
  refine (sq_eq_sq₀ (norm_nonneg _) hs.le).1 ?_
  rw [Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, cxK, cxE11, cxW]
  linear_combination s ^ 2 * Real.sin_sq_add_cos_sq t

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
`F(t, K(t)) = K'(t)`. -/
theorem cxF_cxK {s : ℝ} (hs : 0 < s) (t : ℝ) :
    cxF s t (cxK s t) = (-(s * Real.sin t)) • cxE11 + (s * Real.cos t) • cxW := by
  rw [cxF_of_norm hs t (norm_cxK hs t)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxPhi, cxK, cxE11, cxW]
  all_goals ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem hasDerivAt_cxK (s t : ℝ) :
    HasDerivAt (cxK s) ((-(s * Real.sin t)) • cxE11 + (s * Real.cos t) • cxW) t := by
  exact ((((Real.hasDerivAt_cos t).const_mul s).smul_const cxE11).add
    (((Real.hasDerivAt_sin t).const_mul s).smul_const cxW)).congr_deriv (by simp)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem hasDerivAt_cxA₂ (s t : ℝ) :
    HasDerivAt (cxA₂ s) ((s * Real.sin t) • cxE11 + (-(s * Real.cos t)) • cxW) t := by
  exact ((((Real.hasDerivAt_cos t).const_mul s).neg.smul_const cxE11).add
    (((Real.hasDerivAt_sin t).const_mul s).neg.smul_const cxW)).congr_deriv (by simp)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem hasDerivAt_cxG (s t : ℝ) :
    HasDerivAt (fun u => (-(s * Real.sin u)) • cxE11 + (s * Real.cos u) • cxW) (cxA₂ s t) t := by
  exact ((((Real.hasDerivAt_sin t).const_mul s).neg.smul_const cxE11).add
    (((Real.hasDerivAt_cos t).const_mul s).smul_const cxW)).congr_deriv (by simp [cxA₂])

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_comb_le (x y : ℝ) : ‖x • cxE11 + y • cxW‖ ≤ |x| + |y| := by
  have h1 : ‖cxE11‖ = 1 := by
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two]
    simp [cxE11]
  have h2 : ‖cxW‖ = 1 := by
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 ?_
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two]
    simp [cxW]
    norm_num
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, h1, h2, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_trig_le {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    |s * Real.cos x| + |s * Real.sin y| ≤ 2 * s := by
  rw [abs_mul, abs_mul, abs_of_nonneg hs]
  nlinarith [Real.abs_cos_le_one x, Real.abs_sin_le_one y]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The exact solution of the counterexample has bounded second and third derivatives. -/
theorem cx_regular {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (h : ℝ) :
    IsRegularSolution (cxF s) (cxK s) (cxA₂ s) 0 h 2 2 := by
  have hG : (fun u => cxF s u (cxK s u)) =
      fun u => (-(s * Real.sin u)) • cxE11 + (s * Real.cos u) • cxW :=
    funext fun u => cxF_cxK hs u
  refine IsRegularSolution.of_third_deriv
    (A₃ := fun t => (s * Real.sin t) • cxE11 + (-(s * Real.cos t)) • cxW)
    (fun t _ => by rw [cxF_cxK hs]; exact hasDerivAt_cxK s t)
    (fun t _ => by rw [hG]; exact hasDerivAt_cxG s t)
    (fun t _ => hasDerivAt_cxA₂ s t) (fun t _ => ?_) (fun t _ => ?_)
  · refine (norm_comb_le _ _).trans ?_
    rw [abs_neg, abs_neg]
    linarith [norm_trig_le hs.le t t]
  · refine (norm_comb_le _ _).trans ?_
    rw [abs_neg]
    linarith [norm_trig_le hs.le t t]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
A solution given by a global derivative. -/
theorem odeSolution_of_hasDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G → G} {y : ℝ → G} {a b : ℝ} (hy : ∀ t, HasDerivAt y (g t (y t)) t) :
    ODESolution g y a b where
  cont := fun t _ => (hy t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hy t).hasDerivWithinAt

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxY₀ (s : ℝ) : cxE1 * cxS0 s * cxE1ᵀ = cxK s 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, cxS0, cxK, cxE11, cxW, Matrix.mul_apply]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cxF₀ {s : ℝ} (hs : 0 < s) : cxF s 0 (cxE1 * cxS0 s * cxE1ᵀ) = s • cxW := by
  rw [cxY₀, cxF_cxK hs]
  simp

/-- *arXiv 2403.02834, auxiliary.*
`L'(t)`. -/
theorem hasDerivAt_cxL (s t : ℝ) :
    HasDerivAt (cxL s) ((s * (-Real.sin (3 / 5 * t) * (3 / 5))) • cxE1 +
      (s * (Real.cos (3 / 5 * t) * (3 / 5))) • cxE2) t := by
  have hl : HasDerivAt (fun u : ℝ => 3 / 5 * u) (3 / 5) t := by
    simpa using (hasDerivAt_id t).const_mul (3 / 5 : ℝ)
  exact ((hl.cos.const_mul s).smul_const cxE1).add ((hl.sin.const_mul s).smul_const cxE2)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_cxYL {s : ℝ} (hs : 0 < s) (t : ℝ) : ‖cxE1 * (cxL s t)ᵀ‖ = s := by
  refine (sq_eq_sq₀ (norm_nonneg _) hs.le).1 ?_
  rw [Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two, cxE1, cxE2, cxL, Matrix.mul_apply]
  linear_combination s ^ 2 * Real.sin_sq_add_cos_sq (3 / 5 * t)

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cx_lField {s : ℝ} (hs : 0 < s) (t : ℝ) :
    MatrixKSL.lField cxE1 (cxF s) t (cxL s t) =
      (s * (-Real.sin (3 / 5 * t) * (3 / 5))) • cxE1 +
        (s * (Real.cos (3 / 5 * t) * (3 / 5))) • cxE2 := by
  rw [MatrixKSL.lField, cxF_of_norm hs t (norm_cxYL hs t)]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cxPhi, cxE1, cxE2, cxL, cxW, cxE11, Matrix.mul_apply] <;> ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cx_sField {s : ℝ} (hs : 0 < s) (t : ℝ) :
    sFieldAug cxE1 (1 : Matrix (Fin 2) (Fin 2) ℝ) (cxF s) t (cxS s t) =
      ((s * (-Real.sin (3 / 5 * t) * (3 / 5))) • cxE1 +
        (s * (Real.cos (3 / 5 * t) * (3 / 5))) • cxE2)ᵀ := by
  rw [← cx_lField hs t, sFieldAug, MatrixKSL.lField, cxS]
  simp [Matrix.transpose_mul]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem cx_kField {s : ℝ} (hs : 0 < s) (t : ℝ) :
    MatrixKSL.kField (1 : Matrix (Fin 2) (Fin 2) ℝ) (cxF s) t (cxK s t) =
      (-(s * Real.sin t)) • cxE11 + (s * Real.cos t) • cxW := by
  rw [MatrixKSL.kField, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, cxF_cxK hs]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
**The counterexample is a Variant 2 step** (and also a step of the first-order parallel
integrator): `U₀ = V₀ = e₁`, `S₀ = (s)`, `Û₀ = e₁ = orth([e₁, F₀ e₁])` (since `F₀ e₁ = 0`),
`V̂₀ = I = orth([e₁, F₀ᵀ e₁])`, `Û₁ = [e₁, e₂] = orth([e₁, K(h)])`, `V̂₁ = [I, ∅]`. -/
theorem cx_isVariant2 {s h : ℝ} (hs : 0 < s) (hsh : Real.sin h ≠ 0) :
    IsVariant2 (cxF s) 0 h cxE1 (cxS0 s) cxE1 cxE1 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxE2 cxV2
      (cxK s) (cxL s) (cxS s) where
  orthU₀ := by ext i j; fin_cases i; fin_cases j; simp [cxE1, Matrix.mul_apply]
  orthV₀ := by ext i j; fin_cases i; fin_cases j; simp [cxE1, Matrix.mul_apply]
  augU := by
    rw [cxF₀ hs]
    refine ⟨by ext i j; fin_cases i; fin_cases j; simp [cxE1, Matrix.mul_apply], ?_,
      ⟨fromRows 1 0, ?_⟩⟩
    · ext i j
      rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [cxE1, cxW, Matrix.mul_apply]
    · rw [Matrix.fromCols_mul_fromRows]
      ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, cxW]
  augV := by
    rw [cxF₀ hs]
    have hs0 := hs.ne'
    refine ⟨by simp, by simp, ⟨fromRows cxE1ᵀ ((5 / (3 * s)) • cxE2ᵀ), ?_⟩⟩
    rw [Matrix.fromCols_mul_fromRows]
    ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, cxE2, cxW, Matrix.mul_apply]
    all_goals field_simp
  kSol := odeSolution_of_hasDerivAt fun t => by rw [cx_kField hs]; exact hasDerivAt_cxK s t
  kStart := by rw [← cxY₀]; simp
  lSol := odeSolution_of_hasDerivAt fun t => by rw [cx_lField hs]; exact hasDerivAt_cxL s t
  lStart := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, cxE2, cxL, cxS0, Matrix.mul_apply]
  sSol := odeSolution_of_hasDerivAt fun t => by
    rw [cx_sField hs]; exact Frobenius.hasDerivAt_transpose (hasDerivAt_cxL s t)
  sStart := by
    ext i j; fin_cases i; fin_cases j <;> simp [cxE1, cxE2, cxS, cxL, cxS0, Matrix.mul_apply]
  newU := by
    have hP : fromCols cxE1 cxE2 * (fromCols cxE1 cxE2)ᵀ = 1 := by
      rw [matrix_augmented_proj]
      ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, cxE2, Matrix.mul_apply]
    refine ⟨?_, by rw [hP, Matrix.one_mul], ⟨fromBlocks (Matrix.of fun _ _ => 1)
      (Matrix.of fun _ _ => -3 / 4) 0
      (Matrix.of fun i _ => if i = 0 then 0 else 5 / (4 * (s * Real.sin h))), ?_⟩⟩
    · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
      have h11 : cxE1ᵀ * cxE1 = 1 := by
        ext i j; fin_cases i; fin_cases j; simp [cxE1, Matrix.mul_apply]
      have h12 : cxE1ᵀ * cxE2 = 0 := by
        ext i j; fin_cases i; fin_cases j; simp [cxE1, cxE2, Matrix.mul_apply]
      have h21 : cxE2ᵀ * cxE1 = 0 := by
        ext i j; fin_cases i; fin_cases j; simp [cxE1, cxE2, Matrix.mul_apply]
      have h22 : cxE2ᵀ * cxE2 = 1 := by
        ext i j; fin_cases i; fin_cases j; simp [cxE2, Matrix.mul_apply]
      rw [h11, h12, h21, h22, Matrix.fromBlocks_one]
    · rw [Matrix.fromCols_mul_fromBlocks]
      congr 1
      · ext i j; fin_cases i <;> fin_cases j <;> simp [cxE1, Matrix.mul_apply]
      · have hsh' : s * Real.sin h ≠ 0 := mul_ne_zero hs.ne' hsh
        have hs0 := hs.ne'
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [cxE1, cxE2, cxK, cxE11, cxW, Matrix.mul_apply, Fin.sum_univ_two]
        all_goals field_simp
        all_goals norm_num
  newV := by
    refine ⟨?_, ?_, ⟨fromBlocks 1 0 0 0, ?_⟩⟩
    · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
      simp only [cxV2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.transpose_zero]
      rw [show (0 : Matrix (Fin 0) (Fin 0) ℝ) = 1 from Subsingleton.elim _ _]
      exact Matrix.fromBlocks_one
    · rw [matrix_augmented_proj]
      simp [cxV2]
    · rw [Matrix.fromCols_mul_fromBlocks]
      simp [cxV2]

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.*
The untruncated result of the counterexample:
`Ŷ₁ = [[s cos(3h/5), s sin(3h/5)], [0, (4/5) s sin h]]`. -/
theorem cx_augSol (s h : ℝ) :
    augSol cxE1 cxE2 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxV2 (cxS s h) (cxK s h) (cxL s h) =
      Matrix.of fun i j => if i = 0 then (if j = 0 then s * Real.cos (3 / 5 * h)
        else s * Real.sin (3 / 5 * h)) else (if j = 0 then 0 else 4 / 5 * (s * Real.sin h)) := by
  rw [augSol_eq_sum]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cxE1, cxE2, cxS, cxL, cxK, cxE11, cxW, cxV2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- *arXiv 2403.02834, counterexample to Theorem 5.1.* An auxiliary computation. -/
theorem norm_sq_cx_augSol (s h : ℝ) :
    ‖augSol cxE1 cxE2 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxV2 (cxS s h) (cxK s h) (cxL s h)‖ ^ 2 =
      s ^ 2 * (1 + 16 / 25 * Real.sin h ^ 2) := by
  rw [cx_augSol, Frobenius.norm_sq_eq_sum]
  simp [Fin.sum_univ_two]
  linear_combination s ^ 2 * Real.sin_sq_add_cos_sq (3 / 5 * h)

/-- **Theorem 5.1 of arXiv 2403.02834 is false with a constant independent of the solution.**
The paper states `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ² / (‖Y₁‖ + ‖Y₀‖) + C (h⁴ + h³ ε_r + h² ε_r²)` with `C`
depending only on the Lipschitz constant and bound of `F`, bounds of derivatives of the exact
solution and an upper bound of `h`.  For every `C` there is an instance with `2 × 2` matrices,
rank `r = 1`, a norm-conserving field (`⟨Z, F(t, Z)⟩ = 0`) that is `2`-Lipschitz and bounded by
`s ≤ 1` (so every normal component is at most `ε_r = s`), an exact solution with
`‖A''‖, ‖A'''‖ ≤ 2`, `h ≤ 1`, no truncation (`Y₁ = Ŷ₁`, `ϑ = 0`), all hypotheses of
`theorem_5_1_variant2`, and
`C (h⁴ + h³ ε_r + h² ε_r²) < |‖Ŷ₁‖ - ‖Y₀‖|`.  It uses `‖Y₀‖ = s = h → 0`: the paper's proof
divides `c₃ (h⁴ + h³ ε_r + h² ε_r²)` by `‖Y₁‖ + ‖Y₀‖`, so its constant carries the factor
`1 / (‖Y₁‖ + ‖Y₀‖)` (see `theorem_5_1_variant2`, `theorem_5_1_variant2_of_le`). -/
theorem theorem_5_1_counterexample (C : ℝ) :
    ∃ s h : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 < h ∧ h ≤ 1 ∧
      IsLipschitzField (cxF s) 2 ∧ IsBoundedField (cxF s) s ∧ (∀ t Z, ⟪Z, cxF s t Z⟫ = 0) ∧
      IsVariant2 (cxF s) 0 (0 + h) cxE1 (cxS0 s) cxE1 cxE1 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxE2
        cxV2 (cxK s) (cxL s) (cxS s) ∧
      IsRegularSolution (cxF s) (cxK s) (cxA₂ s) 0 (0 + h) 2 2 ∧
      cxK s 0 = cxE1 * cxS0 s * cxE1ᵀ ∧
      ‖(1 - cxE1 * cxE1ᵀ) * cxF s 0 (cxE1 * cxS0 s * cxE1ᵀ) * (1 - cxE1 * cxE1ᵀ)‖ ≤ s ∧
      C * (h ^ 4 + h ^ 3 * s + h ^ 2 * s ^ 2) <
        |‖augSol cxE1 cxE2 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxV2 (cxS s (0 + h)) (cxK s (0 + h))
          (cxL s (0 + h))‖ - ‖cxE1 * cxS0 s * cxE1ᵀ‖| := by
  set h : ℝ := 1 / (100 * (|C| + 1)) with hdef
  have hC1 : 0 < |C| + 1 := by positivity
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 / 100 := by
    rw [hdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg C]
  have hhC : h * (|C| + 1) = 1 / 100 := by
    have := hC1.ne'
    rw [hdef]; field_simp
  have hsin : h / 2 ≤ Real.sin h := by
    have h1 := Real.sin_gt_sub_cube hh
    have h3 : h ^ 3 ≤ h := pow_le_of_le_one hh.le (by linarith) (by norm_num)
    linarith
  have hsin0 : Real.sin h ≠ 0 := (lt_of_lt_of_le (by positivity) hsin).ne'
  have hsin1 : Real.sin h ≤ 1 := Real.sin_le_one h
  have horth : cxE1ᵀ * cxE1 = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [cxE1, Matrix.mul_apply]
  refine ⟨h, h, hh, by linarith, hh, by linarith, cxF_lipschitz hh, cxF_bounded hh,
    cxF_skew h, by rw [zero_add]; exact cx_isVariant2 hh hsin0,
    cx_regular hh (by linarith) _, (cxY₀ h).symm, ?_, ?_⟩
  · rw [← normal_leftProj_rightProj_apply]
    exact (norm_normal_le (isOrthProj_leftProj horth) (isOrthProj_rightProj horth) _).trans
      (cxF_bounded hh _ _)
  · rw [zero_add, cxY₀, norm_cxK hh]
    set X := ‖augSol cxE1 cxE2 (1 : Matrix (Fin 2) (Fin 2) ℝ) cxV2 (cxS h h) (cxK h h)
      (cxL h h)‖ with hX
    have hX2 : X ^ 2 = h ^ 2 * (1 + 16 / 25 * Real.sin h ^ 2) := norm_sq_cx_augSol h h
    have hX0 : 0 ≤ X := norm_nonneg _
    set a := Real.sin h with ha
    have ha0 : 0 ≤ a := by linarith
    have hlow : h * (1 + 16 / 75 * a ^ 2) ≤ X := by
      refine (sq_le_sq₀ (mul_nonneg hh.le (by positivity)) hX0).1 ?_
      rw [hX2]
      have ha1 : a ^ 2 ≤ 1 := by nlinarith
      have : (h * (1 + 16 / 75 * a ^ 2)) ^ 2 =
          h ^ 2 * (1 + 32 / 75 * a ^ 2 + (16 / 75) ^ 2 * a ^ 4) := by ring
      rw [this]
      have h4 : a ^ 4 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
      nlinarith [sq_nonneg h, mul_le_mul_of_nonneg_left h4 (sq_nonneg h)]
    have hgain : 4 / 75 * h ^ 3 ≤ X - h := by
      have h5 : h / 2 * (h / 2) ≤ a ^ 2 := by
        rw [sq]; exact mul_le_mul hsin hsin (by linarith) ha0
      nlinarith [mul_le_mul_of_nonneg_left h5 hh.le]
    have hCb : C * (h ^ 4 + h ^ 3 * h + h ^ 2 * h ^ 2) ≤ 3 / 100 * h ^ 3 := by
      have e : h ^ 4 + h ^ 3 * h + h ^ 2 * h ^ 2 = 3 * h ^ 4 := by ring
      rw [e]
      have h1 : C * (3 * h ^ 4) ≤ |C| * (3 * h ^ 4) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      have h2 : |C| * (3 * h ^ 4) ≤ (|C| + 1) * (3 * h ^ 4) := by nlinarith [pow_pos hh 4]
      have h3 : (|C| + 1) * (3 * h ^ 4) = 3 * (h * (|C| + 1)) * h ^ 3 := by ring
      rw [h3, hhC] at h2
      linarith
    have hpos : 0 < h ^ 3 := pow_pos hh 3
    calc C * (h ^ 4 + h ^ 3 * h + h ^ 2 * h ^ 2) ≤ 3 / 100 * h ^ 3 := hCb
      _ < 4 / 75 * h ^ 3 := by linarith
      _ ≤ X - h := hgain
      _ ≤ |X - h| := le_abs_self _

/-- *arXiv 2403.02834, satisfiability of Sec. 3.1.*
The `1 × 1` matrix `(1)`. -/
def oneMat : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- *arXiv 2403.02834, satisfiability of Sec. 3.1.*
No new directions. -/
def noCols : Matrix (Fin 1) (Fin 0) ℝ := 0

/-- *arXiv 2403.02834, satisfiability of Sec. 3.1.* `(1) = 1`. -/
theorem oneMat_eq : oneMat = 1 := by
  ext i j; fin_cases i; fin_cases j; simp [oneMat]

/-- **Satisfiability of the Variant 1 hypotheses** (`F = 0`, `1 × 1` matrices, `h = 1`). -/
example : IsVariant1 (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) 0 1 oneMat oneMat oneMat
    oneMat oneMat oneMat oneMat noCols noCols (fun _ => oneMat) (fun _ => oneMat)
    (fun _ => oneMat) := by
  have hcols : ∀ X : Matrix (Fin 1) (Fin 1) ℝ,
      IsOrth (fromCols oneMat noCols) (fromCols oneMat X) := by
    intro X
    refine ⟨?_, ?_, ⟨fromBlocks 1 0 0 0, ?_⟩⟩
    · rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
      simp only [noCols, oneMat_eq, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.transpose_zero]
      rw [show (0 : Matrix (Fin 0) (Fin 0) ℝ) = 1 from Subsingleton.elim _ _]
      exact Matrix.fromBlocks_one
    · rw [matrix_augmented_proj]; simp [noCols, oneMat_eq]
    · rw [Matrix.fromCols_mul_fromBlocks]; simp [noCols]
  have hone : ∀ X : Matrix (Fin 1) (Fin 1) ℝ, X = oneMat → IsOrth oneMat X := by
    rintro X rfl
    exact ⟨by simp [oneMat_eq], by simp [oneMat_eq], ⟨1, by simp⟩⟩
  have hpair : IsOrth oneMat (fromCols oneMat (0 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨by simp [oneMat_eq], by simp [oneMat_eq], ⟨fromRows 1 0, by
      rw [Matrix.fromCols_mul_fromRows]; simp⟩⟩
  have hsol : ∀ (c : Matrix (Fin 1) (Fin 1) ℝ)
      (g : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ), (∀ t, g t c = 0) →
      ODESolution g (fun _ => c) 0 (0 + 1) := fun c g hg =>
    odeSolution_of_hasDerivAt fun t => by simpa [hg] using hasDerivAt_const t c
  exact
    { orthU₀ := by simp [oneMat_eq]
      orthV₀ := by simp [oneMat_eq]
      augU := by simpa using hpair
      augV := by simpa using hpair
      kSol := hsol _ _ fun t => by simp [MatrixKSL.kField]
      kStart := by simp [oneMat_eq]
      lSol := hsol _ _ fun t => by simp [MatrixKSL.lField]
      lStart := by simp [oneMat_eq]
      sSol := hsol _ _ fun t => by simp [sFieldAug]
      sStart := by simp [oneMat_eq]
      starU := hone _ (by simp [oneMat_eq])
      starV := hone _ (by simp [oneMat_eq])
      newU := hcols _
      newV := hcols _ }

end Counterexample

end LeanDLRA.Literature.P2403_02834
