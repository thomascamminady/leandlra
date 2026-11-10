import LeanDLRA.Foundations.Localization

/-!
# Fields conjugated by continuous linear maps

A low-rank integrator does not solve the differential equation `Y' = F(t, Y)` for the full
unknown `Y`. Each of its substeps solves a differential equation for one factor of the low-rank
approximation while the other factors are kept fixed. The right-hand side of such a factor
equation is obtained from `F` in three moves: the factor `x` is mapped to a full-size state
`Φ x`, the field `F` is evaluated there, and the result is mapped back to the space of the
factor by `Ψ`. A field of this form,

`f t x = Ψ (F t (Φ x))` with continuous linear maps `Φ : E' → E` and `Ψ : E → E'`,

is called a **conjugated field** here. The space `E` is that of the full unknown, the space `E'`
that of the factor. This file collects what holds for every conjugated field, without reference
to matrices: it inherits a Lipschitz constant and a bound from `F`, so its differential equation
has a solution for every initial value, and `Φ` carries a solution for the factor to a
trajectory in the full space that solves a projected differential equation.

## Why the fields of the K-, L- and S-step have this form

One step of the BUG integrator [CerutiLubich2022, §3.1] for a matrix `Y = U S Vᵀ` solves three
factor equations.

* K-step. The unknown is `K = U S`, the basis `V₀` is fixed: `K' = F(t, K V₀ᵀ) V₀`. Here
  `Φ K = K V₀ᵀ` and `Ψ Z = Z V₀`.
* L-step. The unknown is `L = V Sᵀ`, the basis `U₀` is fixed: `L' = F(t, U₀ Lᵀ)ᵀ U₀`. Here
  `Φ L = U₀ Lᵀ` and `Ψ Z = Zᵀ U₀`.
* S-step. The unknown is `S`, the new bases `U₁`, `V₁` are fixed: `S' = U₁ᵀ F(t, U₁ S V₁ᵀ) V₁`.
  Here `Φ S = U₁ S V₁ᵀ` and `Ψ Z = U₁ᵀ Z V₁`.

In each case the unknown factor enters the full matrix linearly, because the other factors are
fixed, and the value of `F` is multiplied by the fixed bases, which is linear as well. The
substeps of the projector-splitting integrator and of the parallel BUG integrator have the same
form with other fixed bases; in the S-step of the projector-splitting integrator, which runs
with the opposite sign, the minus sign is part of `Ψ`.

## Main results

* `MatrixBUG.odeSolution_comp_clm`: a continuous linear map `Φ` that intertwines two fields,
  `g t (Φ x) = Φ (f t x)`, maps solutions of `y' = f(t, y)` to solutions of `z' = g(t, z)`. For
  a conjugated field `f` and the projected field `g t z = Φ (Ψ (F t z))` this carries a solution
  `x` for the factor to the trajectory `t ↦ Φ (x t)` in the full space. For the K-step it is
  `K(t) V₀ᵀ`, a solution of `Y' = F(t, Y) V₀ V₀ᵀ`.
* `MatrixBUG.isLipschitzField_conj`, `MatrixBUG.isBoundedField_conj`: if `F` is Lipschitz with
  constant `L ≥ 0`, the conjugated field is Lipschitz with constant `‖Ψ‖ L ‖Φ‖`; if `F` is
  bounded by `B`, the conjugated field is bounded by `‖Ψ‖ B`.
* `MatrixBUG.exists_odeSolution_conj`: if `F` is Lipschitz, bounded and continuous in time, the
  differential equation of a conjugated field has a solution on `[a, b]` for every initial
  value.
* `MatrixBUG.exists_odeSolution_conj_of_lipschitz`: the same for a field `F` that is Lipschitz
  and continuous in time on `[a, b]` and need not be bounded, for example a linear field.

## Implementation notes

The declarations are in the namespace `MatrixBUG`, under the names by which the matrix
integrators refer to them. Nothing in this file depends on matrices.

`exists_odeSolution_conj_of_lipschitz` asks for an inner product on the space `E'` of the
factor, because the existence theorem for Lipschitz fields without a bound,
`exists_ODESolution_of_linearGrowth`, is stated for such spaces.

## References

* [CerutiLubich2022]
-/

open Set

namespace LeanDLRA

namespace MatrixBUG

/-! ### Solutions, Lipschitz constants and bounds under conjugation -/

section Conj

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- **Lifting a solution.**  If a continuous linear map `Φ` intertwines two vector fields,
`g t (Φ x) = Φ (f t x)`, then it maps solutions of `y' = f(t, y)` to solutions of
`z' = g(t, z)` (derivative transfer through `Φ`).  With `Φ K = K V₀ᵀ`, `Φ L = U₀ Lᵀ` and
`Φ S = U₁ S V₁ᵀ` this lifts the factor ODEs of the BUG integrator to the full-space trajectories
of the abstract theory. -/
theorem odeSolution_comp_clm {f : ℝ → E → E} {g : ℝ → E' → E'} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution f y a b) (Φ : E →L[ℝ] E') (h : ∀ t x, g t (Φ x) = Φ (f t x)) :
    ODESolution g (fun t => Φ (y t)) a b where
  cont := Φ.continuous.comp_continuousOn hy.cont
  deriv t ht := by
    rw [h]
    exact Φ.hasFDerivAt.comp_hasDerivWithinAt t (hy.deriv t ht)

/-- Conjugating an `L`-Lipschitz field (`L ≥ 0`) by continuous linear maps,
`x ↦ Ψ (F t (Φ x))`, gives a field with Lipschitz constant `‖Ψ‖ L ‖Φ‖`. -/
theorem isLipschitzField_conj {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    IsLipschitzField (fun t x => Ψ (F t (Φ x))) (‖Ψ‖ * L * ‖Φ‖) := fun t x y => by
  calc ‖Ψ (F t (Φ x)) - Ψ (F t (Φ y))‖ = ‖Ψ (F t (Φ x) - F t (Φ y))‖ := by rw [map_sub]
    _ ≤ ‖Ψ‖ * ‖F t (Φ x) - F t (Φ y)‖ := Ψ.le_opNorm _
    _ ≤ ‖Ψ‖ * (L * ‖Φ (x - y)‖) := by
        rw [map_sub]
        exact mul_le_mul_of_nonneg_left (hF t _ _) (norm_nonneg _)
    _ ≤ ‖Ψ‖ * (L * (‖Φ‖ * ‖x - y‖)) := by
        gcongr
        exact Φ.le_opNorm _
    _ = ‖Ψ‖ * L * ‖Φ‖ * ‖x - y‖ := by ring

/-- Conjugating a field bounded by `B` gives a field bounded by `‖Ψ‖ B`. -/
theorem isBoundedField_conj {F : ℝ → E → E} {B : ℝ} (hB : IsBoundedField F B)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') :
    IsBoundedField (fun t x => Ψ (F t (Φ x))) (‖Ψ‖ * B) := fun t _ =>
  (Ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB t _) (norm_nonneg _))

/-- **Existence for conjugated fields.**  If `F` is Lipschitz, bounded and continuous in time,
every field of the form `f t x = Ψ (F t (Φ x))` (the K-, L- and S-step factor fields) has a
solution on `[a, b]` with arbitrary initial value. -/
theorem exists_odeSolution_conj [CompleteSpace E'] {F : ℝ → E → E} {L B : ℝ}
    (hF : IsLipschitzField F L) (hB : IsBoundedField F B) (hc : ∀ x, Continuous fun t => F t x)
    (Φ : E' →L[ℝ] E) (Ψ : E →L[ℝ] E') {f : ℝ → E' → E'} (hf : ∀ t x, f t x = Ψ (F t (Φ x)))
    {a b : ℝ} (hab : a ≤ b) (y₀ : E') : ∃ y : ℝ → E', ODESolution f y a b ∧ y a = y₀ := by
  have hfe : f = fun t x => Ψ (F t (Φ x)) := funext fun t => funext fun x => hf t x
  subst hfe
  have hF' : IsLipschitzField F (max L 0) := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  exact exists_ODESolution (isLipschitzField_conj hF' (le_max_right _ _) Φ Ψ)
    (isBoundedField_conj hB Φ Ψ) (fun x => Ψ.continuous.comp (hc (Φ x))) hab y₀

end Conj

/-! ### Existence without a bound on the field -/

section Lipschitz

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [InnerProductSpace ℝ E'] [CompleteSpace E']

/-- **Existence for conjugated Lipschitz fields.** If `F` is Lipschitz and continuous in time on
`[a, b]`, every field of the form `f t x = Ψ (F t (Φ x))` with continuous linear maps `Φ`, `Ψ`
(the fields of the K-, L- and S-step of the BUG integrator have this form) has a solution on
`[a, b]` with arbitrary initial value. In contrast to `exists_odeSolution_conj` the field need
not be bounded. -/
theorem exists_odeSolution_conj_of_lipschitz {F : ℝ → E → E} {L : ℝ} (hF : IsLipschitzField F L)
    {a b : ℝ} (hc : ∀ x, ContinuousOn (fun t => F t x) (Icc a b)) (Φ : E' →L[ℝ] E)
    (Ψ : E →L[ℝ] E') {f : ℝ → E' → E'} (hf : ∀ t x, f t x = Ψ (F t (Φ x))) (hab : a ≤ b)
    (y₀ : E') : ∃ y : ℝ → E', ODESolution f y a b ∧ y a = y₀ := by
  obtain rfl : f = fun t x => Ψ (F t (Φ x)) := funext fun t => funext fun x => hf t x
  have hF' : IsLipschitzField F (max L 0) := fun t x y =>
    (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hcΨ : ∀ x, ContinuousOn (fun t => Ψ (F t (Φ x))) (Icc a b) := fun x =>
    Ψ.continuous.comp_continuousOn (hc (Φ x))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn (hcΨ 0)
  exact exists_ODESolution_of_linearGrowth (isLipschitzField_conj hF' (le_max_right _ _) Φ Ψ)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (norm_nonneg _)) hK hcΨ hab y₀

end Lipschitz

end MatrixBUG

end LeanDLRA
