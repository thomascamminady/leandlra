import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2407.11792: Hierarchical DLRA for chemical master equation

This module formalizes the conservation of probability for the chemical master equation (CME)
(paper Eqs. (3)–(5)). The CME on the lattice `ℤ^d` has reactions `μ` with stoichiometric vectors
`ν μ` and propensities `a μ`; its right-hand side at state `x` is
`∑_μ (a_μ(x - ν_μ) P(x - ν_μ) - a_μ(x) P(x))`. For every finitely supported distribution `P`
the right-hand side sums to zero over `x`, so the total probability `∑ P` is a linear invariant
of the CME. This is the re-indexing `x ↦ x + ν_μ` in the paper. The theorem `cme_mass_conserved`
states this as `HasSum` (summability is part of the claim). The propensities are arbitrary real
functions, and the result is for the infinite lattice.

Not formalized: the finite state projection bound (cited, not projector-based) and the
Algorithm 1 PSI and Sec. 4.2 and Algorithms 2–5 results. Their statements need Metzler-flow
comparison, Kronecker-structured operator algebra and the TTN bookkeeping, which are not in
the library. They are left out, not weakened.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2407_11792

/-- The CME right-hand side at state `x`: `∑_μ (a_μ(x - ν_μ) P(x - ν_μ) - a_μ(x) P(x))`
for reactions `μ` with stoichiometric vector `ν μ ∈ ℤ^d` and propensity `a μ`. -/
def cmeRHS {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ) (a : R → (Fin d → ℤ) → ℝ)
    (P : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ μ, (a μ (x - ν μ) * P (x - ν μ) - a μ x * P x)

private theorem hasSum_shift_sub {d : ℕ} {g : (Fin d → ℤ) → ℝ} (hg : Summable g) (v : Fin d → ℤ) :
    HasSum (fun x => g (x - v) - g x) 0 := by
  have h1 : HasSum (fun x => g (x - v)) (∑' x, g x) :=
    (Equiv.subRight v).hasSum_iff.mpr hg.hasSum
  simpa using h1.sub hg.hasSum

/-- **Eqs. (3)–(5), conservation of probability** (arXiv 2407.11792). For a finitely supported
distribution `P` on `ℤ^d`, the CME right-hand side `cmeRHS ν a P` has total sum zero. Hence
`∑_x P(t, x)` is conserved by the CME: the gain and loss terms cancel after re-indexing
`x ↦ x + ν_μ`. Arbitrary propensities `a μ : ℤ^d → ℝ` are allowed. -/
theorem cme_mass_conserved {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ)
    (a : R → (Fin d → ℤ) → ℝ) {P : (Fin d → ℤ) → ℝ} (hP : (Function.support P).Finite) :
    HasSum (cmeRHS ν a P) 0 := by
  have hsum : ∀ μ, Summable (fun x => a μ x * P x) := fun μ => by
    refine summable_of_ne_finset_zero (s := hP.toFinset) fun x hx => ?_
    have hPx : P x = 0 := by
      by_contra h
      exact hx (hP.mem_toFinset.mpr h)
    rw [hPx, mul_zero]
  have hterm : ∀ μ, HasSum (fun x => a μ (x - ν μ) * P (x - ν μ) - a μ x * P x) 0 :=
    fun μ => hasSum_shift_sub (g := fun x => a μ x * P x) (hsum μ) (ν μ)
  have h := hasSum_sum (s := (univ : Finset R)) (fun μ (_ : μ ∈ (univ : Finset R)) => hterm μ)
  rw [Finset.sum_const_zero] at h
  exact h

/-- Non-vacuity: a single reaction with `ν = 1` and constant propensity `1`, applied to the point
mass at `0`. -/
example : HasSum (cmeRHS (d := 1) (fun _ : Unit => (![1] : Fin 1 → ℤ)) (fun _ _ => (1 : ℝ))
    (fun x => if x = 0 then 1 else 0)) 0 := by
  apply cme_mass_conserved
  refine (Set.finite_singleton (0 : Fin 1 → ℤ)).subset ?_
  intro x hx
  by_contra h
  exact hx (ite_eq_right_iff.mpr fun h' => absurd h' h)

end LeanDLRA.Literature.P2407_11792
