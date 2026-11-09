import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import LeanDLRA.Foundations.ODE
import LeanDLRA.Literature.TensorNetworks.P2407_11792a

/-!
# Results of arXiv 2309.08252: Low-rank algorithm for the kinetic chemical master equation

Einkemmer, Mangott and Prugger. This module formalizes two results of the paper: conservation of
probability for the CME (Sec. 2) and the finite state projection bound it quotes (Sec. 4).

**Conservation of probability (Sec. 2, Eqs. (3)–(5), p. 3).** The CME (1) on `ℕ^N` has reactions
`μ` with stoichiometric vectors `ν_μ ∈ ℤ^N` and propensities `a_μ`. Its right-hand side is
`P2407_11792.cmeRHS`, reused from the module of arXiv 2407.11792 (same formula). The paper fixes
the boundary convention on p. 3: the gain arguments `x - ν_μ` are omitted when they become
negative, since no physical reaction can make a population negative, and `a_μ(x)` is read as
the transition probability `T_μ(x + ν_μ | x)`. As a condition on the propensities this says
`a_μ(x) = 0` whenever `x + ν_μ ∉ ℕ^N`: the predicate `IsNatPreserving`, which is exactly what the
index shift of Eq. (5) uses. We model the omission by extending `P` by zero outside `ℕ^d`
(`hP0`).

* `cme_gain_hasSum_nat` (one channel) and `cme_gain_eq_loss_nat`: Eq. (5).
* `cme_mass_conserved_nat`: the right-hand side of (4) vanishes, i.e. the CME right-hand side
  sums to zero over `ℕ^d`.

Differences from the paper: the sums in (5) are assumed to converge (`hsum`), which the paper takes
for granted; `a_μ` and `P` may be arbitrary real functions (non-negativity is not used); the time
integration from (4) to (3) on the infinite lattice is not formalized (for a finite chain it is
`fullSol_sum`). The remark `not_hasSum_cme_nat_without_hprop` shows that the propensity condition
cannot be dropped. It does not correct the paper, which assumes the condition.

**Finite state projection bound (Sec. 4, p. 7, the result of [43], Munsky and Khammash).** The
paper restricts the CME operator to a truncated state space `Ω` and takes `P^Ω` the solution of
the restricted CME started from the initial distribution restricted to `Ω`. If
`∑_{x ∈ Ω} P^Ω(t, x) ≥ 1 - ε`, then `P(t, x) - ε ≤ P^Ω(t, x) ≤ P(t, x)` for `x ∈ Ω`. We prove this
for a finite state space `S` with a generator `Q` (non-negative off-diagonal entries, zero column
sums; for a CME on `S` they say that no reaction leaves `S`, the analogue of the propensity
condition above), any finite `Ω ⊆ S` (the paper uses boxes) and any `ε`: `fsp_bounds` for the
matrix-exponential solutions and `fsp_bounds_of_odeSolution` for arbitrary solutions in the sense
of the core `ODESolution`. The
paper's state space `ℕ^N` is infinite, which needs infinite matrix exponentials and is not
formalized. The restricted operator `restrictGen` keeps the diagonal (outflow) entries on `Ω`, as
in [43]. Also proved: mass conservation `fullSol_sum`, Eq. (3) for a finite chain.

Core definitions used: `ODESolution` and `IsLipschitzField` (`LeanDLRA/Foundations/ODE.lean`),
and `cmeRHS` of `LeanDLRA/Literature/TensorNetworks/P2407_11792a.lean`. Local definitions:
`NatLattice` (`ℕ^d` inside `ℤ^d`), `IsNatPreserving`, `restrictGen`, `fullSol` and
`restrictedSol` (the library has no Markov-generator or matrix-exponential API), and the
matrix-exponential lemmas used in the proofs.

Not formalized: Sec. 3 (the projector-splitting equations (10)–(14) and the Lie–Trotter K, S and L
substeps (15)–(20)), the coefficient formulas (21)–(27), the Strang variant, Algorithms 1–2 of
Sec. 4 and the numerical experiments of Sec. 5, which are not theorems.
-/

open Finset
open scoped Matrix

namespace LeanDLRA.Literature.P2309_08252

open LeanDLRA.Literature.P2407_11792 (cmeRHS)

/-! ### Conservation of probability on `ℕ^N` (Eqs. (3)–(5)) -/

/-- The state space `ℕ^d`, as the points of `ℤ^d` with non-negative coordinates. -/
abbrev NatLattice (d : ℕ) := {x : Fin d → ℤ // ∀ i, 0 ≤ x i}

/-- The paper's propensity condition (arXiv 2309.08252, p. 3: no physical reaction can make a
population negative, and `a_μ(x)` is the transition probability `T_μ(x + ν_μ | x)`): every
channel `μ` has zero propensity at a state `x ∈ ℕ^d` with `x + ν_μ ∉ ℕ^d`. -/
def IsNatPreserving {d : ℕ} {R : Type*} (ν : R → Fin d → ℤ) (a : R → (Fin d → ℤ) → ℝ) : Prop :=
  ∀ μ (x : Fin d → ℤ), (∀ i, 0 ≤ x i) → (∃ i, x i + ν μ i < 0) → a μ x = 0

/-- A family on `ℤ^d` that vanishes off `ℕ^d` and is summable on `ℕ^d` is summable on `ℤ^d`. -/
private theorem summable_of_natLattice {d : ℕ} {g : (Fin d → ℤ) → ℝ}
    (hg0 : ∀ x : Fin d → ℤ, (∃ i, x i < 0) → g x = 0)
    (hg : Summable fun x : NatLattice d => g x.1) :
    Function.support g ⊆ {x | ∀ i, 0 ≤ x i} ∧ Summable g := by
  have hsupp : Function.support g ⊆ {x | ∀ i, 0 ≤ x i} := by
    intro y hy
    by_contra hneg
    have hneg' : ¬ ∀ i, 0 ≤ y i := hneg
    simp only [not_forall, not_le] at hneg'
    exact hy (hg0 y hneg')
  have h := (summable_subtype_iff_indicator (s := {x : Fin d → ℤ | ∀ i, 0 ≤ x i}) (f := g)).mp hg
  rw [Set.indicator_eq_self.mpr hsupp] at h
  exact ⟨hsupp, h⟩

/-- One channel of Eq. (5), for a flux `g = a_μ P` that vanishes off `ℕ^d` and at every state
of `ℕ^d` that the shift `v = ν_μ` would leave: the shifted (gain) sum over `ℕ^d` equals the
unshifted (loss) sum. -/
private theorem hasSum_gain_natLattice {d : ℕ} (v : Fin d → ℤ) {g : (Fin d → ℤ) → ℝ}
    (hg0 : ∀ x : Fin d → ℤ, (∃ i, x i < 0) → g x = 0)
    (hg : Summable fun x : NatLattice d => g x.1)
    (hflux : ∀ x : Fin d → ℤ, (∀ i, 0 ≤ x i) → (∃ i, x i + v i < 0) → g x = 0) :
    HasSum (fun x : NatLattice d => g (x.1 - v)) (∑' x : NatLattice d, g x.1) := by
  obtain ⟨hsuppg, hgZ⟩ := summable_of_natLattice hg0 hg
  have h1 : HasSum (fun x => g (x - v)) (∑' x, g x) :=
    (Equiv.subRight v).hasSum_iff.mpr hgZ.hasSum
  have hsupp : Function.support (fun x => g (x - v)) ⊆ {x | ∀ i, 0 ≤ x i} := by
    intro x hx
    by_contra hneg
    have hneg' : ¬ ∀ i, 0 ≤ x i := hneg
    simp only [not_forall, not_le] at hneg'
    obtain ⟨i0, hi0⟩ := hneg'
    apply hx
    by_cases hy : ∀ i, 0 ≤ (x - v) i
    · exact hflux (x - v) hy ⟨i0, by rw [Pi.sub_apply, sub_add_cancel]; exact hi0⟩
    · simp only [not_forall, not_le] at hy
      exact hg0 _ hy
  have h2 := (hasSum_subtype_iff_of_support_subset hsupp).mpr h1
  rwa [← tsum_subtype_eq_of_support_subset hsuppg] at h2

/-- **Eq. (5), one reaction channel** (arXiv 2309.08252). Let `P` be a distribution on `ℕ^d`,
extended by zero to `ℤ^d` (`hP0`; this omits the gain terms with `x - ν_μ ∉ ℕ^d`, as on p. 3),
let the loss series of channel `μ` be summable (`hsum`), and let the propensities satisfy the
paper's condition `IsNatPreserving`. Then `∑_{x ∈ ℕ^d} a_μ(x - ν_μ) P(x - ν_μ)` converges to
`∑_{x ∈ ℕ^d} a_μ(x) P(x)`. -/
theorem cme_gain_hasSum_nat {d : ℕ} {R : Type*} (ν : R → Fin d → ℤ)
    (a : R → (Fin d → ℤ) → ℝ) (P : (Fin d → ℤ) → ℝ)
    (hP0 : ∀ x : Fin d → ℤ, (∃ i, x i < 0) → P x = 0) (μ : R)
    (hsum : Summable (fun x : NatLattice d => a μ x.1 * P x.1))
    (hprop : IsNatPreserving ν a) :
    HasSum (fun x : NatLattice d => a μ (x.1 - ν μ) * P (x.1 - ν μ))
      (∑' x : NatLattice d, a μ x.1 * P x.1) :=
  hasSum_gain_natLattice (ν μ) (g := fun y => a μ y * P y)
    (fun x hx => by simp only [hP0 x hx, mul_zero]) hsum
    (fun x hx hneg => by simp only [hprop μ x hx hneg, zero_mul])

/-- **Eq. (5)** (arXiv 2309.08252): under the paper's propensity condition `IsNatPreserving`, for
a distribution `P` on `ℕ^d` extended by zero (`hP0`) with summable loss series (`hsum`),
`∑_μ ∑_{x ∈ ℕ^d} a_μ(x - ν_μ) P(x - ν_μ) = ∑_μ ∑_{x ∈ ℕ^d} a_μ(x) P(x)`. -/
theorem cme_gain_eq_loss_nat {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ)
    (a : R → (Fin d → ℤ) → ℝ) (P : (Fin d → ℤ) → ℝ)
    (hP0 : ∀ x : Fin d → ℤ, (∃ i, x i < 0) → P x = 0)
    (hsum : ∀ μ, Summable (fun x : NatLattice d => a μ x.1 * P x.1))
    (hprop : IsNatPreserving ν a) :
    ∑ μ, ∑' x : NatLattice d, a μ (x.1 - ν μ) * P (x.1 - ν μ) =
      ∑ μ, ∑' x : NatLattice d, a μ x.1 * P x.1 :=
  Finset.sum_congr rfl fun μ _ => (cme_gain_hasSum_nat ν a P hP0 μ (hsum μ) hprop).tsum_eq

/-- **Eqs. (3)–(5), conservation of probability** (arXiv 2309.08252), on `ℕ^d` with the paper's
convention: a distribution `P` on `ℕ^d` is extended by zero to `ℤ^d` (`hP0`), so a gain term
`a_μ(x - ν_μ) P(x - ν_μ)` with `x - ν_μ ∉ ℕ^d` is omitted, and the propensities satisfy the
paper's condition `IsNatPreserving` (p. 3). With the loss series summable (`hsum`), the CME
right-hand side sums to zero over `ℕ^d`: the right-hand side of (4) vanishes, so `∑ P` is a linear
invariant. The time integration from (4) to (3) is not formalized. -/
theorem cme_mass_conserved_nat {d : ℕ} {R : Type*} [Fintype R] (ν : R → Fin d → ℤ)
    (a : R → (Fin d → ℤ) → ℝ) (P : (Fin d → ℤ) → ℝ)
    (hP0 : ∀ x : Fin d → ℤ, (∃ i, x i < 0) → P x = 0)
    (hsum : ∀ μ, Summable (fun x : NatLattice d => a μ x.1 * P x.1))
    (hprop : IsNatPreserving ν a) :
    HasSum (fun x : NatLattice d => cmeRHS ν a P x.1) 0 := by
  have hterm : ∀ μ, HasSum (fun x : NatLattice d =>
      a μ (x.1 - ν μ) * P (x.1 - ν μ) - a μ x.1 * P x.1) 0 := fun μ => by
    simpa using (cme_gain_hasSum_nat ν a P hP0 μ (hsum μ) hprop).sub (hsum μ).hasSum
  have h := hasSum_sum (s := (Finset.univ : Finset R)) (fun μ _ => hterm μ)
  rw [Finset.sum_const_zero] at h
  exact h

/-- Non-vacuity: the hypotheses of `cme_mass_conserved_nat` hold for the decay reaction
`x ↦ x - 1` with propensity `x` (zero at the boundary) applied to the point mass at `1`. -/
example : HasSum (fun x : NatLattice 1 =>
      cmeRHS (d := 1) (fun _ : Unit => (![-1] : Fin 1 → ℤ))
        (fun _ x => ((x 0 : ℤ) : ℝ)) (fun y => if y = ![1] then 1 else 0) x.1) 0 := by
  apply cme_mass_conserved_nat
  · intro x hx
    obtain ⟨i, hi⟩ := hx
    have hne : x ≠ ![1] := by
      rintro rfl
      obtain rfl : i = 0 := Subsingleton.elim _ _
      norm_num at hi
    simp [hne]
  · intro μ
    refine summable_of_ne_finset_zero (s := {⟨![1], fun i => by simp⟩}) ?_
    intro x hx
    have hne : x.1 ≠ ![1] := fun h => hx (Finset.mem_singleton.mpr (Subtype.ext h))
    simp [hne]
  · intro μ x hx hneg
    obtain ⟨i, hi⟩ := hneg
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hx 0
    simp at hi
    simp only [Int.cast_eq_zero]
    omega

/-- The decay channel `x ↦ x - 1` with constant propensity `1` violates the paper's propensity
condition: it fires at `x = 0`. -/
theorem not_isNatPreserving_const_decay :
    ¬ IsNatPreserving (d := 1) (fun _ : Unit => (![-1] : Fin 1 → ℤ)) (fun _ _ => (1 : ℝ)) :=
  fun h => one_ne_zero (h () 0 (fun _ => le_rfl) ⟨0, by simp⟩)

/-- **Remark (not a claim of the paper): the propensity condition is needed.** The paper assumes
on p. 3 that no reaction makes a population negative (`IsNatPreserving`). Without it the
conservation identity fails: for the decay channel `x ↦ x - 1` with constant propensity `1`
(`not_isNatPreserving_const_decay`) and the point mass at `0`, the CME right-hand side sums to
`-1` over `ℕ`. On `ℤ` it sums to `0` (`P2407_11792.cme_mass_conserved`); the lost mass sits at
the state `-1`. -/
theorem not_hasSum_cme_nat_without_hprop :
    ¬ HasSum (fun x : NatLattice 1 =>
      cmeRHS (d := 1) (fun _ : Unit => (![-1] : Fin 1 → ℤ))
        (fun _ _ => (1 : ℝ)) (fun y => if y = 0 then 1 else 0) x.1) 0 := by
  intro h
  let b : NatLattice 1 := ⟨0, fun i => by simp⟩
  have hF : (fun x : NatLattice 1 =>
      cmeRHS (d := 1) (fun _ : Unit => (![-1] : Fin 1 → ℤ))
        (fun _ _ => (1 : ℝ)) (fun y => if y = 0 then 1 else 0) x.1) =
      fun x => if x = b then (-1 : ℝ) else 0 := by
    funext x
    obtain ⟨x, hx⟩ := x
    have hx0 : ∀ i, 0 ≤ x i := hx
    have hgain : x - ![-1] ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
      have := hx0 0
      omega
    by_cases hxz : x = 0
    · subst hxz
      simp [cmeRHS, b]
    · simp [cmeRHS, b, hxz]
      have h0 : 0 ≤ Matrix.vecHead x := hx0 0
      omega
  rw [hF] at h
  have h3 := h.unique (hasSum_ite_eq b (-1 : ℝ))
  norm_num at h3

/-- The remark's distribution on `ℤ`: there the CME right-hand side does sum to zero
(`P2407_11792.cme_mass_conserved`, finitely supported `P`, arbitrary propensities). -/
example : HasSum (cmeRHS (d := 1) (fun _ : Unit => (![-1] : Fin 1 → ℤ))
    (fun _ _ => (1 : ℝ)) (fun y => if y = 0 then 1 else 0)) 0 := by
  apply LeanDLRA.Literature.P2407_11792.cme_mass_conserved
  refine (Set.finite_singleton (0 : Fin 1 → ℤ)).subset ?_
  intro x hx
  by_contra h
  exact hx (ite_eq_right_iff.mpr fun h' => absurd h' h)

/-! ### Finite state projection on a finite state space (Sec. 4) -/

section FSP

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Restriction of a generator to `Ω × Ω`, with zero rows and columns outside `Ω`. This is the
operator `A^Ω` of the restricted CME, acting on functions on `S` that vanish outside `Ω`. -/
noncomputable def restrictGen (Q : Matrix S S ℝ) (Ω : Finset S) : Matrix S S ℝ :=
  Matrix.of fun i j => if i ∈ Ω ∧ j ∈ Ω then Q i j else 0

/-- The solution `P(t) = exp(tQ) P0` of the master equation `∂_t P = Q P`
(`odeSolution_fullSol`). -/
noncomputable def fullSol (Q : Matrix S S ℝ) (P0 : S → ℝ) (t : ℝ) : S → ℝ :=
  Matrix.mulVec (NormedSpace.exp (t • Q)) P0

/-- The solution `P^Ω(t) = exp(t A^Ω) (P0 · 1_Ω)` of the restricted (finite state projection) CME,
extended by zero outside `Ω` (`odeSolution_restrictedSol`). -/
noncomputable def restrictedSol (Q : Matrix S S ℝ) (Ω : Finset S) (P0 : S → ℝ) (t : ℝ) : S → ℝ :=
  Matrix.mulVec (NormedSpace.exp (t • restrictGen Q Ω)) (fun x => if x ∈ Ω then P0 x else 0)

/-- The restricted solution is the full solution for the restricted generator. -/
theorem restrictedSol_eq_fullSol (Q : Matrix S S ℝ) (Ω : Finset S) (P0 : S → ℝ) :
    restrictedSol Q Ω P0 = fullSol (restrictGen Q Ω) (fun x => if x ∈ Ω then P0 x else 0) :=
  rfl

theorem fullSol_zero (Q : Matrix S S ℝ) (P0 : S → ℝ) : fullSol Q P0 0 = P0 := by
  simp [fullSol]

/-- `t ↦ exp(tQ) P0` has derivative `Q exp(tQ) P0`. -/
theorem hasDerivAt_fullSol (Q : Matrix S S ℝ) (P0 : S → ℝ) (t : ℝ) :
    HasDerivAt (fullSol Q P0) (Q *ᵥ fullSol Q P0 t) t := by
  let _ := Matrix.linftyOpNormedRing (n := S) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := S) (R := ℝ) (α := ℝ)
  have : CompleteSpace (Matrix S S ℝ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Q t
  let L : Matrix S S ℝ →L[ℝ] (S → ℝ) := LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ P0
      map_add' := fun M N => Matrix.add_mulVec M N P0
      map_smul' := fun c M => Matrix.smul_mulVec c M P0 }
  have h2 := L.hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fullSol Q P0) ((Q * NormedSpace.exp (t • Q)) *ᵥ P0) t := h2
  rwa [← Matrix.mulVec_mulVec] at h3

/-- `P(t) = exp(tQ) P0` solves the master equation `∂_t P = Q P` (core `ODESolution`). -/
theorem odeSolution_fullSol (Q : Matrix S S ℝ) (P0 : S → ℝ) (a b : ℝ) :
    ODESolution (fun _ p => Q *ᵥ p) (fullSol Q P0) a b where
  cont := fun t _ => (hasDerivAt_fullSol Q P0 t).continuousAt.continuousWithinAt
  deriv := fun t _ => (hasDerivAt_fullSol Q P0 t).hasDerivWithinAt

/-- `P^Ω(t)` solves the restricted CME `∂_t P^Ω = A^Ω P^Ω` (core `ODESolution`). -/
theorem odeSolution_restrictedSol (Q : Matrix S S ℝ) (Ω : Finset S) (P0 : S → ℝ) (a b : ℝ) :
    ODESolution (fun _ p => restrictGen Q Ω *ᵥ p) (restrictedSol Q Ω P0) a b :=
  odeSolution_fullSol _ _ a b

/-- The linear field `p ↦ Q p` is Lipschitz (core `IsLipschitzField`), with the operator norm of
`Q` for the sup norm. -/
theorem isLipschitzField_mulVec (Q : Matrix S S ℝ) :
    IsLipschitzField (fun (_ : ℝ) (p : S → ℝ) => Q *ᵥ p)
      ‖(Matrix.toLin' Q).toContinuousLinearMap‖ := by
  intro t x y
  have := ((Matrix.toLin' Q).toContinuousLinearMap).le_opNorm (x - y)
  simpa [Matrix.mulVec_sub] using this

/-- Matrix exponential series, with the scalar normed structure supplied locally. -/
theorem hasSum_exp_series (A : Matrix S S ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) (NormedSpace.exp A) := by
  let _ := Matrix.linftyOpNormedRing (n := S) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (n := S) (R := ℝ) (α := ℝ)
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A

/-- Entrywise form of the exponential series. -/
theorem hasSum_exp_entry (A : Matrix S S ℝ) (t : ℝ) (i j : S) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (t ^ n * (A ^ n) i j))
      (NormedSpace.exp (t • A) i j) := by
  have h := Pi.hasSum.mp (Pi.hasSum.mp (hasSum_exp_series (t • A)) i) j
  convert h using 1
  funext n
  simp [smul_pow]

/-- Powers of an entrywise non-negative matrix are entrywise non-negative. -/
theorem pow_apply_nonneg {A : Matrix S S ℝ} (hA : ∀ i j, 0 ≤ A i j) (n : ℕ) (i j : S) :
    0 ≤ (A ^ n) i j := by
  induction n generalizing i j with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hA k j)

/-- `exp(tA)` is entrywise non-negative for an entrywise non-negative `A` and `t ≥ 0`. -/
theorem exp_apply_nonneg {A : Matrix S S ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (i j : S) : 0 ≤ NormedSpace.exp (t • A) i j :=
  hasSum_le (f := fun _ : ℕ => (0 : ℝ))
    (fun n => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (pow_nonneg ht n) (pow_apply_nonneg hA n i j)))
    hasSum_zero (hasSum_exp_entry A t i j)

/-- Entrywise comparison of powers, restricted to `Ω`: if `N = M` on `Ω × Ω` and `N` vanishes in
the rows outside `Ω` for columns in `Ω`, then `(N^n) ≤ (M^n)` on `Ω × Ω`. -/
theorem pow_restrict_le {M N : Matrix S S ℝ} (hM : ∀ i j, 0 ≤ M i j) (Ω : Finset S)
    (hNM : ∀ i ∈ Ω, ∀ j ∈ Ω, N i j = M i j)
    (hNout : ∀ k j, k ∉ Ω → j ∈ Ω → N k j = 0) :
    ∀ n : ℕ, ∀ i ∈ Ω, ∀ j ∈ Ω, (N ^ n) i j ≤ (M ^ n) i j := by
  intro n
  induction n with
  | zero => intro i _ j _; simp
  | succ n ih =>
    intro i hi j hj
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k ∈ Ω
    · rw [hNM k hk j hj]
      exact mul_le_mul_of_nonneg_right (ih i hi k hk) (hM k j)
    · rw [hNout k j hk hj, mul_zero]
      exact mul_nonneg (pow_apply_nonneg hM n i k) (hM k j)

/-- Entrywise comparison of exponentials from entrywise comparison of all powers, for `t ≥ 0`. -/
theorem exp_apply_le_of_pow_le {M N : Matrix S S ℝ} {t : ℝ} (ht : 0 ≤ t)
    (i j : S) (hpow : ∀ n : ℕ, (N ^ n) i j ≤ (M ^ n) i j) :
    NormedSpace.exp (t • N) i j ≤ NormedSpace.exp (t • M) i j :=
  hasSum_le (fun n => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hpow n) (pow_nonneg ht n))
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (hasSum_exp_entry N t i j) (hasSum_exp_entry M t i j)

/-- Scalar shift: `exp(A + s 1) = e^s exp(A)`. -/
theorem exp_add_smul_one (A : Matrix S S ℝ) (s : ℝ) :
    NormedSpace.exp (A + s • (1 : Matrix S S ℝ)) = Real.exp s • NormedSpace.exp A := by
  rw [Matrix.exp_add_of_commute _ _ ((Commute.one_right A).smul_right s)]
  have h1 : NormedSpace.exp (s • (1 : Matrix S S ℝ)) = Real.exp s • (1 : Matrix S S ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp]
    exact (congrFun Real.exp_eq_exp_ℝ s).symm
  rw [h1, mul_smul_comm, mul_one]

/-- `exp(tX) = e^{-tc} exp(t (X + c 1))`. -/
theorem exp_eq_shift (X : Matrix S S ℝ) (t c : ℝ) :
    NormedSpace.exp (t • X) =
      Real.exp (-(t * c)) • NormedSpace.exp (t • (X + c • (1 : Matrix S S ℝ))) := by
  have h : t • X = t • (X + c • (1 : Matrix S S ℝ)) + (-(t * c)) • (1 : Matrix S S ℝ) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  rw [h, exp_add_smul_one]

omit [Fintype S] in
/-- A generator shifted by `c ≥ max |Q i j|` is entrywise non-negative. -/
theorem shift_nonneg (Q : Matrix S S ℝ) (hQoff : ∀ i j, i ≠ j → 0 ≤ Q i j) {c : ℝ}
    (hc : ∀ i j, |Q i j| ≤ c) : ∀ k l, 0 ≤ (Q + c • (1 : Matrix S S ℝ)) k l := by
  intro k l
  by_cases hkl : k = l
  · subst hkl
    have h1 := neg_abs_le (Q k k)
    have h2 := hc k k
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linarith
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hkl, smul_eq_mul,
      mul_zero, add_zero]
    exact hQoff k l hkl

/-- Comparison: for `i, j ∈ Ω`, the restricted propagator is below the full one. -/
theorem exp_restrict_le (Q : Matrix S S ℝ) (hQoff : ∀ i j, i ≠ j → 0 ≤ Q i j) {c : ℝ}
    (hc : ∀ i j, |Q i j| ≤ c) (Ω : Finset S) {t : ℝ} (ht : 0 ≤ t) {i j : S} (hi : i ∈ Ω)
    (hj : j ∈ Ω) :
    NormedSpace.exp (t • restrictGen Q Ω) i j ≤ NormedSpace.exp (t • Q) i j := by
  have hM := shift_nonneg Q hQoff hc
  have hNM : ∀ k ∈ Ω, ∀ l ∈ Ω, (restrictGen Q Ω + c • (1 : Matrix S S ℝ)) k l =
      (Q + c • (1 : Matrix S S ℝ)) k l := by
    intro k hk l hl
    simp [restrictGen, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, hk, hl]
  have hNout : ∀ k l, k ∉ Ω → l ∈ Ω →
      (restrictGen Q Ω + c • (1 : Matrix S S ℝ)) k l = 0 := by
    intro k l hk hl
    have hkl : k ≠ l := fun h => hk (h ▸ hl)
    simp [restrictGen, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hkl,
      Matrix.of_apply, hk]
  have hpow := pow_restrict_le hM Ω hNM hNout
  have hcmp := exp_apply_le_of_pow_le ht i j (fun n => hpow n i hi j hj)
  rw [exp_eq_shift (restrictGen Q Ω) t c, exp_eq_shift Q t c]
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hcmp (Real.exp_pos _).le

/-- `exp(tQ)` is entrywise non-negative for a generator `Q` and `t ≥ 0`. -/
theorem exp_full_nonneg (Q : Matrix S S ℝ) (hQoff : ∀ i j, i ≠ j → 0 ≤ Q i j) {c : ℝ}
    (hc : ∀ i j, |Q i j| ≤ c) {t : ℝ} (ht : 0 ≤ t) (i j : S) :
    0 ≤ NormedSpace.exp (t • Q) i j := by
  rw [exp_eq_shift Q t c]
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_apply_nonneg (shift_nonneg Q hQoff hc) ht i j)

/-- Column sums of the powers of a generator with zero column sums vanish for `n ≥ 1`. -/
theorem colsum_pow (Q : Matrix S S ℝ) (hQcol : ∀ j, ∑ i, Q i j = 0) :
    ∀ n : ℕ, ∀ j, ∑ k, (Q ^ (n + 1)) k j = 0 := by
  intro n
  induction n with
  | zero => intro j; simpa using hQcol j
  | succ n ih =>
    intro j
    simp only [pow_succ Q (n + 1), Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ih, zero_mul, Finset.sum_const_zero]

/-- Column sums of `exp(tQ)` equal one when `Q` has zero column sums (mass conservation). -/
theorem colsum_exp (Q : Matrix S S ℝ) (hQcol : ∀ j, ∑ i, Q i j = 0) (t : ℝ) (j : S) :
    ∑ k, NormedSpace.exp (t • Q) k j = 1 := by
  have hS := hasSum_sum (s := (Finset.univ : Finset S)) (fun k _ => hasSum_exp_entry Q t k j)
  have hfun : (fun n : ℕ => ∑ k, (n.factorial : ℝ)⁻¹ * (t ^ n * (Q ^ n) k j)) =
      fun n => if n = 0 then (1 : ℝ) else 0 := by
    funext n
    cases n with
    | zero => simp [Matrix.one_apply]
    | succ m =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have hc : ∑ k, ((m + 1).factorial : ℝ)⁻¹ * (t ^ (m + 1) * (Q ^ (m + 1)) k j) =
          ((m + 1).factorial : ℝ)⁻¹ * t ^ (m + 1) * ∑ k, (Q ^ (m + 1)) k j := by
        simp [Finset.mul_sum, mul_assoc]
      rw [hc, colsum_pow Q hQcol m j, mul_zero]
  rw [hfun] at hS
  exact hS.unique (hasSum_ite_eq (0 : ℕ) (1 : ℝ))

/-- **Eq. (3) for a finite chain** (arXiv 2309.08252): if `Q` has zero column sums, the solution
of `∂_t P = Q P` conserves mass, `∑_x P(t, x) = ∑_x P0(x)`. -/
theorem fullSol_sum (Q : Matrix S S ℝ) (hQcol : ∀ j, ∑ i, Q i j = 0) (P0 : S → ℝ) (t : ℝ) :
    ∑ x, fullSol Q P0 t x = ∑ x, P0 x := by
  simp only [fullSol, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, colsum_exp Q hQcol t, one_mul]

/-- **Finite state projection bound** (arXiv 2309.08252, Sec. 4, p. 7, the bound of [43], for a
finite state space). Generator `Q` with non-negative off-diagonal entries and zero column sums,
initial probability vector `P0`, time `t ≥ 0`, and a finite set `Ω`. If the restricted CME keeps
mass at least `1 - ε` on `Ω`, then for every `x ∈ Ω`: `P(t, x) - ε ≤ P^Ω(t, x) ≤ P(t, x)`. Here
`P` and `P^Ω` are the matrix-exponential solutions; `fsp_bounds_of_odeSolution` states it for
arbitrary solutions. The paper's state space `ℕ^N` is infinite; this is the finite case. -/
theorem fsp_bounds (Q : Matrix S S ℝ) (hQoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (hQcol : ∀ j, ∑ i, Q i j = 0) (P0 : S → ℝ) (hP0 : ∀ x, 0 ≤ P0 x)
    (hP0sum : ∑ x, P0 x = 1) (Ω : Finset S) {t : ℝ} (ht : 0 ≤ t) (ε : ℝ)
    (hmass : 1 - ε ≤ ∑ y ∈ Ω, restrictedSol Q Ω P0 t y) :
    ∀ x ∈ Ω, fullSol Q P0 t x - ε ≤ restrictedSol Q Ω P0 t x ∧
      restrictedSol Q Ω P0 t x ≤ fullSol Q P0 t x := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ i j, |Q i j| ≤ c :=
    ⟨∑ k, ∑ l, |Q k l|, fun i j =>
      le_trans (Finset.single_le_sum (f := fun l => |Q i l|) (fun l _ => abs_nonneg _)
          (Finset.mem_univ j))
        (Finset.single_le_sum (f := fun k => ∑ l, |Q k l|)
          (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i))⟩
  have hfull_nonneg : ∀ x, 0 ≤ fullSol Q P0 t x := fun x =>
    Finset.sum_nonneg fun j _ => mul_nonneg (exp_full_nonneg Q hQoff hc ht x j) (hP0 j)
  have hfull_sum : ∑ x, fullSol Q P0 t x = 1 := by
    rw [fullSol_sum Q hQcol P0 t, hP0sum]
  have hres_le : ∀ x ∈ Ω, restrictedSol Q Ω P0 t x ≤ fullSol Q P0 t x := by
    intro x hx
    simp only [restrictedSol, fullSol, Matrix.mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ Ω
    · simp only [hj, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right (exp_restrict_le Q hQoff hc Ω ht hx hj) (hP0 j)
    · simp only [hj, ↓reduceIte, mul_zero]
      exact mul_nonneg (exp_full_nonneg Q hQoff hc ht x j) (hP0 j)
  intro x hx
  have hD : fullSol Q P0 t x - restrictedSol Q Ω P0 t x ≤
      ∑ y ∈ Ω, (fullSol Q P0 t y - restrictedSol Q Ω P0 t y) :=
    Finset.single_le_sum (f := fun y => fullSol Q P0 t y - restrictedSol Q Ω P0 t y)
      (fun y hy => sub_nonneg.mpr (hres_le y hy)) hx
  rw [Finset.sum_sub_distrib] at hD
  have hΩfull : ∑ y ∈ Ω, fullSol Q P0 t y ≤ 1 := by
    rw [← hfull_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ω)
      (fun y _ _ => hfull_nonneg y)
  exact ⟨by linarith, hres_le x hx⟩

/-- **Finite state projection bound, as stated in the paper** (arXiv 2309.08252, Sec. 4, p. 7,
the bound of [43], for a finite state space `S`). `P` is any solution on `[0, T]` of the CME
`∂_t P = Q P` with `P(0) = P0`, and `P^Ω` any solution of the restricted CME `∂_t P^Ω = A^Ω P^Ω`
with `P^Ω(0) = P0 · 1_Ω`, the initial distribution restricted to `Ω` (solutions in the sense of
the core `ODESolution`). `Q` has non-negative off-diagonal entries and zero column sums and `P0`
is a probability vector. If `∑_{y ∈ Ω} P^Ω(t, y) ≥ 1 - ε` at some `t ∈ [0, T]`, then
`P(t, x) - ε ≤ P^Ω(t, x) ≤ P(t, x)` for every `x ∈ Ω`. Differences from the paper: `S` is finite
(the paper's `ℕ^N` is not), `Ω` is any finite subset (the paper uses boxes), and `ε` is any real
number. -/
theorem fsp_bounds_of_odeSolution (Q : Matrix S S ℝ) (hQoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (hQcol : ∀ j, ∑ i, Q i j = 0) (P0 : S → ℝ) (hP0 : ∀ x, 0 ≤ P0 x)
    (hP0sum : ∑ x, P0 x = 1) (Ω : Finset S) {T : ℝ} {P PΩ : ℝ → S → ℝ}
    (hP : ODESolution (fun _ p => Q *ᵥ p) P 0 T) (hPinit : P 0 = P0)
    (hPΩ : ODESolution (fun _ p => restrictGen Q Ω *ᵥ p) PΩ 0 T)
    (hPΩinit : PΩ 0 = fun x => if x ∈ Ω then P0 x else 0)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (ε : ℝ) (hmass : 1 - ε ≤ ∑ y ∈ Ω, PΩ t y) :
    ∀ x ∈ Ω, P t x - ε ≤ PΩ t x ∧ PΩ t x ≤ P t x := by
  have hPeq : P t = fullSol Q P0 t :=
    hP.eqOn (odeSolution_fullSol Q P0 0 T) (isLipschitzField_mulVec Q) (norm_nonneg _)
      (by rw [hPinit, fullSol_zero]) ht
  have hPΩeq : PΩ t = restrictedSol Q Ω P0 t :=
    hPΩ.eqOn (odeSolution_restrictedSol Q Ω P0 0 T) (isLipschitzField_mulVec _) (norm_nonneg _)
      (by rw [hPΩinit, restrictedSol_eq_fullSol, fullSol_zero]) ht
  rw [hPeq, hPΩeq]
  rw [hPΩeq] at hmass
  exact fsp_bounds Q hQoff hQcol P0 hP0 hP0sum Ω ht.1 ε hmass

/-- The generator of a two-state chain (zero column sums, non-negative off-diagonal entries). -/
noncomputable def exampleQ : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; 1, -1]

/-- The initial distribution `(1, 0)`. -/
def exampleP0 : Fin 2 → ℝ := ![1, 0]

theorem exampleQ_off : ∀ i j : Fin 2, i ≠ j → 0 ≤ exampleQ i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [exampleQ]

theorem exampleQ_col : ∀ j : Fin 2, ∑ i, exampleQ i j = 0 := by
  intro j
  fin_cases j <;> simp [exampleQ, Fin.sum_univ_two]

theorem exampleP0_nonneg : ∀ x, 0 ≤ exampleP0 x := by
  intro x
  fin_cases x <;> simp [exampleP0]

theorem exampleP0_sum : ∑ x, exampleP0 x = 1 := by
  simp [exampleP0, Fin.sum_univ_two]

/-- Non-vacuity of `fsp_bounds`: the two-state chain, `Ω = {0}`, `t = 1` and
`ε = 1 - P^Ω`-mass. -/
example : ∃ ε : ℝ, 1 - ε ≤ ∑ y ∈ ({0} : Finset (Fin 2)), restrictedSol exampleQ {0} exampleP0 1 y ∧
    ∀ x ∈ ({0} : Finset (Fin 2)),
      fullSol exampleQ exampleP0 1 x - ε ≤ restrictedSol exampleQ {0} exampleP0 1 x ∧
        restrictedSol exampleQ {0} exampleP0 1 x ≤ fullSol exampleQ exampleP0 1 x := by
  refine ⟨1 - ∑ y ∈ ({0} : Finset (Fin 2)), restrictedSol exampleQ {0} exampleP0 1 y,
    le_of_eq (by ring), ?_⟩
  exact fsp_bounds exampleQ exampleQ_off exampleQ_col exampleP0 exampleP0_nonneg exampleP0_sum
    {0} (by norm_num) _ (le_of_eq (by ring))

/-- Non-vacuity of `fsp_bounds_of_odeSolution`: the matrix-exponential solutions of the two-state
chain satisfy its hypotheses on `[0, 1]`. -/
example : ∀ x ∈ ({0} : Finset (Fin 2)),
    fullSol exampleQ exampleP0 1 x -
        (1 - ∑ y ∈ ({0} : Finset (Fin 2)), restrictedSol exampleQ {0} exampleP0 1 y) ≤
      restrictedSol exampleQ {0} exampleP0 1 x ∧
    restrictedSol exampleQ {0} exampleP0 1 x ≤ fullSol exampleQ exampleP0 1 x :=
  fsp_bounds_of_odeSolution exampleQ exampleQ_off exampleQ_col exampleP0 exampleP0_nonneg
    exampleP0_sum {0} (odeSolution_fullSol _ _ 0 1) (fullSol_zero _ _)
    (odeSolution_restrictedSol _ _ _ 0 1)
    (by rw [restrictedSol_eq_fullSol, fullSol_zero]) ⟨zero_le_one, le_rfl⟩ _ (le_of_eq (by ring))

end FSP

end LeanDLRA.Literature.P2309_08252
