import LeanDLRA.Analysis.Defs

/-!
# Definitions: the DLRA problem and normal-component bounds

The vocabulary of layer 4 (`DLRA/`). Dynamical low-rank approximation replaces the solution `A`
of `y' = F(t, y)` by an approximation `Y` that is confined to a set of low-rank states, for
example `Y(t) = U(t) S(t) V(t)ᵀ` with `r` columns in `U` and `V`. The error estimates of the
field compare `Y` with `A` and depend on two kinds of hypotheses: conditions on `F` near the
reference solution `A` (a Lipschitz constant `L` and a bound `B` of `F` on a tube around `A`),
collected in `DLRAProblem`, and the size `ε` of the part of `F` that the low-rank approximation
cannot follow (the normal component), `NormalBoundOn`.

## Main definitions

* `LeanDLRA.DLRAProblem F A a b ρ L B`: `A` solves `y' = F(t, y)` on `[a, b]`, and `F` is
  `L`-Lipschitz and bounded by `B` on the tube of radius `ρ` around `A`.
* `LeanDLRA.NormalBoundOn F 𝒯 D ε`: `‖(1 - P) ((1 - Q) F(t, Y))‖ ≤ ε` for every admissible triple
  `(P, Q, Y) ∈ 𝒯` (left projector, right projector, point) with `(t, Y) ∈ D`.

## Main results

* `LeanDLRA.DLRAProblem.of_global`: global Lipschitz and boundedness conditions give a DLRA
  problem on every tube; `LeanDLRA.DLRAProblem.mono`: smaller interval and radius.
* `LeanDLRA.dlraProblem_iff`: the bundle in terms of the region conditions
  `IsLipschitzFieldOn`, `IsBoundedFieldOn` on `tubeSet A a b ρ`.
* `LeanDLRA.normalBoundOn_singleton_iff`: for one triple and the region `s ×ˢ {Y}` the bound is
  the pointwise hypothesis `∀ t ∈ s, ‖(1 - P) ((1 - Q) (F t Y))‖ ≤ ε` of the step structures
  (fields `kNormal`, `lNormal`).

The matrix form of the normal bound (`FactoredNormalBoundOn`, with `P = U Uᵀ`, `Q = V Vᵀ`,
`Y = U S Vᵀ`) and its bridge to `NormalBoundOn` are in `LeanDLRA/Integrators/Matrix/Defs.lean`.

## Implementation notes

The constants of `DLRAProblem` are explicit parameters, so that they can appear in conclusions.
Their nonnegativity is part of the bundle (fields `L_nonneg`, `B_nonneg`): `0 ≤ B` does not
follow from the other fields when the tube is empty (`ρ < 0`).

`NormalBoundOn` takes a set of admissible triples instead of a projector-valued function of the
point, because at rank-deficient points the tangent projector is not determined by the point:
every factorization `Y = U S Vᵀ` gives its own pair `(U Uᵀ, V Vᵀ)`.

## References

* [ZhaoOstermannGu2021, Property 1(b)] (conditions on a tube)
* [CerutiLubich2022, Thm. 2] (normal-component assumption)
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

/-! ### The problem bundle -/

section Problem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **DLRA problem** on the time interval `[a, b]`, posed around a reference solution: `A` is an
exact solution of `y' = F(t, y)` on `[a, b]`, and on the tube of radius `ρ` around `A`
(the states `x` with `‖x - A t‖ ≤ ρ` at time `t ∈ [a, b]`) the field `F` is Lipschitz in the
state with constant `L` and bounded by `B`. The error bounds of low-rank integrators need these
constants only near the reference solution, where the approximation stays; global conditions are
the special case `DLRAProblem.of_global`, valid for every radius `ρ`. Fields with a source term
or a linear part are DLRA problems on bounded tubes (see the `example` below). -/
structure DLRAProblem (F : ℝ → E → E) (A : ℝ → E) (a b ρ L B : ℝ) : Prop where
  /-- `A` solves `y' = F(t, y)` on `[a, b]`. -/
  sol : ODESolution F A a b
  /-- The Lipschitz constant is nonnegative. -/
  L_nonneg : 0 ≤ L
  /-- The bound is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `F` is `L`-Lipschitz in the state on the tube of radius `ρ` around `A`. -/
  lipschitz : IsLipschitzOnTube F A a b ρ L
  /-- `F` is bounded by `B` on the tube of radius `ρ` around `A`. -/
  bounded : IsBoundedOnTube F A a b ρ B

variable {F : ℝ → E → E} {A : ℝ → E} {a b a' b' ρ ρ' L B : ℝ}

/-- Global conditions: a globally `L`-Lipschitz field bounded by `B` with an exact solution `A`
is a DLRA problem on the tube of every radius `ρ` around `A`. (`0 ≤ B` follows from the bound at
the state `0`.) -/
theorem DLRAProblem.of_global (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (hA : ODESolution F A a b) (ρ : ℝ) : DLRAProblem F A a b ρ L B :=
  ⟨hA, hL, (norm_nonneg _).trans (hB a 0), fun t _ x y _ _ => hF t x y, fun t _ x _ => hB t x⟩

/-- A DLRA problem restricts to a smaller time interval and a smaller tube. -/
theorem DLRAProblem.mono (hP : DLRAProblem F A a b ρ L B) (ha : a ≤ a') (hb : b' ≤ b)
    (hρ : ρ' ≤ ρ) : DLRAProblem F A a' b' ρ' L B where
  sol := ⟨hP.sol.cont.mono (Icc_subset_Icc ha hb),
    fun t ht => hP.sol.deriv t ⟨ha.trans ht.1, ht.2.trans_le hb⟩⟩
  L_nonneg := hP.L_nonneg
  B_nonneg := hP.B_nonneg
  lipschitz t ht x y hx hy :=
    hP.lipschitz t (Icc_subset_Icc ha hb ht) x y (hx.trans hρ) (hy.trans hρ)
  bounded t ht x hx := hP.bounded t (Icc_subset_Icc ha hb ht) x (hx.trans hρ)

/-- The bundle in terms of the region conditions of `LeanDLRA/Analysis/Defs.lean` on the tube
`tubeSet A a b ρ`. -/
theorem dlraProblem_iff :
    DLRAProblem F A a b ρ L B ↔ ODESolution F A a b ∧ 0 ≤ L ∧ 0 ≤ B ∧
      IsLipschitzFieldOn F (tubeSet A a b ρ) L ∧ IsBoundedFieldOn F (tubeSet A a b ρ) B := by
  rw [← isLipschitzOnTube_iff, ← isBoundedOnTube_iff]
  exact ⟨fun h => ⟨h.sol, h.L_nonneg, h.B_nonneg, h.lipschitz, h.bounded⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end Problem

section ProblemExample

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **Non-vacuity, with a nonzero linear field in tube form.** The matrix field
`F(t, Y) = M Y + Y Nᵀ + G` with a stationary point `C` (`M C + C Nᵀ + G = 0`) has the constant
solution `A(t) = C`, and on the tube of radius `ρ ≥ 0` around it the field is
`(‖M‖ + ‖N‖)`-Lipschitz and bounded by `(‖M‖ + ‖N‖) ρ`, whatever the size of `G`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G C : Matrix m n ℝ)
    (hC : M * C + C * Nᵀ + G = 0) (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) a b ρ (‖M‖ + ‖N‖)
      ((‖M‖ + ‖N‖) * ρ) := by
  have hlin : ∀ X Y : Matrix m n ℝ,
      ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ ≤ (‖M‖ + ‖N‖) * ‖X - Y‖ := fun X Y =>
    calc ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ = ‖M * (X - Y) + (X - Y) * Nᵀ‖ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          congr 1
          abel
      _ ≤ ‖M‖ * ‖X - Y‖ + ‖X - Y‖ * ‖N‖ :=
          (norm_add_le _ _).trans (add_le_add (Frobenius.norm_mul_le _ _)
            ((Frobenius.norm_mul_le _ _).trans_eq (by rw [Frobenius.norm_transpose])))
      _ = (‖M‖ + ‖N‖) * ‖X - Y‖ := by ring
  have hL : 0 ≤ ‖M‖ + ‖N‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, hL, mul_nonneg hL hρ,
    fun _ _ X Y _ _ => hlin X Y, fun _ _ X hX => ?_⟩
  · exact (hasDerivWithinAt_const t (Ici t) C).congr_deriv hC.symm
  · calc ‖M * X + X * Nᵀ + G‖ = ‖M * X + X * Nᵀ + G - (M * C + C * Nᵀ + G)‖ := by
          rw [hC, sub_zero]
      _ ≤ (‖M‖ + ‖N‖) * ‖X - C‖ := hlin X C
      _ ≤ (‖M‖ + ‖N‖) * ρ := mul_le_mul_of_nonneg_left hX hL

end ProblemExample

/-! ### Normal-component bounds -/

section NormalBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Normal-component bound on a region.** A low-rank approximation at a point `Y` is described
by a left projector `P` and a right projector `Q` (for a matrix `Y = U S Vᵀ`: `P X = U Uᵀ X` and
`Q X = X V Vᵀ`); the part of a vector that both discard, `(1 - P) ((1 - Q) x)`, is its normal
component, which a low-rank integrator cannot follow. `NormalBoundOn F 𝒯 D ε` says that the
normal component of `F(t, Y)` has norm at most `ε` for every admissible triple
`(P, Q, Y) ∈ 𝒯` and every time `t` with `(t, Y) ∈ D`. The region `D ⊆ ℝ × E` is typically the
tube around a reference solution, where the bound can hold with small `ε`.

The triples form a set because at rank-deficient points the projectors are not determined by the
point. The matrix instance is `FactoredNormalBoundOn`
(`factoredNormalBoundOn_iff_normalBoundOn`); the hypotheses `kNormal`, `lNormal` of the step
structures are the case of a single triple (`normalBoundOn_singleton_iff`). -/
def NormalBoundOn (F : ℝ → E → E) (𝒯 : Set ((E →L[ℝ] E) × (E →L[ℝ] E) × E))
    (D : Set (ℝ × E)) (ε : ℝ) : Prop :=
  ∀ t P Q Y, (P, Q, Y) ∈ 𝒯 → (t, Y) ∈ D → ‖(1 - P) ((1 - Q) (F t Y))‖ ≤ ε

variable {F : ℝ → E → E} {𝒯 𝒯' : Set ((E →L[ℝ] E) × (E →L[ℝ] E) × E)} {D D' : Set (ℝ × E)}
  {ε ε' : ℝ}

/-- The normal bound passes to fewer triples, a smaller region and a larger `ε`. -/
theorem NormalBoundOn.mono (h : NormalBoundOn F 𝒯 D ε) (h𝒯 : 𝒯' ⊆ 𝒯) (hD : D' ⊆ D)
    (hε : ε ≤ ε') : NormalBoundOn F 𝒯' D' ε' := fun t P Q Y hp hY =>
  (h t P Q Y (h𝒯 hp) (hD hY)).trans hε

/-- For a single triple `(P, Q, Y)` and the times `s`, the normal bound is the pointwise
hypothesis `∀ t ∈ s, ‖(1 - P) ((1 - Q) (F t Y))‖ ≤ ε`, the form of the fields `kNormal`, `lNormal`
of the step structures (with `s = [t₀, t₁]`). -/
theorem normalBoundOn_singleton_iff {P Q : E →L[ℝ] E} {Y : E} {s : Set ℝ} :
    NormalBoundOn F {(P, Q, Y)} (s ×ˢ {Y}) ε ↔ ∀ t ∈ s, ‖(1 - P) ((1 - Q) (F t Y))‖ ≤ ε := by
  constructor
  · exact fun h t ht => h t P Q Y rfl ⟨ht, rfl⟩
  · rintro h t P' Q' Y' hp ⟨ht, -⟩
    simp only [mem_singleton_iff, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact h t ht

/-- **Non-vacuity.** For the linear field `F(t, x) = c x + g`, every triple whose right projector
fixes the point and the source has normal component `0`, so the bound holds with `ε = 0` although
the field is not zero. -/
example (c : ℝ) (g : E) :
    NormalBoundOn (fun _ x => c • x + g) {p | p.2.1 p.2.2 = p.2.2 ∧ p.2.1 g = g} univ 0 := by
  rintro t P Q Y ⟨hY, hg⟩ -
  change Q Y = Y at hY
  change Q g = g at hg
  have h0 : (1 - Q) (c • Y + g) = 0 := by
    simp [hY, hg]
  change ‖(1 - P) ((1 - Q) (c • Y + g))‖ ≤ 0
  rw [h0, map_zero, norm_zero]

end NormalBound

end LeanDLRA
