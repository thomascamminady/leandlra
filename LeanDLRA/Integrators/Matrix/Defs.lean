import LeanDLRA.DLRA.Defs
import LeanDLRA.LinearAlgebra.Frobenius.Defs
import LeanDLRA.LinearAlgebra.Projection.Defs
import Mathlib.Order.Interval.Set.Defs

/-!
# Definitions: normal-component bounds for matrix integrators

The vocabulary of the matrix integrator layer (`Integrators/Matrix/`). The error of dynamical
low-rank approximation is controlled by the size `ε` of the part of the vector field `F` that is
normal to the manifold of rank-`r` matrices. For `Y = U S Vᵀ` with orthonormal `U`, `V` and
invertible `S`, the normal part of `Z` at `Y` is `(I - U Uᵀ) Z (I - V Vᵀ)`; the bounds below ask
this doubly-normal part of `F(t, U S Vᵀ)` to be at most `ε`, for all factors (global form) or for
factors near a given matrix (localized form). Both are stated for arbitrary, possibly singular,
`S`. `FactoredNormalBoundOn` asks the same on an arbitrary region `D ⊆ ℝ × ℝ^{m×n}` of times and
points `U S Vᵀ`; the global and the localized form are its instances for `D = univ` and
`D = [t₀, t₁] × closedBall Y ρ`, and the tube around a reference solution is the region of the
error theorems.

The theorems that use these bounds are in `LeanDLRA/Integrators/Matrix/BUG.lean` (error of the
matrix BUG integrator) and `LeanDLRA/Matrix/LowRankDistance.lean` (robust capture of the exact
flow).

## Main definitions

* `LeanDLRA.MatrixBUG.FactoredNormalBound F r ε`: `‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε` for
  all `t`, all `U : m × r`, `V : n × r` with orthonormal columns and all `S : r × r`.
* `LeanDLRA.NearNormalBound F r ε t₀ t₁ Y ρ`: the same for `t ∈ [t₀, t₁]` and factors with
  `‖U S Vᵀ - Y‖ ≤ ρ` only.
* `LeanDLRA.FactoredNormalBoundOn F r D ε`: the same for factors with `(t, U S Vᵀ) ∈ D`.

## Main results

* `LeanDLRA.nearNormalBound_of_factored`: the global bound implies the localized one.
* `LeanDLRA.factoredNormalBound_iff_univ`, `LeanDLRA.nearNormalBound_iff`: the global and the
  localized bound are `FactoredNormalBoundOn` on `univ` and on `Icc t₀ t₁ ×ˢ closedBall Y ρ`.
* `LeanDLRA.factoredNormalBoundOn_iff_normalBoundOn`: `FactoredNormalBoundOn` is the abstract
  `NormalBoundOn` for the triples `(X ↦ U Uᵀ X, X ↦ X V Vᵀ, U S Vᵀ)`.
* `LeanDLRA.isLipschitzField_linear`, `LeanDLRA.dlraProblem_linear`,
  `LeanDLRA.continuous_uncurry_linear`, `LeanDLRA.factoredNormalBoundOn_linear`: the linear field
  `F(t, Y) = M Y + Y Nᵀ + G` is Lipschitz with constant `‖M‖ + ‖N‖`, bounded by `(‖M‖ + ‖N‖) ρ`
  on the tube of radius `ρ` around a stationary point, continuous, and its normal component is
  at most `‖G‖`. It is the test problem of the non-vacuity examples of the matrix integrators.

## References

* [CerutiLubich2022, Thm. 2]
-/

open Set
open scoped Matrix LeanDLRA.Frobenius

namespace LeanDLRA

namespace MatrixBUG

section NormalBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The **factored normal-component assumption** at rank `r` (assumption 2 of
[CerutiLubich2022, Thm. 2], in factored global form):

    ∀ t U V S, Uᵀ U = 1 → Vᵀ V = 1 → ‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε

for `U : m × r`, `V : n × r`, `S : r × r`. For `Y = U S Vᵀ` with invertible `S`,
`(I - U Uᵀ) Z (I - V Vᵀ) = (I - P(Y)) Z` is the normal part of `Z` at `Y ∈ M_r`. -/
def FactoredNormalBound (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

end NormalBound

end MatrixBUG

section NearNormalBound

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

/-- The **localized factored normal-component assumption**: on `[t₀, t₁]`, the doubly-normal
part `(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)` is `ε`-small at all points `U S Vᵀ` (orthonormal
`U : m × r`, `V : n × r`, arbitrary `S`) within distance `ρ` of `Y`. This is assumption 2 of
[CerutiLubich2022, Thm. 2] ("for `Y ∈ M_r` in a neighbourhood of `A(t)`"), imposed only near
the starting value; `MatrixBUG.FactoredNormalBound` is the global version. -/
def NearNormalBound (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ) (ε t₀ t₁ : ℝ)
    (Y : Matrix m n ℝ) (ρ : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ t₁, ∀ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
    (S : Matrix (Fin r) (Fin r) ℝ), Uᵀ * U = 1 → Vᵀ * V = 1 → ‖U * S * Vᵀ - Y‖ ≤ ρ →
      ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

/-- The global factored assumption implies the localized one. -/
theorem nearNormalBound_of_factored {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {ε : ℝ} (hε : MatrixBUG.FactoredNormalBound F r ε) (t₀ t₁ : ℝ) (Y : Matrix m n ℝ) (ρ : ℝ) :
    NearNormalBound F r ε t₀ t₁ Y ρ :=
  fun t _ U V S hU hV _ => hε t U V S hU hV

end NearNormalBound

/-! ### Non-vacuity -/

/-- The identity field `F(t, Y) = Y` has no normal component at any `U S Vᵀ`, so it satisfies the
factored normal-component assumption with `ε = 0`. -/
example (r : ℕ) :
    MatrixBUG.FactoredNormalBound (fun _ (Y : Matrix (Fin 3) (Fin 2) ℝ) => Y) r 0 := by
  intro t U V S hU hV
  have h : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
    rw [show U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one]
  simp [Matrix.sub_mul, h]

/-- The localized assumption follows for every `Y`, `ρ`. -/
example (r : ℕ) (Y₀ : Matrix (Fin 3) (Fin 2) ℝ) :
    NearNormalBound (fun _ (Y : Matrix (Fin 3) (Fin 2) ℝ) => Y) r 0 0 1 Y₀ 1 := by
  refine nearNormalBound_of_factored (fun t U V S hU hV => ?_) 0 1 Y₀ 1
  have h : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
    rw [show U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one]
  simp [Matrix.sub_mul, h]

/-! ### Normal-component bounds on a region -/

section NormalBoundOn

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The **factored normal-component bound at rank `r` on the region** `D ⊆ ℝ × ℝ^{m×n}`: for every
time `t` and every factorization `U S Vᵀ` with `U : m × r`, `V : n × r` with orthonormal columns
and an arbitrary (possibly singular) `S : r × r` such that `(t, U S Vᵀ) ∈ D`,

    ‖(I - U Uᵀ) F(t, U S Vᵀ) (I - V Vᵀ)‖ ≤ ε.

For invertible `S` the left-hand side is the normal component of `F(t, Y)` at the rank-`r`
matrix `Y = U S Vᵀ`, the part of the vector field that a rank-`r` approximation cannot follow;
asking it for singular `S` as well covers the intermediate values of the integrators. The region is
typically the tube `tubeSet A a b ρ` around a reference solution `A`: there the bound can hold with
small `ε` for fields with a large source term or linear part, while on `univ`
(`MatrixBUG.FactoredNormalBound`, `factoredNormalBound_iff_univ`) it constrains `F` at all points
(see the examples at the end of this file). The localized form `NearNormalBound` is the region
`[t₀, t₁] × closedBall Y ρ` (`nearNormalBound_iff`); the abstract form is `NormalBoundOn`
(`factoredNormalBoundOn_iff_normalBoundOn`). -/
def FactoredNormalBoundOn (F : ℝ → Matrix m n ℝ → Matrix m n ℝ) (r : ℕ)
    (D : Set (ℝ × Matrix m n ℝ)) (ε : ℝ) : Prop :=
  ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
    Uᵀ * U = 1 → Vᵀ * V = 1 → (t, U * S * Vᵀ) ∈ D →
      ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε

variable {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {D D' : Set (ℝ × Matrix m n ℝ)}
  {ε ε' : ℝ}

/-- The factored bound passes to smaller regions and larger `ε`. -/
theorem FactoredNormalBoundOn.mono (h : FactoredNormalBoundOn F r D ε) (hD : D' ⊆ D)
    (hε : ε ≤ ε') : FactoredNormalBoundOn F r D' ε' := fun t U V S hU hV hY =>
  (h t U V S hU hV (hD hY)).trans hε

/-- The global factored bound is the factored bound on the region `univ`. -/
theorem factoredNormalBound_iff_univ :
    MatrixBUG.FactoredNormalBound F r ε ↔ FactoredNormalBoundOn F r univ ε :=
  ⟨fun h t U V S hU hV _ => h t U V S hU hV, fun h t U V S hU hV => h t U V S hU hV trivial⟩

/-- The localized factored bound near `Y` on `[t₀, t₁]` is the factored bound on the region
`Icc t₀ t₁ ×ˢ closedBall Y ρ`. -/
theorem nearNormalBound_iff {t₀ t₁ ρ : ℝ} {Y : Matrix m n ℝ} :
    NearNormalBound F r ε t₀ t₁ Y ρ ↔
      FactoredNormalBoundOn F r (Icc t₀ t₁ ×ˢ Metric.closedBall Y ρ) ε := by
  refine ⟨fun h t U V S hU hV hY => h t hY.1 U V S hU hV ?_,
    fun h t ht U V S hU hV hY => h t U V S hU hV ⟨ht, ?_⟩⟩
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hY.2
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hY

/-- `(1 - P) ((1 - Q) Z) = (I - U Uᵀ) Z (I - V Vᵀ)` for `P = leftProj U`, `Q = rightProj V`. -/
private theorem one_sub_leftProj_one_sub_rightProj (U : Matrix m (Fin r) ℝ)
    (V : Matrix n (Fin r) ℝ) (Z : Matrix m n ℝ) :
    (1 - leftProj U) ((1 - rightProj V) Z) = (1 - U * Uᵀ) * Z * (1 - V * Vᵀ) := by
  change (Z - rightProj V Z) - leftProj U (Z - rightProj V Z) = _
  simp only [leftProj_apply, rightProj_apply, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- The factored bound is the abstract normal bound `NormalBoundOn` for the admissible triples
`(leftProj U, rightProj V, U S Vᵀ)` (`X ↦ U Uᵀ X`, `X ↦ X V Vᵀ`, the point) with `U`, `V` with
orthonormal columns and `S` arbitrary. -/
theorem factoredNormalBoundOn_iff_normalBoundOn :
    FactoredNormalBoundOn F r D ε ↔
      NormalBoundOn F {p | ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ)
        (S : Matrix (Fin r) (Fin r) ℝ), Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧
          p = (leftProj U, rightProj V, U * S * Vᵀ)} D ε := by
  constructor
  · rintro h t P Q Y ⟨U, V, S, hU, hV, hp⟩ hY
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    rw [one_sub_leftProj_one_sub_rightProj]
    exact h t U V S hU hV hY
  · intro h t U V S hU hV hY
    rw [← one_sub_leftProj_one_sub_rightProj]
    exact h t _ _ _ ⟨U, V, S, hU, hV, rfl⟩ hY

end NormalBoundOn

/-! ### Non-vacuity of the region form: linear fields `F(t, Y) = M Y + Y Nᵀ + G` -/

section NormalBoundOnExamples

open scoped RealInnerProductSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {r : ℕ}

omit [DecidableEq m] in
/-- `⟪P X, Y⟫ = ⟪X, Pᵀ Y⟫` for the Frobenius inner product. -/
private theorem inner_mul_left_aux {k : Type*} [Fintype k] (P : Matrix m m ℝ)
    (X Y : Matrix m k ℝ) : ⟪P * X, Y⟫ = ⟪X, Pᵀ * Y⟫ := by
  have h : ∀ A B : Matrix m k ℝ, ⟪A, B⟫ = Matrix.trace (Aᵀ * B) := fun A B => by
    simp only [Frobenius.inner_def, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply]
    exact Finset.sum_comm
  rw [h, h, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The orthogonal projector `I - U Uᵀ` does not increase the Frobenius norm. -/
private theorem norm_one_sub_mul_le_aux {k : Type*} [Fintype k] {U : Matrix m (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (X : Matrix m k ℝ) : ‖(1 - U * Uᵀ) * X‖ ≤ ‖X‖ := by
  have hsymm : (1 - U * Uᵀ)ᵀ = 1 - U * Uᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hidem : (1 - U * Uᵀ) * (1 - U * Uᵀ) = 1 - U * Uᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, sub_self, sub_zero]
  have h : ‖(1 - U * Uᵀ) * X‖ ^ 2 ≤ ‖X‖ * ‖(1 - U * Uᵀ) * X‖ := by
    rw [← real_inner_self_eq_norm_sq, inner_mul_left_aux, hsymm, ← Matrix.mul_assoc, hidem]
    exact real_inner_le_norm _ _
  nlinarith [norm_nonneg X, norm_nonneg ((1 - U * Uᵀ) * X)]

/-- The doubly-normal part `(I - U Uᵀ) X (I - V Vᵀ)` has at most the Frobenius norm of `X`. -/
private theorem norm_normal_le_aux {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (X : Matrix m n ℝ) :
    ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ ≤ ‖X‖ := by
  have hVt : (1 - V * Vᵀ)ᵀ = 1 - V * Vᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  calc ‖(1 - U * Uᵀ) * X * (1 - V * Vᵀ)‖ = ‖(1 - V * Vᵀ) * ((1 - U * Uᵀ) * X)ᵀ‖ := by
        rw [← Frobenius.norm_transpose, Matrix.transpose_mul, hVt]
    _ ≤ ‖((1 - U * Uᵀ) * X)ᵀ‖ := norm_one_sub_mul_le_aux hV _
    _ = ‖(1 - U * Uᵀ) * X‖ := Frobenius.norm_transpose _
    _ ≤ ‖X‖ := norm_one_sub_mul_le_aux hU X

/-- The linear part `M Y + Y Nᵀ` of the field has no doubly-normal component at `Y = U S Vᵀ`. -/
private theorem normal_mul_add_mul_transpose_add_eq {U : Matrix m (Fin r) ℝ}
    {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (M : Matrix m m ℝ)
    (N : Matrix n n ℝ) (S : Matrix (Fin r) (Fin r) ℝ) (G : Matrix m n ℝ) :
    (1 - U * Uᵀ) * (M * (U * S * Vᵀ) + U * S * Vᵀ * Nᵀ + G) * (1 - V * Vᵀ) =
      (1 - U * Uᵀ) * G * (1 - V * Vᵀ) := by
  have hU' : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hV' : Vᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  have h1 : (1 - U * Uᵀ) * (M * (U * S * Vᵀ)) * (1 - V * Vᵀ) = 0 := by
    rw [show (1 - U * Uᵀ) * (M * (U * S * Vᵀ)) * (1 - V * Vᵀ) =
        (1 - U * Uᵀ) * (M * U * S) * (Vᵀ * (1 - V * Vᵀ)) by simp only [Matrix.mul_assoc],
      hV', Matrix.mul_zero]
  have h2 : (1 - U * Uᵀ) * (U * S * Vᵀ * Nᵀ) * (1 - V * Vᵀ) = 0 := by
    rw [show (1 - U * Uᵀ) * (U * S * Vᵀ * Nᵀ) * (1 - V * Vᵀ) =
        (1 - U * Uᵀ) * U * (S * Vᵀ * Nᵀ * (1 - V * Vᵀ)) by simp only [Matrix.mul_assoc],
      hU', Matrix.zero_mul]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, h1, h2, zero_add, zero_add]

/-- The linear field `M Y + Y Nᵀ + G` satisfies the factored bound on every region with
`ε = ‖G‖`. -/
theorem factoredNormalBoundOn_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) (D : Set (ℝ × Matrix m n ℝ)) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r D ‖G‖ := by
  intro t U V S hU hV _
  change ‖(1 - U * Uᵀ) * (M * (U * S * Vᵀ) + U * S * Vᵀ * Nᵀ + G) * (1 - V * Vᵀ)‖ ≤ ‖G‖
  rw [normal_mul_add_mul_transpose_add_eq hU hV]
  exact norm_normal_le_aux hU hV G

/-- **Non-vacuity, global form.** For the linear field `F(t, Y) = M Y + Y Nᵀ + G` the linear part
has no normal component at any `U S Vᵀ`, so the factored bound holds on `univ` with `ε = ‖G‖`; for
`G = 0` it holds with `ε = 0` for a field that is not zero. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) r univ ‖G‖ :=
  factoredNormalBoundOn_linear M N G univ

/-- **Non-vacuity, tube form, with `ε` independent of the source.** On the tube of radius `ρ`
around the constant curve `C`, the field `F(t, Y) = M Y + Y Nᵀ + C` satisfies the factored bound
with `ε = ρ`, however large `‖C‖` is: at `Y = U S Vᵀ` the normal component of `F(t, Y)` is that
of `C - Y`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (C : Matrix m n ℝ) (a b ρ : ℝ) :
    FactoredNormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + C) r
      (tubeSet (fun _ => C) a b ρ) ρ := by
  intro t U V S hU hV hY
  have hY' : ‖U * S * Vᵀ - C‖ ≤ ρ := hY.2
  change ‖(1 - U * Uᵀ) * (M * (U * S * Vᵀ) + U * S * Vᵀ * Nᵀ + C) * (1 - V * Vᵀ)‖ ≤ ρ
  have hC := normal_mul_add_mul_transpose_add_eq hU hV (1 : Matrix m m ℝ) (0 : Matrix n n ℝ) S
    (C - U * S * Vᵀ)
  have e : (1 : Matrix m m ℝ) * (U * S * Vᵀ) + U * S * Vᵀ * (0 : Matrix n n ℝ)ᵀ +
      (C - U * S * Vᵀ) = C := by simp
  rw [e] at hC
  rw [normal_mul_add_mul_transpose_add_eq hU hV, hC]
  exact (norm_normal_le_aux hU hV _).trans (by rwa [norm_sub_rev])

/-- **Non-vacuity of `NormalBoundOn` for matrices**, through
`factoredNormalBoundOn_iff_normalBoundOn`. -/
example (M : Matrix m m ℝ) (N : Matrix n n ℝ) (G : Matrix m n ℝ) :
    NormalBoundOn (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G)
      {p | ∃ (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
        Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ p = (leftProj U, rightProj V, U * S * Vᵀ)} univ ‖G‖ :=
  factoredNormalBoundOn_iff_normalBoundOn.1 (factoredNormalBoundOn_linear M N G univ)

end NormalBoundOnExamples

/-! ### The linear field as a test problem

The lemmas of this section and `factoredNormalBoundOn_linear` show that the linear field
`F(t, Y) = M Y + Y Nᵀ + G` satisfies the hypotheses of the existence and error theorems of the
matrix integrators near a stationary point `C`. The field is Lipschitz but not bounded, so only
the tube form of the theorems applies to it. The non-vacuity examples of the integrators use
these lemmas, so that the integrators can be compared on one problem. -/

section LinearField

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The linear field `Y ↦ M Y + Y Nᵀ + G` changes by at most `(‖M‖ + ‖N‖) ‖X - Y‖`. -/
theorem norm_linear_sub_le (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G X Y : Matrix m n ℝ) :
    ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ ≤ (‖M‖ + ‖N‖) * ‖X - Y‖ :=
  calc ‖M * X + X * Nᵀ + G - (M * Y + Y * Nᵀ + G)‖ = ‖M * (X - Y) + (X - Y) * Nᵀ‖ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        abel
    _ ≤ ‖M‖ * ‖X - Y‖ + ‖X - Y‖ * ‖N‖ :=
        (norm_add_le _ _).trans (add_le_add (Frobenius.norm_mul_le _ _)
          ((Frobenius.norm_mul_le _ _).trans_eq (by rw [Frobenius.norm_transpose])))
    _ = (‖M‖ + ‖N‖) * ‖X - Y‖ := by ring

/-- The linear field is globally Lipschitz with constant `‖M‖ + ‖N‖`. -/
theorem isLipschitzField_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) :
    IsLipschitzField (fun _ (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) (‖M‖ + ‖N‖) :=
  fun _ X Y => norm_linear_sub_le M N G X Y

/-- Around a stationary point `C` the linear field is a `DLRAProblem` on the tube of every radius
`ρ ≥ 0`, with Lipschitz constant `‖M‖ + ‖N‖` and bound `(‖M‖ + ‖N‖) ρ`. -/
theorem dlraProblem_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G C : Matrix m n ℝ) (hC : M * C + C * Nᵀ + G = 0) (a b : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    DLRAProblem (fun _ Y => M * Y + Y * Nᵀ + G) (fun _ => C) a b ρ (‖M‖ + ‖N‖)
      ((‖M‖ + ‖N‖) * ρ) := by
  have hL : 0 ≤ ‖M‖ + ‖N‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨⟨continuousOn_const, fun t _ => ?_⟩, hL, mul_nonneg hL hρ,
    fun _ _ X Y _ _ => norm_linear_sub_le M N G X Y, fun _ _ X hX => ?_⟩
  · exact (hasDerivWithinAt_const t (Ici t) C).congr_deriv hC.symm
  · calc ‖M * X + X * Nᵀ + G‖ = ‖M * X + X * Nᵀ + G - (M * C + C * Nᵀ + G)‖ := by
          rw [hC, sub_zero]
      _ ≤ (‖M‖ + ‖N‖) * ‖X - C‖ := norm_linear_sub_le M N G X C
      _ ≤ (‖M‖ + ‖N‖) * ρ := mul_le_mul_of_nonneg_left hX hL

/-- The linear field is jointly continuous. -/
theorem continuous_uncurry_linear (M : Matrix m m ℝ) (N : Matrix n n ℝ)
    (G : Matrix m n ℝ) :
    Continuous (Function.uncurry fun (_ : ℝ) (Y : Matrix m n ℝ) => M * Y + Y * Nᵀ + G) := by
  change Continuous fun p : ℝ × Matrix m n ℝ =>
    Frobenius.leftMulCLM M p.2 + Frobenius.rightMulCLM Nᵀ p.2 + G
  exact (((Frobenius.leftMulCLM M).continuous.comp continuous_snd).add
    ((Frobenius.rightMulCLM Nᵀ).continuous.comp continuous_snd)).add continuous_const

end LinearField

end LeanDLRA
